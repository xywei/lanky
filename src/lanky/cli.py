"""The ``lanky`` command: a host for verbs.

The design idea. The CLI owns argument parsing and plugin discovery and nothing
else. ``check`` is built in; every other verb arrives through the
``lanky.verbs`` entry-point group, which is how ``loopty run`` becomes a
subcommand of ``lanky`` without lanky knowing what loopty is.

``check`` exits 1 when any fact is ``REFUTED`` or vacuous, so it works in CI:
a refuted fact is a broken claim, and a vacuous one is a claim whose hypotheses
an oracle has shown inconsistent, which is true and says nothing, while an
assumed one is a claim nobody got to. Every oracle reads a statement the same
way, as integer arithmetic (see :mod:`lanky.lean`), so whether a claim is
refuted does not depend on whether Lean is installed. What Lean adds is proofs,
and the proof that a claim is vacuous, which fails a check that without it only
warns (see below).

Two more things are printed under the table and do not change the exit code. A
statement whose sampled reading could not be run where a stronger oracle's
could, or disagrees with it, is reported under ``SEMANTICS`` (a division by
zero is the gap that remains; see :mod:`lanky.semantics`): the fact keeps the
status its oracle gave it. And a statement whose hypotheses no draw satisfied,
and that no oracle could show inconsistent, gets a ``WARNING`` line: the claim
may be vacuous, or its hypotheses may hold only where the sampler does not look.
"""

from __future__ import annotations

import argparse
import json
import traceback
from pathlib import Path
from typing import Any

from lanky.check import check_path, oracle_lines
from lanky.ledger import Ledger, Status
from lanky.plugins import registry

__all__ = ["CheckVerb", "build_parser", "main"]


class CheckVerb:
    """``lanky check FILE...``: print the ledger of everything each file claims."""

    name = "check"
    help = "check files: print every obligation and who decided it"

    def add_arguments(self, parser: argparse.ArgumentParser, /) -> None:
        """Declare the arguments of ``check``."""
        parser.add_argument(
            "files",
            nargs="+",
            metavar="FILE",
            help="a Python file to check for the claims it defines (several may be listed)",
        )
        parser.add_argument("--json", metavar="OUT", help="also write the ledger as JSON")
        parser.add_argument(
            "--verbose",
            action="store_true",
            help="list the oracles and the facts as they are collected",
        )

    def run(self, args: argparse.Namespace, /) -> int:
        """Check each file, print its ledger, and report refutations.

        Exit code 1 on any refutation or vacuous fact, and 1 with the traceback
        when a file itself cannot be imported, because a file that does not
        import is a broken claim too. Exit code 2 when there is no such file,
        which is a mistake in the command rather than in the file, and then
        nothing is checked. A semantics disagreement and a warning about
        hypotheses no draw satisfied are printed but do not fail the check.

        Whether a file exists is asked before anything is imported rather than
        read off a ``FileNotFoundError``, because the file can raise one of its
        own: a checked file that opens a data file which is not there is a
        file that does not import, and deserves its traceback and exit code 1,
        not a claim that the file being checked is missing.

        Each file is checked for the claims it defines (see
        :func:`lanky.check.check_path`), so a claim imported from another
        module is checked by listing that module's file too. With several
        files each gets its own ledger under a ``==> FILE <==`` heading, since
        fact ids are unique within one file's ledger and not across files;
        one that does not import does not stop the others, and ``--json``
        writes the facts of every file that imported into one list. A
        namespace carrying a single ``file`` rather than ``files``, which is
        what ``loopty check`` builds, is read as a list of one.
        """
        files = getattr(args, "files", None) or [args.file]
        missing = [file for file in files if not Path(file).is_file()]
        if missing:
            for file in missing:
                print(f"lanky check: no such file: {file}")
            return 2
        if args.verbose:
            for line in oracle_lines():
                print(line)
            print()
        code = 0
        checked = 0
        facts: list[dict] = []
        for index, file in enumerate(files):
            if len(files) > 1:
                if index:
                    print()
                print(f"==> {file} <==")
            try:
                ledger = check_path(file, verbose=args.verbose)
            except Exception:  # noqa: BLE001 - the file is the user's, so show why
                print(f"lanky check: {file} could not be imported")
                print(traceback.format_exc().rstrip())
                code = 1
                continue
            checked += 1
            facts.extend(fact.to_dict() for fact in ledger)
            if self._report(ledger):
                code = 1
        if args.json and checked:
            Path(args.json).write_text(json.dumps(facts, indent=2, default=str), encoding="utf-8")
        return code

    @staticmethod
    def _report(ledger: Ledger) -> bool:
        """Print one ledger and what follows it; whether anything failed.

        A fact fails when it is refuted or vacuous.
        """
        print(ledger.render())
        for fact in ledger:
            disagreement = fact.provenance.get(
                "semantics_disagreement"
            ) or fact.provenance.get("semantics_undecided")
            if not disagreement:
                continue
            print()
            print(f"SEMANTICS {fact.owner} at {fact.where}: {disagreement}")
            counterexample = fact.provenance.get("semantics_counterexample")
            if counterexample:
                print(f"  counterexample: {counterexample}")
            for note in fact.provenance.get("semantics", ()):
                print(f"  {note}")
        vacuous = CheckVerb._report_hypotheses(ledger)
        refuted = ledger.by_status(Status.REFUTED)
        if not refuted:
            return vacuous
        print()
        for fact in refuted:
            print(f"REFUTED {fact.owner} at {fact.where}: {fact.statement}")
            if "counterexample" not in fact.provenance:
                continue
            witness = fact.provenance["counterexample"]
            print(f"  counterexample: {witness}")
            if not witness and fact.provenance.get("reason"):
                # A closed statement such as ``-> 1 == 2`` is false at no
                # assignment in particular. The empty witness is the honest
                # one and says nothing on its own, so the reason follows it.
                print(f"  {fact.provenance['reason']}")
        return True

    @staticmethod
    def _report_hypotheses(ledger: Ledger) -> bool:
        """Print what is known about hypotheses no draw satisfied; whether any are vacuous.

        A fact an oracle showed vacuous gets a ``VACUOUS`` block, and fails the
        check. One whose hypotheses no draw satisfied and no oracle could show
        inconsistent gets a ``WARNING`` line with the tester's reason under it,
        and does not: the sampler may simply not reach where they hold.
        """
        for fact in ledger:
            unsatisfied = fact.provenance.get("unsatisfied")
            if not unsatisfied or fact.is_vacuous:
                continue
            print()
            print(f"WARNING {fact.owner} at {fact.where}: {unsatisfied}")
            print("  no oracle could show them inconsistent, so the claim may be vacuous")
            CheckVerb._print_detail(fact)
        vacuous = ledger.vacuous()
        for fact in vacuous:
            print()
            print(f"VACUOUS {fact.owner} at {fact.where}: {fact.statement}")
            print(f"  {fact.provenance['vacuous']}, so the goal is never at stake")
            sampled = fact.provenance.get("unsatisfied") or fact.provenance.get("untestable")
            if sampled:
                print(f"  {sampled}")
            CheckVerb._print_detail(fact)
        return bool(vacuous)

    @staticmethod
    def _print_detail(fact: Any) -> None:
        """The reason a draw could not be completed, when the tester recorded one."""
        detail = fact.provenance.get("unsatisfied_detail")
        if detail:
            print(f"  {detail}")


def build_parser() -> tuple[argparse.ArgumentParser, dict[str, Any]]:
    """Build the parser from the built-in verb and every registered one."""
    from lanky import __version__

    registry.load_entry_points()
    parser = argparse.ArgumentParser(prog="lanky", description="Python for math you can check.")
    parser.add_argument("--version", action="version", version=f"lanky {__version__}")
    subparsers = parser.add_subparsers(dest="verb")
    verbs: dict[str, Any] = {}
    for verb in [CheckVerb(), *registry.verbs]:
        if verb.name in verbs:
            continue
        verbs[verb.name] = verb
        verb.add_arguments(subparsers.add_parser(verb.name, help=verb.help))
    return parser, verbs


def main(argv: Any = None) -> int:
    """Run a verb and return its exit code."""
    parser, verbs = build_parser()
    args = parser.parse_args(argv)
    if not args.verb:
        parser.print_help()
        return 0
    return verbs[args.verb].run(args)


if __name__ == "__main__":
    raise SystemExit(main())
