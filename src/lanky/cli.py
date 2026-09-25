"""The ``lanky`` command: a host for verbs.

The design idea. The CLI owns argument parsing and plugin discovery and nothing
else. ``check`` is built in; every other verb arrives through the
``lanky.verbs`` entry-point group, which is how ``loopty run`` becomes a
subcommand of ``lanky`` without lanky knowing what loopty is.

``check`` exits 1 when any fact is ``REFUTED``, so it works in CI: a refuted
fact is a broken claim, while an assumed one is a claim nobody got to. Each
refuted fact is repeated under the table with what explains it: its
counterexample, its reason, or a line saying that nothing was recorded (see
:func:`refutation_lines`).

One more thing is printed under the table and does not change the exit code: a
statement whose Lean reading and whose Python reading disagree, or whose Python
reading could not be run at all (subtraction over ``Nat``, division over
``Int``, division by zero; see :mod:`lanky.semantics`). The fact keeps the
status its oracle gave it, because the oracle was right about the statement it
read; what is reported is that there are two readings and they are not the same
statement.
"""

from __future__ import annotations

import argparse
import json
import traceback
from pathlib import Path
from typing import Any

from lanky.check import check_path, oracle_lines
from lanky.ledger import Fact, Ledger, Status
from lanky.plugins import registry

__all__ = ["CheckVerb", "build_parser", "main", "refutation_lines"]


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

        Exit code 1 on any refutation, and 1 with the traceback when a file
        itself cannot be imported, because a file that does not import is a
        broken claim too. Exit code 2 when there is no such file, which is a
        mistake in the command rather than in the file, and then nothing is
        checked. A semantics disagreement is printed but does not fail the
        check: nothing was refuted, two readings differ.

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
        """Print one ledger and what follows it; whether anything was refuted."""
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
        refuted = ledger.by_status(Status.REFUTED)
        if not refuted:
            return False
        print()
        for fact in refuted:
            print(f"REFUTED {fact.owner} at {fact.where}: {fact.statement}")
            for line in refutation_lines(fact):
                print(f"  {line}")
        return True


def _recorded(value: Any) -> bool:
    """Whether a provenance entry says something: present, and not empty.

    Asked with ``is None`` and ``len`` rather than truthiness, because an entry
    can be a lanky term, whose truth value is not a question Python may ask.
    """
    if value is None:
        return False
    try:
        return len(value) > 0
    except TypeError:
        return True


def refutation_lines(fact: Fact) -> list[str]:
    """The lines ``lanky check`` prints under a fact's ``REFUTED`` line.

    The counterexample, when there is one that names something; then the
    fact's ``reason``, whenever it has one, since a refutation with no
    assignment to show (loopty's fact about a body it cannot trace) is
    explained by nothing else, and one with an assignment is explained better
    with it; and, when there is neither, a line saying so, so that a bare
    ``REFUTED`` is never read as having been explained somewhere. A plugin's
    own ``witness`` (loopty's isl oracle records one) counts as a witness for
    that last line; it is not printed, and stays in the JSON with the rest of
    the provenance. A reason of several lines comes back as several, so that
    each is indented under the ``REFUTED`` line and not only the first.

    An empty counterexample is not printed. A closed statement such as ``-> 1
    == 2`` carries one on purpose, because no assignment is what makes it
    false, and it used to be printed as ``counterexample: {}`` above the
    reason, a line that says nothing; the reason is what explains it. The
    JSON ledger keeps the empty counterexample, as it keeps every field.
    """
    provenance = fact.provenance
    lines = []
    counterexample = provenance.get("counterexample")
    if _recorded(counterexample):
        lines.append(f"counterexample: {counterexample}")
    reason = provenance.get("reason")
    if _recorded(reason):
        lines.extend(str(reason).splitlines())
    if not lines and not _recorded(provenance.get("witness")):
        lines.append("no witness recorded")
    return lines


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
