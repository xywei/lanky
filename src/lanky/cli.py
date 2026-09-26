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
warns (see below). Each refuted fact is repeated under the table with what
explains it: its ``counterexample``, its ``witness`` and its ``reason``, three
standard provenance keys read the same way whichever oracle or plugin refuted
it, or a line saying that none was recorded (see :func:`refutation_lines`).

A fact that rests on others is worth no more than they are, and the table says
so after its status (see :meth:`lanky.ledger.Ledger.support`); ``--json``
carries each fact's ``effective`` status and the ids it is ``under``. Neither
changes the exit code: a fact resting on a refuted one fails the check through
the refuted one, and a fact resting on an assumption is no more a failure than
the assumption.

Four more things are printed under the table and do not change the exit code.
Each axiom is named in a ``CITED`` line with the citation it is taken on,
which is the one thing that stands behind an ``assumed (axiom)`` row. A
statement whose sampled reading could not be run where a stronger oracle's
could, or disagrees with it, is reported under ``SEMANTICS`` (a division by
zero is the gap that remains; see :mod:`lanky.semantics`): the fact keeps the
status its oracle gave it. A statement whose hypotheses no draw satisfied, and
that no oracle could show inconsistent, gets a ``WARNING`` line: the claim may
be vacuous, or its hypotheses may hold only where the sampler does not look.
And a fact that rests on an id no fact in the ledger has gets an
``UNRESOLVED`` line naming it: the id counts as an assumption, and it is either
written wrong or names a fact of another file, which is in that file's ledger.
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

        Exit code 1 on any refutation or vacuous fact, and 1 with the traceback
        when a file itself cannot be imported, because a file that does not
        import is a broken claim too. Exit code 2 when there is no such file,
        which is a mistake in the command rather than in the file, and then
        nothing is checked. An axiom's citation, a semantics disagreement, a
        warning about hypotheses no draw satisfied and an id a fact rests on
        that the ledger does not hold are printed but do not fail the check.

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
            facts.extend(ledger.to_dicts())
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
        CheckVerb._report_citations(ledger)
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
        CheckVerb._report_unresolved(ledger)
        refuted = ledger.by_status(Status.REFUTED)
        if not refuted:
            return vacuous
        print()
        for fact in refuted:
            print(f"REFUTED {fact.owner} at {fact.where}: {fact.statement}")
            for line in refutation_lines(fact):
                print(f"  {line}")
        return True

    @staticmethod
    def _report_citations(ledger: Ledger) -> None:
        """Name each axiom under the table, with the citation it is taken on.

        An axiom is ``assumed`` on its author's word that a reference says
        what it says, so the citation is what a reader of its row needs, and
        it used to be in the JSON alone. The lines come right under the table,
        one per axiom in the table's order, because they explain rows of it:
        the ``assumed (axiom)`` ones, and every ``under`` that names one. A
        refuted axiom keeps its line, since the reference is where to look
        for what was copied down wrong. A citation of several lines is
        indented under its first.
        """
        cited = [fact for fact in ledger if fact.is_axiom and fact.provenance.get("cite")]
        if not cited:
            return
        print()
        for fact in cited:
            first, *rest = str(fact.provenance["cite"]).splitlines() or [""]
            print(f"CITED {fact.owner} at {fact.where}: {first}")
            for line in rest:
                print(f"  {line}")

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
    def _report_unresolved(ledger: Ledger) -> None:
        """Name, under the fact that rests on it, each id no fact in the ledger has.

        Such an id counts as an assumption in what the fact is worth (see
        :meth:`lanky.ledger.Ledger.support`), and the table lists it after
        ``under``, where it reads like any other assumption. It is either
        written wrong, a ``uses=`` string that names nothing, or the id of a
        fact of another file, since each file checked has a ledger of its own;
        lanky cannot tell which, so it says which id it is and leaves the exit
        code alone, because naming a fact of another file is not a mistake.
        """
        for fact in ledger:
            missing = [entry for entry in dict.fromkeys(fact.rests_on) if entry not in ledger]
            if not missing:
                continue
            print()
            print(
                f"UNRESOLVED {fact.owner} at {fact.where}: rests on "
                f"{', '.join(missing)}, which this ledger does not hold"
            )
            print(
                "  counted as an assumption; a fact of another file is in that "
                "file's ledger, not this one"
            )

    @staticmethod
    def _print_detail(fact: Any) -> None:
        """The reason a draw could not be completed, when the tester recorded one."""
        detail = fact.provenance.get("unsatisfied_detail")
        if detail:
            print(f"  {detail}")


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

    Three provenance keys are standard, whichever oracle or plugin refuted the
    fact, and each is printed when it says something. ``counterexample`` is
    the assignment of the statement's variables that makes it false, as the
    property tester records it. ``witness`` is the object that refutes it
    when that is not an assignment: loopty's isl oracle records the cell that
    escapes an array, or the pair of statement instances a schedule runs out
    of order. ``reason`` is the explanation in words, and comes last, because
    a reason usually talks about the counterexample or the witness above it; a
    refutation with neither (loopty's fact about a body it cannot trace) is
    explained by the reason alone. When none of the three is there, a line
    says so, so that a bare ``REFUTED`` is never read as having been explained
    somewhere.

    The keys are read the same way for every plugin, and lanky knows no
    other: a plugin's own keys, such as loopty's ``witness_text``, stay in the
    JSON with the rest of the provenance. A value that prints as several lines
    comes back as several, so that each is indented under the ``REFUTED``
    line and not only the first.

    An empty counterexample or witness is not printed. A closed statement such
    as ``-> 1 == 2`` carries an empty counterexample on purpose, because no
    assignment is what makes it false, and it used to be printed as
    ``counterexample: {}`` above the reason, a line that says nothing; the
    reason is what explains it. The JSON ledger keeps the empty
    counterexample, as it keeps every field.
    """
    provenance = fact.provenance
    lines: list[str] = []
    for key in ("counterexample", "witness"):
        value = provenance.get(key)
        if _recorded(value):
            lines.extend(f"{key}: {value}".splitlines())
    reason = provenance.get("reason")
    if _recorded(reason):
        lines.extend(str(reason).splitlines())
    if not lines:
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
