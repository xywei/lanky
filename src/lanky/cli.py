"""The ``lanky`` command: a host for verbs.

The design idea. The CLI owns argument parsing and plugin discovery and nothing
else. ``check`` is built in; every other verb arrives through the
``lanky.verbs`` entry-point group, which is how ``loopty run`` becomes a
subcommand of ``lanky`` without lanky knowing what loopty is.

``check`` exits 1 when any fact is ``REFUTED`` or vacuous, so it works in CI:
a refuted fact is a broken claim, and a vacuous one is a claim whose hypotheses
an oracle has shown inconsistent, or whose goal's guard it has shown empty
wherever the hypotheses hold, which is true and says nothing, while an assumed
one is a claim nobody got to. It exits 1 as well when two claims of a file have
one fact id, which a definition that makes several claims gives them: a ledger
holds one fact per id, so the later claims are named in a ``DUPLICATE`` block
and not checked (see :func:`lanky.check.check_path`). Every oracle reads a
statement the same way, as integer arithmetic (see :mod:`lanky.lean`), so
whether a claim is refuted does not depend on whether Lean is installed. What
Lean adds is proofs, and the proof that a claim is vacuous, which fails a check
that without it only warns (see below). Each refuted fact is repeated under the
table with what explains it: its ``counterexample``, its ``witness`` and its
``reason``, three standard provenance keys read the same way whichever oracle
or plugin refuted it, or a line saying that none was recorded (see
:func:`refutation_lines`).

A fact that rests on others is worth no more than they are, and the table says
so after its status (see :meth:`lanky.ledger.Ledger.support`); ``--json``
carries each fact's ``effective`` status and the ids it is ``under``. Neither
changes the exit code: a fact resting on a refuted one fails the check through
the refuted one, and a fact resting on an assumption is no more a failure than
the assumption.

Six more things are printed under the table and do not change the exit code.
Each axiom is named in a ``CITED`` line with the citation it is taken on,
which is the one thing that stands behind an ``assumed (axiom)`` row. A fact
left ``assumed`` that an oracle looked at and declined, saying why, gets a
``DECLINED`` line with that reason, the standard provenance key ``declined``
(see :func:`decline_lines`): an ``assumed`` row is otherwise read as "no oracle
knows this kind of claim", where the one that knows it may have found it
outside what it decides. A fact an oracle raised over gets a ``RAISED`` line
with the oracle and the exception (see :func:`report_raised`): its row is
what the other oracles found, and would otherwise read as a claim that oracle
was never offered. A
statement whose sampled reading could not be run where a stronger oracle's
could, or disagrees with it, is reported under ``SEMANTICS`` (a division by
zero is the gap that remains; see :mod:`lanky.semantics`): the fact keeps the
status its oracle gave it. A statement whose hypotheses no draw satisfied, and
that no oracle could show inconsistent, gets a ``WARNING`` line: the claim may
be vacuous, or its hypotheses may hold only where the sampler does not look.
So does a statement whose goal is a universal whose guard held at no valid
draw, when no oracle could show the guard empty, and a ``tested`` fact whose
pass rests on thin evidence, with the ``reason`` the tester gave it: most of
its draws decided nothing, or its valid draws are all at a few assignments
(see :func:`lanky.testing.thin_pass_reason`).
And a fact that rests on an id no fact in the ledger has gets an
``UNRESOLVED`` line naming it: the id counts as an assumption, and it is either
written wrong or names a fact of another file, which is in that file's ledger.

Checking a file imports it, and a process imports a module of a given name
once. So ``check`` gives each distinct source root of the files it is handed
(see :func:`lanky.check.source_roots`) a child process of its own, and files
with the same roots share one: two directories that each hold a ``helpers.py``
are checked against their own. Files that all share their roots are checked in
this process, as :func:`lanky.check.check_path` checks a file, and print what
they always printed (see :meth:`CheckVerb.run`). A child is started with this
interpreter's command-line options; on Linux and macOS it also ends when this
process ends, however it ends, and cannot hold the command up once it has
exited, whatever it started (see :meth:`CheckVerb._check_in_children`).
"""

from __future__ import annotations

import argparse
import codecs
import functools
import json
import os
import re
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import traceback
from collections.abc import Iterator
from pathlib import Path
from typing import Any, BinaryIO, TextIO

from lanky.check import check_path, oracle_lines, source_roots
from lanky.ledger import Fact, Ledger, Status
from lanky.outline import proof_lines, step_lines
from lanky.plugins import oracle_availability, registry

__all__ = [
    "CheckVerb",
    "build_parser",
    "decline_lines",
    "main",
    "refutation_lines",
    "report_known",
    "report_lean",
    "report_missing",
    "report_proofs",
    "report_proved",
    "report_raised",
    "report_refused",
    "report_steps",
    "report_unproved",
    "report_written",
    "terminal_columns",
]


class CheckVerb:
    """``lanky check FILE...``: print the ledger of everything each file claims."""

    name = "check"
    help = "check files: print every obligation and who decided it"

    def add_arguments(self, parser: argparse.ArgumentParser, /) -> None:
        """Declare the arguments of ``check``."""
        parser.add_argument(
            "files",
            nargs="*",
            metavar="FILE",
            help="a Python file to check for the claims it defines (several may be listed)",
        )
        parser.add_argument("--json", metavar="OUT", help="also write the ledger as JSON")
        parser.add_argument(
            "--verbose",
            action="store_true",
            help="list the oracles and the facts as they are collected",
        )
        parser.add_argument(
            "--show-lean",
            nargs="?",
            const="",
            default=None,
            metavar="TEXT",
            help=(
                "print the Lean of every row that has some, or of the rows whose "
                "owner, id or statement contains TEXT"
            ),
        )
        parser.add_argument(
            "--proofs",
            nargs="?",
            const="",
            default=None,
            metavar="TEXT",
            help=(
                "print the proof lanky found for each proved claim, as a Python body "
                "where Python can say it, or of the claims whose name contains TEXT"
            ),
        )
        parser.add_argument(
            "--steps",
            nargs="?",
            const="",
            default=None,
            metavar="TEXT",
            help=(
                "print the outline of the proof lanky found for each proved claim, "
                "or of the claims whose name contains TEXT"
            ),
        )

    def run(self, args: argparse.Namespace, /) -> int:
        """Check each file, print its ledger, and report refutations.

        Exit code 1 on any refutation or vacuous fact, and on two claims of
        one id, which leaves one of them unchecked; and 1 with the traceback
        when a file itself cannot be imported, because a file that does not
        import is a broken claim too. Exit code 2 when there is no such file,
        which is a mistake in the command rather than in the file, and then
        nothing is checked; and 2 under ``python -O``, which removes every
        ``assert``, and so every step of every written proof. An axiom's
        citation, the reason an oracle declined a fact left assumed, an
        oracle that raised, a semantics disagreement, a warning about
        hypotheses no draw satisfied or a pass on thin evidence, and an id a
        fact rests on that the ledger does not hold are printed but do not
        fail the check.

        Whether a file exists is asked before anything is imported rather than
        read off a ``FileNotFoundError``, because the file can raise one of its
        own: a checked file that opens a data file which is not there is a
        file that does not import, and deserves its traceback and exit code 1,
        not a claim that the file being checked is missing.

        Each file is checked for the claims it defines (see
        :func:`lanky.check.check_path`), so a claim imported from another
        module is checked by listing that module's file too. With several
        files each gets its own ledger under a ``==> FILE <==`` heading, and
        what one file's facts rest on in another is named, not resolved: an
        id names its definition by the module name the file's path gives it
        (:func:`lanky.check.module_name`), so it is the id the other file's
        ledger holds, and this file's ledger names it in an ``UNRESOLVED``
        line. Ids are unique within one file's ledger. Two files at the same
        place under different roots, ``a/helpers.py`` and ``b/helpers.py``,
        have one module name, as a file of a namespace package has with a
        file of its name beside the package, and ``where`` and the ``path``
        in the provenance tell their facts apart. A file that does not import
        does not stop the others, and ``--json`` writes the facts of every
        file that imported into one list. A namespace carrying a single
        ``file`` rather than ``files``, which is what ``loopty check`` builds,
        is read as a list of one.

        Files are checked one process per distinct source root (see
        :func:`lanky.check.source_roots`). When every file has the same
        roots, which a single file always does, they are checked in this
        process one after another, and a module one of them imports is there
        for the next, as it always was. When the roots differ, each distinct
        set of roots gets a child process of its own (see
        :meth:`_check_in_children`), started with this interpreter, this
        ``sys.path`` and the environment, so that no file is handed a module
        another directory's file imported under the same name. The ledgers are
        then printed root by root, in the order each root first appears among
        the files and within a root in the order the files are listed, and
        ``--json`` lists the facts in that order too. What each root's files
        print is what ``lanky check`` of those files alone prints, headings
        included (the oracles ``--verbose`` lists are listed once, above
        them all), and the check fails when any root's does.
        """
        files = getattr(args, "files", None)
        files = [*(files if files is not None else [args.file]), *_files_given_as_text(args)]
        files = _in_the_order_given(files, getattr(args, "argv", None))
        if not __debug__ or sys.flags.optimize:
            from lanky.check import OPTIMIZED

            print(f"lanky check: {OPTIMIZED}")
            return 2
        if not files:
            print("lanky check: name a file to check, as in lanky check examples/gauss.py")
            return 2
        missing = [file for file in files if not Path(file).is_file()]
        if missing:
            for file in missing:
                print(f"lanky check: no such file: {file}")
            return 2
        if args.verbose:
            for line in oracle_lines():
                print(line)
            print()
        groups = _by_source_roots(files)
        show_lean = getattr(args, "show_lean", None)
        views = {
            "proofs": getattr(args, "proofs", None),
            "steps": getattr(args, "steps", None),
        }
        if len(groups) == 1:
            code, checked, facts = self._check_files(
                files,
                verbose=args.verbose,
                headings=len(files) > 1,
                show_lean=show_lean,
                **views,
            )
        else:
            code, checked, facts = self._check_in_children(
                groups,
                verbose=args.verbose,
                facts_wanted=bool(args.json),
                show_lean=show_lean,
                **views,
            )
        if args.json and checked:
            Path(args.json).write_text(json.dumps(facts, indent=2, default=str), encoding="utf-8")
        return code

    @classmethod
    def _check_files(
        cls,
        files: list[str],
        *,
        verbose: bool,
        headings: bool,
        show_lean: str | None = None,
        proofs: str | None = None,
        steps: str | None = None,
    ) -> tuple[int, int, list[dict]]:
        """Check files in this process, printing each ledger as it is done.

        Returns the exit code, how many files imported, and the facts of
        those that did. With ``headings`` each file's ledger is printed under
        a ``==> FILE <==`` line, and a blank line separates one file from the
        next. ``show_lean`` is ``--show-lean``: ``None`` when it was not
        given, and the text the rows have to contain, maybe empty, when it
        was (see :meth:`_report_lean`); ``proofs`` and ``steps`` are
        ``--proofs`` and ``--steps``, read the same way (see
        :func:`report_proofs` and :func:`report_steps`).
        """
        code = 0
        checked = 0
        facts: list[dict] = []
        for index, file in enumerate(files):
            if headings:
                if index:
                    print()
                print(f"==> {file} <==")
            try:
                ledger = check_path(file, verbose=verbose)
            except Exception:  # noqa: BLE001 - the file is the user's, so show why
                print(f"lanky check: {file} could not be imported")
                print(traceback.format_exc().rstrip())
                code = 1
                continue
            checked += 1
            facts.extend(ledger.to_dicts())
            if cls._report(
                ledger, verbose=verbose, show_lean=show_lean, proofs=proofs, steps=steps
            ):
                code = 1
        return code, checked, facts

    @staticmethod
    def _check_in_children(
        groups: list[list[str]],
        *,
        verbose: bool,
        facts_wanted: bool,
        show_lean: str | None = None,
        proofs: str | None = None,
        steps: str | None = None,
    ) -> tuple[int, int, list[dict]]:
        """Check each group of files in a child process of its own, one after another.

        A child is this interpreter running :data:`_CHILD`, which takes this
        process's ``sys.path`` and ``sys.argv`` before it imports lanky, so it
        finds what this process would find, and then checks its files as
        :meth:`_check_files` does, with headings. Its working directory and
        environment are this process's. What it prints is copied to this
        process's ``sys.stdout`` and ``sys.stderr`` line by line as it comes,
        so the output reads as a check in one process would, and a blank line
        separates one child's output from the next. What it reports (its
        exit code, how many of its files imported, and their facts when
        ``--json`` wants them) comes back through a file in a scratch
        directory rather than through its output, which the checked files
        write to as well.

        A child that stops before it reports, because a checked file ended
        the process (``sys.exit`` while it is imported, say) or it could not
        be started, gets a line saying so, and the check fails; the other
        groups are still checked.

        A child finds its plugins the way the ``lanky`` command does, through
        their entry points (see :meth:`lanky.plugins.Registry.load_entry_points`).
        A theory or an oracle that a program registered by hand in this
        process before calling the verb is not in a child, so such a program
        checks files of several roots with :func:`lanky.check.check_path`, a
        process per root.

        Three things keep a child's life inside this one's. It is started
        with this interpreter's command-line options (``-O``, ``-W``, ``-X``
        and the rest, see :func:`_interpreter_flags`), which reached it only
        through the environment variables that mirror them. It gets
        ``SIGTERM`` when this process ends (see :func:`_end_with_parent`), so
        a ``SIGTERM`` or a ``SIGKILL`` sent to this process alone, which ends
        it with nothing run on the way out, no longer leaves the child
        checking for no one until its next write to the closed pipe; and on
        ``SIGTERM`` a child kills the Lean REPLs it started before it ends,
        which this process relies on when it has to stop a child itself (see
        :func:`_stop`). And once it has exited, its output is copied up to
        the last byte it wrote rather than until it ends (see
        :func:`_follow`), so a process a checked file left running with the
        child's output as its own does not hold the command up. The last two
        are for Linux and macOS: on Windows the child is not told that this
        process ended, is stopped with ``TerminateProcess``, which runs nothing
        in it, and has its streams copied to their end (see :func:`_watch_parent`,
        :func:`_stop` and :func:`_copy_lines`).
        """
        code = 0
        checked = 0
        facts: list[dict] = []
        with tempfile.TemporaryDirectory(prefix="lanky-check-") as scratch:
            for index, files in enumerate(groups):
                if index:
                    print()
                spec_path = Path(scratch) / f"root-{index}.json"
                results = Path(scratch) / f"root-{index}-results.json"
                spec = {
                    "files": files,
                    "verbose": verbose,
                    "show_lean": show_lean,
                    "proofs": proofs,
                    "steps": steps,
                    "facts": facts_wanted,
                    "results": str(results),
                    "path": [os.fsdecode(entry) for entry in sys.path if _is_path(entry)],
                    "argv": list(sys.argv),
                    "parent": os.getpid(),
                    "columns": terminal_columns(),
                }
                spec_path.write_text(json.dumps(spec), encoding="utf-8")
                named = ", ".join(files)
                try:
                    child = _start_child(spec_path)
                except OSError as exc:
                    print(f"lanky check: could not start a process to check {named}: {exc}")
                    code = 1
                    continue
                returncode = _follow(child)
                report = _read_report(results)
                if report is None:
                    print(
                        f"lanky check: the process checking {named} stopped with "
                        f"{_how_it_ended(returncode)} before it reported"
                    )
                    code = 1
                    continue
                checked += report["checked"]
                facts.extend(report["facts"])
                if report["code"] != returncode:
                    print(
                        f"lanky check: the process checking {named} ended with "
                        f"{_how_it_ended(returncode)} after it reported"
                    )
                if report["code"] or returncode:
                    code = 1
        return code, checked, facts

    @staticmethod
    def _report(
        ledger: Ledger,
        *,
        verbose: bool = False,
        show_lean: str | None = None,
        proofs: str | None = None,
        steps: str | None = None,
    ) -> bool:
        """Print one ledger and what follows it; whether anything failed.

        A fact fails when it is refuted or vacuous, or when another claim had
        its id (see :meth:`_report_duplicates`). A fact Lean was asked about
        and did not prove, and a refuted one whose counterexample Lean could
        not confirm, is named (see :meth:`_report_unproved`). ``--proofs``
        and ``--steps`` print the proofs lanky found (see
        :func:`report_proofs` and :func:`report_steps`), and ``--show-lean``
        prints the Lean last (see :meth:`_report_lean`); none of them fails
        the check.
        """
        print(ledger.render(columns=terminal_columns()))
        report_proved(ledger)
        report_missing(ledger)
        CheckVerb._report_citations(ledger)
        CheckVerb._report_declines(ledger)
        report_raised(ledger)
        CheckVerb._report_unproved(ledger, verbose=verbose)
        report_known(ledger)
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
        duplicated = CheckVerb._report_duplicates(ledger)
        refused = report_refused(ledger)
        broken = report_written(ledger) or refused
        refuted = ledger.by_status(Status.REFUTED)
        if refuted:
            print()
        for fact in refuted:
            print(f"REFUTED {fact.owner} at {fact.where}: {fact.statement}")
            for line in refutation_lines(fact):
                print(f"  {line}")
        if proofs is not None:
            report_proofs(ledger, proofs)
        if steps is not None:
            report_steps(ledger, steps)
        if show_lean is not None:
            CheckVerb._report_lean(ledger, show_lean)
        return bool(refuted) or vacuous or duplicated or broken

    @staticmethod
    def _report_unproved(ledger: Ledger, *, verbose: bool = False) -> None:
        """Name what Lean was asked to prove and did not (see :func:`report_unproved`)."""
        report_unproved(ledger, verbose=verbose)

    @staticmethod
    def _report_lean(ledger: Ledger, text: str = "") -> None:
        """``--show-lean`` (see :func:`report_lean`)."""
        report_lean(ledger, text)

    @staticmethod
    def _report_duplicates(ledger: Ledger) -> bool:
        """Name each definition that made several claims with one id; whether there was one.

        The claims a definition makes all have its id, and a ledger holds one
        fact per id, so :func:`lanky.check.check_path` checks the first claim
        and records the others on it, unchecked (#52). Each such definition
        gets a ``DUPLICATE`` block: the id, the claim in the table, and the
        claims that were not checked, by their statements, and then what to
        do about it. A definition that owns several facts, as a plugin's
        kernel owns one per obligation, gets one block, with the id and the
        claims of each fact under it. It fails the check, since a claim nobody
        checked could be false, and a refuted one used to be dropped this way
        without a word.
        """
        duplicated = ledger.duplicated()
        by_owner: dict[str, list[Fact]] = {}
        for fact in duplicated:
            by_owner.setdefault(fact.owner, []).append(fact)
        for owner, facts in by_owner.items():
            first = facts[0]
            print()
            if len(facts) == 1:
                claims = len(first.provenance["duplicate_claims"]) + 1
                print(
                    f"DUPLICATE {owner} at {first.where}: {claims} claims have the id "
                    f"{first.id}"
                )
                indent = "  "
            else:
                print(
                    f"DUPLICATE {owner} at {first.where}: several claims have each of "
                    f"the {len(facts)} ids below"
                )
                indent = "    "
            for fact in facts:
                if len(facts) > 1:
                    print(f"  {fact.id}")
                print(f"{indent}checked, in the table: {fact.statement}")
                for statement in fact.provenance["duplicate_claims"]:
                    print(f"{indent}not checked: {statement}")
            print(
                "  each claim needs an id of its own: a definition of its own, or a "
                "__qualname__ of its own before it is decorated"
            )
        return bool(duplicated)

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
    def _report_declines(ledger: Ledger) -> None:
        """Say why an oracle declined each fact left ``assumed``, when it said.

        A ``DECLINED`` line names the fact, and the reason the oracle recorded
        as ``declined`` is indented under it (see :func:`decline_lines`).
        Only a fact that ends ``assumed`` gets one: a fact a weaker oracle
        went on to establish or refute has its status to explain it, and an
        axiom is ``assumed`` on its citation, which its ``CITED`` line gives.
        The lines come right after those, in the table's order, since they
        explain ``assumed`` rows too. Nothing here fails the check: an
        assumed fact is a claim nobody established, not a broken one.

        A claim's reading of its annotations (:mod:`lanky.faithful`) that
        could not be checked gets a line only where something rests on it,
        a pass or a proof of the claim. Otherwise the claim is an axiom, or
        is ``assumed`` itself, and its ``CITED`` or ``DECLINED`` line says
        why it is worth nothing; a reading of a boundary no draw can be made
        of said it once more for every axiom about one.
        """
        resting = {entry for fact in ledger for entry in fact.rests_on}
        declined = [
            fact
            for fact in ledger
            if fact.status is Status.ASSUMED
            and not fact.is_axiom
            and (not fact.is_reading or fact.id in resting)
            and decline_lines(fact)
            # a script use_tactic gave that was not sent has a REFUSED line, with the fix
            and not isinstance(fact.provenance.get("tactic_refused"), dict)
        ]
        if not declined:
            return
        print()
        for fact in declined:
            print(f"DECLINED {fact.owner} at {fact.where}: {fact.statement}")
            for line in decline_lines(fact):
                print(f"  {line}")

    @staticmethod
    def _report_hypotheses(ledger: Ledger) -> bool:
        """Print what is known about hypotheses no draw satisfied; whether any are vacuous.

        A fact an oracle showed vacuous gets a ``VACUOUS`` block, and fails the
        check. One whose hypotheses no draw satisfied and no oracle could show
        inconsistent gets a ``WARNING`` line with the tester's reason under it,
        and does not: the sampler may simply not reach where they hold. So
        does one whose goal is a universal whose guard held at no valid draw,
        when no oracle could show the guard empty: the guard may hold only
        where the sampler does not look. And so does a ``tested`` fact with a
        ``reason``, which says that the pass rests on thin evidence (#55, see
        :func:`lanky.testing.thin_pass_reason`): the status stands, and the
        reason, which is the explanation in words wherever it is recorded,
        says how far it goes.
        """
        for fact in ledger:
            if fact.is_vacuous:
                continue
            unsatisfied = fact.provenance.get("unsatisfied")
            if unsatisfied:
                print()
                print(f"WARNING {fact.owner} at {fact.where}: {unsatisfied}")
                print("  no oracle could show them inconsistent, so the claim may be vacuous")
                CheckVerb._print_detail(fact)
            unreached = fact.provenance.get("goal_unreached")
            if unreached:
                print()
                print(f"WARNING {fact.owner} at {fact.where}: {unreached}")
                print("  no oracle could show it empty, so the goal may be vacuous")
            thin = fact.provenance.get("reason") if fact.status is Status.TESTED else None
            if _recorded(thin):
                first, *rest = str(thin).splitlines() or [""]
                print()
                print(f"WARNING {fact.owner} at {fact.where}: {first}")
                for line in rest:
                    print(f"  {line}")
        vacuous = ledger.vacuous()
        for fact in vacuous:
            print()
            print(f"VACUOUS {fact.owner} at {fact.where}: {fact.statement}")
            print(f"  {fact.provenance['vacuous']}, so the goal is never at stake")
            for key in ("unsatisfied", "untestable", "goal_unreached"):
                sampled = fact.provenance.get(key)
                if sampled:
                    print(f"  {sampled}")
                    break
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
        The id printed is the one that file's ledger holds the fact under,
        because an id is read off the path of the file that defines it and not
        off the name that file was imported under (see
        :func:`lanky.check.module_name`).
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


def _count(number: int, noun: str) -> str:
    """``one claim``, ``2 claims``."""
    return f"one {noun}" if number == 1 else f"{number} {noun}s"


def report_proved(ledger: Ledger) -> None:
    """Say in a line what ``proved lean`` means for the facts a solver decided.

    A plugin's fact Lean proved part by part (:mod:`lanky.obligations`) was
    decided by the plugin's solver too, and the row says only ``lean``. The
    line says, per solver, how many of the facts it decided Lean proved;
    how many it did not prove, which the ``NOT PROVED`` lines name; how
    many the plugin has no statement of for Lean yet, which ``--verbose``
    names; and what a proof means here: Lean proved the plugin's own
    statement of the claim, not the solver's result, and the solver's hints
    were checked and not trusted. Nothing is printed for a ledger with no
    such fact::

        LEAN proved 2 of the 5 facts isl decided; 3 are not stated for Lean yet
        (--verbose says why). Lean's statements are loopty's, from its own
        description, not isl's results, and isl's hints were checked, not
        trusted. --show-lean prints the Lean.

    A claim about real numbers that Lean was not asked, core Lean having no
    reals, is counted apart, with where Lean checks it::

        LEAN proved all 11 facts isl decided; 2 more are about real numbers,
        which Lean checks where Mathlib is (LANKY_LEAN_MATHLIB). ...

    The ``WITHOUT MATHLIB`` line under it names them, with the command that
    sets Mathlib up (:func:`report_missing`); with no fact a solver decided,
    it is the only line about them.
    """
    settled = (Status.PROVED, Status.CERTIFIED, Status.REFUTED)
    by_decider: dict[str, list[Fact]] = {}
    for fact in ledger:
        if fact.provenance.get("lean_parts") and fact.provenance.get("lean_decider"):
            by_decider.setdefault(str(fact.provenance["lean_decider"]), []).append(fact)
    reals = sum(
        1
        for fact in ledger
        if fact.provenance.get("lean_needs_mathlib") and fact.status not in settled
    )
    if not by_decider:
        # the claims about real numbers are named under WITHOUT MATHLIB
        return
    unstated: dict[str, int] = {}
    for fact in ledger:
        if (
            fact.decided_by in by_decider
            and not fact.provenance.get("lean_parts")
            and not fact.provenance.get("lean_needs_mathlib")
            and fact.status not in settled
            and _recorded(fact.provenance.get("lean_declined"))
        ):
            unstated[fact.decided_by] = unstated.get(fact.decided_by, 0) + 1
    print()
    for position, (decider, facts) in enumerate(by_decider.items()):
        proved = sum(fact.status in (Status.PROVED, Status.CERTIFIED) for fact in facts)
        missed = len(facts) - proved
        more = unstated.get(decider, 0)
        total = len(facts) + more
        if proved == total:
            head = (
                f"LEAN proved all {total} facts {decider} decided"
                if total > 1
                else f"LEAN proved the one fact {decider} decided"
            )
        else:
            head = f"LEAN proved {proved} of the {total} facts {decider} decided"
        clauses = []
        if missed:
            clauses.append(f"{missed} {'is' if missed == 1 else 'are'} NOT PROVED below")
        if more:
            clauses.append(
                f"{more} {'is' if more == 1 else 'are'} not stated for Lean yet "
                "(--verbose says why)"
            )
        if reals and position == 0:
            clauses.append(
                f"{reals} more {'is' if reals == 1 else 'are'} about real numbers, "
                "which Lean checks where Mathlib is (LANKY_LEAN_MATHLIB)"
            )
        authors = sorted(
            {
                str(fact.provenance["lean_stated_by"])
                for fact in facts
                if fact.provenance.get("lean_stated_by")
            }
        )
        named = " and ".join(authors) or "the plugin"
        whose = f"{named}'" if named.endswith("s") else f"{named}'s"
        print(
            "; ".join([head, *clauses])
            + f". Lean's statements are {whose}, from its own description, not "
            f"{decider}'s results, and {decider}'s hints were checked, not trusted. "
            "--show-lean prints the Lean."
        )


#: Why the rows that need each piece an oracle may say this machine lacks are
#: not proved, for its line (see :func:`report_missing`); a piece not named
#: here gets the line without a reason.
_WHY_MISSING: dict[str, tuple[str, str]] = {
    "mathlib": ("only Lean with Mathlib can state it", "only Lean with Mathlib can state them"),
    "cas": (
        "it is an induction whose steps sympy finds and Lean checks",
        "each is an induction whose steps sympy finds and Lean checks",
    ),
}

#: What each piece is called in the heading of its line.
_PIECE_NAMES = {"lean": "LEAN", "mathlib": "MATHLIB", "cas": "SYMPY"}


def report_missing(ledger: Ledger) -> None:
    """Say, a line for each, what this machine lacks for Lean to prove the rows it did not.

    Without Lean a theorem reads ``assumed`` or ``tested`` and a fact isl
    decided reads ``decided``, which says how far each is established here
    and not that Lean, installed, would prove it. An oracle that can tell
    what it lacks for a fact (:meth:`lanky.oracles.lean.LeanOracle.missing`)
    is asked about each row, and each piece some row lacks gets one line,
    in the order the oracle names them: the rows, by the names of the
    claims and a count of the rest, why they are not proved, and the
    command that installs the piece (its ``remedy``)::

        WITHOUT LEAN: compressed_taylor, on_every_triangle and 40 more rows
        are not proved. To have Lean prove what it can: pip install
        "lanky[lean]", and Lean v4.29.1 from elan (elan default
        leanprover/lean4:v4.29.1).

    Where the piece is installed and does not work, a Lean whose REPL could
    not be built, say, there is no command to give, and the line says why
    instead, as ``--verbose`` does: ``WITHOUT LEAN (<the reason>): ...``.
    The line depends on what is installed and not on why it is not, so a
    machine without Lean and a CI job with ``LANKY_LEAN_DISABLE`` print the
    same one.

    ``lanky check`` prints it under the ``LEAN`` line (:func:`report_proved`),
    and so can a plugin's verb that prints a ledger. Nothing is printed when
    nothing is lacking.
    """
    lacking: dict[str, tuple[Any, list[Fact]]] = {}
    for oracle in registry.sorted_oracles():
        if not callable(getattr(oracle, "missing", None)):
            continue
        for fact in ledger:
            try:
                pieces = oracle.missing(fact)
            except Exception:  # noqa: BLE001 - a line under the table must not stop the check
                continue
            for piece in pieces:
                lacking.setdefault(piece, (oracle, []))[1].append(fact)
    if not lacking:
        return
    print()
    for piece, (oracle, facts) in lacking.items():
        rows, many = _rows_named(facts)
        heading = f"WITHOUT {_PIECE_NAMES.get(piece, piece.upper())}"
        try:
            remedy = oracle.remedy(piece) if callable(getattr(oracle, "remedy", None)) else ""
        except Exception:  # noqa: BLE001 - as above
            remedy = ""
        if not remedy:
            # installed and not working: the reason is what there is to say
            _, reason = oracle_availability(oracle)
            if reason:
                heading += f" ({reason})"
        line = f"{heading}: {rows} {'are' if many else 'is'} not proved"
        why = _WHY_MISSING.get(piece)
        if why is not None:
            line += f", since {why[many]}"
        line += "."
        if remedy:
            what = "what it can" if piece == "lean" else ("them" if many else "it")
            line += f" To have Lean prove {what}: {remedy}."
        print(line)


def _rows_named(facts: list[Fact]) -> tuple[str, bool]:
    """The rows of a ``WITHOUT`` line in words, and whether they are more than one.

    A claim of lanky's, a theorem, is named by its owner, up to three of
    them, and the other rows are counted: ``compressed_taylor,
    on_every_triangle and 41 more rows``. A plugin's facts, a kernel's
    many, are counted and not named.
    """

    def claim(fact: Fact) -> bool:
        return bool(fact.owner) and not callable(getattr(fact.term, "lean_obligation", None))

    named = list(dict.fromkeys(fact.owner for fact in facts if claim(fact)))[:3]
    rest = sum(1 for fact in facts if not (claim(fact) and fact.owner in named))
    if not named:
        return (f"{rest} rows" if rest > 1 else "one row"), rest > 1
    if rest:
        named.append(f"{rest} more row{'s' if rest > 1 else ''}")
    words = named[0] if len(named) == 1 else ", ".join(named[:-1]) + " and " + named[-1]
    return words, len(named) > 1


#: The width of the terminal a child's parent prints to, ``None`` when it
#: prints to none (see :func:`_check_in_child`).
_PARENT_COLUMNS: int | None = None


def terminal_columns() -> int | None:
    """How wide the terminal the ledger is printed in is; ``None`` when it goes elsewhere.

    The table fits a terminal (see :meth:`lanky.ledger.Ledger.render`), and
    not a file or a pipe, so that what a transcript shows does not depend on
    the window it was made in. A child that checks the files of one source
    root (see :meth:`CheckVerb._check_in_children`) prints to a pipe its
    parent copies, and takes the width of the parent's terminal, so that its
    ledgers fit it as the parent's own would.
    """
    if _PARENT_COLUMNS is not None:
        return _PARENT_COLUMNS
    try:
        if not sys.stdout.isatty():
            return None
    except (AttributeError, ValueError):
        return None
    return shutil.get_terminal_size().columns


#: What the oracle that gave a fact its status did, for a ``NOT PROVED`` line.
_SETTLED_BY = {Status.DECIDED: "decided", Status.TESTED: "tested"}


def report_unproved(ledger: Ledger, *, verbose: bool = False) -> None:
    """Name each fact Lean was asked to prove from a plugin's statement and did not.

    ``lanky check`` prints it under the table, and so can a plugin's verb that
    prints a ledger (``loopty run`` does).

    A plugin with a decision procedure states its claims for Lean too
    (:mod:`lanky.obligations`), and Lean proves them part by part: a
    fact Lean proved reads ``proved lean``, and one it did not keeps the
    decision procedure's ``decided``. That is either a part ``omega``
    could not close, which is a disagreement between the two worth a
    look, or one Lean did not finish in its time; a ``NOT PROVED`` line
    names the fact, the parts and why, and says who decided it. A claim
    the plugin could not state for Lean, a kind of fact it has no
    statement for, is named too under ``--verbose``.

    So is a claim of lanky's own whose statement Lean's printer declines,
    which Lean is not asked about (#132): its row reads ``tested`` or
    ``assumed``, and the line says who tested it and what the printer could
    not state (``lean_declined``, see
    :meth:`lanky.oracles.lean.LeanOracle.not_taken`)::

        NOT PROVED flattening at sum_factorization.py:143: <the statement>
          property-test tested it; Lean was not asked: <the printer's reason>

    A fact left ``assumed`` whose ``DECLINED`` line gives Lean's reason
    already is not named again.
    """
    lines: list[tuple[Fact, str]] = []
    for fact in ledger:
        if fact.status in (Status.PROVED, Status.CERTIFIED, Status.REFUTED):
            continue
        reason = fact.provenance.get("lean_reason")
        if fact.provenance.get("lean_parts") and _recorded(reason):
            who = f"{fact.decided_by} decided it; " if fact.decided_by else ""
            lines.append((fact, f"{who}{reason} (--show-lean shows what Lean said)"))
            continue
        declined = fact.provenance.get("lean_declined")
        if not verbose or not _recorded(declined) or fact.is_reading or fact.is_axiom:
            continue
        if fact.status is Status.ASSUMED and str(declined) in "\n".join(decline_lines(fact)):
            continue
        how = _SETTLED_BY.get(fact.status)
        who = f"{fact.decided_by} {how} it; " if fact.decided_by and how else ""
        lines.append((fact, f"{who}Lean was not asked: {declined}"))
    if not lines:
        return
    print()
    for fact, reason in lines:
        print(f"NOT PROVED {fact.owner} at {fact.where}: {fact.statement}")
        for line in str(reason).splitlines():
            print(f"  {line}")


def report_refused(ledger: Ledger) -> bool:
    """Name each script ``use_tactic`` gave that the screen kept from Lean; whether any was.

    A script is the proof that follows ``:= by``, and one with anything a
    proof never needs (a ``#`` command, ``set_option``, a declaration) is not
    sent (:func:`lanky.audit.refusal`). Importing the file still works, and
    the claim reads as the other oracles leave it; here the script is named,
    with what was found and what to write instead::

        REFUSED scan_monotone at gauss.py:39: the script use_tactic gives it is
        not sent to Lean, since it has #exit, a Lean command.
          Fix: take #exit out; lanky writes every command around the script, and
          lanky check --show-lean prints them.

    It fails the check, as a written proof that does not hold does: the
    script is the proof the file gives, and it was not checked. The check
    records it in the claim's row (``tactic_refused``) on a machine without
    Lean too, where no oracle was asked (:func:`lanky.check.check_path`).
    """
    refused = [
        (fact, fact.provenance["tactic_refused"])
        for fact in ledger
        if isinstance(fact.provenance.get("tactic_refused"), dict)
    ]
    if not refused:
        return False
    print()
    for fact, said in refused:
        print(f"REFUSED {fact.owner} at {fact.where}: {said.get('reason')}.")
        if _recorded(said.get("fix")):
            print(f"  Fix: {said['fix']}.")
    return True


def report_written(ledger: Ledger) -> bool:
    """Report each written proof that fails, or was not checked; whether one fails.

    A theorem's body that is a proof is checked by Lean (:mod:`lanky.proofs`).
    One that fails gets a block at the line of the body that fails, in
    lanky's notation, with the fix where one can be named::

        UNPROVED every_box at every_box.py:30: a step of its proof does not follow.

          every_box.py:52    return recurrence(i, a - 2, b), claim(i, a - 2, b + 3), ...

          When a + b != 0 and a >= 2 (every_box.py:48, 50), the step needs
          R[i, a, b] == D[i, a, b]
          ...
          Fix: claim(i, a - 2, b + 2) makes the step follow (checked).

    A claim lanky proved alone keeps its row, proved by lanky's own proof,
    and the block says so instead: ``WARNING every_box at every_box.py:30:
    your proof fails at every_box.py:52; lanky proved the claim without it``.
    Either fails the check, since a broken proof is a failing test. A proof
    not checked, on a machine without Lean, or without Mathlib for a claim
    only Mathlib states, gets a ``NOT CHECKED`` line, which does not, and so
    does a proof Lean accepted with steps left open, ``by=...``, whose
    ``LEFT OPEN`` line names them.
    """
    broken = False
    for fact in ledger:
        proof = fact.provenance.get("proof") if isinstance(fact.provenance, dict) else None
        if not isinstance(proof, dict):
            continue
        if proof.get("closed") is None and _recorded(proof.get("reason")):
            print()
            if _recorded(proof.get("said")):
                print(f"NOT CHECKED {fact.owner} at {fact.where}: {proof['said']}.")
            else:
                print(
                    f"NOT CHECKED {fact.owner} at {fact.where}: its proof, {proof.get('where')}, "
                    f"was not checked: {proof['reason']}"
                )
            continue
        if proof.get("closed") == "holes":
            holes = ", ".join(str(hole) for hole in proof.get("holes") or ())
            print()
            print(
                f"LEFT OPEN {fact.owner} at {fact.where}: its proof, {proof.get('where')}, "
                f"holds but for the steps left open at {holes} (by=...); until they are "
                "written, the claim reads as the other oracles leave it"
            )
            continue
        if proof.get("closed") is not False:
            continue
        broken = True
        failures = [item for item in proof.get("failures") or () if isinstance(item, dict)]
        first = failures[0] if failures else {}
        print()
        if fact.status in (Status.PROVED, Status.CERTIFIED):
            at = first.get("where") or proof.get("where")
            print(
                f"WARNING {fact.owner} at {fact.where}: your proof fails at {at}; "
                "lanky proved the claim without it"
            )
        else:
            headline = first.get("headline") or "its proof does not hold"
            more = f" (and {len(failures) - 1} more)" if len(failures) > 1 else ""
            print(f"UNPROVED {fact.owner} at {fact.where}: {headline}{more}.")
        for failure in failures:
            print()
            if failure.get("where") and failure.get("source"):
                print(f"  {failure['where']}    {failure['source']}")
                print()
            for line in failure.get("lines") or ():
                print(f"  {line}")
            if failure.get("fix"):
                print(f"  Fix: {failure['fix']}.")
    return broken


def report_known(ledger: Ledger) -> None:
    """Name the facts of :mod:`lanky.known` that fit a claim Lean did not prove alone.

    A theorem whose row reads ``tested`` because Lean's search found no proof
    is often one known fact away from a proof: ``log(abs(alpha)) ==
    log(real(alpha * conj(alpha))) / 2`` needs the modulus squared. So
    ``lanky check`` names the facts whose shape occurs in the claim
    (:func:`lanky.suggest.suggestions`), each with the term it fits and its
    values there, and the import that brings them into a proof::

        NOT PROVED log_of_the_modulus at log_of_the_modulus.py:41: <the statement>
          Lean found no proof alone. What lanky knows of its shape:
            modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha
          A proof cites them by name: from lanky.known import modulus_squared

    Only a claim Lean was asked about and did not prove gets the line, and
    only when some fact fits: a claim no Lean could state reads ``tested``
    for another reason, which the ``WITHOUT`` lines give. A fact of
    :mod:`lanky.known` is not suggested for itself. The line does not fail the
    check, and a suggestion that cannot be made is left out without a word:
    it is help, and nothing rests on it.
    """
    found: list[tuple[Fact, list[Any]]] = []
    settled = (Status.PROVED, Status.CERTIFIED, Status.REFUTED)
    for fact in ledger:
        if fact.kind != "theorem" or fact.status in settled or fact.term is None:
            continue
        if not fact.provenance.get("lean_tried") or fact.provenance.get("lean_parts"):
            continue
        own = fact.owner if fact.id.startswith("theorem:lanky.known.") else None
        try:
            from lanky.suggest import suggestions

            fitting = suggestions(fact.term, exclude=(own,) if own else ())
        except Exception:  # noqa: BLE001 - a suggestion is help, and its failure no one's
            continue
        if fitting:
            found.append((fact, fitting))
    if not found:
        return
    print()
    for fact, fitting in found:
        print(f"NOT PROVED {fact.owner} at {fact.where}: {fact.statement}")
        print("  Lean found no proof alone. What lanky knows of its shape:")
        for suggestion in fitting:
            print(f"    {suggestion.text}")
        names = ", ".join(dict.fromkeys(suggestion.name for suggestion in fitting))
        print(f"  A proof cites them by name: from lanky.known import {names}")


def report_raised(ledger: Ledger) -> None:
    """Name each fact an oracle raised over, with the oracle and the exception (#137).

    An oracle that raises is passed over, and the fact records it as
    ``raised`` (see :func:`lanky.check.establish`). The row then reads what
    the other oracles found, ``tested`` where Lean would have proved it,
    and nothing else said that Lean was asked: a bug in one of Lean's
    strategies read as a claim Lean had not been offered. A ``RAISED`` line
    names the fact, each exception is indented under it, and the last line
    says what it means and where to look::

        RAISED scatter_total at scatter.py:40: <the statement>
          lean raised AttributeError: 'Var' object has no attribute 'free_variables'
          the oracle failed, not the claim: the row says what the other oracles
          found, and lanky check --verbose prints where it raised

    ``lanky check`` prints it under the ``DECLINED`` lines, and so can a
    plugin's verb that prints a ledger. It does not fail the check: the
    claim is as established as its row says.
    """
    raised = [fact for fact in ledger if _recorded(fact.provenance.get("raised"))]
    if not raised:
        return
    print()
    for fact in raised:
        print(f"RAISED {fact.owner} at {fact.where}: {fact.statement}")
        entries = fact.provenance["raised"]
        for entry in entries if isinstance(entries, list | tuple) else [entries]:
            for line in str(entry).splitlines():
                print(f"  {line}")
        print(
            "  the oracle failed, not the claim: the row says what the other oracles "
            "found, and lanky check --verbose prints where it raised"
        )


def report_lean(ledger: Ledger, text: str = "") -> None:
    """``--show-lean``: the Lean of every row that has some, last.

    ``lanky check`` prints it, and so can a plugin's verb that prints a
    ledger (``loopty run --show-lean`` does).

    For a row Lean proved, the file that replays the proof
    (``lean_source``); for a claim a plugin stated in parts and Lean did
    not prove, each part as it was last tried, with whether it was
    proved; for a refutation whose counterexample Lean checked, the
    theorem that the claim is false there; and for a claim of lanky's
    own Lean did not prove, its statement, without a proof. A row with
    no Lean form is left out. ``text`` keeps the rows whose owner, id or
    statement contains it. The status words of Lean appear here and
    nowhere else, which is where a reader who wants them looks.

    A theorem is named after its claim's owner, and a part's after the part
    as well, so the facts of one owner whose parts have one name declared
    theorems of one name: loopty's stencil printed ``theorem
    Lanky.jacobi_in_bounds`` once for each of its three accesses, which a
    reader could not tell apart by name and Lean would not take in one file
    (#120). Each theorem is shown under a name of its own in the ledger
    (:func:`_named_apart`): the first keeps its name, and a later one is
    shown with ``_2``, ``_3`` and on after it, counted over every row of the
    ledger whatever ``text`` keeps, so that a theorem has one name in every
    view of one ledger. Only the display changes, as for a long theorem
    shown one parameter to a line (:func:`_wrapped`): the provenance keeps
    the source Lean was given, and the proof cache the answers to it.
    """
    rows = [(fact, _lean_lines(fact)) for fact in ledger]
    shown = [(fact, body) for fact, body in rows if body]
    named = _named_apart([body for _fact, body in shown])
    blocks: list[list[str]] = []
    for (fact, _body), body in zip(shown, named, strict=True):
        fields = (fact.owner, fact.id, fact.statement)
        if text and not any(text in str(field) for field in fields):
            continue
        blocks.append([f"LEAN {fact.owner} at {fact.where}: {fact.statement}", *body])
    if not blocks:
        print()
        among = f" among those matching {text!r}" if text else ""
        print(f"LEAN no row has a Lean form{among}")
        return
    for block in blocks:
        print()
        print("\n".join(block))


def report_proofs(ledger: Ledger, text: str = "") -> None:
    """``--proofs``: the proof lanky found for each proved theorem, as a Python body where it can.

    The body is in the surface a written proof uses, in the theorem's own
    names, and pastes under the theorem's docstring: for an induction over
    families, ``def claim(a, b):`` with a case per base and the facts each
    case rests on, at the points the search found, written as the user
    writes them; for an exchange of sums, the chain through the left side
    with its sums put in order. For a proof by any other rung of the
    ladder, the rung is named. ``text`` keeps the theorems whose name, id
    or statement contains it. See :mod:`lanky.outline`.
    """
    _report_found(ledger, text, "PROOF", proof_lines)


def report_steps(ledger: Ledger, text: str = "") -> None:
    """``--steps``: the outline of the proof lanky found for each proved theorem.

    In lanky's notation, with the points the search found: for an induction,
    each case as a chain of equations from the claim's left side to its
    right, each link with the fact it follows from and the point, and the
    multiplier where it is not ``1`` or ``-1``. lanky builds the outline
    itself; nothing is read back from Lean. ``text`` keeps the theorems as
    for :func:`report_proofs`.
    """
    _report_found(ledger, text, "STEPS", step_lines)


def _report_found(ledger: Ledger, text: str, word: str, lines_of: Any) -> None:
    """Print ``lines_of`` each proved theorem whose name, id or statement contains ``text``."""
    blocks = []
    for fact in ledger:
        if fact.kind != "theorem":
            continue
        proof = fact.provenance.get("proof")
        written = word == "STEPS" and isinstance(proof, dict) and proof.get("outline")
        if fact.status not in (Status.PROVED, Status.CERTIFIED) and not written:
            continue
        fields = (fact.owner, fact.id, fact.statement)
        if text and not any(text in str(field) for field in fields):
            continue
        blocks.append(lines_of(fact))
    if not blocks:
        print()
        among = f" among those matching {text!r}" if text else ""
        print(f"{word} no theorem was proved{among}")
        return
    for block in blocks:
        print()
        print("\n".join(block))


def _files_given_as_text(args: argparse.Namespace) -> list[str]:
    """The files ``--show-lean``, ``--proofs`` or ``--steps`` took as their text.

    Each of them takes an optional text, so ``lanky check --proofs
    examples/l2p.py`` hands it the file. A text that is the path of a Python
    file that exists is taken back as a file to check, and the option as
    given with no text.
    """
    taken = []
    for option in ("show_lean", "proofs", "steps"):
        value = getattr(args, option, None)
        if value and value.endswith(".py") and Path(value).is_file():
            taken.append(value)
            setattr(args, option, "")
    return taken


def _in_the_order_given(files: list[str], argv: list[str] | None) -> list[str]:
    """``files`` in the order the command line names them.

    An option that takes an optional text takes the file after it
    (:func:`_files_given_as_text`), so ``lanky check --proofs a.py b.py``
    reads ``a.py`` last among the files; the command line puts it first,
    and files of one root share their modules, so the order is kept
    (Codex, #171). Without the command line, ``files`` as they are.
    """
    if not argv:
        return files
    position: dict[str, int] = {}
    for index, token in enumerate(argv):
        if token.startswith("--") and "=" in token:
            # an option's value written attached, --proofs=a.py
            token = token.split("=", 1)[1]
        position.setdefault(token, index)
    return sorted(files, key=lambda file: position.get(file, len(argv)))


def _by_source_roots(files: list[str]) -> list[list[str]]:
    """The files grouped by their source roots, in the order each group first appears.

    Within a group the files keep the order they were listed in (see
    :func:`lanky.check.source_roots`).
    """
    groups: dict[tuple[Path, ...], list[str]] = {}
    for file in files:
        groups.setdefault(source_roots(file), []).append(file)
    return list(groups.values())


def _is_path(entry: Any) -> bool:
    """Whether a ``sys.path`` entry is a path a child can be handed.

    ``sys.path`` should hold strings, but nothing stops a program from putting
    a ``pathlib.Path`` or bytes there, or something the import system skips.
    """
    return isinstance(entry, str | bytes | os.PathLike)


# The program a child process runs to check the files of one source root. It
# reads what to do from the file named on its command line, and takes this
# process's ``sys.path`` and ``sys.argv`` before it imports anything of
# lanky's, so it finds lanky, the plugins and every module a checked file
# imports where this process would, and a checked file that reads its command
# line reads the same one. ``-P`` keeps the working directory off its path
# until then, so that a ``json.py`` there is not what the first line imports.
_CHILD = """\
import json, sys
with open(sys.argv[1], encoding="utf-8") as handle:
    spec = json.load(handle)
sys.path[:] = spec["path"]
sys.argv[:] = spec["argv"]
from lanky.cli import _check_in_child
raise SystemExit(_check_in_child(spec))
"""


def _check_in_child(spec: dict[str, Any]) -> int:
    """Check the files of one source root, in a child process ``lanky check`` started.

    The files are checked as :meth:`CheckVerb._check_files` checks them, each
    under its heading, and what is printed goes to the parent, which copies it
    line by line; so the output is UTF-8, whatever the locale says, and
    flushed at every line. A character UTF-8 cannot carry, such as a lone
    surrogate a checked file prints, is written as its escape rather than
    failing the print. Then the exit code, how many files imported and,
    when the parent asked for them, their facts are written to the file the
    parent reads. The facts are serialized as ``--json`` serializes them, so
    the parent writes what it would have written for a check of its own.

    Before anything is checked, the child arranges to end with its parent
    (see :func:`_end_with_parent`), and takes the width of the terminal the
    parent prints to, if it prints to one, since its own output is a pipe
    (see :func:`terminal_columns`).
    """
    global _PARENT_COLUMNS
    _end_with_parent(spec["parent"])
    _PARENT_COLUMNS = spec.get("columns")
    for stream in (sys.stdout, sys.stderr):
        stream.reconfigure(encoding="utf-8", errors="backslashreplace", line_buffering=True)
    code, checked, facts = CheckVerb._check_files(
        spec["files"],
        verbose=spec["verbose"],
        headings=True,
        show_lean=spec.get("show_lean"),
        proofs=spec.get("proofs"),
        steps=spec.get("steps"),
    )
    report = {"code": code, "checked": checked, "facts": facts if spec["facts"] else []}
    Path(spec["results"]).write_text(json.dumps(report, default=str), encoding="utf-8")
    return code


#: ``PR_SET_PDEATHSIG``, the ``prctl`` option that has Linux signal a process
#: when the thread that started it ends.
_PR_SET_PDEATHSIG = 1

#: How often a child without ``PR_SET_PDEATHSIG`` asks who its parent is, in seconds.
_PARENT_POLL = 0.5


def _end_with_parent(parent: int) -> None:
    """Have this child sent ``SIGTERM`` when the ``lanky check`` that started it ends.

    A ``SIGTERM`` or a ``SIGKILL`` sent to the command's process alone, and not
    to its process group, ends it at once with nothing run on the way out, so
    it cannot pass the signal on. On Linux the kernel is asked to send the
    child ``SIGTERM`` when its parent ends (``PR_SET_PDEATHSIG``); elsewhere,
    or where that is refused, a daemon thread asks for the parent's pid twice
    a second and sends it when the parent is no longer the one that started
    the child. ``SIGTERM`` ends a child, whose checked files have not been
    imported yet, once it has killed the Lean REPLs it started (see
    :func:`_terminated`), and leaves a checked file that handles it to handle
    it.

    ``parent`` is the pid of the command's process, which the spec hands
    down: a parent that ended before either of the two was in place is
    already gone, and the child ends at once. On Windows neither works yet,
    since there a process keeps the parent's pid it was created with (see
    :func:`_watch_parent`).
    """
    signal.signal(signal.SIGTERM, functools.partial(_terminated, os.getpid()))
    if not (sys.platform.startswith("linux") and _signal_at_parent_death()):
        threading.Thread(target=_watch_parent, args=(parent,), daemon=True).start()
    if os.getppid() != parent:
        os.kill(os.getpid(), signal.SIGTERM)


def _terminated(child: int, signum: int, frame: Any) -> None:
    """End this child on ``SIGTERM``, once the Lean REPLs it started are killed.

    No signal that ends this process reaches a REPL, which would go on with
    the attempt it was given for as long as that runs (see
    :func:`lanky.oracles.lean.kill_servers`). Nothing else is run on the way
    out: the child then ends of the signal, as it would with no handler.

    Further ``SIGTERM`` is ignored meanwhile, because more can come: Linux
    sends the parent-death signal each time the thread the child is attached
    to ends, and the child is attached to the next thread of the command's
    process until the last one has ended. A process forked from the child
    (``multiprocessing``, say) inherits this handler with copies of the
    sessions, whose REPLs are the child's, and ``child``, the child's pid,
    keeps it from killing them.
    """
    signal.signal(signum, signal.SIG_IGN)
    try:
        lean = sys.modules.get("lanky.oracles.lean")
        if lean is not None and os.getpid() == child:
            lean.kill_servers()
    finally:
        signal.signal(signum, signal.SIG_DFL)
        os.kill(os.getpid(), signum)


def _signal_at_parent_death() -> bool:
    """Ask Linux to send this process ``SIGTERM`` when its parent ends; whether it agreed."""
    try:
        import ctypes

        libc = ctypes.CDLL(None, use_errno=True)
        return libc.prctl(_PR_SET_PDEATHSIG, int(signal.SIGTERM), 0, 0, 0) == 0
    except (ImportError, OSError, AttributeError):  # pragma: no cover - a libc without prctl
        return False


def _watch_parent(parent: int) -> None:  # pragma: no cover - the fallback off Linux
    """Send this process ``SIGTERM`` once its parent is no longer ``parent``.

    An orphan is handed to another parent on macOS and the other POSIX
    systems, so its parent's pid changes. Not on Windows, where
    ``os.getppid`` keeps returning the pid of the process that created this
    one after it has ended, and so this never sends it; waiting on a handle
    to the parent would.
    """
    while os.getppid() == parent:
        time.sleep(_PARENT_POLL)
    os.kill(os.getpid(), signal.SIGTERM)


def _interpreter_flags() -> list[str]:
    """This interpreter's command-line options, for a child to be started with.

    ``subprocess._args_from_interpreter_flags`` is what ``multiprocessing``
    starts its workers with: the options that ``sys.flags`` and
    ``sys.warnoptions`` record (``-O``, ``-B``, ``-E``, ``-s``, ``-W`` and the
    rest) and the ``-X`` options it knows. It is private, so a Python without
    it gets none of those, and so does a program that took out of
    ``sys.warnoptions`` an entry ``sys.flags`` implies, which the function
    refuses. Every other ``-X`` option in ``sys._xoptions``
    (``int_max_str_digits``, say, which changes what ``int`` does) is added
    after them, as it was given.
    """
    from_flags = getattr(subprocess, "_args_from_interpreter_flags", None)
    try:
        options: list[str] = list(from_flags()) if from_flags is not None else []
    except ValueError:  # pragma: no cover - sys.warnoptions edited by the program
        options = []
    for name, value in getattr(sys, "_xoptions", {}).items():
        option = name if value is True else f"{name}={value}"
        if option not in options:
            options += ["-X", option]
    return options


def _start_child(spec_path: Path) -> subprocess.Popen:
    """Start :data:`_CHILD` on a spec, with both its output streams piped here.

    The child's interpreter is this one, with its command-line options (see
    :func:`_interpreter_flags`), and ``-P``, whose reason is at :data:`_CHILD`.

    Raises:
        OSError: If the child cannot be started.
    """
    options = _interpreter_flags()
    if "-P" not in options and "-I" not in options:
        options.append("-P")
    return subprocess.Popen(
        [sys.executable, *options, "-c", _CHILD, str(spec_path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )


#: How often a thread copying a stream looks at whether the child has exited,
#: in seconds, while the stream is quiet.
_POLL = 0.1

#: The most a thread copying a stream reads at once, in bytes.
_CHUNK = 65536

#: How long a child sent ``SIGTERM`` has to end before it is sent ``SIGKILL``,
#: in seconds (see :func:`_stop`).
_STOP_GRACE = 5.0


def _follow(child: subprocess.Popen) -> int:
    """Copy a child's output here as it comes, wait for it, and return its exit code.

    Its standard output is copied to ``sys.stdout`` and its standard error to
    ``sys.stderr``, each line as the child prints it, so the ledgers appear
    as they are checked and wherever this process's output goes, which need
    not be the terminal the child would write to directly (a test capturing
    ``sys.stdout``, say). Each stream is read by a thread of its own, and
    this one waits for the child. The thread copying standard error keeps
    reading even when ``sys.stderr`` fails, so that a child writing a lot to
    it never blocks on a full pipe.

    Once the child has exited, everything it wrote is in the pipes, and a
    stream is copied up to the last byte it held then, which is the end of
    the stream unless a process the child started still has it. Such a
    process, a server a checked file left running with the child's output as
    its own, say, keeps the stream from ending, and used to hold this process
    up until it closed it. What it writes after the child has exited is read
    and dropped, never copied, so that it neither blocks on a full pipe nor
    lands among the ledgers of the roots after this one. However often it
    writes, nothing written after the child exited is waited for, and
    however slowly this process's own output takes what is copied (a pager's,
    say), nothing the child wrote is lost.

    When copying fails here, because this process's own output is closed, the
    child is stopped (see :func:`_stop`), and the exception is raised here
    once the child has been reaped and the rest of what it wrote copied; so
    is an interrupt (a ``KeyboardInterrupt`` that reached this process and
    not the child) while the child is waited for. The child would otherwise
    keep checking for no one.
    """
    assert child.stdout is not None and child.stderr is not None
    exited = threading.Event()
    failures: list[BaseException] = []
    copies: list[threading.Event] = []
    for source, sink, keep_reading in (
        (child.stdout, sys.stdout, False),
        (child.stderr, sys.stderr, True),
    ):
        copied = threading.Event()
        threading.Thread(
            target=_copy_from_child,
            args=(child, source, sink, keep_reading, exited, copied, failures),
            daemon=True,
        ).start()
        copies.append(copied)
    try:
        returncode = child.wait()
    except BaseException:
        _stop(child)
        raise
    finally:
        exited.set()
        for copied in copies:
            copied.wait()
    if failures:
        raise failures[0]
    return returncode


def _copy_from_child(
    child: subprocess.Popen,
    source: BinaryIO,
    sink: TextIO | None,
    keep_reading: bool,
    exited: threading.Event,
    copied: threading.Event,
    failures: list[BaseException],
) -> None:
    """Copy one of a child's streams, in a thread of its own (see :func:`_follow`).

    A failure to copy is kept in ``failures`` for :func:`_follow` to raise,
    and stops the child, which :func:`_follow` is waiting for. ``copied`` is
    set once nothing more will be copied, and the stream is closed once
    nothing more will be read from it.
    """
    try:
        _copy_lines(source, sink, keep_reading=keep_reading, exited=exited, copied=copied)
    except BaseException as exc:  # noqa: BLE001 - raised again by _follow
        failures.append(exc)
        _stop(child)
    finally:
        copied.set()
        try:
            source.close()
        except OSError:  # pragma: no cover - a pipe that cannot be closed is closed at exit
            pass


def _stop(child: subprocess.Popen) -> None:
    """End a child, and reap it: ``SIGTERM`` first, then ``SIGKILL`` if it is still there.

    ``SIGTERM`` has the child kill the Lean REPLs it started before it ends
    (see :func:`_terminated`), which ``SIGKILL`` would leave running; a child
    that is not gone :data:`_STOP_GRACE` seconds later, because a checked file
    handles the signal, say, is killed. On Windows ``terminate`` is
    ``TerminateProcess`` already, which runs nothing in the child, so its
    REPLs are left running there.
    """
    child.terminate()
    try:
        child.wait(timeout=_STOP_GRACE)
    except subprocess.TimeoutExpired:
        child.kill()
        child.wait()


def _copy_lines(
    source: BinaryIO,
    sink: TextIO | None,
    *,
    keep_reading: bool = False,
    exited: threading.Event | None = None,
    copied: threading.Event | None = None,
) -> None:
    """Copy lines from a child's stream to one of this process's, as they arrive.

    The child writes UTF-8 (see :func:`_check_in_child`). A byte that is not
    UTF-8, which a checked file can still write to the stream underneath, is
    copied as its escape (``\\xff``), and so is a character this process's
    stream cannot encode (an accented letter where it writes ASCII), rather
    than failing the write, which would end the check here and leave the
    roots after this one unchecked. Line endings are passed on as they are, so a
    ``\\r`` a checked file prints stays one. A sink of ``None``, which is
    what ``sys.stderr`` is where a program runs with no console, drains the
    stream without writing it anywhere.

    With ``keep_reading``, a sink that fails for any other reason (a closed
    pipe, say) is dropped and the stream is still read to its end: the
    thread copying a child's standard error must not stop while the child
    may still write to it, or the child blocks on a full pipe while this
    process waits for it.

    ``exited`` is set once the child has exited. The stream is then copied
    up to the last byte it held at that point; ``copied`` is set, and the
    rest is read to the end of the stream without being copied (see
    :func:`_follow`). A stream with no descriptor to wait on, and every
    stream on Windows, where a selector waits on sockets alone, is copied to
    its end, so that there a process the child left running with the stream
    as its own holds this process up until it closes it.
    """
    decoder = codecs.getincrementaldecoder("utf-8")(errors="backslashreplace")
    pending = ""
    for chunk in _chunks(source, exited):
        text = pending + decoder.decode(chunk)
        cut = max(text.rfind("\n"), text.rfind("\r")) + 1
        text, pending = text[:cut], text[cut:]
        if text and sink is not None:
            sink = _write_or_drop(sink, text, keep_reading)
    pending += decoder.decode(b"", final=True)
    if pending and sink is not None:
        _write_or_drop(sink, pending, keep_reading)
    if copied is not None:
        copied.set()
    _drain(source)


def _write_or_drop(sink: TextIO, text: str, keep_reading: bool) -> TextIO | None:
    """Write to a sink, and return it; with ``keep_reading``, ``None`` for one that failed."""
    try:
        _write_escaped(sink, text)
    except Exception:
        if not keep_reading:
            raise
        return None
    return sink


def _descriptor(source: BinaryIO) -> int | None:
    """The descriptor a selector can wait on for a stream, or ``None``."""
    if os.name == "nt":  # pragma: no cover - a selector takes sockets alone there
        return None
    try:
        return source.fileno()
    except (AttributeError, OSError, ValueError):
        return None


def _chunks(source: BinaryIO, exited: threading.Event | None) -> Iterator[bytes]:
    """What a child writes to a stream, as it arrives, until the last of it is read.

    Without ``exited``, or without a descriptor to wait on, until the stream
    ends. Otherwise also until the bytes the stream held when ``exited`` was
    first seen set have been read: the child had exited by then, so they are
    the last it wrote, and what comes after them was written by a process it
    left running. Where the stream cannot say how many bytes it holds, until
    it ends.
    """
    descriptor = None if exited is None else _descriptor(source)
    if exited is None or descriptor is None:
        read = getattr(source, "read1", source.read)
        while chunk := read(_CHUNK):
            yield chunk
        return
    left: int | None = None  # the bytes left of the child's, once it has exited
    seen = False
    with selectors.DefaultSelector() as selector:
        selector.register(descriptor, selectors.EVENT_READ)
        while left is None or left > 0:
            if not seen and exited.is_set():
                seen = True
                left = _unread(descriptor)
                continue
            if not selector.select(_POLL):
                continue
            chunk = os.read(descriptor, _CHUNK if left is None else min(left, _CHUNK))
            if not chunk:
                return
            if left is not None:
                left -= len(chunk)
            yield chunk


def _unread(descriptor: int) -> int | None:
    """How many bytes the pipe ``descriptor`` reads holds, or ``None`` where it cannot say."""
    try:
        import fcntl
        import termios

        held = fcntl.ioctl(descriptor, termios.FIONREAD, b"\0\0\0\0")
    except (ImportError, AttributeError, OSError):  # pragma: no cover - no FIONREAD
        return None
    return int.from_bytes(held, sys.byteorder, signed=True)


def _drain(source: BinaryIO) -> None:
    """Read a stream to its end, dropping what it holds."""
    descriptor = _descriptor(source)
    if descriptor is None:
        return
    try:
        while os.read(descriptor, _CHUNK):
            pass
    except OSError:  # pragma: no cover - a stream closed under the reader
        pass


def _write_escaped(sink: TextIO, line: str) -> None:
    """Write a line, escaping what the sink's encoding cannot carry (see :func:`_copy_lines`)."""
    try:
        sink.write(line)
    except UnicodeEncodeError:
        encoding = getattr(sink, "encoding", None) or "ascii"
        sink.write(line.encode(encoding, "backslashreplace").decode(encoding))


def _read_report(path: Path) -> dict[str, Any] | None:
    """What a child reported, or ``None`` when it stopped before it wrote a report."""
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return report if isinstance(report, dict) else None


def _how_it_ended(returncode: int) -> str:
    """A child's exit status in words: its exit code, or the signal that ended it."""
    if returncode < 0:
        return f"signal {-returncode}"
    return f"exit code {returncode}"


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

    The keys are read the same way for every plugin, and lanky knows one
    more of its own: ``lean_counterexample``, which says whether Lean proved
    the claim false at a solver's counterexample (see
    :meth:`lanky.oracles.lean.LeanOracle.establish`), and comes last. A
    plugin's own keys, such as loopty's ``witness_text``, stay in the JSON
    with the rest of the provenance. A value that prints as several lines
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
    checked = provenance.get("lean_counterexample")
    if _recorded(checked):
        lines.extend(str(checked).splitlines())
    return lines


def _indented(text: str) -> list[str]:
    """Lean source as lines indented under a header, blank lines kept blank.

    A theorem whose parameters run past a line is shown one parameter to a
    line (:func:`_wrapped`), which is the same declaration to Lean.
    """
    return [
        f"    {line}" if line.strip() else ""
        for line in _wrapped(str(text).rstrip()).splitlines()
    ]


def _wrapped(source: str, width: int = 100) -> str:
    """``source`` with each long ``theorem`` line broken before each parameter.

    A parameter is a bracketed group at the top level of the line, ``(h3 : i
    > 0)``; the statement after the last one, from `` : ``, goes on a line of
    its own. Only the display changes: the provenance keeps the source Lean
    was given, and either replays.
    """
    out: list[str] = []
    for line in source.splitlines():
        name_end = line.find(" ", len("theorem "))
        if (
            not line.startswith("theorem ")
            or len(line) <= width
            or line.startswith(" : ", name_end)
        ):
            # short enough, or a statement with no parameter to break before
            out.append(line)
            continue
        pieces: list[str] = []
        depth = 0
        start = 0
        index = 0
        while index < len(line):
            character = line[index]
            if depth == 0 and line.startswith(" : ", index) and pieces:
                break
            if character in "([{":
                if depth == 0 and line[start:index].strip():
                    pieces.append(line[start:index].rstrip())
                    start = index
                depth += 1
            elif character in ")]}":
                depth -= 1
                if depth == 0:
                    pieces.append(line[start : index + 1].strip())
                    start = index + 1
            index += 1
        rest = line[start:].strip()
        head, *params = pieces
        out.append(head)
        out.extend(f"    {param}" for param in params)
        if rest:
            out.append(f"    {rest}")
    return "\n".join(out)


#: A line of shown Lean that declares a theorem: the indent and keyword, and the name.
_DECLARATION = re.compile(r"^(\s*theorem\s+)(\S+)")


def _named_apart(bodies: list[list[str]]) -> list[list[str]]:
    """``--show-lean``'s rows with every theorem declared under a name of its own (#120).

    ``bodies`` are the rows' lines (:func:`_lean_lines`), in the ledger's
    order. A theorem whose name a row before it declared is renamed to the
    name with the first of ``_2``, ``_3``, and on, that no row declares and
    no rename took: ``Lanky.jacobi_in_bounds`` becomes
    ``Lanky.jacobi_in_bounds_2``, and a quoted name ``Lanky.«fun»`` becomes
    ``Lanky.«fun_2»``. A row names its own theorems besides declaring them,
    in the axiom audit that ends each command (``#print axioms
    _root_.Lanky.name``) and in the ``as_cited`` theorem proved from the
    claim's, ``Lanky.name.as_cited``, so a rename is made everywhere in the
    row: the name itself, and the names under it, ``Lanky.name_2.as_cited``.
    """
    declared = {
        match.group(2)
        for body in bodies
        for line in body
        if (match := _DECLARATION.match(line)) is not None
    }
    taken: set[str] = set()
    out: list[list[str]] = []
    for body in bodies:
        renames: dict[str, str] = {}
        for line in body:
            match = _DECLARATION.match(line)
            if match is None:
                continue
            name = match.group(2)
            if any(name.startswith(f"{old}.") for old in renames):
                # a theorem under a renamed one, which moves with it
                continue
            if name in taken:
                index = 2
                while (renamed := _numbered(name, index)) in declared | taken:
                    index += 1
                renames[name] = renamed
                name = renamed
            taken.add(name)
        out.append([_renamed(line, renames) for line in body] if renames else list(body))
    return out


#: A character a Lean name goes on with, after or before one it contains.
_NAME_CHARACTER = r"[\w'!?«»]"


def _renamed(line: str, renames: dict[str, str]) -> str:
    """``line`` with each name ``renames`` renames, and each name under it, renamed.

    ``Lanky.x`` is renamed where it is the whole name or the start of one,
    ``Lanky.x.as_cited``, named from the root or not, ``_root_.Lanky.x``,
    and not where it is part of another, ``Lanky.x_branch_cut_0`` or
    ``Decoy.Lanky.x``.
    """
    for old, new in renames.items():
        pattern = (
            rf"(?<![\w.'!?«»])(?P<root>_root_\.)?{re.escape(old)}(?!{_NAME_CHARACTER})"
        )
        line = re.sub(
            pattern, lambda match, new=new: f"{match.group('root') or ''}{new}", line
        )
    return line


def _numbered(name: str, index: int) -> str:
    """``name`` with ``_index`` after its last component, inside the quotes of a quoted one."""
    if name.endswith("»"):
        return f"{name[:-1]}_{index}»"
    return f"{name}_{index}"


def _lean_lines(fact: Fact) -> list[str]:
    """What ``--show-lean`` prints under one row; empty for a row with no Lean form.

    See :meth:`CheckVerb._report_lean`. A claim with a written proof
    (:mod:`lanky.proofs`) shows that proof's command too, after what proved
    the row, when it is not the same, with whether Lean accepted it.
    """
    lines = _row_lean_lines(fact)
    proof = fact.provenance.get("proof") if isinstance(fact.provenance, dict) else None
    if not isinstance(proof, dict) or not _recorded(proof.get("lean_source")):
        return lines
    if proof["lean_source"] == fact.provenance.get("lean_source") and lines:
        return lines
    state = "accepted by Lean" if proof.get("closed") else "not accepted by Lean"
    return [*lines, f"  its written proof, {proof.get('where')}, {state}",
            *_indented(proof["lean_source"])]


def _row_lean_lines(fact: Fact) -> list[str]:
    """What ``--show-lean`` prints for a row's own Lean (see :func:`_lean_lines`)."""
    provenance = fact.provenance
    source = provenance.get("lean_source")
    if fact.status in (Status.PROVED, Status.CERTIFIED) and _recorded(source):
        tactic = provenance.get("tactic")
        how = f" ({tactic})" if provenance.get("lean_parts") and _recorded(tactic) else ""
        return [f"  proved by Lean{how}", *_indented(source)]
    parts = provenance.get("lean_parts")
    if _recorded(parts):
        lines: list[str] = []
        for record in parts:
            state = "proved" if record.get("proved") else f"not proved: {record.get('reason', '')}"
            label = f" ({record['label']})" if record.get("label") else ""
            lines.append(f"  part {record.get('name')}{label}: {state}")
            if record.get("source"):
                lines.extend(_indented(record["source"]))
        return lines
    refutation = provenance.get("lean_refutation")
    if _recorded(refutation):
        how = provenance.get("lean_refuted_by")
        head = str(provenance.get("lean_counterexample", ""))
        lines = [f"  {head} (by {how})" if _recorded(how) else f"  {head}"]
        said = provenance.get("lean_counterexample_detail")
        if _recorded(said):
            lines.append(f"  Lean said: {said}")
        return [*lines, *_indented(refutation)]
    term = fact.term
    if term is None or callable(getattr(term, "lean_obligation", None)):
        return []
    from lanky.oracles.lean import claim_statement

    statement = None
    for mathlib in (False, True):
        # core Lean first, and Mathlib's dialect for a claim only it can state,
        # a real or complex one the Mathlib oracle tried (Codex)
        try:
            statement = claim_statement(fact, mathlib)
        except Exception:  # noqa: BLE001 - a statement the printer declines has no Lean form
            continue
        break
    if statement is None:
        return []
    why = provenance.get("lean_reason") or provenance.get("lean_declined")
    if not _recorded(why):
        # Lean raised over the claim itself (#137), and not over a question
        # asked about it, which is why it was not proved
        entries = provenance.get("raised") or ()
        entries = entries if isinstance(entries, list | tuple) else [entries]
        why = next(
            (
                str(entry)
                for entry in entries
                if str(entry).startswith("lean raised ") and ", while it " not in str(entry)
            ),
            None,
        )
    said = f": {why}" if _recorded(why) else ""
    return [f"  not proved by Lean{said}", *_indented(statement.source("sorry"))]


def decline_lines(fact: Fact) -> list[str]:
    """The lines ``lanky check`` prints under a fact's ``DECLINED`` line; empty for none.

    ``declined`` is the standard provenance key for a decline, read the same
    way whichever oracle or plugin recorded it, as ``reason`` is for a
    refutation (see :func:`refutation_lines`). An oracle that looks at a
    fact it was willing to try (its ``can_establish`` said yes) and finds it
    outside what it decides returns it with its status unchanged and the
    reason as ``declined``, best prefixed by its own name: the pytential
    demonstration's rule engine records ``layer-rules: the identity
    coefficient -1/2*eta mentions eta, so the verdict depends on its value``.
    An oracle that is not willing to try a kind of claim says no in
    ``can_establish`` and records nothing. A reason of several lines comes
    back as several, and a list or tuple of reasons, one per oracle, as one
    line each; an empty one is not printed.
    """
    declined = fact.provenance.get("declined")
    if not _recorded(declined):
        return []
    reasons = declined if isinstance(declined, list | tuple) else [declined]
    return [line for reason in reasons for line in str(reason).splitlines() if line.strip()]


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
    # the command line as given, for the order of the files (_in_the_order_given)
    args.argv = [str(token) for token in (sys.argv[1:] if argv is None else argv)]
    if not args.verb:
        parser.print_help()
        return 0
    return verbs[args.verb].run(args)


if __name__ == "__main__":
    raise SystemExit(main())
