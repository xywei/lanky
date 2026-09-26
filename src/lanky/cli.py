"""The ``lanky`` command: a host for verbs.

The design idea. The CLI owns argument parsing and plugin discovery and nothing
else. ``check`` is built in; every other verb arrives through the
``lanky.verbs`` entry-point group, which is how ``loopty run`` becomes a
subcommand of ``lanky`` without lanky knowing what loopty is.

``check`` exits 1 when any fact is ``REFUTED`` or vacuous, so it works in CI:
a refuted fact is a broken claim, and a vacuous one is a claim whose hypotheses
an oracle has shown inconsistent, or whose goal's guard it has shown empty
wherever the hypotheses hold, which is true and says nothing, while an assumed
one is a claim nobody got to. Every oracle reads a statement the same
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
So does a statement whose goal is a universal whose guard held at no valid
draw, when no oracle could show the guard empty.
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
import selectors
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
        groups = _by_source_roots(files)
        if len(groups) == 1:
            code, checked, facts = self._check_files(
                files, verbose=args.verbose, headings=len(files) > 1
            )
        else:
            code, checked, facts = self._check_in_children(
                groups, verbose=args.verbose, facts_wanted=bool(args.json)
            )
        if args.json and checked:
            Path(args.json).write_text(json.dumps(facts, indent=2, default=str), encoding="utf-8")
        return code

    @classmethod
    def _check_files(
        cls, files: list[str], *, verbose: bool, headings: bool
    ) -> tuple[int, int, list[dict]]:
        """Check files in this process, printing each ledger as it is done.

        Returns the exit code, how many files imported, and the facts of
        those that did. With ``headings`` each file's ledger is printed under
        a ``==> FILE <==`` line, and a blank line separates one file from the
        next.
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
            if cls._report(ledger):
                code = 1
        return code, checked, facts

    @staticmethod
    def _check_in_children(
        groups: list[list[str]], *, verbose: bool, facts_wanted: bool
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
                    "facts": facts_wanted,
                    "results": str(results),
                    "path": [os.fsdecode(entry) for entry in sys.path if _is_path(entry)],
                    "argv": list(sys.argv),
                    "parent": os.getpid(),
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
        and does not: the sampler may simply not reach where they hold. So
        does one whose goal is a universal whose guard held at no valid draw,
        when no oracle could show the guard empty: the guard may hold only
        where the sampler does not look.
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
    (see :func:`_end_with_parent`).
    """
    _end_with_parent(spec["parent"])
    for stream in (sys.stdout, sys.stderr):
        stream.reconfigure(encoding="utf-8", errors="backslashreplace", line_buffering=True)
    code, checked, facts = CheckVerb._check_files(
        spec["files"], verbose=spec["verbose"], headings=True
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
