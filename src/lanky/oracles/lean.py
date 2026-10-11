"""The Lean oracle: kernel evidence for a lanky fact.

The design idea. Lean is the platform and lanky is a language hosted on it, so a
fact Lean closes carries the strongest evidence lanky has, the trust class
``kernel``: the proof term was checked by the Lean kernel, not sampled and not
decided by a procedure lanky trusts on its word. The oracle prints the fact's
term with :mod:`lanky.lean`, opens a Lean session through ``lean_interact``, and
tries a fixed ladder of tactic scripts. A script that closes the goal becomes the
fact's provenance, alongside the Lean source, so the claim can be replayed by
hand or rechecked later by ``certify``.

Core Lean 4 by default, no Mathlib: the fragment is what :mod:`lanky.lean` can
print, and the tactics are the ones core Lean ships (``omega``, ``decide``,
``simp``, ``simp_all``, ``obtain``, ``induction``, ``by_cases``). Mathlib mode
is opt-in (see :mod:`lanky.mathlib`): with ``LANKY_LEAN_MATHLIB`` naming a Lake
project, the session imports Mathlib once and elaborates every attempt in that
environment, the statement is printed in the Mathlib dialect, and the ladder
goes on, after the core attempts, to Mathlib's tactics (``norm_num``,
``positivity``, ``ring``, ``field_simp``, ``linarith``, ``nlinarith``) and to
an induction for a reduction whose bound a natural parameter sets. A fact
proved there records the Mathlib revision it was proved against. A statement
that takes a complex logarithm or square root comes with side conditions, that
each argument stays off the function's branch cut, where Python and Lean read
it differently (see :mod:`lanky.lean`); they are proved before the statement
is tried, and one Lean cannot prove declines the statement. With the variable
unset nothing of this is consulted, and the oracle is the core one.

The ladder is not proof search. It is five cheap attempts and then one strategy
that is derived from the shape of the statement: a statement of the form "for
all ``a`` and ``b`` below a bound, with ``a <= b``, ``f a <= f b``" is proved by
induction on ``b`` with a case split on whether ``a`` has been reached yet, and
that is the shape every scan postcondition has. What makes it a strategy rather
than a hand-written proof of one theorem is that the induction variable, the
variable to split on, and the hypotheses to instantiate are all read off the
term (see :func:`induction_scripts`). The statement is the integer reading of
the lanky one (see :mod:`lanky.lean`), so a natural is an ``Int`` with ``0 ≤ b``
among its hypotheses, and the strategy trades it for a ``Nat`` before it
induces.

A fact the ladder does not close is returned unchanged, with what was tried in
its provenance, so the weaker oracles still run and the ledger still shows the
claim.

A plugin's claim is not printed from its term and sent up the ladder. Its term
offers an obligation (:mod:`lanky.obligations`): the claim in parts, each a
closed lanky term, with the hints the plugin's solver found. Each part is
proved on its own, ``omega`` first and then with its hints, the parts at once
in a pool of core sessions, and every answer of Lean's is kept by the hash of
its source (:class:`ProofCache`); a claim the solver refuted is checked at its
counterexample instead (see :meth:`LeanOracle.establish`).

Availability is a two-step story, because building the Lean REPL is slow the
first time (it clones and ``lake build``s a small project, which needs the
network) and instantaneous afterwards. :meth:`LeanOracle.availability` answers
the cheap question, whether ``lean`` is on the ``PATH`` and ``lean_interact``
imports, so that ``lanky check`` does not pay for a build just to print a
status line. The build happens on the first fact, and if it fails the reason is
remembered and reported from then on: an unavailable oracle is a clean no-op
with a one-line explanation under ``lanky check --verbose``.
"""

from __future__ import annotations

import atexit
import logging
import math
import os
import re
import shutil
import signal
import subprocess
import sys
import threading
import time
import weakref
from dataclasses import replace
from importlib.util import find_spec
from typing import Any

import pymbolic.primitives as prim

from lanky import mathlib as mathlib_mode
from lanky.deadline import Expired, deadline
from lanky.induction import (
    Case,
    Finder,
    Lemma,
    Use,
    domain_conditions,
    find_certificate,
    lemma_of,
    substitute,
    substitute_domain,
)
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    dialect,
    domain_guards,
    is_natural,
    lean_identifier,
    number_type,
    render_term,
    statement_of,
)
from lanky.ledger import Fact, Status
from lanky.obligations import (
    attempts,
    negation_source,
    obligation_of,
    part_statement,
    theorem_name,
)
from lanky.prelude import FinType, FnType, Nat, Refined
from lanky.terms import (
    Add,
    Comparison,
    Exists,
    Forall,
    Sum,
    Var,
    conjuncts,
    free_variables,
    init_args,
)

__all__ = [
    "COMBINATION_NORM",
    "LeanOracle",
    "LeanSession",
    "ProofCache",
    "decline",
    "default_cache_dir",
    "default_proof_cache_dir",
    "family_induction_scripts",
    "induction_scripts",
    "kill_servers",
    "reduction_scripts",
    "tactic_ladder",
    "use_certificate",
    "use_tactic",
]

#: Seconds one tactic attempt may take before the session is asked to give up.
DEFAULT_TIMEOUT = float(os.environ.get("LANKY_LEAN_TIMEOUT", "60"))

#: Seconds the whole ladder may take over one fact, unless ``LANKY_LEAN_BUDGET``
#: says otherwise (#83): the search for an induction's certificates, the side
#: conditions and every attempt, each attempt given what is left when it is
#: less than its timeout. Two attempts that run to the default timeout.
DEFAULT_BUDGET = 120.0

#: Seconds the ladder may take over a question whether a fact is vacuous,
#: unless ``LANKY_LEAN_VACUITY_BUDGET`` says otherwise: whether its hypotheses
#: are inconsistent, or its goal's guard empty, which a check asks after a
#: proof and whose answer is almost always no (#83).
DEFAULT_VACUITY_BUDGET = 30.0

#: The kinds of the facts that ask whether a claim is vacuous
#: (:func:`lanky.check.hypotheses_fact`, :func:`lanky.check.goal_guard_fact`).
VACUITY_KINDS = frozenset({"hypotheses", "goal-guard"})

#: What :meth:`LeanSession.run` answers for an attempt it did not send, because
#: nothing was left of the budget it was given.
BUDGET_SPENT = "the budget ran out before the attempt was sent"


def _spent(until: float | None) -> bool:
    """Whether the budget that ends at ``until``, on :func:`time.monotonic`'s clock, is spent."""
    return until is not None and time.monotonic() >= until

#: The cheap tactics, tried on the goal as printed, before any script is built.
#: The last one is for a goal ``simp_all`` reduces to linear arithmetic over
#: ``Int``: a natural is an ``Int`` with ``0 ≤ n`` as a hypothesis, so a fact
#: such as ``0 < n + 1``, which ``simp`` knows for a ``Nat``, is one for
#: ``omega`` once the hypothesis is in play.
BASE_TACTICS: tuple[str, ...] = ("omega", "decide", "simp", "simp_all", "simp_all <;> omega")

#: What a compound attempt falls back through once the context is set up. Each
#: arm has to close the goal: a ``simp_all`` that only simplifies would end the
#: ``first`` with the goal still open, and the arms after it would never run.
_CLOSERS = "first | omega | (simp_all; done) | (simp_all <;> omega)"

#: The facts about ``exp``, ``log`` and ``sqrt`` that are not in Mathlib's
#: simp set and that a statement over them most often needs: the exponential
#: of a sum or a difference, the square root of a number that is not
#: positive, which is where Mathlib's total ``Real.sqrt`` is ``0``, the
#: exponential of a complex logarithm, and the complex square root unfolded to
#: the power ``z ^ (2⁻¹ : ℂ)`` it is defined as, which is what Mathlib's simp
#: set knows about (``Complex.sqrt z ^ 2`` is ``z``).
_ELEMENTARY_LEMMAS = (
    "Real.exp_add",
    "Complex.exp_add",
    "Real.exp_sub",
    "Complex.exp_sub",
    "Real.sqrt_eq_zero'",
    "Complex.exp_log",
    "Complex.sqrt",
)


def _mathlib_tactics(lemmas: tuple[str, ...], refuting: bool = False) -> tuple[str, ...]:
    """The whole-goal attempts of Mathlib mode, with ``lemmas`` for the elementary functions.

    ``refuting`` is for a goal that is ``False`` under binders, the question
    whether a fact is vacuous: ``positivity``, ``ring``, ``field_simp`` and
    ``ring`` after ``push_cast`` close an order, an equation or what
    ``field_simp`` simplifies to one, and none of them can show ``False``
    from the hypotheses, so they are left out (#83).
    """
    tactics = (
        "norm_num",
        "positivity",
        "ring",
        "field_simp",
        "linarith",
        "nlinarith",
        "(push_cast; ring)",
        f"simp [{', '.join(lemmas)}]",
        f"simp_all [{', '.join(lemmas)}] <;> linarith",
    )
    if refuting:
        return tuple(tactic for tactic in tactics if tactic not in _CANNOT_REFUTE)
    return tactics


#: The whole-goal attempts of Mathlib mode that cannot close ``False`` (see
#: :func:`_mathlib_tactics`).
_CANNOT_REFUTE = frozenset({"positivity", "ring", "field_simp", "(push_cast; ring)"})


#: The whole-goal attempts Mathlib mode adds after :data:`BASE_TACTICS`. An
#: attempt that leaves a goal open fails as a declaration, so a tactic such as
#: ``norm_num`` that can succeed without closing needs no ``done`` here. A
#: statement with a variable named ``Real`` or ``Complex`` gets them with the
#: lemmas named from the root (see :func:`lanky.lean.global_name`).
MATHLIB_TACTICS: tuple[str, ...] = _mathlib_tactics(_ELEMENTARY_LEMMAS)

#: What closes a side condition once ``norm_num`` has computed the real and
#: imaginary parts of its argument. The condition is a disjunction,
#: ``0 < Complex.re a ∨ Complex.im a ≠ 0``, and ``norm_num`` settles a part
#: that is a constant, which leaves one side of it or nothing: ``x + 1j`` has
#: the imaginary part ``1``. A part that is not constant needs a hypothesis,
#: ``y > 0`` for ``x + y * 1j`` say, so each side is tried with the
#: arithmetic tactics, which read the hypotheses. Every arm closes the goal or
#: fails, so that ``first`` goes on to the next one.
_OFF_THE_CUT_CLOSERS = (
    "first | positivity | linarith | nlinarith "
    "| (left; positivity) | (left; linarith) | (left; nlinarith) "
    "| (right; positivity) | (right; intro; linarith) | (right; intro; nlinarith) "
    "| (right; intro; simp_all; done) | (simp_all; done)"
)

#: The attempts at a side condition (:attr:`lanky.lean.LeanStatement.side_conditions`),
#: each after an ``intros`` that brings any variable and guard the condition
#: quantifies into the context. A side condition says that a complex number is
#: off a branch cut, and is proved from the statement's hypotheses and guards
#: alone, which is what keeps it cheap: two attempts, and a statement whose
#: argument they cannot keep off the cut is declined (see :mod:`lanky.lean`).
SIDE_CONDITION_TACTICS: tuple[str, ...] = (
    f"(try norm_num) <;> {_OFF_THE_CUT_CLOSERS}",
    "simp_all",
)

#: What closes the side goal of a lemma ``simp`` rewrites with, ``a ≠ 0`` for
#: ``Complex.exp_log``, once ``simp`` has taken ``a`` apart into its real and
#: imaginary parts: what is left says that they are not both zero, ``x = 0 →
#: ¬y = 0`` for ``x + y * 1j`` or ``¬x * x + 1 = 0`` for ``x * x + 1``, and
#: the arithmetic tactics show it from the hypotheses (``y > 0``) or from
#: nothing. Every arm closes the goal or fails.
_NONZERO_CLOSERS = (
    "first | positivity | linarith | nlinarith "
    "| (intro; linarith) | (intro; nlinarith) | (intro; positivity)"
)

#: :data:`_CLOSERS`, with Mathlib's closing tactics after the core ones.
_MATHLIB_CLOSERS = (
    f"{_CLOSERS} | linarith | nlinarith | positivity | (ring_nf; done) "
    "| (push_cast; ring) | (norm_num; done)"
)


def _peel_sum(statement: LeanStatement) -> str:
    """Peel the last term off a sum over ``Finset.Ico a (b + 1)``.

    That is how a reduction's bound reads after an induction's step has
    rewritten it. Tried, never required: a goal with no such sum is left as it
    was. The lemmas are named as the statement names root declarations
    (:meth:`lanky.lean.LeanStatement.qualified`).
    """
    insert = statement.qualified("Finset.insert_Ico_right_eq_Ico_add_one")
    return f"try rw [← {insert} (by omega), {statement.qualified('Finset.sum_insert')} (by simp)]"


#: How long importing Mathlib may take when a session starts, in seconds. The
#: first import on a machine reads several gigabytes; later ones are quicker.
MATHLIB_IMPORT_TIMEOUT = float(os.environ.get("LANKY_LEAN_MATHLIB_IMPORT_TIMEOUT", "600"))


# {{{ choosing a Lean version


def _lean_interact_installed() -> bool:
    """Whether the driver is really installed, and not a leftover directory.

    An uninstall can leave an empty package directory behind, which Python
    happily reports as a namespace package with no origin. Asking for the origin
    rather than for the spec keeps the oracle from claiming availability it
    cannot back up.
    """
    try:
        spec = find_spec("lean_interact")
    except (ImportError, ValueError):  # pragma: no cover - a broken installation
        return False
    return spec is not None and spec.origin is not None


def _lean_on_path_version() -> str | None:
    """The version of the ``lean`` on the ``PATH``, as a REPL tag such as ``v4.34.0``."""
    if shutil.which("lean") is None:
        return None
    try:
        output = subprocess.run(
            ["lean", "--version"], capture_output=True, text=True, timeout=30, check=False
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    found = re.search(r"(\d+\.\d+\.\d+(?:-\w+)?)", output)
    return f"v{found.group(1)}" if found else None


def _elan_versions() -> list[str]:
    """Every Lean toolchain elan has already installed, newest first.

    A toolchain that is installed costs nothing to use; one that is not costs a
    download of several hundred megabytes, which an oracle should not start
    behind the user's back.
    """
    if shutil.which("elan") is None:
        return []
    try:
        output = subprocess.run(
            ["elan", "toolchain", "list"], capture_output=True, text=True, timeout=30, check=False
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return []
    versions = []
    for line in output.splitlines():
        found = re.search(r"lean4:v?(\d+\.\d+\.\d+(?:-\w+)?)", line)
        if found:
            versions.append(f"v{found.group(1)}")
    return sorted(set(versions), key=_version_key, reverse=True)


def _version_key(version: str) -> tuple:
    """Sort ``v4.29.1`` before ``v4.34.0``, and a release before its candidates."""
    found = re.match(r"v?(\d+)\.(\d+)\.(\d+)(?:-(\w+))?", version)
    if not found:
        return (0, 0, 0, 1, "")
    major, minor, patch, suffix = found.groups()
    return (int(major), int(minor), int(patch), 0 if suffix else 1, suffix or "")


#: The version a session settled on, so that later sessions in this process do
#: not pay again for the versions that turned out to have no REPL build.
_RESOLVED: str | None | tuple[()] = ()


def candidate_versions() -> list[str | None]:
    """The Lean versions to try, in order, when opening a session.

    The REPL lanky drives is built against one toolchain, and the toolchains the
    REPL has a build for are not all of them, so the first choice is the Lean on
    the ``PATH``, then any other toolchain elan has, then ``None``, which lets
    ``lean_interact`` pick the newest version it supports and download it.
    Whatever worked once in this process is tried first from then on: ruling a
    version out costs a git fetch, and a check run opens more than one session.
    """
    pinned = os.environ.get("LANKY_LEAN_VERSION")
    if pinned:
        return [pinned]
    candidates: list[str | None] = []
    if _RESOLVED != ():
        candidates.append(_RESOLVED)  # type: ignore[arg-type]
    on_path = _lean_on_path_version()
    if on_path is not None and on_path not in candidates:
        candidates.append(on_path)
    for version in _elan_versions():
        if version not in candidates:
            candidates.append(version)
    if None not in candidates:
        candidates.append(None)
    return candidates


# }}}


# {{{ the session


def _quieten() -> None:
    """Keep the REPL builder's progress chatter out of the ledger.

    ``lean_interact`` logs at warning level about things lanky has already
    decided to tolerate, such as a git pull that failed because the cached REPL
    checkout is a detached tag. ``lanky check`` prints a ledger, so anything
    below an error is noise; ``LANKY_LEAN_VERBOSE`` puts it back.
    """
    if os.environ.get("LANKY_LEAN_VERBOSE"):
        return
    logging.getLogger("lean_interact").setLevel(logging.ERROR)


def default_cache_dir() -> str:
    """Where the built Lean REPL is kept, and why not where the driver puts it.

    ``lean_interact`` defaults to a directory inside its own installed package,
    which means every reinstall of the package throws away a REPL that took a
    minute and a network connection to build. lanky puts it in the user's cache
    directory instead, which survives the virtual environment it was built from:
    ``$LANKY_LEAN_CACHE_DIR`` when it is set, else ``$XDG_CACHE_HOME/lanky`` or
    ``~/.cache/lanky``. The directory is not created here; the driver creates it
    when it first builds anything.
    """
    chosen = os.environ.get("LANKY_LEAN_CACHE_DIR")
    if chosen:
        return chosen
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(
        os.path.expanduser("~"), ".cache"
    )
    return os.path.join(base, "lanky", "lean-repl")


class LeanSession:
    """A Lean REPL, opened on demand and kept for the life of the process.

    Opening one means building the REPL project (minutes, and the network, the
    first time) and then starting a server (a second). Every command lanky sends
    is a whole declaration elaborated in a fresh environment, so attempts cannot
    contaminate each other and a failed tactic leaves nothing behind.

    The REPL driver kills the server when a command runs past its timeout, and
    does not start it again. A session starts it again before the next
    command, so that one slow attempt costs that attempt and not every proof
    after it in the process: the dead server used to answer every later
    command with ``The Lean server is not running``, while the session still
    reported no error and the oracle still reported itself available.

    ``mathlib`` names a Lake project with Mathlib fetched (see
    :mod:`lanky.mathlib`), and makes this a Mathlib session: the REPL runs in
    that project, Mathlib is imported once when the session starts, and every
    command is elaborated in the environment the import left, which is as
    fresh for each attempt as core Lean's empty one. The Lean version is the
    project's, not one chosen from the toolchains installed. A server started
    again after a timeout imports Mathlib again, since the import is part of
    what the session is.
    """

    def __init__(
        self,
        timeout: float = DEFAULT_TIMEOUT,
        cache_dir: str | None = None,
        mathlib: str | None = None,
    ) -> None:
        self.timeout = timeout
        self.cache_dir = cache_dir or default_cache_dir()
        self.mathlib = mathlib
        self.server: Any = None
        self.version: str | None = None
        self.error: str | None = None
        #: The REPL environment Mathlib was imported into, in a Mathlib session.
        self.environment: int | None = None
        #: The Mathlib revision the project pins, in a Mathlib session.
        self.mathlib_revision: str | None = None
        #: The REPL's process group, while the reaper watches it (see :meth:`_watch`).
        self._group: int | None = None
        #: The configuration of a running session this one is a twin of (see
        #: :meth:`twin`), whose REPL it starts again rather than setting one up.
        self._config: Any = None

    def twin(self) -> LeanSession:
        """Another core session that runs the REPL this one runs, once this one has started.

        Parts of an obligation are checked at once, a session each (see
        :meth:`LeanOracle.establish`). Setting a REPL up checks its build
        directory with git, which two sessions doing at once in one cache
        could trip over, so a twin is handed this session's configuration
        and only starts a server of its own. ``None`` before this session
        has started, and for a Mathlib session, whose import a twin would
        repeat for every part.
        """
        if self.server is None or self.mathlib is not None:
            raise ValueError("only a running core session has a twin")
        other = LeanSession(self.timeout, self.cache_dir)
        other._config = getattr(self.server, "config", None)
        other.version = self.version
        return other

    def start(self) -> bool:
        """Open the session, remembering the reason if it cannot be opened."""
        if self.server is not None:
            return True
        if self.error is not None:
            return False
        try:
            from lean_interact import LeanREPLConfig, LeanServer
        except ImportError as exc:  # pragma: no cover - guarded by availability()
            self.error = f"lean_interact does not import ({exc})"
            return False
        _quieten()
        if self._config is not None:
            try:
                self.server = LeanServer(self._config)
            except Exception as exc:  # noqa: BLE001 - a server that will not start is a reason
                self.error = f"the Lean REPL did not start ({exc})"
                return False
            self._opened()
            return True
        options: dict[str, Any] = {}
        if self.cache_dir:
            options["cache_dir"] = self.cache_dir
        if self.mathlib is not None:
            return self._start_with_mathlib(LeanREPLConfig, LeanServer, options)
        reasons = []
        for version in candidate_versions():
            try:
                config = LeanREPLConfig(lean_version=version, **options)
                self.server = LeanServer(config)
            except Exception as exc:  # noqa: BLE001 - every failure is a reason to move on
                reasons.append(f"{version or 'newest supported'}: {exc}")
                continue
            global _RESOLVED
            _RESOLVED = version
            self.version = version or getattr(config, "lean_version", None)
            self._opened()
            return True
        self.error = "no Lean REPL could be built (" + "; ".join(reasons[-2:]) + ")"
        return False

    def _start_with_mathlib(self, config_class: Any, server_class: Any, options: dict) -> bool:
        """Open a Mathlib session: the REPL in the project, and Mathlib imported.

        The project is checked cheaply first (:func:`lanky.mathlib.problem`),
        and a pinned ``LANKY_LEAN_VERSION`` that is not the project's toolchain
        is refused rather than ignored: the REPL runs the project's Lean, and a
        pin that says otherwise is a mistake worth a reason. lean-interact is
        told not to build the project, which for a Mathlib project would mean
        fetching the cache and then building: lanky's setup does the first
        (:func:`lanky.mathlib.main`) and nothing should ever do the second.
        """
        from lean_interact import LocalProject

        assert self.mathlib is not None
        reason = mathlib_mode.problem(self.mathlib)
        if reason is not None:
            self.error = reason
            return False
        directory = os.path.expanduser(self.mathlib)
        try:
            config = config_class(
                project=LocalProject(directory=directory, auto_build=False), **options
            )
        except Exception as exc:  # noqa: BLE001 - every failure is a reason to report
            self.error = f"no Lean REPL could be built for the Mathlib project ({exc})"
            return False
        version = getattr(config, "lean_version", None)
        pinned = os.environ.get("LANKY_LEAN_VERSION")
        if pinned and version and pinned.lstrip("v") != str(version).lstrip("v"):
            self.error = (
                f"LANKY_LEAN_VERSION is {pinned}, but the Mathlib project at "
                f"{self.mathlib} runs Lean {version}"
            )
            return False
        self.version = version
        self.mathlib_revision = mathlib_mode.revision(directory)
        try:
            self.server = server_class(config)
        except Exception as exc:  # noqa: BLE001 - every failure is a reason to report
            self.error = f"the Lean REPL did not start in the Mathlib project ({exc})"
            return False
        # watched from the start, since the import can take minutes
        self._watch()
        if not self._import_mathlib():
            self.close()
            return False
        self._opened()
        return True

    def _opened(self) -> None:
        """Have the server stopped on the way out of the process, and by :func:`kill_servers`.

        However the process ends: the REPL's process group is handed to this
        process's reaper first (:meth:`_watch`), whose own handler at exit is
        then registered before the session's, so that the session closes
        first, at an exit that runs anything.
        """
        self._watch()
        atexit.register(self.close)
        _OPENED.add(self)

    def _watch(self) -> None:
        """Hand the running REPL's process group to the reaper, in place of the last one.

        lean-interact starts the REPL in a session of its own, so its process
        group is its pid, and the reaper (see :func:`_reaper`) kills that group
        when this process ends, however it ends. A server that is not the
        leader of a group of its own, and one in this process's group, is not
        handed over: killing the group would kill more than the REPL.
        """
        process = getattr(self.server, "_proc", None)
        pid = getattr(process, "pid", None)
        if pid is not None and pid == self._group:
            return
        self._forget()
        if pid is None:
            return
        try:
            group = os.getpgid(pid)
            own = os.getpgrp()
        except (AttributeError, OSError):
            return
        if group == pid and group != own and _watch_group(group):
            self._group = group

    def _forget(self) -> None:
        """Take this session's REPL group back from the reaper, which then leaves it alone."""
        group, self._group = self._group, None
        if group is not None:
            _forget_group(group)

    def _import_mathlib(self) -> bool:
        """``import Mathlib`` in the running server, keeping the environment it leaves."""
        from lean_interact import Command

        try:
            response = self.server.run(
                Command(cmd="import Mathlib"), timeout=MATHLIB_IMPORT_TIMEOUT
            )
        except Exception as exc:  # noqa: BLE001 - a failed import is a reason, not a crash
            self.error = f"importing Mathlib failed ({type(exc).__name__}: {exc})"
            return False
        except BaseException:
            self._interrupted()
            raise
        message = getattr(response, "message", None)
        problems = [str(message)] if message is not None else _errors(response)
        if problems:
            self.error = f"importing Mathlib failed: {problems[0]}"
            return False
        self.environment = getattr(response, "env", None)
        return True

    def _revive(self) -> bool:
        """Start again a server the driver killed; a Mathlib session imports Mathlib again.

        A server that will not start again leaves its reason in :attr:`error`,
        which the oracle reports from then on, as it does a session that
        could not be opened.
        """
        alive = getattr(self.server, "is_alive", None)
        if alive is None or alive():
            return True
        try:
            self.server.start()
        except Exception as exc:  # noqa: BLE001 - a server that will not start is a reason
            self.error = f"the Lean REPL could not be restarted ({exc})"
            return False
        self._watch()
        if self.mathlib is None:
            return True
        return self._import_mathlib()

    def close(self) -> None:
        """Stop the Lean process, if one is running.

        Letting the interpreter collect the server instead works, but the
        collection happens during shutdown, when the modules the server's own
        finalizer uses may already be gone; closing on purpose keeps that noise
        out of a test run. The reaper is told to forget the REPL first, since
        its process group will be gone, and its number may be another's.
        """
        self._forget()
        server, self.server = self.server, None
        if server is not None:
            try:
                server.kill()
            except Exception:  # noqa: BLE001 - a session being closed cannot fail
                pass

    def _interrupted(self) -> None:
        """Stop a REPL whose command was interrupted, by Ctrl-C above all, so the process can end.

        lean-interact reads the REPL's answer in a thread of its own, which the
        interpreter waits for on its way out, before anything registered to
        run at exit, and which reads until the REPL answers. So a
        ``KeyboardInterrupt`` raised while the REPL was busy unwound
        ``lanky check`` and then left the process waiting until the attempt
        finished, a minute for a tactic bounded by heartbeats and as long as
        an unbounded one takes, with the REPL running for no one (#46). The
        REPL is stopped where the command is interrupted, which ends that
        read, and the next command starts another, as after a timeout.
        """
        self.close()

    def ready(self) -> bool:
        """Open the session, or start again the REPL a timeout killed; whether it is running.

        The oracle asks before it starts a fact's budget, so that starting the
        REPL, which in a Mathlib session imports Mathlib, is not counted
        against the first fact, or against the fact after a timeout.
        """
        return self.start() and self._revive()

    def run(self, source: str, until: float | None = None) -> tuple[bool, str]:
        """Elaborate one declaration; ``(closed, first diagnostic)``.

        A declaration is closed when Lean reports no error and no ``sorry``:
        the kernel accepted the proof term the tactics built. A command
        interrupted by anything but an error, a ``KeyboardInterrupt`` above
        all, stops the REPL (:meth:`_interrupted`) and is raised again.

        ``until`` is a time on :func:`time.monotonic`'s clock, the end of a
        budget (see :class:`LeanOracle`): the command is given what is left of
        it, when that is less than :attr:`timeout`, and is not sent at all
        when nothing is left. What is left is read after the REPL is started
        again, if a timeout killed it.
        """
        closed, detail, _ = self.answer(source, until)
        return closed, detail

    def answer(self, source: str, until: float | None = None) -> tuple[bool, str, bool]:
        """:meth:`run`, and whether the answer is Lean's own.

        The third value is true when Lean elaborated the declaration and
        accepted it or reported an error in it, which the same source will
        get again from the same Lean, and false when the command was not
        answered: it timed out, the budget was spent, or the REPL could not
        be reached. Only an answer of Lean's own may be kept for next time
        (see :class:`ProofCache`).
        """
        from lean_interact import Command

        if not self.start():
            return False, self.error or "no Lean session", False
        if not self._revive():
            return False, self.error or "no Lean session", False
        timeout = self.timeout
        if until is not None:
            left = until - time.monotonic()
            if left <= 0:
                return False, BUDGET_SPENT, False
            timeout = min(timeout, left)
        if self.mathlib is not None:
            command = Command(cmd=source, env=self.environment)
        else:
            command = Command(cmd=source)
        try:
            response = self.server.run(command, timeout=timeout)
        except Exception as exc:  # noqa: BLE001 - a timeout must not stop the ladder
            return False, f"{type(exc).__name__}: {exc}", False
        except BaseException:
            self._interrupted()
            raise
        message = getattr(response, "message", None)
        if message is not None:
            return False, str(message), False
        problems = _errors(response)
        if getattr(response, "sorries", ()):
            problems.append("the proof was accepted with a sorry in it")
        if problems:
            lines = problems[0].strip().splitlines()
            return False, lines[0] if lines else "Lean reported an error with no message", True
        return True, "", True


#: Every session that opened, for :func:`kill_servers`.
_OPENED: weakref.WeakSet[LeanSession] = weakref.WeakSet()


# {{{ the reaper

#: The program the reaper runs (see :func:`_reaper`). It reads process groups
#: from its standard input, a line each, a group to forget written with a
#: minus, and when its input ends it kills the groups it still has. It ignores
#: the signals a terminal or a ``kill`` of lanky's process group sends, so that
#: it is there when the input ends, and needs nothing but the standard library.
_REAPER_PROGRAM = """\
import os, signal, sys
for name in ("SIGINT", "SIGTERM", "SIGHUP", "SIGQUIT"):
    signal.signal(getattr(signal, name), signal.SIG_IGN)
groups = set()
for line in sys.stdin.buffer:
    word = line.strip()
    if word.startswith(b"-"):
        groups.discard(int(word[1:]))
    elif word:
        groups.add(int(word))
for group in groups:
    try:
        os.killpg(group, signal.SIGKILL)
    except OSError:
        pass
"""

#: This process's reaper, the pid of the process that started it, and the
#: groups it has been handed and not told to forget.
_REAPER: subprocess.Popen | None = None
_REAPER_OWNER: int | None = None
_WATCHED: set[int] = set()
_REAPER_LOCK = threading.Lock()


def _reaper() -> subprocess.Popen | None:
    """The process that kills this process's Lean REPLs when this process ends, however it ends.

    lean-interact starts the REPL in a session of its own, and the timeout
    of an attempt is kept by this process, so a process ended by a signal,
    which runs nothing on the way out, used to leave its REPL going on with
    the attempt it was given until the attempt finished (#46): within a
    minute for a tactic bounded by heartbeats, much longer for one that is
    not. That was ``lanky check`` of files with one root, or any program that
    calls :func:`lanky.check.check_path` or the oracle, ended by ``kill``, a
    child of ``lanky check`` sent ``SIGKILL``, and one busy in a long call that
    keeps its ``SIGTERM`` handler from running.

    The reaper is a small Python process, one per lanky process and started
    with the first REPL, that reads a pipe from this one (see
    :data:`_REAPER_PROGRAM`). The kernel closes the pipe when this process
    ends, whatever ends it, ``SIGKILL`` included, and the reaper then kills
    every REPL's process group it was handed and not told to forget. It is in
    a session of its own, so a signal sent to this process's group does not
    end it first. A process forked from this one lets go of this one's
    reaper (see :func:`_after_fork`), starts a reaper of its own for the
    REPLs it starts, and hands it none of this one's. ``None`` off
    POSIX, where there are no process groups to kill, and where the reaper
    cannot be started; the sessions then work as they did.
    """
    global _REAPER, _REAPER_OWNER
    if os.name != "posix":  # pragma: no cover - Windows has no process groups
        return None
    pid = os.getpid()
    if _REAPER_OWNER != pid:
        # a fork of the process that started the reaper: its groups are not ours
        _REAPER, _REAPER_OWNER = None, pid
        _WATCHED.clear()
    if _REAPER is not None and _REAPER.poll() is None:
        return _REAPER
    if not sys.executable:  # pragma: no cover - an embedded interpreter
        return None
    try:
        process = subprocess.Popen(
            [sys.executable, "-I", "-c", _REAPER_PROGRAM],
            stdin=subprocess.PIPE,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
    except OSError:  # pragma: no cover - no interpreter to start
        return None
    _REAPER = process
    atexit.register(_release_reaper, process)
    # a reaper started again after the last one ended is handed what that one had
    if _WATCHED and not _tell(process, "".join(f"{group}\n" for group in _WATCHED)):
        return None
    return process


def _tell(process: subprocess.Popen, text: str) -> bool:
    """Write to the reaper; whether it took it."""
    try:
        assert process.stdin is not None
        process.stdin.write(text.encode("ascii"))
        process.stdin.flush()
    except (OSError, ValueError):
        return False
    return True


def _watch_group(group: int) -> bool:
    """Hand a REPL's process group to the reaper; whether it is watched."""
    with _REAPER_LOCK:
        process = _reaper()
        if process is None or not _tell(process, f"{group}\n"):
            return False
        _WATCHED.add(group)
        return True


def _forget_group(group: int) -> None:
    """Tell the reaper to leave a process group alone: it is being stopped another way."""
    with _REAPER_LOCK:
        if group not in _WATCHED or _REAPER_OWNER != os.getpid():
            return
        _WATCHED.discard(group)
        if _REAPER is not None:
            _tell(_REAPER, f"-{group}\n")


def _after_fork() -> None:
    """In a forked process: let go of the parent's reaper, which the fork would keep waiting.

    A fork inherits the write end of the pipe the reaper reads, and the
    reaper sees the pipe close only when every process that holds it has
    ended, so with the fork still running, a parent ended by ``SIGKILL`` left
    its REPLs running until the fork ended too. The fork's copy of the pipe
    is pointed at ``/dev/null`` (closing the file object could wait on a lock
    a thread of the parent held at the fork, and closing its descriptor
    alone would leave the object to close whatever takes the number next),
    and the fork starts a reaper of its own for the REPLs it starts (see
    :func:`_reaper`). Its lock is a new one, for the same reason.
    """
    global _REAPER_LOCK
    _REAPER_LOCK = threading.Lock()
    process = _REAPER
    if process is None or process.stdin is None:
        return
    try:
        descriptor = process.stdin.fileno()
        null = os.open(os.devnull, os.O_WRONLY)
        try:
            os.dup2(null, descriptor, inheritable=False)
        finally:
            os.close(null)
    except (OSError, ValueError):  # pragma: no cover - a pipe already closed
        pass


if hasattr(os, "register_at_fork"):  # pragma: no branch - POSIX
    os.register_at_fork(after_in_child=_after_fork)


def _release_reaper(process: subprocess.Popen) -> None:
    """At an exit that runs anything: close the reaper's input, and wait for it to end.

    The sessions have closed by then and taken their groups back (see
    :meth:`LeanSession._opened`), so it ends without killing anything; a
    session still open has its REPL killed, as the session would have.
    """
    if _REAPER_OWNER != os.getpid():
        return
    try:
        if process.stdin is not None:
            process.stdin.close()
        process.wait(timeout=5)
    except (OSError, ValueError, subprocess.TimeoutExpired):
        pass


# }}}


def kill_servers() -> None:
    """Kill the Lean process of every session in this process, and everything it started.

    A session stops its own when the interpreter exits, but a process ended by
    a signal runs nothing on the way out, and lean-interact starts the REPL in
    a session of its own, which no signal sent to this process or its process
    group reaches. The REPL then goes on with the attempt it was given, however
    long that runs, since the timeout is kept by the process that is gone, and
    ends only when it next reads its input and finds it closed. A process
    about to end of a signal calls this first: a child of ``lanky check``
    does, on ``SIGTERM`` (see :func:`lanky.cli._terminated`). A process that
    ends of a signal it does not handle, ``SIGKILL`` above all, runs nothing,
    and its REPLs are killed by its reaper instead (see :func:`_reaper`),
    once the kernel has closed the pipe the reaper reads; this is the
    quicker way for one that can run something.

    So this is written for a signal handler: it sends ``SIGKILL`` to the
    REPL's process group and returns, waiting for nothing and taking no lock,
    where :meth:`LeanSession.close` waits for the REPL and closes the pipes a
    thread may be reading. A server already reaped is left alone, since its
    process id may be another process's by now. A session whose server was
    killed and that goes on starts it again before its next command, as it
    does after a timeout.
    """
    for session in list(_OPENED):
        # lean-interact keeps the process it started, ``lake env repl``, there
        process = getattr(session.server, "_proc", None)
        if process is None or getattr(process, "returncode", 0) is not None:
            continue
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (AttributeError, ProcessLookupError):
            # no process groups here, or the REPL is not the leader of one
            try:
                process.kill()
            except OSError:  # pragma: no cover - ended since it was looked at
                pass
        except OSError:  # pragma: no cover - a group that is not this user's
            pass


def _errors(response: Any) -> list[str]:
    """The error diagnostics in a REPL response."""
    return [
        str(item.data)
        for item in getattr(response, "messages", ())
        if str(getattr(item, "severity", "")).endswith("error")
    ]


# }}}


# {{{ tactic scripts derived from the statement


def _fresh(stem: str, used: set[str]) -> str:
    """A name like ``stem`` that nothing in ``used`` already answers to."""
    name = stem
    index = 1
    while name in used:
        name = f"{stem}_{index}"
        index += 1
    used.add(name)
    return name


#: The names ``intro`` and an ``rcases`` pattern read as a pattern rather than
#: as a name: ``rfl`` substitutes the equation it is given, and ``_`` (which the
#: printer writes ``«_»``, the same name) introduces nothing a script can name.
_PATTERN_NAMES = frozenset({"rfl", "_"})


def _goal_intro(
    statement: LeanStatement,
) -> tuple[list[str], list[Var], list[Any], dict[str, str], dict[str, str]]:
    """What ``intro`` must name to strip the goal's own quantifier.

    The printer emits one binder at a time with its guards right after it
    (``∀ a : Int, 0 ≤ a → a < n + 1 → ...``), so the names are a variable, its
    guards, the next variable, its guards, and the generator's own guard comes
    last. Returning the binder variables and the guards as terms as well is
    what lets a strategy decide which variable to induce on, and the fourth
    value names, for each natural variable, the hypothesis ``0 ≤ a`` that makes
    it one, which is what an induction on it has to start from. The names are
    Lean source, so a variable named like a keyword is quoted, as the printer
    quotes it (:func:`lanky.lean.lean_identifier`); the fourth value is keyed
    by the lanky name, and so is the fifth, the name each variable is
    introduced as.

    That is its own name, unless it is one that ``intro`` and ``rcases`` read
    as a pattern (:data:`_PATTERN_NAMES`): ``intro rfl`` substitutes, and fails
    on a variable, so a variable named ``rfl`` is introduced under a fresh
    name, ``x``, and a strategy names it so.

    The guards are rendered to be counted, and rendering a bound such as
    ``Fin[2 ** n]`` needs to know that ``n`` is a natural, so each binder's
    guards are rendered with the statement's own binders and the goal's
    earlier ones in scope, as the printer rendered them.
    """
    goal = statement.goal_term
    if not isinstance(goal, Forall):
        return [], [], [], {}, {}
    used = {name for name, _ in statement.binders} | {name for name, _ in statement.hypotheses}
    # every binder's name is taken before a guard is named, so that a guard of
    # an earlier binder is never named like a later one, which would shadow it
    used |= {lean_identifier(var.name) for var, _ in goal.binders}
    names: list[str] = []
    variables: list[Var] = []
    naturals: dict[str, str] = {}
    introduced: dict[str, str] = {}
    guards = list(conjuncts(goal.guard))
    scope = dict(statement.types)
    for position, (var, domain) in enumerate(goal.binders):
        if var.name in _PATTERN_NAMES:
            introduced[var.name] = _fresh("x", used)
        else:
            introduced[var.name] = lean_identifier(var.name)
        names.append(introduced[var.name])
        variables.append(var)
        conditions = domain_guards(var, domain, scope)
        scope = {**scope, var.name: domain}
        for index, _ in enumerate(conditions):
            names.append(_fresh("hd", used))
            if index == 0 and is_natural(domain):
                naturals[var.name] = names[-1]
        if position == len(goal.binders) - 1:
            for _ in guards:
                names.append(_fresh("hg", used))
    return names, variables, guards, naturals, introduced


def _induction_target(variables: list[Var], guards: list[Any]) -> tuple[Var | None, str | None]:
    """The variable to induce on, and the one to split against.

    A guard ``a <= b`` says that ``b`` is reached from ``a`` by steps, which is
    the recurrence the statement is really about, so ``b`` is the induction
    variable and ``a`` is what the successor case must compare against. With no
    such guard the last binder is induced on and nothing is split.
    """
    names = [var.name for var in variables]
    for guard in guards:
        if not isinstance(guard, prim.Comparison) or guard.operator not in ("<=", "<"):
            continue
        left, right = guard.left, guard.right
        if isinstance(right, Var) and right.name in names and isinstance(left, Var):
            return right, left.name
    return (variables[-1] if variables else None), None


def _bounded_hypotheses(statement: LeanStatement) -> list[tuple[str, int]]:
    """The hypotheses that are themselves bounded quantifiers, and their premises.

    Such a hypothesis is the recurrence (``off (r + 1) = off r + cnt r`` for
    every ``r`` below ``n``), and the successor case of an induction is exactly
    where it has to be instantiated. The count is how many premises follow the
    variable once it is applied: its domain's guards (two for a point of a
    ``Fin``) and its own generator guard. The guards are rendered with the
    statement's binders in scope, as in :func:`_goal_intro`.
    """
    found = []
    for (name, _), term in zip(statement.hypotheses, statement.hypothesis_terms, strict=False):
        if isinstance(term, Forall) and len(term.binders) == 1:
            var, domain = term.binders[0]
            premises = len(domain_guards(var, domain, statement.types))
            found.append((name, premises + len(conjuncts(term.guard))))
    return found


def induction_scripts(statement: LeanStatement) -> list[str]:
    """Tactic scripts that induce on the statement's own recurrence variable.

    Two shapes, the second a weakening of the first: induction with a case split
    on whether the other variable has been reached, and induction without it.
    Every name in them is read off the statement, so the scripts are a strategy
    and not a proof of one theorem.

    The variable is an ``Int`` with ``0 ≤ b`` among its hypotheses, because that
    is how a natural prints (see :mod:`lanky.lean`), and core Lean has no
    induction on an ``Int`` from a lower bound. So the script first trades it
    for the natural it is: ``Int.eq_ofNat_of_zero_le`` gives ``b = ↑b`` for a
    new ``Nat`` that takes the old name, and the induction is on that. In the
    successor case ``↑(k + 1)`` is rewritten to ``↑k + 1``, the form a
    recurrence instantiated at ``k`` produces, so that ``omega`` sees one atom
    where it would otherwise see two. In the base case the variable split
    against lies between ``0`` and ``↑0``, and is substituted away. A variable
    that is not a natural has nothing to trade, and is not induced on.

    A variable is named as it was introduced (see :func:`_goal_intro`), and a
    root declaration as the statement names it, ``_root_.Int`` where a
    variable is named ``Int`` (:meth:`lanky.lean.LeanStatement.qualified`).
    """
    with dialect(statement.mathlib):
        names, variables, guards, naturals, introduced = _goal_intro(statement)
    target, companion = _induction_target(variables, guards)
    if target is None or target.name not in naturals:
        return []
    induced = introduced[target.name]
    if companion is not None:
        companion = introduced[companion]
    closers = _closers(statement)
    peel = [f"  {_peel_sum(statement)}"] if _has_reduction(statement) else []
    integer, natural = statement.qualified("Int"), statement.qualified("Nat")
    used = set(names) | {name for name, _ in statement.binders}
    used |= {name for name, _ in statement.hypotheses}
    step = _fresh("k", used)
    hypothesis = _fresh("ih", used)
    cast = _fresh("hcast", used)
    instantiations = []
    for name, premises in _bounded_hypotheses(statement):
        instance = _fresh("hstep", used)
        instantiations.append(
            f"  first | (have {instance} := {name} {step}{' (by omega)' * premises}) | skip"
        )
    # The induction reverts every hypothesis that mentions the variable, and
    # the hypothesis it gets back takes them as premises again; at most every
    # name introduced after the variable, and the attempts count down from there.
    later = len(names) - names.index(induced) - 1
    applied = _fresh("hih", used)
    apply_ih = " | ".join(
        f"(have {applied} := {hypothesis}{' (by omega)' * count})"
        for count in range(later, -1, -1)
    )
    apply_ih = f"first | {apply_ih} | skip"
    zero = closers
    if companion is not None:
        pinned = _fresh("hzero", used)
        zero = (
            f"first | omega | (have {pinned} : {companion} = ((0 : {natural}) : {integer}) "
            f":= (by omega); subst {pinned}; {closers}) | (simp_all; done) "
            "| (simp_all <;> omega)"
        )
    head = [f"intro {' '.join(names)}"] if names else []
    head += [
        f"obtain ⟨{induced}, rfl⟩ := {statement.qualified('Int.eq_ofNat_of_zero_le')} "
        f"{naturals[target.name]}",
        f"induction {induced} with",
        "| zero =>",
        f"  {zero}",
        f"| succ {step} {hypothesis} =>",
        f"  have {cast} : (({step} + 1 : {natural}) : {integer}) = ({step} : {integer}) + 1 "
        ":= (by omega)",
        f"  try simp only [{cast}] at *",
    ]

    scripts = []
    if companion is not None:
        equality = _fresh("heq", used)
        less = _fresh("hlt", used)
        scripts.append(
            "\n".join(
                [
                    *head,
                    *instantiations,
                    f"  by_cases {less} : ({step} : {integer}) < {companion}",
                    f"  · have {equality} : {companion} = ({step} : {integer}) + 1 := (by omega)",
                    f"    subst {equality}",
                    f"    {closers}",
                    f"  · {apply_ih}",
                    f"    {closers}",
                ]
            )
        )
    scripts.append(
        "\n".join([*head, *instantiations, f"  {apply_ih}", *peel, f"  {closers}"])
    )
    return scripts


def _closers(statement: LeanStatement) -> str:
    """What an attempt falls back through, with Mathlib's tactics where it is imported."""
    return _MATHLIB_CLOSERS if statement.mathlib else _CLOSERS


def _reductions(term: Any) -> list[Sum]:
    """Every reduction in the body or the guard of ``term``, at any depth."""
    found: list[Sum] = []
    stack = [term]
    while stack:
        node = stack.pop()
        if isinstance(node, Sum):
            found.append(node)
        if isinstance(node, Forall | Exists | Sum):
            stack.extend(child for child in (node.body, node.guard) if child is not None)
        elif isinstance(node, prim.ExpressionNode):
            for child in init_args(node):
                stack.extend(child if isinstance(child, tuple) else (child,))
    return found


def _has_reduction(statement: LeanStatement) -> bool:
    """Whether a Mathlib statement's goal has a reduction in it to peel."""
    return statement.mathlib and bool(_reductions(statement.goal_term))


def reduction_scripts(statement: LeanStatement) -> list[str]:
    """Induction on a natural parameter that the bound of a reduction mentions.

    Mathlib mode only, and the shape of Gauss's sum: ``2 * sum(i for i in
    Fin[n + 1]) == n * (n + 1)`` has no quantified goal to induce inside, and
    what it recurs on is ``n``, a parameter of the theorem. The parameter is
    traded for the natural it is (as in :func:`induction_scripts`), the step
    rewrites ``↑(k + 1)`` to ``↑k + 1``, so that the bound reads
    ``Finset.Ico 0 (↑k + 1 + 1)``, and :func:`_peel_sum` takes the last term
    off the sum. What is left is the induction hypothesis plus a polynomial
    identity or inequality, which the closers take. The base case peels the
    one term of ``Finset.Ico 0 (↑0 + 1)`` the same way.

    A goal that is itself quantified is left to :func:`induction_scripts`.
    The natural the parameter is traded for takes its name, unless the name is
    one an ``rcases`` pattern reads as a pattern (``rfl``, see
    :data:`_PATTERN_NAMES`), and then a fresh one.
    """
    if not statement.mathlib or isinstance(statement.goal_term, Forall):
        return []
    bounds: set[str] = set()
    for reduction in _reductions(statement.goal_term):
        for _var, domain in reduction.binders:
            while isinstance(domain, Refined):
                domain = domain.base
            if isinstance(domain, FinType):
                bounds |= free_variables(domain.bound)
    used = {name for name, _ in statement.binders} | {name for name, _ in statement.hypotheses}
    closers = _closers(statement)
    peel = _peel_sum(statement)
    integer, natural = statement.qualified("Int"), statement.qualified("Nat")
    scripts = []
    # a statement built by hand may leave out the lanky names, which are then
    # the printed ones
    variables = statement.variables or tuple(name for name, _ in statement.binders)
    for position, ((printed, _sort), name) in enumerate(
        zip(statement.binders, variables, strict=True)
    ):
        if name not in bounds or not is_natural(statement.types.get(name)):
            continue
        anchors = statement.anchors or (len(statement.binders),) * len(statement.hypotheses)
        own = [
            hypothesis
            for (hypothesis, _), at, term in zip(
                statement.hypotheses,
                anchors,
                statement.hypothesis_terms or (None,) * len(statement.hypotheses),
                strict=True,
            )
            if at == position + 1 and term is None
        ]
        if not own:
            continue
        later = sum(1 for at in anchors if at > position)
        traded = _fresh("x", used) if name in _PATTERN_NAMES else printed
        step = _fresh("k", used)
        hypothesis = _fresh("ih", used)
        cast = _fresh("hcast", used)
        applied = _fresh("hih", used)
        apply_ih = " | ".join(
            f"(have {applied} := {hypothesis}{' (by omega)' * count})"
            for count in range(later, -1, -1)
        )
        scripts.append(
            "\n".join(
                [
                    f"obtain ⟨{traded}, rfl⟩ := "
                    f"{statement.qualified('Int.eq_ofNat_of_zero_le')} {own[0]}",
                    f"induction {traded} with",
                    "| zero =>",
                    f"  {peel}",
                    f"  {closers}",
                    f"| succ {step} {hypothesis} =>",
                    f"  have {cast} : (({step} + 1 : {natural}) : {integer}) = "
                    f"({step} : {integer}) + 1 := (by omega)",
                    f"  try simp only [{cast}] at *",
                    f"  first | {apply_ih} | skip",
                    f"  {peel}",
                    f"  {closers}",
                ]
            )
        )
    return scripts


#: How a linear combination is checked once it is moved to one side. The casts
#: are pushed down to the variables first, since the order a step is at is a
#: ``Nat`` inside an ``Int`` inside a ``ℝ``. Then ``ring``; ``ring_nf``, which
#: normalizes the arguments of the families too, where two uses write one
#: point differently (``R k (b + 2)`` and ``R k (2 + b)`` are different atoms
#: to ``ring``); and ``field_simp`` before ``ring`` where the multipliers or
#: the equations have denominators, on the goal as it is first, whose factored
#: denominators it knows are not zero, and then normalized.
COMBINATION_NORM = (
    "(first | ((try push_cast) <;> ring1) | ((try push_cast) <;> ring_nf <;> done) "
    "| ((try push_cast) <;> field_simp <;> ring1) "
    "| ((try push_cast) <;> ring_nf <;> field_simp <;> ring1))"
)

#: What discharges a guard of a hypothesis a certificate applies: the search
#: proposes a use only where the case's bounds show its guards as linear
#: arithmetic over the integers (see :mod:`lanky.induction`), which is
#: ``omega``'s.
_GUARD_DISCHARGER = "(by omega)"

#: The largest step a family induction is tried with: the order the goal is
#: at is ``k + step``, and the cases below it are the base.
_MAX_STEP = 4


def _family_names(statement: LeanStatement) -> frozenset[str]:
    """The statement's binders that are families, whose applications a certificate combines."""
    names = set()
    for name, sort in statement.types.items():
        while isinstance(sort, Refined):
            sort = sort.base
        if isinstance(sort, FnType):
            names.add(name)
    return frozenset(names)


def _applications(term: Any) -> list[tuple[str, tuple[Any, ...]]]:
    """Every chain of applications of a variable in ``term``, as ``(name, arguments)``."""
    found = []
    stack = [term]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Call | prim.Subscript):
            arguments: tuple[Any, ...] = ()
            head: Any = node
            while isinstance(head, prim.Call | prim.Subscript):
                if isinstance(head, prim.Call):
                    arguments = (*head.parameters, *arguments)
                    head = head.function
                else:
                    index = head.index if isinstance(head.index, tuple) else (head.index,)
                    arguments = (*index, *arguments)
                    head = head.aggregate
            if isinstance(head, prim.Variable):
                found.append((head.name, arguments))
            stack.extend(arguments)
            continue
        if isinstance(node, Forall | Exists | Sum):
            stack.extend(part for part in (node.body, node.guard) if part is not None)
        elif isinstance(node, prim.ExpressionNode):
            for child in init_args(node):
                stack.extend(child if isinstance(child, tuple) else (child,))
    return found


def _offset(argument: Any) -> tuple[str, int] | None:
    """``("a", 2)`` for the argument ``a + 2``, ``("a", 0)`` for ``a``, and ``None`` otherwise."""
    if isinstance(argument, prim.Variable):
        return argument.name, 0
    if isinstance(argument, prim.Sum):
        names = [child for child in argument.children if isinstance(child, prim.Variable)]
        constants = [
            child
            for child in argument.children
            if isinstance(child, int) and not isinstance(child, bool)
        ]
        if len(names) == 1 and len(names) + len(constants) == len(argument.children):
            return names[0].name, sum(constants)
    return None


def _steps(target: Var, goal: Forall, lemmas: list[Lemma]) -> list[int]:
    """The steps a family induction on ``target`` is tried with, smallest first.

    Read off the hypotheses: where the goal applies a family with the target
    in an argument, a hypothesis that applies the same family there at ``a +
    2`` and at ``a`` relates orders two apart, and the step is ``2``. One is
    always tried.
    """
    positions = {
        (name, index)
        for name, arguments in _applications(goal.body)
        for index, argument in enumerate(arguments)
        if target.name in free_variables(argument)
    }
    steps = {1}
    for lemma in lemmas:
        offsets: dict[str, list[int]] = {}
        for name, arguments in _applications(lemma.equation):
            for index, argument in enumerate(arguments):
                found = _offset(argument)
                if (name, index) in positions and found is not None:
                    offsets.setdefault(found[0], []).append(found[1])
        for values in offsets.values():
            spread = max(values) - min(values)
            if 0 < spread <= _MAX_STEP:
                steps.add(spread)
    return sorted(steps)


def _bounds_of(domain: Any) -> tuple[Any, Any] | None:
    """A domain's bounds on its variable, as :attr:`lanky.induction.Case.bounds` keeps them."""
    while isinstance(domain, Refined):
        domain = domain.base
    if isinstance(domain, FinType):
        return 0, domain.bound - 1
    if is_natural(domain):
        return 0, None
    return None


def family_induction_scripts(
    statement: LeanStatement, finder: Finder | None = None, until: float | None = None
) -> list[str]:
    """Induction on an order, with each case closed by a certificate a finder gives.

    Mathlib mode only, and the shape of a claim about every order: the goal is
    a universal over naturals whose body is an equation between applications
    of the statement's families, and the hypotheses that are equations, under
    universals of their own, are what may be combined (see
    :mod:`lanky.induction`). The order, a natural variable of the goal, is
    traded for the ``Nat`` it is, as in :func:`induction_scripts`, and induced
    on strongly, with the goal's other variables and guards generalized, the
    earlier ones as well as the later, so the induction hypothesis holds at
    every lower order and at any values of the others. The step size is read
    off the hypotheses (:func:`_steps`). A case below the step is the base,
    closed by one certificate for every order there, or else by one for each
    order, after ``interval_cases``; the order ``k + step`` is the step, where
    the induction hypothesis may be used too. Each certificate is checked by
    ``linear_combination``, normalized by :data:`COMBINATION_NORM`, and every
    guard of a hypothesis it applies is discharged by ``omega``.

    ``finder`` is the certificate hook (:data:`lanky.induction.Finder`),
    lanky's search (:func:`lanky.induction.find_certificate`) by default. A
    script is written for each order and step for which it gives a
    certificate for every case, in the order they are tried; lanky's search
    checks its certificates as polynomial identities first, so it gives at
    most one, while a plugin's hook may answer for a step it does not mean
    (:attr:`lanky.induction.Case.step` says which), and Lean is the judge.

    The search is Python, sympy's above all, and runs before any attempt, so
    it is counted in the fact's budget (#83): ``until``, a time on
    :func:`time.monotonic`'s clock, ends it, by an interval timer
    (:func:`lanky.deadline.deadline`) where one can be set, and the scripts
    written before then are kept.
    """
    if not statement.mathlib:
        return []
    goal = statement.goal_term
    if not isinstance(goal, Forall) or not (
        isinstance(goal.body, prim.Comparison) and goal.body.operator == "=="
    ):
        return []
    families = _family_names(statement)
    if not families:
        return []
    # a goal variable named like a parameter hides it after intro, where the
    # hypotheses still mean the parameter, and the search would confuse the two
    if {var.name for var, _ in goal.binders} & set(statement.types):
        return []
    terms = statement.hypothesis_terms or (None,) * len(statement.hypotheses)
    lemmas = [
        lemma
        for (name, _), term in zip(statement.hypotheses, terms, strict=False)
        if term is not None
        for lemma in (lemma_of(name, term),)
        if lemma is not None
    ]
    if not lemmas:
        return []
    with dialect(statement.mathlib):
        names, variables, _, naturals, introduced = _goal_intro(statement)
    shared = _FamilyGoal(goal, families, lemmas, names, variables, naturals, introduced)
    scripts: list[str] = []
    for target in variables:
        if target.name not in naturals:
            continue
        for step in _steps(target, goal, lemmas):
            left = None if until is None else until - time.monotonic()
            if left is not None and left <= 0:
                return scripts
            owner = object()
            try:
                with deadline(left, owner):
                    script = _family_induction(
                        statement, shared, target, step, finder or find_certificate
                    )
            except Expired as exc:
                if exc.owner is not owner:
                    raise
                return scripts
            if script is not None:
                scripts.append(script)
    return scripts


class _FamilyGoal:
    """What every case of one family induction shares, read off the statement once."""

    def __init__(
        self,
        goal: Forall,
        families: frozenset[str],
        lemmas: list[Lemma],
        names: list[str],
        variables: list[Var],
        naturals: dict[str, str],
        introduced: dict[str, str],
    ) -> None:
        self.goal = goal
        self.families = families
        self.lemmas = lemmas
        self.names = names
        self.variables = variables
        self.naturals = naturals
        self.introduced = introduced
        # a variable introduced under another name than its own is written so
        self.renaming = {
            var.name: Var(introduced[var.name])
            for var in variables
            if introduced[var.name] != lean_identifier(var.name)
        }


def _family_induction(
    statement: LeanStatement, shared: _FamilyGoal, target: Var, step: int, finder: Finder
) -> str | None:
    """The script for an induction on ``target`` with this step; ``None`` if a case has none."""
    goal, renaming = shared.goal, shared.renaming
    order = shared.introduced[target.name]
    # the order as the cases name it: the name it is introduced under (see _goal_intro)
    name = renaming.get(target.name, target).name
    position = shared.names.index(order)
    natural_guard = shared.naturals[target.name]
    if shared.names[position + 1] != natural_guard:
        return None
    # Only the order and the guard that makes it a natural are introduced to
    # be traded for a Nat; the rest of the goal stays as the statement binds it,
    # so the induction hypothesis takes the order's other guards, the later
    # variables and the goal's guards in the order they are printed. The
    # earlier variables are reverted before the induction, so the hypothesis
    # holds at any values of them too, and come first.
    earlier = shared.names[:position]
    later = shared.names[position + 2 :]
    used = set(shared.names) | {binder for binder, _ in statement.binders}
    used |= {hypothesis for hypothesis, _ in statement.hypotheses}
    induction_name = _fresh("ih", used)
    below = _fresh("hbase", used)
    successor = _fresh("k", used)
    smaller = _fresh("m", used)
    body = substitute(goal.body, renaming)
    domains = {var.name: domain for var, domain in goal.binders}
    index = [var.name for var, _ in goal.binders].index(target.name)

    # the names every case has in scope, and what is known of their values
    types: dict[str, Any] = dict(statement.types)
    bounds: dict[str, tuple[Any, Any]] = {}
    for variable, sort in statement.types.items():
        found = _bounds_of(sort)
        if found is not None:
            bounds[variable] = found
    for var, domain in goal.binders:
        if var.name == target.name:
            continue
        renamed = renaming.get(var.name, var).name
        types[renamed] = substitute_domain(domain, renaming)
        found = _bounds_of(types[renamed])
        if found is not None:
            bounds[renamed] = found
    # the order's own upper bound, a point of Fin[n] being at most n - 1
    _, highest = _bounds_of(substitute_domain(domains[target.name], renaming)) or (0, None)

    def induction_hypothesis(below_this: Any) -> Lemma | None:
        """The induction hypothesis, at every order below ``below_this``.

        Its premises are in the order Lean's hypothesis takes them: the
        smaller order and that it is smaller, then the earlier variables,
        each with its domain's guards, then the order's own guards beyond
        ``0 ≤ m``, then the later variables with theirs, then the goal's
        guards.
        """
        m = Var(smaller)
        values = {**renaming, target.name: m}
        premises: list[tuple[str, Any]] = [
            ("value", smaller),
            ("proof", Comparison(m, "<", below_this)),
        ]
        binders: list[tuple[Var, Any]] = [(m, Nat)]

        def generalized(var: Var, domain: Any) -> None:
            renamed = renaming.get(var.name, var)
            binders.append((renamed, substitute_domain(domain, values)))
            premises.append(("value", renamed.name))
            premises.extend(
                ("proof", substitute(guard, values)) for guard in domain_conditions(var, domain)
            )

        for var, domain in goal.binders[:index]:
            generalized(var, domain)
        own = domain_conditions(target, domains[target.name])[1:]
        premises.extend(("proof", substitute(guard, values)) for guard in own)
        for var, domain in goal.binders[index + 1 :]:
            generalized(var, domain)
        premises.extend(("proof", substitute(guard, values)) for guard in conjuncts(goal.guard))
        if len(premises) - 2 != len(earlier) + len(later):
            return None
        return Lemma(
            induction_name,
            tuple(binders),
            tuple(premises),
            substitute(goal.body, values),
            conditions=(Comparison(0, "<=", m),),
        )

    # the goal's guards, which every case has as hypotheses: a guard of a
    # lemma is shown from them too (lanky.induction.Case.facts)
    guards = [substitute(guard, renaming) for guard in conjuncts(goal.guard)]

    def case(label: str, value: Any, own: dict[str, Any], inductive: bool) -> Case | None:
        """The case where the order is ``value``; ``own`` maps its new name to its bounds."""
        lemmas = list(shared.lemmas)
        if inductive:
            hypothesis = induction_hypothesis(value)
            if hypothesis is None:
                return None
            lemmas.append(hypothesis)
        return Case(
            name=label,
            goal=substitute(body, {name: value}),
            lemmas=tuple(lemmas),
            variables={**types, **dict.fromkeys(own, Nat)},
            bounds={**bounds, **own},
            families=shared.families,
            step=step,
            order=name,
            facts=tuple(substitute(guard, {name: value}) for guard in guards),
        )

    printing = {**types, name: Nat, successor: Nat}
    # the ring the equation is in, which a multiplier is ascribed: the wider side's
    ring = number_type(Add((body.left, body.right)), printing, mathlib=True)

    def closing(this: Case | None) -> str | None:
        """The ``linear_combination`` that checks the certificate the finder gives for a case."""
        if this is None:
            return None
        try:
            uses = finder(this)
        except Exception:  # noqa: BLE001 - a hook that fails finds nothing
            return None
        if not uses:
            return None
        try:
            return _combination(statement, tuple(uses), this.lemmas, printing, ring)
        except UnsupportedTerm:
            return None

    base = closing(case("base", Var(name), {name: (0, step - 1)}, inductive=False))
    if base is not None:
        base_lines = [base]
    else:
        base_lines = [f"interval_cases {order}"]
        for value in range(step):
            closed = closing(case(str(value), value, {}, inductive=True))
            if closed is None:
                return None
            base_lines.append(f"· {closed}")
    highest_successor = None if highest is None else highest - step
    successive = closing(
        case("step", Var(successor) + step, {successor: (0, highest_successor)}, inductive=True)
    )
    if successive is None:
        return None
    lines = [
        f"intro {' '.join([*earlier, order, natural_guard])}",
        f"obtain ⟨{order}, rfl⟩ := {statement.qualified('Int.eq_ofNat_of_zero_le')} "
        f"{natural_guard}",
        f"clear {natural_guard}",
    ]
    if earlier:
        lines.append(f"revert {' '.join(earlier)}")
    lines += [
        f"induction {order} using {statement.qualified('Nat.strong_induction_on')} with",
        f"| _ {order} {induction_name} =>",
    ]
    if earlier or later:
        lines.append(f"  intro {' '.join([*earlier, *later])}")
    lines += [
        f"  by_cases {below} : {order} < {step}",
        f"  · {base_lines[0]}",
        *(f"    {line}" for line in base_lines[1:]),
        f"  · obtain ⟨{successor}, rfl⟩ : ∃ {successor} : {statement.qualified('Nat')}, "
        f"{order} = {successor} + {step} := ⟨{order} - {step}, by omega⟩",
        f"    {successive}",
    ]
    return "\n".join(lines)


def _combination(
    statement: LeanStatement,
    uses: tuple[Use, ...],
    lemmas: tuple[Lemma, ...],
    types: dict[str, Any],
    ring: str,
) -> str | None:
    """The ``linear_combination`` that checks a certificate; ``None`` if it names no lemma here.

    Each use is its lemma applied to its values, with every guard discharged
    by :data:`_GUARD_DISCHARGER`, and multiplied by its multiplier, which is
    ascribed the ring the goal is in so that Lean elaborates it there.
    """
    by_name = {lemma.name: lemma for lemma in lemmas}
    parts: list[str] = []
    # a use taken once is written first, so the combination does not open with a sign
    for use in sorted(uses, key=lambda use: not _is_number(use.multiplier, 1)):
        lemma = by_name.get(use.lemma)
        if lemma is None or len(use.arguments) != len(lemma.binders):
            return None
        values = dict(zip((var.name for var, _ in lemma.binders), use.arguments, strict=True))
        arguments = [
            render_term(values[item], types, True, statement.shadowed, atomic=True)
            if kind == "value"
            else _GUARD_DISCHARGER
            for kind, item in lemma.premises
        ]
        proof = " ".join([lemma.name, *arguments])
        multiplier = use.multiplier
        if _is_number(multiplier, 1):
            term = proof
        elif _is_number(multiplier, -1) and parts:
            parts.append(f"- {proof}")
            continue
        else:
            factor = render_term(multiplier, types, True, statement.shadowed)
            term = f"({factor} : {ring}) * ({proof})"
        parts.append(f"+ {term}" if parts else term)
    if not parts:
        return None
    return f"linear_combination (norm := {COMBINATION_NORM}) {' '.join(parts)}"


def _is_number(value: Any, number: int) -> bool:
    """Whether a multiplier is the plain number ``number``, and not a term that equals it."""
    return not isinstance(value, bool | prim.ExpressionNode) and value == number


def tactic_ladder(
    statement: LeanStatement, finder: Finder | None = None, until: float | None = None
) -> list[str]:
    """Every script the oracle tries, cheapest and most general first.

    A statement printed in the Mathlib dialect gets the core ladder first, as
    it stands but for the closers, and then Mathlib's attempts: the tactics in
    :data:`MATHLIB_TACTICS` on the whole goal, and :func:`reduction_scripts`.
    One that takes a complex logarithm or square root, which is one with side
    conditions (:attr:`lanky.lean.LeanStatement.side_conditions`), gets two
    more whole-goal attempts. ``Complex.exp_log`` holds for an argument that
    is not zero, and ``simp`` shows one is not by its real and imaginary parts
    (``Complex.ext_iff``), so that ``exp(log(x + 1j)) == x + 1j`` is proved.
    ``simp`` does not read the hypotheses there, so the second attempt is the
    same ``simp`` with a discharger that does, through the arithmetic tactics
    (:data:`_NONZERO_CLOSERS`): ``exp(log(x + y * 1j)) == x + y * 1j`` under
    ``y > 0``, and ``exp(log(x * x + 1 + 0j)) == x * x + 1 + 0j``.

    A goal that is ``False`` under binders, which is what a question whether a
    fact is vacuous asks (:data:`VACUITY_KINDS`), gets only the attempts that
    can show ``False`` from the hypotheses (#83): no induction over a family,
    on a recurrence or on a reduction's bound, none of which has an equation
    to work on, and no whole-goal tactic that closes only an equation or an
    order (:func:`_mathlib_tactics`).

    ``until``, a time on :func:`time.monotonic`'s clock, ends the search for
    the family induction's certificates (:func:`family_induction_scripts`),
    which is Python and runs here, before any attempt.
    """
    with dialect(statement.mathlib):
        names, _, _, _, _ = _goal_intro(statement)
    refuting = _goal_is_false(statement)
    ladder = list(BASE_TACTICS)
    if statement.mathlib:
        if not refuting:
            ladder += family_induction_scripts(statement, finder, until)
        lemmas = tuple(map(statement.qualified, _ELEMENTARY_LEMMAS))
        ladder += _mathlib_tactics(lemmas, refuting)
        if statement.side_conditions and not refuting:
            ext = statement.qualified("Complex.ext_iff")
            parts = ", ".join((*lemmas, ext))
            ladder.append(f"simp [{parts}]")
            ladder.append(f"simp (disch := (simp [{ext}] <;> {_NONZERO_CLOSERS})) [{parts}]")
    if names:
        introduction = f"intro {' '.join(names)}"
        ladder += [
            f"{introduction}\n{_closers(statement)}",
            f"{introduction}\nsimp_all\nomega",
        ]
    if not refuting:
        ladder += induction_scripts(statement)
        ladder += reduction_scripts(statement)
    return ladder


def _goal_is_false(statement: LeanStatement) -> bool:
    """Whether the statement's goal is ``False``, under any number of universals."""
    goal = statement.goal_term
    while isinstance(goal, Forall):
        goal = goal.body
    return goal is False


# }}}


# {{{ obligations: a plugin's claim in parts, with its solver's hints


def default_proof_cache_dir() -> str | None:
    """Where Lean's answers about obligations are kept; ``None`` when nowhere.

    ``$LANKY_LEAN_PROOF_CACHE`` when it is set, and not kept at all when it is
    ``off``; else ``proofs`` beside the REPL's build, under
    ``$XDG_CACHE_HOME/lanky`` or ``~/.cache/lanky``.
    """
    chosen = os.environ.get("LANKY_LEAN_PROOF_CACHE")
    if chosen is not None:
        return None if chosen.strip().lower() in ("", "off", "0", "no") else chosen
    base = os.environ.get("XDG_CACHE_HOME") or os.path.join(os.path.expanduser("~"), ".cache")
    return os.path.join(base, "lanky", "proofs")


def _mathlib_key(directory: str | None) -> str | None:
    """The key a Mathlib project's answers are kept under, read from its files.

    ``v4.29.1+mathlib@v4.29.1 (5e932f9...)``: the toolchain its REPL runs and
    the Mathlib its manifest pins, both known without starting a session, so
    that a warm check reads them back without one (#118). A Mathlib upgrade
    is a new key, and reads no stale answer. ``None`` when either cannot be
    read.
    """
    if directory is None:
        return None
    version = mathlib_mode.toolchain(directory)
    revision = mathlib_mode.revision(directory)
    if not version or not revision:
        return None
    return f"{version}+mathlib@{revision}"


class ProofCache:
    """Lean's answers to the declarations an obligation sends, kept by their source.

    A file checked again sends Lean the same declarations, since a kernel's
    statements change only when the kernel does, and an obligation of a few
    dozen parts is seconds of Lean each time. So each answer that is Lean's
    own (:meth:`LeanSession.answer`), a proof accepted or an error reported,
    is kept under the hash of the Lean version and the declaration's source,
    and read back instead of asked again. A timeout, a spent budget and a
    REPL that could not be reached are not kept, since asked again they may
    be answered. A part read back says so (``cached`` in its record), and its
    source is the one ``--show-lean`` prints and ``lean`` replays.
    """

    def __init__(self, directory: str | None) -> None:
        self.directory = directory

    def _path(self, version: str | None, source: str) -> str | None:
        if not self.directory:
            return None
        import hashlib

        key = hashlib.sha256(f"{version}\n{source}".encode()).hexdigest()
        return os.path.join(self.directory, key[:2], f"{key}.json")

    def get(self, version: str | None, source: str) -> tuple[bool, str] | None:
        """The answer kept for ``source`` under ``version``, or ``None``."""
        path = self._path(version, source)
        if path is None:
            return None
        try:
            with open(path, encoding="utf-8") as handle:
                import json

                record = json.load(handle)
        except (OSError, ValueError):
            return None
        if record.get("source") != source:
            return None
        return bool(record.get("closed")), str(record.get("detail", ""))

    def put(self, version: str | None, source: str, closed: bool, detail: str) -> None:
        """Keep Lean's answer; a cache that cannot be written is no cache."""
        path = self._path(version, source)
        if path is None:
            return
        import json
        import tempfile

        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            fd, scratch = tempfile.mkstemp(dir=os.path.dirname(path), suffix=".tmp")
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump(
                    {"version": version, "source": source, "closed": closed, "detail": detail},
                    handle,
                )
            os.replace(scratch, path)
        except OSError:
            return


def _fallback_attempts(part: Any, statement: LeanStatement) -> list[tuple[str, str]]:
    """The scripts a part's ``fallback`` hints make, with its own, ``omega`` alone left out.

    The fallback's hints are added to the part's, not put in their place: a
    part may need an instance of a hypothesis, which its hints give, and a
    case split, which only its fallback does, in one script.
    """
    from dataclasses import replace as replaced

    from lanky.obligations import Hints

    try:
        more = part.fallback()
    except Exception:  # noqa: BLE001 - a solver's failure is no hint
        return []
    if not more:
        return []
    own = part.hints
    hints = Hints(
        instances=(*own.instances, *more.instances),
        witness=more.witness or own.witness,
        splits=(*own.splits, *more.splits),
    )
    return [
        (how, tactic)
        for how, tactic in attempts(replaced(part, hints=hints, fallback=None), statement)
        if how != "omega"
    ]


def _jobs() -> int:
    """How many parts of an obligation Lean checks at once: ``LANKY_LEAN_JOBS``, or up to 4."""
    text = os.environ.get("LANKY_LEAN_JOBS")
    if text:
        try:
            return max(1, int(text))
        except ValueError:
            pass
    return max(1, min(4, os.cpu_count() or 1))


#: How many parts a reason names before it counts the rest.
_PARTS_SHOWN = 3


def _missed_text(records: list[dict]) -> str:
    """Why a claim was not proved, in plain words: which parts, and what Lean did.

    ``Lean ran out of time``, or ``Lean proved 3 of its 5 parts, and found no
    proof for u[t, i + 1] read by S0 after u[t + 1, i] is written by S0``. A
    part is named by its label, the plugin's words for it, and at most
    :data:`_PARTS_SHOWN` of them are named. What Lean said stays in each
    part's record, which ``--show-lean`` prints.
    """
    missed = [record for record in records if not record.get("proved")]
    if len(records) == 1:
        return f"Lean {missed[0].get('short') or missed[0].get('reason', '')}"
    by_reason: dict[str, list[str]] = {}
    for record in missed:
        short = record.get("short") or record.get("reason", "")
        by_reason.setdefault(short, []).append(record.get("label") or record["name"])
    said = []
    for short, labels in by_reason.items():
        shown = "; ".join(labels[:_PARTS_SHOWN])
        if len(labels) > _PARTS_SHOWN:
            shown += f"; and {len(labels) - _PARTS_SHOWN} more"
        said.append(f"{short} for {shown}")
    proved = len(records) - len(missed)
    return f"Lean proved {proved} of its {len(records)} parts, and {', and '.join(said)}"


def _how_text(records: list[dict]) -> str:
    """What proved the parts, in a few words: ``omega`` or ``omega, with the witness``."""
    hows = list(dict.fromkeys(record.get("how", "") for record in records if record.get("how")))
    return "; ".join(hows) if hows else "omega"


# }}}


# {{{ the oracle


class LeanOracle:
    """Establish facts by proving them in Lean, with core Lean or with Mathlib.

    A per-fact tactic override is possible through :attr:`tactics`, keyed by
    fact id, for the statement whose proof the ladder cannot find: it is an
    escape hatch and not the intended path, and the ledger records which script
    closed the goal either way.

    Which Lean is driven is read from ``LANKY_LEAN_MATHLIB`` when a session is
    wanted, not when the oracle is built, because the registered oracle is
    built when lanky is imported: unset, it is core Lean, exactly as it has
    always been, and set, it is a session in the Mathlib project the variable
    names (see :mod:`lanky.mathlib`). Each mode keeps its own session. An
    oracle given a ``session`` uses that one, in whichever mode it was made.

    Each attempt has its timeout, and the ladder as a whole has a budget
    (#83): a statement no attempt fits used to pay for every attempt, each up
    to the timeout, and in Mathlib mode that was minutes. The budget is
    ``budget`` seconds for a claim (``LANKY_LEAN_BUDGET``, by default
    :data:`DEFAULT_BUDGET`), and ``vacuity_budget`` for a question whether a
    fact is vacuous (``LANKY_LEAN_VACUITY_BUDGET``, by default
    :data:`DEFAULT_VACUITY_BUDGET`), whose answer is almost always no. It
    counts the search for an induction's certificates, the side conditions
    and the attempts, and starts once the REPL is running, so that starting
    it, which imports Mathlib, is counted against no fact. An attempt is
    given what is left of it where that is less than its timeout, and when
    nothing is left the ladder stops, and the fact says after how many of its
    attempts. ``0`` is no budget.
    """

    name = "lean"

    def __init__(
        self,
        timeout: float = DEFAULT_TIMEOUT,
        session: LeanSession | None = None,
        budget: float | None = None,
        vacuity_budget: float | None = None,
    ) -> None:
        self.timeout = timeout
        #: Seconds for the ladder of a claim; ``None`` reads ``LANKY_LEAN_BUDGET``.
        self.budget = budget
        #: Seconds for the ladder of a question whether a fact is vacuous;
        #: ``None`` reads ``LANKY_LEAN_VACUITY_BUDGET``.
        self.vacuity_budget = vacuity_budget
        self._pinned = session
        self._sessions: dict[str | None, LeanSession] = {}
        #: ``fact id -> tactic script``, consulted before the ladder.
        self.tactics: dict[str, str] = {}
        #: ``fact id -> certificate hook``, asked by the family induction in
        #: place of lanky's search (see :func:`use_certificate`).
        self.certificates: dict[str, Finder] = {}
        #: ``fact id -> reason``, for the facts this oracle leaves to the
        #: oracles after it without trying them (see :func:`decline`).
        self.declines: dict[str, str] = {}
        #: The core sessions an obligation's parts are checked in, at once
        #: (see :meth:`_establish_obligation`); the first is set up, and the
        #: others are its twins (:meth:`LeanSession.twin`).
        self._pool: list[LeanSession] = []
        #: Where Lean's answers about obligations are kept (:class:`ProofCache`);
        #: read from the environment when the first obligation is checked.
        self.proofs: ProofCache | None = None
        #: The version of the ``lean`` on the ``PATH``, asked once, which keys
        #: the cache before a session has started (:meth:`_cache_version`).
        self._on_path: tuple[str] | None = None

    @property
    def session(self) -> LeanSession:
        """The session for the mode in effect, made the first time it is asked for."""
        if self._pinned is not None:
            return self._pinned
        project = mathlib_mode.project_directory()
        session = self._sessions.get(project)
        if session is None:
            session = self._sessions[project] = LeanSession(self.timeout, mathlib=project)
        return session

    @session.setter
    def session(self, session: LeanSession) -> None:
        """Pin a session, as passing one to the constructor does.

        ``session`` was a plain attribute before Mathlib mode, and code that
        assigns one keeps working: the oracle uses it whatever the variable says.
        """
        self._pinned = session

    def trust_class(self) -> str:
        """Lean's kernel checks the proof, the strongest evidence lanky has."""
        return "kernel"

    def availability(self) -> tuple[bool, str]:
        """Whether Lean can be driven from here, and the one-line reason if not.

        The question asked here is the cheap one, and the reason says so: until
        a fact has been offered, nothing has tried to build the REPL, so the
        honest answer is "available, untested". Whether the REPL can actually be
        built is discovered on the first fact and remembered, and from then on
        this line names either the Lean version in use or the reason there is
        none. In Mathlib mode the project is looked at too, which is cheap, and
        the line names the Mathlib revision once the session is open.
        """
        if os.environ.get("LANKY_LEAN_DISABLE"):
            return False, "disabled by LANKY_LEAN_DISABLE"
        if shutil.which("lean") is None:
            return False, "lean is not on PATH"
        if not _lean_interact_installed():
            return False, 'lean_interact is not installed (pip install "lanky[lean]")'
        session = self.session
        if session.mathlib is not None:
            return self._mathlib_availability(session)
        if session.error is not None:
            return False, session.error
        if session.server is None:
            return True, "untested until the first fact: the REPL is built on demand"
        return True, f"Lean {session.version}" if session.version else ""

    @staticmethod
    def _mathlib_availability(session: LeanSession) -> tuple[bool, str]:
        """:meth:`availability` for a Mathlib session."""
        assert session.mathlib is not None
        if session.error is not None:
            return False, session.error
        problem = mathlib_mode.problem(session.mathlib)
        if problem is not None:
            return False, problem
        if session.server is None:
            return True, (
                "untested until the first fact: the REPL is built on demand, "
                f"with Mathlib from {session.mathlib}"
            )
        return True, f"Lean {session.version} with Mathlib {session.mathlib_revision}"

    def can_establish(self, fact: Fact, /) -> bool:
        """Whether the fact's statement lands in the fragment the session can read.

        Honesty here is what makes the ladder of oracles work: a reduction or a
        real-valued claim is declined at once by core Lean and reaches the
        property tester with nothing wasted. In Mathlib mode both are printed
        (see :mod:`lanky.lean`), and what is still declined is declined the
        same way.
        """
        if fact.term is None:
            return False
        if callable(getattr(fact.term, "lean_obligation", None)):
            # a plugin's claim, stated for Lean when Lean is asked (lanky.obligations)
            return True
        try:
            statement_of(fact.term, fact.owner or fact.id, mathlib=self._mathlib())
        except (UnsupportedTerm, AttributeError, TypeError, ValueError):
            return False
        return True

    def _mathlib(self) -> bool:
        """Whether the session in effect has Mathlib."""
        return self.session.mathlib is not None

    def _budget(self, fact: Fact) -> float | None:
        """The seconds the ladder may take over ``fact``; ``None`` for no budget.

        Read when the fact is offered, so that a variable set after lanky is
        imported counts.

        Raises:
            ValueError: If the variable, or the budget the oracle was made
                with, is not a finite number, ``nan`` and ``inf`` included,
                which :meth:`establish` declines the fact for, saying so: a
                budget that is no number would be no budget, and the ladder
                would run unbounded where a bound was asked for.
        """
        vacuity = fact.kind in VACUITY_KINDS
        given = self.vacuity_budget if vacuity else self.budget
        if given is not None and not math.isfinite(given):
            keyword = "vacuity_budget" if vacuity else "budget"
            raise ValueError(
                f"the oracle's {keyword} is {given!r}, which is not a finite number of seconds"
            )
        if given is None:
            variable = "LANKY_LEAN_VACUITY_BUDGET" if vacuity else "LANKY_LEAN_BUDGET"
            text = os.environ.get(variable)
            if text is None:
                given = DEFAULT_VACUITY_BUDGET if vacuity else DEFAULT_BUDGET
            else:
                try:
                    given = float(text)
                except ValueError:
                    given = math.nan
                if not math.isfinite(given):
                    raise ValueError(
                        f"{variable} is {text!r}, which is not a finite number of seconds"
                    )
        return given if given > 0 else None

    def establish(self, fact: Fact, /) -> Fact | None:
        """Try the ladder; ``PROVED`` on success, the fact unchanged otherwise.

        A statement the printer declines, or a Lean that cannot be driven, is
        returned with the reason as ``lean_declined`` and as the standard
        ``declined`` (see :func:`lanky.cli.decline_lines`). :meth:`can_establish`
        asks the printer first, so a check reaches this only when the two are
        called apart. So is a statement whose side conditions Lean cannot
        prove (:meth:`_side_conditions`), which are tried before the ladder.

        A proof records its tactic, the Lean version, and as ``lean_source``
        the file that replays it: the side conditions' theorems first, if the
        statement has any, then the statement's, after ``import Mathlib`` in
        Mathlib mode. The propositions the side conditions proved are listed
        as ``lean_side_conditions``.

        Lean's answer to each attempt is kept in the :class:`ProofCache`, as
        an obligation's are, and a claim every answer of which is kept is
        read back without starting a session (#118): the ladder is Python's,
        the same each time for the same statement, and the key is the Lean
        version a session would run, known without one (:meth:`_cache_version`,
        and a Mathlib project's toolchain and revision).
        """
        declined = self.declines.get(fact.id)
        if declined is not None:
            return fact.with_status(
                fact.status, lean_declined=declined, declined=f"{self.name}: {declined}"
            )
        if callable(getattr(fact.term, "lean_obligation", None)):
            return self._establish_obligation(fact)
        session = self.session
        mathlib = session.mathlib is not None
        try:
            statement = statement_of(fact.term, fact.owner or fact.id, mathlib=mathlib)
        except UnsupportedTerm as exc:
            return fact.with_status(
                fact.status, lean_declined=str(exc), declined=f"{self.name}: {exc}"
            )
        available, reason = self.availability()
        if not available:
            return fact.with_status(
                fact.status, lean_declined=reason, declined=f"{self.name}: {reason}"
            )
        try:
            budget = self._budget(fact)
        except ValueError as exc:
            return fact.with_status(
                fact.status, lean_declined=str(exc), declined=f"{self.name}: {exc}"
            )
        until = None if budget is None else time.monotonic() + budget
        if self.proofs is None:
            self.proofs = ProofCache(default_proof_cache_dir())
        # the ladder is Python's, and the same whether Lean is asked or the cache
        override = self.tactics.get(fact.id)
        if override is not None:
            ladder = [override]
        else:
            ladder = tactic_ladder(statement, self.certificates.get(fact.id), until)
        if mathlib:
            key = _mathlib_key(session.mathlib)
        elif self._pinned is not None:
            # a session handed to the oracle is the Lean that answers
            key = session.version
        else:
            key = self._cache_version()
        if key is not None:
            kept = self._claim_from_cache(fact, statement, ladder, key)
            if kept is not None:
                return kept
        if not session.ready():
            return fact.with_status(fact.status, lean_tried=0, lean_reason=session.error)
        conditions, declined = self._side_conditions(statement, until)
        if declined is not None:
            if session.error is not None:
                return fact.with_status(fact.status, lean_tried=0, lean_reason=session.error)
            if _spent(until):
                return fact.with_status(
                    fact.status,
                    lean_tried=0,
                    lean_budget=budget,
                    lean_reason=(
                        f"the ladder's budget of {budget:g} s ran out while the statement's "
                        "side conditions were tried"
                    ),
                )
            return fact.with_status(
                fact.status, lean_declined=declined, declined=f"{self.name}: {declined}"
            )
        last = ""
        tried = 0
        for tactic in ladder:
            if _spent(until):
                break
            source = statement.source(tactic)
            closed, detail, _cached, _answered = self._ask(session, source, until)
            if detail == BUDGET_SPENT:
                break
            tried += 1
            if closed:
                return self._proved_claim(
                    fact, statement, tactic, source, conditions, session.version
                )
            last = detail
            if session.error is not None:
                break
        if session.error is None and tried < len(ladder):
            spent = (
                f"the ladder's budget of {budget:g} s ran out after {tried} of its "
                f"{len(ladder)} attempts"
            )
            return fact.with_status(
                fact.status,
                lean_tried=tried,
                lean_budget=budget,
                lean_reason=f"{spent}; the last: {last}" if last else spent,
            )
        return fact.with_status(
            fact.status,
            lean_tried=tried,
            lean_reason=session.error or last,
        )

    def _proved_claim(
        self,
        fact: Fact,
        statement: LeanStatement,
        tactic: str,
        source: str,
        conditions: list[str],
        version: str | None,
    ) -> Fact:
        """``fact`` proved by ``tactic``, with the file that replays the proof."""
        extra: dict[str, Any] = {}
        if conditions:
            source = "\n".join((*conditions, source))
            extra["lean_side_conditions"] = [
                condition.proposition for condition in statement.side_conditions
            ]
        if statement.mathlib:
            # the file that replays it, which the REPL command, run in the
            # environment the import left, could not spell
            source = f"import Mathlib\n\n{source}"
            directory = self.session.mathlib
            extra["lean_mathlib"] = self.session.mathlib_revision or (
                mathlib_mode.revision(directory) if directory else None
            )
        return fact.with_status(
            Status.PROVED,
            self.name,
            tactic=tactic,
            lean_source=source,
            lean_version=version,
            **extra,
        )

    def _claim_from_cache(
        self, fact: Fact, statement: LeanStatement, ladder: list[str], key: str
    ) -> Fact | None:
        """``fact`` as the kept answers settle it, or ``None`` if Lean has to be asked (#118).

        The side conditions and the ladder are walked as :meth:`establish`
        walks them, each attempt's answer read from the cache under ``key``:
        the first attempt that closed proves the claim, and every attempt
        kept as failed leaves it as Lean left it. An attempt the cache does
        not hold, or a side condition no kept attempt proved, sends the
        claim to Lean.
        """
        cache = self.proofs
        if cache is None:
            return None
        conditions: list[str] = []
        for condition in statement.side_conditions:
            closing = None
            for tactic in SIDE_CONDITION_TACTICS:
                source = condition.source(f"intros\n{tactic}")
                kept = cache.get(key, source)
                if kept is None:
                    return None
                if kept[0]:
                    closing = source
                    break
            if closing is None:
                return None
            conditions.append(closing)
        last = ""
        for tactic in ladder:
            source = statement.source(tactic)
            kept = cache.get(key, source)
            if kept is None:
                return None
            closed, detail = kept
            if closed:
                version = key
                if statement.mathlib:
                    directory = self.session.mathlib
                    version = mathlib_mode.toolchain(directory) if directory else None
                return self._proved_claim(
                    fact, statement, tactic, source, conditions, version
                )
            last = detail
        return fact.with_status(fact.status, lean_tried=len(ladder), lean_reason=last)

    def _side_conditions(
        self, statement: LeanStatement, until: float | None = None
    ) -> tuple[list[str], str | None]:
        """Prove a statement's side conditions, before the statement itself is tried.

        A side condition is what makes the printed statement mean in Lean what
        the lanky one means in Python: that the argument of a complex logarithm
        or square root is off its branch cut (see :mod:`lanky.lean`). Each is
        tried with :data:`SIDE_CONDITION_TACTICS`. The sources that proved them
        come back, to be kept with the proof, or, at the first one no attempt
        closes, why the statement is declined: a proof of it would be a proof
        of what Lean reads on the cut, which is not what Python computes there.
        ``until`` is the end of the fact's budget, which they count against.
        """
        session = self.session
        proved: list[str] = []
        for condition in statement.side_conditions:
            closing = None
            for tactic in SIDE_CONDITION_TACTICS:
                source = condition.source(f"intros\n{tactic}")
                closed, _detail, _cached, _answered = self._ask(session, source, until)
                if closed:
                    closing = source
                    break
                if session.error is not None:
                    return proved, session.error
                if _spent(until):
                    return proved, BUDGET_SPENT
            if closing is None:
                return proved, (
                    f"Lean could not prove {condition.proposition}, so the statement "
                    "may take a complex logarithm or square root on its branch cut, "
                    "where cmath picks a side by the sign of a zero imaginary part "
                    "and Lean's complex numbers have no signed zero, or the "
                    "logarithm of zero, which has no value in Python"
                )
            proved.append(closing)
        return proved, None

    # {{{ obligations

    def _establish_obligation(self, fact: Fact) -> Fact:
        """Check the claim a plugin states for Lean (:mod:`lanky.obligations`).

        Every part is proved on its own, ``omega`` first and then with the
        part's hints, the parts at once in a pool of sessions
        (``LANKY_LEAN_JOBS``, up to four), each attempt within the oracle's
        timeout and all of them within the fact's budget, as the ladder's
        are. When every part is proved the fact is ``proved`` by ``lean``,
        resting besides on what the obligation names as its hypotheses, and
        its provenance has the file that replays the proof (``lean_source``),
        a record of each part (``lean_parts``: how it was proved, in how many
        seconds, and whether the answer was read from the
        :class:`ProofCache`), and the solver that decided it and found the
        hints (``lean_decider``). When a part is not, the fact is returned as
        it was handed, with ``lean_reason`` naming the parts and why, and the
        oracles after Lean decide it as they would have: a fact the plugin's
        solver decides is ``decided`` with the reason Lean did not prove it.

        A claim the solver refuted comes with its counterexample, and is not
        offered to Lean as a claim: Lean proves the part false at the point
        instead, and the fact keeps its status with ``lean_counterexample``
        saying whether Lean confirmed it, and ``lean_refuted_by`` how, when it
        did (see :meth:`_check_counterexample`).
        A fact already ``refuted`` whose obligation has no counterexample is
        not offered either, and keeps its status: Lean only ever checks a
        refutation, and never turns one into a proof.

        The :class:`ProofCache` is read first, and no session is started when
        it answers for every part (#118): a file checked again sends the same
        declarations, so a warm check reads every answer back, and starting
        the REPL to ask nothing was most of what a warm check cost. The cache
        is keyed by the Lean version as well as the source, and the version
        is the one the session would run (:meth:`_cache_version`), read
        without starting it; a part about reals is kept under the Mathlib
        project's toolchain and revision, read from its files
        (:func:`_mathlib_key`). A part with an attempt the cache does not hold
        sends the whole obligation to the sessions, which read the cache in
        their turn.
        """
        try:
            obligation = obligation_of(fact.term)
        except Exception as exc:  # noqa: BLE001 - a plugin's failure declines one fact
            obligation = None
            reason = f"the claim could not be stated for Lean ({type(exc).__name__}: {exc})"
        else:
            reason = "the claim is stated with nothing for Lean to check"
        if obligation is not None and obligation.declined:
            reason = obligation.declined
        if obligation is None or obligation.declined or not obligation.parts:
            return fact.with_status(
                fact.status, lean_declined=reason, declined=f"{self.name}: {reason}"
            )
        if fact.status is Status.REFUTED and obligation.counterexample is None:
            # a refuted claim is checked at its counterexample, never proved: a
            # proof of its parts would read proved where the solver refuted it
            return fact.with_status(
                fact.status,
                lean_counterexample=(
                    "Lean did not check the refutation: no counterexample to it "
                    "was stated for Lean"
                ),
            )
        available, why = self.availability()
        if not available:
            return fact.with_status(fact.status, lean_declined=why, declined=f"{self.name}: {why}")
        reals = any(getattr(part, "mathlib", False) for part in obligation.parts)
        if reals and not self._mathlib():
            reason = (
                "the claim is about real numbers, which core Lean does not have; "
                "where Mathlib is (LANKY_LEAN_MATHLIB), Lean checks it"
            )
            return fact.with_status(
                fact.status,
                lean_declined=reason,
                lean_needs_mathlib=True,
                declined=f"{self.name}: {reason}",
            )
        try:
            budget = self._budget(fact)
        except ValueError as exc:
            return fact.with_status(
                fact.status, lean_declined=str(exc), declined=f"{self.name}: {exc}"
            )
        if self.proofs is None:
            self.proofs = ProofCache(default_proof_cache_dir())
        owner = fact.owner or fact.id
        # a part about reals is kept under the Mathlib project's key, the
        # others under the core version, both known without a session
        directory = self.session.mathlib if reals else None
        version = self._cache_version()
        real_key = _mathlib_key(directory) if reals else None
        records: list[dict] | None = None
        if obligation.counterexample is not None:
            # every answer from the cache, or none: no session is started (#118)
            if version is not None and not reals:
                found = self._check_counterexample(fact, obligation, owner, None, version)
                if found is not None:
                    return found
        elif not reals or real_key is not None:
            records = self._cached_parts(obligation.parts, owner, version, real_key)
            if records is not None and reals:
                version = mathlib_mode.toolchain(directory) if directory else None
        if records is None:
            sessions = self._part_sessions()
            if not sessions:
                return fact.with_status(
                    fact.status, lean_tried=0, lean_reason=self._pool_error()
                )
            until = None if budget is None else time.monotonic() + budget
            if obligation.counterexample is not None:
                checked = self._check_counterexample(fact, obligation, owner, until)
                assert checked is not None  # a session answers or says why not
                return checked
            records = self._check_parts(obligation.parts, owner, until)
            version = self.session.version if reals else sessions[0].version
        common: dict[str, Any] = {
            "lean_parts": records,
            "lean_version": version,
        }
        if obligation.decider:
            common["lean_decider"] = obligation.decider
        if obligation.stated_by:
            common["lean_stated_by"] = obligation.stated_by
        if reals:
            common["lean_mathlib"] = self.session.mathlib_revision or (
                mathlib_mode.revision(directory) if directory else None
            )
        if all(record.get("proved") for record in records):
            source = "\n".join(record["source"] for record in records)
            if reals:
                # the file that replays it imports Mathlib first
                source = f"import Mathlib\n\n{source}"
            result = fact.with_status(
                Status.PROVED,
                self.name,
                tactic=_how_text(records),
                lean_source=source,
                **common,
            )
            if obligation.rests_on:
                result = replace(
                    result,
                    rests_on=tuple(dict.fromkeys((*fact.rests_on, *obligation.rests_on))),
                )
            return result
        said = _missed_text(records)
        return fact.with_status(fact.status, lean_tried=len(records), lean_reason=said, **common)

    def _pool_error(self) -> str:
        """Why the first session of the pool did not start."""
        if self._pool and self._pool[0].error:
            return self._pool[0].error
        return "no Lean session could be started"

    def _part_sessions(self) -> list[LeanSession]:
        """The pool's sessions, the first of them running; empty when it will not start.

        The first is the oracle's own session when that is a core one, and a
        core session of its own when the oracle runs Mathlib: a part is
        integer arithmetic, and a twin of a Mathlib session would import
        Mathlib again for every part.
        """
        if not self._pool:
            session = self.session
            if session.mathlib is not None:
                session = LeanSession(self.timeout)
            self._pool.append(session)
        if not self._pool[0].ready():
            return []
        return self._pool

    def _cache_version(self) -> str | None:
        """The Lean version the parts' answers are kept under, known without a session.

        The version of the pool's running session, once there is one; before
        that, the version a session would start with: ``LANKY_LEAN_VERSION``
        when it pins one, the version an earlier session of this process
        settled on, or the version of the ``lean`` on the ``PATH``, which is
        what :func:`candidate_versions` tries first (#118). ``None`` when
        none of them names a version, and the cache is then read by the
        sessions alone. An answer kept under a version is one that version of
        Lean gave, whichever version this process ends up running, so
        reading it back is sound even where a session would fall back on
        another toolchain.
        """
        if self._pool and self._pool[0].server is not None:
            return self._pool[0].version
        pinned = os.environ.get("LANKY_LEAN_VERSION")
        if pinned:
            return pinned
        if _RESOLVED != ():
            return _RESOLVED  # type: ignore[return-value]
        if self._on_path is None:
            self._on_path = (_lean_on_path_version() or "",)
        return self._on_path[0] or None

    def _cached_parts(
        self, parts: Any, owner: str, version: str | None, real_key: str | None = None
    ) -> list[dict] | None:
        """Every part's record read from the cache, or ``None`` if one needs Lean (#118).

        A part about reals is read under ``real_key``, the Mathlib project's
        (:func:`_mathlib_key`), the others under ``version``.
        """
        cache = self.proofs

        def reader(key: str | None) -> Any:
            def kept(source: str) -> tuple[bool, str, bool, bool] | None:
                found = cache.get(key, source) if cache is not None and key else None
                return None if found is None else (found[0], found[1], True, True)

            return kept

        records = []
        for part in parts:
            key = real_key if getattr(part, "mathlib", False) else version
            if key is None:
                return None
            record = self._check_part(part, owner, None, reader(key))
            if record is None:
                return None
            records.append(record)
        return records

    def _check_parts(self, parts: Any, owner: str, until: float | None) -> list[dict]:
        """Check every part, in a pool of sessions; one record per part, in order.

        A part about reals (:attr:`lanky.obligations.Part.mathlib`) is
        checked in the oracle's Mathlib session, one after another, and the
        others in the pool of core sessions.
        """
        reals = [index for index, part in enumerate(parts) if getattr(part, "mathlib", False)]
        if reals:
            records: dict[int, dict] = {}
            for index in reals:
                records[index] = self._checked(self.session, parts[index], owner, until)
            rest = [index for index in range(len(parts)) if index not in records]
            if rest:
                checked = self._check_parts([parts[index] for index in rest], owner, until)
                records.update(zip(rest, checked, strict=True))
            return [records[index] for index in range(len(parts))]
        sessions = self._part_sessions()
        jobs = min(len(parts), _jobs())
        while len(sessions) < jobs:
            try:
                sessions.append(sessions[0].twin())
            except ValueError:
                break
        jobs = min(jobs, len(sessions))
        if jobs <= 1:
            return [self._checked(sessions[0], part, owner, until) for part in parts]
        import queue
        from concurrent.futures import ThreadPoolExecutor

        free: queue.Queue[LeanSession] = queue.Queue()
        for session in sessions[:jobs]:
            free.put(session)

        def check(part: Any) -> dict:
            session = free.get()
            try:
                return self._checked(session, part, owner, until)
            finally:
                free.put(session)

        with ThreadPoolExecutor(max_workers=jobs, thread_name_prefix="lanky-lean") as pool:
            return list(pool.map(check, parts))

    def _checked(
        self, session: LeanSession, part: Any, owner: str, until: float | None
    ) -> dict:
        """:meth:`_check_part` in ``session``, the cache read first."""
        record = self._check_part(
            part, owner, until, lambda source: self._ask(session, source, until)
        )
        assert record is not None  # a session answers every attempt, or says why not
        return record

    def _ask(
        self, session: LeanSession, source: str, until: float | None
    ) -> tuple[bool, str, bool, bool]:
        """``(closed, detail, cached, answered)`` for one declaration, the cache first.

        A Mathlib session's answers are kept under its Lean version and the
        Mathlib revision it imported, apart from core Lean's. An answer of a
        session whose version is not known is not kept, nor read: the key
        would say nothing of which Lean gave it.
        """

        def key() -> str | None:
            if session.mathlib is not None:
                found = _mathlib_key(session.mathlib)
                if found is None and session.version is not None:
                    found = f"{session.version}+mathlib@{session.mathlib_revision}"
                return found
            return session.version

        cache = self.proofs
        version = key()
        if cache is not None and version is not None:
            kept = cache.get(version, source)
            if kept is not None:
                return kept[0], kept[1], True, True
        closed, detail, answered = session.answer(source, until)
        # the session may have started for this answer, and only now know it
        version = key()
        if answered and cache is not None and version is not None:
            cache.put(version, source, closed, detail)
        return closed, detail, False, answered

    def _check_part(
        self, part: Any, owner: str, until: float | None, ask: Any
    ) -> dict | None:
        """Prove one part: its record, with how it was proved or why it was not.

        The record holds the part's ``name`` and ``label``, ``proved``, the
        ``source`` of the declaration that proved it (the last one tried when
        none did), ``how``, ``seconds`` and ``cached``, and otherwise
        ``reason`` and, when Lean ran out of time rather than answering,
        ``timed_out``.

        ``ask`` answers one declaration's source as :meth:`_ask` does, or
        gives ``None`` when it cannot, which a reading of the cache alone does
        for a declaration it does not hold (:meth:`_cached_parts`); the part
        then has no record, and ``None`` comes back.
        """
        record: dict[str, Any] = {"name": part.name, "label": part.label, "proved": False}
        try:
            statement = part_statement(part, theorem_name(owner, part))
        except (UnsupportedTerm, AttributeError, TypeError, ValueError) as exc:
            record["reason"] = f"it has no Lean statement ({exc})"
            record["short"] = f"had no statement of it ({exc})"
            return record
        tried = attempts(part, statement)
        if not tried:
            record["reason"] = (
                "its goal is an existential and no witness was given for it, which "
                "omega does not look for"
            )
            record["short"] = "was given no witness for what it claims exists"
            record["source"] = statement.source("sorry")
            return record
        start = time.monotonic()
        last = ""
        tried = list(tried)
        asked = False
        while tried:
            how, tactic = tried.pop(0)
            source = statement.source(tactic)
            record["source"] = source
            if _spent(until):
                record["timed_out"] = True
                record["reason"] = "the budget ran out before Lean was asked"
                record["short"] = "ran out of time"
                break
            answer = ask(source)
            if answer is None:
                return None
            closed, detail, cached, answered = answer
            if closed:
                record.update(proved=True, how=how, cached=cached)
                record.pop("reason", None)
                record.pop("short", None)
                record.pop("timed_out", None)
                break
            if not answered:
                record["timed_out"] = True
                record["reason"] = (
                    f"Lean did not answer within the time it was given ({detail})"
                )
                record["short"] = "ran out of time"
                continue
            last = detail
            record.pop("timed_out", None)
            record["reason"] = f"no script closed it; Lean said: {last}"
            record["short"] = "found no proof"
            if not tried and not asked and callable(getattr(part, "fallback", None)):
                # what the solver finds only when asked: a case split, say
                asked = True
                tried = _fallback_attempts(part, statement)
        record["seconds"] = round(time.monotonic() - start, 3)
        return record

    def _check_counterexample(
        self,
        fact: Fact,
        obligation: Any,
        owner: str,
        until: float | None,
        version: str | None = None,
    ) -> Fact | None:
        """Prove the refuted part false at the solver's counterexample.

        By ``decide``, which evaluates the instantiated statement in the
        kernel, and then by ``omega``. The fact keeps its status: the plugin's
        solver refutes it, and ``lean_counterexample`` says in plain words what
        Lean made of the counterexample, ``lean_refuted_by`` by what it proved
        the claim false, and ``lean_refutation`` holds the theorem. One Lean
        cannot prove false there is no counterexample to the printed
        statement, a disagreement between the solver and Lean that the
        ledger names (``lean_disagrees``, with what Lean said in
        ``lean_counterexample_detail``).

        With ``version``, the answers are read from the cache alone, as they
        were kept under that Lean version, and ``None`` comes back when one
        Lean has to be asked for is not there (#118); without it, the pool's
        first session is asked, the cache first.
        """
        counter = obligation.counterexample
        where = counter.text or ", ".join(f"{k}={v}" for k, v in counter.point.items())
        part = next((p for p in obligation.parts if p.name == counter.part), None)
        if part is None:
            return fact.with_status(
                fact.status,
                lean_counterexample=(
                    f"Lean did not check the counterexample: it is to the part "
                    f"{counter.part}, which the claim does not have"
                ),
            )
        try:
            statement = part_statement(part, theorem_name(owner, part))
            sources = [
                ("decide", negation_source(part, statement, counter.point, decide=True)),
                ("omega", negation_source(part, statement, counter.point, decide=False)),
            ]
        except (UnsupportedTerm, AttributeError, TypeError, ValueError) as exc:
            return fact.with_status(
                fact.status,
                lean_counterexample=f"Lean did not check the counterexample: {exc}",
            )
        if version is None:
            session = self._part_sessions()[0]
            version = session.version

            def ask(source: str) -> tuple[bool, str, bool, bool] | None:
                return self._ask(session, source, until)

        else:

            def ask(source: str) -> tuple[bool, str, bool, bool] | None:
                kept = self.proofs.get(version, source) if self.proofs else None
                return None if kept is None else (kept[0], kept[1], True, True)

        last = ""
        heard = False
        for how, source in sources:
            answer = ask(source)
            if answer is None:
                return None
            closed, detail, _cached, answered = answer
            heard = heard or answered
            if closed:
                return fact.with_status(
                    fact.status,
                    lean_counterexample=(
                        f"Lean confirmed the counterexample: the claim is false at {where}"
                    ),
                    lean_refuted_by=how,
                    lean_refutation=source,
                    lean_version=version,
                )
            last = detail if answered else f"no answer in time ({detail})"
        if not heard:
            # Lean gave no verdict, which is no disagreement (Codex)
            return fact.with_status(
                fact.status,
                lean_counterexample=(
                    f"Lean did not check the counterexample at {where}: it ran out of time"
                ),
                lean_counterexample_detail=last,
                lean_refutation=sources[-1][1],
            )
        return fact.with_status(
            fact.status,
            lean_counterexample=(
                f"the counterexample and Lean disagree: Lean could not prove the claim "
                f"false at {where} (--show-lean shows what Lean said)"
            ),
            lean_counterexample_detail=last,
            lean_refutation=sources[-1][1],
            lean_disagrees=True,
        )

    # }}}


# }}}


def use_tactic(claim: Any, script: str) -> None:
    """Pin the tactic script for one claim, bypassing the ladder.

    The escape hatch for a statement the ladder cannot find a proof of. It takes
    a :class:`~lanky.theory.Theorem`, a :class:`~lanky.ledger.Fact` or a fact id,
    and applies to every Lean oracle in the registry, so a file can pin a script
    next to the theorem it belongs to::

        use_tactic(
            scan_monotone,
            "intro a ha0 ha b hb0 hb hab\n"
            "obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0\n"
            "induction b with ...",
        )

    The script proves the statement as it is printed, which is the integer
    reading (see :mod:`lanky.lean`): a natural is an ``Int`` followed by its
    ``0 ≤ b``, which is why the script above trades ``b`` for a ``Nat`` before
    inducing. The ledger still records which script closed the goal, so a
    pinned proof is as visible as a found one.
    """
    fact_id = _claim_id(claim)
    for oracle in _lean_oracles():
        oracle.tactics[fact_id] = script


def use_certificate(claim: Any, finder: Finder) -> None:
    """Have the family induction ask ``finder`` for one claim's certificates.

    The certificate hook (see :mod:`lanky.induction`). A claim about every
    order is proved by :func:`family_induction_scripts`, whose cases are each
    closed by a linear combination of the hypotheses, and lanky's search
    (:func:`lanky.induction.find_certificate`) finds the combination where it
    can. A plugin that knows it, the multipliers a PDE's coefficients give,
    say, hands it over here: ``finder`` takes a :class:`~lanky.induction.Case`
    and returns the :class:`~lanky.induction.Use` of each lemma, or ``None``.
    Lean checks whatever it returns, so a wrong certificate costs an attempt
    and never a wrong proof.

    ``claim`` is named as for :func:`use_tactic`, and the finder applies to
    every Lean oracle in the registry.
    """
    fact_id = _claim_id(claim)
    for oracle in _lean_oracles():
        oracle.certificates[fact_id] = finder


def decline(claim: Any, reason: str) -> None:
    """Have the Lean oracle leave one claim to the oracles after it, saying why.

    For a claim that is some other oracle's to settle, such as the row of a
    demonstration that shows what a computer algebra system decides, where a
    proof would take Lean minutes and be beside the point (#71). The fact is
    returned with ``reason`` as its ``declined`` entry, as for one the printer
    declines, and the oracles after Lean are asked as they always are.

    ``claim`` is named as for :func:`use_tactic`, and the decline applies to
    every Lean oracle in the registry.
    """
    if not isinstance(reason, str) or not reason.strip():
        raise TypeError("decline() needs the reason, which the ledger records")
    fact_id = _claim_id(claim)
    for oracle in _lean_oracles():
        oracle.declines[fact_id] = reason


def _claim_id(claim: Any) -> str:
    """The fact id a theorem, a fact or an id names."""
    fact_id = getattr(claim, "id", None)
    if fact_id is None and hasattr(claim, "fact"):
        fact_id = claim.fact().id
    return str(claim) if fact_id is None else fact_id


def _lean_oracles() -> list[LeanOracle]:
    """Every Lean oracle in the registry; ``LookupError`` when there is none."""
    import lanky.oracles  # noqa: F401 - importing registers the built-in oracles
    from lanky.plugins import registry

    oracles = [oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)]
    if not oracles:
        raise LookupError("no Lean oracle is registered")
    return oracles
