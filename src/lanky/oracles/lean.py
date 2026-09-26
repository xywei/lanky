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
proved there records the Mathlib revision it was proved against. With the
variable unset nothing of this is consulted, and the oracle is the core one.

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
import os
import re
import shutil
import subprocess
from importlib.util import find_spec
from typing import Any

import pymbolic.primitives as prim

from lanky import mathlib as mathlib_mode
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    dialect,
    domain_guards,
    is_natural,
    statement_of,
)
from lanky.ledger import Fact, Status
from lanky.prelude import FinType, Refined
from lanky.terms import Exists, Forall, Sum, Var, conjuncts, free_variables, init_args

__all__ = [
    "LeanOracle",
    "LeanSession",
    "default_cache_dir",
    "induction_scripts",
    "reduction_scripts",
    "tactic_ladder",
    "use_tactic",
]

#: Seconds one tactic attempt may take before the session is asked to give up.
DEFAULT_TIMEOUT = float(os.environ.get("LANKY_LEAN_TIMEOUT", "60"))

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
#: of a sum or a difference, and the square root of a number that is not
#: positive, which is where Mathlib's total ``Real.sqrt`` is ``0``.
_ELEMENTARY_LEMMAS = (
    "Real.exp_add",
    "Complex.exp_add",
    "Real.exp_sub",
    "Complex.exp_sub",
    "Real.sqrt_eq_zero'",
)

#: The whole-goal attempts Mathlib mode adds after :data:`BASE_TACTICS`. An
#: attempt that leaves a goal open fails as a declaration, so a tactic such as
#: ``norm_num`` that can succeed without closing needs no ``done`` here.
MATHLIB_TACTICS: tuple[str, ...] = (
    "norm_num",
    "positivity",
    "ring",
    "field_simp",
    "linarith",
    "nlinarith",
    "(push_cast; ring)",
    f"simp [{', '.join(_ELEMENTARY_LEMMAS)}]",
    f"simp_all [{', '.join(_ELEMENTARY_LEMMAS)}] <;> linarith",
)

#: :data:`_CLOSERS`, with Mathlib's closing tactics after the core ones.
_MATHLIB_CLOSERS = (
    f"{_CLOSERS} | linarith | nlinarith | positivity | (ring_nf; done) "
    "| (push_cast; ring) | (norm_num; done)"
)

#: Peel the last term off a sum over ``Finset.Ico a (b + 1)``, which is how a
#: reduction's bound reads after an induction's step has rewritten it. Tried,
#: never required: a goal with no such sum is left as it was.
_PEEL_SUM = (
    "try rw [← Finset.insert_Ico_right_eq_Ico_add_one (by omega), "
    "Finset.sum_insert (by simp)]"
)

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

    ``mathlib`` names a Lake project with Mathlib fetched (see
    :mod:`lanky.mathlib`), and makes this a Mathlib session: the REPL runs in
    that project, Mathlib is imported once when the session starts, and every
    command is elaborated in the environment the import left, which is as
    fresh for each attempt as core Lean's empty one. The Lean version is the
    project's, not one chosen from the toolchains installed. A server the
    REPL driver killed, which it does to a command that runs past its timeout,
    is started again with Mathlib imported before the next command, since the
    import is part of what the session is.
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
            atexit.register(self.close)
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
        if not self._import_mathlib():
            self.close()
            return False
        atexit.register(self.close)
        return True

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
        message = getattr(response, "message", None)
        problems = [str(message)] if message is not None else _errors(response)
        if problems:
            self.error = f"importing Mathlib failed: {problems[0]}"
            return False
        self.environment = getattr(response, "env", None)
        return True

    def _revive(self) -> bool:
        """Start a Mathlib session's server again if the driver killed it."""
        alive = getattr(self.server, "is_alive", None)
        if alive is None or alive():
            return True
        try:
            self.server.start()
        except Exception as exc:  # noqa: BLE001 - a server that will not start is a reason
            self.error = f"the Lean REPL could not be restarted ({exc})"
            return False
        return self._import_mathlib()

    def close(self) -> None:
        """Stop the Lean process, if one is running.

        Letting the interpreter collect the server instead works, but the
        collection happens during shutdown, when the modules the server's own
        finalizer uses may already be gone; closing on purpose keeps that noise
        out of a test run.
        """
        server, self.server = self.server, None
        if server is not None:
            try:
                server.kill()
            except Exception:  # noqa: BLE001 - a session being closed cannot fail
                pass

    def run(self, source: str) -> tuple[bool, str]:
        """Elaborate one declaration; ``(closed, first diagnostic)``.

        A declaration is closed when Lean reports no error and no ``sorry``:
        the kernel accepted the proof term the tactics built.
        """
        from lean_interact import Command

        if not self.start():
            return False, self.error or "no Lean session"
        if self.mathlib is not None:
            if not self._revive():
                return False, self.error or "no Lean session"
            command = Command(cmd=source, env=self.environment)
        else:
            command = Command(cmd=source)
        try:
            response = self.server.run(command, timeout=self.timeout)
        except Exception as exc:  # noqa: BLE001 - a timeout must not stop the ladder
            return False, f"{type(exc).__name__}: {exc}"
        message = getattr(response, "message", None)
        if message is not None:
            return False, str(message)
        problems = _errors(response)
        if getattr(response, "sorries", ()):
            problems.append("the proof was accepted with a sorry in it")
        if problems:
            lines = problems[0].strip().splitlines()
            return False, lines[0] if lines else "Lean reported an error with no message"
        return True, ""


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


def _goal_intro(
    statement: LeanStatement,
) -> tuple[list[str], list[Var], list[Any], dict[str, str]]:
    """What ``intro`` must name to strip the goal's own quantifier.

    The printer emits one binder at a time with its guards right after it
    (``∀ a : Int, 0 ≤ a → a < n + 1 → ...``), so the names are a variable, its
    guards, the next variable, its guards, and the generator's own guard comes
    last. Returning the binder variables and the guards as terms as well is
    what lets a strategy decide which variable to induce on, and the fourth
    value names, for each natural variable, the hypothesis ``0 ≤ a`` that makes
    it one, which is what an induction on it has to start from.

    The guards are rendered to be counted, and rendering a bound such as
    ``Fin[2 ** n]`` needs to know that ``n`` is a natural, so each binder's
    guards are rendered with the statement's own binders and the goal's
    earlier ones in scope, as the printer rendered them.
    """
    goal = statement.goal_term
    if not isinstance(goal, Forall):
        return [], [], [], {}
    used = {name for name, _ in statement.binders} | {name for name, _ in statement.hypotheses}
    names: list[str] = []
    variables: list[Var] = []
    naturals: dict[str, str] = {}
    guards = list(conjuncts(goal.guard))
    scope = dict(statement.types)
    for position, (var, domain) in enumerate(goal.binders):
        names.append(var.name)
        used.add(var.name)
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
    return names, variables, guards, naturals


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
    """
    with dialect(statement.mathlib):
        names, variables, guards, naturals = _goal_intro(statement)
    target, companion = _induction_target(variables, guards)
    if target is None or target.name not in naturals:
        return []
    closers = _closers(statement)
    peel = [f"  {_PEEL_SUM}"] if _has_reduction(statement) else []
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
    later = len(names) - names.index(target.name) - 1
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
            f"first | omega | (have {pinned} : {companion} = ((0 : Nat) : Int) := "
            f"(by omega); subst {pinned}; {closers}) | (simp_all; done) "
            "| (simp_all <;> omega)"
        )
    head = [f"intro {' '.join(names)}"] if names else []
    head += [
        f"obtain ⟨{target.name}, rfl⟩ := Int.eq_ofNat_of_zero_le {naturals[target.name]}",
        f"induction {target.name} with",
        "| zero =>",
        f"  {zero}",
        f"| succ {step} {hypothesis} =>",
        f"  have {cast} : (({step} + 1 : Nat) : Int) = ({step} : Int) + 1 := (by omega)",
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
                    f"  by_cases {less} : ({step} : Int) < {companion}",
                    f"  · have {equality} : {companion} = ({step} : Int) + 1 := (by omega)",
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
    ``Finset.Ico 0 (↑k + 1 + 1)``, and :data:`_PEEL_SUM` takes the last term
    off the sum. What is left is the induction hypothesis plus a polynomial
    identity or inequality, which the closers take. The base case peels the
    one term of ``Finset.Ico 0 (↑0 + 1)`` the same way.

    A goal that is itself quantified is left to :func:`induction_scripts`.
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
    scripts = []
    for position, (name, _sort) in enumerate(statement.binders):
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
                    f"obtain ⟨{name}, rfl⟩ := Int.eq_ofNat_of_zero_le {own[0]}",
                    f"induction {name} with",
                    "| zero =>",
                    f"  {_PEEL_SUM}",
                    f"  {closers}",
                    f"| succ {step} {hypothesis} =>",
                    f"  have {cast} : (({step} + 1 : Nat) : Int) = ({step} : Int) + 1 "
                    ":= (by omega)",
                    f"  try simp only [{cast}] at *",
                    f"  first | {apply_ih} | skip",
                    f"  {_PEEL_SUM}",
                    f"  {closers}",
                ]
            )
        )
    return scripts


def tactic_ladder(statement: LeanStatement) -> list[str]:
    """Every script the oracle tries, cheapest and most general first.

    A statement printed in the Mathlib dialect gets the core ladder first, as
    it stands but for the closers, and then Mathlib's attempts: the tactics in
    :data:`MATHLIB_TACTICS` on the whole goal, and :func:`reduction_scripts`.
    """
    with dialect(statement.mathlib):
        names, _, _, _ = _goal_intro(statement)
    ladder = list(BASE_TACTICS)
    if statement.mathlib:
        ladder += MATHLIB_TACTICS
    if names:
        introduction = f"intro {' '.join(names)}"
        ladder += [
            f"{introduction}\n{_closers(statement)}",
            f"{introduction}\nsimp_all\nomega",
        ]
    ladder += induction_scripts(statement)
    ladder += reduction_scripts(statement)
    return ladder


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
    """

    name = "lean"

    def __init__(
        self, timeout: float = DEFAULT_TIMEOUT, session: LeanSession | None = None
    ) -> None:
        self.timeout = timeout
        self._pinned = session
        self._sessions: dict[str | None, LeanSession] = {}
        #: ``fact id -> tactic script``, consulted before the ladder.
        self.tactics: dict[str, str] = {}

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
            return False, "lean_interact is not installed (pip install lanky[lean])"
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
        try:
            statement_of(fact.term, fact.owner or fact.id, mathlib=self._mathlib())
        except (UnsupportedTerm, AttributeError, TypeError, ValueError):
            return False
        return True

    def _mathlib(self) -> bool:
        """Whether the session in effect has Mathlib."""
        return self.session.mathlib is not None

    def establish(self, fact: Fact, /) -> Fact | None:
        """Try the ladder; ``PROVED`` on success, the fact unchanged otherwise."""
        session = self.session
        mathlib = session.mathlib is not None
        try:
            statement = statement_of(fact.term, fact.owner or fact.id, mathlib=mathlib)
        except UnsupportedTerm as exc:
            return fact.with_status(fact.status, lean_declined=str(exc))
        available, reason = self.availability()
        if not available:
            return fact.with_status(fact.status, lean_declined=reason)
        override = self.tactics.get(fact.id)
        ladder = [override] if override is not None else tactic_ladder(statement)
        last = ""
        for tactic in ladder:
            source = statement.source(tactic)
            closed, detail = session.run(source)
            if closed:
                extra = {}
                if mathlib:
                    # the file that replays it, which the REPL command, run in
                    # the environment the import left, could not spell
                    source = f"import Mathlib\n\n{source}"
                    extra["lean_mathlib"] = session.mathlib_revision
                return fact.with_status(
                    Status.PROVED,
                    self.name,
                    tactic=tactic,
                    lean_source=source,
                    lean_version=session.version,
                    **extra,
                )
            last = detail
            if session.error is not None:
                break
        return fact.with_status(
            fact.status,
            lean_tried=len(ladder),
            lean_reason=session.error or last,
        )


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
    import lanky.oracles  # noqa: F401 - importing registers the built-in oracles
    from lanky.plugins import registry

    fact_id = getattr(claim, "id", None)
    if fact_id is None and hasattr(claim, "fact"):
        fact_id = claim.fact().id
    if fact_id is None:
        fact_id = str(claim)
    oracles = [oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)]
    if not oracles:
        raise LookupError("no Lean oracle is registered")
    for oracle in oracles:
        oracle.tactics[fact_id] = script
