"""The Lean oracle: kernel evidence for a lanky fact.

The design idea. Lean is the platform and lanky is a language hosted on it, so a
fact Lean closes carries the strongest evidence lanky has, the trust class
``kernel``: the proof term was checked by the Lean kernel, not sampled and not
decided by a procedure lanky trusts on its word. The oracle prints the fact's
term with :mod:`lanky.lean`, opens a Lean session through ``lean_interact``, and
tries a fixed ladder of tactic scripts. A script that closes the goal becomes the
fact's provenance, alongside the Lean source, so the claim can be replayed by
hand or rechecked later by ``certify``.

Core Lean 4 only, no Mathlib: the fragment is what :mod:`lanky.lean` can print,
and the tactics are the ones core Lean ships (``omega``, ``decide``, ``simp``,
``simp_all``, ``induction``, ``rcases``).

The ladder is not proof search. It is four cheap attempts and then one strategy
that is derived from the shape of the statement: a statement of the form "for
all ``a`` and ``b`` below a bound, with ``a <= b``, ``f a <= f b``" is proved by
induction on ``b`` with a case split on whether ``a`` has been reached yet, and
that is the shape every scan postcondition has. What makes it a strategy rather
than a hand-written proof of one theorem is that the induction variable, the
variable to split on, and the hypotheses to instantiate are all read off the
term (see :func:`induction_scripts`).

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

from lanky.lean import LeanStatement, UnsupportedTerm, domain_guards, statement_of
from lanky.ledger import Fact, Status
from lanky.terms import Forall, Var, conjuncts

__all__ = [
    "LeanOracle",
    "LeanSession",
    "default_cache_dir",
    "induction_scripts",
    "tactic_ladder",
    "use_tactic",
]

#: Seconds one tactic attempt may take before the session is asked to give up.
DEFAULT_TIMEOUT = float(os.environ.get("LANKY_LEAN_TIMEOUT", "60"))

#: The cheap tactics, tried on the goal as printed, before any script is built.
BASE_TACTICS: tuple[str, ...] = ("omega", "decide", "simp", "simp_all")

#: What a compound attempt falls back through once the context is set up.
_CLOSERS = "first | omega | simp_all | (simp_all <;> omega)"


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
    """

    def __init__(self, timeout: float = DEFAULT_TIMEOUT, cache_dir: str | None = None) -> None:
        self.timeout = timeout
        self.cache_dir = cache_dir or default_cache_dir()
        self.server: Any = None
        self.version: str | None = None
        self.error: str | None = None

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
        try:
            response = self.server.run(Command(cmd=source), timeout=self.timeout)
        except Exception as exc:  # noqa: BLE001 - a timeout must not stop the ladder
            return False, f"{type(exc).__name__}: {exc}"
        message = getattr(response, "message", None)
        if message is not None:
            return False, str(message)
        problems = [
            str(item.data)
            for item in getattr(response, "messages", ())
            if str(getattr(item, "severity", "")).endswith("error")
        ]
        if getattr(response, "sorries", ()):
            problems.append("the proof was accepted with a sorry in it")
        if problems:
            lines = problems[0].strip().splitlines()
            return False, lines[0] if lines else "Lean reported an error with no message"
        return True, ""


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


def _goal_intro(statement: LeanStatement) -> tuple[list[str], list[Var], list[Any]]:
    """What ``intro`` must name to strip the goal's own quantifier.

    The printer emits one binder at a time with its bound as a guard right after
    it (``∀ a : Nat, a < n + 1 → ...``), so the names alternate variable, guard,
    variable, guard, and the generator's own guard comes last. Returning the
    binder variables and the guards as terms as well is what lets a strategy
    decide which variable to induce on.
    """
    goal = statement.goal_term
    if not isinstance(goal, Forall):
        return [], [], []
    used = {name for name, _ in statement.binders} | {name for name, _ in statement.hypotheses}
    names: list[str] = []
    variables: list[Var] = []
    guards = list(conjuncts(goal.guard))
    for position, (var, domain) in enumerate(goal.binders):
        names.append(var.name)
        used.add(var.name)
        variables.append(var)
        for _ in domain_guards(var, domain):
            names.append(_fresh("hd", used))
        if position == len(goal.binders) - 1:
            for _ in guards:
                names.append(_fresh("hg", used))
    return names, variables, guards


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


def _bounded_hypotheses(statement: LeanStatement) -> list[str]:
    """The names of the hypotheses that are themselves bounded quantifiers.

    Such a hypothesis is the recurrence (``off (r + 1) = off r + cnt r`` for
    every ``r`` below ``n``), and the successor case of an induction is exactly
    where it has to be instantiated.
    """
    names = []
    for (name, _), term in zip(statement.hypotheses, statement.hypothesis_terms, strict=False):
        if isinstance(term, Forall) and len(term.binders) == 1:
            names.append(name)
    return names


def induction_scripts(statement: LeanStatement) -> list[str]:
    """Tactic scripts that induce on the statement's own recurrence variable.

    Two shapes, the second a weakening of the first: induction with a case split
    on whether the other variable has been reached, and induction without it.
    Every name in them is read off the statement, so the scripts are a strategy
    and not a proof of one theorem.
    """
    names, variables, guards = _goal_intro(statement)
    target, companion = _induction_target(variables, guards)
    if target is None:
        return []
    used = set(names) | {name for name, _ in statement.binders}
    used |= {name for name, _ in statement.hypotheses}
    step = _fresh("k", used)
    hypothesis = _fresh("ih", used)
    instantiations = [
        f"  first | (have {_fresh('hstep', used)} := {name} {step} (by omega)) | skip"
        for name in _bounded_hypotheses(statement)
    ]
    apply_ih = (
        f"first | (have {_fresh('hih', used)} := {hypothesis} (by omega) (by omega))"
        f" | (have {_fresh('hih', used)} := {hypothesis} (by omega))"
        f" | (have {_fresh('hih', used)} := {hypothesis}) | skip"
    )
    head = [f"intro {' '.join(names)}"] if names else []
    head += [
        f"induction {target.name} with",
        "| zero =>",
        f"  {_CLOSERS}",
        f"| succ {step} {hypothesis} =>",
    ]

    scripts = []
    if companion is not None:
        equality = _fresh("heq", used)
        less, greater = _fresh("hlt", used), _fresh("hge", used)
        scripts.append(
            "\n".join(
                [
                    *head,
                    *instantiations,
                    f"  rcases Nat.lt_or_ge {step} {companion} with {less} | {greater}",
                    f"  · have {equality} : {companion} = {step} + 1 := by omega",
                    f"    subst {equality}",
                    f"    {_CLOSERS}",
                    f"  · {apply_ih}",
                    f"    {_CLOSERS}",
                ]
            )
        )
    scripts.append("\n".join([*head, *instantiations, f"  {apply_ih}", f"  {_CLOSERS}"]))
    return scripts


def tactic_ladder(statement: LeanStatement) -> list[str]:
    """Every script the oracle tries, cheapest and most general first."""
    names, _, _ = _goal_intro(statement)
    ladder = list(BASE_TACTICS)
    if names:
        introduction = f"intro {' '.join(names)}"
        ladder += [
            f"{introduction}\n{_CLOSERS}",
            f"{introduction}\nsimp_all\nomega",
        ]
    ladder += induction_scripts(statement)
    return ladder


# }}}


# {{{ the oracle


class LeanOracle:
    """Establish facts by proving them in Lean, with core Lean only.

    A per-fact tactic override is possible through :attr:`tactics`, keyed by
    fact id, for the statement whose proof the ladder cannot find: it is an
    escape hatch and not the intended path, and the ledger records which script
    closed the goal either way.
    """

    name = "lean"

    def __init__(
        self, timeout: float = DEFAULT_TIMEOUT, session: LeanSession | None = None
    ) -> None:
        self.session = session if session is not None else LeanSession(timeout)
        #: ``fact id -> tactic script``, consulted before the ladder.
        self.tactics: dict[str, str] = {}

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
        none.
        """
        if os.environ.get("LANKY_LEAN_DISABLE"):
            return False, "disabled by LANKY_LEAN_DISABLE"
        if shutil.which("lean") is None:
            return False, "lean is not on PATH"
        if not _lean_interact_installed():
            return False, "lean_interact is not installed (pip install lanky[lean])"
        if self.session.error is not None:
            return False, self.session.error
        if self.session.server is None:
            return True, "untested until the first fact: the REPL is built on demand"
        return True, f"Lean {self.session.version}" if self.session.version else ""

    def can_establish(self, fact: Fact, /) -> bool:
        """Whether the fact's statement lands in the core-Lean fragment.

        Honesty here is what makes the ladder of oracles work: a reduction or a
        real-valued claim is declined at once and reaches the property tester
        with nothing wasted.
        """
        if fact.term is None:
            return False
        try:
            statement_of(fact.term, fact.owner or fact.id)
        except (UnsupportedTerm, AttributeError, TypeError, ValueError):
            return False
        return True

    def establish(self, fact: Fact, /) -> Fact | None:
        """Try the ladder; ``PROVED`` on success, the fact unchanged otherwise."""
        try:
            statement = statement_of(fact.term, fact.owner or fact.id)
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
            closed, detail = self.session.run(source)
            if closed:
                return fact.with_status(
                    Status.PROVED,
                    self.name,
                    tactic=tactic,
                    lean_source=source,
                    lean_version=self.session.version,
                )
            last = detail
            if self.session.error is not None:
                break
        return fact.with_status(
            fact.status,
            lean_tried=len(ladder),
            lean_reason=self.session.error or last,
        )


# }}}


def use_tactic(claim: Any, script: str) -> None:
    """Pin the tactic script for one claim, bypassing the ladder.

    The escape hatch for a statement the ladder cannot find a proof of. It takes
    a :class:`~lanky.theory.Theorem`, a :class:`~lanky.ledger.Fact` or a fact id,
    and applies to every Lean oracle in the registry, so a file can pin a script
    next to the theorem it belongs to::

        use_tactic(scan_monotone, "intro a ha b hb hab\n  induction b with ...")

    The ledger still records which script closed the goal, so a pinned proof is
    as visible as a found one.
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
