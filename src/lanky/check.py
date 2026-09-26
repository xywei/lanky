"""``lanky check``: import a file, collect its facts, and try to establish them.

The design idea. The decorators are inert and registering, so checking a file is
importing it. Every decorated object lands in the registry in import order; each
registered theory is asked what facts that object claims; each fact is offered to
the oracles from the strongest trust class that is willing to take it down to the
weakest; whatever nobody establishes is recorded as ``ASSUMED`` rather than
dropped. The result is a ledger that reads like the source file.

A check collects the claims the file itself defines, and none from the modules
it imports: ``lanky check a.py b.py`` is how two files are checked together.
"""

from __future__ import annotations

import importlib.machinery
import importlib.util
import inspect
import keyword
import sys
from pathlib import Path
from typing import Any

from lanky import semantics
from lanky.ledger import STATUS_STRENGTH, Fact, Ledger, Status
from lanky.plugins import TRUST_STRENGTH, oracle_availability, registry
from lanky.prelude import FinType, FnType, Refined
from lanky.terms import Forall

__all__ = [
    "check_path",
    "establish",
    "has_hypotheses",
    "hypotheses_fact",
    "import_path",
    "oracle_lines",
]


class _PackageSpec(importlib.machinery.ModuleSpec):
    """A module spec whose parent package is given rather than read off its name.

    ``ModuleSpec.parent`` is the dotted name without its last part, and the
    name :func:`import_path` gives a checked file has no dots, so its parent
    would be empty. A relative import finds its package through
    ``__package__`` and warns when that disagrees with ``__spec__.parent``
    (``__package__`` itself is deprecated in favour of the spec), so the two
    are made to agree here rather than only ``__package__`` being set.
    """

    def __init__(self, spec: importlib.machinery.ModuleSpec, package: str) -> None:
        super().__init__(
            spec.name, spec.loader, origin=spec.origin, loader_state=spec.loader_state
        )
        self.submodule_search_locations = spec.submodule_search_locations
        self.has_location = spec.has_location
        self._package = package

    @property
    def parent(self) -> str:
        """The package the checked file sits in."""
        return self._package


def _package_of(path: Path) -> tuple[str, Path] | None:
    """The package a file sits in, and the directory that package is found from.

    The walk goes up through the directories that carry an ``__init__.py``
    and could be imported by name, so ``root/pkg/sub/mod.py`` gives
    ``("pkg.sub", root)``. A file whose directory is not a package gives
    ``None``.
    """
    parts: list[str] = []
    directory = path.parent
    while (
        directory.name.isidentifier()
        and not keyword.iskeyword(directory.name)
        and (directory / "__init__.py").is_file()
    ):
        parts.append(directory.name)
        directory = directory.parent
    if not parts:
        return None
    return ".".join(reversed(parts)), directory


def _refuse_a_package_imported_elsewhere(path: Path, package: str, root: Path) -> None:
    """Raise ``ImportError`` if this process holds another package of the same name.

    A relative import resolves through ``sys.modules`` before it looks at
    ``sys.path``, so once ``pkg`` (or ``pkg.sub``) has been imported from one
    source tree, a file of another tree's ``pkg`` would have its ``from
    .helpers import ...`` answered by the first tree's modules, and its ledger
    computed from code it does not contain. That happens in ``lanky check
    a/pkg/mod.py b/pkg/mod.py``. Every level of the package that is already
    imported has to be the directory the file sits under; a package imported
    from that same directory, by an earlier check of the same tree, say, is
    the one the file would get anyway.
    """
    parts = package.split(".")
    for depth in range(1, len(parts) + 1):
        name = ".".join(parts[:depth])
        cached = sys.modules.get(name)
        if cached is None:
            continue
        expected = root.joinpath(*parts[:depth]).resolve()
        locations = [Path(entry).resolve() for entry in getattr(cached, "__path__", None) or ()]
        if expected not in locations:
            where = locations[0] if locations else getattr(cached, "__file__", None)
            raise ImportError(
                f"{path} sits in the package {package!r}, but {name!r} is already "
                f"imported from {where or 'somewhere else'} in this process, so a "
                "relative import in the file would resolve there; check it in a "
                "process of its own"
            )


def import_path(path: str | Path) -> Any:
    """Import a file as a module, without making it ``__main__``.

    The file's directory goes on ``sys.path`` so that its imports work, and the
    module keeps a name of its own so that a ``__main__`` guard in the file does
    not fire while it is being checked. That name is registered in
    ``sys.modules`` only while the file executes and then withdrawn, so two
    files with the same basename do not share one entry; the module object
    returned here stays usable either way.

    A file inside a package keeps that name as well, and is given the package
    it sits in (see :func:`_package_of`), so that a relative import in it
    resolves the way it does when the package imports the file:
    ``__package__`` and ``__spec__.parent`` name the package, and the
    directory the package is found from joins ``sys.path`` while the file
    executes. The package is not imported up front. The file's first relative
    import imports it the ordinary way, and it then stays imported like any
    other package; a file with no relative import never runs its package's
    ``__init__``, as before. A package of the same name already imported
    from another directory is refused with ``ImportError`` rather than
    lent to the file (see :func:`_refuse_a_package_imported_elsewhere`).
    """
    path = Path(path).resolve()
    if not path.is_file():
        raise FileNotFoundError(str(path))
    name = f"lanky_checked_{path.stem}"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot import {path}")
    directories = [str(path.parent)]
    package = _package_of(path)
    if package is not None:
        _refuse_a_package_imported_elsewhere(path, *package)
        spec = _PackageSpec(spec, package[0])
        directories.append(str(package[1]))
    module = importlib.util.module_from_spec(spec)
    added = [entry for entry in dict.fromkeys(directories) if entry not in sys.path]
    for entry in reversed(added):
        sys.path.insert(0, entry)
    previous = sys.modules.get(name)
    sys.modules[name] = module
    try:
        spec.loader.exec_module(module)
    finally:
        for entry in added:
            sys.path.remove(entry)
        # The entry exists so that machinery that looks a class up by its
        # module (dataclasses, pickle) works while the file is executing. It is
        # dropped again afterwards: two files with the same basename would
        # otherwise share one entry, and a long-lived process would keep every
        # file it ever checked alive. The module object returned here, and the
        # globals its functions close over, stay valid either way.
        if previous is None:
            sys.modules.pop(name, None)
        else:
            sys.modules[name] = previous
    return module


def establish(fact: Fact, verbose: bool = False) -> Fact:
    """Offer one fact to the oracles, strongest trust class first.

    Before anything is offered, the fact is annotated with the semantics gaps
    its term is exposed to (see :mod:`lanky.semantics`): a statement that may
    divide by zero is a theorem in Lean and an exception in Python. When a fact
    with such a gap, or with hypotheses, is established by something stronger
    than a test, the test is still run afterwards as a cross-check (see
    :func:`_cross_check`); it cannot change the status, but what it finds is
    recorded rather than lost.

    Last, a fact whose hypotheses no draw satisfied is examined for vacuity
    (:func:`_examine_vacuity`): a claim that nothing is ever at stake in says
    nothing, however strongly it is established, and the ledger says so.

    The oracle that settles a fact, establishing or refuting it, leaves its
    trust class in the provenance as ``trust_class``. A status says what kind
    of evidence a fact has, and the trust class says how far its decider is to
    be trusted: ``decided`` by a decision procedure and ``decided`` by a
    heuristic are worth different things, and the table marks the second
    (see :meth:`lanky.ledger.Ledger.render`). A heuristic's answer is not
    guaranteed and a counterexample is, so a fact a heuristic established is
    sampled all the same, and a counterexample overrules it
    (:func:`_overrule`).

    An axiom (:attr:`~lanky.ledger.Fact.is_axiom`) is only ever refuted, or
    shown vacuous (see :func:`_examine_axiom`). It is ``assumed`` on its
    citation, which is its author's word and not an oracle's, and a stronger
    status from one would make it a theorem that says it is an axiom. Its
    semantics gaps are noted all the same, since the sampling that looks for
    a counterexample to it is the reading a gap leaves without an answer.
    """
    gaps = semantics.notes(fact.term)
    if gaps:
        fact = fact.with_status(fact.status, semantics=list(gaps))
        if verbose:
            for note in gaps:
                print(f"  semantics: {note}")
    if fact.is_axiom:
        return _examine_axiom(fact, verbose=verbose)
    for oracle in registry.sorted_oracles():
        available, reason = oracle_availability(oracle)
        if not available:
            continue
        try:
            if not oracle.can_establish(fact):
                continue
            result = oracle.establish(fact)
        except Exception as exc:  # noqa: BLE001 - one oracle must not stop the rest
            if verbose:
                print(f"  {oracle.name} raised {type(exc).__name__}: {exc}")
            continue
        if result is None:
            continue
        if result.status is not Status.ASSUMED:
            result = result.with_status(result.status, trust_class=oracle.trust_class())
            overruled = _overrule(fact, result, verbose=verbose)
            fact = overruled or _cross_check(result, gaps, verbose=verbose)
            break
        fact = result
    return _examine_vacuity(fact, verbose=verbose)


def _overrule(fact: Fact, result: Fact, verbose: bool = False) -> Fact | None:
    """A counterexample to what a heuristic established, as the refuted fact; else ``None``.

    ``fact`` is the fact as the heuristic was handed it and ``result`` what it
    made of it. A heuristic's answer is worth more than a sample's pass and is
    still not guaranteed, while a counterexample is definite, so the oracles
    of the ``test`` trust class sample a fact a heuristic established, whether
    or not it has hypotheses or a semantics gap, and a refutation from one
    stands in place of the heuristic's answer. The provenance says what was
    overruled, as ``overruled``, and so does the last line of the ``reason``,
    which ``lanky check`` prints under the table. Nothing is done for a
    heuristic's refutation, which a sample cannot overturn, or for an oracle
    of any other class.
    """
    if result.provenance.get("trust_class") != "heuristic" or result.status is Status.REFUTED:
        return None
    for oracle in registry.sorted_oracles():
        if TRUST_STRENGTH.get(oracle.trust_class(), 0) != TRUST_STRENGTH["test"]:
            continue
        available, _reason = oracle_availability(oracle)
        if not available:
            continue
        try:
            if not oracle.can_establish(fact):
                continue
            sampled = oracle.establish(fact)
        except Exception:  # noqa: BLE001 - a sample must not fail a check
            continue
        if sampled is None or sampled.status is not Status.REFUTED:
            continue
        overruled = f"{result.decided_by}, a heuristic, {result.status.value} it"
        if verbose:
            print(f"  {oracle.name} refutes what {overruled}")
        reason = sampled.provenance.get("reason")
        note = f"{overruled}, and this draw overrules it"
        return sampled.with_status(
            Status.REFUTED,
            trust_class=oracle.trust_class(),
            overruled=overruled,
            reason=f"{reason}\n{note}" if reason else note,
        )
    return None


def _examine_axiom(fact: Fact, verbose: bool = False) -> Fact:
    """Sample an axiom for a counterexample, and keep it ``assumed`` without one.

    An axiom is taken on its citation, so no oracle is asked to establish it.
    It can still be false as written: a citation copied down with a sign
    flipped or a bound off by one states something the reference does not,
    and everything that rests on it rests on that. A counterexample is
    definite whatever the citation says, so the oracles of the ``test`` trust
    class sample it, as they sample any statement, and a refutation is kept,
    with the citation still in the provenance, so that ``lanky check`` fails
    on it. A pass is not kept, since it would make the axiom a tested theorem.
    The stronger oracles are not asked: what they establish would be thrown
    away the same way, and a prover's attempt costs what a sample does not.

    What is kept of a pass is what it says against the hypotheses. An axiom
    whose hypotheses no draw satisfied is examined for vacuity as a theorem
    is (:func:`_examine_vacuity`), since hypotheses copied down wrong are as
    likely as a goal copied down wrong: when a stronger oracle shows them
    inconsistent the axiom is ``vacuous`` and the check fails, and otherwise
    it gets the same warning. That asks the stronger oracles about the
    hypotheses alone, never about the axiom.
    """
    marks: dict[str, Any] = {}
    for oracle in registry.sorted_oracles():
        if TRUST_STRENGTH.get(oracle.trust_class(), 0) != TRUST_STRENGTH["test"]:
            continue
        available, _reason = oracle_availability(oracle)
        if not available:
            continue
        try:
            if not oracle.can_establish(fact):
                continue
            result = oracle.establish(fact)
        except Exception as exc:  # noqa: BLE001 - one oracle must not stop the rest
            if verbose:
                print(f"  {oracle.name} raised {type(exc).__name__}: {exc}")
            continue
        if result is None:
            continue
        if result.status is Status.REFUTED:
            if verbose:
                print(f"  {oracle.name} refutes the axiom {fact.owner} as it is written")
            return result.with_status(result.status, trust_class=oracle.trust_class())
        if not marks:
            unsatisfied = _never_satisfied(result.provenance)
            untestable = _never_drawn(result.provenance)
            if unsatisfied:
                marks = {
                    "unsatisfied": unsatisfied,
                    "unsatisfied_detail": _skipped(result.provenance),
                }
            elif untestable:
                marks = {"untestable": untestable}
    if marks:
        fact = fact.with_status(fact.status, **marks)
    return _examine_vacuity(fact, verbose=verbose)


def has_hypotheses(term: Any) -> bool:
    """Whether a statement assumes something that a draw of its variables can fail.

    That is a guard, which is what a theorem's hypotheses become, or a binder
    whose domain restricts its sort: a point of ``Fin[n]`` has to be below
    ``n``, and a refined variable has to satisfy its refinement. Lean states
    all of them as hypotheses of the theorem it is asked. So does a family
    whose values are restricted in the same way: ``Fn[Fin[1], Nat & False]``
    has no member, because its one value has nowhere to go. A variable of a
    plain sort, or a family into one, assumes nothing a draw can miss.
    """
    if not isinstance(term, Forall):
        return False
    if term.guard is not None:
        return True
    return any(_restricts(domain) for _var, domain in term.binders)


def _restricts(domain: Any) -> bool:
    """Whether a binder's domain, or the values of a family it is, restrict a sort."""
    if isinstance(domain, FinType | Refined):
        return True
    if isinstance(domain, FnType):
        return _restricts(domain.codomain)
    return False


def _never_satisfied(provenance: dict) -> str | None:
    """What a property test's record says about the hypotheses, if it is that none held.

    The record is the one :class:`~lanky.oracles.test.TestOracle` leaves when
    no draw was valid. A draw the statement could not be decided at (an
    existential no draw witnessed, a division by zero, a hypothesis whose
    sampled universal held at every draw, which admits no draw for certain)
    did not find the hypotheses false, so a record with any such draw says
    nothing against them. Neither does a draw of a sort
    the tester has no sampler for, which never reached them (see
    :func:`_never_drawn`).
    """
    if provenance.get("valid") != 0 or not provenance.get("untested"):
        return None
    if provenance.get("undecided") or provenance.get("unsampleable"):
        return None
    return f"hypotheses never satisfied in {provenance.get('samples', 0)} draws"


def _never_drawn(provenance: dict) -> str | None:
    """What a property test's record says when no draw reached the hypotheses at all.

    A family over ``Nat`` has no sampler, so every draw of a statement that
    quantifies over one stops before its hypotheses are evaluated
    (:class:`~lanky.testing.Unsampleable`). That is no evidence against the
    hypotheses, so it is no ground for a warning, but it is no evidence for
    them either, and the stronger oracles are still asked whether they are
    inconsistent.
    """
    if provenance.get("valid") != 0 or provenance.get("undecided"):
        return None
    if not provenance.get("unsampleable"):
        return None
    return provenance.get("untested") or "no draw could be completed"


def _skipped(provenance: dict) -> str | None:
    """Why a draw could not be completed, when a test's record says one could not.

    An empty ``Fin`` or a refinement no value satisfies is a hypothesis that
    fails before the guard is reached, and a reader of a warning needs to know
    which one it was.
    """
    skipped = provenance.get("skipped") or ()
    return f"a draw could not be completed: {skipped[0]}" if skipped else None


def _cross_check(fact: Fact, gaps: tuple[str, ...], verbose: bool = False) -> Fact:
    """Sample a fact a stronger oracle established, and record what sampling says.

    Only for a fact that carries a semantics note or has hypotheses (see
    :func:`has_hypotheses`), and only to record what the sampled reading says.
    The status a stronger oracle gave stands.

    Three things are worth recording. A counterexample is the loud one: the
    Python reading is false where a stronger oracle established the statement,
    which with one reading of arithmetic for every oracle means that one of them
    is wrong. The second is a sampled reading that could not be run at all,
    which is what a division by zero does: Lean's division is total and
    Python's raises, so there is no counterexample and no evidence either, and a
    ledger that said nothing here would suggest the two readings had been
    compared. The third is that no draw satisfied the hypotheses, which is the
    evidence a vacuous claim leaves (see :func:`_examine_vacuity`); a proof from
    hypotheses nothing satisfies is valid and says nothing. A test that could
    not draw at all is recorded as ``untestable``, so that the hypotheses are
    still examined.
    """
    if fact.status in (Status.REFUTED, Status.TESTED, Status.ASSUMED):
        return fact
    if not gaps and not has_hypotheses(fact.term):
        return fact
    for oracle in registry.sorted_oracles():
        if TRUST_STRENGTH.get(oracle.trust_class(), 0) != TRUST_STRENGTH["test"]:
            continue
        available, _reason = oracle_availability(oracle)
        if not available:
            continue
        try:
            if not oracle.can_establish(fact):
                continue
            result = oracle.establish(fact)
        except Exception:  # noqa: BLE001 - a cross-check must not fail a check
            continue
        if result is None:
            continue
        if result.status is Status.REFUTED:
            counterexample = result.provenance.get("counterexample")
            if verbose:
                print(
                    f"  {oracle.name} refutes the sampled reading of a "
                    f"{fact.status.value} fact: {counterexample}"
                )
            return fact.with_status(
                fact.status,
                semantics_disagreement=(
                    f"{oracle.name} refutes this statement under lanky's Python reading"
                ),
                semantics_counterexample=counterexample,
            )
        unsatisfied = _never_satisfied(result.provenance)
        if unsatisfied:
            if verbose:
                print(f"  {oracle.name}: {unsatisfied}")
            return fact.with_status(
                fact.status,
                unsatisfied=unsatisfied,
                unsatisfied_detail=_skipped(result.provenance),
            )
        untestable = _never_drawn(result.provenance)
        if untestable:
            if verbose:
                print(f"  {oracle.name}: {untestable}")
            return fact.with_status(fact.status, untestable=untestable)
        undecided = result.provenance.get("untested")
        if gaps and undecided and result.provenance.get("undecided"):
            if verbose:
                print(f"  {oracle.name} could not run the sampled reading: {undecided}")
            return fact.with_status(fact.status, semantics_undecided=undecided)
    return fact


def _examine_vacuity(fact: Fact, verbose: bool = False) -> Fact:
    """Ask whether a fact whose hypotheses no draw satisfied is vacuous.

    The property tester's word is evidence and not proof: hypotheses that hold
    somewhere the sampler rarely looks (``n == 1000`` over naturals drawn up to
    five) leave the same record as hypotheses that hold nowhere. So the
    stronger oracles are asked the definite question, whether the hypotheses
    alone prove ``False`` (:func:`_inconsistency`). When one of them says yes,
    the fact is marked ``vacuous`` in its provenance, the ledger shows it, and
    ``lanky check`` exits 1: the claim is true and says nothing, and the usual
    cause is a mistake in the hypotheses. When none can, the fact keeps
    ``unsatisfied`` in its provenance and ``lanky check`` prints a warning.

    A test that could not draw at all, because a sort has no sampler, is no
    evidence either way (:func:`_never_drawn`): the question is asked all the
    same, and when no oracle answers it nothing is printed, because nothing
    suggests the claim is vacuous.

    This runs whoever established the fact, so a statement whose goal no
    oracle can take but whose hypotheses Lean can refute is caught too.
    """
    if fact.status is Status.REFUTED or not has_hypotheses(fact.term):
        return fact
    unsatisfied = fact.provenance.get("unsatisfied") or _never_satisfied(fact.provenance)
    untestable = fact.provenance.get("untestable") or _never_drawn(fact.provenance)
    if not unsatisfied and not untestable:
        return fact
    if unsatisfied and "unsatisfied" not in fact.provenance:
        fact = fact.with_status(
            fact.status,
            unsatisfied=unsatisfied,
            unsatisfied_detail=_skipped(fact.provenance),
        )
    found = _inconsistency(fact, verbose=verbose)
    if found is None:
        return fact
    name, result = found
    if verbose:
        print(f"  {name} shows the hypotheses of {fact.owner} inconsistent")
    evidence = {
        key: value for key, value in result.provenance.items() if key not in ("path", "line")
    }
    marks = {} if unsatisfied else {"untestable": untestable}
    return fact.with_status(
        fact.status,
        vacuous=f"the hypotheses are inconsistent: {result.status.value} by {name}",
        vacuous_by=name,
        vacuous_evidence=evidence,
        **marks,
    )


def hypotheses_fact(fact: Fact) -> Fact:
    """The claim that a fact's hypotheses are inconsistent, as a fact of its own.

    Its term keeps the binders and the guard and replaces the goal by
    ``False``, so an oracle that establishes it has shown that nothing
    satisfies the hypotheses. It has an id and a kind of its own, so no
    tactic pinned to the original fact and no plugin that recognizes the
    original kind takes it for the original.

    Raises:
        ValueError: If the fact's term is not a quantified statement, which is
            the only kind that has hypotheses.
    """
    term = fact.term
    if not isinstance(term, Forall):
        raise ValueError(f"{fact.id} has no hypotheses: its term is not a quantified statement")
    return Fact(
        id=f"{fact.id}:hypotheses",
        kind="hypotheses",
        statement=f"the hypotheses of {fact.owner or fact.id} are inconsistent",
        term=Forall(term.binders, False, term.guard),
        provenance={
            key: fact.provenance[key] for key in ("path", "line") if key in fact.provenance
        },
        where=fact.where,
        owner=fact.owner,
    )


def _inconsistency(fact: Fact, verbose: bool = False) -> tuple[str, Fact] | None:
    """The first decision procedure or kernel that proves the hypotheses inconsistent.

    Returns the oracle's name and the fact it established (see
    :func:`hypotheses_fact`), or ``None`` when no such oracle establishes it.
    A test cannot: no draw satisfying the hypotheses is exactly what is in
    question. Neither can a heuristic. Its answer is not guaranteed, and what
    keeps a wrong one out of the ledger elsewhere is a counterexample overruling
    it (:func:`_overrule`), which a question no draw satisfies cannot have; so
    a vacuous fact, which fails the check, needs an answer that is. For consistent
    hypotheses every attempt fails, so what Lean is asked is its short ladder,
    which for a goal of ``False`` is the five cheap tactics.
    """
    question = hypotheses_fact(fact)
    for oracle in registry.sorted_oracles():
        if TRUST_STRENGTH.get(oracle.trust_class(), 0) <= TRUST_STRENGTH["heuristic"]:
            continue
        available, _reason = oracle_availability(oracle)
        if not available:
            continue
        try:
            if not oracle.can_establish(question):
                continue
            result = oracle.establish(question)
        except Exception as exc:  # noqa: BLE001 - one oracle must not stop the rest
            if verbose:
                print(f"  {oracle.name} raised {type(exc).__name__}: {exc}")
            continue
        if result is None:
            continue
        if STATUS_STRENGTH.get(result.status, 0) > STATUS_STRENGTH[Status.TESTED]:
            return oracle.name, result
    return None


def oracle_lines() -> list[str]:
    """One line per registered oracle: its trust class, and what it can do.

    An oracle that is available may still have something to say (that it has
    not been exercised yet, say), and it is printed in parentheses after
    ``available`` rather than dropped.
    """
    lines = []
    for oracle in registry.sorted_oracles():
        available, reason = oracle_availability(oracle)
        if available:
            state = f"available ({reason})" if reason else "available"
        else:
            state = f"unavailable: {reason}"
        lines.append(f"{oracle.name} ({oracle.trust_class()}): {state}")
    return lines


def _owned(obj: Any, path: Path, module: Any) -> bool | None:
    """Whether ``obj`` was defined by this check's import of the file at ``path``.

    The answer comes from the function the object wraps: the object itself
    when it is a function, or what its ``__wrapped__`` chain leads to, which
    :func:`functools.update_wrapper` sets and which ``@theorem`` and loopty's
    decorators both use. Two things have to agree. The function's code was
    compiled from ``path``, which is where it was defined; and its globals are
    the namespace of the module :func:`import_path` just executed, which tells
    this execution of the file apart from another one in the same process. A
    package whose ``__init__`` imports the checked file runs it a second time,
    under its real name, when the check imports the package (a relative
    import in the file does), and the claims that copy registers are the same
    claims again.

    ``None`` when the object wraps no function, so that nothing about it says
    where it was written; :func:`check_path` then asks each of its facts for
    the path it records.
    """
    try:
        function = inspect.unwrap(obj)
    except ValueError:  # a cycle of ``__wrapped__``: nothing to read
        return None
    code = getattr(function, "__code__", None)
    if code is None:
        return None
    if Path(code.co_filename).resolve() != path:
        return False
    return getattr(function, "__globals__", None) is vars(module)


def _recorded_in(fact: Fact, path: Path) -> bool:
    """Whether ``fact`` records ``path`` as its source, or records no path at all.

    A fact that records nothing is kept: its object was decorated while the
    file was imported, nothing says it was written anywhere else, and a claim
    the ledger drops is a claim nobody sees.
    """
    recorded = fact.provenance.get("path")
    return recorded is None or Path(str(recorded)).resolve() == path


def check_path(path: str | Path, verbose: bool = False) -> Ledger:
    """Check one file and return the ledger of the claims it defines.

    A claim belongs to the file it was written in. An object decorated while
    the file is imported is checked when it was defined by the file itself
    (see :func:`_owned`), and a claim that lives in a module the file imports
    is not collected, on the first check or any other: ``lanky check main.py
    helpers.py`` checks both files, each for its own claims. Ownership is read
    off where each object was defined rather than off the order of the
    imports, so a module that was imported before the check, and runs nothing
    now, changes nothing, and checking a file twice gives the same ledger
    twice. Nothing is withdrawn from ``sys.modules`` for that: an imported
    module stays imported, as it would anywhere else.

    Only the objects this import registers are considered, and they are
    released from the registry afterwards, so checking several files in one
    process keeps their ledgers apart and does not accumulate them.
    """
    import lanky.oracles  # noqa: F401 - registers the built-in oracles

    registry.load_entry_points()
    path = Path(path).resolve()
    with registry.collecting() as decorated:
        module = import_path(path)
    ledger = Ledger()
    for obj in decorated:
        owned = _owned(obj, path, module)
        if owned is False:
            continue
        for theory in registry.theories:
            for fact in theory.facts(obj):
                if owned is None and not _recorded_in(fact, path):
                    continue
                if verbose:
                    print(f"{fact.where} {fact.owner}: {fact.statement}")
                ledger.add(establish(fact, verbose=verbose))
    return ledger
