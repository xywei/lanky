"""``lanky check``: import a file, collect its facts, and try to establish them.

The design idea. The decorators are inert and registering, so checking a file is
importing it. Every decorated object lands in the registry in import order; each
registered theory is asked what facts that object claims; each fact is offered to
the oracles from the strongest trust class that is willing to take it down to the
weakest; whatever nobody establishes is recorded as ``ASSUMED`` rather than
dropped. The result is a ledger that reads like the source file.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from typing import Any

from lanky import semantics
from lanky.ledger import Fact, Ledger, Status
from lanky.plugins import TRUST_STRENGTH, oracle_availability, registry

__all__ = ["check_path", "establish", "import_path", "oracle_lines"]


def import_path(path: str | Path) -> Any:
    """Import a file as a module, without making it ``__main__``.

    The file's directory goes on ``sys.path`` so that its imports work, and the
    module keeps a name of its own so that a ``__main__`` guard in the file does
    not fire while it is being checked. That name is registered in
    ``sys.modules`` only while the file executes and then withdrawn, so two
    files with the same basename do not share one entry; the module object
    returned here stays usable either way.
    """
    path = Path(path).resolve()
    if not path.is_file():
        raise FileNotFoundError(str(path))
    name = f"lanky_checked_{path.stem}"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    directory = str(path.parent)
    added = directory not in sys.path
    if added:
        sys.path.insert(0, directory)
    previous = sys.modules.get(name)
    sys.modules[name] = module
    try:
        spec.loader.exec_module(module)
    finally:
        if added:
            sys.path.remove(directory)
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
    its term is exposed to (see :mod:`lanky.semantics`), because a statement
    that subtracts over ``Nat`` does not mean the same thing to Lean and to the
    property tester. When such a fact is established by something stronger than
    a test, the test is still run afterwards as a cross-check: it cannot change
    the status, but a counterexample under the Python reading of a statement
    Lean proved is exactly the discrepancy the note warns about, and it is
    recorded rather than lost.
    """
    gaps = semantics.notes(fact.term)
    if gaps:
        fact = fact.with_status(fact.status, semantics=list(gaps))
        if verbose:
            for note in gaps:
                print(f"  semantics: {note}")
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
            return _cross_check(result, gaps, verbose=verbose)
        fact = result
    return fact


def _cross_check(fact: Fact, gaps: tuple[str, ...], verbose: bool = False) -> Fact:
    """Sample a fact a stronger oracle established, when the two readings differ.

    Only for a fact carrying a semantics note, and only to record what the
    sampled reading says. The status a stronger oracle gave stands.

    There are two things worth recording. A counterexample is the loud one: the
    Python reading is false where the Lean reading was proved. The quiet one is
    a sampled reading that could not be run at all, which is what a division by
    zero does: Lean's division is total and Python's raises, so there is no
    counterexample and no evidence either, and a ledger that said nothing here
    would suggest the two readings had been compared.
    """
    if not gaps or fact.status in (Status.REFUTED, Status.TESTED, Status.ASSUMED):
        return fact
    for oracle in registry.sorted_oracles():
        if TRUST_STRENGTH.get(oracle.trust_class(), 0) != 1:
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
        if result.status is not Status.REFUTED:
            undecided = result.provenance.get("untested")
            if not undecided or not result.provenance.get("undecided"):
                continue
            if verbose:
                print(f"  {oracle.name} could not run the sampled reading: {undecided}")
            return fact.with_status(fact.status, semantics_undecided=undecided)
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
    return fact


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


def _release_local_modules(before: set[str], directory: Path) -> None:
    """Withdraw the modules the checked file's directory supplied to this import.

    ``import_path`` withdraws the checked file's own module, but a claim can
    live in a module the file imports, and Python imports a module once per
    process: the first check of ``main.py`` executes ``helper.py`` and collects
    its theorems, and a second check finds ``helper`` cached, executes nothing,
    and returns a ledger without them. Withdrawing what the import brought in
    makes every check of a file see the same claims.

    Only modules that were not imported before this check started, and that
    were found *through* ``directory`` (the one ``import_path`` puts on
    ``sys.path``), are withdrawn: a module ``a.b`` whose file is
    ``directory/a/b.py`` or ``directory/a/b/__init__.py``, or a namespace
    package whose path is ``directory/a``. That is the file's own
    neighbourhood and nothing else. The expected place is resolved the way the
    module's own file is, so a neighbouring directory that is a symbolic link
    still counts as the neighbourhood. An installed package imported for the
    first time stays put even when its files happen to sit below the directory
    (a virtual environment in the project root, say), because a second copy of
    a package such as numpy is not something a process survives, and a plugin
    re-imported under the registry that already holds its first copy would no
    longer recognize its own objects.

    For the same reason a submodule stays put when its top-level package was
    imported before the check, even if the submodule itself is new and sits
    next to the file (a plugin whose source tree is the checked file's
    directory, loaded earlier through its entry point). Withdrawing it alone
    would split the package: its next import executes the submodule again and
    rebinds the package's attribute to the new copy, while every module that
    imported from the old one keeps the old classes.
    """
    for name in [name for name in sys.modules if name not in before]:
        if name.split(".", 1)[0] in before:
            continue
        module = sys.modules.get(name)
        expected = directory.joinpath(*name.split("."))
        origin = getattr(module, "__file__", None)
        if origin is not None:
            found = Path(origin).resolve()
            stem = found.name.split(".", 1)[0]
            local = (found.parent, stem) in (
                (expected.parent.resolve(), expected.name),
                (expected.resolve(), "__init__"),
            )
        else:
            local = any(
                Path(entry).resolve() == expected.resolve()
                for entry in getattr(module, "__path__", ())
            )
        if local:
            del sys.modules[name]


def check_path(path: str | Path, verbose: bool = False) -> Ledger:
    """Check one file and return its ledger.

    Only the objects this import registers are checked, so checking several
    files in one process keeps their ledgers apart, and they are released again
    afterwards, so a process that checks many files does not accumulate them.
    The modules next to the file that its import brought in are released too
    (see :func:`_release_local_modules`), so that checking a file twice
    collects the claims it imports twice rather than once.
    """
    import lanky.oracles  # noqa: F401 - registers the built-in oracles

    registry.load_entry_points()
    before = set(sys.modules)
    try:
        with registry.collecting() as decorated:
            import_path(path)
    finally:
        _release_local_modules(before, Path(path).resolve().parent)
    ledger = Ledger()
    for obj in decorated:
        for theory in registry.theories:
            for fact in theory.facts(obj):
                if verbose:
                    print(f"{fact.where} {fact.owner}: {fact.statement}")
                ledger.add(establish(fact, verbose=verbose))
    return ledger
