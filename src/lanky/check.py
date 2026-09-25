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
from lanky.ledger import Fact, Ledger, Status
from lanky.plugins import TRUST_STRENGTH, oracle_availability, registry

__all__ = ["check_path", "establish", "import_path", "oracle_lines"]


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
    ``__init__``, as before.
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
