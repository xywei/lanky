"""Plugin interfaces and the registry.

The design idea. lanky is a thin host. It owns the ledger and four extension
points, and knows nothing about any particular mathematics. A theory turns
decorated Python objects into facts; an oracle establishes facts and says how
much it should be trusted; an executor runs decorated objects; a verb is a
subcommand of the ``lanky`` command. The sister project loopty is a plugin: it
registers a kernel theory, an isl oracle, a loopy executor and a ``run`` verb,
and lanky never imports it.

Two mechanisms make that work. Discovery is by entry points, in the four groups
named below, so installing loopty is all it takes. Registration is also possible
in process, which is what the decorators do: ``@theorem`` records the decorated
object in :data:`registry` in import order, and ``lanky check FILE`` imports the
file and then reads the registry.

The protocols are structural. A plugin satisfies one by having the right
methods; importing lanky at run time is not required of it.
"""

from __future__ import annotations

import contextlib
from collections.abc import Iterator
from importlib.metadata import entry_points
from typing import Any, Protocol, runtime_checkable

__all__ = [
    "ENTRY_POINT_GROUPS",
    "EXECUTOR_GROUP",
    "ORACLE_GROUP",
    "THEORY_GROUP",
    "TRUST_STRENGTH",
    "VERB_GROUP",
    "Executor",
    "Oracle",
    "Registry",
    "Theory",
    "Verb",
    "oracle_availability",
    "registry",
]

#: Entry-point group for theories: vocabularies of statements and their decorators.
THEORY_GROUP = "lanky.theories"

#: Entry-point group for oracles: things that establish facts.
ORACLE_GROUP = "lanky.oracles"

#: Entry-point group for executors: things that run decorated Python objects.
EXECUTOR_GROUP = "lanky.executors"

#: Entry-point group for CLI verbs: subcommands of the ``lanky`` command.
VERB_GROUP = "lanky.verbs"

ENTRY_POINT_GROUPS = (THEORY_GROUP, ORACLE_GROUP, EXECUTOR_GROUP, VERB_GROUP)

#: How much a trust class is worth. Oracles are tried strongest first.
TRUST_STRENGTH: dict[str, int] = {
    "kernel": 3,
    "decision-procedure": 2,
    "test": 1,
}


@runtime_checkable
class Theory(Protocol):
    """A vocabulary of statements, exposed as a decorator.

    A theory turns an ordinary Python object, typically a typed function whose
    parameters are the variables and hypotheses and whose return annotation is
    the goal, into facts. It owns the reading of annotations and decides what
    they are allowed to say.

    The decorator is inert in the mypy sense: it records the claim and returns
    something still callable, so the body remains executable Python.
    """

    name: str

    def __call__(self, obj: Any, /) -> Any:
        """Decorate ``obj``, registering it, and return something callable."""
        ...

    def facts(self, obj: Any, /) -> tuple:
        """The facts ``obj`` claims, or an empty tuple if this theory does not own it."""
        ...


@runtime_checkable
class Oracle(Protocol):
    """Something that establishes facts, and says how much it should be trusted.

    Oracles are the only way a fact's status improves. They are tried from the
    strongest trust class that can handle the fact to the weakest: a Lean kernel
    proof, then a decision procedure such as isl, then a property test. Hence
    both methods: :meth:`can_establish` is the cheap question asked of every
    oracle in turn, :meth:`establish` does the work.

    An oracle may also expose ``availability() -> (bool, str)`` to explain, in
    one line, why it is not going to do anything (no Lean on the PATH, for
    instance). See :func:`oracle_availability`.
    """

    name: str

    def trust_class(self) -> str:
        """Name the kind of evidence produced: ``kernel``, ``decision-procedure``, ``test``."""
        ...

    def can_establish(self, fact: Any, /) -> bool:
        """Whether this oracle is willing to try this fact."""
        ...

    def establish(self, fact: Any, /) -> Any:
        """Try to establish ``fact``; return an updated fact, or ``None`` to decline."""
        ...


@runtime_checkable
class Executor(Protocol):
    """Something that runs a decorated object.

    The default executor is plain ``python``: it calls the body. Others run the
    object differently (loopty hands its kernels to loopy), but all of them
    answer the same question: what happens when this object is actually run?
    """

    name: str

    def run(self, obj: Any, /, *args: Any, **kwargs: Any) -> Any:
        """Run the decorated object and return its result."""
        ...


@runtime_checkable
class Verb(Protocol):
    """A subcommand of the ``lanky`` command-line tool."""

    name: str
    help: str

    def add_arguments(self, parser: Any, /) -> None:
        """Declare this verb's command-line arguments on ``parser``."""
        ...

    def run(self, args: Any, /) -> int:
        """Execute the verb and return a process exit code."""
        ...


def oracle_availability(oracle: Any) -> tuple[bool, str]:
    """Whether ``oracle`` can do anything here, and why not when it cannot.

    An oracle that does not answer the question is assumed available, so the
    common case needs no code.

    An oracle whose answer is an exception is unavailable, with the exception as
    the reason. The probe is where an optional oracle finds out that a native
    dependency is missing, so raising there is the ordinary way for it to fail,
    and it must cost that one oracle and not the check: the callers ask before
    they reach the per-oracle handler in :func:`lanky.check.establish`, and an
    exception here used to abort the whole check and make ``lanky check``
    report the checked file as unimportable.
    """
    query = getattr(oracle, "availability", None)
    if query is None:
        return True, ""
    try:
        available, reason = query()
    except Exception as exc:  # noqa: BLE001 - one broken oracle must not stop the rest
        return False, f"its availability check raised {type(exc).__name__}: {exc}"
    return bool(available), str(reason)


class Registry:
    """What is installed and what has been decorated, in import order.

    The registry is deliberately plain: four lists, a list of decorated objects,
    and a table of term lowerings. ``lanky check FILE`` imports the file, which
    runs the decorators, which fill ``objects``; the theories then turn those
    objects into facts.

    A plugin is identified by its ``name`` within its kind, and registering a
    second one under a name already present is ignored. That matters because a
    plugin can arrive twice: loopty registers its kernel theory when
    ``loopty.kernel`` is imported and again through the ``lanky.theories`` entry
    point, and two copies of one theory would compute every fact twice. Pass
    ``replace=True`` to swap a registered plugin for another of the same name,
    which is the only way to displace one. An object with no ``name`` is not
    deduplicated, since there is nothing to compare.
    """

    def __init__(self) -> None:
        self.theories: list[Any] = []
        self.oracles: list[Any] = []
        self.executors: list[Any] = []
        self.verbs: list[Any] = []
        self.objects: list[Any] = []
        #: Term type to lowering callable; how loopty turns ``Sum`` into a reduction.
        self.term_lowerings: dict[type, Any] = {}
        self._loaded_groups: set[str] = set()

    # {{{ in-process registration

    @staticmethod
    def _install(installed: list[Any], plugin: Any, replace: bool) -> Any:
        """Put ``plugin`` in ``installed`` unless its name is already there.

        Returns the plugin, so every ``register_*`` works as a decorator whether
        or not the registration was a duplicate.
        """
        name = getattr(plugin, "name", None)
        if name is not None:
            for index, existing in enumerate(installed):
                if getattr(existing, "name", None) == name:
                    if replace:
                        installed[index] = plugin
                    return plugin
        installed.append(plugin)
        return plugin

    def register_theory(self, theory: Any, replace: bool = False) -> Any:
        """Register a theory; returns it, so this works as a decorator."""
        return self._install(self.theories, theory, replace)

    def register_oracle(self, oracle: Any, replace: bool = False) -> Any:
        """Register an oracle; returns it, so this works as a decorator."""
        return self._install(self.oracles, oracle, replace)

    def register_executor(self, executor: Any, replace: bool = False) -> Any:
        """Register an executor; returns it, so this works as a decorator."""
        return self._install(self.executors, executor, replace)

    def register_verb(self, verb: Any, replace: bool = False) -> Any:
        """Register a CLI verb; returns it, so this works as a decorator."""
        return self._install(self.verbs, verb, replace)

    def register_object(self, obj: Any) -> Any:
        """Record a decorated object in import order; returns it.

        Decorated objects are not deduplicated: two theorems may well have the
        same name, and their order is the order of the file.
        """
        self.objects.append(obj)
        return obj

    @contextlib.contextmanager
    def collecting(self) -> Iterator[list[Any]]:
        """Collect the objects registered inside the block, then release them.

        ``lanky check FILE`` wants exactly the objects that importing ``FILE``
        decorated, and wants them gone afterwards, so that checking many files
        in one process neither mixes their ledgers nor grows without bound. The
        yielded list is filled when the block exits::

            with registry.collecting() as decorated:
                import_path(path)
            for obj in decorated:
                ...
        """
        first = len(self.objects)
        collected: list[Any] = []
        try:
            yield collected
        finally:
            collected.extend(self.objects[first:])
            del self.objects[first:]

    def register_term_lowering(self, term_type: type, lowering: Any) -> Any:
        """Register how one term type is lowered by a plugin; returns the lowering."""
        self.term_lowerings[term_type] = lowering
        return lowering

    # }}}

    def sorted_oracles(self) -> list[Any]:
        """The oracles, strongest trust class first."""
        return sorted(
            self.oracles,
            key=lambda o: TRUST_STRENGTH.get(o.trust_class(), 0),
            reverse=True,
        )

    def load_entry_points(self, reload: bool = False) -> None:
        """Discover installed plugins through the four entry-point groups.

        Each entry point may name an instance or a class; a class is
        instantiated with no arguments. Groups already loaded are skipped unless
        ``reload`` is set, so calling this on every command is cheap.
        """
        register = {
            THEORY_GROUP: self.register_theory,
            ORACLE_GROUP: self.register_oracle,
            EXECUTOR_GROUP: self.register_executor,
            VERB_GROUP: self.register_verb,
        }
        for group in ENTRY_POINT_GROUPS:
            if group in self._loaded_groups and not reload:
                continue
            self._loaded_groups.add(group)
            for entry_point in entry_points(group=group):
                plugin = entry_point.load()
                if isinstance(plugin, type):
                    plugin = plugin()
                register[group](plugin)

    def __repr__(self) -> str:
        """Summarize what is registered."""
        return (
            f"Registry(theories={len(self.theories)}, oracles={len(self.oracles)}, "
            f"executors={len(self.executors)}, verbs={len(self.verbs)}, "
            f"objects={len(self.objects)})"
        )


#: The registry the decorators and the CLI use.
registry = Registry()
