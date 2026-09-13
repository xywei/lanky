"""Plugin interfaces.

PREPARED, NOT IMPLEMENTED.

lanky is a thin plugin host. It owns the ledger (see :mod:`lanky.ledger`) and four
extension points, discovered through the entry-point groups named by the module
constants below. Everything domain-specific -- the Lean session, a polyhedral
theory, a new CLI verb -- arrives as a plugin. The sister project ``loopty``
(a typed polyhedral layer over ``loopy``, with ``isl`` as an oracle and ``loopy``
as a code generator) will be the first plugin.

The protocols here are structural: a plugin satisfies one by having the right
methods, with no import of lanky required at runtime.
"""

from __future__ import annotations

from typing import Any, Protocol, runtime_checkable

#: Entry-point group for theories: vocabularies of statements and their decorators.
THEORY_GROUP = "lanky.theories"

#: Entry-point group for oracles: things that establish facts.
ORACLE_GROUP = "lanky.oracles"

#: Entry-point group for executors: things that run decorated Python objects.
EXECUTOR_GROUP = "lanky.executors"

#: Entry-point group for CLI verbs: subcommands of the ``lanky`` command.
VERB_GROUP = "lanky.verbs"

ENTRY_POINT_GROUPS = (THEORY_GROUP, ORACLE_GROUP, EXECUTOR_GROUP, VERB_GROUP)


@runtime_checkable
class Theory(Protocol):
    """A vocabulary of statements, exposed as a decorator.

    A theory turns an ordinary Python object -- typically a typed function whose
    parameters are the variables and hypotheses and whose return annotation is the
    goal -- into one or more :class:`~lanky.ledger.Fact` objects. It owns the
    translation from Python annotations into the platform's statement language, and
    it decides what the annotations are allowed to say.

    The decorator is inert in the mypy sense: it records the claim and returns
    something still callable, so the body remains executable Python.
    """

    name: str

    def __call__(self, obj: Any, /) -> Any:
        """Decorate ``obj``, registering the facts it claims, and return it."""
        ...

    def facts(self, obj: Any, /) -> tuple:
        """Return the facts claimed by a previously decorated object."""
        ...


@runtime_checkable
class Oracle(Protocol):
    """Something that establishes facts, and says how much it should be trusted.

    Oracles are the only way a fact's status improves. A Lean session driven
    through PyPantograph is the reference oracle: it runs tactics against a live
    goal and can emit a certificate. A decision procedure such as ``isl`` or an SMT
    solver is an oracle too, at a weaker trust class.

    The trust class is reported, never assumed, so the ledger can distinguish a
    kernel-checked certificate from a solver's say-so.
    """

    name: str

    def trust_class(self) -> str:
        """Name the kind of evidence this oracle produces (e.g. ``"kernel"``)."""
        ...

    def establish(self, fact: Any, /) -> Any:
        """Attempt to establish ``fact``; return it with an updated status."""
        ...


@runtime_checkable
class Executor(Protocol):
    """Something that runs a decorated object.

    The default executor is plain ``python``: it calls the theorem's body, drawing
    values for the parameters, so theorems double as property tests and facts reach
    status ``TESTED``. Other executors run the object differently -- ``loopty``'s
    code generator will hand its decorated kernels to ``loopy`` -- but all of them
    answer the same question: what happens when this object is actually run?
    """

    name: str

    def run(self, obj: Any, /, *args: Any, **kwargs: Any) -> Any:
        """Run the decorated object and return its result."""
        ...


@runtime_checkable
class Verb(Protocol):
    """A subcommand of the ``lanky`` command-line tool.

    Planned built-in verbs are ``check``, ``certify``, ``watch``, and ``shell``.
    Plugins add their own; the host supplies argument parsing, plugin discovery, and
    access to the ledger.
    """

    name: str
    help: str

    def add_arguments(self, parser: Any, /) -> None:
        """Declare this verb's command-line arguments on ``parser``."""
        ...

    def run(self, args: Any, /) -> int:
        """Execute the verb and return a process exit code."""
        ...
