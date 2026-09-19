"""The prelude: the sorts and index types an annotation may mention.

The design idea. An annotation is an expression, so the things it names must be
ordinary Python objects: ``Nat`` is a value, ``Fin[n]`` is a subscript on a
value, ``Fn[Fin[n], Nat]`` is a subscript with a tuple, and ``T & prop`` is
``__and__`` on a value. Nothing here is a typing construct and nothing is
inspected by a static checker; a hint is data that lanky reads at run time.

Two ideas earn their keep.

*Exactness.* Every scalar sort carries an exactness class, ``exact`` for the
discrete sorts and by default ``approx`` for ``Real``, with ``reassoc``
selectable. A claim that two runs agree means nothing without it, and a
reduction that a schedule reassociates has to say so.

*Index types.* ``Fin[n]`` is the domain ``{0, ..., n-1}``. When ``n`` is a
concrete integer it iterates as ``range(n)``, so the file runs under plain
``python``. When ``n`` is symbolic it yields exactly one generic point, a fresh
bound variable, which is how a generator expression becomes a quantifier or a
reduction over a domain rather than a loop over values.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from typing import Any

from lanky.terms import current_trace, evaluate, render, structurally_equal

__all__ = [
    "Bool",
    "Fin",
    "FinType",
    "Fn",
    "FnType",
    "Int",
    "LankyType",
    "Nat",
    "Prop",
    "Real",
    "Refined",
    "Sort",
    "exactness_of",
]

#: The exactness classes, from strongest to weakest.
EXACTNESS_CLASSES = ("exact", "reassoc", "approx")


class LankyType:
    """Anything an annotation may use as the type of a variable.

    The one operation every type has is refinement: ``T & prop`` is the subtype
    of ``T`` whose inhabitants satisfy ``prop``. It is written with ``&`` because
    that is the only spare binary operator that reads like conjunction.
    """

    def __and__(self, prop: Any) -> Refined:
        """Refine this type by a proposition."""
        return Refined(self, (prop,))


@dataclass(frozen=True)
class Sort(LankyType):
    """A scalar sort, such as ``Nat`` or ``Real``, with its exactness class."""

    name: str
    exactness: str = "exact"

    def __str__(self) -> str:
        """Print the sort, naming the exactness class when it is not the default."""
        default = "approx" if self.name == "Real" else "exact"
        return self.name if self.exactness == default else f"{self.name}[{self.exactness}]"

    def __iter__(self) -> Any:
        """Yield the one generic point of the sort, inside binder tracing.

        A sort has no extent, so this only makes sense symbolically: it is what
        lets a statement quantify over all naturals. A property test samples
        such a binder rather than enumerating it.
        """
        return _GenericPoint(self)

    def with_exactness(self, exactness: str) -> Sort:
        """This sort at another exactness class."""
        if exactness not in EXACTNESS_CLASSES:
            raise ValueError(f"unknown exactness class {exactness!r}")
        return replace(self, exactness=exactness)

    @property
    def exact(self) -> Sort:
        """This sort with exact arithmetic demanded (no reassociation, no atomics)."""
        return self.with_exactness("exact")

    @property
    def reassoc(self) -> Sort:
        """This sort allowing reassociation, which is what a reduction tree needs."""
        return self.with_exactness("reassoc")

    @property
    def approx(self) -> Sort:
        """This sort allowing any approximation within the target's contract."""
        return self.with_exactness("approx")


#: The natural numbers.
Nat = Sort("Nat", "exact")
#: The integers.
Int = Sort("Int", "exact")
#: The booleans.
Bool = Sort("Bool", "exact")
#: The reals. Approximate by default: floating point is the implementation.
Real = Sort("Real", "approx")
#: The sort of propositions, the marker for "this annotation is a statement".
Prop = Sort("Prop", "exact")


@dataclass(frozen=True, eq=False)
class FinType(LankyType):
    """``Fin[n]``: the index type with points ``0 <= i < n``.

    Iteration is the whole point. With a concrete bound it is ``range(n)``, so
    the same source runs natively; with a symbolic bound it yields one fresh
    variable and records the binder, so the enclosing generator expression
    becomes a quantifier, a reduction, or (in loopty) a loop nest.
    """

    bound: Any

    def __str__(self) -> str:
        """Print as ``Fin(n)``."""
        return f"Fin({render(self.bound)})"

    def __repr__(self) -> str:
        """Print as ``Fin(n)``."""
        return str(self)

    def __eq__(self, other: Any) -> bool:
        """Compare bounds structurally; ``==`` on a bound would build a term."""
        return isinstance(other, FinType) and structurally_equal(self.bound, other.bound)

    def __hash__(self) -> int:
        """Hash the bound."""
        return hash(("FinType", self.bound))

    @property
    def is_concrete(self) -> bool:
        """Whether the bound is an integer, so the domain can be walked."""
        return isinstance(self.bound, int)

    def __iter__(self) -> Any:
        """Walk the points, or yield the one generic point of a symbolic domain."""
        if self.is_concrete:
            return iter(range(self.bound))
        return _GenericPoint(self)

    def __len__(self) -> int:
        """The number of points, when the bound is concrete."""
        if not self.is_concrete:
            raise TypeError(f"{self} has no length: its bound is symbolic")
        return self.bound

    def points(self, evaluate_expr: Any) -> range:
        """The concrete points, given a way to evaluate the bound.

        This is the hook the evaluator uses to enumerate a quantifier.
        """
        return range(int(evaluate_expr(self.bound)))


class _GenericPoint:
    """The iterator of a symbolic index type: one fresh bound variable, lazily.

    Laziness is what makes the surface syntax work. Python evaluates the
    outermost iterable of a generator expression, and calls ``iter`` on it, when
    the generator object is built, which is before ``all`` or ``lanky.sum`` has
    had a chance to start tracing binders. Binding on the first ``next`` instead
    puts the binder inside the trace, where it belongs, and keeps the binders in
    outer-to-inner order.
    """

    def __init__(self, domain: Any) -> None:
        self.domain = domain
        self.done = False

    def __iter__(self) -> _GenericPoint:
        """Iterators are their own iterable."""
        return self

    def __next__(self) -> Any:
        """Yield the one generic point, once."""
        if self.done:
            raise StopIteration
        self.done = True
        trace = current_trace()
        if trace is None:
            raise TypeError(
                f"cannot iterate {self.domain} here: its bound is symbolic, so "
                "there is nothing to walk. Write it inside all(...), any(...) or "
                "lanky.sum(...), or give it a concrete bound"
            )
        return trace.bind(self.domain)


class _FinFamily:
    """The ``Fin`` name itself: ``Fin[n]`` builds a :class:`FinType`."""

    def __getitem__(self, bound: Any) -> FinType:
        """Build the index type with this bound."""
        return FinType(bound)

    def __repr__(self) -> str:
        """Print as ``Fin``."""
        return "Fin"


#: ``Fin[n]`` is the index type of ``n`` points.
Fin = _FinFamily()


@dataclass(frozen=True, eq=False)
class FnType(LankyType):
    """``Fn[A, B]``: a family of ``B`` indexed by ``A``.

    A function used as a family is how a theorem talks about the data a kernel
    writes, without owning the array: ``off: Fn[Fin[n + 1], Nat]`` is applied as
    ``off(r)``, and a property test supplies a table.
    """

    domain: Any
    codomain: Any

    def __str__(self) -> str:
        """Print as ``Fn[A, B]``."""
        return f"Fn[{self.domain}, {self.codomain}]"

    def __repr__(self) -> str:
        """Print as ``Fn[A, B]``."""
        return str(self)

    def __eq__(self, other: Any) -> bool:
        """Compare domain and codomain."""
        return (
            isinstance(other, FnType)
            and self.domain == other.domain
            and self.codomain == other.codomain
        )

    def __hash__(self) -> int:
        """Hash domain and codomain."""
        return hash(("FnType", self.domain, self.codomain))


class _FnFamily:
    """The ``Fn`` name itself: ``Fn[A, B]`` builds a :class:`FnType`."""

    def __getitem__(self, args: Any) -> FnType:
        """Build the family type from a ``(domain, codomain)`` pair."""
        if not isinstance(args, tuple) or len(args) != 2:
            raise TypeError("Fn takes exactly two arguments: Fn[domain, codomain]")
        return FnType(args[0], args[1])

    def __repr__(self) -> str:
        """Print as ``Fn``."""
        return "Fn"


#: ``Fn[A, B]`` is the type of families of ``B`` indexed by ``A``.
Fn = _FnFamily()


@dataclass(frozen=True, eq=False)
class Refined(LankyType):
    """``T & prop``: the inhabitants of ``T`` that satisfy every proposition.

    Chaining is flat: ``T & p & q`` carries both propositions, so a checker sees
    a conjunction and not a nest.
    """

    base: Any
    props: tuple[Any, ...]

    def __and__(self, prop: Any) -> Refined:
        """Add another proposition to the refinement."""
        return Refined(self.base, (*self.props, prop))

    def __str__(self) -> str:
        """Print as ``T & (p) & (q)``."""
        return " & ".join([str(self.base), *(f"({render(p)})" for p in self.props)])

    def __repr__(self) -> str:
        """Print as ``T & (p) & (q)``."""
        return str(self)

    def __eq__(self, other: Any) -> bool:
        """Compare base and propositions structurally."""
        return (
            isinstance(other, Refined)
            and self.base == other.base
            and structurally_equal(self.props, other.props)
        )

    def __hash__(self) -> int:
        """Hash the base only; the propositions are terms."""
        return hash(("Refined", self.base, len(self.props)))

    def holds(self, context: dict[str, Any]) -> bool:
        """Whether every refining proposition holds at these values."""
        return all(bool(evaluate(p, context)) for p in self.props)


def exactness_of(obj: Any) -> str:
    """The exactness class of a type, defaulting to ``exact`` for index types."""
    if isinstance(obj, Sort):
        return obj.exactness
    if isinstance(obj, Refined):
        return exactness_of(obj.base)
    if isinstance(obj, FnType):
        return exactness_of(obj.codomain)
    return "exact"
