"""The faithfulness fact: a claim's term computes what its annotations compute (#91).

The design idea. lanky reads an annotation by running its Python on terms
(:func:`lanky.terms.evaluate_annotations`), and every oracle is handed the term
that reading leaves. Some of Python's operations answer from the object they
are handed rather than through its overloads: ``is``, an attribute load, a
hash, a text, the truth value of a number, a comparison of two lanky types. On
a term each of them gives one answer, whatever value the term takes, so the
term says something else than the claim, and an oracle proves the term. Rules
refuse the cases found so far (#61, #63, #64, #70, #73), and each fix found
more; a helper function or a library between the annotation and the term
escapes all of them (#79, #80, #88).

So the reading is checked by its results rather than by its spelling, as
loopty checks a kernel's trace against its body (its ``trace-faithful``
fact): each annotation of a claim is run again as Python at drawn concrete
values of the parameters, the term the reading left is evaluated at the same
values, and the two have to agree. Whatever answered from the term rather
than from its value shows up as a point where they do not.

*The rerun.* An annotation is compiled from its source again and evaluated as
Python evaluates it, in a copy of the function's globals as they were when
lanky read it (:attr:`lanky.theory.Theorem.namespace`), so a helper function
the annotation calls, a library and a dict lookup run on numbers, as in the
file run as a program. A parameter that is a variable is its drawn value, a
family a :class:`~lanky.testing.Table` or a family drawn as it is applied
(:class:`DrawnFamily`), both callable, and a parameter that is a hypothesis is
the variable lanky's reading makes of it. ``all``, ``any``, ``sum`` and
``abs`` are Python's, which is what lanky's are at concrete values. The
prelude's types iterate concretely while the rerun runs
(:func:`lanky.terms.concrete_sorts`): ``Fin[n]`` at a drawn ``n`` is
``range(n)`` already, and a sort with no end, ``Nat`` say, iterates a finite
sample of itself, drawn once per draw, which is the same list wherever and
however often the annotation iterates it.

The connectives are lanky's, as an annotation means them: ``~``, ``&`` and
``|`` of truth values are ``not``, ``and`` and ``or``, where Python's ``~`` of
a ``bool`` is the bitwise complement of an integer, ``~True == -2``, and they
are read three-valued, as lanky reads them (:func:`lanky.terms.disjoin`): ``(i
== 0) | (f(i - 1) <= f(i))`` is true at ``i = 0``, where Python's ``|``
evaluates ``f(-1)`` first and stops. Of anything but truth values they are
Python's own operators. A term the rerun builds anyway, from a module-level
variable or a function that makes terms on purpose
(:func:`lanky.cas.from_sympy`), is read at the draw by the evaluator.

*The term.* The term is evaluated at the same values by lanky's evaluator
(:class:`lanky.terms.LankyEvaluationMapper`) in the Python reading, the one
:meth:`lanky.theory.Theorem.__call__` uses, so that Python's numbers and its
rounding are on both sides. A quantifier over a sort ranges over the same
sample the rerun iterated, read as the whole domain, so a universal and an
existential are answered over it both ways, as Python's ``all`` and ``any``
answer them. A variable's sort is compared too, as it is at the draw: a
``Fin``'s bound, a refinement's truth values, a family's domain and values.

*The points.* First come :data:`CORNERS` draws of small values and domain
ends, every natural the tester draws, a ``Fin``'s first and last points,
zero, one and minus one, and then :data:`SAMPLES` of the property tester's
draws (:func:`lanky.testing.sample_value`, from its seed), with the
definitional hypotheses satisfied by construction
(:func:`lanky.testing.satisfy_hypotheses`) so that a scan is one. A bounded
quantifier enumerates every point of its domain anyway. A family over a sort
with no end, ``Fn[Nat, Real]``, which the tester cannot tabulate, is drawn
point by point as either reading applies it, the same value at a point for
both. A refinement no draw satisfies is drawn from what it refines: the
readings are compared whether or not the hypotheses hold.

*Agreement.* At a draw each annotation has to compute the same on both sides:
the same truth value, or the same value, and a truth value against a number
is a disagreement. So is an exception on one side only, ``i.name`` raising at
a number where its term has a value, with one exception: where Python stops
with no answer, at a family applied outside its domain, a division by zero,
an elementary function outside its domain or an overflow, lanky's reading
may settle the point three-valued, as a quantifier does at a point past one
with no answer, so such a point is not compared (``open``). Where both sides
stop there for one reason, with the same exception, neither has a value, and
they agree: ``n // 0 == 0`` is read faithfully, and what Lean's total
division makes of it is the semantics gap :mod:`lanky.semantics` notes. Two
other exceptions are no comparison (``silent``). A disagreement in a truth
value at a draw where the term compared two floating-point numbers that
agree to :data:`TOLERANCE` is put down to rounding and not counted
(``rounding``): Python's ``sum`` compensates as it adds, and the evaluator
adds the term's sum one by one, which can differ in the last bit, where the
claim is read over the reals. A value is compared to the same tolerance when
it is a floating-point number.

*The fact.* Its kind is ``faithful`` (:data:`lanky.ledger.FAITHFUL`), its id
is the claim's with that kind (``faithful:gauss.gauss@31``), and it has the
claim's owner and location. It is

* ``refuted`` at the first draw at which an annotation and its term disagree,
  with the draw as ``counterexample``, the annotation as written as
  ``witness``, and both answers in the ``reason``;
* ``tested`` by ``python`` when every annotation was compared at some draw
  and none disagreed at any;
* ``assumed``, with the reason as ``declined``, when an annotation could not
  be compared at all: a statement with a free name, a variable of a sort no
  draw can be made of, an annotation Python evaluated when the function was
  defined that holds a term, or an annotation that had no answer on both
  sides at any draw.

The check is sampled: a disagreement only at a point no draw reaches escapes
it. :meth:`lanky.theory.Theorem.faithful_fact` makes the fact once per claim,
and :func:`lanky.check.establish` rests every pass, decision and proof of the
claim on it, and offers a claim whose reading is refuted to no oracle.
"""

from __future__ import annotations

import ast
import inspect
import itertools
import numbers
import operator
import random
import warnings
from collections.abc import Callable, Iterator, Sequence
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import numpy
import pymbolic.primitives as prim

from lanky.intervals import ComplexValue
from lanky.ledger import FAITHFUL, Fact, Status, fact_id
from lanky.prelude import FinType, FnType, LankyType, Refined, Sort, SumType
from lanky.terms import (
    LankyEvaluationMapper,
    Polarity,
    Undecided,
    Var,
    concrete_sorts,
    evaluate,
    render,
)
from lanky.testing import (
    MAX_NAT,
    SAMPLED_SORTS,
    OpenStatement,
    SkipSample,
    Table,
    Unsampleable,
    in_sort,
    sample_value,
    sampling_order,
    satisfy_hypotheses,
    statement_free_names,
)

__all__ = [
    "CORNERS",
    "DECIDED_BY",
    "KIND",
    "SAMPLES",
    "SEED",
    "SORT_POINTS",
    "STATEMENT",
    "TOLERANCE",
    "DrawnFamily",
    "faithful_fact",
]

#: The kind of the fact, as the ledger and its JSON name it.
KIND = FAITHFUL

#: What the statement of the fact says, for every claim.
STATEMENT = "the term computes what the annotations compute"

#: Who the fact names as its decider when the comparison was made.
DECIDED_BY = "python"

#: How many draws of small values and domain ends come first: enough that a
#: single natural takes every value the tester draws, ``0`` to ``MAX_NAT``.
CORNERS = MAX_NAT + 1

#: How many of the property tester's draws follow them.
SAMPLES = 32

#: How many times as many draws are attempted, for those that cannot be
#: completed (an empty ``Fin``, a definition outside its codomain).
ATTEMPTS = 4

#: The seed of the draws, the property tester's.
SEED = 0

#: How many drawn points a sort's sample holds besides its small values.
SORT_POINTS = 2

#: How close two floating-point numbers are, relative to the larger, for a
#: disagreement at them to be put down to rounding (see the module docstring).
TOLERANCE = 1e-9

#: The small values each sort's sample starts with.
_SMALL: dict[str, tuple[Any, ...]] = {
    "Nat": (0, 1, 2),
    "Int": (0, -1, 1),
    "Real": (Fraction(0), Fraction(1), Fraction(-1, 2)),
    "Complex": (0j, 1 + 0j, 1j),
    "Bool": (False, True),
    "Prop": (False, True),
}

#: What Python raises where it stops with no answer and lanky's reading may
#: settle the point three-valued: a family applied outside its domain, a
#: quantifier the draws leave open, a division by zero, an elementary function
#: outside its domain (:class:`lanky.terms.UndefinedValue`), an overflow.
_OPEN = (Undecided, ArithmeticError)

#: What a comparison's operator is, as the function Python applies for it.
_COMPARISONS: dict[str, Callable[[Any, Any], Any]] = {
    "==": operator.eq,
    "!=": operator.ne,
    "<": operator.lt,
    "<=": operator.le,
    ">": operator.gt,
    ">=": operator.ge,
}


# {{{ the rerun


def _is_truth(value: Any) -> bool:
    """Whether ``value`` is a truth value, Python's or numpy's."""
    return isinstance(value, bool | numpy.bool_)


def _not(value: Any) -> Any:
    """``~value`` as lanky means it: ``not`` of a truth value, Python's ``~`` of anything else."""
    if _is_truth(value):
        return not value
    return ~value


#: Stands for an operand that had no answer.
_MISSING = object()


def _connective(settles: bool) -> Callable[[Callable[[], Any], Callable[[], Any]], Any]:
    """``&`` (``settles`` false) or ``|`` (true) as lanky reads them, of two operands not yet run.

    Of two truth values it is ``and`` or ``or``, read three-valued, as
    :func:`lanky.terms.conjoin` and :func:`lanky.terms.disjoin` read them: an
    operand that settles it settles it, whatever the other could not answer,
    and an operand with no answer is raised again when nothing settles it.
    Python's ``|`` runs both operands first, so ``(i == 0) | (f(i - 1) <=
    f(i))`` stopped at ``f(-1)`` where lanky's reading is true. Of anything
    else it is Python's own operator, the bitwise one on two integers.
    """
    python = operator.or_ if settles else operator.and_

    def apply(left: Callable[[], Any], right: Callable[[], Any]) -> Any:
        pending: Exception | None = None
        try:
            first = left()
        except _OPEN as exc:
            pending, first = exc, _MISSING
        if first is not _MISSING and not _is_truth(first):
            return python(first, right())
        if first is not _MISSING and bool(first) == settles:
            return settles
        try:
            second = right()
        except _OPEN:
            if pending is not None:
                raise pending from None
            raise
        if not _is_truth(second):
            if pending is not None:
                raise pending
            return python(first, second)
        if bool(second) == settles:
            return settles
        if pending is not None:
            raise pending
        return not settles

    return apply


#: The names the rerun calls the connectives by, and Python's builtins that
#: lanky's own stand for at concrete values (see :class:`_Connectives`).
_RERUN_NAMES: dict[str, Any] = {
    "__lanky_not__": _not,
    "__lanky_and__": _connective(False),
    "__lanky_or__": _connective(True),
    "all": all,
    "any": any,
    "sum": sum,
    "abs": abs,
}


class _Connectives(ast.NodeTransformer):
    """Read ``~``, ``&`` and ``|`` in an annotation's source as lanky's connectives.

    ``~operand`` becomes ``__lanky_not__(operand)``, and ``left | right``
    becomes ``__lanky_or__(lambda: left, lambda: right)``, so that an operand
    is run only when it is asked for (see :func:`_connective`).
    """

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Any:
        """``~operand`` as ``__lanky_not__(operand)``; any other operator as it is."""
        self.generic_visit(node)
        if not isinstance(node.op, ast.Invert):
            return node
        call = ast.Call(ast.Name("__lanky_not__", ast.Load()), [node.operand], [])
        return ast.copy_location(call, node)

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        """``left & right`` and ``left | right`` as calls on thunks; anything else as it is."""
        self.generic_visit(node)
        name = {ast.BitAnd: "__lanky_and__", ast.BitOr: "__lanky_or__"}.get(type(node.op))
        if name is None:
            return node
        thunks = [
            ast.Lambda(
                ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[]),
                side,
            )
            for side in (node.left, node.right)
        ]
        return ast.copy_location(ast.Call(ast.Name(name, ast.Load()), thunks, []), node)


def _compiled(source: str) -> Any:
    """An annotation's source compiled for the rerun, its connectives read as lanky's.

    ``eval`` strips the spaces and tabs a string starts with and ``compile``
    does not, so they are stripped here as :func:`lanky.terms.evaluate_annotations`
    strips them.
    """
    with warnings.catch_warnings():
        # Python warned about the source when lanky read it, ``is not`` with
        # a literal say, and saying it twice says nothing more.
        warnings.simplefilter("ignore", SyntaxWarning)
        tree = ast.parse(source.lstrip(" \t"), "<string>", "eval")
        tree = ast.fix_missing_locations(_Connectives().visit(tree))
        return compile(tree, "<string>", "eval")


@dataclass(frozen=True)
class _Outcome:
    """What one reading of one annotation came to at one draw: a value, or what it raised."""

    value: Any = None
    error: Exception | None = None

    def text(self) -> str:
        """The outcome as a reason says it."""
        if self.error is not None:
            return f"raises {type(self.error).__name__}: {self.error}"
        return f"computes {_shown(self.value)}"


def _shown(value: Any) -> str:
    """A value as a reason shows it: a term rendered, a family as its values, short."""
    if isinstance(value, prim.ExpressionNode):
        text = render(value)
    elif isinstance(value, Table):
        text = repr(value.values)
    else:
        text = repr(value)
    return text if len(text) <= 120 else text[:117] + "..."


# }}}


# {{{ the term, at a draw


def _inexact(value: Any) -> bool:
    """Whether ``value`` is a floating-point number, real or complex."""
    return isinstance(value, float | complex | numpy.inexact)


def _close(left: Any, right: Any) -> bool:
    """Whether two numbers, one of them floating-point, agree to :data:`TOLERANCE`."""
    if not (_inexact(left) or _inexact(right)):
        return False
    if not (isinstance(left, numbers.Number) and isinstance(right, numbers.Number)):
        return False
    if _is_truth(left) or _is_truth(right):
        return False
    try:
        scale = max(abs(left), abs(right))
        return bool(abs(left - right) <= TOLERANCE * scale)
    except (TypeError, ArithmeticError):
        return False


class _Reading(LankyEvaluationMapper):
    """lanky's evaluator in the Python reading, a sort read as the sample the rerun iterated.

    ``fragile`` records whether a comparison it made was between two
    floating-point numbers that agree to :data:`TOLERANCE`, where rounding
    can decide the answer (see the module docstring).
    """

    def __init__(self, context: dict[str, Any], samples: _Samples) -> None:
        super().__init__(context, samples, Polarity.POSITIVE)
        self.exact = False
        self.fragile = False

    @staticmethod
    def is_exhaustive(domain: Any) -> bool:
        """Every domain is walked whole: a sort's sample is its domain here."""
        return True

    def map_comparison(self, expr: prim.Comparison) -> Any:
        """Compare the two sides as Python does, noting a comparison rounding can decide."""
        left = self._at(Polarity.MIXED, expr.left)
        right = self._at(Polarity.MIXED, expr.right)
        if _close(left, right):
            self.fragile = True
        return _COMPARISONS[expr.operator](left, right)


def _sort_at(sort: Any, reading: _Reading) -> Any:
    """``sort`` as it is at the draw ``reading`` holds: its bounds and refinements evaluated."""
    if isinstance(sort, FinType):
        return FinType(reading.rec(sort.bound))
    if isinstance(sort, FnType):
        return FnType(_sort_at(sort.domain, reading), _sort_at(sort.codomain, reading))
    if isinstance(sort, Refined):
        return Refined(
            _sort_at(sort.base, reading), tuple(reading.rec(prop) for prop in sort.props)
        )
    if isinstance(sort, SumType):
        return SumType(tuple(_sort_at(piece, reading) for piece in sort.pieces))
    if isinstance(sort, prim.ExpressionNode):
        return reading.rec(sort)
    return sort


def _value_at(value: Any, reading: _Reading) -> Any:
    """A term or a type read at the draw; anything else as it is."""
    if isinstance(value, LankyType):
        return _sort_at(value, reading)
    if isinstance(value, prim.ExpressionNode):
        return reading.rec(value)
    return value


def _holds_term(value: Any) -> bool:
    """Whether ``value`` is a term, or a type or container that holds one."""
    if isinstance(value, prim.ExpressionNode):
        return True
    if isinstance(value, FinType):
        return _holds_term(value.bound)
    if isinstance(value, FnType):
        return _holds_term(value.domain) or _holds_term(value.codomain)
    if isinstance(value, Refined):
        return _holds_term(value.base) or any(_holds_term(prop) for prop in value.props)
    if isinstance(value, SumType):
        return any(_holds_term(piece) for piece in value.pieces)
    if isinstance(value, tuple | list | set | frozenset):
        return any(_holds_term(item) for item in value)
    if isinstance(value, dict):
        return any(_holds_term(item) for item in (*value.keys(), *value.values()))
    return False


# }}}


# {{{ the draws


class _Samples:
    """The finite sample each sort iterates at one draw, the same for both readings.

    A sort's sample is its small values (:data:`_SMALL`) and
    :data:`SORT_POINTS` of the tester's draws of it, drawn the first time the
    sort is iterated at the draw and kept, so that the rerun and the term
    range over the same points wherever and however often they iterate it.
    """

    def __init__(self, rng: random.Random) -> None:
        self.rng = rng
        self.drawn: list[tuple[Any, list[Any]]] = []

    def __call__(self, sort: Any) -> list[Any]:
        """The sample of ``sort``, or of what it refines.

        Raises:
            Unsampleable: For a sort the tester has no sampler for.
        """
        while isinstance(sort, Refined):
            sort = sort.base
        for seen, points in self.drawn:
            if seen is sort or (isinstance(seen, Sort) and seen == sort):
                return points
        if not isinstance(sort, Sort) or sort.name not in SAMPLED_SORTS:
            raise Unsampleable(f"no sampler for {sort!r}")
        points = list(_SMALL[sort.name])
        if sort.name not in ("Bool", "Prop"):
            for _ in range(SORT_POINTS):
                point = _python(sample_value(sort, self.rng, {}))
                if not any(type(point) is type(seen) and point == seen for seen in points):
                    points.append(point)
        self.drawn.append((sort, points))
        return points

    def described(self) -> dict[str, list[Any]]:
        """The samples drawn, by sort, as a reason shows them."""
        return {str(sort): list(points) for sort, points in self.drawn}


class _Corners(random.Random):
    """A stand-in for the tester's random source that gives small values and domain ends.

    The tester draws every value through ``randrange`` and ``random``
    (:func:`lanky.testing.sample_value`). Here ``randrange`` answers the
    ``k``-th of the values in its range in the order ``0``, ``1``, ``-1``, the
    last, the first, and then outwards from zero, each once, so the ``k``-th
    corner draw puts a natural at ``0``, ``1``, ``5``, ``2``, ``3``, ``4``, a
    point of ``Fin[n]`` at ``0``, ``1``, ``n - 1``, ..., and a rational at
    ``0``, ``1/4``, ``-1/2``, ``8/2``, ...; so the first draws, at which a
    disagreement is reported, are the smallest. ``random`` answers ``0`` and
    then ``0.75``, so a ``Bool`` is ``True`` and then ``False``.
    """

    def __init__(self, k: int) -> None:
        super().__init__(k)
        self.k = k

    def randrange(self, start: int, stop: int | None = None, step: int = 1) -> int:  # type: ignore[override]
        """The ``k``-th value of the range in the order the class docstring gives."""
        if stop is None:
            start, stop = 0, start
        size = stop - start
        if size <= 0:
            raise ValueError(f"empty range for randrange({start}, {stop})")
        wanted = self.k % size
        seen: list[int] = []
        order = itertools.chain(
            (0, 1, -1, stop - 1, start),
            itertools.chain.from_iterable((m, -m) for m in itertools.count(2)),
        )
        for value in order:
            if start <= value < stop and value not in seen:
                seen.append(value)
                if len(seen) > wanted:
                    return value
        raise AssertionError("unreachable: the order reaches every integer")

    def random(self) -> float:
        """``0`` at an even ``k`` and ``0.75`` at an odd one."""
        return 0.0 if self.k % 2 == 0 else 0.75


class DrawnFamily:
    """A family over a domain the tester cannot tabulate, drawn at each point as it is applied.

    The property tester draws a family over a ``Fin`` as a
    :class:`~lanky.testing.Table`, and none over a sort with no end, so a
    claim about ``D: Fn[Nat, Fn[Nat, Real]]`` was never drawn. The
    faithfulness check needs only the points the annotation and its term
    apply the family at, which are the same points on both sides, so the
    value at a point is drawn the first time either reading applies the family
    there, from the draw's random source, and kept. A point outside the
    domain has no value, as for a table (:class:`~lanky.terms.Undecided`).

    Attributes:
        values: The value at each point applied so far, in the order drawn.
    """

    def __init__(
        self, domain: Any, codomain: Any, source: random.Random, context: dict[str, Any], name: str
    ) -> None:
        self.domain = domain
        self.codomain = codomain
        self.source = source
        self.context = context
        self.name = name
        self.values: dict[Any, Any] = {}

    def __call__(self, point: Any) -> Any:
        """The value at ``point``, drawn the first time it is asked for."""
        if (
            _is_truth(point)
            or not isinstance(point, numbers.Number)
            or not in_sort(point, self.domain, self.context)
        ):
            raise Undecided(
                f"{self.name} is applied at {point!r}, which is outside the domain "
                f"{self.domain} it declares, so this draw decides nothing"
            )
        if point not in self.values:
            self.values[point] = _draw(self.codomain, self.source, self.context)
        return self.values[point]

    __getitem__ = __call__

    def __repr__(self) -> str:
        """Print as the values drawn so far, by point."""
        return f"DrawnFamily({_described(self.values)!r})"


def _python(value: Any) -> Any:
    """A drawn value as Python computes with it.

    The tester draws a ``Complex`` as a :class:`~lanky.intervals.ComplexValue`
    of two fractions, for its exact reading; both readings here are Python's,
    and Python's ``exp`` and ``log`` take a ``complex``.
    """
    if isinstance(value, ComplexValue):
        return complex(float(value.real), float(value.imag))
    return value


def _unrefined(sort: Any) -> Any:
    """What a refinement refines, through any number of refinements."""
    while isinstance(sort, Refined):
        sort = sort.base
    return sort


def _draw(
    sort: Any, source: random.Random, context: dict[str, Any], name: str | None = None
) -> Any:
    """One value of ``sort`` for the comparison, drawn as the tester draws it where it can.

    A family over a ``Fin`` is a table, and one over anything else a
    :class:`DrawnFamily`; their values are drawn from what their codomain
    refines, since an entry has no name to read a refinement of. A variable
    of a refined sort is drawn as the tester draws it, and from what the sort
    refines when no draw satisfies the refinement: the readings are compared
    whether or not a draw satisfies the hypotheses.

    Raises:
        SkipSample: If no value can be drawn: an empty ``Fin``, a family over
            a domain of negative size, a sort with no sampler.
    """
    if isinstance(sort, FnType):
        codomain = _unrefined(sort.codomain)
        domain = _unrefined(sort.domain)
        if isinstance(domain, FinType):
            bound = int(evaluate(domain.bound, context))
            if bound < 0:
                raise SkipSample(f"{domain} has a negative size")
            return Table(
                [_draw(codomain, source, context) for _ in range(bound)], name=name or "a family"
            )
        return DrawnFamily(domain, codomain, source, dict(context), name or "a family")
    if isinstance(sort, Refined):
        if name is not None:
            try:
                return _python(sample_value(sort, source, context, name))
            except SkipSample:
                pass
        return _draw(sort.base, source, context, name)
    return _python(sample_value(sort, source, context, name))


def _described(value: Any) -> Any:
    """A drawn value as a counterexample shows it: a family as its values.

    A family drawn as it was applied is its values by point, and a point that
    is not an ``int``, ``Fraction(1, 2)`` of a family over ``Real``, is named
    by its text, since a JSON object's keys are strings and numbers.
    """
    if isinstance(value, Table):
        return [_described(item) for item in value.values]
    if isinstance(value, DrawnFamily):
        return {_key(point): _described(item) for point, item in value.values.items()}
    return value


def _key(point: Any) -> Any:
    """A point of a drawn family as a counterexample's key: an ``int`` as it is, else its text."""
    return point if isinstance(point, int) and not _is_truth(point) else str(point)


@dataclass
class _Draw:
    """One draw: its label, the values of the variables, and the samples of the sorts."""

    label: str
    context: dict[str, Any]
    samples: _Samples


def _draws(variables: Sequence[tuple[str, Any]], hypotheses: Sequence[Any]) -> Iterator[Any]:
    """The draws to compare at, corner draws first; for one that could not be made, why not.

    Each draw takes a value of every variable, a size before what it sizes
    (:func:`lanky.testing.sampling_order`), and then assigns the definitional
    hypotheses, as the tester does, so that a family that is a scan of
    another is one. A statement with no variables has one draw, the empty one.
    """
    ordered = sampling_order(variables)
    sorts = dict(ordered)
    rng = random.Random(SEED)
    sources: list[tuple[str, random.Random]] = [
        (f"corner {k}", _Corners(k)) for k in range(CORNERS if ordered else 1)
    ]
    made = 0
    attempt = 0
    while sources or (ordered and made < SAMPLES and attempt < SAMPLES * ATTEMPTS):
        if sources:
            label, source = sources.pop(0)
        else:
            label, source = f"draw {attempt}", rng
            attempt += 1
        samples = _Samples(random.Random(f"{SEED}:{label}"))
        context: dict[str, Any] = {}
        try:
            for name, sort in ordered:
                context[name] = _draw(sort, source, context, name)
            satisfy_hypotheses(hypotheses, context, sorts, samples)
        except Exception as exc:  # noqa: BLE001 - a draw that cannot be made is skipped
            yield str(exc) or type(exc).__name__
            continue
        if not label.startswith("corner"):
            made += 1
        yield _Draw(label, context, samples)


# }}}


# {{{ comparing


@dataclass(frozen=True)
class _Annotation:
    """One annotation of a claim: what it says, its source, and the term lanky read off it."""

    name: str
    role: str
    term: Any
    source: str
    code: Any = None
    given: Any = None

    @property
    def what(self) -> str:
        """The annotation as a reason names it."""
        if self.role == "goal":
            return "the goal"
        if self.role == "sort":
            return f"the sort of {self.name}"
        return f"the hypothesis {self.name}"


def _same(left: Any, right: Any) -> bool | None:
    """Whether two values the readings computed are the same; ``None`` where ``==`` cannot say.

    A floating-point number is the same as one that agrees with it to
    :data:`TOLERANCE`. Anything else is compared with ``==``: a number, a
    table by its values, a type by its parts.
    """
    if _inexact(left) or _inexact(right):
        if isinstance(left, numbers.Number) and isinstance(right, numbers.Number):
            return bool(left == right) or _close(left, right)
    try:
        answer = left == right
    except Exception:  # noqa: BLE001 - values == cannot compare are not compared
        return None
    if not _is_truth(answer):
        return None
    return bool(answer)


def _judge(python: _Outcome, term: _Outcome, fragile: bool) -> str:
    """How the two readings of one annotation compare at one draw.

    ``agreed``, the same value, or no value on either side for one reason
    (one of :data:`_OPEN`, of one type); ``differed``; ``open``, where Python
    stopped with no answer that lanky's reading may settle; ``silent``, where
    both raised otherwise; ``rounding``, a truth value that differs where the
    term compared two floating-point numbers that agree to :data:`TOLERANCE`;
    or ``uncomparable``, a value that holds a term or that ``==`` cannot
    compare.
    """
    if python.error is not None and term.error is not None:
        if isinstance(python.error, _OPEN) and type(python.error) is type(term.error):
            # neither has a value here, for the one reason: a division by
            # zero, say, or a family applied outside its domain
            return "agreed"
        return "silent"
    if python.error is not None:
        return "open" if isinstance(python.error, _OPEN) else "differed"
    if term.error is not None:
        return "differed"
    left, right = python.value, term.value
    if _holds_term(left) or _holds_term(right):
        return "uncomparable"
    if _is_truth(left) != _is_truth(right):
        # a truth value and a number: one reading is a proposition and the
        # other is not, which the tester and Lean read differently
        return "differed"
    if _is_truth(left):
        if bool(left) == bool(right):
            return "agreed"
        return "rounding" if fragile else "differed"
    same = _same(left, right)
    if same is None:
        return "uncomparable"
    return "agreed" if same else "differed"


def _compare(
    namespace: dict[str, Any],
    parameters: Sequence[str],
    annotations: Sequence[_Annotation],
    draw: _Draw,
) -> Iterator[tuple[_Annotation, str, _Outcome, _Outcome]]:
    """Each annotation, how its two readings compare at ``draw``, and the two outcomes.

    ``namespace`` is the function's globals as they were when lanky read the
    annotations (:attr:`lanky.theory.Theorem.namespace`).
    """
    scope = dict(namespace)
    scope.update(_RERUN_NAMES)
    for name in parameters:
        scope[name] = draw.context[name] if name in draw.context else Var(name)
    for annotation in annotations:
        reading = _Reading(dict(draw.context), draw.samples)
        with concrete_sorts(draw.samples):
            try:
                if annotation.code is not None:
                    value = eval(annotation.code, scope, None)
                else:
                    value = annotation.given
                python = _Outcome(_value_at(value, reading))
            except Exception as exc:  # noqa: BLE001 - what the annotation raises is its answer
                python = _Outcome(error=exc)
        # only the comparisons the term makes say whether rounding decided it
        reading.fragile = False
        try:
            term = _Outcome(_value_at(annotation.term, reading))
        except Exception as exc:  # noqa: BLE001 - what the term raises is its answer
            term = _Outcome(error=exc)
        yield annotation, _judge(python, term, reading.fragile), python, term


@dataclass
class _Tally:
    """What the draws came to for each annotation, while none disagreed."""

    draws: int = 0
    agreed: dict[str, int] = field(default_factory=dict)
    unanswered: dict[str, str] = field(default_factory=dict)
    counts: dict[str, int] = field(default_factory=dict)
    skipped: list[str] = field(default_factory=list)

    def record(
        self, annotation: _Annotation, verdict: str, python: _Outcome, term: _Outcome
    ) -> None:
        """Count one comparison that did not disagree."""
        if verdict == "agreed":
            self.agreed[annotation.name] = self.agreed.get(annotation.name, 0) + 1
            return
        self.counts[verdict] = self.counts.get(verdict, 0) + 1
        if annotation.name not in self.unanswered:
            if verdict == "uncomparable":
                why = (
                    f"as Python it computes {_shown(python.value)} and its term "
                    f"{_shown(term.value)}, which == cannot compare"
                )
            else:
                why = f"as Python it {python.text()}, and its term {term.text()}"
            self.unanswered[annotation.name] = why


# }}}


def _annotations(theorem: Any) -> list[_Annotation] | str:
    """The claim's annotations, in the order lanky read them; or why they cannot be run again."""
    fn = theorem.fn
    raw = inspect.get_annotations(fn, eval_str=False)
    terms: dict[str, tuple[str, Any]] = {name: ("sort", sort) for name, sort in theorem.variables}
    terms.update((name, ("hypothesis", prop)) for name, prop in theorem.hypotheses)
    terms["return"] = ("goal", theorem.goal)
    out: list[_Annotation] = []
    for name, annotation in raw.items():
        if name not in terms:
            continue
        role, term = terms[name]
        if isinstance(annotation, str):
            code = _compiled(annotation)
            out.append(_Annotation(name, role, term, annotation.strip(), code=code))
            continue
        if _holds_term(annotation):
            what = "the goal" if role == "goal" else f"the annotation of {name}"
            return (
                f"{what} was evaluated by Python when the function was defined, "
                "without `from __future__ import annotations`, and it holds a term, "
                "so there is no source to run again at a point"
            )
        # Python computed it once, and the reading took that value as it is.
        out.append(_Annotation(name, role, term, repr(annotation), given=annotation))
    return out


def faithful_fact(theorem: Any) -> Fact:
    """The ``faithful`` fact of one claim, established by running its annotations again.

    ``theorem`` is a :class:`lanky.theory.Theorem`, or an
    :class:`~lanky.theory.Axiom`. Nothing here raises: anything the rerun
    cannot do leaves the fact ``assumed``, with the reason as ``declined``.
    """
    identifier = fact_id(KIND, theorem.qualname, module=theorem.module, line=theorem.line)

    def fact(status: Status, **provenance: Any) -> Fact:
        return Fact(
            id=identifier,
            kind=KIND,
            statement=STATEMENT,
            term=None,
            status=status,
            decided_by=None if status is Status.ASSUMED else DECIDED_BY,
            provenance={"path": theorem.path, "line": theorem.line, **provenance},
            where=theorem.where,
            owner=theorem.qualname,
        )

    def declined(why: str) -> Fact:
        return fact(Status.ASSUMED, declined=f"{DECIDED_BY}: {why}")

    tally = _Tally()
    try:
        hypotheses = [prop for _, prop in theorem.hypotheses]
        free = statement_free_names(theorem.variables, hypotheses, theorem.goal)
        if free:
            names = OpenStatement(free).names
            listing = names[0] if len(names) == 1 else f"{', '.join(names[:-1])} and {names[-1]}"
            return declined(
                f"the statement mentions {listing}, which no parameter or binder of it "
                "binds, so no draw gives it a value and its annotations cannot be run "
                "again at one"
            )
        annotations = _annotations(theorem)
        if isinstance(annotations, str):
            return declined(annotations)
        parameters = list(inspect.signature(theorem.fn).parameters)
        for draw in _draws(theorem.variables, hypotheses):
            if isinstance(draw, str):
                tally.skipped.append(draw)
                continue
            tally.draws += 1
            for annotation, verdict, python, term in _compare(
                theorem.namespace, parameters, annotations, draw
            ):
                if verdict == "differed":
                    return _refuted(fact, annotation, draw, python, term)
                tally.record(annotation, verdict, python, term)
    except Exception as exc:  # noqa: BLE001 - a fact, never a crash of the check
        return declined(f"the annotations could not be run again: {type(exc).__name__}: {exc}")
    if not tally.draws:
        why = f" ({tally.skipped[0]})" if tally.skipped else ""
        return declined(
            f"no draw could be made{why}, so the annotations were run again at no point"
        )
    for annotation in annotations:
        if not tally.agreed.get(annotation.name):
            return declined(
                f"{annotation.what} had no answer on both sides at any of {tally.draws} "
                f"draws, so its reading was not compared ({tally.unanswered[annotation.name]})"
            )
    return fact(
        Status.TESTED,
        draws=tally.draws,
        compared=sum(tally.agreed.values()),
        seed=SEED,
        **tally.counts,
    )


def _refuted(
    fact: Any, annotation: _Annotation, draw: _Draw, python: _Outcome, term: _Outcome
) -> Fact:
    """The refutation at ``draw``, where ``annotation`` and its term disagree."""
    counterexample = {name: _described(value) for name, value in draw.context.items()}
    sampled = draw.samples.described()
    iterated = f" with each sort iterating its sample {sampled}" if sampled else ""
    term_text = _shown(annotation.term)
    return fact(
        Status.REFUTED,
        counterexample=counterexample,
        witness=f"{annotation.what}, {annotation.source}",
        python_answer=python.text(),
        term_answer=term.text(),
        draw=draw.label,
        reason=(
            f"{annotation.what}, run again as Python at these values{iterated}, "
            f"{python.text()}, and its term, {term_text}, {term.text()}: the term "
            "says something else than what was written, so no oracle that decides "
            "or proves is asked about the claim"
        ),
    )
