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
``abs`` are Python's, which is what lanky's are at concrete values, whatever
the module binds the names to, since lanky's reading takes them as its own
there too. The prelude's types iterate concretely while the rerun runs
(:func:`lanky.terms.concrete_sorts`): ``Fin[n]`` at a drawn ``n`` is
``range(n)`` already, and a sort with no end, ``Nat`` say, iterates a finite
sample of itself, drawn once per draw, which is the same list wherever and
however often the annotation iterates it.

The connectives and the quantifiers are lanky's, as an annotation means them,
read three-valued, and both readings read them alike (:func:`_kleene`).
``~``, ``&`` and ``|`` of truth values are ``not``, ``and`` and ``or``, where
Python's ``~`` of a ``bool`` is the bitwise complement of an integer, ``~True
== -2``; an operand that settles one settles it, whatever the other raised,
so ``(i == 0) | (f(i - 1) <= f(i))`` is true at ``i = 0``, where Python's
``|`` evaluates ``f(-1)`` first and stops. Of anything but truth values they
are Python's own operators. ``all`` and ``any`` over a generator, or a list
comprehension, walk its points in order (:func:`_quantify`): at each the
``if`` clauses, all of them, are one conjunction of guards, read once the
binders are bound, as lanky's term holds them, and then the body. A point
whose domain, guard or body has no answer, whatever Python raised there, is
passed over, and a later point that settles the quantifier settles it; when
none does, the first such answer is raised again. Python's ``all`` stops at
the first point that raises, and so would a comparison that read the term
the same way, so that a point after it, where a misreading may show, would
never be compared on either side: ``all(f(i) * 0 + (1 // i) * 0 == table(i)
for i in Fin[n])`` stops at ``i = 0``, and its term, ``f(i)*0 + (1 // i)*0 ==
0``, is what Lean proves, while ``table(1)`` is ``1``. ``sum`` over a
generator walks every point the same way, and has no value where a point has
none, as Python's has none; what it came to at each point is compared on both
sides all the same (:func:`_add`). A term the rerun builds anyway, from a
module-level variable or a function that makes terms on purpose
(:func:`lanky.cas.from_sympy`), is read at the draw by the evaluator.

*The term.* The term is evaluated at the same values by lanky's evaluator
(:class:`lanky.terms.LankyEvaluationMapper`) in the Python reading, the one
:meth:`lanky.theory.Theorem.__call__` uses, so that Python's numbers and its
rounding are on both sides, with its quantifiers and connectives read as the
rerun reads them (:class:`_Reading`). A quantifier over a sort ranges over the
same sample the rerun iterated, read as the whole domain. A sum is added by
Python's ``sum``, over the values of the body in the order of the walk, so
that it rounds as the rerun's ``sum`` does, which compensates as it adds since
Python 3.12. A variable's sort is compared too, as it is at the draw: a
``Fin``'s bound, a refinement's truth values, a family's domain and values.

*The points.* First come :data:`CORNERS` draws of small values and domain
ends, every natural the tester draws, a ``Fin``'s first and last points,
zero, one and minus one. Then come draws at the integers written in the
claim, in its annotations and in the functions they call, and next to them
(:func:`_written`), up to :data:`WRITTEN` of them and none past
:data:`WRITTEN_MAX`: a helper that answers otherwise at ``1000`` is reached
there. A variable that sizes a domain the claim walks takes such a value only
up to a size that keeps the walk to about :data:`SIZE_POINTS` points, and the
values join the samples of the sorts; a draw of such a claim at which a
reading walks more than :data:`WALK_POINTS` points all the same, over
``Fin[2 ** n]`` say, is given up as too large to walk (``unwalked``). Then
come :data:`SAMPLES` of the property tester's draws
(:func:`lanky.testing.sample_value`, from its seed).
The definitional hypotheses are satisfied by construction
(:func:`lanky.testing.satisfy_hypotheses`) so that a scan is one. A bounded
quantifier enumerates every point of its domain anyway. A family over a sort
with no end, ``Fn[Nat, Real]``, which the tester cannot tabulate, is drawn
point by point as either reading applies it, the same value at a point for
both. A refinement no draw satisfies is drawn from what it refines: the
readings are compared whether or not the hypotheses hold.

*Agreement.* At a draw each annotation has to compute the same on both sides:
the same truth value, or the same value, compared exactly, and a truth value
against a number is a disagreement. So is an exception on one side only,
whatever it is: ``i.name`` raising at a number where its term has a value, and
a division by zero or a family applied outside its domain where Python stops
and the term does not, as ``(f(i) * 0 == 1 // i + 1) | (i is not 0)`` does at
``i = 0``, where its term reads ``or True``. Where both sides stop with no
answer for one reason, the same exception of :data:`_OPEN`, a family applied
outside its domain, a division by zero, an elementary function outside its
domain or an overflow, neither has a value, and they agree: ``n // 0 == 0`` is
read faithfully, and what Lean's total division makes of it is the semantics
gap :mod:`lanky.semantics` notes. Two other exceptions are no comparison
(``silent``). Nothing is put down to rounding: the two readings make the same
operations in the same order, a sum included, and round alike, so a truth
value that differs is a disagreement.

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
it, and so does one in a part of an annotation that comes after a point where
both readings stop with no answer, in a sum or in an operation that is not a
connective or a quantifier. :meth:`lanky.theory.Theorem.faithful_fact` makes
the fact once per claim, and :func:`lanky.check.establish` rests every pass,
decision and proof of the claim on it, and offers a claim whose reading is
refuted to no oracle.
"""

from __future__ import annotations

import ast
import builtins
import functools
import inspect
import itertools
import math
import numbers
import operator
import random
import types
import warnings
from collections.abc import Callable, Iterable, Iterator, Sequence
from contextlib import closing
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
from fractions import Fraction
from typing import Any

import numpy
import pymbolic.primitives as prim

from lanky.intervals import ComplexValue
from lanky.ledger import FAITHFUL, Fact, Status, fact_id
from lanky.prelude import FinType, FnType, LankyType, Refined, Sort, SumType
from lanky.terms import (
    BUILTIN_OVERRIDES,
    Exists,
    Forall,
    LankyEvaluationMapper,
    Polarity,
    Undecided,
    Var,
    concrete_sorts,
    evaluate,
    init_args,
    render,
    sort_free_names,
)
from lanky.terms import Sum as SumTerm
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
    "SIZE_POINTS",
    "SORT_POINTS",
    "STATEMENT",
    "WALK_POINTS",
    "WRITTEN",
    "WRITTEN_MAX",
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

#: How many integers written in a claim, or next to one, are drawn at, the
#: nearest to zero first (see :func:`_written`).
WRITTEN = 12

#: The largest integer written in a claim that is drawn at, in magnitude: an
#: annotation computes at the values it is drawn at, and ``2 ** n`` at a
#: written ``2 ** 63`` would not end.
WRITTEN_MAX = 4096

#: About how many points a walk over the claim's domains may take at a draw
#: at a written value: a variable that sizes a domain, the ``n`` of
#: ``Fin[n]``, takes a written value only up to the size at which the domains
#: nested in the claim, each that large, hold this many points.
SIZE_POINTS = 1024

#: How many points one reading of one annotation may walk at a draw of a
#: claim that writes an integer the draws take, before the draw is given up as
#: too large to walk: a size kept to :data:`SIZE_POINTS` can still size a
#: domain of ``2 ** n`` points.
WALK_POINTS = 1 << 15

#: The small values each sort's sample starts with.
_SMALL: dict[str, tuple[Any, ...]] = {
    "Nat": (0, 1, 2),
    "Int": (0, -1, 1),
    "Real": (Fraction(0), Fraction(1), Fraction(-1, 2)),
    "Complex": (0j, 1 + 0j, 1j),
    "Bool": (False, True),
    "Prop": (False, True),
}

#: What Python raises where it stops with no answer at a point: a family
#: applied outside its domain, a division by zero, an elementary function
#: outside its domain (:class:`lanky.terms.UndefinedValue`), an overflow. Two
#: readings that raise one of these, of one type, agree that there is no value
#: there.
_OPEN = (Undecided, ArithmeticError)

# {{{ the rerun


def _is_truth(value: Any) -> bool:
    """Whether ``value`` is a truth value, Python's or numpy's."""
    return isinstance(value, bool | numpy.bool_)


def _kleene(settles: bool, operands: Iterable[Callable[[], Any]]) -> bool:
    """A conjunction (``settles`` false) or a disjunction of truth values, read three-valued.

    Each operand is a thunk, asked in order. The first that answers
    ``settles`` answers the whole, whatever an operand before it raised; an
    operand that raises, whatever it raises, is passed over as having no
    answer here, and when nothing settles the whole the first such exception
    is raised again. That is how lanky reads its connectives
    (:func:`lanky.terms.conjoin`), there for the answers lanky knows to be
    open; here, where only a comparison of two readings is made, for every
    exception, so that an exception never keeps an operand after it from
    being compared on both sides.

    Raises:
        TypeError: If an operand answers something that is not a truth
            value, which is passed over like any other exception.
    """
    pending: Exception | None = None
    for operand in operands:
        try:
            value = _truth(operand())
        except Exception as exc:  # noqa: BLE001 - an operand with no answer is passed over
            if pending is None:
                pending = exc
            continue
        if value == settles:
            return settles
    if pending is not None:
        raise pending
    return not settles


def _truth(value: Any) -> bool:
    """``value`` as a truth value, or :exc:`TypeError` where it is none, as lanky reads it."""
    if _is_truth(value):
        return bool(value)
    raise TypeError(f"{_shown(value)} is not a truth value")


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
    :func:`_kleene` reads them, and as the term's reading does
    (:class:`_Reading`). Python's ``|`` runs both operands first, so ``(i ==
    0) | (f(i - 1) <= f(i))`` stopped at ``f(-1)`` where lanky's reading is
    true. Of anything else it is Python's own operator, the bitwise one on
    two integers.
    """
    python = operator.or_ if settles else operator.and_

    def apply(left: Callable[[], Any], right: Callable[[], Any]) -> Any:
        pending: Exception | None = None
        try:
            first = left()
        except Exception as exc:  # noqa: BLE001 - an operand with no answer is passed over
            pending, first = exc, _MISSING
        if first is not _MISSING and not _is_truth(first):
            return python(first, right())
        if first is not _MISSING and bool(first) == settles:
            return settles
        try:
            second = right()
        except Exception:
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


def _both(*operands: Callable[[], Any]) -> bool:
    """``and`` in a generator's ``if`` clause, read three-valued as one conjunction of guards.

    lanky's reading records each operand of such an ``and`` as a guard of its
    own, one conjunction of them all (#97), so the rerun reads it the same
    way. A value that is not a truth value is read by its truthiness, as
    Python's ``and`` reads it.
    """
    return _kleene(False, (lambda op=op: _truthy(op()) for op in operands))


def _truthy(value: Any) -> bool:
    """A truth value as it is, and anything else by its truthiness, as ``and`` reads it."""
    return bool(value) if not _is_truth(value) else value


class _TooLarge(BaseException):  # noqa: N818 - not an error, a walk given up
    """A reading at a counted draw walked more than :data:`WALK_POINTS` points (see :class:`_Draw`).

    It is no ``Exception``, so that neither reading passes over it as a point
    with no answer: it gives the draw up (see :func:`_compare`).
    """


#: The points the walk at the current draw may still take, or ``None`` where
#: the draw is not counted (see :class:`_Draw`).
_BUDGET: ContextVar[list[int] | None] = ContextVar("lanky_faithful_budget", default=None)


def _step() -> None:
    """Count one point a walk takes, and give the draw up past its budget.

    Raises:
        _TooLarge: If the walks at this draw have taken :data:`WALK_POINTS`
            points.
    """
    budget = _BUDGET.get()
    if budget is None:
        return
    budget[0] -= 1
    if budget[0] < 0:
        raise _TooLarge(f"the walk took more than {WALK_POINTS} points")


def _domain(opened: list[Exception], thunk: Callable[[], Any]) -> Iterator[Any]:
    """The points of one ``for`` clause of a quantifier's generator, or none, noting why.

    ``thunk`` is the clause's iterable, not yet evaluated. Where evaluating
    it, or walking it, raises, the domain has no points to give here, and the
    exception is put in ``opened`` (see :func:`_quantify`), as lanky's reading
    makes an open point of a domain it cannot enumerate, ``Fin[10 // i]`` at
    ``i = 0``.
    """
    try:
        points = iter(thunk())
    except Exception as exc:  # noqa: BLE001 - a domain with no points here
        opened.append(exc)
        return
    while True:
        try:
            point = next(points)
        except StopIteration:
            return
        except Exception as exc:  # noqa: BLE001 - a domain that stopped giving points
            opened.append(exc)
            return
        _step()
        yield point


def _quantify(settles: bool, make: Callable[[list[Exception]], Iterable[Any]]) -> bool:
    """``all`` (``settles`` false) or ``any`` of a generator, read as lanky's reading reads it.

    ``make`` makes the generator, rewritten by :class:`_Rerun`: each point is
    the ``if`` clauses of every ``for`` clause, as thunks, and the body, as a
    thunk, and a domain that has no points to give puts what it raised in the
    list ``make`` is handed (:func:`_domain`). The points are read in order,
    as :meth:`_Reading._quantify` reads the term's: a point whose guards
    reject it is skipped, and one whose body settles the quantifier, a
    counterexample to a universal or a witness to an existential, settles it
    when its guards hold. A point where a domain, a guard or the body has no
    answer is passed over, and so is one with a guard that has no answer and a
    body that would settle it; when nothing settles the quantifier, the first
    of these answers is raised again.
    """
    opened: list[Exception] = []
    pending: Exception | None = None
    seen = 0

    def note_opened() -> None:
        nonlocal pending, seen
        while seen < len(opened):
            pending = pending or opened[seen]
            seen += 1

    points = make(opened)
    try:
        for guards, body in points:
            note_opened()
            try:
                admitted: bool | Exception = _kleene(False, guards)
            except Exception as exc:  # noqa: BLE001 - a guard with no answer here
                admitted = exc
            if admitted is False:
                continue
            try:
                value = _truth(body())
            except Exception as exc:  # noqa: BLE001 - a body with no answer here
                pending = pending or exc
                continue
            if value != settles:
                continue
            if admitted is True:
                return settles
            pending = pending or admitted
    finally:
        close = getattr(points, "close", None)
        if close is not None:
            close()
    note_opened()
    if pending is not None:
        raise pending
    return not settles


def _add(log: list[list[tuple[str, Any]]], make: Callable[[list[Exception]], Any]) -> Any:
    """``sum`` of a generator, rewritten by :class:`_Rerun` as for :func:`_quantify`.

    Every point is walked, and the body's values at the points the guards
    admit are added with Python's ``sum``, which is what the rerun's ``sum``
    computes. A point where a domain, a guard or the body has no answer
    leaves the sum with none, as it leaves Python's, and the first such
    exception is raised; the points after it are walked all the same, and
    what the sum came to at each point (:func:`_points_of`) is put in ``log``,
    so that a misreading at a point after one where both readings stop is
    compared all the same (see :func:`_compare`).
    """
    opened: list[Exception] = []
    outcomes: list[tuple[str, Any]] = []
    values: list[Any] = []
    pending: Exception | None = None
    seen = 0

    def note_opened() -> None:
        nonlocal pending, seen
        while seen < len(opened):
            pending = pending or opened[seen]
            outcomes.append(("no points", type(opened[seen]).__name__))
            seen += 1

    points = make(opened)
    try:
        for guards, body in points:
            note_opened()
            try:
                admitted = _kleene(False, guards)
            except Exception as exc:  # noqa: BLE001 - a guard with no answer here
                pending = pending or exc
                outcomes.append(("no guard", type(exc).__name__))
                continue
            if not admitted:
                continue
            try:
                value = body()
            except Exception as exc:  # noqa: BLE001 - a body with no answer here
                pending = pending or exc
                outcomes.append(("no value", type(exc).__name__))
                continue
            outcomes.append(("value", value))
            values.append(value)
    finally:
        close = getattr(points, "close", None)
        if close is not None:
            close()
    note_opened()
    if pending is not None:
        log.append(outcomes)
        raise pending
    return builtins.sum(values)


#: The names the rerun calls its own functions by (see :class:`_Rerun`).
_RERUN_NAMES: dict[str, Any] = {
    "__lanky_not__": _not,
    "__lanky_and__": _connective(False),
    "__lanky_or__": _connective(True),
    "__lanky_both__": _both,
    "__lanky_domain__": _domain,
    "__lanky_quantify__": _quantify,
}

#: Stands for a binder that had no value before the walk bound it.
_ABSENT = object()


def _reduction_names(namespace: dict[str, Any]) -> dict[str, str]:
    """The names an annotation quantifies and sums by: ``"all"``, ``"any"`` or ``"sum"`` for each.

    ``all``, ``any`` and ``sum`` are lanky's in an annotation whatever the
    module binds them to (:data:`lanky.terms.BUILTIN_OVERRIDES`), and so is a
    name the module binds to lanky's own :func:`~lanky.terms.forall`,
    :func:`~lanky.terms.exists` or :func:`~lanky.terms.sum_`, such as
    loopty's ``reduce_sum``.
    """
    names = {name: name for name in ("all", "any", "sum")}
    ours = {id(BUILTIN_OVERRIDES[name]): name for name in ("all", "any", "sum")}
    for name, value in namespace.items():
        if id(value) in ours:
            names[name] = ours[id(value)]
    return names


def _scope(namespace: dict[str, Any]) -> dict[str, Any]:
    """The globals the rerun evaluates an annotation in: the module's, and the rerun's own names.

    ``all``, ``any``, ``sum`` and ``abs`` are lanky's in an annotation
    whatever the module binds them to, as :func:`lanky.terms.evaluate_annotations`
    reads them, and lanky's at concrete values are Python's.
    """
    scope = dict(namespace)
    scope.update(_RERUN_NAMES)
    for name in BUILTIN_OVERRIDES:
        scope[name] = getattr(builtins, name)
    return scope


def _thunk(node: ast.expr) -> ast.Lambda:
    """``lambda: node``."""
    arguments = ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[])
    return ast.Lambda(arguments, node)


def _call(name: str, *args: ast.expr) -> ast.Call:
    """``name(*args)``."""
    return ast.Call(ast.Name(name, ast.Load()), list(args), [])


class _Rerun(ast.NodeTransformer):
    """Rewrite an annotation's source so that its connectives and quantifiers are lanky's.

    ``~operand`` becomes ``__lanky_not__(operand)``, and ``left | right``
    becomes ``__lanky_or__(lambda: left, lambda: right)``, so that an operand
    is run only when it is asked for (see :func:`_connective`).

    ``all(body for i in D if g for j in E(i) if h)``, called by a name in
    ``names`` (:func:`_reduction_names`), becomes
    ``__lanky_quantify__(False, lambda opened: (((lambda: g, lambda: h),
    lambda: body) for i in __lanky_domain__(opened, lambda: D) for j in
    __lanky_domain__(opened, lambda: E(i))))``: the same clauses, with every
    ``if`` moved to the point, as lanky's term holds them, and each piece run
    when :func:`_quantify` asks for it, so that what one raises does not end
    the walk. ``sum`` over a generator becomes ``__lanky_sum__`` of the same
    points (:func:`_add`). An ``and`` in an ``if`` clause is read three-valued
    too (:func:`_both`). A generator that binds a name with ``:=`` is left as
    it is written, and runs as Python runs it: the thunk would bind the name
    for itself alone.
    """

    def __init__(self, names: dict[str, str]) -> None:
        self.names = names

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Any:
        """``~operand`` as ``__lanky_not__(operand)``; any other operator as it is."""
        self.generic_visit(node)
        if not isinstance(node.op, ast.Invert):
            return node
        return ast.copy_location(_call("__lanky_not__", node.operand), node)

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        """``left & right`` and ``left | right`` as calls on thunks; anything else as it is."""
        self.generic_visit(node)
        name = {ast.BitAnd: "__lanky_and__", ast.BitOr: "__lanky_or__"}.get(type(node.op))
        if name is None:
            return node
        return ast.copy_location(_call(name, _thunk(node.left), _thunk(node.right)), node)

    def visit_Call(self, node: ast.Call) -> Any:
        """A quantifier or a sum over a generator as the rerun reads it; any other call as it is."""
        self.generic_visit(node)
        kind = self.names.get(node.func.id) if isinstance(node.func, ast.Name) else None
        if kind is None or len(node.args) != 1 or node.keywords:
            return node
        (generator,) = node.args
        readable = ast.GeneratorExp if kind == "sum" else ast.GeneratorExp | ast.ListComp
        if (
            not isinstance(generator, readable)
            or any(clause.is_async for clause in generator.generators)
            # a name bound by := in a clause is the generator's to read, and a
            # thunk would bind it to itself, so such a generator runs as written
            or any(isinstance(part, ast.NamedExpr) for part in ast.walk(generator))
        ):
            return node
        guards = [_guard(test) for clause in generator.generators for test in clause.ifs]
        clauses = [
            ast.comprehension(
                target=clause.target,
                iter=_call(
                    "__lanky_domain__",
                    ast.Name("__lanky_opened__", ast.Load()),
                    _thunk(clause.iter),
                ),
                ifs=[],
                is_async=0,
            )
            for clause in generator.generators
        ]
        point = ast.Tuple(
            [ast.Tuple([_thunk(guard) for guard in guards], ast.Load()), _thunk(generator.elt)],
            ast.Load(),
        )
        arguments = ast.arguments(
            posonlyargs=[],
            args=[ast.arg("__lanky_opened__")],
            kwonlyargs=[],
            kw_defaults=[],
            defaults=[],
        )
        make = ast.Lambda(arguments, ast.GeneratorExp(point, clauses))
        if kind == "sum":
            return ast.copy_location(_call("__lanky_sum__", make), node)
        settles = ast.Constant(kind == "any")
        return ast.copy_location(_call("__lanky_quantify__", settles, make), node)


def _guard(test: ast.expr) -> ast.expr:
    """An ``if`` clause's test, an ``and`` at its top read three-valued (:func:`_both`).

    lanky's reading refuses an ``or`` of propositions there, so an ``or`` is
    left as Python's.
    """
    if isinstance(test, ast.BoolOp) and isinstance(test.op, ast.And):
        return _call("__lanky_both__", *(_thunk(_guard(value)) for value in test.values))
    return test


def _compiled(source: str, names: dict[str, str]) -> Any:
    """An annotation's source compiled for the rerun, its connectives, quantifiers and sums lanky's.

    ``eval`` strips the spaces and tabs a string starts with and ``compile``
    does not, so they are stripped here as :func:`lanky.terms.evaluate_annotations`
    strips them.
    """
    with warnings.catch_warnings():
        # Python warned about the source when lanky read it, ``is not`` with
        # a literal say, and saying it twice says nothing more.
        warnings.simplefilter("ignore", SyntaxWarning)
        tree = ast.parse(source.lstrip(" \t"), "<string>", "eval")
        tree = ast.fix_missing_locations(_Rerun(names).visit(tree))
        return compile(tree, "<string>", "eval")


@dataclass(frozen=True)
class _Outcome:
    """What one reading of one annotation came to at one draw: a value, or what it raised."""

    value: Any = None
    error: Exception | None = None
    #: What a sum with no value came to at its points, where that is the difference.
    sums: str = ""

    def text(self) -> str:
        """The outcome as a reason says it."""
        if self.error is not None:
            said = f"raises {type(self.error).__name__}: {self.error}"
        else:
            said = f"computes {_shown(self.value)}"
        if self.sums:
            said += f", its sums with no value coming to {self.sums} at their points"
        return said


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


class _Unbound:
    """A point of the term's walk where a binder's domain had no points to give, and why."""

    def __init__(self, reason: Exception) -> None:
        self.reason = reason


class _Reading(LankyEvaluationMapper):
    """lanky's evaluator in the Python reading, its quantifiers and connectives read as the rerun's.

    A sort is read as the sample the rerun iterated. A quantifier walks its
    points in order (:meth:`_quantify`) and a connective its operands
    (:func:`_kleene`), passing over whatever a point or an operand raised, as
    the rerun does (:func:`_quantify`, :func:`_connective`). A sum is added
    by Python's ``sum`` (:meth:`map_lanky_sum`).

    Attributes:
        unsummed: What each sum that had no value came to at each point, in
            the order the sums were met (see :func:`_add`).
    """

    def __init__(self, context: dict[str, Any], samples: _Samples) -> None:
        super().__init__(context, samples, Polarity.POSITIVE)
        self.exact = False
        #: What each sum that had no value came to at each of its points.
        self.unsummed: list[list[tuple[str, Any]]] = []

    @staticmethod
    def is_exhaustive(domain: Any) -> bool:
        """Every domain is walked whole: a sort's sample is its domain here."""
        return True

    def map_logical_and(self, expr: prim.LogicalAnd) -> bool:
        """The conjunction, read three-valued as the rerun reads ``&`` (:func:`_kleene`)."""
        return _kleene(False, (lambda child=child: self._truth(child) for child in expr.children))

    def map_logical_or(self, expr: prim.LogicalOr) -> bool:
        """The disjunction, read three-valued as the rerun reads ``|`` (:func:`_kleene`)."""
        return _kleene(True, (lambda child=child: self._truth(child) for child in expr.children))

    def _every(
        self, binders: Sequence[tuple[Var, Any]], polarity: Polarity, unsure: Any = None
    ) -> Iterator[Any]:
        """Bind the binders at each point in turn, as the rerun's ``for`` clauses walk them.

        Each assignment is yielded as ``None``, or as the exception a
        refinement of a domain raised there, which leaves the point's guard
        without an answer; a domain that had no points to give, or stopped
        giving them, is yielded once as an :class:`_Unbound`, with nothing
        bound, as :func:`_domain` notes it. The bindings are restored on the
        way out, as :meth:`~lanky.terms.LankyEvaluationMapper.assignments`
        restores them.
        """
        if not binders:
            yield unsure
            return
        (var, domain), rest = binders[0], binders[1:]
        saved = self.context.get(var.name, _ABSENT)
        try:
            try:
                points = iter(self._points(domain))
            except Exception as exc:  # noqa: BLE001 - a domain with no points here
                yield _Unbound(exc)
                return
            while True:
                try:
                    point = next(points)
                except StopIteration:
                    break
                except Exception as exc:  # noqa: BLE001 - a domain that stopped giving points
                    yield _Unbound(exc)
                    break
                _step()
                self.context[var.name] = point
                here = unsure
                try:
                    if not self._admits(domain, polarity):
                        continue
                except Exception as exc:  # noqa: BLE001 - a refinement with no answer here
                    here = here or exc
                yield from self._every(rest, polarity, here)
        finally:
            if saved is _ABSENT:
                self.context.pop(var.name, None)
            else:
                self.context[var.name] = saved

    def _quantify(self, expr: Forall | Exists) -> bool:
        """A quantifier read as the rerun reads the generator it was written as (:func:`_quantify`).

        The points come in the order the rerun walks them, and at each the
        guard, the ``if`` clauses as one conjunction, is read before the
        body. A point whose body settles the quantifier, a counterexample to
        a universal or a witness to an existential, settles it when its
        guard holds. A point where a domain, a refinement, the guard or the
        body has no answer, whatever it raised, is passed over, and so is one
        whose guard has no answer and whose body would settle it; when
        nothing settles the quantifier, the first of these answers is raised
        again. The evaluator's own reading passes over only the answers lanky
        knows to be open; this one is made to compare with the rerun, which
        passes over every exception, so that one stops neither reading
        before the points after it are compared.
        """
        settles = isinstance(expr, Exists)
        antecedent = self.polarity if settles else self.polarity.flipped()
        pending: Exception | None = None
        with closing(self._every(list(expr.binders), antecedent)) as points:
            for point in points:
                if isinstance(point, _Unbound):
                    pending = pending or point.reason
                    continue
                admitted: bool | Exception = True if point is None else point
                try:
                    if not self._holds(expr.guard, antecedent):
                        continue
                except Exception as exc:  # noqa: BLE001 - a guard with no answer here
                    admitted = admitted if admitted is not True else exc
                try:
                    body = self._truth(expr.body)
                except Exception as exc:  # noqa: BLE001 - a body with no answer here
                    pending = pending or exc
                    continue
                if body != settles:
                    continue
                if admitted is True:
                    return settles
                pending = pending or admitted
        if pending is not None:
            raise pending
        return not settles

    def map_lanky_sum(self, expr: SumTerm) -> Any:
        """Add the body over the guarded domain with Python's ``sum``, as :func:`_add` adds.

        The values are those of the body at each point the guard admits, in
        the order of the walk, and Python's ``sum`` over them is what Python's
        ``sum`` over the annotation's generator computes, to the last bit:
        since Python 3.12 it compensates as it adds floating-point numbers,
        where adding them one by one, as the evaluator does, can differ in the
        last bit, and a comparison of the sum with ``1.0`` with it. A point
        where a domain, the guard or the body has no answer leaves the sum
        with none, and the first such exception is raised once every point
        has been walked; what the sum came to at each point goes in
        :attr:`unsummed`, as :func:`_add` puts the rerun's.
        """
        outcomes: list[tuple[str, Any]] = []
        values: list[Any] = []
        pending: Exception | None = None
        with closing(self._every(list(expr.binders), self.polarity)) as points:
            for point in points:
                if isinstance(point, _Unbound):
                    pending = pending or point.reason
                    outcomes.append(("no points", type(point.reason).__name__))
                    continue
                try:
                    if point is not None:
                        raise point
                    admitted = self._holds(expr.guard, self.polarity)
                except Exception as exc:  # noqa: BLE001 - a guard with no answer here
                    pending = pending or exc
                    outcomes.append(("no guard", type(exc).__name__))
                    continue
                if not admitted:
                    continue
                try:
                    value = self.rec(expr.body)
                except Exception as exc:  # noqa: BLE001 - a body with no answer here
                    pending = pending or exc
                    outcomes.append(("no value", type(exc).__name__))
                    continue
                outcomes.append(("value", value))
                values.append(value)
        if pending is not None:
            self.unsummed.append(outcomes)
            raise pending
        return builtins.sum(values)


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


@dataclass(frozen=True)
class _Extent:
    """The integers a claim's draws take besides the corners, and how large a size may be.

    Attributes:
        written: The integers written in the claim and next to them
            (:func:`_written`), nearest to zero first.
        sizes: The names that size a domain the claim walks, a ``Fin``'s bound
            in a variable's sort or a binder's domain (:func:`_extent`).
        largest: The largest magnitude a written value gives a variable in
            ``sizes``, or an entry of a family in it, or a point of a sort's
            sample, any of which can size a domain.
    """

    written: tuple[int, ...] = ()
    sizes: frozenset[str] = frozenset()
    largest: int = SIZE_POINTS


class _Samples:
    """The finite sample each sort iterates at one draw, the same for both readings.

    A sort's sample is its small values (:data:`_SMALL`), :data:`SORT_POINTS`
    of the tester's draws of it and the integers written in the claim
    (:class:`_Extent`), drawn the first time the sort is iterated at the draw
    and kept, so that the rerun and the term range over the same points
    wherever and however often they iterate it.
    """

    def __init__(self, rng: random.Random, extent: _Extent | None = None) -> None:
        self.rng = rng
        self.extent = extent or _Extent()
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
            drawn = [_python(sample_value(sort, self.rng, {})) for _ in range(SORT_POINTS)]
            written = [
                _at(value, sort.name)
                for value in self.extent.written
                if sort.name in ("Real", "Complex") or abs(value) <= self.extent.largest
            ]
            for point in (*drawn, *written):
                if point is None:
                    continue
                if not any(type(point) is type(seen) and point == seen for seen in points):
                    points.append(point)
        self.drawn.append((sort, points))
        return points

    def described(self) -> dict[str, list[Any]]:
        """The samples drawn, by sort, as a reason shows them."""
        return {str(sort): list(points) for sort, points in self.drawn}


def _at(value: int, sort: str) -> Any:
    """The written integer ``value`` as a value of the sort named ``sort``, or ``None``.

    A natural takes its magnitude, so that a written ``-7`` reaches ``7``
    too; a truth value has no integer to take.
    """
    if sort == "Nat":
        return abs(value)
    if sort == "Int":
        return value
    if sort == "Real":
        return Fraction(value)
    if sort == "Complex":
        return complex(value)
    return None


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


class _Pinned(random.Random):
    """A stand-in for the tester's random source that draws every value at one written integer.

    A natural, an integer, a real or a complex number is the integer itself
    (:func:`_at`), up to :attr:`_Extent.largest` in magnitude where it sizes a
    domain; a point of a ``Fin`` is the point nearest to it, the domain's last
    one when it is past the end; a truth value is whether it is odd.
    """

    def __init__(self, value: int, extent: _Extent) -> None:
        super().__init__(value)
        self.value = value
        self.extent = extent

    def at(self, sort: Sort, size: bool) -> Any:
        """The value of ``sort``, a sort the tester samples, for a variable or an entry."""
        if sort.name in ("Bool", "Prop"):
            return self.value % 2 == 1
        value = self.value
        if size:
            value = max(-self.extent.largest, min(value, self.extent.largest))
        return _at(value, sort.name)

    def randrange(self, start: int, stop: int | None = None, step: int = 1) -> int:  # type: ignore[override]
        """The value of the range nearest to the written integer."""
        if stop is None:
            start, stop = 0, start
        if stop <= start:
            raise ValueError(f"empty range for randrange({start}, {stop})")
        return max(start, min(self.value, stop - 1))

    def random(self) -> float:
        """``0``, whatever the value."""
        return 0.0


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
        self,
        domain: Any,
        codomain: Any,
        source: random.Random,
        context: dict[str, Any],
        name: str,
        size: bool = False,
    ) -> None:
        self.domain = domain
        self.codomain = codomain
        self.source = source
        self.context = context
        self.name = name
        self.size = size
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
            self.values[point] = _draw(self.codomain, self.source, self.context, size=self.size)
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
    sort: Any,
    source: random.Random,
    context: dict[str, Any],
    name: str | None = None,
    size: bool = False,
) -> Any:
    """One value of ``sort`` for the comparison, drawn as the tester draws it where it can.

    A family over a ``Fin`` is a table, and one over anything else a
    :class:`DrawnFamily`; their values are drawn from what their codomain
    refines, since an entry has no name to read a refinement of. A variable
    of a refined sort is drawn as the tester draws it, and from what the sort
    refines when no draw satisfies the refinement: the readings are compared
    whether or not a draw satisfies the hypotheses. At a written integer
    (:class:`_Pinned`) the value is drawn from what the sort refines at once.
    ``size`` says whether the value, or a family's entries, size a domain.

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
            if isinstance(source, _Pinned) and bound > WALK_POINTS:
                raise SkipSample(f"{domain} has {bound} points, too many to draw a family over")
            return Table(
                [_draw(codomain, source, context, size=size) for _ in range(bound)],
                name=name or "a family",
            )
        return DrawnFamily(domain, codomain, source, dict(context), name or "a family", size)
    if isinstance(source, _Pinned):
        base = _unrefined(sort)
        if isinstance(base, Sort) and base.name in SAMPLED_SORTS:
            return source.at(base, size)
        return _python(sample_value(base, source, context))
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
    """One draw: its label, the values of the variables, and the samples of the sorts.

    ``counted`` says whether the walks at it count their points against
    :data:`WALK_POINTS`, which they do wherever the claim writes an integer
    the draws take: at a draw at one, and at every other draw, whose samples
    of the sorts hold them.
    """

    label: str
    context: dict[str, Any]
    samples: _Samples
    counted: bool = False


def _draws(
    variables: Sequence[tuple[str, Any]],
    hypotheses: Sequence[Any],
    extent: _Extent | None = None,
) -> Iterator[Any]:
    """The draws to compare at, corner draws first; for one that could not be made, why not.

    The corners come first, then a draw at each integer written in the claim
    (``extent``, see :func:`_written`), then the tester's draws. Each draw
    takes a value of every variable, a size before what it sizes
    (:func:`lanky.testing.sampling_order`), and then assigns the definitional
    hypotheses, as the tester does, so that a family that is a scan of
    another is one. A statement with no variables has one draw, the empty one.
    """
    extent = extent or _Extent()
    ordered = sampling_order(variables)
    sorts = dict(ordered)
    rng = random.Random(SEED)
    sources: list[tuple[str, random.Random]] = [
        (f"corner {k}", _Corners(k)) for k in range(CORNERS if ordered else 1)
    ]
    if ordered:
        sources += [(f"written {value}", _Pinned(value, extent)) for value in extent.written]
    made = 0
    attempt = 0
    while sources or (ordered and made < SAMPLES and attempt < SAMPLES * ATTEMPTS):
        if sources:
            label, source = sources.pop(0)
        else:
            label, source = f"draw {attempt}", rng
            attempt += 1
        samples = _Samples(random.Random(f"{SEED}:{label}"), extent)
        context: dict[str, Any] = {}
        try:
            for name, sort in ordered:
                context[name] = _draw(sort, source, context, name, size=name in extent.sizes)
            satisfy_hypotheses(hypotheses, context, sorts, samples)
        except Exception as exc:  # noqa: BLE001 - a draw that cannot be made is skipped
            yield str(exc) or type(exc).__name__
            continue
        if label.startswith("draw"):
            made += 1
        # a written integer reaches the samples of the sorts at every draw
        yield _Draw(label, context, samples, counted=bool(extent.written))


#: How deep the functions an annotation calls are read for the integers they hold.
_CALL_DEPTH = 3

#: How many items of a module-level container are read for the integers they hold.
_CONTAINER_ITEMS = 256


def _written(codes: Sequence[Any], namespace: dict[str, Any]) -> tuple[int, ...]:
    """The integers written in a claim and next to them, to draw at, nearest to zero first.

    ``codes`` are the claim's annotations compiled for the rerun, read in
    ``namespace``. An annotation reaches a value through what it is written
    with: its constants, the functions it calls and the constants, defaults
    and closures of those, :data:`_CALL_DEPTH` calls deep, and the integers a
    module-level name or container holds (``{1000: 1}`` in a helper, ``K =
    6``). Each such integer ``c`` gives ``c - 1``, ``c`` and ``c + 1``, which
    are kept where the corners do not reach them, past ``MAX_NAT`` or below
    ``-1``, and up to :data:`WRITTEN_MAX` in magnitude; the :data:`WRITTEN`
    nearest to zero are drawn at.
    """
    found: set[int] = set()
    seen: set[int] = set()

    def take(value: Any) -> None:
        if isinstance(value, bool):
            return
        if isinstance(value, int):
            found.add(value)
        elif isinstance(value, float) and math.isfinite(value) and value.is_integer():
            found.add(int(value))
        elif isinstance(value, Fraction) and value.denominator == 1:
            found.add(int(value))

    def read_code(code: types.CodeType, globals_: dict[str, Any], depth: int) -> None:
        if id(code) in seen:
            return
        seen.add(id(code))
        for constant in code.co_consts:
            if isinstance(constant, types.CodeType):
                read_code(constant, globals_, depth)
            elif isinstance(constant, tuple | frozenset):
                for item in constant:
                    take(item)
            else:
                take(constant)
        for name in code.co_names:
            read_object(globals_.get(name), depth)

    def read_object(value: Any, depth: int) -> None:
        if value is None or isinstance(value, bool) or id(value) in seen:
            return
        if isinstance(value, int | float | Fraction):
            take(value)
            return
        seen.add(id(value))
        function = getattr(value, "__wrapped__", value)
        if isinstance(function, types.FunctionType):
            # lanky's own functions, such as lanky.sum, hold no value of the claim's;
            # a checked file's module is named lanky_checked_..., which is not one
            if depth >= _CALL_DEPTH or str(function.__module__).split(".")[0] == "lanky":
                return
            read_code(function.__code__, function.__globals__, depth + 1)
            for default in function.__defaults__ or ():
                take(default)
            for cell in function.__closure__ or ():
                try:
                    read_object(cell.cell_contents, depth + 1)
                except ValueError:  # an empty cell
                    pass
        elif isinstance(value, dict) and len(value) <= _CONTAINER_ITEMS:
            for key, item in value.items():
                take(key)
                take(item)
        elif isinstance(value, list | tuple | set | frozenset) and len(value) <= _CONTAINER_ITEMS:
            for item in value:
                take(item)

    for code in codes:
        read_code(code, namespace, 0)
    near = {c + step for c in found for step in (-1, 0, 1)}
    kept = sorted(
        (v for v in near if (v > MAX_NAT or v < -1) and abs(v) <= WRITTEN_MAX),
        key=lambda v: (abs(v), v < 0),
    )
    return tuple(kept[:WRITTEN])


def _extent(theorem: Any, codes: Sequence[Any]) -> _Extent:
    """What the claim's draws take besides the corners (see :class:`_Extent`).

    A name sizes a domain where it is free in the bound of a ``Fin`` the claim
    holds, in a variable's sort or in a quantifier's or a sum's domain. A
    walk at a draw takes about the product of its nested domains' sizes, so
    a size takes a written value only up to the root of :data:`SIZE_POINTS`
    by how deeply the claim nests its domains and its families.
    """
    sizes: set[str] = set()

    def sort_depth(sort: Any) -> int:
        if isinstance(sort, FinType):
            names = sort_free_names(sort)
            sizes.update(names)
            return 1 if names else 0
        if isinstance(sort, FnType):
            return sort_depth(sort.domain) + sort_depth(sort.codomain)
        if isinstance(sort, Refined):
            return max(sort_depth(sort.base), *(term_depth(prop) for prop in sort.props))
        if isinstance(sort, SumType):
            return max((sort_depth(piece) for piece in sort.pieces), default=0)
        return 0

    def term_depth(expr: Any) -> int:
        if isinstance(expr, Forall | Exists | SumTerm):
            for _var, domain in expr.binders:
                sort_depth(domain)
            return len(expr.binders) + max(term_depth(expr.body), term_depth(expr.guard))
        if isinstance(expr, prim.ExpressionNode):
            return max((term_depth(child) for child in init_args(expr)), default=0)
        if isinstance(expr, tuple | list):
            return max((term_depth(item) for item in expr), default=0)
        if isinstance(expr, LankyType):
            return sort_depth(expr)
        return 0

    depth = max(
        [
            *(sort_depth(sort) for _, sort in theorem.variables),
            *(term_depth(prop) for _, prop in theorem.hypotheses),
            term_depth(theorem.goal),
        ],
        default=0,
    )
    largest = max(MAX_NAT + 1, int(SIZE_POINTS ** (1 / depth))) if depth else SIZE_POINTS
    return _Extent(_written(codes, theorem.namespace), frozenset(sizes), largest)


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


def _nan(value: Any) -> bool:
    """Whether ``value`` is a floating-point NaN, real or complex."""
    if isinstance(value, complex | numpy.complexfloating):
        return bool(numpy.isnan(value))
    if isinstance(value, float | numpy.floating):
        return math.isnan(value)
    return False


def _same(left: Any, right: Any) -> bool | None:
    """Whether two values the readings computed are the same; ``None`` where ``==`` cannot say.

    They are compared with ``==``, exactly: a number, a table by its values, a
    type by its parts. Two NaNs are the same value, which ``==`` says of no
    NaN.
    """
    if _nan(left) and _nan(right):
        return True
    try:
        answer = left == right
    except Exception:  # noqa: BLE001 - values == cannot compare are not compared
        return None
    if not _is_truth(answer):
        return None
    return bool(answer)


def _judge(python: _Outcome, term: _Outcome) -> str:
    """How the two readings of one annotation compare at one draw.

    ``agreed``, the same value, or no value on either side for one reason
    (one of :data:`_OPEN`, of one type); ``differed``, which an exception on
    one side only is too, whatever it is; ``silent``, where both raised
    otherwise; or ``uncomparable``, a value that holds a term or that ``==``
    cannot compare.
    """
    if python.error is not None and term.error is not None:
        if isinstance(python.error, _OPEN) and type(python.error) is type(term.error):
            # neither has a value here, for the one reason: a division by
            # zero, say, or a family applied outside its domain
            return "agreed"
        return "silent"
    if python.error is not None or term.error is not None:
        # one reading has a value and the other none: i.name raising at a
        # number, or Python stopping at 1 // 0 where the term's or is True
        return "differed"
    left, right = python.value, term.value
    if _holds_term(left) or _holds_term(right):
        return "uncomparable"
    if _is_truth(left) != _is_truth(right):
        # a truth value and a number: one reading is a proposition and the
        # other is not, which the tester and Lean read differently
        return "differed"
    if _is_truth(left):
        return "agreed" if bool(left) == bool(right) else "differed"
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
    annotations (:attr:`lanky.theory.Theorem.namespace`), and the rerun runs
    in it (:func:`_scope`).
    """
    scope = _scope(namespace)
    for name in parameters:
        scope[name] = draw.context[name] if name in draw.context else Var(name)
    for annotation in annotations:
        unsummed: list[list[tuple[str, Any]]] = []
        scope["__lanky_sum__"] = functools.partial(_add, unsummed)
        reading = _Reading(dict(draw.context), draw.samples)
        try:
            python, term = _both_readings(annotation, scope, reading, draw)
        except _TooLarge as exc:
            yield annotation, "unwalked", _Outcome(error=exc), _Outcome(error=exc)
            return
        if not _same_points(unsummed, reading.unsummed):
            # a sum had no value on both sides, or on one, and its points differ
            python = replace(python, sums=_points_of(unsummed))
            term = replace(term, sums=_points_of(reading.unsummed))
            yield annotation, "differed", python, term
            continue
        yield annotation, _judge(python, term), python, term


def _both_readings(
    annotation: _Annotation, scope: dict[str, Any], reading: _Reading, draw: _Draw
) -> tuple[_Outcome, _Outcome]:
    """What the rerun of ``annotation`` and its term came to at ``draw``.

    Where the draw is counted (:class:`_Draw`), each reading may walk
    :data:`WALK_POINTS` points.

    Raises:
        _TooLarge: If one of them walked more than that, which gives the draw
            up.
    """
    token = _BUDGET.set([WALK_POINTS] if draw.counted else None)
    try:
        with concrete_sorts(draw.samples):
            try:
                if annotation.code is not None:
                    value = eval(annotation.code, scope, None)
                else:
                    value = annotation.given
                python = _Outcome(_value_at(value, _Reading(dict(draw.context), draw.samples)))
            except Exception as exc:  # noqa: BLE001 - what the annotation raises is its answer
                python = _Outcome(error=exc)
    finally:
        _BUDGET.reset(token)
    token = _BUDGET.set([WALK_POINTS] if draw.counted else None)
    try:
        try:
            term = _Outcome(_value_at(annotation.term, reading))
        except Exception as exc:  # noqa: BLE001 - what the term raises is its answer
            term = _Outcome(error=exc)
    finally:
        _BUDGET.reset(token)
    return python, term


def _same_points(left: list[list[tuple[str, Any]]], right: list[list[tuple[str, Any]]]) -> bool:
    """Whether the sums that had no value came to the same at each point on both sides.

    A value is compared as :func:`_same` compares it, and a point with no
    answer by where it had none, its domain, its guard or its body, and not
    by what was raised there, as two readings that raise otherwise are not a
    disagreement either (see :func:`_judge`).
    """
    if len(left) != len(right):
        return False
    for ours, theirs in zip(left, right, strict=True):
        if len(ours) != len(theirs):
            return False
        for (tag, value), (other_tag, other) in zip(ours, theirs, strict=True):
            if tag != other_tag:
                return False
            if tag == "value" and not (_holds_term(value) or _same(value, other)):
                return False
    return True


def _points_of(unsummed: list[list[tuple[str, Any]]]) -> str:
    """What the sums with no value came to at their points, as a reason says it."""
    if not unsummed:
        return "no sum without a value"
    shown = [
        ", ".join(_shown(value) if tag == "value" else f"{tag} ({value})" for tag, value in sum_)
        for sum_ in unsummed
    ]
    return "; ".join(f"[{points}]" for points in shown)


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
    names = _reduction_names(theorem.namespace)
    out: list[_Annotation] = []
    for name, annotation in raw.items():
        if name not in terms:
            continue
        role, term = terms[name]
        if isinstance(annotation, str):
            code = _compiled(annotation, names)
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
        extent = _extent(theorem, [a.code for a in annotations if a.code is not None])
        for draw in _draws(theorem.variables, hypotheses, extent):
            if isinstance(draw, str):
                tally.skipped.append(draw)
                continue
            tally.draws += 1
            for annotation, verdict, python, term in _compare(
                theorem.namespace, parameters, annotations, draw
            ):
                if verdict == "differed":
                    return _refuted(fact, annotation, draw, python, term)
                if verdict == "unwalked":
                    # given up as too large to walk, so the draw is not one
                    tally.draws -= 1
                    tally.skipped.append(f"{draw.label}: {python.error}")
                    tally.counts["unwalked"] = tally.counts.get("unwalked", 0) + 1
                    continue
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
