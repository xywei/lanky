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
Python evaluates it, so a helper function the annotation calls, a library and
a dict lookup run on numbers, as in the file run as a program. It runs in
the module as lanky found it when it read the claim (:class:`Snapshot`): what
the annotations reach, the names they read, the functions of the user's
modules they call, the names those read and what they close over, tables,
lists and numpy arrays included, is copied then, the functions bound to the
copy (:func:`capture`), and each draw runs in a copy of that copy
(:meth:`Snapshot.fresh`). So a helper reads what it read when the claim was
read, whatever the module rebinds or changes in place after the claim, and
whatever a helper changed at the draw before. What the copy cannot hold as
it was, an object of a type it does not know, a structure past
:data:`COPY_ITEMS`, leaves the reading untested: it is ``assumed``, naming
the object, where it would otherwise be ``tested``.
A parameter that is a variable is its drawn value, a family a
:class:`~lanky.testing.Table` or a family drawn as it is applied
(:class:`DrawnFamily`), both callable, and a parameter that is a hypothesis is
the variable lanky's reading makes of it. ``all``, ``any``, ``sum`` and
``abs`` are Python's, which is what lanky's are at concrete values; an
annotation that reads one of them in a module that binds it to anything else
is refused while it is read (#100). The prelude's types iterate concretely
while the rerun runs (:func:`lanky.terms.concrete_sorts`): ``Fin[n]`` at a
drawn ``n`` is ``range(n)`` already, and a sort with no end, ``Nat`` say,
iterates a finite sample of itself, drawn once per draw, which is the same
list wherever and however often the annotation iterates it.

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
(:func:`lanky.testing.sample_value`, from its seed). A draw whose readings
take more than :data:`DRAW_SECONDS`, a helper that takes time exponential in
its argument at a value the claim writes, or ask for a power of more than
:data:`POWER_BITS` bits, ``2 ** 2 ** n`` there, is given up as too slow
(``slow``) (#101): the walks and the term's reading ask for the time as they
go, and the user's code is stopped at a call or a turn of a loop
(:func:`_watching`). No interval timer keeps that time, so the check sets
none that would clobber one set around it (:mod:`lanky.deadline`'s, which
the oracles keep their deadlines with), and what such a deadline raises is
no ``Exception`` and passes through the check to its owner. Each draw has
that time of its own, a written value past one too slow to draw at too,
since a helper slow at ``999`` can answer otherwise at ``1000`` (#114);
once more than :data:`SLOW_DRAWS` draws of a claim have been given up so,
the check makes no more, and the reading is declined (#113).
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
(``silent``). Where both have no value, whatever the reason, what Python would
have evaluated after the operation that had none is compared on neither side,
so the draw is read again on both with what Python has no value for read as
Lean has it (:func:`lanky.terms.totalized`): ``x // 0`` and ``x / 0`` are
``0``, ``x % 0`` is ``x``, a logarithm or a square root outside its Python
domain is Mathlib's, and a family outside its domain is ``0``. Where both
then have a value they have to agree (#99): ``f(i) * 0 + 1 // (i - i) ==
table(i)`` is ``0 == 1`` at ``i = 0`` read so, and its misread term ``0 ==
0``. The rerun reads the operators the annotation writes so, and a helper's
are Python's, so a helper's division leaves the rerun without a value there,
and says nothing more; the term reads all of its own so, and has a value
wherever the rerun has one, the same one if it is faithful. Nothing is put
down to rounding: the two readings make the same operations in the same
order, a sum included, and round alike, so a truth value that differs is a
disagreement.

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
  defined that holds a term, an annotation that had no answer on both
  sides at any draw, or, where they agreed at every draw, annotations that
  reach what the snapshot could not copy (:attr:`Snapshot.shared`).

The check is sampled: a disagreement only at a point no draw reaches escapes
it, and so does one in a part of an annotation that comes after an operation
with no value in Python that Lean's reading leaves without one too, an
overflow, or that a helper makes, whose operations the rerun leaves Python's.
:meth:`lanky.theory.Theorem.faithful_fact` makes
the fact once per claim, and :func:`lanky.check.establish` rests every pass,
decision and proof of the claim on it, and offers a claim whose reading is
refuted to no oracle.
"""

from __future__ import annotations

import ast
import builtins
import collections
import enum
import functools
import gc
import inspect
import itertools
import math
import numbers
import operator
import os
import random
import re
import site
import sys
import sysconfig
import time
import types
import warnings
from collections.abc import Callable, Iterable, Iterator, Sequence
from contextlib import closing, contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
from fractions import Fraction
from pathlib import Path
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
    code_reads,
    concrete_sorts,
    evaluate,
    init_args,
    is_totalized,
    render,
    sort_free_names,
    totalized,
)
from lanky.terms import Sum as SumTerm
from lanky.testing import (
    MAX_NAT,
    SAMPLED_SORTS,
    OpenStatement,
    SkipSample,
    Table,
    Unsampleable,
    apply_at,
    in_sort,
    sample_value,
    sampling_order,
    satisfy_hypotheses,
    statement_free_names,
    totalized_value,
)

__all__ = [
    "COPY_ELEMENTS",
    "COPY_ITEMS",
    "CORNERS",
    "DECIDED_BY",
    "DRAW_SECONDS",
    "KIND",
    "POWER_BITS",
    "SAMPLES",
    "SEED",
    "SIZE_POINTS",
    "SLOW_DRAWS",
    "SORT_POINTS",
    "STATEMENT",
    "WALK_POINTS",
    "WRITTEN",
    "WRITTEN_MAX",
    "DrawnFamily",
    "Snapshot",
    "capture",
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

#: How many seconds the readings of a claim's annotations may take at one
#: draw, both readings of every annotation together and the draw's second
#: reading with them (#99), before the draw is given up as too slow (#101): a
#: helper that takes time exponential in its argument, at a value the claim
#: writes.
DRAW_SECONDS = 5.0

#: How many draws of one claim may be given up as too slow: at one more the
#: check draws no more, and the reading is declined (#113). Each such draw
#: costs :data:`DRAW_SECONDS`, and a helper slow at the small values the
#: corners and the tester draw made one claim cost a minute and more.
SLOW_DRAWS = 4

#: How many bits a power or a left shift may have that an annotation, or its
#: term, computes at a draw, an integer's or a fraction's: one past it, ``2 **
#: 2 ** n`` at a written ``99``, gives the draw up as too slow, since Python
#: computes it in one step that no deadline stops.
POWER_BITS = 1 << 20

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

    An operand that answers something other than a truth value has no answer
    either, as lanky's reading has it (:func:`_truth`).

    Raises:
        Exception: The first exception an operand raised, when no operand
            settles the whole.
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


class _GivenUp(BaseException):  # noqa: N818 - not an error, a draw given up
    """A draw given up: it is no ``Exception``, so neither reading passes over it.

    Neither reading takes it for a point or an operand with no answer, and a
    helper's ``except Exception`` lets it through: it gives the draw up (see
    :func:`_compare`), as one at which nothing was compared. ``verdict`` is
    what the draw is counted as.
    """

    verdict = "given up"


class _TooLarge(_GivenUp):
    """A reading at a counted draw walked more than :data:`WALK_POINTS` points (:class:`_Draw`)."""

    verdict = "unwalked"


class _TooSlow(_GivenUp):
    """The readings at a draw ran past :data:`DRAW_SECONDS`, or a power past :data:`POWER_BITS`."""

    verdict = "slow"


#: The points the walk at the current draw may still take, or ``None`` where
#: the draw is not counted (see :class:`_Draw`).
_BUDGET: ContextVar[list[int] | None] = ContextVar("lanky_faithful_budget", default=None)

#: When, by :func:`time.monotonic`, the readings at the current draw are given
#: up as too slow, or ``None`` outside a reading (see :func:`_both_readings`).
_DEADLINE: ContextVar[float | None] = ContextVar("lanky_faithful_deadline", default=None)

#: What gave the current reading up, or ``None`` outside a reading: kept, so
#: that a helper that catches it does not keep the draw (see :func:`_kept`).
_GIVEN_UP: ContextVar[list[_GivenUp] | None] = ContextVar("lanky_faithful_given_up", default=None)


def _giving_up(exc: _GivenUp) -> _GivenUp:
    """``exc``, noted as what gave the current reading up, to be raised."""
    given = _GIVEN_UP.get()
    if given is not None:
        given.append(exc)
    return exc


def _kept() -> None:
    """Give the draw up where a reading that has ended was given up, or is past its time.

    A helper that catches everything, ``except BaseException`` or a bare
    ``except``, catches what gives a draw up too, and the reading goes on
    with what the helper answered instead: that answer is not Python's, so
    the draw is given up all the same once the reading ends.

    Raises:
        _GivenUp: What gave the reading up, if anything did.
        _TooSlow: If the readings at this draw have run past their time.
    """
    given = _GIVEN_UP.get()
    if given:
        raise given[0]
    _on_time()


def _on_time() -> None:
    """Give the draw up if its readings have run past its time.

    The walks of both readings ask at every point (:func:`_step`), the
    term's reading at every node it evaluates (:meth:`_Reading.rec`), and
    the user's code at every call and every turn of a loop
    (:func:`_watching`).

    Raises:
        _TooSlow: If the readings at this draw have taken more than
            :data:`DRAW_SECONDS`.
    """
    deadline = _DEADLINE.get()
    if deadline is not None and time.monotonic() > deadline:
        raise _giving_up(
            _TooSlow(f"the readings at this draw took more than {DRAW_SECONDS:g} seconds")
        )


def _step() -> None:
    """Count one point a walk takes, and give the draw up past its budget or its time.

    Raises:
        _TooLarge: If the walks at this draw have taken :data:`WALK_POINTS`
            points.
        _TooSlow: If the readings at this draw have run past their time.
    """
    _on_time()
    budget = _BUDGET.get()
    if budget is None:
        return
    budget[0] -= 1
    if budget[0] < 0:
        raise _giving_up(_TooLarge(f"the walk took more than {WALK_POINTS} points"))


def _bits(value: Any) -> int | None:
    """How many bits an exact number has, an integer's, or a fraction's larger part's."""
    if isinstance(value, bool):
        return 1
    if isinstance(value, int):
        return value.bit_length()
    if isinstance(value, Fraction):
        return max(value.numerator.bit_length(), value.denominator.bit_length())
    return None


def _computable(name: str, left: Any, right: Any) -> None:
    """Give the draw up where a power or a left shift would have more than :data:`POWER_BITS` bits.

    Python computes such a number in one step, which no deadline stops
    (:func:`_on_time`): ``2 ** 2 ** n`` at a written ``99`` is never
    computed. A power of a float overflows instead, and one of an integer to
    a negative integer is a float.

    Raises:
        _TooSlow: If it would.
    """
    if name == "lshift":
        if isinstance(left, int) and isinstance(right, int) and left and right > POWER_BITS:
            raise _giving_up(
                _TooSlow(f"a left shift by {right} has more than {POWER_BITS} bits")
            )
        return
    if isinstance(right, Fraction) and right.denominator == 1:
        right = right.numerator
    if not isinstance(right, int) or isinstance(right, bool):
        return
    bits = _bits(left)
    if bits is None or bits < 2 or (right < 0 and isinstance(left, int)):
        return
    if abs(right) * bits > POWER_BITS:
        raise _giving_up(
            _TooSlow(
                f"a power of a number of {bits} bits to the {right} has more than "
                f"{POWER_BITS} bits"
            )
        )


def _lean_total(name: str, left: Any, right: Any) -> Any:
    """Lean's value where Python's operation raised ``ZeroDivisionError``; else ``_MISSING``.

    ``x / 0`` and ``x // 0`` are ``0``, ``x % 0`` is ``x``, and ``0 ** -k`` is
    ``0`` (``0⁻¹ = 0``), as :func:`lanky.terms.totalized` says.
    """
    try:
        zero = left == 0 and right < 0 if name == "pow" else right == 0
    except Exception:  # noqa: BLE001 - operands that cannot say are not a division by zero
        return _MISSING
    if not _is_truth(zero) or not zero:
        return _MISSING
    return left if name == "mod" else 0


def _arithmetic(name: str) -> Callable[[Any, Any], Any]:
    """Python's operator ``name``, as both readings compute it at a draw.

    It is Python's, except that a power or a left shift past
    :data:`POWER_BITS` gives the draw up (:func:`_computable`), and that
    inside :func:`lanky.terms.totalized` a division, a remainder or a power
    by zero is Lean's (:func:`_lean_total`). The rerun calls it for the
    operators the annotation writes (:class:`_Rerun`), and the term's
    reading for the term's (:class:`_Reading`), so that both read the same
    operation alike.
    """
    python = getattr(operator, name)

    def apply(left: Any, right: Any) -> Any:
        if name in ("pow", "lshift"):
            _computable(name, left, right)
        try:
            return python(left, right)
        except ZeroDivisionError:
            if not is_totalized():
                raise
            total = _lean_total(name, left, right)
            if total is _MISSING:
                raise
            return total

    apply.__name__ = apply.__qualname__ = f"lanky_{name}"
    return apply


_TRUEDIV = _arithmetic("truediv")
_FLOORDIV = _arithmetic("floordiv")
_MOD = _arithmetic("mod")
_POW = _arithmetic("pow")
_LSHIFT = _arithmetic("lshift")

#: The name the rerun calls each of the annotation's operators by, that
#: :func:`_arithmetic` reads (see :meth:`_Rerun.visit_BinOp`).
_ARITHMETIC: dict[type, str] = {
    ast.Div: "__lanky_truediv__",
    ast.FloorDiv: "__lanky_floordiv__",
    ast.Mod: "__lanky_mod__",
    ast.Pow: "__lanky_pow__",
    ast.LShift: "__lanky_lshift__",
}


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


def _bind(scope: dict[str, Any], variable: Callable[[], Any], name: str, value: Any) -> Any:
    """``name := value``, bound in the scope Python binds it in (see :class:`_Rerun`).

    ``variable`` is ``lambda: name``, written where the ``:=`` was. Where
    ``name`` is a variable of a lambda of the annotation's, that lambda is
    where Python binds it, and ``variable`` closes over its cell, which is
    set; anywhere else Python binds it in the annotation's globals,
    ``scope``.
    """
    cells = variable.__closure__
    if cells:
        cells[0].cell_contents = value
    else:
        scope[name] = value
    return value


#: The names the rerun calls its own functions by (see :class:`_Rerun`).
_RERUN_NAMES: dict[str, Any] = {
    "__lanky_not__": _not,
    "__lanky_and__": _connective(False),
    "__lanky_or__": _connective(True),
    "__lanky_both__": _both,
    "__lanky_domain__": _domain,
    "__lanky_quantify__": _quantify,
    "__lanky_live__": True,
    "__lanky_truediv__": _TRUEDIV,
    "__lanky_floordiv__": _FLOORDIV,
    "__lanky_mod__": _MOD,
    "__lanky_pow__": _POW,
    "__lanky_lshift__": _LSHIFT,
}

#: Stands for a binder that had no value before the walk bound it.
_ABSENT = object()


def _reduction_names(namespace: dict[str, Any], parameters: Iterable[str] = ()) -> dict[str, str]:
    """The names an annotation quantifies and sums by: ``"all"``, ``"any"`` or ``"sum"`` for each.

    ``all``, ``any`` and ``sum`` are lanky's in an annotation whatever the
    module binds them to (:data:`lanky.terms.BUILTIN_OVERRIDES`), and so is a
    name the module binds to lanky's own :func:`~lanky.terms.forall`,
    :func:`~lanky.terms.exists` or :func:`~lanky.terms.sum_`, such as
    loopty's ``reduce_sum``. A name that is one of the claim's
    ``parameters`` is the parameter, in both readings (#105).
    """
    names = {name: name for name in ("all", "any", "sum")}
    ours = {id(BUILTIN_OVERRIDES[name]): name for name in ("all", "any", "sum")}
    for name, value in namespace.items():
        if id(value) in ours:
            names[name] = ours[id(value)]
    for name in parameters:
        names.pop(name, None)
    return names


def _scope(namespace: dict[str, Any]) -> dict[str, Any]:
    """The globals the rerun evaluates an annotation in: the module's, and the rerun's own names.

    ``all``, ``any``, ``sum`` and ``abs`` are lanky's in an annotation, as
    :func:`lanky.terms.evaluate_annotations` reads them, and lanky's at
    concrete values are Python's. An annotation that reads one of them in a
    module that binds it to anything but Python's builtin or lanky's own is
    refused while it is read (#100), so these are what the module means by
    them too.
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
    too (:func:`_both`).

    ``name := value`` binds the name where Python binds it, which a thunk
    would not: a thunk is a scope of its own, and ``:=`` in it would bind the
    name there alone. Python binds it in the nearest scope around it that is
    not a generator's, the annotation's globals or a lambda the annotation
    writes, and every thunk inside that scope reads it there. So it becomes
    ``__lanky_walrus__(lambda: name, "name", value)`` (:func:`_bind`): inside
    a lambda of the annotation's, ``lambda: name`` closes over the lambda's
    variable, whose cell is set, and the lambda's body is made to bind the
    name, in a branch never taken, so that the name is its variable as it is
    in Python; anywhere else the name is bound in the globals (#105).
    """

    def __init__(self, names: dict[str, str]) -> None:
        self.names = names
        #: The names ``:=`` binds in each lambda of the annotation's around
        #: the node visited, the innermost last.
        self.lambdas: list[dict[str, None]] = []

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Any:
        """``~operand`` as ``__lanky_not__(operand)``; any other operator as it is."""
        self.generic_visit(node)
        if not isinstance(node.op, ast.Invert):
            return node
        return ast.copy_location(_call("__lanky_not__", node.operand), node)

    def visit_BinOp(self, node: ast.BinOp) -> Any:
        """``&`` and ``|`` as calls on thunks, ``/``, ``//``, ``%``, ``**`` and ``<<`` as calls.

        ``left | right`` is ``__lanky_or__(lambda: left, lambda: right)``
        (:func:`_connective`), and ``left // right`` is
        ``__lanky_floordiv__(left, right)``, Python's ``//`` but for what
        :func:`_arithmetic` says; any other operator is as it is.
        """
        self.generic_visit(node)
        name = {ast.BitAnd: "__lanky_and__", ast.BitOr: "__lanky_or__"}.get(type(node.op))
        if name is not None:
            return ast.copy_location(_call(name, _thunk(node.left), _thunk(node.right)), node)
        name = _ARITHMETIC.get(type(node.op))
        if name is not None:
            return ast.copy_location(_call(name, node.left, node.right), node)
        return node

    def visit_Lambda(self, node: ast.Lambda) -> Any:
        """A lambda the annotation writes, a scope of its own for the ``:=`` in its body.

        Its defaults are evaluated in the scope around it, and are visited
        there. A name ``:=`` binds in its body is made its variable by a
        branch never taken, ``body if __lanky_live__ else ((name := None),)``,
        as the ``:=`` itself made it in Python, since the ``:=`` becomes a call
        (:meth:`visit_NamedExpr`). The thunks this rewrite makes are lambdas
        too, made after their contents are visited, so none is visited here.
        """
        node.args = self.visit(node.args)
        self.lambdas.append({})
        try:
            node.body = self.visit(node.body)
        finally:
            bound = self.lambdas.pop()
        if bound:
            never = ast.Tuple(
                [ast.NamedExpr(ast.Name(name, ast.Store()), ast.Constant(None)) for name in bound],
                ast.Load(),
            )
            node.body = ast.IfExp(ast.Name("__lanky_live__", ast.Load()), node.body, never)
        return node

    def visit_NamedExpr(self, node: ast.NamedExpr) -> Any:
        """``name := value`` as ``__lanky_walrus__(lambda: name, "name", value)`` (:func:`_bind`).

        Python binds the name in the nearest lambda of the annotation's around
        it, or in the annotation's globals, never in a generator's scope or a
        thunk's; ``lambda: name``, where the ``:=`` was, reads the name where
        Python binds it, and :func:`_bind` binds it there.
        """
        self.generic_visit(node)
        name = node.target.id
        if self.lambdas:
            self.lambdas[-1][name] = None
        variable = _thunk(ast.Name(name, ast.Load()))
        call = _call("__lanky_walrus__", variable, ast.Constant(name), node.value)
        return ast.copy_location(call, node)

    def visit_Call(self, node: ast.Call) -> Any:
        """A quantifier or a sum over a generator as the rerun reads it; any other call as it is."""
        self.generic_visit(node)
        kind = self.names.get(node.func.id) if isinstance(node.func, ast.Name) else None
        if kind is None or len(node.args) != 1 or node.keywords:
            return node
        (generator,) = node.args
        readable = ast.GeneratorExp if kind == "sum" else ast.GeneratorExp | ast.ListComp
        if not isinstance(generator, readable) or any(
            clause.is_async for clause in generator.generators
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


# {{{ the snapshot

#: How many items, the entries of dicts and the items of lists, sets, tuples
#: and object arrays, the snapshot of one claim copies (:func:`capture`). A
#: structure past that is not copied, and the claim's reading is declined.
COPY_ITEMS = 1 << 16

#: How many elements of numpy arrays the snapshot of one claim copies.
COPY_ELEMENTS = 1 << 20

#: The values that need no copy: they cannot change, or they are code, read
#: as they are. A class and a library's module are code, and so is a
#: function of a library, which reads its module as it is (see
#: :class:`_Copier`).
_UNCHANGING: tuple[type, ...] = (
    type(None),
    bool,
    numbers.Number,
    str,
    bytes,
    range,
    slice,
    type(Ellipsis),
    type(NotImplemented),
    types.CodeType,
    numpy.generic,
    numpy.dtype,
    numpy.ufunc,
    re.Pattern,
    enum.Enum,
    prim.ExpressionNode,
    LankyType,
    type,
    types.MethodDescriptorType,
    types.WrapperDescriptorType,
    types.ClassMethodDescriptorType,
    types.GetSetDescriptorType,
    types.MemberDescriptorType,
    property,
    staticmethod,
    classmethod,
)

#: Stands for an attribute a module or a class does not have.
_NO_ATTRIBUTE = object()

#: What Python and the standard decorators put in a class body, which holds
#: no state of the class's (see :meth:`_Copier.cls`).
_CLASS_BOOKKEEPING = frozenset(
    """
    __module__ __qualname__ __doc__ __dict__ __weakref__ __annotations__
    __annotate__ __slots__ __firstlineno__ __static_attributes__
    __orig_bases__ __parameters__ __type_params__ __match_args__
    __dataclass_fields__ __dataclass_params__ __abstractmethods__ _abc_impl
    """.split()
)


def _class_state(item: Any) -> bool:
    """Whether ``item``, from a class body, is state of the class: a method, or changing data."""
    if isinstance(item, staticmethod | classmethod):
        return True
    if isinstance(item, property):
        return True
    return isinstance(item, types.FunctionType) or not _unchanging(item)


#: The mappings copied entry by entry, each into a new one of its type.
_MAPPINGS = (dict, collections.OrderedDict, collections.Counter)

#: The type of a function :func:`functools.lru_cache` wraps.
_CACHED = type(functools.lru_cache(maxsize=None)(lambda: None))


def _unchanging(value: Any) -> bool:
    """Whether ``value`` needs no copy: a number, a text, a term, a lanky type, or code.

    lanky's own objects, ``Fin`` among them, a term built with sympy, and
    ``typing``'s are values too; a bare ``object()`` holds nothing.
    """
    if isinstance(value, _UNCHANGING) or type(value) is object:
        return True
    module = getattr(type(value), "__module__", "")
    if module == "typing" or module.split(".")[0] == "lanky":
        return True
    sympy = sys.modules.get("sympy")
    return sympy is not None and isinstance(value, sympy.Basic)


@functools.cache
def _library_directories() -> tuple[Path, ...]:
    """Where Python and the packages installed for it live: no module there is the user's."""
    directories = {sys.prefix, sys.base_prefix, sys.exec_prefix, sys.base_exec_prefix}
    paths = sysconfig.get_paths()
    directories.update(paths.get(key) for key in ("stdlib", "platstdlib", "purelib", "platlib"))
    try:
        directories.update(site.getsitepackages())
        directories.add(site.getusersitepackages())
    except AttributeError:  # pragma: no cover - a site module without them
        pass
    return tuple(Path(directory).resolve() for directory in directories if directory)


@functools.lru_cache(maxsize=1024)
def _users_file(file: str, roots: tuple[Path, ...]) -> bool:
    """Whether ``file`` lies under ``roots`` and not where Python or a package is installed."""
    path = Path(file).resolve()
    if any(path.is_relative_to(directory) for directory in _library_directories()):
        return False
    return any(path.is_relative_to(root) for root in roots)


@functools.lru_cache(maxsize=256)
def _roots(file: str) -> tuple[Path, ...]:
    """The source roots of the file a claim was compiled from, or none for one that is no file."""
    if not os.path.isfile(file):
        return ()
    from lanky.check import source_roots

    return source_roots(file)


def _users(globals_: dict[str, Any], roots: tuple[Path, ...]) -> bool:
    """Whether ``globals_`` are those of a module of the user's, copied with the claim's.

    That is a module whose file lies under the claim's source roots
    (:func:`lanky.check.source_roots`, the directories ``lanky check`` puts on
    ``sys.path``), a helper module beside the claim's file say, and not
    where Python or an installed package lives, nor lanky.
    """
    name, file = globals_.get("__name__"), globals_.get("__file__")
    if not roots or not isinstance(name, str) or not isinstance(file, str):
        return False
    return name.split(".")[0] != "lanky" and _users_file(file, roots)


@dataclass
class _World:
    """The copy of one module's globals: a module of its own, which its copied functions read."""

    source: dict[str, Any]
    module: types.ModuleType
    prefix: str
    reached: set[str] = field(default_factory=set)
    everything: bool = False

    @property
    def target(self) -> dict[str, Any]:
        """The copy of the globals: the copied functions' globals."""
        return self.module.__dict__


def _cache_entries(cache: Any) -> list[tuple[Any, Any]] | None:
    """The entries of a function behind ``functools.lru_cache``, as ``(key, result)``; or ``None``.

    The cache offers no way to read its entries, so they are read off what
    it holds, as the garbage collector lists it (:func:`gc.get_referents`):
    the dict that is the cache comes just before the function it wraps. One
    of unbounded size maps each key to its result, in the order they went
    in. One of bounded size maps each key to a link of its own, and the
    links are listed before the cache, oldest first, each as its key and its
    result, and the link's type where the version lists it. ``None`` where
    what is listed is not laid out so, which leaves the cache shared
    (:meth:`_Copier.cache`).
    """
    held = cache.cache_info().currsize
    listed = gc.get_referents(cache)
    # the function the cache calls: the one it wraps, or for a copy the check
    # made (:meth:`_Copier.cache`), the one that put its entries in
    function = getattr(cache, _CALLS, None) or getattr(cache, "__wrapped__", None)
    # the cache's own reference to its function is listed after any result
    at = max((k for k, item in enumerate(listed) if item is function), default=0)
    table = listed[at - 1] if at else None
    if type(table) is not dict or len(table) != held:
        return None
    if cache.cache_parameters()["maxsize"] is None:
        return list(table.items())
    start = 1 if listed and listed[0] is type(cache) else 0
    span = at - 1 - start
    if not held or span % held or span // held not in (2, 3):
        return None
    stride = span // held
    entries = [(listed[start + k * stride], listed[start + k * stride + 1]) for k in range(held)]
    if sorted(id(key) for key, _ in entries) != sorted(id(key) for key in table):
        return None
    # where the links' type is listed, it is listed after each result, which
    # tells a result from what else a version could list there
    if stride == 3 and any(
        listed[start + k * stride + 2] is not type(table[key]) for k, (key, _) in enumerate(entries)
    ):
        return None
    return entries


#: The attribute of a cache the check made again that holds the function it
#: calls, which is not the one it wraps (see :meth:`_Copier.cache`).
_CALLS = "_lanky_calls"


def _counted(cache: Any, info: Any) -> Any:
    """``cache``, made again by the check, counting its hits and misses on from ``info``'s.

    The copy counts the calls that put its entries in, and none before, while
    the original counts on from what it counted when the claim was read, which
    an annotation may read (``cache_info().misses``). So the copy's
    ``cache_info`` adds what the original had counted, and its
    ``cache_clear`` clears that too, as it clears the original's counts.
    """
    kind = type(cache)
    own = kind.cache_info(cache)
    offset = [info.hits - own.hits, info.misses - own.misses]

    def cache_info() -> Any:
        now = kind.cache_info(cache)
        return type(now)(now.hits + offset[0], now.misses + offset[1], now.maxsize, now.currsize)

    def cache_clear() -> None:
        kind.cache_clear(cache)
        offset[0] = offset[1] = 0

    # attributes of the object's own, which come before the methods of its type
    cache.cache_info = cache_info
    cache.cache_clear = cache_clear
    return cache


@functools.cache
def _cache_mark() -> Any:
    """What ``functools.lru_cache`` puts in a key between the positional and keyword arguments."""
    probe = functools.lru_cache(maxsize=None)(lambda **kwargs: None)
    probe(x=0)
    entries = _cache_entries(probe)
    if not entries or not isinstance(entries[0][0], tuple) or len(entries[0][0]) != 3:
        return None
    return entries[0][0][0]


def _cache_key(args: tuple[Any, ...], kwargs: dict[str, Any], typed: bool) -> Any:
    """The key ``functools.lru_cache`` keeps a call's result under, as CPython makes it."""
    if not typed and not kwargs:
        if len(args) == 1 and type(args[0]) in (int, str):
            return args[0]
        return args
    key = args
    if kwargs:
        key += (_cache_mark(), *itertools.chain.from_iterable(kwargs.items()))
    if typed:
        key += tuple(type(arg) for arg in (*args, *kwargs.values()))
    return key


def _cache_call(key: Any, typed: bool) -> tuple[tuple[Any, ...], dict[str, Any]] | None:
    """The call a cache's ``key`` was made of, its arguments and keywords; or ``None``.

    The key is read back as :func:`_cache_key` makes it, and made again from
    the call, which has to give the same key, item for item, by identity.
    """
    if not isinstance(key, tuple):
        call: tuple[tuple[Any, ...], dict[str, Any]] = ((key,), {})
    else:
        mark = _cache_mark()
        at = next((k for k, item in enumerate(key) if item is mark), None)
        if at is None:
            if typed and len(key) % 2:
                return None
            call = (key[: len(key) // 2] if typed else key, {})
        else:
            args, rest = key[:at], key[at + 1 :]
            if typed:
                if (len(rest) - len(args)) % 3:
                    return None
                rest = rest[: 2 * ((len(rest) - len(args)) // 3)]
            names = rest[0::2]
            if len(rest) % 2 or not all(type(name) is str for name in names):
                return None
            call = (args, dict(zip(names, rest[1::2], strict=True)))
    made = _cache_key(*call, typed)
    if made is key:
        return call
    if (
        type(made) is not tuple
        or type(key) is not tuple
        or len(made) != len(key)
        or any(new is not old for new, old in zip(made, key, strict=True))
    ):
        return None
    return call


class _Copier:
    """One copy of the part of the user's modules that a claim's annotations reach.

    ``copied`` says which modules' globals are copied, given the globals.
    When lanky reads a claim they are the claim's module and the user's
    modules beside it (:func:`capture`), and at a draw they are the copies
    taken then (:meth:`Snapshot.fresh`). ``kept`` are the objects left as they
    are when the claim was read, by ``id``, which a draw leaves as they are
    too.

    What is copied, and how:

    * the names of a copied module's globals that the annotations read, and
      that the functions of the module they call read, at any depth, each in
      a copy of that module's globals, a module of its own (:class:`_World`);
    * a function of a copied module is bound to the copy of its globals,
      closing over new cells, one for each cell of the function's, so that
      two functions that closed over one cell close over one copy of it, and
      with copies of its defaults and its attributes;
    * data: a dict, a list, a set, a tuple, a deque, a bytearray, a numpy
      array, item by item and nested, up to :data:`COPY_ITEMS` items and
      :data:`COPY_ELEMENTS` elements of arrays in all; one object reached
      twice is copied once, and a view of an array is made again over the
      copy of the array it views (:meth:`array`);
    * a ``functools.partial``, a function behind ``functools.lru_cache``
      with the entries its cache holds (:meth:`cache`), a method bound to a
      copied object (``TABLE.get``), and a library's function that closes
      over a function of the user's (a decorator's wrapper) are made again
      around the copies.

    Numbers, texts, terms, lanky's types, the modules, the classes and the
    functions of libraries need no copy (:func:`_unchanging`). A module of
    the user's is its copy, and code that reads a name off it,
    ``helpers.TABLE``, reads the copy of that name; where it is passed
    around as a value its every name is copied, as is every name of a
    module whose code calls ``globals``, ``vars``, ``eval`` or ``exec``.

    What is not copied is shared, with the reason, in :attr:`shared`:

    * an object of any other type, which may hold state the check does not
      know how to copy (an instance of a class of the user's, a random
      generator);
    * a structure past the budget;
    * a class of the user's that holds a method or data (:meth:`cls`), whose
      instances and methods read it, and their module, as they are;
    * a value read off a class or a library's module by name that would
      need a copy, ``Rules.table``, since the check copies neither;
    * a function behind ``functools.lru_cache`` whose entries cannot be
      read off its cache, which answer as the function might no longer, and
      a view the copy cannot make again;
    * a module of the user's that a function imports as it runs
      (:meth:`imported`), which binds the module and not its copy.
    """

    def __init__(
        self, copied: Callable[[dict[str, Any]], bool], kept: frozenset[int] = frozenset()
    ) -> None:
        self.copied = copied
        self.kept = set(kept)
        self.worlds: dict[int, _World] = {}
        self.memo: dict[int, Any] = {}
        # the originals the memo is keyed by, kept alive so that no other
        # object takes an id of theirs while the copy is made
        self.originals: list[Any] = []
        self.left: list[Any] = []
        self.items = 0
        self.elements = 0
        self.shared: list[str] = []
        #: The code of the functions of the user's that the copy made again.
        self.codes: set[Any] = set()

    # {{{ modules and names

    def world(self, globals_: Any, prefix: str | None = None) -> _World | None:
        """The copy of the module whose globals are ``globals_``, if it is copied."""
        if not isinstance(globals_, dict):
            return None
        key = id(globals_)
        if key in self.worlds:
            return self.worlds[key]
        if not self.copied(globals_):
            return None
        name = globals_.get("__name__")
        name = name if isinstance(name, str) else "module"
        module = types.ModuleType(name)
        module.__dict__.update(globals_)
        world = _World(globals_, module, f"{name}." if prefix is None else prefix)
        self.worlds[key] = world
        self.originals.append(globals_)
        return world

    def reach(self, code: Any, world: _World, skip: frozenset[str] = frozenset()) -> None:
        """Copy into ``world`` each name of it that ``code`` reads, and what they reach."""
        reads = code_reads(code)
        if reads.dynamic:
            self.everything(world)
        chained = {chain[0] for chain in reads.chains}
        for name in reads.names:
            if name not in skip:
                self.name(world, name, bare=name in reads.bare or name not in chained)
        for root, *attributes in reads.chains:
            if root not in skip and root in world.source:
                self.chain(world.source[root], attributes, world.prefix + root)
        for name in reads.imports:
            self.imported(world, name)

    def imported(self, world: _World, name: str) -> None:
        """Share a module of the user's that code imports where it runs: the import is not copied.

        ``import helpers`` in a helper's body binds the module as it is in
        ``sys.modules`` when the rerun runs it, never the copy, so what it
        reads there is read as it is now. ``name`` is what the code imports,
        and is looked up as a module and as one of the module's package.
        """
        package = world.source.get("__package__")
        candidates = [name.lstrip(".")]
        if isinstance(package, str) and package:
            candidates.append(f"{package}.{name.lstrip('.')}")
        for candidate in candidates:
            module = sys.modules.get(candidate)
            if isinstance(module, types.ModuleType) and self.world(module.__dict__) is not None:
                if id(module) not in self.kept:
                    self.share(
                        module,
                        f"{world.prefix}{name}",
                        "a module of the user's that a function imports as it runs, "
                        "which reads the module as it is",
                    )

    def name(self, world: _World, name: str, bare: bool = True) -> None:
        """Copy one name of ``world``'s module, if it has it."""
        if name not in world.source:
            return
        value = world.source[name]
        if name in world.reached:
            if bare and isinstance(value, types.ModuleType):
                self.module(value, bare=True)
            return
        world.reached.add(name)
        world.target[name] = self.copy(value, world.prefix + name, bare=bare)

    def everything(self, world: _World) -> None:
        """Copy every name of ``world``'s module: code reads them by names it does not spell."""
        if world.everything:
            return
        world.everything = True
        for name in list(world.source):
            if not (name.startswith("__") and name.endswith("__")):
                self.name(world, name)

    def module(self, value: types.ModuleType, bare: bool) -> Any:
        """A module as the copy has it: its copy, if it is one of the user's."""
        world = self.world(value.__dict__)
        if world is None:
            return value
        if bare:
            self.everything(world)
        return world.module

    def chain(self, value: Any, attributes: Sequence[str], path: str) -> None:
        """Follow what code reads off a module or a class by name, ``helpers.TABLE`` say.

        What is read off a module of the user's is copied there. A library's
        module and a class are not copied, so what is read off one has to
        need no copy, and anything else is shared (:meth:`share`).
        """
        for attribute in attributes:
            if isinstance(value, types.ModuleType):
                world = self.world(value.__dict__)
                if world is not None:
                    if attribute not in world.source:
                        return
                    self.name(world, attribute, bare=False)
                    value, path = world.source[attribute], f"{path}.{attribute}"
                    continue
                held = value.__dict__.get(attribute, _NO_ATTRIBUTE)
                holder = f"the module {value.__name__}, which the check does not copy"
            elif isinstance(value, type):
                held = inspect.getattr_static(value, attribute, _NO_ATTRIBUTE)
                holder = f"the class {value.__qualname__}, and the check copies no class"
            else:
                return
            if held is _NO_ATTRIBUTE:
                return
            if isinstance(held, staticmethod | classmethod):
                held = held.__func__
            path = f"{path}.{attribute}"
            if isinstance(held, types.ModuleType | type):
                value = held
                continue
            if self.copy(held, path) is not held:
                self.share(held, path, f"read off {holder}")
            return

    # }}}

    # {{{ values

    def copy(self, value: Any, path: str, bare: bool = True) -> Any:
        """``value`` as the copy has it: copied, made again around copies, or as it is.

        ``path`` names it in a reason, ``bare`` says whether a module is
        passed around as a value rather than read names off.
        """
        if isinstance(value, types.ModuleType):
            return self.module(value, bare)
        if isinstance(value, type):
            return self.cls(value, path)
        if _unchanging(value):
            return value
        key = id(value)
        if key in self.memo:
            return self.memo[key]
        if key in self.kept:
            return value
        try:
            return self._copy(value, path)
        except Exception as exc:  # noqa: BLE001 - what cannot be copied is shared, saying why
            why = f"which could not be copied ({type(exc).__name__}: {exc})"
            return self.share(value, path, why)

    def cls(self, value: type, path: str) -> type:
        """A class as the copy has it: itself, shared where it is the user's and holds state.

        A class is not copied. Its instances read its attributes, and its
        methods read their module's globals, as they are when they are
        called, not as the copy has them; so a class of the user's whose
        body holds a method or anything but a number, a text or a term
        (:func:`_unchanging`) is shared, with what it holds named. One with
        none, an exception or a marker, is read as it is, and so is a
        library's class.
        """
        if id(value) in self.memo:
            return value
        self.remember(value, value)
        for klass in value.__mro__:
            if not self.users_class(klass):
                continue
            held = [
                name
                for name, item in vars(klass).items()
                if name not in _CLASS_BOOKKEEPING and _class_state(item)
            ]
            if held:
                what = f"{len(held)} attributes" if len(held) > 1 else held[0]
                self.share(
                    value,
                    path,
                    f"a class of the user's that holds {what}, which the check does not copy, "
                    "and its instances and methods read as they are",
                )
                break
        return value

    def users_class(self, klass: type) -> bool:
        """Whether ``klass`` was defined in a copied module, the claim's or one beside it."""
        name = getattr(klass, "__module__", None)
        if not isinstance(name, str):
            return False
        if any(world.source.get("__name__") == name for world in self.worlds.values()):
            return True
        module = sys.modules.get(name)
        return isinstance(module, types.ModuleType) and self.world(module.__dict__) is not None

    def remember(self, original: Any, copy: Any) -> Any:
        """Record ``copy`` as the copy of ``original``, and return it."""
        self.memo[id(original)] = copy
        self.originals.append(original)
        return copy

    def share(self, value: Any, path: str, why: str) -> Any:
        """Leave ``value`` as it is, and say why it is not copied."""
        self.memo[id(value)] = value
        self.kept.add(id(value))
        self.left.append(value)
        self.shared.append(f"{path}, {why}")
        return value

    def spend(self, value: Any, path: str, items: int = 0, elements: int = 0) -> bool:
        """Count ``value``'s items and elements against the budget; share it past it."""
        if self.items + items > COPY_ITEMS:
            what = f"a {type(value).__name__} of {items} items"
            self.share(value, path, f"{what}, past the {COPY_ITEMS} the check copies")
            return False
        if self.elements + elements > COPY_ELEMENTS:
            what = f"an array of {elements} elements"
            self.share(value, path, f"{what}, past the {COPY_ELEMENTS} the check copies")
            return False
        self.items += items
        self.elements += elements
        return True

    def _copy(self, value: Any, path: str) -> Any:
        """A copy of ``value``, which is neither unchanging nor copied yet (see :meth:`copy`)."""
        kind = type(value)
        inner = f"{path}[...]"
        if isinstance(value, types.FunctionType):
            return self.function(value, path)
        if kind in _MAPPINGS or kind is collections.defaultdict:
            if not self.spend(value, path, items=len(value)):
                return value
            out = self.remember(value, kind())
            if kind is collections.defaultdict:
                out.default_factory = self.copy(value.default_factory, f"{path}.default_factory")
            for key, item in value.items():
                out[self.copy(key, inner)] = self.copy(item, inner)
            return out
        if kind in (list, set, collections.deque, bytearray):
            if not self.spend(value, path, items=len(value)):
                return value
            if kind is bytearray:
                return self.remember(value, bytearray(value))
            if kind is collections.deque:
                out = self.remember(value, collections.deque(maxlen=value.maxlen))
            else:
                out = self.remember(value, kind())
            (out.update if kind is set else out.extend)(self.copy(item, inner) for item in value)
            return out
        if isinstance(value, tuple | frozenset):
            if not self.spend(value, path, items=len(value)):
                return value
            items = [self.copy(item, inner) for item in value]
            if all(new is old for new, old in zip(items, value, strict=True)):
                return self.remember(value, value)
            if kind is tuple or kind is frozenset:
                return self.remember(value, kind(items))
            if isinstance(value, tuple) and hasattr(kind, "_make"):
                return self.remember(value, kind._make(items))
            return self.share(value, path, f"a {kind.__qualname__} that holds what needs a copy")
        if isinstance(value, numpy.ndarray):
            return self.array(value, path)
        if isinstance(value, functools.partial) and kind is functools.partial:
            out = functools.partial(
                self.copy(value.func, f"{path}.func"),
                *self.copy(value.args, f"{path}.args"),
                **self.copy(value.keywords, f"{path}.keywords"),
            )
            return self.remember(value, out)
        if isinstance(value, _CACHED):
            wrapped = self.copy(value.__wrapped__, path)
            if wrapped is value.__wrapped__:
                return value
            return self.cache(value, wrapped, path)
        if isinstance(value, types.MethodType):
            owner = self.copy(value.__self__, path)
            function = self.copy(value.__func__, path)
            if owner is value.__self__ and function is value.__func__:
                return value
            return self.remember(value, types.MethodType(function, owner))
        if isinstance(value, types.BuiltinMethodType | types.MethodWrapperType):
            owner = getattr(value, "__self__", None)
            if owner is None or isinstance(owner, types.ModuleType | type):
                return value
            copied = self.copy(owner, path)
            if copied is owner:
                return value
            return self.remember(value, getattr(copied, value.__name__))
        return self.share(
            value,
            path,
            f"an object of type {kind.__qualname__}, whose state the check does not copy",
        )

    def cache(self, value: Any, wrapped: Any, path: str) -> Any:
        """A function behind ``functools.lru_cache`` made again around ``wrapped``, entries and all.

        A cache is state: an entry answers where the function, run again on
        the copy, may answer otherwise, from what the module holds now. So
        the copy is a cache of the same size around the copy of the function,
        holding the same entries, their results copied, in the order in which
        the cache would evict them: a call they answer is answered from them,
        as Python answers it, and any other runs the copy of the function
        (#105). An entry is put in by calling the new cache as the original
        was called, the arguments read back off the entry's key
        (:func:`_cache_call`), and the call answered with the copy of its
        result. Where the entries cannot be read off the cache
        (:func:`_cache_entries`), or a key cannot be read back into a call,
        the cache is shared, and the reading declined, naming it. The copy
        counts its hits and misses on from the original's (:func:`_counted`),
        and holds copies of what was set on the original after it was made
        (:meth:`cache_attributes`).
        """
        info = value.cache_info()
        held = info.currsize
        parameters = value.cache_parameters()
        if not held:
            out = self.remember(value, functools.lru_cache(**parameters)(wrapped))
            self.cache_attributes(value, out, path)
            return _counted(out, info)
        entries = _cache_entries(value)
        calls = [] if entries is not None else None
        for key, result in entries or ():
            call = _cache_call(key, parameters["typed"])
            if call is None:
                calls = None
                break
            calls.append((call, result))
        if calls is None:
            return self.share(
                value,
                path,
                f"a function behind functools.lru_cache whose cache holds {held} entries, "
                "which the check could not read",
            )
        answers: list[Any] = []

        def answer(*args: Any, **kwargs: Any) -> Any:
            return answers.pop() if answers else wrapped(*args, **kwargs)

        out = self.remember(value, functools.lru_cache(**parameters)(answer))
        functools.update_wrapper(out, wrapped)
        self.cache_attributes(value, out, path)
        setattr(out, _CALLS, answer)
        for (args, kwargs), result in calls:
            # the rerun calls the copy with copies of what the original was
            # called with, a function of the user's say, so its keys are made
            # of the copies
            where = f"an entry of the cache of {path}"
            args = self.copy(args, where)
            kwargs = {name: self.copy(item, where) for name, item in kwargs.items()}
            answers.append(self.copy(result, where))
            out(*args, **kwargs)
        if answers or out.cache_info().currsize != held:
            raise RuntimeError("the entries of the cache did not go in as they were")
        return _counted(out, info)

    def cache_attributes(self, value: Any, out: Any, path: str) -> None:
        """Give ``out``, made again from the cache ``value``, copies of what was set on ``value``.

        ``functools.update_wrapper`` gives a cache made around the copy of a
        function that function's name, text and attributes, and not what was
        set on the original cache after it was made, ``cached.flag = 1``,
        which an annotation may read, and which the rerun had no value for.
        What the check sets on a cache it makes (:data:`_CALLS`, the counts of
        :func:`_counted`) is its own, and not copied from a copy.
        """
        own = {"__wrapped__", _CALLS, "cache_info", "cache_clear", *functools.WRAPPER_ASSIGNMENTS}
        for name, item in vars(value).items():
            if name not in own:
                setattr(out, name, self.copy(item, f"{path}.{name}"))

    def array(self, value: numpy.ndarray, path: str) -> Any:
        """A numpy array as the copy has it: copied, a view made again over the copy it views.

        Two views of one array, or a view and the array, share their memory,
        so a helper that writes through one reads the write through the
        other. Each is therefore made over one copy of the array that owns
        the memory, at the same offset and with the same strides, rather
        than copied apart. A view of an array of objects, or of one that is
        not laid out in C order, is shared.
        """
        base = value
        while isinstance(base.base, numpy.ndarray):
            base = base.base
        if base is value:
            objects = value.dtype == object
            if not self.spend(value, path, items=value.size if objects else 0, elements=value.size):
                return value
            if not objects:
                return self.remember(value, value.copy())
            out = self.remember(value, numpy.empty_like(value))
            for index, item in numpy.ndenumerate(value):
                out[index] = self.copy(item, f"{path}[...]")
            return out
        if (
            value.dtype == object
            or base.dtype == object
            or type(value) is not numpy.ndarray
            or not base.flags.c_contiguous
        ):
            return self.share(
                value, path, "a view of another array, which the check cannot make again"
            )
        copied = self.copy(base, f"the array {path} views")
        if copied is base:
            return self.share(value, path, "a view of an array the check does not copy")
        offset = value.__array_interface__["data"][0] - base.__array_interface__["data"][0]
        view = numpy.ndarray(
            value.shape, value.dtype, buffer=copied, offset=offset, strides=value.strides
        )
        if not value.flags.writeable:
            view.flags.writeable = False
        return self.remember(value, view)

    def function(self, value: types.FunctionType, path: str) -> Any:
        """A function as the copy has it.

        One of a copied module is bound to the copy of its globals, and what
        it reads is copied there. A library's function reads its module as
        it is, and is made again only where it closes over a function of the
        user's, as a decorator's wrapper does, so that it calls the copy.
        """
        world = self.world(value.__globals__)
        closure = value.__closure__ or ()
        if world is None and not any(self._closes_over_ours(cell) for cell in closure):
            return value
        code = value.__code__
        cells: list[Any] = []
        pending: list[tuple[str, Any, Any]] = []
        for variable, cell in zip(code.co_freevars, closure, strict=True):
            if id(cell) in self.memo:
                cells.append(self.memo[id(cell)])
                continue
            new = self.remember(cell, types.CellType())
            cells.append(new)
            pending.append((variable, cell, new))
        globals_ = world.target if world is not None else value.__globals__
        if world is not None:
            self.codes.add(code)
        out = types.FunctionType(code, globals_, value.__name__, None, tuple(cells) or None)
        self.remember(value, out)
        out.__qualname__ = value.__qualname__
        out.__module__ = value.__module__
        out.__doc__ = value.__doc__
        try:
            out.__annotations__ = value.__annotations__
        except Exception:  # noqa: BLE001 - annotations that do not evaluate are left out
            pass
        out.__defaults__ = self.copy(value.__defaults__, f"a default of {value.__qualname__}")
        out.__kwdefaults__ = self.copy(value.__kwdefaults__, f"a default of {value.__qualname__}")
        out.__dict__.update(self.copy(value.__dict__, f"an attribute of {value.__qualname__}"))
        reads = code_reads(code)
        chained = {chain[0] for chain in reads.free_chains}
        for variable, cell, new in pending:
            try:
                contents = cell.cell_contents
            except ValueError:  # an empty cell stays empty
                continue
            bare = variable in reads.free_bare or variable not in chained
            new.cell_contents = self.copy(
                contents, f"{variable}, which {value.__qualname__} closes over", bare=bare
            )
        for variable, *attributes in reads.free_chains:
            if variable in code.co_freevars:
                cell = closure[code.co_freevars.index(variable)]
                try:
                    contents = cell.cell_contents
                except ValueError:
                    continue
                self.chain(contents, attributes, variable)
        if world is not None:
            self.reach(code, world)
        return out

    def _closes_over_ours(self, cell: Any) -> bool:
        """Whether ``cell`` holds a function of a copied module."""
        try:
            contents = cell.cell_contents
        except ValueError:
            return False
        return (
            isinstance(contents, types.FunctionType)
            and self.world(contents.__globals__) is not None
        )

    # }}}


@dataclass(frozen=True, eq=False)
class Snapshot:
    """The user's modules as a claim's annotations reach them, copied when lanky read the claim.

    lanky reads a claim when its module runs the decorator, and the
    faithfulness check runs the annotations again later, when the module has
    run to its end: a module that rebinds a name, ``K = 1`` after ``K = 0``,
    or changes a table in place, ``TABLE.clear()``, would have the rerun read
    something else than the reading read, and a misreading could hide there
    (#102). So what the annotations reach, through the functions they call,
    the names those read and what they close over, is copied when the claim
    is read (:func:`capture`, :class:`_Copier`), and every draw runs in a
    copy of that copy (:meth:`fresh`), so that a draw starts where the
    reading started, whatever a helper changed at the draw before (#103).

    Attributes:
        namespace: The claim's module's globals, a copy, with what the
            annotations reach copied and its functions bound to it.
        shared: What the annotations reach that is not copied, each with the
            reason. A reading that reaches any of it is not tested: the rerun
            reads it as it is, not as it was when the claim was read.
        codes: The annotations, compiled, whose reads the copy follows.
        watched: The code of the functions of the user's that the copy
            makes again, which a draw that runs past its time stops
            (:func:`_watching`).
        roots: The source roots of the claim's file: the functions of the
            modules under them are the user's too, which a draw that runs
            past its time stops (:func:`_watching`).
    """

    namespace: dict[str, Any]
    shared: tuple[str, ...] = ()
    codes: tuple[Any, ...] = ()
    watched: frozenset[Any] = frozenset()
    roots: tuple[Path, ...] = ()
    skip: frozenset[str] = frozenset()
    worlds: frozenset[int] = frozenset()
    kept: frozenset[int] = frozenset()
    held: tuple[Any, ...] = ()

    def fresh(self) -> dict[str, Any]:
        """A copy for one draw: the module's globals, with what is reached copied again."""
        return self.fresh_copy()[0]

    def fresh_copy(self) -> tuple[dict[str, Any], tuple[str, ...]]:
        """A copy for one draw, as :meth:`fresh` makes it, and what it could not copy again.

        What the snapshot shared is shared again, and is not listed: it is in
        :attr:`shared`. Anything else the copy for the draw has to share is
        something the snapshot holds as it was and the copy cannot make
        again, and the draw would read it as it is, so it is listed.
        """
        copier = _Copier(lambda globals_: id(globals_) in self.worlds, self.kept)
        world = copier.world(self.namespace, "")
        if world is None:
            return dict(self.namespace), ()
        for code in self.codes:
            copier.reach(code, world, self.skip)
        return world.target, tuple(dict.fromkeys(copier.shared))


def _annotation_codes(fn: Any) -> tuple[Any, ...]:
    """The annotations of ``fn`` that are sources, compiled as lanky compiles them to read them."""
    try:
        raw = inspect.get_annotations(fn, eval_str=False)
    except Exception:  # noqa: BLE001 - the reading says what is wrong with them
        return ()
    codes = []
    for annotation in raw.values():
        if isinstance(annotation, str):
            try:
                codes.append(compile(annotation.lstrip(" \t"), "<string>", "eval"))
            except (SyntaxError, ValueError):
                continue
    return tuple(codes)


def capture(fn: Any) -> Snapshot:
    """The :class:`Snapshot` of what ``fn``'s annotations reach, as it is now.

    :class:`lanky.theory.Theorem` takes it before it reads the claim. The
    copy is of the claim's module and of the user's modules beside it
    (:func:`_users`), and what cannot be copied is listed with the reason.
    Nothing here raises: a snapshot that could not be taken lists why.
    """
    live = getattr(fn, "__globals__", None)
    if not isinstance(live, dict):
        return Snapshot({})
    try:
        code = getattr(fn, "__code__", None)
        roots = _roots(code.co_filename) if code is not None else ()
        copier = _Copier(lambda globals_: globals_ is live or _users(globals_, roots))
        world = copier.world(live, "")
        assert world is not None
        codes = _annotation_codes(fn)
        skip = frozenset(inspect.signature(fn).parameters)
        for annotation in codes:
            copier.reach(annotation, world, skip)
    except Exception as exc:  # noqa: BLE001 - a snapshot that could not be taken says why
        return Snapshot(
            dict(live),
            shared=(f"the module, which could not be copied ({type(exc).__name__}: {exc})",),
        )
    worlds = tuple(copier.worlds.values())
    return Snapshot(
        world.target,
        shared=tuple(dict.fromkeys(copier.shared)),
        codes=codes,
        skip=skip,
        worlds=frozenset(id(each.target) for each in worlds),
        kept=frozenset(copier.kept),
        held=(*(each.module for each in worlds), *copier.left),
        watched=frozenset(copier.codes),
        roots=roots,
    )


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

    def rec(self, expr: Any, *args: Any, **kwargs: Any) -> Any:
        """Evaluate ``expr``, giving the draw up past its time (:func:`_on_time`)."""
        # _on_time, written out: this runs at every node
        deadline = _DEADLINE.get()
        if deadline is not None and time.monotonic() > deadline:
            _on_time()
        return LankyEvaluationMapper.rec(self, expr, *args, **kwargs)

    __call__ = rec

    def map_quotient(self, expr: prim.Quotient) -> Any:
        """True division, as the rerun's ``/`` divides (:func:`_arithmetic`)."""
        return _TRUEDIV(self.rec(expr.numerator), self.rec(expr.denominator))

    def map_floor_div(self, expr: prim.FloorDiv) -> Any:
        """Floor division, as the rerun's ``//`` divides (:func:`_arithmetic`)."""
        return _FLOORDIV(self.rec(expr.numerator), self.rec(expr.denominator))

    def map_remainder(self, expr: prim.Remainder) -> Any:
        """The remainder, as the rerun's ``%`` takes it (:func:`_arithmetic`)."""
        return _MOD(self.rec(expr.numerator), self.rec(expr.denominator))

    def map_power(self, expr: prim.Power) -> Any:
        """A power, as the rerun's ``**`` takes it (:func:`_arithmetic`)."""
        return _POW(self.rec(expr.base), self.rec(expr.exponent))

    def map_left_shift(self, expr: prim.LeftShift) -> Any:
        """A left shift, as the rerun's ``<<`` takes it (:func:`_arithmetic`)."""
        return _LSHIFT(self.rec(expr.shiftee), self.rec(expr.shift))

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

    def __call__(self, *points: Any) -> Any:
        """The value at ``points``: ``f(i)``, or ``f(i, j)`` for ``f(i)(j)``."""
        return apply_at(self._at, points, self.name)

    def __getitem__(self, point: Any) -> Any:
        """The same as a call: ``f[i]``, or ``f[i, j]`` for ``f[i][j]``."""
        return apply_at(self._at, point if isinstance(point, tuple) else (point,), self.name)

    def _at(self, point: Any) -> Any:
        """The value at ``point``, drawn the first time it is asked for.

        Outside the domain it has none, and inside
        :func:`lanky.terms.totalized` it is what a table's is there
        (:func:`lanky.testing.totalized_value`).
        """
        if (
            _is_truth(point)
            or not isinstance(point, numbers.Number)
            or not in_sort(point, self.domain, self.context)
        ):
            if is_totalized():
                return totalized_value(self.codomain)
            raise Undecided(
                f"{self.name} is applied at {point!r}, which is outside the domain "
                f"{self.domain} it declares, so this draw decides nothing"
            )
        if point not in self.values:
            self.values[point] = _draw(self.codomain, self.source, self.context, size=self.size)
        return self.values[point]

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
                codomain=codomain,
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


def _extent(theorem: Any, codes: Sequence[Any], namespace: dict[str, Any]) -> _Extent:
    """What the claim's draws take besides the corners (see :class:`_Extent`).

    ``namespace`` is the module's globals as the claim was read
    (:attr:`Snapshot.namespace`), where the integers it writes are read.

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
    return _Extent(_written(codes, namespace), frozenset(sizes), largest)


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


#: The ids :mod:`sys.monitoring` names no tool for, one of which the check
#: takes while it runs a claim's draws (:func:`_watching`).
_TOOL_IDS = (3, 4)

#: Where lanky's own code lives, which is never the user's, whatever the
#: claim's source roots hold (:func:`_users_code`).
_LANKY = Path(__file__).resolve().parent


@functools.lru_cache(maxsize=4096)
def _users_code(file: str, roots: tuple[Path, ...]) -> bool:
    """Whether code compiled from ``file`` is the user's, which a draw past its time stops.

    That is code from a file under the claim's source roots, as for the
    snapshot (:func:`_users`), and not where Python, a package or lanky
    lives; code compiled from no file, ``<string>``, is no one's in
    particular.
    """
    if not roots or file.startswith("<"):
        return False
    return not Path(file).resolve().is_relative_to(_LANKY) and _users_file(file, roots)


def _users_codes(roots: tuple[Path, ...], namespace: dict[str, Any] | None = None) -> list[Any]:
    """The code of the functions the user's modules hold now, their methods included.

    A module is the user's where its file is (:func:`_users_code`), and the
    claim's own module, whose globals are ``namespace``, is one, though
    ``lanky check`` takes it out of ``sys.modules`` once it has run. Their
    globals are read for functions, for their classes and those of their
    objects, for what wraps a function (a ``functools.partial``, a cache, a
    bound method, a decorator's wrapper), and for what a function closes
    over, at any depth, and the code of each function compiled from a file
    of the user's is kept: a method of a class of the user's, which the
    snapshot shares, and a function of a module the snapshot does not copy,
    which a helper imports as it runs, among them (see :func:`_watching`).
    What a library defines is not.
    """
    if not roots:
        return []
    # a module of a subclass, a lazy one say, is no module of the user's,
    # and reading its attributes could load it
    modules = {
        name: module.__dict__
        for name, module in list(sys.modules.items())
        if type(module) is types.ModuleType
        and isinstance(module.__dict__.get("__file__"), str)
        and _users_code(module.__dict__["__file__"], roots)
    }
    if namespace is not None and isinstance(namespace.get("__name__"), str):
        modules.setdefault(namespace["__name__"], namespace)
    files: dict[str, bool] = {}
    found: list[Any] = []
    seen: set[int] = set()
    pending: list[Any] = [value for globals_ in modules.values() for value in globals_.values()]
    while pending:
        value = pending.pop()
        if id(value) in seen:
            continue
        seen.add(id(value))
        if isinstance(value, types.FunctionType):
            code = value.__code__
            if code.co_filename not in files:
                files[code.co_filename] = _users_code(code.co_filename, roots)
            if files[code.co_filename]:
                found.append(code)
            for cell in value.__closure__ or ():
                try:
                    pending.append(cell.cell_contents)
                except ValueError:  # an empty cell
                    continue
            pending.extend(value.__dict__.values())
        elif isinstance(value, type):
            name = getattr(value, "__module__", None)
            if isinstance(name, str) and name in modules:
                pending.extend(vars(value).values())
        elif isinstance(value, staticmethod | classmethod | types.MethodType):
            pending.append(value.__func__)
        elif isinstance(value, property):
            pending.extend((value.fget, value.fset, value.fdel))
        elif isinstance(value, functools.partial):
            pending.append(value.func)
        elif isinstance(value, _CACHED):
            pending.append(value.__wrapped__)
        elif not isinstance(value, types.ModuleType) and not _unchanging(value):
            # an object: its class's methods are what it runs
            pending.append(type(value))
    return found


def _nested_codes(code: Any) -> Iterator[Any]:
    """``code`` and the code compiled inside it, its lambdas and generators."""
    yield code
    for constant in code.co_consts:
        if isinstance(constant, types.CodeType):
            yield from _nested_codes(constant)


def _late(code: Any, offset: int, *rest: Any) -> None:
    """At a call or a turn of a loop in the user's code, give the draw up past its time."""
    # _on_time, written out: this runs at every turn of the user's loops
    deadline = _DEADLINE.get()
    if deadline is not None and time.monotonic() > deadline:
        _on_time()


@contextmanager
def _watching(
    codes: Iterable[Any], roots: tuple[Path, ...] = (), namespace: dict[str, Any] | None = None
) -> Iterator[None]:
    """Stop the user's code at a draw that runs past its time, while the block runs (#101).

    The walks and the term's reading ask for the time themselves
    (:func:`_on_time`); a helper's own loop, or a helper that calls itself,
    does not. So the user's code is watched with :mod:`sys.monitoring` at
    every call and every turn of a loop (``PY_START`` and ``JUMP``), under an
    id it names no tool for, and past :data:`DRAW_SECONDS` the next of these
    gives the draw up. The user's code is ``codes``, the annotations and the
    helpers the snapshot copied, and the functions of the user's modules,
    those whose files lie under the claim's source ``roots`` and the claim's
    own, whose globals are ``namespace``, their methods included
    (:func:`_users_codes`), with the code compiled inside each. The
    events are switched on for that code alone, and off again when the
    block ends. Where every such id is taken, nothing is watched, and a
    helper that loops forever at a draw stops the check there.

    What Python runs in one step, a builtin's or a library's loop in C, or
    ``2 ** 2 ** n`` in a helper, is not stopped, nor is a library's code, nor
    a function no module of the user's holds when the draws start; the
    annotation's own powers and its term's are kept small
    (:func:`_computable`).
    """
    monitoring = sys.monitoring
    tool = None
    for candidate in _TOOL_IDS:
        if monitoring.get_tool(candidate) is not None:
            continue
        try:
            monitoring.use_tool_id(candidate, "lanky faithful")
        except ValueError:  # pragma: no cover - taken since it was asked
            continue
        tool = candidate
        break
    if tool is None:
        yield
        return
    events = monitoring.events.PY_START | monitoring.events.JUMP
    watched: dict[int, Any] = {}
    try:
        monitoring.register_callback(tool, monitoring.events.PY_START, _late)
        monitoring.register_callback(tool, monitoring.events.JUMP, _late)
        try:
            users = _users_codes(roots, namespace)
        except Exception:  # noqa: BLE001 - what cannot be read is not watched
            users = []
        for each in (*codes, *users):
            for code in _nested_codes(each):
                # by id: hashing a code object reads all of it
                if id(code) in watched:
                    continue
                try:
                    monitoring.set_local_events(tool, code, events)
                except (TypeError, ValueError):  # pragma: no cover - code it cannot watch
                    continue
                watched[id(code)] = code
        yield
    finally:
        for code in watched.values():
            monitoring.set_local_events(tool, code, 0)
        monitoring.register_callback(tool, monitoring.events.PY_START, None)
        monitoring.register_callback(tool, monitoring.events.JUMP, None)
        monitoring.free_tool_id(tool)


def _compare(
    namespace: dict[str, Any],
    parameters: Sequence[str],
    annotations: Sequence[_Annotation],
    draw: _Draw,
    total: bool = False,
    deadline: float | None = None,
) -> Iterator[tuple[_Annotation, str, _Outcome, _Outcome]]:
    """Each annotation, how its two readings compare at ``draw``, and the two outcomes.

    ``namespace`` is the function's globals as they were when lanky read the
    annotations, what they reach copied for this draw and its helpers bound
    to it (:meth:`Snapshot.fresh`), and the rerun runs in it
    (:func:`_scope`). With ``total`` both readings read what Python has no
    value for as Lean has it (:func:`lanky.terms.totalized`), and a sum with
    no value is not compared point by point: a helper's operation is
    Python's in the rerun and Lean's in the term, so the two may have
    values at other points, and only where both have a value do they say
    the same if the term is faithful.

    The readings of all the annotations at the draw may run until
    ``deadline``, :data:`DRAW_SECONDS` from now unless the draw has one
    already (:func:`_run`). Where they run longer, or walk more than
    :data:`WALK_POINTS` points, the draw is given up: the annotation is
    yielded with the verdict ``slow`` or ``unwalked``, and none after it.
    """
    scope = _scope(namespace)
    for name in parameters:
        scope[name] = draw.context[name] if name in draw.context else Var(name)
    scope["__lanky_walrus__"] = functools.partial(_bind, scope)
    if deadline is None:
        deadline = time.monotonic() + DRAW_SECONDS
    for annotation in annotations:
        unsummed: list[list[tuple[str, Any]]] = []
        scope["__lanky_sum__"] = functools.partial(_add, unsummed)
        reading = _Reading(dict(draw.context), draw.samples)
        try:
            python, term = _both_readings(
                annotation, scope, reading, draw, unsummed, deadline, total
            )
        except _GivenUp as exc:
            yield annotation, exc.verdict, _Outcome(error=exc), _Outcome(error=exc)
            return
        if not total and not _same_points(unsummed, reading.unsummed):
            # a sum had no value on both sides, or on one, and its points differ
            python = replace(python, sums=_points_of(unsummed))
            term = replace(term, sums=_points_of(reading.unsummed))
            yield annotation, "differed", python, term
            continue
        yield annotation, _judge(python, term), python, term


@contextmanager
def _reading(draw: _Draw, deadline: float, total: bool) -> Iterator[None]:
    """One reading at ``draw``: its walk's budget, the draw's time, and, with ``total``, Lean's."""
    budget = _BUDGET.set([WALK_POINTS] if draw.counted else None)
    late = _DEADLINE.set(deadline)
    given = _GIVEN_UP.set([])
    try:
        if total:
            with totalized():
                yield
        else:
            yield
    finally:
        _GIVEN_UP.reset(given)
        _DEADLINE.reset(late)
        _BUDGET.reset(budget)


def _both_readings(
    annotation: _Annotation,
    scope: dict[str, Any],
    reading: _Reading,
    draw: _Draw,
    unsummed: list[list[tuple[str, Any]]],
    deadline: float,
    total: bool = False,
) -> tuple[_Outcome, _Outcome]:
    """What the rerun of ``annotation`` and its term came to at ``draw``.

    ``unsummed`` is where the rerun's sums with no value go (:func:`_add`).
    With ``total`` both read what Python has no value for as Lean has it.

    Where the draw is counted (:class:`_Draw`), each reading may walk
    :data:`WALK_POINTS` points, and both together may run until
    ``deadline``.

    Raises:
        _TooLarge: If one of them walked more than that, which gives the draw
            up.
        _TooSlow: If they ran past ``deadline``, or a power past
            :data:`POWER_BITS` was asked for, which gives the draw up too.
    """
    with _reading(draw, deadline, total), concrete_sorts(draw.samples):
        try:
            if annotation.code is not None:
                value = eval(annotation.code, scope, None)
            else:
                value = annotation.given
            # a term the rerun built, read at the draw, logs its sums with the rerun's
            built = _Reading(dict(draw.context), draw.samples)
            built.unsummed = unsummed
            python = _Outcome(_value_at(value, built))
        except Exception as exc:  # noqa: BLE001 - what the annotation raises is its answer
            python = _Outcome(error=exc)
        # a helper may have caught the draw's giving up and answered all the same
        _kept()
    with _reading(draw, deadline, total):
        try:
            term = _Outcome(_value_at(annotation.term, reading))
        except Exception as exc:  # noqa: BLE001 - what the term raises is its answer
            term = _Outcome(error=exc)
        _kept()
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
    #: What a draw's copy of the snapshot could not make again (:meth:`Snapshot.fresh_copy`).
    shared: dict[str, None] = field(default_factory=dict)
    unanswered: dict[str, str] = field(default_factory=dict)
    counts: dict[str, int] = field(default_factory=dict)
    skipped: list[str] = field(default_factory=list)
    #: Why each draw given up as ``slow`` was.
    slow: list[str] = field(default_factory=list)
    #: The draw at which the check made no more, past :data:`SLOW_DRAWS`
    #: draws too slow (#113), or ``None``.
    stopped: str | None = None

    def give_up(self, verdict: str, why: str) -> None:
        """Count a draw given up, ``unwalked`` or ``slow``, and say why."""
        self.counts[verdict] = self.counts.get(verdict, 0) + 1
        self.skipped.append(why)
        if verdict == "slow":
            self.slow.append(why)

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
    names = _reduction_names(theorem.namespace, inspect.signature(fn).parameters)
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
        snapshot = theorem.snapshot
        codes = [annotation.code for annotation in annotations if annotation.code is not None]
        extent = _extent(theorem, codes, snapshot.namespace)
        with _watching((*codes, *snapshot.watched), snapshot.roots, snapshot.namespace):
            refuted = _run(fact, tally, snapshot, parameters, annotations, theorem, extent)
        if refuted is not None:
            return refuted
    except Exception as exc:  # noqa: BLE001 - a fact, never a crash of the check
        return declined(f"the annotations could not be run again: {type(exc).__name__}: {exc}")
    if tally.stopped is not None:
        return declined(_too_slow(tally))
    if not tally.draws:
        why = f" ({tally.skipped[0]})" if tally.skipped else ""
        return declined(
            f"no draw could be made{why}, so the annotations were run again at no point"
        )
    for annotation in annotations:
        if not tally.agreed.get(annotation.name):
            return declined(
                f"{annotation.what} had no answer on both sides at any of {tally.draws} "
                f"draws, so its reading was not compared "
                f"({tally.unanswered.get(annotation.name, 'no draw compared it')})"
            )
    if snapshot.shared or tally.shared:
        return declined(_not_copied((*snapshot.shared, *tally.shared)))
    return fact(
        Status.TESTED,
        draws=tally.draws,
        compared=sum(tally.agreed.values()),
        seed=SEED,
        **tally.counts,
    )


def _run(
    fact: Callable[..., Fact],
    tally: _Tally,
    snapshot: Snapshot,
    parameters: Sequence[str],
    annotations: Sequence[_Annotation],
    theorem: Any,
    extent: _Extent,
) -> Fact | None:
    """Compare the readings at every draw, counting in ``tally``; the refutation, if one disagrees.

    Each draw starts from the module as the reading found it (#103). Where
    both readings of an annotation have no value at a draw, the draw is
    read again with what Python has no value for read as Lean has it
    (:func:`lanky.terms.totalized`), so that what follows where Python
    stopped is compared on both sides (#99): where both then have a value,
    they have to agree. Until the second reading has run, such an
    annotation's first comparison is not counted, so that a draw at which
    the second reading is given up compares nothing past where Python
    stopped, and counts for nothing. A draw that is given up is not counted.
    Each draw has :data:`DRAW_SECONDS` of its own, a written value past one
    too slow to draw at too, since a helper slow at ``999`` can answer
    otherwise at ``1000`` (#114); once more than :data:`SLOW_DRAWS` draws
    have been given up as too slow, no more are made, and ``tally`` says so
    (:attr:`_Tally.stopped`), which declines the reading (#113).
    """
    hypotheses = [prop for _, prop in theorem.hypotheses]
    for draw in _draws(theorem.variables, hypotheses, extent):
        if isinstance(draw, str):
            tally.skipped.append(draw)
            continue
        if tally.counts.get("slow", 0) > SLOW_DRAWS:
            tally.stopped = draw.label
            return None
        tally.draws += 1
        # both readings of the draw, and its second reading, share its time
        deadline = time.monotonic() + DRAW_SECONDS
        stopped: dict[str, tuple[_Outcome, _Outcome]] = {}
        # the comparisons of the annotations that stopped, counted once the
        # second reading has compared what follows
        pending: list[tuple[_Annotation, str, _Outcome, _Outcome]] = []
        # every other comparison of the draw, counted only once the draw is
        # one: an annotation that agreed before a later one was given up must
        # not count that agreement, since the draw is not a draw
        done: list[tuple[_Annotation, str, _Outcome, _Outcome]] = []
        given_up = False
        namespace, shared = snapshot.fresh_copy()
        tally.shared.update(dict.fromkeys(shared))
        for annotation, verdict, python, term in _compare(
            namespace, parameters, annotations, draw, deadline=deadline
        ):
            if verdict == "differed":
                return _refuted(fact, annotation, draw, python, term)
            if verdict in ("unwalked", "slow"):
                # given up, so the draw is not one
                tally.draws -= 1
                tally.give_up(verdict, f"{draw.label}: {python.error}")
                given_up = True
                continue
            if python.error is not None and term.error is not None:
                stopped[annotation.name] = (python, term)
                pending.append((annotation, verdict, python, term))
                continue
            done.append((annotation, verdict, python, term))
        if given_up:
            continue
        if not stopped:
            for comparison in done:
                tally.record(*comparison)
            continue
        namespace, shared = snapshot.fresh_copy()
        tally.shared.update(dict.fromkeys(shared))
        for annotation, verdict, python, term in _compare(
            namespace, parameters, annotations, draw, total=True, deadline=deadline
        ):
            if verdict in ("unwalked", "slow"):
                # what follows where Python stopped was not compared
                tally.draws -= 1
                tally.give_up(verdict, f"{draw.label}, read as Lean reads it: {python.error}")
                break
            if (
                annotation.name in stopped
                and verdict == "differed"
                and python.error is None
                and term.error is None
            ):
                return _refuted(
                    fact, annotation, draw, python, term, stopped=stopped[annotation.name]
                )
        else:
            for comparison in done + pending:
                tally.record(*comparison)
    return None


def _too_slow(tally: _Tally) -> str:
    """Why a reading is not tested whose draws the check stopped, too many of them too slow."""
    listing = "; ".join(tally.slow[:3])
    if len(tally.slow) > 3:
        listing += f"; and {len(tally.slow) - 3} more"
    return (
        f"{len(tally.slow)} draws were given up as too slow ({listing}), more than the "
        f"{SLOW_DRAWS} a claim may give up so, so the check made no draw from "
        f"{tally.stopped} on, and the reading was not compared there"
    )


def _not_copied(shared: Sequence[str]) -> str:
    """Why a reading that agreed at every draw is not tested: what it reaches was not copied."""
    listing = "; ".join(shared[:3])
    if len(shared) > 3:
        listing += f"; and {len(shared) - 3} more"
    return (
        "the annotations reach what the check could not copy as it was when the claim "
        f"was read: {listing}. The rerun reads it as it is now, which may have changed "
        "since, so agreeing at every draw does not test the reading"
    )


#: What the second reading of a draw reads as Lean has it (see :func:`lanky.terms.totalized`).
_TOTALIZED = (
    "x / 0 and x // 0 are 0, x % 0 is x, 0 ** -k is 0, a logarithm and a square root "
    "outside their Python domain are Mathlib's, and a family outside its domain is 0"
)


def _refuted(
    fact: Any,
    annotation: _Annotation,
    draw: _Draw,
    python: _Outcome,
    term: _Outcome,
    stopped: tuple[_Outcome, _Outcome] | None = None,
) -> Fact:
    """The refutation at ``draw``, where ``annotation`` and its term disagree.

    ``stopped`` are the two outcomes of the first reading of the draw where
    both had no value, and ``python`` and ``term`` those of the second, which
    reads what Python has no value for as Lean has it (#99).
    """
    counterexample = {name: _described(value) for name, value in draw.context.items()}
    sampled = draw.samples.described()
    iterated = f" with each sort iterating its sample {sampled}" if sampled else ""
    term_text = _shown(annotation.term)
    found = f"{python.text()}, and its term, {term_text}, {term.text()}"
    differs = "the term says"
    extra: dict[str, Any] = {}
    if stopped is not None:
        first, second = stopped
        found = (
            f"{first.text()}, and its term, {term_text}, {second.text()}; read as Lean "
            f"reads what has no value in Python ({_TOTALIZED}), it {python.text()} "
            f"and its term {term.text()}"
        )
        differs = "what follows where Python stopped says"
        extra = {"totalized": True, "stopped": first.text()}
    return fact(
        Status.REFUTED,
        counterexample=counterexample,
        witness=f"{annotation.what}, {annotation.source}",
        python_answer=python.text(),
        term_answer=term.text(),
        draw=draw.label,
        **extra,
        reason=(
            f"{annotation.what}, run again as Python at these values{iterated}, "
            f"{found}: {differs} something else than what was written, so no "
            "oracle that decides or proves is asked about the claim"
        ),
    )
