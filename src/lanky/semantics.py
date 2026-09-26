"""Where lanky's Python reading of a statement and Lean's still differ.

The design idea. A lanky statement is read by more than one oracle: the property
tester evaluates it with Python's arithmetic on Python integers, isl reads its
index arithmetic as integer arithmetic, and the Lean oracle elaborates what
:mod:`lanky.lean` prints. They read one statement, the integer one. ``Nat``
means an integer that is not negative, and the Lean printer says so: a natural
is an ``Int`` with ``0 ≤ n`` as a hypothesis, subtraction is ``Int``
subtraction, and ``//`` and ``%`` are ``Int.fdiv`` and ``Int.fmod``, which
round toward negative infinity as Python's do. Subtraction over ``Nat`` and
floor division over ``Int`` therefore mean the same thing to every oracle, and
carry no note.

One gap is left in integer arithmetic, and a fact exposed to it is worth a note
in its provenance rather than a silent discrepancy:

*Division or remainder by something that may be zero.* Lean's division is
total: ``Int.fdiv x 0`` is ``0`` and ``Int.fmod x 0`` is ``x``, and Lean proves
statements that say so. Python raises ``ZeroDivisionError``, so the sampled
reading has no answer where the Lean reading has an easy one: ``n // 0 == 0``
is a Lean theorem and a Python exception. A divisor that is a nonzero integer
literal is the one case that can be ruled out by looking, so it is the one case
that carries no note.

The Mathlib dialect of the printer reads two more things Lean totalizes, and
they get notes of the same kind whether or not Mathlib is installed, since they
are properties of the statement and not of the machine:

*True division by something that may be zero.* ``x / 0`` is ``0`` in a Mathlib
field and a ``ZeroDivisionError`` in Python, whatever the sort.

*A logarithm or a square root outside its Python domain.* ``Real.log 0`` is
``0``, ``Real.log (-x)`` is ``Real.log x`` and ``Real.sqrt`` of a negative
number is ``0``; ``math.log`` and ``math.sqrt`` raise. An argument that is a
positive literal is the one that can be ruled out by looking.

A real statement has a third difference that is no gap in this sense and is not
noted: the tester computes ``Real`` and ``Complex`` in floating point (or with
fractions, for ``exact``), and Lean over ``ℝ`` and ``ℂ``. A claim that holds
only up to rounding is refuted by the one and can be proved by the other, which
is what the exactness class of a sort is there to say.

This module only *detects* the gap, and records what it found; it does not
change how anything is evaluated. Making the tester total instead would give
``n // 0`` a value the file, run as a program, never computes.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import Elementary, Exists, Forall, Sum, init_args

__all__ = [
    "DIVISION_BY_ZERO",
    "OUTSIDE_THE_DOMAIN",
    "TRUE_DIVISION_BY_ZERO",
    "divides_by_possible_zero",
    "leaves_the_domain",
    "notes",
    "sorts_of",
    "truly_divides_by_possible_zero",
]

#: The note recorded for a division whose divisor cannot be seen to be nonzero.
DIVISION_BY_ZERO = (
    "division or remainder by a divisor that is not a nonzero literal: Lean's "
    "integer division is total (Int.fdiv x 0 is 0 and Int.fmod x 0 is x) while "
    "Python raises ZeroDivisionError, so the sampled reading cannot answer where "
    "Lean can"
)


#: The note recorded for a true division whose divisor cannot be seen to be nonzero.
TRUE_DIVISION_BY_ZERO = (
    "true division by a divisor that is not a nonzero literal: division in a "
    "Mathlib field is total (x / 0 is 0) while Python raises ZeroDivisionError, "
    "so the sampled reading cannot answer where Lean can"
)

#: The note recorded for a logarithm or square root of an argument that may be
#: outside the domain Python gives it.
OUTSIDE_THE_DOMAIN = (
    "a logarithm or square root of an argument that is not a positive literal: "
    "Mathlib's Real.log and Real.sqrt are total (Real.log 0 is 0, Real.log (-x) "
    "is Real.log x, and the square root of a negative number is 0) while "
    "Python's math.log and math.sqrt raise, so the sampled reading cannot "
    "answer where Lean can"
)


def _children(expr: Any) -> tuple[Any, ...]:
    """The subexpressions of a term, everything a domain object carries included.

    A domain is not a pymbolic node, so the walk has to know how to open one, and
    it has to: arithmetic hides in a domain as readily as in a body.
    ``n : Nat & (10 // n > 1)`` divides in a refinement predicate,
    ``Fin[n // k]`` in an index type's bound, and ``Fn[Fin[m % k], Nat]`` inside
    a family's domain. Lean elaborates all three with its total division, so all
    three are exposed to the same gap as a body that divides.
    """
    if isinstance(expr, Forall | Exists | Sum):
        parts: list[Any] = [expr.body]
        if expr.guard is not None:
            parts.append(expr.guard)
        for _var, domain in expr.binders:
            parts.append(domain)
        return tuple(parts)
    if isinstance(expr, Refined):
        return (expr.base, *expr.props)
    if isinstance(expr, FnType):
        return (expr.domain, expr.codomain)
    if isinstance(expr, FinType):
        return (expr.bound,)
    if isinstance(expr, prim.ExpressionNode):
        return init_args(expr)
    if isinstance(expr, tuple):
        return expr
    return ()


def _walk(expr: Any) -> Any:
    """Yield every subterm of ``expr``, itself included."""
    yield expr
    for child in _children(expr):
        yield from _walk(child)


def sorts_of(term: Any) -> set[str]:
    """The names of the sorts a term quantifies over, ``Fin`` counted as ``Nat``.

    A point of ``Fin[n]`` is a natural below ``n``, and its arithmetic is the
    same integer arithmetic as any natural's.
    """
    found: set[str] = set()
    for node in _walk(term):
        for sort in _domain_sorts(node):
            found.add(sort)
    return found


def _domain_sorts(node: Any) -> tuple[str, ...]:
    """The sort names one binder domain contributes."""
    if isinstance(node, Refined):
        return _domain_sorts(node.base)
    if isinstance(node, FinType):
        return ("Nat",)
    if isinstance(node, FnType):
        return _domain_sorts(node.domain) + _domain_sorts(node.codomain)
    if isinstance(node, Sort):
        return (node.name,)
    return ()


def _is_nonzero_literal(expr: Any) -> bool:
    """Whether this divisor is an integer literal that is plainly not zero.

    An integral ``Fraction``, which only a term built node by node carries, is
    the integer it equals, as the Lean printer reads it: ``n // Fraction(2,
    1)`` prints as ``n / 2``.
    """
    if isinstance(expr, Fraction) and expr.denominator == 1:
        expr = int(expr)
    return isinstance(expr, int) and not isinstance(expr, bool) and expr != 0


def divides_by_possible_zero(term: Any) -> bool:
    """Whether ``term`` divides by something that has not been ruled out as zero.

    Syntactic on purpose, and in the safe direction: a nonzero integer literal
    is the only divisor that can be dismissed by looking at it, so ``n // 2``
    carries no note and ``n // 0``, ``n // k`` and ``n // (k + 1)`` all do. A
    divisor a hypothesis keeps away from zero is flagged as well, which
    overstates the gap by one note and never understates it.
    """
    return any(
        isinstance(node, prim.FloorDiv | prim.Remainder)
        and not _is_nonzero_literal(node.denominator)
        for node in _walk(term)
    )


def truly_divides_by_possible_zero(term: Any) -> bool:
    """Whether ``term`` has a true division (``/``) by something not ruled out as zero.

    The same syntactic test as :func:`divides_by_possible_zero`, in the same
    safe direction, for ``/``: ``x / 2`` carries no note, ``x / y`` does.
    """
    return any(
        isinstance(node, prim.Quotient)
        and not isinstance(node, prim.FloorDiv | prim.Remainder)
        and not _is_nonzero_literal(node.denominator)
        for node in _walk(term)
    )


def _is_positive_literal(expr: Any) -> bool:
    """Whether an argument is a number literal that is plainly above zero."""
    if isinstance(expr, bool) or not isinstance(expr, int | float | Fraction):
        return False
    return expr > 0


def leaves_the_domain(term: Any) -> bool:
    """Whether ``term`` takes a logarithm or a square root of something not seen positive.

    Syntactic, like the division checks: ``log(2)`` carries no note, and
    ``log(x)``, ``log(x * x)`` and ``sqrt(x - 1)`` do, a hypothesis that keeps
    the argument positive included. ``exp`` is total on both sides and is never
    noted; a float it overflows is rare at the points the tester draws, and the
    draw is dropped when it happens.
    """
    return any(
        isinstance(node, Elementary)
        and node.function in ("log", "sqrt")
        and not _is_positive_literal(node.argument)
        for node in _walk(term)
    )


def notes(term: Any) -> tuple[str, ...]:
    """The semantics gaps this term is exposed to, as lines for a provenance.

    An empty tuple is the common case and the one worth having: arithmetic over
    ``Nat`` and ``Int``, subtraction and floor division included, means the same
    thing to every oracle, so only a division that may be by zero is noted, and
    in a statement Mathlib reads, a true division that may be by zero and a
    logarithm or square root that may leave its Python domain.
    """
    if term is None:
        return ()
    try:
        sorts = sorts_of(term)
        found: list[str] = []
        if ("Nat" in sorts or "Int" in sorts) and divides_by_possible_zero(term):
            found.append(DIVISION_BY_ZERO)
        if truly_divides_by_possible_zero(term):
            found.append(TRUE_DIVISION_BY_ZERO)
        if leaves_the_domain(term):
            found.append(OUTSIDE_THE_DOMAIN)
    except Exception:  # noqa: BLE001 - a note is never worth failing a check over
        return ()
    return tuple(found)
