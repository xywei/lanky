"""Where lanky's Python reading of a statement and Lean's differ.

The design idea. A lanky statement is read twice: the property tester evaluates
it with Python's arithmetic on Python integers, and the Lean oracle elaborates
it with Lean's arithmetic on ``Nat`` and ``Int``. For index arithmetic the two
readings agree, which is why the same annotation can be both a test and a
theorem. Three things break that agreement, and a fact that uses one is worth a
note in its provenance rather than a silent discrepancy:

*Subtraction over ``Nat``.* Lean truncates at zero, so ``n - 1`` is ``0`` at
``n = 0``. The property tester samples a natural as a Python integer, where
``n - 1`` is ``-1``. A statement can therefore be ``PROVED`` in Lean and false
under the sampled reading, or the other way around.

*Floor division and remainder over ``Int``.* Lean and Python disagree on how a
negative operand rounds. Over ``Nat`` they agree.

*Division or remainder by something that may be zero.* Lean's ``Nat`` and
``Int`` division are total: ``x / 0`` is ``0`` and ``x % 0`` is ``x``, and
``omega`` proves statements that say so. Python raises ``ZeroDivisionError``,
so the sampled reading has no answer where the Lean reading has an easy one.
This one is over ``Nat`` as much as over ``Int``, which is why it is a note of
its own: ``n // 0 == 0`` is a Lean theorem and a Python exception. A divisor
that is a nonzero integer literal is the one case that can be ruled out by
looking, so it is the one case that carries no note.

This module only *detects* the three, and records what it found; it does not
change how anything is evaluated. Truncating the evaluator instead would be
wrong in an interesting way, and the reason is worth writing down: pymbolic has
no subtraction node, so ``a - b + c`` is one flattened
:class:`pymbolic.primitives.Sum` with a ``(-1) * b`` summand in it. Lean reads
the same source as ``(a - b) + c`` and truncates at the inner subtraction, which
at ``a = 0, b = 1, c = 5`` gives ``5``; truncating a flattened sum at the end
gives ``4``. The two readings cannot be reconciled without recovering the
association the source had, which lanky deliberately does not parse. So the
honest thing, and what this module does, is to say which statements are affected
and leave both readings as they are.
"""

from __future__ import annotations

from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import Exists, Forall, Sum, init_args

__all__ = [
    "DIVISION_BY_ZERO",
    "INT_DIVISION",
    "NAT_SUBTRACTION",
    "divides_by_possible_zero",
    "notes",
    "sorts_of",
    "uses_floor_division",
    "uses_subtraction",
]

#: The note recorded for a statement over ``Nat`` that subtracts.
NAT_SUBTRACTION = (
    "subtraction over Nat: Lean truncates at 0 (n - 1 is 0 at n = 0) while the "
    "property tester samples naturals as Python integers, which go negative"
)

#: The note recorded for a statement over ``Int`` that divides or takes a remainder.
INT_DIVISION = (
    "floor division or remainder over Int: Lean and Python round a negative "
    "operand differently"
)

#: The note recorded for a division whose divisor cannot be seen to be nonzero.
DIVISION_BY_ZERO = (
    "division or remainder by a divisor that is not a nonzero literal: Lean's "
    "Nat and Int division are total (x / 0 is 0 and x % 0 is x) while Python "
    "raises ZeroDivisionError, so the sampled reading cannot answer where Lean "
    "can"
)


def _is_negated(child: Any) -> bool:
    """Whether this summand is the ``(-1) * x`` pymbolic builds for ``a - b``."""
    if isinstance(child, prim.Product) and child.children:
        first = child.children[0]
        return isinstance(first, int) and not isinstance(first, bool) and first < 0
    return isinstance(child, int) and not isinstance(child, bool) and child < 0


def _children(expr: Any) -> tuple[Any, ...]:
    """The subexpressions of a term, everything a domain object carries included.

    A domain is not a pymbolic node, so the walk has to know how to open one, and
    it has to: arithmetic hides in a domain as readily as in a body.
    ``n : Nat & (n - 1 < n)`` subtracts in a refinement predicate, ``Fin[n - 1]``
    in an index type's bound, and ``Fn[Fin[k - 1], Nat]`` inside a family's
    domain. Lean elaborates all three with Lean's arithmetic, so all three are
    exposed to the same gap as a body that subtracts.
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

    A bounded quantifier prints as a guarded ``Nat`` quantifier in Lean, so an
    index variable is a natural there and its arithmetic is Nat arithmetic.
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


def uses_subtraction(term: Any) -> bool:
    """Whether any addition in ``term`` has a negated summand, which is a ``-``."""
    return any(
        isinstance(node, prim.Sum) and any(_is_negated(child) for child in node.children)
        for node in _walk(term)
    )


def uses_floor_division(term: Any) -> bool:
    """Whether ``term`` divides or takes a remainder."""
    return any(isinstance(node, prim.FloorDiv | prim.Remainder) for node in _walk(term))


def _is_nonzero_literal(expr: Any) -> bool:
    """Whether this divisor is an integer literal that is plainly not zero."""
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


def notes(term: Any) -> tuple[str, ...]:
    """The semantics gaps this term is exposed to, as lines for a provenance.

    An empty tuple is the common case and the one worth having: index
    arithmetic over ``Nat`` with no subtraction means exactly the same thing in
    both readings.
    """
    if term is None:
        return ()
    try:
        sorts = sorts_of(term)
        found: list[str] = []
        if "Nat" in sorts and uses_subtraction(term):
            found.append(NAT_SUBTRACTION)
        if "Int" in sorts and uses_floor_division(term):
            found.append(INT_DIVISION)
        if ("Nat" in sorts or "Int" in sorts) and divides_by_possible_zero(term):
            found.append(DIVISION_BY_ZERO)
    except Exception:  # noqa: BLE001 - a note is never worth failing a check over
        return ()
    return tuple(found)
