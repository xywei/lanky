"""Where lanky's Python reading of a statement and Lean's differ.

The design idea. A lanky statement is read twice: the property tester evaluates
it with Python's arithmetic on Python integers, and the Lean oracle elaborates
it with Lean's arithmetic on ``Nat`` and ``Int``. For index arithmetic the two
readings agree, which is why the same annotation can be both a test and a
theorem. Two operators break that agreement, and a fact that uses one is worth a
note in its provenance rather than a silent discrepancy:

*Subtraction over ``Nat``.* Lean truncates at zero, so ``n - 1`` is ``0`` at
``n = 0``. The property tester samples a natural as a Python integer, where
``n - 1`` is ``-1``. A statement can therefore be ``PROVED`` in Lean and false
under the sampled reading, or the other way around.

*Floor division and remainder over ``Int``.* Lean and Python disagree on how a
negative operand rounds. Over ``Nat`` they agree.

This module only *detects* the two, and records what it found; it does not
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
    "INT_DIVISION",
    "NAT_SUBTRACTION",
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


def _is_negated(child: Any) -> bool:
    """Whether this summand is the ``(-1) * x`` pymbolic builds for ``a - b``."""
    if isinstance(child, prim.Product) and child.children:
        first = child.children[0]
        return isinstance(first, int) and not isinstance(first, bool) and first < 0
    return isinstance(child, int) and not isinstance(child, bool) and child < 0


def _children(expr: Any) -> tuple[Any, ...]:
    """The subexpressions of a term, quantifier domains included."""
    if isinstance(expr, Forall | Exists | Sum):
        parts: list[Any] = [expr.body]
        if expr.guard is not None:
            parts.append(expr.guard)
        for _var, domain in expr.binders:
            parts.append(domain)
        return tuple(parts)
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
    except Exception:  # noqa: BLE001 - a note is never worth failing a check over
        return ()
    return tuple(found)
