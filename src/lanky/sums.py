"""Exchanging finite sums: Python finds the order of the sums, Lean checks it.

The design idea. Most identities between finite sums that a numerical code
rests on are one move: distribute the products into the sums, put the sums in
the same order on both sides, and compare the summands. Sum factorization is
the example the demonstrations need. A tensor-product operator applied to a
field on a hexahedron, ``sum(H[c, r] * G[b, q] * F[a, p] * u[p, q, r] for p
... for q ... for r ...)``, is three one-axis passes, ``sum(H[c, r] * sum(G[b,
q] * sum(F[a, p] * u[p, q, r] for p ...) for q ...) for r ...)``: distributed,
the right side is a sum over ``r``, ``q`` and ``p`` in that order, the left a
sum over ``p``, ``q`` and ``r``, and the two summands are one product. Lean
does each step with a lemma Mathlib has (``Finset.mul_sum``, ``Finset.sum_mul``
and ``Finset.sum_div`` to distribute, ``Finset.sum_comm`` to exchange two
adjacent sums, ``Finset.sum_congr`` to compare the summands, ``ring`` for the
comparison). What it does not do is choose which sums to exchange: that is a
search over the orders of the sums, and it is the Python half's.

This module is that half. :func:`spread` reads one side as Lean's ``simp only
[Finset.mul_sum, Finset.sum_mul, Finset.sum_div]`` leaves it: the binders of
the sums, outermost first, and the summand (a :class:`Spread`). The order is
the one ``simp`` produces: in a product of two sides that both sum, the right
one's sums end up outside the left one's, since ``Finset.mul_sum`` rewrites the
product before ``Finset.sum_mul`` does. :func:`orders` then finds the orders of
the left side's sums under which its summand, its binders renamed, is the right
side's: the domains have to agree, and the summands are compared up to
``ring`` by sympy where it is installed (the ``cas`` extra), and by their
factors where it is not. The Lean half, :func:`lanky.oracles.lean.sum_scripts`,
writes the script that does the exchanges one adjacent pair at a time, and Lean
checks it: a wrong order, or a model of ``simp`` that is wrong for some term,
costs an attempt and never a proof.

What is not read: a sum with a guard (``if`` in the generator, which Lean
filters by), a binder over anything but a ``Fin``, a sum whose bound mentions
another sum's binder (a triangle, whose sums do not exchange by
``Finset.sum_comm``), a sum inside anything but a product, a quotient's
numerator or another sum, and a side with more than :data:`MAX_SUMS` sums.
"""

from __future__ import annotations

import itertools
import numbers
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import substitute, substitute_domain
from lanky.prelude import FinType
from lanky.terms import Abs, Elementary, Exists, Forall, Product, Quotient, Sum, Var, init_args

__all__ = ["DISTRIBUTE", "MAX_SUMS", "Spread", "mentioned", "orders", "spread"]

#: The lemmas Lean's ``simp only`` distributes with, which :func:`spread` models.
DISTRIBUTE = ("Finset.mul_sum", "Finset.sum_mul", "Finset.sum_div")

#: The most sums one side may have: every order of them is a candidate, so
#: this bounds the search at ``MAX_SUMS!`` orders.
MAX_SUMS = 6

#: How many orders :func:`orders` proposes when it cannot tell which is right.
_UNVERIFIED = 2


@dataclass(frozen=True, eq=False)
class Spread:
    """One side of an equation with its products distributed into its sums.

    Attributes:
        binders: ``(variable, domain)`` for each sum, outermost first, as
            Lean's ``simp only`` (:data:`DISTRIBUTE`) leaves them. Each
            variable has a name of its own, not one the statement uses.
        body: The summand, with no sum left in it.
    """

    binders: tuple[tuple[Var, Any], ...]
    body: Any


def spread(expr: Any, taken: set[str]) -> Spread | None:
    """``expr`` with its products distributed into its sums, as Lean's ``simp only`` does it.

    ``taken`` holds the names the statement mentions, and gets the names given
    to the binders, which are fresh: the same name bound by two sums of a
    product, ``sum(f(i) ...) * sum(g(i) ...)``, would otherwise be one
    variable of the summand. ``None`` for a side this does not read (see the
    module docstring).
    """
    found = _spread(expr, taken)
    if found is None:
        return None
    names = {var.name for var, _ in found.binders}
    for _, domain in found.binders:
        if _mentions(domain.bound, names):
            # a triangle: the inner sum's extent depends on the outer binder
            return None
    return found


def _spread(expr: Any, taken: set[str]) -> Spread | None:
    if isinstance(expr, Sum):
        if expr.guard is not None:
            return None
        binders: list[tuple[Var, Any]] = []
        renaming: dict[str, Any] = {}
        for var, domain in expr.binders:
            if not isinstance(domain, FinType):
                return None
            fresh = Var(_fresh(var.name, taken))
            binders.append((fresh, substitute_domain(domain, renaming)))
            renaming[var.name] = fresh
        inner = _spread(substitute(expr.body, renaming), taken)
        if inner is None:
            return None
        return Spread((*binders, *inner.binders), inner.body)
    if isinstance(expr, prim.Product):
        parts = [_spread(child, taken) for child in expr.children]
        if any(part is None for part in parts):
            return None
        total = parts[0]
        assert total is not None
        for part in parts[1:]:
            assert part is not None
            # Finset.mul_sum takes the right factor's sums out first
            total = Spread((*part.binders, *total.binders), Product((total.body, part.body)))
        return total
    if isinstance(expr, prim.Quotient):
        if _has_sum(expr.denominator):
            return None
        numerator = _spread(expr.numerator, taken)
        if numerator is None:
            return None
        return Spread(numerator.binders, Quotient(numerator.body, expr.denominator))
    if _has_sum(expr):
        return None
    return Spread((), expr)


def _fresh(stem: str, taken: set[str]) -> str:
    """``stem_1``, ``stem_2``, ...: the first such name not in ``taken``, which gets it."""
    index = 1
    while f"{stem}_{index}" in taken:
        index += 1
    name = f"{stem}_{index}"
    taken.add(name)
    return name


def _has_sum(expr: Any) -> bool:
    """Whether a sum appears anywhere in ``expr``."""
    if isinstance(expr, Sum):
        return True
    if isinstance(expr, Forall | Exists):
        return any(_has_sum(part) for part in (expr.body, expr.guard) if part is not None)
    if isinstance(expr, tuple):
        return any(_has_sum(item) for item in expr)
    if isinstance(expr, prim.ExpressionNode):
        return any(_has_sum(child) for child in init_args(expr))
    return False


def _mentions(expr: Any, names: set[str]) -> bool:
    """Whether ``expr`` mentions a variable among ``names``."""
    if isinstance(expr, prim.Variable):
        return expr.name in names
    if isinstance(expr, tuple):
        return any(_mentions(item, names) for item in expr)
    if isinstance(expr, prim.ExpressionNode):
        return any(_mentions(child, names) for child in init_args(expr))
    return False


def orders(left: Spread, right: Spread) -> list[tuple[int, ...]]:
    """The orders of the left side's sums under which its summand is the right side's.

    An order lists, for each sum of the right side from the outermost, which
    sum of the left side it is. The domains have to agree, and so do the
    summands once the left side's binders are renamed to the right side's:
    up to ``ring``, as sympy expands their difference to zero. The first order
    sympy confirms is the one returned. Where sympy is not installed, or
    cannot read a summand, an order whose summands are the same product of
    the same factors is taken as confirmed, and otherwise the first
    :data:`_UNVERIFIED` orders whose domains agree are proposed, for Lean to
    judge. Empty when the two sides have different numbers of sums, none,
    more than :data:`MAX_SUMS`, or no order sympy accepts.
    """
    size = len(left.binders)
    if size != len(right.binders) or size == 0 or size > MAX_SUMS:
        return []
    unverified: list[tuple[int, ...]] = []
    for order in itertools.permutations(range(size)):
        if not all(
            left.binders[order[place]][1] == right.binders[place][1] for place in range(size)
        ):
            continue
        renaming = {
            left.binders[order[place]][0].name: right.binders[place][0]
            for place in range(size)
        }
        verdict = _same(substitute(left.body, renaming), right.body)
        if verdict is True:
            return [order]
        if verdict is None and len(unverified) < _UNVERIFIED:
            unverified.append(order)
    return unverified


def _same(left: Any, right: Any) -> bool | None:
    """Whether two summands are equal up to ``ring``; ``None`` where that cannot be told."""
    if sorted(_factors(left)) == sorted(_factors(right)):
        return True
    try:
        import sympy
    except ImportError:
        return None
    functions: dict[str, Any] = {}
    try:
        difference = _to_sympy(sympy, left, functions) - _to_sympy(sympy, right, functions)
    except _Unreadable:
        return None
    if sympy.expand(difference) == 0:
        return True
    try:
        return bool(sympy.simplify(difference) == 0)
    except (TypeError, ValueError, NotImplementedError):  # pragma: no cover - sympy's own limits
        return None


def _factors(expr: Any) -> list[str]:
    """The factors of a product, each as its text, with the numbers multiplied out first."""
    from lanky.terms import render

    coefficient: Any = 1
    found: list[str] = []
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Product):
            stack.extend(node.children)
        elif isinstance(node, numbers.Number) and not isinstance(node, bool):
            coefficient *= node
        else:
            found.append(render(node))
    return [str(coefficient), *found]


class _Unreadable(Exception):
    """A summand :func:`_to_sympy` cannot read."""


def _to_sympy(sympy: Any, expr: Any, functions: dict[str, Any]) -> Any:
    """A summand as a sympy expression: a family's application is an undefined function's."""
    if isinstance(expr, bool):
        raise _Unreadable("a truth value")
    if isinstance(expr, prim.Variable):
        return sympy.Symbol(expr.name)
    if isinstance(expr, numbers.Integral):
        return sympy.Integer(int(expr))
    if isinstance(expr, Fraction):
        return sympy.Rational(expr.numerator, expr.denominator)
    if isinstance(expr, float):
        exact = Fraction(expr)
        return sympy.Rational(exact.numerator, exact.denominator)
    if isinstance(expr, complex):
        return _to_sympy(sympy, expr.real, functions) + sympy.I * _to_sympy(
            sympy, expr.imag, functions
        )
    if isinstance(expr, prim.Call | prim.Subscript):
        head, arguments = _application(expr)
        if head is None:
            raise _Unreadable("an application of something that is not a family")
        function = functions.setdefault(head, sympy.Function(head))
        return function(*(_to_sympy(sympy, argument, functions) for argument in arguments))
    if isinstance(expr, prim.Sum):
        return sympy.Add(*(_to_sympy(sympy, child, functions) for child in expr.children))
    if isinstance(expr, prim.Product):
        return sympy.Mul(*(_to_sympy(sympy, child, functions) for child in expr.children))
    if isinstance(expr, prim.Quotient):
        return _to_sympy(sympy, expr.numerator, functions) / _to_sympy(
            sympy, expr.denominator, functions
        )
    if isinstance(expr, prim.Power):
        return sympy.Pow(
            _to_sympy(sympy, expr.base, functions), _to_sympy(sympy, expr.exponent, functions)
        )
    if isinstance(expr, Elementary):
        function = {"exp": sympy.exp, "log": sympy.log, "sqrt": sympy.sqrt}.get(expr.function)
        if function is None:
            raise _Unreadable(f"the function {expr.function}")
        return function(_to_sympy(sympy, expr.argument, functions))
    if isinstance(expr, Abs):
        return sympy.Abs(_to_sympy(sympy, expr.operand, functions))
    raise _Unreadable(type(expr).__name__)


def _application(expr: Any) -> tuple[str | None, tuple[Any, ...]]:
    """``(family, arguments)`` of a chain of applications: ``F(a)(b)`` and ``F[a, b]`` alike."""
    arguments: tuple[Any, ...] = ()
    while True:
        if isinstance(expr, prim.Call):
            arguments = (*expr.parameters, *arguments)
            expr = expr.function
        elif isinstance(expr, prim.Subscript):
            index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
            arguments = (*index, *arguments)
            expr = expr.aggregate
        elif isinstance(expr, prim.Variable):
            return expr.name, arguments
        else:
            return None, arguments


def mentioned(expr: Any, found: set[str] | None = None) -> set[str]:
    """Every name ``expr`` mentions, free or bound, so that a fresh one is none of them."""
    found = set() if found is None else found
    if isinstance(expr, prim.Variable):
        found.add(expr.name)
    elif isinstance(expr, Forall | Exists | Sum):
        for var, domain in expr.binders:
            found.add(var.name)
            if isinstance(domain, FinType):
                mentioned(domain.bound, found)
        for part in (expr.body, expr.guard):
            if part is not None:
                mentioned(part, found)
    elif isinstance(expr, tuple):
        for item in expr:
            mentioned(item, found)
    elif isinstance(expr, prim.ExpressionNode):
        for child in init_args(expr):
            mentioned(child, found)
    return found
