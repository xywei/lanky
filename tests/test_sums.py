"""Exchanging finite sums, the Python half: the sides as Lean distributes them, and the order.

Lean is not needed here: :func:`lanky.sums.spread` models what ``simp only
[Finset.mul_sum, Finset.sum_mul, Finset.sum_div]`` leaves of a side, and
:func:`lanky.sums.orders` finds the order of the sums that makes the summands
agree. That Lean checks the script built from them is ``test_mathlib.py``'s.
"""

from __future__ import annotations

import pytest

from lanky import sums
from lanky.prelude import Fin, FinType, Nat
from lanky.terms import Sum, Var, render, sum_

n, m = Var("n"), Var("m")
a, b, c, p, q, r = (Var(name) for name in "abcpqr")
F, G, H, u = (Var(name) for name in ("F", "G", "H", "u"))
f = Var("f")


def _sides():
    """The two sides of sum factorization in three dimensions, as an annotation builds them."""
    left = sum_(
        H[c, r] * G[b, q] * F[a, p] * u[p, q, r] for p in Fin[n] for q in Fin[n] for r in Fin[n]
    )
    right = sum_(
        H[c, r] * sum_(G[b, q] * sum_(F[a, p] * u[p, q, r] for p in Fin[n]) for q in Fin[n])
        for r in Fin[n]
    )
    return left, right


def test_a_nest_of_sums_is_its_binders_outermost_first() -> None:
    left, right = _sides()
    taken: set[str] = set()
    spread_left = sums.spread(left, taken)
    spread_right = sums.spread(right, taken)
    assert spread_left is not None and spread_right is not None
    # fresh names, outermost first: p, q, r on the left
    assert [var.name for var, _ in spread_left.binders] == ["p_1", "q_1", "r_1"]
    # a factor's sums go inside the sum it multiplies: r, then q, then p
    assert [var.name for var, _ in spread_right.binders] == ["r_2", "q_2", "p_2"]
    assert all(domain == FinType(n) for _, domain in spread_right.binders)
    assert not isinstance(spread_right.body, Sum)
    assert render(spread_right.body) == "H[c, r_2]*(G[b, q_2]*(F[a, p_2]*u[p_2, q_2, r_2]))"


def test_the_order_of_the_left_sums_that_is_the_right_ones() -> None:
    """The left side's ``(p, q, r)`` is the right side's ``(r, q, p)``: one order, reversed."""
    left, right = _sides()
    taken: set[str] = set()
    found = sums.orders(sums.spread(left, taken), sums.spread(right, taken))
    assert found == [(2, 1, 0)]


def test_in_a_product_of_two_sums_the_right_ones_go_outside() -> None:
    """``Finset.mul_sum`` rewrites a product before ``Finset.sum_mul`` does, as Lean was seen to."""
    g = Var("g")
    product = sum_(f[i] for i in Fin[n]) * sum_(g[j] for j in Fin[m])
    spread = sums.spread(product, set())
    assert [(var.name, str(domain)) for var, domain in spread.binders] == [
        ("j_1", "Fin(m)"),
        ("i_1", "Fin(n)"),
    ]
    assert render(spread.body) == "f[i_1]*g[j_1]"


def test_one_name_bound_by_two_sums_is_two_variables() -> None:
    """``sum(f(i) ...) * sum(g(i) ...)`` has two ``i``'s, which the spread side keeps apart."""
    g = Var("g")
    product = sum_(f[i] for i in Fin[n]) * sum_(g[i] for i in Fin[n])
    spread = sums.spread(product, {"i"})
    names = [var.name for var, _ in spread.binders]
    assert len(set(names)) == 2 and "i" not in names
    assert render(spread.body) == f"f[{names[1]}]*g[{names[0]}]"


def test_a_quotient_of_a_sum_is_its_sum_of_quotients() -> None:
    spread = sums.spread(sum_(f[i] for i in Fin[n]) / 3, set())
    assert [var.name for var, _ in spread.binders] == ["i_1"]
    assert render(spread.body) == "f[i_1] / 3"
    assert sums.spread(1 / sum_(f[i] for i in Fin[n]), set()) is None


@pytest.mark.parametrize(
    "side",
    [
        # a triangle: the inner sum's extent is the outer binder
        lambda: sum_(f[i, j] for i in Fin[n] for j in Fin[i]),
        # a guard, which Lean filters by
        lambda: sum_(f[i] for i in Fin[n] if i > 2),
        # a sum over a sort, which has no finite extent
        lambda: Sum(((Var("i"), Nat),), f[Var("i")]),
        # a sum inside something that does not distribute
        lambda: sum_(f[i] for i in Fin[n]) + 1,
    ],
    ids=["triangle", "guard", "sort", "addition"],
)
def test_what_is_not_read(side) -> None:
    assert sums.spread(side(), set()) is None


def test_no_order_where_the_summands_differ(cas) -> None:
    """With the factors swapped on one side, no order makes the summands one product."""
    left, _ = _sides()
    wrong = sum_(
        F[c, r] * sum_(G[b, q] * sum_(H[a, p] * u[p, q, r] for p in Fin[n]) for q in Fin[n])
        for r in Fin[n]
    )
    taken: set[str] = set()
    assert sums.orders(sums.spread(left, taken), sums.spread(wrong, taken)) == []


def test_the_summands_are_compared_up_to_ring(cas) -> None:
    """``F * (u + v)`` against ``F * u + F * v``: not one product, and sympy sees them equal."""
    v, w = Var("v"), Var("w")
    left = sum_(f[i, j] * (v[i] + w[j]) for i in Fin[n] for j in Fin[m])
    right = sum_(f[i, j] * v[i] + f[i, j] * w[j] for j in Fin[m] for i in Fin[n])
    taken: set[str] = set()
    assert sums.orders(sums.spread(left, taken), sums.spread(right, taken)) == [(1, 0)]


def test_a_family_is_read_whichever_way_it_is_applied() -> None:
    """``F[a, p]``, ``F(a, p)`` and ``F(a)(p)`` are one factor to the comparison."""
    left = sum_(F[a, i] * u(i) for i in Fin[n])
    right = sum_(u[i] * F(a)(i) for i in Fin[n])
    taken: set[str] = set()
    assert sums.orders(sums.spread(left, taken), sums.spread(right, taken)) == [(0,)]

