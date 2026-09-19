"""The prelude: sorts, exactness, index types, families, refinement."""

from __future__ import annotations

import pytest

from lanky.prelude import (
    Bool,
    Fin,
    FinType,
    Fn,
    FnType,
    Int,
    Nat,
    Real,
    Refined,
    exactness_of,
)
from lanky.terms import Var, binders, evaluate, render


def test_exactness_classes() -> None:
    assert Nat.exactness == "exact"
    assert Int.exactness == "exact"
    assert Bool.exactness == "exact"
    assert Real.exactness == "approx"
    assert Real.reassoc.exactness == "reassoc"
    assert Real.exact.exactness == "exact"
    assert str(Real) == "Real"
    assert str(Real.reassoc) == "Real[reassoc]"
    with pytest.raises(ValueError, match="exactness"):
        Real.with_exactness("lossy")


def test_fin_iterates_concretely() -> None:
    assert list(Fin[4]) == [0, 1, 2, 3]
    assert len(Fin[4]) == 4
    assert Fin[4].is_concrete


def test_fin_yields_one_generic_point_when_symbolic() -> None:
    n = Var("n")
    domain = Fin[n * 2]
    assert not domain.is_concrete
    assert str(domain) == "Fin(n*2)"
    bound = binders(j for j in domain)
    assert [var.name for var, _ in bound] == ["j"]
    with pytest.raises(TypeError, match="symbolic"):
        list(domain)


def test_fin_points_are_enumerated_for_evaluation() -> None:
    n = Var("n")
    assert list(Fin[n + 1].points(lambda e: evaluate(e, {"n": 2}))) == [0, 1, 2]


def test_fn_is_a_family_type() -> None:
    n = Var("n")
    family = Fn[Fin[n], Nat]
    assert isinstance(family, FnType)
    assert family.domain == FinType(n)
    assert str(family) == "Fn[Fin(n), Nat]"
    assert exactness_of(Fn[Fin[n], Real]) == "approx"
    with pytest.raises(TypeError, match="two arguments"):
        Fn[Nat]


def test_refinement_with_and() -> None:
    n = Var("n")
    refined = Nat & (n > 0)
    assert isinstance(refined, Refined)
    assert refined.base is Nat
    assert render(refined.props[0]) == "n > 0"
    assert refined.holds({"n": 1})
    assert not refined.holds({"n": 0})
    chained = refined & (n < 10)
    assert len(chained.props) == 2
    assert str(chained) == "Nat & (n > 0) & (n < 10)"
    assert exactness_of(chained) == "exact"
