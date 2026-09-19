"""The @theorem theory: statements, native calls, and property tests."""

from __future__ import annotations

import pytest

from lanky import theorem
from lanky.ledger import Status
from lanky.plugins import registry
from lanky.prelude import Fin, Fn, Int, Nat
from lanky.theory import Theorem


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of 0 .. n is n * (n + 1)."""


def false_theorem() -> Theorem:
    """A deliberately false theorem, built inside a function.

    It lives here rather than at module level so that lanky's pytest plugin,
    which collects module-level theorems as test items, does not collect a
    statement this suite means to refute.
    """

    @theorem
    def wrong(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
        """False as soon as n is at least two."""

    return wrong


@theorem
def bounded(n: Nat, k: Int, h: k >= n) -> k + 1 > n:
    """A hypothesis restricts which draws count."""


def test_the_signature_is_the_statement() -> None:
    assert isinstance(gauss, Theorem)
    assert gauss.variables == (("n", Nat),)
    assert gauss.hypotheses == ()
    assert gauss.statement == "n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)"
    assert bounded.statement == "n : Nat, k : Int | k >= n |- k + 1 > n"


def test_the_decorator_registers_in_import_order() -> None:
    names = [obj.__name__ for obj in registry.objects if isinstance(obj, Theorem)]
    assert "gauss" in names
    assert names.index("gauss") < names.index("bounded")


def test_calling_a_theorem_evaluates_it_at_concrete_values() -> None:
    verdict = gauss(n=4)
    assert verdict.goal is True
    assert verdict.holds is True
    assert bool(verdict)
    assert false_theorem()(n=3).goal is False
    # a failed hypothesis means the statement is not violated
    verdict = bounded(n=3, k=0)
    assert verdict.hypotheses == {"h": False}
    assert verdict.hypotheses_hold is False
    assert verdict.holds is True
    with pytest.raises(TypeError, match="needs values for n"):
        gauss()


def test_a_true_theorem_passes_the_property_test() -> None:
    ok, counterexample = gauss.test(n=30)
    assert ok
    assert counterexample is None
    report = gauss.report(n=30)
    assert report.valid == 30


def test_a_false_theorem_returns_a_counterexample() -> None:
    ok, counterexample = false_theorem().test(n=30)
    assert not ok
    assert counterexample is not None
    assert counterexample["n"] not in (0, 1)


def test_hypotheses_filter_the_draws() -> None:
    report = bounded.report(n=20)
    assert report.ok
    assert 0 < report.valid <= 20
    assert report.samples > report.valid


def test_a_theorem_becomes_an_assumed_fact_until_an_oracle_speaks() -> None:
    fact = gauss.fact()
    # the id names the definition, not only the qualified name: module, name
    # and line, which is what keeps two same-named theorems apart in one ledger
    assert fact.id == f"theorem:{gauss.__module__}.gauss@{gauss.line}"
    assert fact.id == gauss.fact_id
    assert fact.kind == "theorem"
    assert fact.status is Status.ASSUMED
    assert fact.owner == "gauss"
    assert fact.where.startswith("test_theory.py:")
    assert fact.statement == gauss.statement


def test_the_closed_term_carries_binders_and_guard() -> None:
    term = bounded.term
    assert [var.name for var, _ in term.binders] == ["n", "k"]
    assert term.guard is not None


def test_families_are_sampled_as_tables() -> None:
    @theorem
    def head_is_smallest(
        n: Nat,
        f: Fn[Fin[n + 1], Nat],
        h0: f(0) == 0,
    ) -> f(0) <= f(n):
        """The sampler satisfies a definitional hypothesis rather than rejecting."""

    report = head_is_smallest.report(n=20)
    assert report.ok
    assert report.valid == 20


def test_the_lean_printer_is_not_here_yet() -> None:
    with pytest.raises(NotImplementedError):
        gauss.lean()
