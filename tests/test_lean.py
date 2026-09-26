"""The Lean printer and the Lean oracle.

The printer is tested against golden source: what lanky sends to Lean is part of
the contract with the reader, not only with the elaborator, so the tests spell
the expected text out. The oracle is tested against a real Lean, and skips
cleanly when there is none, because a machine without Lean must still have a
green suite.
"""

from __future__ import annotations

import os
from collections.abc import Iterator
from pathlib import Path
from typing import NoReturn

import pytest

from lanky import theorem
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    check_applications,
    lean_type,
    print_lean,
    statement_of,
)
from lanky.ledger import Status
from lanky.oracles.lean import (
    LeanOracle,
    LeanSession,
    induction_scripts,
    tactic_ladder,
    use_tactic,
)
from lanky.prelude import Bool, Fin, FinType, Fn, Int, Nat, Real
from lanky.terms import Abs, Exists, Forall, Sum, Var

# {{{ terms to print

n = Var("n")
i = Var("i")
a = Var("a")
b = Var("b")
f = Var("f")


# }}}


# {{{ types


def test_scalar_sorts_print_as_core_lean_types() -> None:
    # A natural is an integer that is not negative: its variable is an Int,
    # and 0 ≤ n is a hypothesis (see the tests of the integer reading below).
    assert lean_type(Nat) == "Int"
    assert lean_type(Int) == "Int"
    assert lean_type(Bool) == "Bool"


def test_an_index_type_is_an_integer_with_bounds() -> None:
    # Fin[n] is not Fin n in Lean: its points are integers with both bounds as
    # guards, so that omega sees linear arithmetic and no coercion.
    assert lean_type(FinType(n)) == "Int"


def test_a_family_is_a_total_function() -> None:
    # A family is a function from Int; a natural value stays a Nat, which is
    # cast where it is used as a number.
    assert lean_type(Fn[Fin[n], Nat]) == "Int → Nat"
    assert lean_type(Fn[Fin[n], Fn[Fin[n], Int]]) == "Int → Int → Int"
    assert lean_type(Fn[Fin[n], Fin[n]]) == "Int → Nat"


def test_a_function_typed_domain_is_bracketed() -> None:
    """``→`` is right associative, so only a domain can need brackets.

    ``Fn[Fn[Fin[n], Nat], Nat]`` printed as ``Nat → Nat → Nat``, the type of a
    family of families, so a higher-order parameter applied to a family did not
    elaborate and a statement Lean could prove was left assumed. A refinement
    prints as its base, so a refined function-typed domain is bracketed too,
    and a function-typed codomain still needs nothing.
    """
    assert lean_type(Fn[Fn[Fin[n], Nat], Nat]) == "(Int → Nat) → Nat"
    assert lean_type(Fn[Fn[Fin[n], Nat] & (n > 0), Int]) == "(Int → Nat) → Int"
    assert lean_type(Fn[Fin[n], Fn[Fn[Fin[n], Nat], Nat]]) == "Int → (Int → Nat) → Nat"

    @theorem
    def higher_order(
        m: Nat,
        total: Fn[Fn[Fin[m], Nat], Nat],
        g: Fn[Fin[m], Nat],
    ) -> total(g) >= 0:
        """A family indexed by families, applied to one."""

    statement = statement_of(higher_order.term, "higher_order")
    assert statement.binders == (
        ("m", "Int"),
        ("total", "(Int → Nat) → Nat"),
        ("g", "Int → Nat"),
    )
    assert print_lean(higher_order.term) == (
        "∀ m : Int, 0 ≤ m → ∀ total : (Int → Nat) → Nat, ∀ g : Int → Nat, "
        "(total g : Int) ≥ 0"
    )


def test_real_has_no_core_lean_type() -> None:
    with pytest.raises(UnsupportedTerm):
        lean_type(Real)


# }}}


# {{{ expressions


def test_arithmetic_and_precedence() -> None:
    assert print_lean((a + b) * n) == "(a + b) * n"
    assert print_lean(a + b * n) == "a + b * n"
    assert print_lean(a**2 + 1) == "a ^ 2 + 1"
    assert print_lean(a // 2) == "a / 2"
    assert print_lean(a % 2) == "a % 2"
    assert print_lean(a // b) == "Int.fdiv a b"
    assert print_lean(a % b) == "Int.fmod a b"


def test_floor_division_rounds_the_way_python_does() -> None:
    """``//`` and ``%`` are Python's, which round toward negative infinity.

    ``Int.fdiv`` and ``Int.fmod`` are Lean's functions that do the same. A
    positive literal divisor is printed with Lean's ``/`` and ``%`` instead,
    which on ``Int`` are Euclidean and agree with floor division exactly when
    the divisor is positive, so ``omega`` can still reason about ``n // 2``.
    Any other divisor, a negative literal or zero included, gets ``Int.fdiv``:
    ``7 // -2`` is ``-4`` in Python, and Euclidean division says ``-3``.
    """
    assert print_lean((a + b) // 2) == "(a + b) / 2"
    assert print_lean(a // 2 * 2 <= a) == "(a / 2) * 2 ≤ a"
    assert print_lean(a // -2) == "Int.fdiv a (-2)"
    assert print_lean(a % -2) == "Int.fmod a (-2)"
    assert print_lean(a // 0) == "Int.fdiv a 0"
    assert print_lean((a + b) // (n + 1)) == "Int.fdiv (a + b) (n + 1)"
    assert print_lean(a // b * 2 <= a) == "Int.fdiv a b * 2 ≤ a"
    assert print_lean(f(a // b)) == "f (Int.fdiv a b)"


def test_subtraction_is_printed_as_written() -> None:
    # pymbolic has no subtraction node: a - b is a sum with (-1) * b in it, and
    # -1 is not a Nat, so the printer reads the negation back.
    assert print_lean(n - 1) == "n - 1"
    assert print_lean(a - b * n) == "a - b * n"


def test_comparisons_and_connectives() -> None:
    assert print_lean(a == b) == "a = b"
    assert print_lean(a != b) == "a ≠ b"
    assert print_lean(a <= b) == "a ≤ b"
    assert print_lean(a >= b) == "a ≥ b"
    assert print_lean((a < b) & (b < n)) == "a < b ∧ b < n"
    assert print_lean((a < b) | (b < n)) == "a < b ∨ b < n"
    assert print_lean(~(a < b)) == "¬(a < b)"


def test_a_family_is_applied_not_subscripted() -> None:
    assert print_lean(f(a)) == "f a"
    assert print_lean(f(a + 1)) == "f (a + 1)"
    assert print_lean(f[a]) == "f a"


def test_a_bounded_quantifier_is_a_guarded_int_quantifier() -> None:
    assert print_lean(Forall(((i, FinType(n)),), f(i) <= n)) == (
        "∀ i : Int, 0 ≤ i → i < n → f i ≤ n"
    )
    assert print_lean(Forall(((i, Nat),), f(i) <= n)) == "∀ i : Int, 0 ≤ i → f i ≤ n"
    assert print_lean(Forall(((i, Int),), f(i) <= n)) == "∀ i : Int, f i ≤ n"


def test_an_existential_conjoins_its_guard() -> None:
    assert print_lean(Exists(((i, FinType(n)),), f(i) == 0)) == (
        "∃ i : Int, 0 ≤ i ∧ i < n ∧ f i = 0"
    )


def test_a_generator_guard_follows_the_last_binder() -> None:
    term = Forall(((a, FinType(n)), (b, FinType(n))), f(a) <= f(b), a <= b)
    assert print_lean(term) == (
        "∀ a : Int, 0 ≤ a → a < n → ∀ b : Int, 0 ≤ b → b < n → a ≤ b → f a ≤ f b"
    )


def test_a_reduction_needs_mathlib() -> None:
    with pytest.raises(UnsupportedTerm, match="Finset"):
        print_lean(Sum(((i, FinType(n)),), i))


def test_an_absolute_value_needs_mathlib() -> None:
    with pytest.raises(UnsupportedTerm, match="Mathlib"):
        print_lean(Abs(a))


def test_true_division_needs_a_field() -> None:
    with pytest.raises(UnsupportedTerm, match="field"):
        print_lean(a / b)


# }}}


# {{{ statements


@theorem
def commutes(x: Nat, y: Nat) -> x + y == y + x:
    """Addition on the naturals commutes."""


@theorem
def below(m: Nat, j: Fin[m]) -> j < m + 1:
    """A point of an index type is below the next bound."""


@theorem
def scan_monotone(
    size: Nat,
    cnt: Fn[Fin[size], Nat],
    off: Fn[Fin[size + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
) -> all(off(p) <= off(q) for p in Fin[size + 1] for q in Fin[size + 1] if p <= q):
    """The offsets of an exclusive scan over counts are monotone."""


@theorem
def gauss(size: Nat) -> 2 * sum(k for k in Fin[size + 1]) == size * (size + 1):
    """Gauss's schoolboy sum, which core Lean cannot even state."""


def test_a_statement_becomes_lean_binders_and_hypotheses() -> None:
    statement = statement_of(commutes.term, "commutes")
    assert statement.binders == (("x", "Int"), ("y", "Int"))
    assert statement.hypotheses == (("h0", "0 ≤ x"), ("h1", "0 ≤ y"))
    assert statement.goal == "x + y = y + x"
    # each binder's guard follows it, as it does in print_lean
    assert statement.source("omega") == (
        "theorem commutes (x : Int) (h0 : 0 ≤ x) (y : Int) (h1 : 0 ≤ y) : "
        "x + y = y + x := by\n  omega\n"
    )


def test_an_index_typed_variable_carries_its_bounds_as_hypotheses() -> None:
    statement = statement_of(below.term, "below")
    assert statement.binders == (("m", "Int"), ("j", "Int"))
    assert statement.hypotheses == (("h0", "0 ≤ m"), ("h1", "0 ≤ j"), ("h2", "j < m"))
    assert statement.goal == "j < m + 1"


def test_the_scan_statement_prints_as_a_lean_theorem() -> None:
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert statement.source("omega").splitlines()[0] == (
        "theorem scan_monotone (size : Int) (h0 : 0 ≤ size) (cnt : Int → Nat) "
        "(off : Int → Nat) (h1 : (off 0 : Int) = 0) "
        "(h2 : ∀ r : Int, 0 ≤ r → r < size → "
        "(off (r + 1) : Int) = (off r : Int) + (cnt r : Int)) : "
        "∀ p : Int, 0 ≤ p → p < size + 1 → ∀ q : Int, 0 ≤ q → q < size + 1 → "
        "p ≤ q → (off p : Int) ≤ (off q : Int) := by"
    )


def test_a_quantified_hypothesis_is_parenthesized_in_the_proposition() -> None:
    # To the left of an arrow a quantifier needs brackets; in binder syntax it
    # does not, which is why the proposition is rendered rather than pasted.
    proposition = statement_of(scan_monotone.term, "scan_monotone").proposition
    assert (
        "(∀ r : Int, 0 ≤ r → r < size → "
        "(off (r + 1) : Int) = (off r : Int) + (cnt r : Int)) →"
    ) in proposition
    assert proposition == print_lean(scan_monotone.term)
    # and a binder's own guard sits next to it in both
    for term in (commutes.term, below.term):
        assert statement_of(term, "t").proposition == print_lean(term)


def test_a_theorem_prints_itself() -> None:
    assert commutes.lean() == "∀ x : Int, 0 ≤ x → ∀ y : Int, 0 ≤ y → x + y = y + x"


def test_a_reduction_statement_is_declined_by_the_printer() -> None:
    with pytest.raises(UnsupportedTerm):
        gauss.lean()


@theorem
def within_bounds(m: Nat, g: Fn[Fin[m], Nat]) -> all(g(k) >= 0 for k in Fin[m]):
    """A family applied inside its domain, under a quantifier of its own."""


@theorem
def _outside_bounds(m: Nat, g: Fn[Fin[m], Nat]) -> g(m) == g(m):
    """A family applied at ``m``, which is one point past its domain.

    Erased to a total ``Nat -> Nat`` this is a Lean tautology, and lanky's own
    types say ``g`` has no value there at all. The name is private so that the
    pytest plugin does not collect a statement that decides nothing.
    """


def test_an_application_outside_its_domain_is_declined() -> None:
    """The erasure of a family to a total function is sound only in bounds.

    ``Fn[Fin[m], Nat]`` prints as ``Nat -> Nat`` and the bound lives in the
    guards, which says exactly nothing about ``g m``. Lean would prove the
    tautology, the property tester has no value to compare, and the ledger
    would read ``proved``, so the printer refuses the statement instead.
    """
    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(_outside_bounds.term)
    with pytest.raises(UnsupportedTerm, match="Fin\\(m\\)"):
        statement_of(_outside_bounds.term, "outside_bounds")
    oracle = LeanOracle(session=LeanSession())
    assert not oracle.can_establish(_outside_bounds.fact())


def test_an_application_inside_its_domain_still_prints() -> None:
    """The check has to leave the statements the project exists for alone.

    ``off(r + 1)`` against an ``off : Fn[Fin[size + 1], Nat]`` with ``r`` in
    ``Fin[size]`` is in bounds because ``r < size``, which is affine arithmetic
    and not a proof search.
    """
    check_applications(scan_monotone.term)
    assert "(off (r + 1) : Int)" in print_lean(scan_monotone.term)
    assert print_lean(within_bounds.term) == (
        "∀ m : Int, 0 ≤ m → ∀ g : Int → Nat, ∀ k : Int, 0 ≤ k → k < m → (g k : Int) ≥ 0"
    )


def test_an_argument_that_could_be_negative_is_declined_too() -> None:
    """``Fin`` starts at zero, so an ``Int`` index has two bounds to clear.

    Nothing here says ``k`` is not ``-1``, and a family erased to ``Int → Nat``
    would be applied at a point the domain does not have on that side either.
    Only a hypothesis would rule it out, and the check is affine arithmetic
    over the binders rather than a solver, so it declines.
    """

    @theorem
    def signed(size: Nat, k: Int, fam: Fn[Fin[size], Nat]) -> fam(k) == fam(k):
        """An Int index into a Fin domain."""

    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(signed.term)


def test_an_open_term_has_no_domain_to_leave() -> None:
    """Only a family the statement itself declares is checked.

    ``f`` here is a free variable of an open term, so there is nothing that
    says what its domain is and nothing to refuse.
    """
    assert print_lean(Forall(((i, FinType(n)),), f(i + 3) <= n)) == (
        "∀ i : Int, 0 ≤ i → i < n → f (i + 3) ≤ n"
    )
    check_applications(f(n + 100))


@theorem
def chained_in_bounds(grid: Fn[Fin[1], Fn[Fin[1], Nat]]) -> grid(0)(0) == grid(0)(0):
    """A family of families, applied twice and in bounds at both levels."""


@theorem
def _chained_out_of_bounds(grid: Fn[Fin[1], Fn[Fin[1], Nat]]) -> grid(0)(1) == grid(0)(1):
    """The same shape with the *outer* application one point past its domain.

    ``grid(0)`` is a family over ``Fin[1]`` in lanky and a total ``Int → Nat``
    in Lean, so ``grid(0)(1)`` is a Lean tautology about a value the statement does
    not have. The name is private so that the pytest plugin does not collect a
    statement that decides nothing.
    """


@theorem
def _applied_more_often_than_its_type(row: Fn[Fin[1], Nat]) -> row(0)(0) == row(0)(0):
    """A family applied twice though its type takes one argument.

    Printed it would be ``row 0 0`` for a ``row : Int → Nat``, which Lean will
    not elaborate, so the honest answer is to decline it here.
    """


def test_a_chained_application_is_checked_at_every_level() -> None:
    """A family whose codomain is a family is applied again, and that counts.

    Reading only the innermost call left the outer argument unchecked, while
    the erasure of ``Fn[Fin[1], Fn[Fin[1], Nat]]`` to a total ``Int → Int →
    Nat`` says nothing about it: Lean proved the reflexive statement and the
    property tester had no entry to compare. Every level is now discharged
    against its own ``Fin`` bound.
    """
    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(_chained_out_of_bounds.term)
    with pytest.raises(UnsupportedTerm, match="Fin\\(1\\)"):
        statement_of(_chained_out_of_bounds.term, "chained_out_of_bounds")
    oracle = LeanOracle(session=LeanSession())
    assert not oracle.can_establish(_chained_out_of_bounds.fact())
    with pytest.raises(UnsupportedTerm, match="more times than its type"):
        print_lean(_applied_more_often_than_its_type.term)


def test_a_chained_application_in_bounds_still_prints() -> None:
    """And the check costs a chain that stays in bounds nothing."""
    check_applications(chained_in_bounds.term)
    assert print_lean(chained_in_bounds.term) == (
        "∀ grid : Int → Int → Nat, (grid 0 0 : Int) = (grid 0 0 : Int)"
    )


@theorem
def _over_a_refined_domain(fam: Fn[Fin[1] & False, Nat]) -> fam(0) == fam(0):
    """A family over a domain a refinement empties, applied at ``0``.

    ``Fin[1] & False`` has no points at all, so lanky has no value to compare
    and the tester cannot even tabulate the family; stripping the refinement to
    its base made ``0`` look like a point of it and turned the statement into a
    reflexive Lean theorem over a total function.
    """


def test_a_refined_family_domain_is_declined() -> None:
    """The erasure keeps the ``Fin`` bound as a guard and the refinement not at all.

    Discharging the predicate would need a solver rather than the affine
    reading of the binders this module does, so an application over a refined
    domain is refused instead of approximated by its base.
    """
    with pytest.raises(UnsupportedTerm, match="refined domain"):
        print_lean(_over_a_refined_domain.term)
    with pytest.raises(UnsupportedTerm, match="refined domain"):
        statement_of(_over_a_refined_domain.term, "over_a_refined_domain")
    oracle = LeanOracle(session=LeanSession())
    assert not oracle.can_establish(_over_a_refined_domain.fact())


@theorem
def _impossible_refinement(
    m: Nat,
    g: Fn[Fin[m], Nat],
    k: Nat & (g(m) != g(m)),
) -> 1 == 2:
    """A binder refined by a proposition about a point ``g`` does not have.

    ``g m`` is out of the declared domain, so lanky has no value for it, while
    Lean reads the refinement as the hypothesis ``g m ≠ g m`` on a total
    function and derives anything at all from it.
    """


def test_an_application_in_a_refinement_predicate_is_checked() -> None:
    """A domain carries expressions, and Lean elaborates every one of them.

    The checker used to visit only a domain's ``Fin`` bound, so an application
    inside a refinement predicate was never discharged and an impossible
    hypothesis about an erased point proved a false goal.
    """
    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(_impossible_refinement.term)
    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        statement_of(_impossible_refinement.term, "impossible_refinement")
    oracle = LeanOracle(session=LeanSession())
    assert not oracle.can_establish(_impossible_refinement.fact())


def test_a_refinement_whose_applications_are_in_bounds_still_prints() -> None:
    """And a predicate that stays inside the domain goes through as before.

    The predicate is checked with its own binder in scope, because that is what
    it talks about and because the base's guard (``k < m``) is printed ahead of
    it and stands as its antecedent.
    """

    @theorem
    def refined_index(
        m: Nat,
        g: Fn[Fin[m], Nat],
        k: Fin[m] & (g(k) == 0),
    ) -> g(k) == 0:
        """``g`` is applied at ``k``, which its own domain bounds."""

    check_applications(refined_index.term)
    assert print_lean(refined_index.term) == (
        "∀ m : Int, 0 ≤ m → ∀ g : Int → Nat, ∀ k : Int, 0 ≤ k → k < m → "
        "(g k : Int) = 0 → (g k : Int) = 0"
    )


@theorem
def _captured_binder(i: Nat) -> all(i > 0 for i in Fin[i]):
    """A binder whose own domain names the parameter it shadows.

    ``Fin[i]`` is evaluated before the generator binds its ``i``, so it is the
    parameter's ``i`` and the statement is false at ``i = 1``. Printed with the
    guard after the binder it is ``∀ i : Nat, i < i → i > 0``, which is
    vacuous. The name is private so that the pytest plugin does not collect a
    false statement.
    """


def test_a_binder_that_captures_a_name_its_domain_mentions_is_declined() -> None:
    """The printed guard would bind a name Python had already resolved.

    The translation was a different statement, vacuously true, and with Lean
    on the machine the ledger read ``proved`` for a false claim, with no
    semantics note to trigger a cross-check. It is declined now, and the
    tester, which reads the domain the way Python does, refutes it.
    """
    with pytest.raises(UnsupportedTerm, match="captures"):
        print_lean(_captured_binder.term)
    with pytest.raises(UnsupportedTerm, match="captures"):
        statement_of(_captured_binder.term, "captured_binder")
    oracle = LeanOracle(session=LeanSession())
    assert not oracle.can_establish(_captured_binder.fact())
    with pytest.raises(UnsupportedTerm, match="captures"):
        print_lean(Exists(((i, FinType(i)),), i == 0))

    from lanky.oracles.test import TestOracle

    refuted = TestOracle(samples=20).establish(_captured_binder.fact())
    assert refuted is not None
    assert refuted.status is Status.REFUTED
    assert refuted.provenance["counterexample"]["i"] >= 1


def test_a_binder_that_captures_nothing_still_prints() -> None:
    """A fresh name, a shadowing that is not a capture, and a refinement of its own.

    A refinement's predicates are about the variable being bound, so ``k`` in
    ``Fin[m] & (k > 0)`` is not a capture; nor is an inner ``i`` whose domain
    does not mention the outer one it shadows.
    """

    @theorem
    def fresh(m: Nat) -> all(j >= 0 for j in Fin[m]):
        """The same shape as the captured one, with a name of its own."""

    assert print_lean(fresh.term) == "∀ m : Int, 0 ≤ m → ∀ j : Int, 0 ≤ j → j < m → j ≥ 0"
    shadowing = Forall(((i, FinType(n)),), Exists(((i, FinType(1)),), i == 0))
    assert print_lean(shadowing) == (
        "∀ i : Int, 0 ≤ i → i < n → ∃ i : Int, 0 ≤ i ∧ i < 1 ∧ i = 0"
    )
    k = Var("k")
    refined = Forall(((k, Fin[n] & (k > 0)),), k < n)
    assert print_lean(refined) == "∀ k : Int, 0 ≤ k → k < n → k > 0 → k < n"


def test_a_closed_boolean_statement_prints_as_a_proposition() -> None:
    """``-> 1 == 2`` is the Prop ``False``, not the ``Bool`` literal ``false``.

    The literal elaborates as a proposition only through the Bool-to-Prop
    coercion, which is a second reading of a statement that has one. In a value
    position the literal is still what is printed.
    """
    assert print_lean(False) == "False"
    assert print_lean(True) == "True"
    assert print_lean(Forall((), False, Var("p") > 1)) == "p > 1 → False"
    assert print_lean(f(a) == True) == "f a = true"  # noqa: E712 - the point of it


def test_a_binderless_statement_keeps_its_hypotheses() -> None:
    """A theorem whose only parameters are hypotheses is still an implication.

    Its term is a ``Forall`` with an empty binder tuple, and both the printer
    and the statement arranger have to carry the guard: dropping it would print
    a strictly stronger claim than the one that was written.
    """
    from lanky.terms import Forall, Var

    term = Forall((), Var("p") > 0, Var("p") > 1)
    assert print_lean(term) == "p > 1 → p > 0"

    statement = statement_of(term, "binderless")
    assert statement.binders == ()
    assert statement.hypotheses == (("h0", "p > 1"),)
    assert statement.goal == "p > 0"


# }}}


# {{{ one reading of arithmetic, the integer one


def _make_truncated():
    """``n - 1 >= 0`` over ``Nat``: true only where subtraction truncates.

    Built inside a function because it is false, at ``n = 0``, and a
    module-level theorem is collected and run by lanky's own pytest plugin.
    """

    @theorem
    def truncated(n: Nat) -> n - 1 >= 0:
        """False at n = 0, which Lean has to see as well."""

    return truncated


_truncated = _make_truncated()


@theorem
def one_below(m: Nat) -> m - 1 <= m:
    """True in the integer reading, so Lean still proves it."""


def test_a_natural_is_an_integer_with_its_bound_as_a_hypothesis() -> None:
    """The statement Lean gets is the one the property tester runs.

    A ``Nat`` used to print as a Lean ``Nat``, whose subtraction truncates at
    zero, so Lean proved ``n - 1 >= 0`` while the tester refuted it at
    ``n = 0`` and ``lanky check`` exited 0 or 1 depending on whether Lean was
    installed. A natural is now an ``Int`` with ``0 ≤ n`` as a hypothesis, and
    ``n - 1`` is integer subtraction in both readings.
    """
    assert print_lean(_truncated.term) == "∀ n : Int, 0 ≤ n → n - 1 ≥ 0"
    statement = statement_of(_truncated.term, "truncated")
    assert statement.source("omega").splitlines()[0] == (
        "theorem truncated (n : Int) (h0 : 0 ≤ n) : n - 1 ≥ 0 := by"
    )
    assert print_lean(one_below.term) == "∀ m : Int, 0 ≤ m → m - 1 ≤ m"


def test_a_natural_value_is_cast_where_it_is_a_number() -> None:
    """A family's natural values stay ``Nat`` and are cast to ``Int`` where used.

    ``off(r + 1) - off(r)`` is integer subtraction under the tester, which
    draws the table's entries as Python integers, so it has to be integer
    subtraction in Lean too: every application of a family with natural values
    is written ``(f x : Int)``. A family with integer values needs no cast, a
    partial application of a family of families is a function and gets none,
    and a family nothing binds, in an open term, is left as written.
    """

    @theorem
    def steps(
        size: Nat,
        off: Fn[Fin[size + 1], Nat],
        shift: Fn[Fin[size], Int],
    ) -> all(off(r + 1) - off(r) + shift(r) >= shift(r) - off(r) for r in Fin[size]):
        """Arithmetic on natural values, and on integer ones."""

    assert print_lean(steps.term) == (
        "∀ size : Int, 0 ≤ size → ∀ off : Int → Nat, ∀ shift : Int → Int, "
        "∀ r : Int, 0 ≤ r → r < size → "
        "(off (r + 1) : Int) - (off r : Int) + shift r ≥ shift r - (off r : Int)"
    )

    @theorem
    def rows(grid: Fn[Fin[2], Fn[Fin[3], Nat]], pick: Fn[Fn[Fin[3], Nat], Nat]) -> (
        pick(grid(1)) >= grid(1)(2)
    ):
        """A family of families, and one applied to a family."""

    assert print_lean(rows.term) == (
        "∀ grid : Int → Int → Nat, ∀ pick : (Int → Nat) → Nat, "
        "(pick (grid 1) : Int) ≥ (grid 1 2 : Int)"
    )


def test_a_family_over_the_naturals_is_applied_only_at_naturals() -> None:
    """A family over ``Nat`` is a function from ``Int`` too, so ``-1`` is a point.

    ``f(n - 1)`` at ``n = 0`` names a value the family does not have. With a
    ``Nat`` domain Lean used to truncate the argument to ``0``; with an ``Int``
    one it would reason about ``f (-1)``. Either way it is not the statement
    lanky holds, so an argument has to be shown non-negative from the binders,
    the way an argument into ``Fin`` has to be shown in bounds.
    """

    @theorem
    def _before(n: Nat, f: Fn[Nat, Nat]) -> f(n - 1) == f(n - 1):
        """One point before n, which is -1 at n = 0."""

    @theorem
    def at_n(n: Nat, f: Fn[Nat, Nat]) -> f(n + 1) >= f(n) - f(n):
        """Points the family has, whatever n is."""

    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(_before.term)
    assert print_lean(at_n.term) == (
        "∀ n : Int, 0 ≤ n → ∀ f : Int → Nat, "
        "(f (n + 1) : Int) ≥ (f n : Int) - (f n : Int)"
    )


def test_a_natural_value_is_a_point_of_a_family_over_the_naturals() -> None:
    """``g(f(i))`` is not affine, and ``f(i)`` is a ``Nat`` all the same.

    The affine check cannot read an application, so a family over ``Nat``
    applied to another family's value was declined, though the value is a
    natural in the printed source as in the lanky statement. An argument that
    only lands in ``Nat`` because it is an ``Int`` expression of such values,
    ``f(i) - 1``, is still declined.
    """

    @theorem
    def composed(n: Nat, f: Fn[Fin[n], Nat], g: Fn[Nat, Nat]) -> all(
        g(f(i)) >= 0 for i in Fin[n]
    ):
        """g is applied at points it has."""

    @theorem
    def _shifted(n: Nat, f: Fn[Fin[n], Nat], g: Fn[Nat, Nat]) -> all(
        g(f(i) - 1) >= 0 for i in Fin[n]
    ):
        """g is applied at -1 wherever f is 0."""

    assert print_lean(composed.term) == (
        "∀ n : Int, 0 ≤ n → ∀ f : Int → Nat, ∀ g : Int → Nat, "
        "∀ i : Int, 0 ≤ i → i < n → (g (f i : Int) : Int) ≥ 0"
    )
    with pytest.raises(UnsupportedTerm, match="outside the domain"):
        print_lean(_shifted.term)


def test_an_exponent_is_a_natural() -> None:
    """Lean's ``^`` on ``Int`` takes a ``Nat``, and a natural variable is an ``Int``.

    A literal elaborates as it is; a natural variable is given as ``n.toNat``,
    which is ``n`` under its own ``0 ≤ n``; a family's natural value is a
    ``Nat`` already; anything else could be negative, where Python's ``**`` is
    a float, and is declined.
    """

    @theorem
    def powers(k: Int, m: Nat, f: Fn[Fin[1], Nat]) -> k**m * k**2 == k ** (m + 2) + 2 ** f(0):
        """Three exponents Lean can take and one it cannot."""

    with pytest.raises(UnsupportedTerm, match="exponent"):
        print_lean(powers.term)

    @theorem
    def fine(k: Int, m: Nat, f: Fn[Fin[1], Nat]) -> k**m * k**2 >= 2 ** f(0) - 2 ** f(0):
        """The three it can."""

    assert print_lean(fine.term) == (
        "∀ k : Int, ∀ m : Int, 0 ≤ m → ∀ f : Int → Nat, "
        "k ^ m.toNat * k ^ 2 ≥ (2 : Int) ^ f 0 - (2 : Int) ^ f 0"
    )
    with pytest.raises(UnsupportedTerm, match="exponent"):
        print_lean(Forall(((a, Int),), a**a >= 0))


def _make_power_below_one():
    """``1 - 2 ** m >= 0`` over ``Nat``: false at ``m = 1``, true only in ``Nat``.

    Built inside a function because it is false, and a module-level theorem is
    collected and run by lanky's own pytest plugin.
    """

    @theorem
    def power_below_one(m: Nat) -> 1 - 2**m >= 0:
        """Its variable is only in the exponent, so nothing else types the numerals."""

    return power_below_one


_power_below_one = _make_power_below_one()


def test_a_literal_base_is_an_integer() -> None:
    """A numeral with no typed neighbour is a ``Nat`` to Lean, so a literal base is not.

    ``m`` appears only in the exponent, as ``m.toNat``, which is a ``Nat``. Printed
    as ``1 - 2 ^ m.toNat ≥ 0`` every numeral in the statement defaulted to
    ``Nat``, whose subtraction truncates, so Lean proved a claim Python refutes
    at ``m = 1``, and ``lanky check`` exited 0 with Lean and 1 without, which
    is #6 again. The ascription makes it integer arithmetic; a base that is not
    a literal is typed by what is in it and is left alone.
    """
    assert print_lean(_power_below_one.term) == "∀ m : Int, 0 ≤ m → 1 - (2 : Int) ^ m.toNat ≥ 0"
    assert print_lean(Forall(((n, Nat),), (-1) ** n <= 1)) == (
        "∀ n : Int, 0 ≤ n → (-1 : Int) ^ n.toNat ≤ 1"
    )
    assert print_lean(Forall(((n, Nat),), (n + 1) ** n >= 1)) == (
        "∀ n : Int, 0 ≤ n → (n + 1) ^ n.toNat ≥ 1"
    )


# }}}


# {{{ the tactic ladder, without Lean


def test_the_ladder_starts_cheap_and_ends_with_an_induction() -> None:
    ladder = tactic_ladder(statement_of(scan_monotone.term, "scan_monotone"))
    assert ladder[:5] == ["omega", "decide", "simp", "simp_all", "simp_all <;> omega"]
    script = ladder[-2]
    # The strategy is read off the statement: q is the variable the guard p <= q
    # makes reachable by steps, p is what the successor case splits against, and
    # h2 is the recurrence to instantiate, at a point of Fin, so with two
    # guards to discharge. q is an Int with 0 ≤ q as hd_2, and it is traded for
    # the natural it is before anything is induced on.
    assert "intro p hd hd_1 q hd_2 hd_3 hg" in script
    assert "obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hd_2" in script
    assert "induction q with" in script
    assert "by_cases hlt : (k : Int) < p" in script
    assert "have hstep := h2 k (by omega) (by omega)" in script


def test_a_variable_that_is_not_a_natural_is_not_induced_on() -> None:
    """An ``Int`` has no lower bound to start an induction from.

    The strategy trades a natural for a ``Nat`` through its ``0 ≤ b``
    hypothesis, and an ``Int`` variable has none, so the ladder stops at the
    cheap attempts rather than emitting a script that cannot elaborate.
    """
    k = Var("k")
    term = Forall(((n, Nat),), Forall(((k, Int),), k + n >= k))
    assert induction_scripts(statement_of(term, "t")) == []
    natural = Forall(((n, Nat),), Forall(((k, Nat),), k + n >= k))
    (script,) = induction_scripts(statement_of(natural, "t"))
    assert "obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd" in script


def test_the_ladder_renders_a_goal_bound_with_the_binders_in_scope() -> None:
    """``Fin[2 ** n]`` in the goal needs to know that ``n`` is a natural.

    The ladder counts each goal binder's guards by rendering them, and it used
    to render them with nothing in scope, so ``n.toNat`` could not be printed
    and the ladder raised for a statement the printer had printed; the oracle
    loop swallowed that, and Lean was never asked. A bounded hypothesis over
    such a domain is counted the same way.
    """
    j = Var("j")
    goal = Forall(((i, FinType(2**n)),), i >= 0)
    ladder = tactic_ladder(statement_of(Forall(((n, Nat),), goal), "t"))
    assert "intro i hd hd_1\nfirst | omega" in ladder[5]
    hypothesis = Forall(((j, FinType(2**n)),), j < 2**n)
    (script,) = induction_scripts(statement_of(Forall(((n, Nat),), goal, hypothesis), "t"))
    assert "have hstep := h1 k (by omega) (by omega)" in script


def test_a_statement_with_no_quantified_goal_has_only_the_cheap_ladder() -> None:
    assert tactic_ladder(statement_of(commutes.term, "commutes")) == [
        "omega",
        "decide",
        "simp",
        "simp_all",
        "simp_all <;> omega",
    ]


def test_the_oracle_declines_what_it_cannot_print() -> None:
    oracle = LeanOracle(session=LeanSession())
    assert oracle.trust_class() == "kernel"
    assert oracle.can_establish(scan_monotone.fact())
    assert not oracle.can_establish(gauss.fact())


def test_a_disabled_oracle_is_a_clean_no_op(monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    assert not available
    assert "LANKY_LEAN_DISABLE" in reason
    fact = scan_monotone.fact()
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert reason in result.provenance["lean_declined"]


def test_without_lean_on_the_path_the_oracle_explains_itself(monkeypatch) -> None:
    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    monkeypatch.setenv("PATH", "")
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    assert not available
    assert reason == "lean is not on PATH"


def test_availability_does_not_claim_a_repl_it_has_not_built(monkeypatch) -> None:
    """The cheap question is cheap, and the answer says what it did not ask.

    ``lean`` on the PATH and a driver that imports is all this checks; whether
    a REPL can be built is discovered on the first fact. Reporting a bare
    "available" would be a promise the oracle cannot keep, so the line says it
    has not been tested yet.
    """
    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    if not available:  # no Lean here, so nothing to overstate
        assert reason
        _without_lean(f"no Lean oracle here: {reason}")
    assert "untested until the first fact" in reason
    # and the line the CLI prints carries that reason rather than dropping it
    from lanky.check import oracle_lines

    (line,) = [one for one in oracle_lines() if one.startswith("lean ")]
    assert line.startswith("lean (kernel): available (") or "unavailable" in line


def test_the_repl_cache_is_outside_the_virtual_environment(monkeypatch) -> None:
    """A reinstall of the driver must not throw away a built REPL.

    lean-interact's own default is a directory inside its installed package,
    which any ``uv sync`` that reinstalls it deletes, costing another build.
    """
    from lanky.oracles.lean import default_cache_dir

    monkeypatch.delenv("LANKY_LEAN_CACHE_DIR", raising=False)
    monkeypatch.setenv("XDG_CACHE_HOME", "/tmp/xdg")
    assert default_cache_dir() == "/tmp/xdg/lanky/lean-repl"
    assert LeanSession().cache_dir == "/tmp/xdg/lanky/lean-repl"

    monkeypatch.delenv("XDG_CACHE_HOME", raising=False)
    assert default_cache_dir().endswith("/.cache/lanky/lean-repl")

    monkeypatch.setenv("LANKY_LEAN_CACHE_DIR", "/tmp/chosen")
    assert default_cache_dir() == "/tmp/chosen"
    assert "site-packages" not in default_cache_dir()


def test_an_unavailable_oracle_is_named_in_the_check_report(monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    import lanky.oracles  # noqa: F401 - registers the built-in oracles
    from lanky.check import oracle_lines

    lines = [line for line in oracle_lines() if line.startswith("lean ")]
    assert lines == ["lean (kernel): unavailable: disabled by LANKY_LEAN_DISABLE"]


def test_a_pinned_tactic_reaches_the_registered_oracle() -> None:
    from lanky.plugins import registry

    use_tactic(commutes, "omega")
    # the pin is keyed by the fact id, which names the definition and not only
    # the qualified name, so two same-named theorems cannot share a script
    assert commutes.fact().id == commutes.fact_id
    pinned = [
        oracle.tactics.get(commutes.fact_id)
        for oracle in registry.oracles
        if isinstance(oracle, LeanOracle)
    ]
    assert pinned == ["omega"]


ROOT = Path(__file__).resolve().parent.parent

#: The command both documents show the ledger of, as the quickstart spells it.
CHECK_GAUSS = "uv run lanky check examples/gauss.py"


def _printed_after(document: str, command: str) -> list[str]:
    """What a console block in ``document`` shows ``$ command`` printing.

    The lines after the prompt, up to the next prompt or the end of the block,
    without the trailing spaces a Markdown file does not keep. A comment after
    the command is not part of it.
    """
    lines = (ROOT / document).read_text(encoding="utf-8").splitlines()
    starts = [
        index for index, line in enumerate(lines) if line.split("#")[0].strip() == f"$ {command}"
    ]
    assert starts, f"{document} no longer shows `$ {command}`"
    shown = []
    for line in lines[starts[0] + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line.rstrip())
    return shown


def _check_gauss(capsys) -> list[str]:
    """``lanky check examples/gauss.py``, as the lines it prints."""
    from lanky import cli

    assert cli.main(["check", str(ROOT / "examples" / "gauss.py")]) == 0
    return [line.rstrip() for line in capsys.readouterr().out.splitlines()]


def _abridges(shown: str, printed: str, statement_at: int) -> bool:
    """Whether a line of the README's table is the printed one, or it trimmed to fit.

    The README ends a row whose statement it trimmed in ``...``, and shortens
    the rule under the header to the same width. Only the statement column is
    trimmed: what comes before ``statement_at``, where that column starts, is
    kept whole, so a row cannot shed its status, location or owner and still
    count as the printed one.
    """
    if shown == printed:
        return True
    if shown.endswith("..."):
        kept = shown.removesuffix("...")
    elif set(shown) <= {"-", " "}:
        kept = shown
    else:
        return False
    return len(kept) > statement_at and printed.startswith(kept)


def _assert_abridged(readme: list[str], printed: list[str]) -> None:
    """The README's table is the printed one, row for row, each whole or trimmed."""
    assert len(readme) == len(printed), (readme, printed)
    statement_at = printed[0].index("STATEMENT")
    for shown, line in zip(readme, printed, strict=True):
        assert _abridges(shown, line, statement_at), (shown, line)


def _read_as_tested(line: str) -> str:
    """A line of the documented table as a machine without Lean prints it."""
    return line.replace(f"proved  {'lean':13}", f"tested  {'property-test':13}").replace(
        "2 facts: 1 proved, 1 tested", "2 facts: 2 tested"
    )


def test_an_abridged_row_keeps_every_column_but_the_statement() -> None:
    """The README check accepts a trimmed statement and nothing looser.

    A row cut back to ``...``, a row whose location moved, and a rule longer
    than the printed one are not what the check printed, so they must not pass
    for it.
    """
    header = "STATUS  BY    WHERE        OWNER  STATEMENT"
    rule = "------  ----  -----------  -----  ---------------------"
    row = "proved  lean  gauss.py:39  scan   n : Nat |- n + 0 == n"
    at = header.index("STATEMENT")
    assert _abridges(row, row, at)
    assert _abridges(row[:-6] + "...", row, at)
    assert _abridges(rule[:-8], rule, at)
    assert _abridges("", "", at)

    assert not _abridges("...", row, at)
    assert not _abridges(row[: at - 2] + "...", row, at)
    assert not _abridges(row.replace(":39", ":40")[:-6] + "...", row, at)
    assert not _abridges(row[:-6], row, at)
    assert not _abridges(rule + "---", rule, at)
    assert not _abridges("", row, at)


def test_without_lean_the_documented_ledger_reads_tested(monkeypatch, capsys) -> None:
    """On a machine without Lean the README's ``proved lean`` row reads ``tested``.

    That is the README's other claim about the table: the status column changes
    and nothing else does, the exit code included. The columns keep their
    widths, because the property tester decided the other row already. Both
    documents are held to it, so the README's rows are checked here too and not
    only where Lean is installed.
    """
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    printed = _check_gauss(capsys)
    quickstart = _printed_after("docs/quickstart.md", CHECK_GAUSS)
    assert printed == [_read_as_tested(line) for line in quickstart]
    readme = _printed_after("README.md", "lanky check examples/gauss.py")
    _assert_abridged([_read_as_tested(line) for line in readme], printed)


# }}}


# {{{ the oracle, with Lean


def _without_lean(reason: str) -> NoReturn:
    """Skip a test that needs Lean, or fail it where Lean was promised.

    A machine without Lean must still have a green suite, so the default is a
    skip that says why. The CI job that installs Lean sets
    ``LANKY_LEAN_TEST_REQUIRED=1``, and there a missing oracle is a failure: a
    toolchain that stopped installing, or a REPL that stopped building, would
    otherwise turn every Lean test into a quiet skip and leave the job green.
    """
    if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


def _open_lean_oracle() -> LeanOracle:
    """A Lean oracle whose session is open, or the reason there is none."""
    if os.environ.get("LANKY_LEAN_DISABLE"):
        _without_lean("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    oracle = LeanOracle(timeout=float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120")))
    available, reason = oracle.availability()
    if not available:
        _without_lean(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        _without_lean(f"the Lean REPL could not be built: {oracle.session.error}")
    return oracle


def test_a_required_lean_fails_where_it_would_have_skipped(monkeypatch) -> None:
    """``LANKY_LEAN_TEST_REQUIRED=1`` turns the Lean tests' skip into a failure.

    Without it a missing oracle skips, which keeps a machine without Lean
    green. With it, as in the CI job that installs Lean, the same reason fails
    the test, so that job cannot pass by running none of what it is for.
    """
    monkeypatch.delenv("LANKY_LEAN_TEST_REQUIRED", raising=False)
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    with pytest.raises(pytest.skip.Exception, match="disabled by LANKY_LEAN_DISABLE"):
        _open_lean_oracle()

    monkeypatch.setenv("LANKY_LEAN_TEST_REQUIRED", "1")
    with pytest.raises(
        pytest.fail.Exception,
        match="LANKY_LEAN_TEST_REQUIRED is set, but the Lean oracle is disabled",
    ):
        _open_lean_oracle()

    # and a Lean that is simply not there is a failure too, not only a disabled one
    monkeypatch.delenv("LANKY_LEAN_DISABLE")
    monkeypatch.setenv("PATH", "")
    with pytest.raises(pytest.fail.Exception, match="lean is not on PATH"):
        _open_lean_oracle()


@pytest.fixture(scope="module")
def lean_oracle() -> Iterator[LeanOracle]:
    """One Lean session for the whole module, or a skip explaining why not.

    The first session ever opened on a machine builds the REPL, which takes
    minutes and wants the network; afterwards it is a second. A suite that
    cannot pay for that says so and moves on, unless it was told that it can
    (see :func:`_without_lean`).
    """
    oracle = _open_lean_oracle()
    yield oracle
    oracle.session.close()


def test_lean_closes_a_nat_identity(lean_oracle: LeanOracle) -> None:
    proved = lean_oracle.establish(commutes.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert proved.provenance["tactic"] == "omega"
    assert "theorem commutes" in proved.provenance["lean_source"]


def test_lean_closes_a_bounded_implication(lean_oracle: LeanOracle) -> None:
    proved = lean_oracle.establish(below.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "omega"


def test_lean_proves_the_scan_is_monotone(lean_oracle: LeanOracle) -> None:
    # The demo theorem: the ladder has to find the induction itself.
    proved = lean_oracle.establish(scan_monotone.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert "induction q with" in proved.provenance["tactic"]


def test_a_pinned_tactic_is_the_one_that_runs(lean_oracle: LeanOracle) -> None:
    lean_oracle.tactics[commutes.fact().id] = "exact Int.add_comm x y"
    try:
        proved = lean_oracle.establish(commutes.fact())
    finally:
        lean_oracle.tactics.clear()
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "exact Int.add_comm x y"


def test_lean_reports_a_goal_it_cannot_close(lean_oracle: LeanOracle) -> None:
    @theorem
    def false_claim(x: Nat, y: Nat) -> x <= y:
        """Not a theorem at all, so no tactic closes it."""

    fact = false_claim.fact()
    assert lean_oracle.can_establish(fact)
    result = lean_oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert result.provenance["lean_tried"] >= 4
    assert result.provenance["lean_reason"]


def test_the_lean_oracle_never_refutes(lean_oracle: LeanOracle) -> None:
    """A failed proof is not a counterexample, and must never be read as one.

    Three ways the ladder can fail: a statement that is false, one that is true
    but out of the ladder's reach, and an attempt that times out. None of them
    is evidence against the claim, so the fact comes back with the status it
    arrived with and the weaker oracles still get their turn.
    """

    @theorem
    def plainly_false(x: Nat, y: Nat) -> x <= y:
        """False at x = 1, y = 0, and Lean will fail to prove it."""

    @theorem
    def true_but_hard(x: Nat, y: Nat) -> (x + y) * (x + y) >= x * x + y * y:
        """True, and nonlinear, so the core-Lean ladder does not close it."""

    for claim in (plainly_false, true_but_hard):
        result = lean_oracle.establish(claim.fact())
        assert result is not None
        assert result.status is not Status.REFUTED
        assert result.status is Status.ASSUMED
        assert result.decided_by is None
        assert result.provenance["lean_reason"]

    # a timeout is a failed attempt, not a refutation either
    impatient = LeanOracle(timeout=1e-6, session=lean_oracle.session)
    result = impatient.establish(plainly_false.fact())
    assert result.status is not Status.REFUTED


def test_a_session_runs_lean_source_directly(lean_oracle: LeanOracle) -> None:
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 0 = x := by omega\n")
    assert closed, detail
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 1 = x := by omega\n")
    assert not closed
    assert "omega" in detail


def test_checking_the_example_file_proves_the_scan(lean_oracle: LeanOracle) -> None:
    # The demo, end to end: the file is imported, the claims become facts, and
    # the strongest oracle that can take each one takes it.
    from pathlib import Path

    from lanky.check import check_path

    example = Path(__file__).resolve().parent.parent / "examples" / "gauss.py"
    ledger = check_path(example)
    by_owner = {fact.owner: fact for fact in ledger}
    assert by_owner["scan_monotone"].status is Status.PROVED
    assert by_owner["scan_monotone"].decided_by == "lean"
    # Gauss's sum is outside core Lean, so the property tester keeps it.
    assert by_owner["gauss"].status is Status.TESTED


def test_the_documented_ledger_is_the_one_check_prints(lean_oracle: LeanOracle, capsys) -> None:
    """The README's table and the quickstart's are what ``lanky check`` prints.

    Both were copied from a terminal with Lean installed, and the row they are
    there to show is ``scan_monotone`` reading ``proved lean``, so a machine
    with Lean is the one place they can be checked. The quickstart has the
    whole table; the README's is abridged to fit the page.
    """
    printed = _check_gauss(capsys)
    assert _printed_after("docs/quickstart.md", CHECK_GAUSS) == printed
    readme = _printed_after("README.md", "lanky check examples/gauss.py")
    _assert_abridged(readme, printed)
    assert any(line.startswith("proved  lean ") and "scan_monotone" in line for line in readme)


def test_the_printed_proposition_elaborates(lean_oracle: LeanOracle) -> None:
    # Lean reading the proposition as a term of type Prop is the strongest
    # check the printer can get short of a proof: it says the source is not
    # only plausible but well typed, binders, coercions and all.
    for term in (commutes.term, below.term, scan_monotone.term):
        closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(term)}\n")
        assert closed, detail


def test_lean_proves_a_family_applied_within_its_domain(lean_oracle: LeanOracle) -> None:
    """The bound check must cost nothing a statement in bounds was getting.

    ``g`` is applied under a quantifier of its own here rather than at the top
    level, which is where an in-bounds argument has to be recognized from the
    enclosing binder rather than from the theorem's parameters.
    """
    proved = lean_oracle.establish(within_bounds.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"


def test_lean_proves_a_chained_application_within_its_domain(
    lean_oracle: LeanOracle,
) -> None:
    """Checking every level of a chain must cost a chain in bounds nothing.

    ``grid(0)(0)`` against a ``Fn[Fin[1], Fn[Fin[1], Nat]]`` is a point of
    both domains, so the statement still reaches Lean and Lean still closes it.
    """
    proved = lean_oracle.establish(chained_in_bounds.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert "(grid 0 0 : Int) = (grid 0 0 : Int)" in proved.provenance["lean_source"]


def test_lean_is_never_asked_about_a_chained_application_out_of_bounds(
    lean_oracle: LeanOracle,
) -> None:
    """And the level the old check skipped keeps the statement away from Lean."""
    from lanky.check import establish

    assert not lean_oracle.can_establish(_chained_out_of_bounds.fact())
    fact = establish(_chained_out_of_bounds.fact())
    assert fact.status is not Status.PROVED
    assert "outside the domain" in fact.provenance["untested"]


def test_lean_is_never_asked_about_a_refined_family_domain(
    lean_oracle: LeanOracle,
) -> None:
    """Nor about a family whose domain a refinement may have emptied."""
    assert not lean_oracle.can_establish(_over_a_refined_domain.fact())


def test_lean_is_never_asked_about_an_impossible_refinement(
    lean_oracle: LeanOracle,
) -> None:
    """Nor about a refinement that hypothesizes over an erased point.

    ``g m ≠ g m`` is false for a lanky family, which has no value at ``m`` at
    all, and is an ordinary hypothesis for the total function Lean sees; from
    it Lean would close the goal ``1 = 2``.
    """
    assert not lean_oracle.can_establish(_impossible_refinement.fact())


def test_lean_is_never_asked_about_an_application_out_of_bounds(
    lean_oracle: LeanOracle,
) -> None:
    """And the ledger row is not ``proved``, whatever else it is."""
    from lanky.check import establish

    assert not lean_oracle.can_establish(_outside_bounds.fact())
    fact = establish(_outside_bounds.fact())
    assert fact.status is not Status.PROVED
    assert fact.status is Status.ASSUMED
    assert "outside the domain" in fact.provenance["untested"]


def test_lean_is_never_asked_about_a_captured_binder(lean_oracle: LeanOracle) -> None:
    """With Lean here the vacuous translation was proved; the row is refuted now."""
    from lanky.check import establish

    assert not lean_oracle.can_establish(_captured_binder.fact())
    fact = establish(_captured_binder.fact())
    assert fact.status is Status.REFUTED


def test_lean_does_not_prove_what_only_truncation_makes_true(
    lean_oracle: LeanOracle,
) -> None:
    """#6 with a real Lean: ``n - 1 >= 0`` is not a theorem of the integers.

    Lean used to prove it, because its ``Nat`` subtraction truncates, and the
    same file then exited 0 with Lean and 1 without. Lean now reads the integer
    statement, fails to prove it, and the tester's refutation is the answer on
    every machine. A statement whose readings always agreed keeps its proof.
    """
    result = lean_oracle.establish(_truncated.fact())
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_tried"] >= 4
    proved = lean_oracle.establish(one_below.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "omega"


@pytest.mark.parametrize("lean", ["as installed", "disabled"])
def test_a_variable_only_in_an_exponent_does_not_make_the_claim_natural(
    lean_oracle: LeanOracle, tmp_path, monkeypatch, capsys, lean
) -> None:
    """``1 - 2 ** m >= 0`` is refuted, and exits 1, with Lean and without.

    Its only variable sits in an exponent, which Lean takes as a ``Nat``, so
    before the literal base was ascribed nothing typed the numerals, Lean read
    the claim over ``Nat`` and proved it, and the check exited 0 where Lean was
    installed. The tester refutes it at ``m = 1``.
    """
    from lanky import cli
    from lanky.check import check_path

    assert lean_oracle.establish(_power_below_one.fact()).status is Status.ASSUMED
    if lean == "disabled":
        monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "power.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def power_below_one(m: Nat) -> 1 - 2**m >= 0:\n"
        '    """False at m = 1."""\n',
        encoding="utf-8",
    )
    (fact,) = list(check_path(path))
    assert fact.status is Status.REFUTED
    assert fact.decided_by == "property-test"
    assert cli.main(["check", str(path)]) == 1
    assert "REFUTED power_below_one" in capsys.readouterr().out


def test_lean_proves_a_goal_whose_bound_is_a_power(lean_oracle: LeanOracle) -> None:
    """The ladder used to raise on ``Fin[2 ** n]``, and Lean was never asked."""

    @theorem
    def powered(n: Nat) -> all(i < 2**n for i in Fin[2**n]):
        """Every point of Fin[2 ** n] is below its bound."""

    proved = lean_oracle.establish(powered.fact())
    assert proved.status is Status.PROVED
    assert "(2 : Int) ^ n.toNat" in proved.provenance["lean_source"]


def test_hypotheses_with_a_power_are_not_found_inconsistent_by_truncation(
    lean_oracle: LeanOracle,
) -> None:
    """``2 ** m - 5 < 0`` holds at ``m = 0``; over ``Nat`` it held nowhere.

    Together with ``n == 1000`` no draw satisfies the hypotheses, so Lean is
    asked whether they prove ``False``. Read over ``Nat``, ``2 ^ m - 5`` is
    never below zero and ``omega`` said yes, which marked a satisfiable claim
    vacuous and failed the check.
    """
    from lanky.check import hypotheses_fact

    @theorem
    def rare_power(m: Nat, n: Nat, h: (2**m - 5 < 0) & (n == 1000)) -> n > 999:
        """Satisfied at m = 0 and n = 1000, where no draw looks."""

    question = hypotheses_fact(rare_power.fact())
    assert "(2 : Int) ^ m.toNat - 5 < 0" in print_lean(question.term)
    assert lean_oracle.establish(question).status is Status.ASSUMED


def test_lean_reads_floor_division_the_way_python_does(lean_oracle: LeanOracle) -> None:
    """Division by a positive literal still proves, and a negative divisor floors.

    ``(k // 2) * 2 <= k`` is true under floor division and ``omega`` proves it
    through Lean's ``/``, which is floor division for a positive divisor.
    ``3 // -2`` is ``-2`` in Python and ``-1`` under Euclidean division, so a
    claim that it is ``-1`` must not be proved: it is false as the file runs it.
    """

    @theorem
    def halves(k: Int) -> (k // 2) * 2 <= k:
        """Floor division by two rounds down, negative k included."""

    proved = lean_oracle.establish(halves.fact())
    assert proved.status is Status.PROVED

    @theorem
    def euclidean(k: Int, h: k == 3) -> k // -2 == -1:
        """True of Euclidean division and false of Python's."""

    assert "Int.fdiv k (-2)" in print_lean(euclidean.term)
    result = lean_oracle.establish(euclidean.fact())
    assert result.status is not Status.PROVED
    from lanky.check import establish

    assert establish(euclidean.fact()).status is Status.REFUTED


def test_the_printed_integer_reading_elaborates(lean_oracle: LeanOracle) -> None:
    """Casts, ``Int.fdiv``, ``Int.fmod`` and ``.toNat`` exponents are well typed."""

    @theorem
    def everything(
        size: Nat,
        off: Fn[Fin[size + 1], Nat],
        k: Int,
        m: Nat,
    ) -> (k // (m + 1)) * (m + 1) + k % (m + 1) + 2**m - 2**m == k + off(0) - off(size):
        """A statement that uses every construct the integer reading prints."""

    source = print_lean(everything.term)
    for construct in (
        "Int.fdiv k (m + 1)",
        "Int.fmod k (m + 1)",
        "(2 : Int) ^ m.toNat",
        "(off 0 : Int)",
    ):
        assert construct in source
    claims = (everything, _truncated, one_below, scan_monotone, chained_in_bounds, _power_below_one)
    for claim in claims:
        closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(claim.term)}\n")
        assert closed, detail


def test_lean_closes_an_existential_over_an_index_type(lean_oracle: LeanOracle) -> None:
    """``simp`` knew ``0 < n + 1`` for a ``Nat``; for an ``Int`` it is ``omega``'s.

    The witness is found by ``simp``, which leaves ``0 < n + 1``; with ``n`` an
    ``Int`` and ``0 ≤ n`` a hypothesis that takes ``omega``, so the cheap ladder
    ends with ``simp_all <;> omega``.
    """

    @theorem
    def enumerated(m: Nat) -> any(j == 0 for j in Fin[m + 1]):
        """A witness in the domain, whatever m is."""

    proved = lean_oracle.establish(enumerated.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "simp_all <;> omega"


_VACUOUS = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Fin, Nat\n\n\n"
    "@theorem\n"
    "def vacuous(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1:\n"
    '    """No natural satisfies the hypotheses, so the goal is never at stake."""\n'
)


def test_lean_shows_a_vacuous_claim_vacuous(lean_oracle: LeanOracle, tmp_path, capsys) -> None:
    """#5 with a real Lean: the claim is proved, marked vacuous, and fails the check.

    ``omega`` closes ``n = n + 1`` from ``n > 2`` and ``n < 1``, which is a
    valid proof of a claim that says nothing. The tester finds no draw that
    satisfies the hypotheses, and Lean proves them inconsistent on their own.
    """
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "vacuous.py"
    path.write_text(_VACUOUS, encoding="utf-8")
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert fact.decided_by == "lean"
    assert fact.is_vacuous
    assert fact.provenance["vacuous_by"] == "lean"
    assert ": False := by" in fact.provenance["vacuous_evidence"]["lean_source"]
    assert cli.main(["check", str(path)]) == 1
    assert "proved (vacuous)  lean" in capsys.readouterr().out


def test_lean_shows_a_vacuous_axiom_vacuous_without_being_shown_the_axiom(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """An axiom with inconsistent hypotheses is vacuous, and still ``assumed``.

    Lean is asked whether the hypotheses prove ``False``, which ``omega``
    shows, and is never asked the axiom itself, so the row reads ``assumed
    (axiom) (vacuous)`` and the check fails.
    """
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "vacuous.py"
    path.write_text(
        _VACUOUS.replace("import theorem", "import axiom").replace(
            "@theorem", '@axiom(cite="a textbook, copied down wrong")'
        ),
        encoding="utf-8",
    )
    (fact,) = list(check_path(path))
    assert fact.kind == "axiom"
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.is_vacuous
    assert fact.provenance["vacuous_by"] == "lean"
    assert cli.main(["check", str(path)]) == 1
    assert "assumed (axiom) (vacuous)  -" in capsys.readouterr().out


def test_lean_leaves_hypotheses_the_sampler_misses_to_a_warning(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """``n == 1000`` holds where no draw looks, and ``False`` does not follow from it."""
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "rare.py"
    path.write_text(
        _VACUOUS.replace("(n > 2) & (n < 1)) -> n == n + 1", "n == 1000) -> n > 999"),
        encoding="utf-8",
    )
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    assert cli.main(["check", str(path)]) == 0
    assert "WARNING vacuous at rare.py:7" in capsys.readouterr().out


def test_lean_refutes_hypotheses_under_a_goal_it_cannot_state(
    lean_oracle: LeanOracle, tmp_path
) -> None:
    """A reduction keeps the goal from Lean, and the hypotheses still reach it."""
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "reduction.py"
    path.write_text(
        _VACUOUS.replace("-> n == n + 1", "-> 2 * sum(i for i in Fin[n + 1]) == 7"),
        encoding="utf-8",
    )
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.is_vacuous
    assert cli.main(["check", str(path)]) == 1


def test_the_statement_the_oracle_sends_is_the_one_it_records(
    lean_oracle: LeanOracle,
) -> None:
    proved = lean_oracle.establish(scan_monotone.fact())
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert isinstance(statement, LeanStatement)
    assert proved.provenance["lean_source"] == statement.source(proved.provenance["tactic"])


# }}}
