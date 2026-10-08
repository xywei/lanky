"""The Lean printer and the Lean oracle.

The printer is tested against golden source: what lanky sends to Lean is part of
the contract with the reader, not only with the elaborator, so the tests spell
the expected text out. The oracle is tested against a real Lean, and skips
cleanly when there is none, because a machine without Lean must still have a
green suite.
"""

from __future__ import annotations

import os
import re
from collections.abc import Iterator
from fractions import Fraction
from pathlib import Path
from typing import NoReturn

import pymbolic.primitives as prim
import pytest

from conftest import ProcessWatch, claims
from lanky import theorem
from lanky.check import import_path
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    check_applications,
    lean_identifier,
    lean_type,
    print_lean,
    statement_of,
)
from lanky.ledger import Fact, Status
from lanky.oracles.lean import (
    LeanOracle,
    LeanSession,
    induction_scripts,
    kill_servers,
    reduction_scripts,
    tactic_ladder,
    use_tactic,
)
from lanky.plugins import registry
from lanky.prelude import Bool, Fin, FinType, Fn, Int, Nat, Real
from lanky.terms import Abs, Elementary, Exists, Forall, Sum, Var

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


def test_an_existential_brackets_a_disjunctive_condition() -> None:
    """An existential's conditions are conjuncts, so a disjunction among them is bracketed (#61).

    They were printed as a universal's are, to the left of an arrow, where a
    disjunction needs no brackets. Joined with ``∧``, which binds more tightly
    than ``∨``, the guard of ``any(x == -1 for x in Fin[3] if (x > 5) | (x <
    1))`` made the statement ``(0 ≤ x ∧ x < 3 ∧ x > 5) ∨ (x < 1 ∧ x = -1)``,
    which ``x = -1`` satisfies, while the only point Python's guard admits is
    ``0``. A refinement of the domain and the guard of an existential with no
    binders were printed the same way, in both dialects.
    """
    x = Var("x")
    either = (x > 5) | (x < 1)
    guarded = Exists(((x, FinType(3)),), x == -1, either)
    refined = Exists(((x, Nat & either),), x == -1)
    binderless = Forall(((x, Int),), Exists((), x == -1, either))
    for mathlib in (False, True):
        assert print_lean(guarded, mathlib=mathlib) == (
            "∃ x : Int, 0 ≤ x ∧ x < 3 ∧ (x > 5 ∨ x < 1) ∧ x = -1"
        )
        assert print_lean(refined, mathlib=mathlib) == (
            "∃ x : Int, 0 ≤ x ∧ (x > 5 ∨ x < 1) ∧ x = -1"
        )
        assert print_lean(binderless, mathlib=mathlib) == (
            "∀ x : Int, (x > 5 ∨ x < 1) ∧ x = -1"
        )
    # a universal's conditions stand to the left of an arrow, which binds more
    # loosely than ∨, and need no brackets
    assert print_lean(Forall(((x, FinType(3)),), x != -1, either)) == (
        "∀ x : Int, 0 ≤ x → x < 3 → x > 5 ∨ x < 1 → x ≠ -1"
    )
    assert print_lean(Forall(((x, Nat & either),), x != -1)) == (
        "∀ x : Int, 0 ≤ x → x > 5 ∨ x < 1 → x ≠ -1"
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
    # each binder's guard follows it, as it does in print_lean, and the
    # declaration is elaborated with auto-bound implicits off (#68)
    assert statement.source("omega") == (
        "set_option autoImplicit false in\n"
        "theorem Lanky.commutes (x : Int) (h0 : 0 ≤ x) (y : Int) (h1 : 0 ≤ y) : "
        "x + y = y + x := by\n  omega\n"
    )


def test_an_index_typed_variable_carries_its_bounds_as_hypotheses() -> None:
    statement = statement_of(below.term, "below")
    assert statement.binders == (("m", "Int"), ("j", "Int"))
    assert statement.hypotheses == (("h0", "0 ≤ m"), ("h1", "0 ≤ j"), ("h2", "j < m"))
    assert statement.goal == "j < m + 1"


def test_the_scan_statement_prints_as_a_lean_theorem() -> None:
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert statement.source("omega").splitlines()[1] == (
        "theorem Lanky.scan_monotone (size : Int) (h0 : 0 ≤ size) (cnt : Int → Nat) "
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

    # what the oracle proves has to be closed (#64), so the arranger is shown
    # a closed one, which only a term built node by node can be
    closed = Forall((), prim.Comparison(2, ">", 0), prim.Comparison(2, ">", 1))
    statement = statement_of(closed, "binderless")
    assert statement.binders == ()
    assert statement.hypotheses == (("h0", "(2 : Int) > 1"),)
    assert statement.goal == "(2 : Int) > 0"


# }}}


# {{{ names Lean would read as something else


def _scoped():
    @theorem
    def scoped(a: Nat, b: Nat) -> a + b == b + a:
        """A true claim under a name that is a Lean keyword."""

    return scoped


def _keyword_binders():
    @theorem
    def binders(fun: Nat, at: Nat) -> fun + at == at + fun:
        """The same claim over variables whose names are Lean keywords."""

    return binders


def _named_like_a_hypothesis():
    @theorem
    def named(h0: Nat, b: Nat) -> h0 + b == b + h0:
        """The same claim over a variable named like the first hypothesis."""

    return named


def _truth():
    @theorem
    def truth(true: Bool) -> true == True:  # noqa: E712 - the point of it
        """False at ``true = False``, over a variable named like the Boolean literal."""

    return truth


def _scan_with_keyword_binders():
    @theorem
    def scan_keywords(
        size: Nat,
        cnt: Fn[Fin[size], Nat],
        off: Fn[Fin[size + 1], Nat],
        h0: off(0) == 0,
        hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
    ) -> all(
        off(show) <= off(at) for show in Fin[size + 1] for at in Fin[size + 1] if show <= at
    ):
        """The scan's monotonicity, with its goal's variables named like Lean keywords."""

    return scan_keywords


def test_a_name_lean_reserves_is_quoted() -> None:
    """#38: a keyword, or a letter outside ASCII, is written ``«name»``, the same name to Lean.

    The list of keywords is Lean's parser table, core and Mathlib's both; a
    name Lean reads as it is stays as it is.
    """
    assert lean_identifier("size") == "size"
    assert lean_identifier("h0_1") == "h0_1"
    assert lean_identifier("Fun") == "Fun"
    for word in ("fun", "at", "show", "end", "scoped", "open", "Type", "exists", "_"):
        assert lean_identifier(word) == f"«{word}»"
    for word in ("lemma", "to", "over"):  # reserved once Mathlib is imported
        assert lean_identifier(word) == f"«{word}»"
    for name in ("λ", "é", "x₁"):
        assert lean_identifier(name) == f"«{name}»"
    for name in ("", "a»b", "«a", "a\nb"):
        with pytest.raises(UnsupportedTerm, match="cannot be written as a Lean identifier"):
            lean_identifier(name)


def test_a_theorem_named_like_a_keyword_is_declared_under_its_quoted_name() -> None:
    """``theorem scoped`` does not parse, and every tactic of the ladder failed on it."""
    scoped = _scoped()
    statement = statement_of(scoped.term, "scoped")
    assert statement.name == "«scoped»"
    assert statement.source("omega").startswith(
        "set_option autoImplicit false in\ntheorem Lanky.«scoped» (a : Int) (h0 : 0 ≤ a) "
    )
    mathlib = statement_of(scoped.term, "scoped", mathlib=True)
    assert mathlib.declared_name == "Lanky.«scoped»"
    # a qualified name is cleaned first, and quoted only if what is left needs it
    assert statement_of(scoped.term, "test_x.<locals>.scoped").name == "test_x__locals__scoped"
    assert statement_of(scoped.term, "lemma").name == "«lemma»"


def test_variables_named_like_keywords_are_quoted_wherever_they_are_printed() -> None:
    """A parameter, a bound variable, an exponent and a reduction's binder alike."""
    binders = _keyword_binders()
    statement = statement_of(binders.term, "binders")
    assert statement.binders == (("«fun»", "Int"), ("«at»", "Int"))
    assert statement.variables == ("fun", "at")
    assert statement.hypotheses == (("h0", "0 ≤ «fun»"), ("h1", "0 ≤ «at»"))
    assert statement.goal == "«fun» + «at» = «at» + «fun»"
    assert print_lean(binders.term) == (
        "∀ «fun» : Int, 0 ≤ «fun» → ∀ «at» : Int, 0 ≤ «at» → «fun» + «at» = «at» + «fun»"
    )

    show, end = Var("show"), Var("end")
    bound = Forall(((n, Nat),), Forall(((show, FinType(n)),), show < 2**show))
    assert print_lean(bound) == (
        "∀ n : Int, 0 ≤ n → ∀ «show» : Int, 0 ≤ «show» → «show» < n → "
        "«show» < (2 : Int) ^ «show».toNat"
    )
    reduction = Forall(((n, Nat),), Sum(((end, FinType(n)),), end) >= 0)
    assert "(∑ «end» ∈ Finset.Ico (0 : ℤ) n, «end») ≥ 0" in print_lean(reduction, mathlib=True)


def test_a_variable_named_like_a_hypothesis_does_not_meet_one() -> None:
    """The hypothesis ``0 ≤ h0`` named ``h0`` shadowed the variable, and the goal's ``h0``
    was the proof: ``named`` read ``tested`` with Lean's "Application type mismatch".

    A hypothesis takes the next name no variable of the statement has, bound
    ones in the goal included, since the ladder introduces those after the
    hypotheses.
    """
    statement = statement_of(_named_like_a_hypothesis().term, "named")
    assert statement.hypotheses == (("h0_1", "0 ≤ h0"), ("h1", "0 ≤ b"))
    assert statement.source("omega").startswith(
        "set_option autoImplicit false in\n"
        "theorem Lanky.named (h0 : Int) (h0_1 : 0 ≤ h0) (b : Int) (h1 : 0 ≤ b) : "
        "h0 + b = b + h0"
    )

    first, second = Var("h0"), Var("h1")
    goal = Forall(((second, FinType(b)),), second < b)
    statement = statement_of(Forall(((first, Nat), (b, Nat)), goal), "t")
    assert [name for name, _ in statement.hypotheses] == ["h0_1", "h1_1"]
    assert "intro h1 hd hd_1" in tactic_ladder(statement)[5]


def test_a_variable_named_true_is_not_the_boolean_literal() -> None:
    """``true == True`` over a ``Bool`` named ``true`` printed as ``true = true``.

    Lean proves that by ``simp``, and the claim is false at ``true = False``.
    Where a variable of that name is in scope, free or bound, the literal is
    written ``Bool.true``; elsewhere it is printed as it always was.
    """
    truth = _truth()
    assert statement_of(truth.term, "truth").goal == "true = Bool.true"
    assert print_lean(truth.term) == "∀ true : Bool, true = Bool.true"
    assert print_lean(Var("false") == False) == "false = Bool.false"  # noqa: E712
    assert print_lean(f(a) == True) == "f a = true"  # noqa: E712


def test_the_ladder_names_a_keyword_variable_as_the_printer_does() -> None:
    """The strategy's ``intro``, ``obtain`` and ``induction`` quote what the statement quotes."""
    ladder = tactic_ladder(statement_of(_scan_with_keyword_binders().term, "scan_keywords"))
    script = ladder[-2]
    assert "intro «show» hd hd_1 «at» hd_2 hd_3 hg" in script
    assert "obtain ⟨«at», rfl⟩ := Int.eq_ofNat_of_zero_le hd_2" in script
    assert "induction «at» with" in script
    assert "by_cases hlt : (k : Int) < «show»" in script


def test_the_ladder_names_no_guard_like_a_later_binder() -> None:
    """A guard of ``a`` named ``hd`` was shadowed by a later goal binder named ``hd``.

    The script then traded ``a`` for a natural through ``hd``, which by then
    was the variable and not the guard ``0 ≤ a``.
    """
    guard = Var("hd")
    term = Forall(((n, Nat),), Forall(((a, Nat), (guard, Nat)), guard + a >= a + n - n))
    (script,) = induction_scripts(statement_of(term, "t"))
    assert script.startswith("intro a hd_1 hd hd_2\n")
    assert "obtain ⟨hd, rfl⟩ := Int.eq_ofNat_of_zero_le hd_2" in script


def test_a_claim_named_like_a_core_declaration_is_declared_in_a_namespace() -> None:
    """#39 and #43: ``theorem and_comm`` is refused as already declared, whatever the tactic.

    Core Lean declares ``and_comm``, ``trivial``, ``id``, ``absurd`` and
    ``congr`` at the root, so a claim named like one read ``tested`` with
    "already declared" as its reason. A keyword that is also a root
    declaration, ``inferInstanceAs``, was quoted and refused all the same, and
    ``True_`` was cleaned into ``True``. Every statement is declared in the
    ``Lanky`` namespace now, as a Mathlib one already was.
    """
    for name in ("and_comm", "trivial", "id", "absurd", "congr"):
        statement = statement_of(commutes.term, name)
        assert statement.declared_name == f"Lanky.{name}"
        assert f"\ntheorem Lanky.{name} (x : Int) " in statement.source("omega")
    assert statement_of(commutes.term, "inferInstanceAs").declared_name == (
        "Lanky.«inferInstanceAs»"
    )
    assert statement_of(commutes.term, "True_").declared_name == "Lanky.True"


def _typed_like_int():
    @theorem
    def typed(Int: Nat, b: Nat) -> Int + b == b + Int:
        """A variable named like the type a natural is printed as."""

    return typed


def test_a_variable_named_like_a_type_the_printer_writes_leaves_the_type_alone() -> None:
    """#43: ``(Int : Int) (b : Int)`` read the second ``Int`` as the variable.

    The binder ``b`` was given the variable as its type, which does not
    elaborate, and every attempt failed with "type expected". A root name
    some variable is named like is printed from the root, ``_root_.Int``, in
    that statement and only there.
    """
    statement = statement_of(_typed_like_int().term, "typed")
    assert statement.binders == (("Int", "_root_.Int"), ("b", "_root_.Int"))
    assert statement.goal == "Int + b = b + Int"
    assert statement.shadowed == frozenset({"Int"})
    assert statement.qualified("Int.eq_ofNat_of_zero_le") == "_root_.Int.eq_ofNat_of_zero_le"
    assert statement.qualified("Nat") == "Nat"
    # a statement with no such variable prints as it always did
    assert statement_of(commutes.term, "commutes").binders == (("x", "Int"), ("y", "Int"))
    assert statement_of(commutes.term, "commutes").qualified("Int") == "Int"

    # every root name the printer writes: the types, a cast, a floor division, a power
    family, nat, integer = Var("f"), Var("Nat"), Var("Int")
    term = Forall(
        ((nat, Nat), (integer, Nat), (family, Fn[Fin[nat], Nat])),
        Forall(((i, FinType(nat)),), family(i) // (integer + 1) <= 2**i),
    )
    assert print_lean(term) == (
        "∀ Nat : _root_.Int, 0 ≤ Nat → ∀ Int : _root_.Int, 0 ≤ Int → "
        "∀ f : _root_.Int → _root_.Nat, ∀ i : _root_.Int, 0 ≤ i → i < Nat → "
        "_root_.Int.fdiv (f i : _root_.Int) (Int + 1) ≤ (2 : _root_.Int) ^ i.toNat"
    )
    boolean, true = Var("Bool"), Var("true")
    assert print_lean(Forall(((boolean, Bool), (true, Bool)), true == True)) == (  # noqa: E712
        "∀ Bool : _root_.Bool, ∀ true : _root_.Bool, true = _root_.Bool.true"
    )
    assert print_lean(Forall(((Var("True"), Nat),), True)) == (
        "∀ True : Int, 0 ≤ True → _root_.True"
    )


def test_mathlib_names_are_printed_from_the_root_where_a_variable_shadows_them() -> None:
    """``Real.exp``, ``Complex.I`` and ``Finset.Ico`` are fields of a variable named so."""
    real, finset, x = Var("Real"), Var("Finset"), Var("x")
    exponential = Forall(((real, Real), (x, Real)), Elementary("exp", x) > 0)
    assert print_lean(exponential, mathlib=True) == (
        "∀ Real : ℝ, ∀ x : ℝ, _root_.Real.exp x > 0"
    )
    complex_ = Forall(((Var("Complex"), Real),), Var("Complex") * complex(0, 1) == 0)
    assert "(0 + 1 * _root_.Complex.I : ℂ)" in print_lean(complex_, mathlib=True)
    reduction = Forall(((finset, Nat),), Sum(((i, FinType(finset)),), i) >= 0)
    assert "∑ i ∈ _root_.Finset.Ico (0 : ℤ) Finset, i" in print_lean(reduction, mathlib=True)
    statement = statement_of(exponential, "positive", mathlib=True)
    ladder = tactic_ladder(statement)
    assert "simp [_root_.Real.exp_add, Complex.exp_add, _root_.Real.exp_sub, " in "\n".join(
        ladder
    )


def _scan_over_rfl():
    @theorem
    def scan_rfl(
        size: Nat,
        cnt: Fn[Fin[size], Nat],
        off: Fn[Fin[size + 1], Nat],
        h0: off(0) == 0,
        hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
    ) -> all(off(a) <= off(rfl) for a in Fin[size + 1] for rfl in Fin[size + 1] if a <= rfl):
        """The scan's monotonicity, inducing on a variable named ``rfl``."""

    return scan_rfl


def test_a_variable_named_rfl_is_introduced_under_a_name_no_pattern_reads() -> None:
    """#43: ``obtain ⟨rfl, rfl⟩`` substituted twice, and ``intro rfl`` substitutes too.

    The induction strategy introduced the goal's variables under their own
    names and traded the one it induces on for a natural in an ``rcases``
    pattern, so a variable named ``rfl`` was read as a substitution at both,
    and the script failed. It is introduced as a fresh ``x`` now, and the
    strategy names it so; ``_`` is the other name a pattern reads.
    """
    scripts = induction_scripts(statement_of(_scan_over_rfl().term, "scan_rfl"))
    for script in scripts:
        assert script.startswith("intro a hd hd_1 x hd_2 hd_3 hg\n")
        assert "obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le hd_2" in script
        assert "induction x with" in script
    hole = Var("_")
    term = Forall(((n, Nat),), Forall(((hole, FinType(n + 1)),), hole <= n))
    (script,) = induction_scripts(statement_of(term, "t"))
    assert script.startswith("intro x hd hd_1\n")
    # a parameter traded in a Mathlib reduction's induction gets a fresh name too
    rfl = Var("rfl")
    gauss_rfl = Forall(((rfl, Nat),), 2 * Sum(((i, FinType(rfl + 1)),), i) == rfl * (rfl + 1))
    (script,) = reduction_scripts(statement_of(gauss_rfl, "gauss_rfl", mathlib=True))
    assert script.startswith("obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le h0\ninduction x with")


def _scan_over_int():
    @theorem
    def scan_int(
        Int: Nat,
        cnt: Fn[Fin[Int], Nat],
        off: Fn[Fin[Int + 1], Nat],
        h0: off(0) == 0,
        hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[Int]),
    ) -> all(off(p) <= off(q) for p in Fin[Int + 1] for q in Fin[Int + 1] if p <= q):
        """The scan's monotonicity, over a size named like the type a natural prints as."""

    return scan_int


def test_the_induction_names_root_declarations_as_the_statement_does() -> None:
    """A size named ``Int`` made ``Int.eq_ofNat_of_zero_le`` and the casts fields of it."""
    scripts = induction_scripts(statement_of(_scan_over_int().term, "scan_int"))
    for script in scripts:
        assert "obtain ⟨q, rfl⟩ := _root_.Int.eq_ofNat_of_zero_le hd_2" in script
        # Nat is not shadowed here, and stays as it is
        assert "((k + 1 : Nat) : _root_.Int) = (k : _root_.Int) + 1" in script
    assert "by_cases hlt : (k : _root_.Int) < p" in scripts[0]


def test_a_free_name_is_shown_and_not_handed_to_lean() -> None:
    """A statement with a name nothing in it binds is declined where it would be proved (#64).

    The printer printed a free name as it stands, and Lean read it as its own
    declaration of that name or, where there is none, bound it implicitly at a
    type it inferred: ``x - 1 >= 0`` with a free ``x`` was ``theorem
    Lanky.free (h0 : int) : x - 1 ≥ 0``, about a natural ``x`` and an ``int``
    of any type, which ``omega`` proved. :func:`print_lean` still prints an
    open term, to show it; :func:`statement_of`, what the oracle proves,
    declines it, naming the names.
    """
    x, m, g, k = Var("x"), Var("m"), Var("g"), Var("k")
    free = Forall((), x - 1 >= 0, Var("int"))
    assert print_lean(free) == "int → x - 1 ≥ 0"
    with pytest.raises(UnsupportedTerm, match="mentions int and x, which no parameter"):
        statement_of(free, "free")
    # a family applied and bound nowhere, a size in a domain, a size in a
    # family's type, and a plain pymbolic variable, all free
    for term, name in (
        (Forall(((n, Nat),), f(n) >= 0), "f"),
        (Forall(((i, FinType(m)),), i >= 0), "m"),
        (Forall(((g, Fn[Fin[m], Nat]),), g(0) >= 0), "m"),
        (Forall(((n, Nat),), prim.Comparison(prim.Variable("y"), ">=", n)), "y"),
    ):
        for mathlib in (False, True):
            with pytest.raises(UnsupportedTerm, match=f"mentions {name}, which no parameter"):
                statement_of(term, "free", mathlib=mathlib)
    # a refinement's propositions are about the variable it refines, which is
    # bound, and so is every name a closed statement mentions
    statement = statement_of(Forall(((k, Nat & (k > 0)),), k >= 1), "bound")
    assert statement.goal == "k ≥ 1"
    statement = statement_of(Forall(((n, Nat), (i, FinType(n))), i < n), "bound")
    assert statement.goal == "i < n"


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
    assert statement.source("omega").splitlines()[1] == (
        "theorem Lanky.truncated (n : Int) (h0 : 0 ≤ n) : n - 1 ≥ 0 := by"
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


#: ``1 - Fraction(2, 1) ** n >= 0`` over ``Nat``, built node by node: pymbolic's
#: operators refuse a ``Fraction`` operand, so a plugin is where it comes from.
_FRACTION_BASE = Forall(
    ((n, Nat),),
    prim.Comparison(prim.Sum((1, prim.Product((-1, prim.Power(Fraction(2, 1), n))))), ">=", 0),
)


def test_an_integral_fraction_is_the_integer_it_equals() -> None:
    """``Fraction(2, 1)`` prints as ``2``, so every rule for an integer literal applies to it.

    The base of a power is the one that mattered: an ``int`` base is ascribed
    ``Int`` and an integral ``Fraction`` was not, so ``_FRACTION_BASE`` printed
    as ``1 - 2 ^ n.toNat ≥ 0``, a statement about ``Nat`` that Lean proves by
    truncating and Python refutes at ``n = 1``. A literal exponent, a positive
    literal divisor, a negative summand and a coefficient of -1 read the same
    way, a family applied at one is applied at an integer the bounds check can
    see, and a fraction that is not an integer still needs a field.
    """
    assert print_lean(_FRACTION_BASE) == "∀ n : Int, 0 ≤ n → 1 - (2 : Int) ^ n.toNat ≥ 0"
    squared = prim.Comparison(prim.Power(n, Fraction(2, 1)), ">=", 0)
    assert print_lean(Forall(((n, Nat),), squared)) == "∀ n : Int, 0 ≤ n → n ^ 2 ≥ 0"
    halved = prim.Comparison(prim.FloorDiv(n, Fraction(2, 1)), "<=", n)
    assert print_lean(Forall(((n, Nat),), halved)) == "∀ n : Int, 0 ≤ n → n / 2 ≤ n"
    lowered = prim.Comparison(prim.Sum((n, Fraction(-3, 1))), "<", n)
    assert print_lean(Forall(((n, Nat),), lowered)) == "∀ n : Int, 0 ≤ n → n - 3 < n"
    # a coefficient of -1 is a subtraction too, whichever kind of literal it is
    negated = prim.Comparison(prim.Sum((n, prim.Product((Fraction(-1, 1), i)))), "<=", n)
    assert print_lean(Forall(((n, Nat), (i, Nat)), negated)) == (
        "∀ n : Int, 0 ≤ n → ∀ i : Int, 0 ≤ i → n - i ≤ n"
    )
    # and a family applied at one is applied at the integer, in bounds
    applied = Forall(((f, Fn[Fin[1], Nat]),), prim.Comparison(f(Fraction(0, 1)), ">=", 0))
    assert print_lean(applied) == "∀ f : Int → Nat, (f 0 : Int) ≥ 0"
    with pytest.raises(UnsupportedTerm, match="needs a field"):
        print_lean(Forall(((n, Nat),), prim.Comparison(n, ">=", Fraction(1, 2))))


#: ``1 - 2 >= 0``, built node by node: Python would answer it in an annotation.
_CLOSED_SUBTRACTION = prim.Comparison(prim.Sum((1, -2)), ">=", 0)


def test_a_comparison_with_no_name_in_it_is_integer_arithmetic() -> None:
    """A closed comparison is ascribed ``Int``, as a literal base is.

    With no variable on either side Lean has nothing to read the numerals'
    type off, and reads them as ``Nat``: ``1 - 2 ≥ 0`` is then a truncated
    subtraction Lean proves, and Python refutes, and ``-1 ≠ 0`` does not
    elaborate at all. Such a term comes from a plugin, the demonstration's
    claim that a coefficient it computed is not zero among them. A comparison
    with a name in it is typed by the name, as before.
    """
    assert print_lean(_CLOSED_SUBTRACTION) == "(1 - 2 : Int) ≥ 0"
    assert print_lean(prim.Comparison(-1, "!=", 0)) == "(-1 : Int) ≠ 0"
    assert print_lean(prim.Comparison(Fraction(3, 1), "==", 3)) == "(3 : Int) = 3"
    nested = Forall(
        ((n, Nat),),
        prim.LogicalOr((prim.Comparison(prim.Product((2, 3)), "<", 7), prim.Comparison(n, "<", 0))),
    )
    assert print_lean(nested) == "∀ n : Int, 0 ≤ n → (2 * 3 : Int) < 7 ∨ n < 0"
    assert print_lean(Forall(((n, Nat),), prim.Comparison(n, ">=", 0))) == (
        "∀ n : Int, 0 ≤ n → n ≥ 0"
    )
    assert print_lean(Forall(((f, Fn[Fin[1], Nat]),), prim.Comparison(f(0), ">=", 0))) == (
        "∀ f : Int → Nat, (f 0 : Int) ≥ 0"
    )


#: ``(1 - 2) ** n >= 0`` over ``Nat``, built node by node: Python would compute
#: ``1 - 2`` in an annotation. False at ``n = 1``.
_CLOSED_BASE = Forall(((n, Nat),), prim.Comparison(prim.Power(prim.Sum((1, -2)), n), ">=", 0))


def test_a_base_with_no_name_in_it_is_an_integer() -> None:
    """A base of literals alone is ascribed ``Int``, as a literal base is.

    ``n`` is only in the exponent, as ``n.toNat``, a ``Nat``, and the base has
    no name in it either, so nothing typed its numerals: ``(1 - 2) ^ n.toNat
    ≥ 0`` was ``0 ^ n.toNat ≥ 0`` over ``Nat``, which Lean proves and Python
    refutes at ``n = 1``, the closed comparison's gap again one level down.
    """
    assert print_lean(_CLOSED_BASE) == "∀ n : Int, 0 ≤ n → (1 - 2 : Int) ^ n.toNat ≥ 0"
    product = prim.Comparison(prim.Power(prim.Product((2, 3)), n), ">=", 1)
    assert print_lean(Forall(((n, Nat),), product)) == (
        "∀ n : Int, 0 ≤ n → (2 * 3 : Int) ^ n.toNat ≥ 1"
    )
    # a base with a name in it is typed by the name, as before
    assert print_lean(Forall(((n, Nat),), (n - 2) ** n >= 0)) == (
        "∀ n : Int, 0 ≤ n → (n - 2) ^ n.toNat ≥ 0"
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
    # and as the standard key for a decline, which lanky check prints (#37)
    assert result.provenance["declined"] == f"lean: {reason}"
    printed = oracle.establish(gauss.fact())
    assert printed.provenance["declined"].startswith("lean: a reduction needs Finset.sum")


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


class _KilledOnTimeout:
    """A stand-in for lean-interact's server, which kills itself on a timeout.

    lean-interact's ``LeanServer`` kills its REPL process when a command runs
    past its timeout, and answers every later command with a
    ``ChildProcessError`` until ``start`` is called again; this does the same
    without a Lean.
    """

    def __init__(self) -> None:
        self.alive = True
        self.starts = 0

    def is_alive(self) -> bool:
        return self.alive

    def start(self) -> None:
        self.starts += 1
        self.alive = True

    def kill(self) -> None:
        self.alive = False

    def run(self, command, timeout=None):
        from types import SimpleNamespace

        if not self.alive:
            raise ChildProcessError("The Lean server is not running.")
        if timeout is not None and timeout < 1e-3:
            self.kill()
            raise TimeoutError("The Lean server did not respond in time and is now killed.")
        return SimpleNamespace(messages=(), sorries=())


def test_a_core_session_starts_a_killed_server_again(monkeypatch) -> None:
    """#32: one attempt that timed out cost every Lean proof after it in the process.

    The driver kills the server on a timeout and never starts it again, and a
    core session went on sending commands to the dead one, each answered with
    "The Lean server is not running", while the session had no error and the
    oracle said it was available. The session now starts it again before the
    next command, as a Mathlib session already did.
    """
    import sys
    from types import SimpleNamespace

    monkeypatch.setitem(
        sys.modules, "lean_interact", SimpleNamespace(Command=lambda **fields: fields)
    )
    session = LeanSession(timeout=60)
    session.server = server = _KilledOnTimeout()
    assert session.run("theorem t : True := trivial\n") == (True, "")
    session.timeout = 1e-6
    closed, detail = session.run("theorem t : True := trivial\n")
    assert not closed
    assert detail.startswith("TimeoutError")
    assert not server.alive
    session.timeout = 60
    assert session.run("theorem t : True := trivial\n") == (True, "")
    assert server.starts == 1
    assert session.error is None

    # a server that will not start again is a reason, reported from then on
    def refuse() -> None:
        raise ChildProcessError("The Lean server could not be started")

    server.kill()
    server.start = refuse
    closed, detail = session.run("theorem t : True := trivial\n")
    assert not closed
    assert detail == session.error
    assert "could not be restarted" in detail


class _Interrupted:
    """A stand-in server whose command is interrupted, as Ctrl-C interrupts one."""

    def __init__(self) -> None:
        self.kills = 0

    def is_alive(self) -> bool:
        return True

    def run(self, command, timeout=None):
        raise KeyboardInterrupt

    def kill(self) -> None:
        self.kills += 1


def test_an_interrupted_command_stops_the_repl(monkeypatch) -> None:
    """#46: Ctrl-C during an attempt left the process waiting for the REPL's answer.

    lean-interact reads the answer in a thread the interpreter waits for on
    its way out, so ``lanky check`` interrupted while the REPL was busy did
    not end until the attempt did, and the session's close at exit, which
    would have stopped the REPL, ran only after that. The REPL is stopped
    where the command is interrupted now, the interrupt goes on, and the
    session starts another REPL for its next command.
    """
    import sys
    from types import SimpleNamespace

    monkeypatch.setitem(
        sys.modules, "lean_interact", SimpleNamespace(Command=lambda **fields: fields)
    )
    session = LeanSession(timeout=60)
    session.server = server = _Interrupted()
    with pytest.raises(KeyboardInterrupt):
        session.run("theorem t : True := trivial\n")
    assert server.kills == 1
    assert (session.server, session.error) == (None, None)


#: A stand-in for ``lake env repl``: a process that starts one of its own,
#: prints that one's pid, and sleeps, as ``lake`` waits on the REPL.
_LAKE = """\
import subprocess, sys, time
repl = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(60)"])
print(repl.pid, flush=True)
time.sleep(60)
"""


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX process groups")
@pytest.mark.parametrize("own_session", [True, False])
def test_kill_servers_kills_each_repl_and_what_it_started(own_session) -> None:
    """#28: a process about to end of a signal kills each session's REPL first.

    lean-interact starts ``lake env repl`` in a session of its own, which no
    signal sent to lanky's process reaches, so the REPL outlived a process
    ended by one, going on with its attempt. A child of ``lanky check`` calls
    this on ``SIGTERM``. The whole process group goes, the REPL ``lake``
    started with it; a server that is not in a group of its own is killed
    alone. A server already reaped is left alone, and so is a session that
    never started one.
    """
    import subprocess
    import sys
    from types import SimpleNamespace

    from lanky.oracles.lean import _OPENED

    lake = subprocess.Popen(
        [sys.executable, "-c", _LAKE], stdout=subprocess.PIPE, start_new_session=own_session
    )
    repl = ProcessWatch(int(lake.stdout.readline()))
    reaped = subprocess.Popen([sys.executable, "-c", "pass"])
    reaped.wait()
    sessions = [LeanSession(), LeanSession(), LeanSession()]
    sessions[0].server = SimpleNamespace(_proc=lake)
    sessions[1].server = SimpleNamespace(_proc=reaped)
    try:
        for session in sessions:
            _OPENED.add(session)
        kill_servers()
        assert lake.wait(timeout=60) == -9
        if own_session:
            assert repl.wait(60), "the REPL lake started outlived it"
    finally:
        for session in sessions:
            _OPENED.discard(session)
        lake.kill()
        lake.wait()
        repl.kill()


def _gone(pid: int) -> bool:
    """Whether process ``pid`` has ended; one ended and not yet reaped counts."""
    return ProcessWatch(pid).gone()


#: A program that hands a stand-in REPL to the reaper as a session does, says
#: which processes to watch, and then sleeps, or closes the session and ends.
_HANDED_OVER = """\
import subprocess, sys, time
from types import SimpleNamespace
import lanky.oracles.lean as lean
repl = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"],
                        start_new_session=True, stdout=subprocess.DEVNULL)
session = lean.LeanSession()
session.server = SimpleNamespace(_proc=repl, kill=lambda: None)
session._opened()
print(repl.pid, lean._REAPER.pid, flush=True)
if sys.argv[1] == "sleep":
    time.sleep(120)
session.close()
"""


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX process groups")
def test_a_repl_ends_with_the_process_however_it_ends() -> None:
    """#46: a REPL outlived a lanky process ended by a signal, going on with its attempt.

    lean-interact starts the REPL in a session of its own, which no signal
    sent to lanky's process or its group reaches, and the process ended of a
    ``SIGKILL`` ran nothing on the way out. A reaper, which reads a pipe from
    the process and kills the REPL's group when the pipe closes, ends it now,
    whatever ended the process. The stand-in here is a REPL busy with an
    attempt: it does not read its input.
    """
    import signal
    import subprocess
    import sys

    program = subprocess.Popen(
        [sys.executable, "-c", _HANDED_OVER, "sleep"], stdout=subprocess.PIPE
    )
    repl = reaper = None
    try:
        repl_pid, reaper_pid = map(int, program.stdout.readline().split())
        repl, reaper = ProcessWatch(repl_pid), ProcessWatch(reaper_pid)
        program.send_signal(signal.SIGKILL)
        assert program.wait(timeout=60) == -signal.SIGKILL
        assert repl.wait(60), "the REPL outlived the process"
        assert reaper.wait(60), "the reaper outlived the process"
    finally:
        program.kill()
        program.wait()
        for watched in (repl, reaper):
            if watched is not None:
                watched.kill()


#: A program that opens a Lean session, gives it an attempt that sleeps for
#: five minutes, and says which processes the REPL is.
_BUSY_REPL = """\
import threading, time
import psutil
from lanky.oracles.lean import LeanSession
session = LeanSession(timeout=900)
assert session.start(), session.error
attempt = "theorem t : True := by\\n  sleep 300000\\n  trivial\\n"
threading.Thread(target=session.run, args=(attempt,), daemon=True).start()
time.sleep(3)
lake = psutil.Process(session.server._proc.pid)
print(*[process.pid for process in [lake, *lake.children(recursive=True)]], flush=True)
time.sleep(900)
"""


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX process groups")
def test_a_busy_repl_ends_with_a_process_ended_by_sigkill(lean_oracle: LeanOracle) -> None:
    """#46 with a real Lean: the REPL went on with its five-minute attempt for no one."""
    import signal
    import subprocess
    import sys

    program = subprocess.Popen([sys.executable, "-c", _BUSY_REPL], stdout=subprocess.PIPE)
    watched: list[ProcessWatch] = []
    try:
        watched = [ProcessWatch(int(pid)) for pid in program.stdout.readline().split()]
        assert len(watched) >= 2, "the REPL is lake and the process lake runs"
        program.send_signal(signal.SIGKILL)
        assert program.wait(timeout=60) == -signal.SIGKILL
        for process in watched:
            assert process.wait(60), "the REPL outlived the process"
    finally:
        program.kill()
        program.wait()
        for process in watched:
            process.kill()


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX process groups")
def test_the_reaper_leaves_alone_a_repl_its_session_closed() -> None:
    """A session that closes takes its REPL back, and the reaper ends without killing it.

    Its process group is being stopped another way, and once it is gone its
    number may be another process's. The stand-in here survives its session's
    close, so that what the reaper did shows.
    """
    import subprocess
    import sys

    program = subprocess.run(
        [sys.executable, "-c", _HANDED_OVER, "close"],
        stdout=subprocess.PIPE,
        timeout=120,
        check=True,
    )
    repl_pid, reaper_pid = map(int, program.stdout.split())
    repl, reaper = ProcessWatch(repl_pid), ProcessWatch(reaper_pid)
    try:
        assert reaper.wait(60), "the reaper outlived the process"
        assert not repl.gone(), "the reaper killed a REPL its session had taken back"
    finally:
        repl.kill()


#: :data:`_HANDED_OVER`, but the process forks a child that outlives it.
_FORKED = """\
import os, subprocess, sys, time
from types import SimpleNamespace
import lanky.oracles.lean as lean
repl = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)"],
                        start_new_session=True, stdout=subprocess.DEVNULL)
session = lean.LeanSession()
session.server = SimpleNamespace(_proc=repl, kill=lambda: None)
session._opened()
fork = os.fork()
if fork == 0:
    time.sleep(120)
    os._exit(0)
print(repl.pid, fork, flush=True)
time.sleep(120)
"""


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX process groups")
def test_a_fork_does_not_keep_the_repl_of_its_parent_going() -> None:
    """A fork held the reaper's pipe open, so the REPL outlived its parent while the fork ran.

    The reaper kills when every process holding the pipe has ended, and a
    fork (``multiprocessing``'s default start on Linux) inherits it. The fork
    lets go of it now, so the parent's end is the one the reaper sees.
    """
    import signal
    import subprocess
    import sys

    program = subprocess.Popen([sys.executable, "-c", _FORKED], stdout=subprocess.PIPE)
    repl = fork = None
    try:
        repl_pid, fork_pid = map(int, program.stdout.readline().split())
        repl, fork = ProcessWatch(repl_pid), ProcessWatch(fork_pid)
        program.send_signal(signal.SIGKILL)
        assert program.wait(timeout=60) == -signal.SIGKILL
        assert repl.wait(60), "the REPL outlived its process while a fork of it ran"
        assert not fork.gone(), "the fork ended first, so this shows nothing"
    finally:
        program.kill()
        program.wait()
        for watched in (repl, fork):
            if watched is not None:
                watched.kill()


#: A program that gives a Lean session an attempt that sleeps for five
#: minutes, in its main thread, and says which processes the REPL is. It
#: raises ``KeyboardInterrupt`` on ``SIGINT`` even where it was started with
#: the signal ignored, as a command started in the background by a shell is.
_INTERRUPTED_REPL = """\
import signal, threading, time
import psutil
from lanky.oracles.lean import LeanSession
signal.signal(signal.SIGINT, signal.default_int_handler)
session = LeanSession(timeout=900)
assert session.start(), session.error
lake = psutil.Process(session.server._proc.pid)
def report():
    time.sleep(3)
    print(*[process.pid for process in [lake, *lake.children(recursive=True)]], flush=True)
threading.Thread(target=report, daemon=True).start()
session.run("theorem t : True := by\\n  sleep 300000\\n  trivial\\n")
"""


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX signals")
def test_ctrl_c_ends_a_process_whose_repl_is_busy(lean_oracle: LeanOracle) -> None:
    """#46 with a real Lean: ``SIGINT`` during a five-minute attempt ended nothing for minutes."""
    import signal
    import subprocess
    import sys

    program = subprocess.Popen(
        [sys.executable, "-c", _INTERRUPTED_REPL],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    watched: list[ProcessWatch] = []
    try:
        watched = [ProcessWatch(int(pid)) for pid in program.stdout.readline().split()]
        assert len(watched) >= 2, "the REPL is lake and the process lake runs"
        program.send_signal(signal.SIGINT)
        assert program.wait(timeout=60) == -signal.SIGINT
        for process in watched:
            assert process.wait(60), "the REPL outlived the interrupt"
    finally:
        program.kill()
        program.wait()
        for process in watched:
            process.kill()


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


#: The ``EFFECTIVE`` cells of the documented table, each with the two spaces
#: after it: the header, the rule under it, and what every row is worth.
_EFFECTIVE_CELLS = ("EFFECTIVE  ", "---------  ", "tested     ")


def _read_as_tested(line: str) -> str:
    """A line of the documented table as a machine without Lean prints it.

    With Lean the proof of ``scan_monotone`` rests on its reading, which the
    draws tested (#91), so it is worth ``tested`` and the table has an
    ``EFFECTIVE`` column after the status. Without Lean nothing is worth less
    than its own status, and the column is not there; it is the eleven
    characters after the status column's eight, in every row of the table.
    """
    if line[8:19] in _EFFECTIVE_CELLS:
        line = line[:8] + line[19:]
    return line.replace(f"proved  {'lean':13}", f"tested  {'property-test':13}").replace(
        "4 facts: 1 proved, 3 tested", "4 facts: 4 tested"
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

    That is the README's other claim about the table: the status column changes,
    and the ``EFFECTIVE`` column, which says that the proof is worth the
    ``tested`` reading it rests on, is not needed, and nothing else changes,
    the exit code included. The other columns keep their widths, because the
    property tester decided the other row already. Both documents are held to
    it, so the README's rows are checked here too and not only where Lean is
    installed.
    """
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    printed = _check_gauss(capsys)
    quickstart = _printed_after("docs/quickstart.md", CHECK_GAUSS)
    assert printed == [_read_as_tested(line) for line in quickstart]
    readme = _printed_after("README.md", "lanky check examples/gauss.py")
    _assert_abridged([_read_as_tested(line) for line in readme], printed)


#: The command the quickstart shows the ledger of ``gap.py`` for.
CHECK_GAP = "uv run lanky check gap.py"


def _python_after(document: str, marker: str) -> str:
    """The first ``python`` block in ``document`` after the line that contains ``marker``."""
    lines = (ROOT / document).read_text(encoding="utf-8").splitlines()
    at = next((index for index, line in enumerate(lines) if marker in line), None)
    assert at is not None, f"{document} no longer says {marker!r}"
    start = lines.index("```python", at) + 1
    return "\n".join(lines[start : lines.index("```", start)]) + "\n"


def _block_from(document: str, first: str) -> list[str]:
    """The lines of the fenced block in ``document`` whose first line starts with ``first``.

    A block inside a list item is indented with it, and comes back without
    the indentation, as the command printed it.
    """
    lines = (ROOT / document).read_text(encoding="utf-8").splitlines()
    at = next(
        (index for index, line in enumerate(lines) if line.lstrip().startswith(first)), None
    )
    assert at is not None, f"{document} no longer shows a block starting {first!r}"
    indent = len(lines[at]) - len(lines[at].lstrip())
    end = next(index for index in range(at, len(lines)) if lines[index].strip() == "```")
    return [line[indent:].rstrip() for line in lines[at:end]]


def _div_zero_snippet() -> str:
    """``div_zero`` as the quickstart spells it inline, decorated and given a body."""
    text = (ROOT / "docs" / "quickstart.md").read_text(encoding="utf-8")
    found = re.search(r"`(def div_zero\([^`]*)`", text)
    assert found is not None, "docs/quickstart.md no longer shows div_zero"
    return f'@theorem\n{found.group(1)}:\n    """Total in Lean, an exception in Python."""\n'


def _write_gap(directory: Path, snippet: str) -> Path:
    """``gap.py`` as the quickstart has a reader write it: gauss.py's imports, then ``snippet``.

    The imports are read off ``examples/gauss.py``, from its ``__future__``
    import up to its first theorem, which is what puts the snippet's
    decorator on line 7, where the quickstart's ``WHERE`` column has it. Each
    file gets a directory of its own, so no import of one is taken for the
    other.
    """
    lines = (ROOT / "examples" / "gauss.py").read_text(encoding="utf-8").splitlines(keepends=True)
    start = next(index for index, line in enumerate(lines) if line.startswith("from __future__"))
    end = next(index for index, line in enumerate(lines) if line.startswith("@theorem"))
    directory.mkdir()
    path = directory / "gap.py"
    path.write_text("".join(lines[start:end]) + snippet, encoding="utf-8")
    return path


def _check_gap(path: Path, capsys, code: int) -> list[str]:
    """``lanky check`` on one ``gap.py``, as the lines it prints; it has to exit with ``code``."""
    from lanky import cli

    assert cli.main(["check", str(path)]) == code
    return [line.rstrip() for line in capsys.readouterr().out.splitlines()]


def _gap_rows(tmp_path: Path, capsys) -> tuple[list[str], list[str]]:
    """What ``lanky check`` prints for ``truncated`` and for ``div_zero``."""
    snippet = _python_after("docs/quickstart.md", "Put this in `gap.py`")
    truncated = _check_gap(_write_gap(tmp_path / "truncated", snippet), capsys, 1)
    div_zero = _check_gap(_write_gap(tmp_path / "div_zero", _div_zero_snippet()), capsys, 0)
    return truncated, div_zero


def test_without_lean_the_quickstart_gap_transcripts_hold(monkeypatch, tmp_path, capsys) -> None:
    """The quickstart's ``gap.py`` blocks are a real run too, without Lean.

    ``truncated`` prints the same block with Lean and without, the refutation
    included, and exits 1; ``div_zero`` reads ``assumed`` with no
    ``SEMANTICS`` block, because the only oracle left could not run it, and
    exits 0. The file is written from the quickstart's own snippet.
    """
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    truncated, div_zero = _gap_rows(tmp_path, capsys)
    assert truncated == _printed_after("docs/quickstart.md", CHECK_GAP)
    assert div_zero[2].split()[:4] == ["assumed", "-", "gap.py:7", "div_zero"]
    assert not any(line.startswith("SEMANTICS") for line in div_zero)


def _check_flipped_gauss(
    directory: Path, capsys, code: int, guard: str = "(a < b) & (a > b)"
) -> list[str]:
    """``examples/gauss.py`` with the guard of ``scan_monotone``'s goal flipped, as checked.

    The quickstart has a reader flip ``if a <= b`` to ``if (a < b) & (a > b)``
    in the example itself, so the file keeps its name and its lines; it
    mentions ``a == 7`` as well, a guard only the sampler misses.
    """
    source = (ROOT / "examples" / "gauss.py").read_text(encoding="utf-8")
    assert "if a <= b):" in source
    directory.mkdir()
    path = directory / "gauss.py"
    path.write_text(source.replace("if a <= b):", f"if {guard}):"), encoding="utf-8")
    return _check_gap(path, capsys, code)


def test_without_lean_the_quickstart_goal_guard_warning_holds(
    monkeypatch, tmp_path, capsys
) -> None:
    """The quickstart's warning for a flipped goal guard is a real run, without Lean."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    printed = _check_flipped_gauss(tmp_path / "flipped", capsys, 0)
    warning = _block_from("docs/quickstart.md", "WARNING scan_monotone at gauss.py:39")
    at = printed.index(warning[0])
    assert printed[at : at + len(warning)] == warning
    row = next(line for line in printed if "scan_monotone" in line and "gauss.py:39" in line)
    assert row.split()[:2] == ["tested", "property-test"]


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
    assert "theorem Lanky.commutes" in proved.provenance["lean_source"]


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


def test_a_closed_comparison_means_in_lean_what_it_means_in_python(
    lean_oracle: LeanOracle,
) -> None:
    """``1 - 2 >= 0`` is not proved, and ``-1 != 0`` is, as the integer reading has it."""
    false = Fact(
        id="closed:false",
        kind="coefficient",
        statement="1 - 2 >= 0",
        term=_CLOSED_SUBTRACTION,
        owner="closed_false",
    )
    assert lean_oracle.establish(false).status is Status.ASSUMED
    true = Fact(
        id="closed:true",
        kind="coefficient",
        statement="-1 != 0",
        term=prim.Comparison(-1, "!=", 0),
        owner="closed_true",
    )
    proved = lean_oracle.establish(true)
    assert proved.status is Status.PROVED
    assert "(-1 : Int) ≠ 0" in proved.provenance["lean_source"]


def test_the_pytential_demonstrations_arithmetic_is_proved(
    lean_oracle: LeanOracle, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The one part of ``examples/pytential_skie.py`` Lean touches, it proves.

    Each second-kind claim states that its identity coefficient is not zero,
    as integer arithmetic on the numerator; the verdicts themselves rest on
    axioms and a rule engine, and nothing about compactness goes to Lean.
    """
    examples = Path(__file__).resolve().parent.parent / "examples"
    monkeypatch.syspath_prepend(str(examples))
    monkeypatch.setattr(registry, "oracles", list(registry.oracles))
    with registry.collecting():
        demo = import_path(examples / "pytential_skie.py")
    coefficients = [
        fact for claim in demo.CLAIMS for fact in claim.facts() if fact.kind == "coefficient"
    ]
    assert [fact.statement for fact in coefficients] == [
        "coefficient of I: -1/2 != 0",
        "coefficient of I: 1/2 != 0",
        "coefficient of I: 1/2 != 0",
    ]
    for fact in coefficients:
        proved = lean_oracle.establish(fact)
        assert proved.status is Status.PROVED, proved.provenance


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

    # A timeout is a failed attempt, not a refutation either. The timeout that
    # applies is the session's, so the impatient oracle gets a session of its
    # own: an oracle handed the module's session never timed out at all.
    impatient = LeanOracle(session=LeanSession(timeout=1e-6))
    try:
        result = impatient.establish(plainly_false.fact())
    finally:
        impatient.session.close()
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_reason"].startswith("TimeoutError")
    assert result.provenance["lean_tried"] == len(tactic_ladder(statement_of(plainly_false.term)))


def test_a_session_survives_an_attempt_that_timed_out(lean_oracle: LeanOracle) -> None:
    """#32 with a real Lean: the attempts after a timeout are elaborated, not refused.

    The driver kills the REPL on a timeout. The next command used to come back
    as "The Lean server is not running", on this fact and on every fact after
    it in the process; the session now starts the REPL again first.
    """
    source = "theorem t (x : Nat) : x + 0 = x := by omega\n"
    session = LeanSession(timeout=lean_oracle.session.timeout)
    try:
        assert session.run(source) == (True, "")
        session.timeout = 1e-6
        closed, detail = session.run(source)
        assert not closed
        assert detail.startswith("TimeoutError")
        session.timeout = lean_oracle.session.timeout
        assert session.run(source) == (True, "")
        assert session.error is None
        proved = LeanOracle(session=session).establish(commutes.fact())
        assert proved.status is Status.PROVED
    finally:
        session.close()


#: A true claim whose one attempt keeps Lean busy for a minute before it
#: proves it: ``sleep`` is a tactic of core Lean.
_SLEEPS_IN_LEAN = '''\
from __future__ import annotations

from lanky import theorem
from lanky.oracles.lean import use_tactic
from lanky.prelude import Nat


@theorem
def sleeps(a: Nat, b: Nat) -> a + b == b + a:
    """True, with a script that sleeps in Lean before it proves it."""


use_tactic(sleeps, "sleep 60000\\n  omega")
'''


@pytest.mark.skipif("sys.platform == 'win32'", reason="POSIX signals")
@pytest.mark.parametrize("name", ["SIGTERM", "SIGKILL", "SIGINT"])
def test_a_child_ended_with_the_command_stops_its_lean_repl(
    lean_oracle: LeanOracle, tmp_path, name
) -> None:
    """#28: the Lean REPL of a child of ``lanky check`` ends with the child.

    lean-interact starts the REPL in a session of its own, so no signal that
    ends the child reaches it, and the timeout that would stop its attempt is
    kept by the child. A child ended of ``SIGTERM`` (which it gets when the
    command is ended alone, by ``SIGTERM`` or ``SIGKILL``), or of the
    ``SIGKILL`` the command sent it on an interrupt, left the REPL going on
    with the attempt it was given, a minute here. The child now kills its
    REPLs on ``SIGTERM``, and the command sends it ``SIGTERM`` first. Ended
    alone, the command's threads end one after another, and each sends the
    child ``SIGTERM`` again; the child used to end of the second one while it
    was still stopping the REPL.
    """
    import signal
    import subprocess
    import sys
    import time

    psutil = pytest.importorskip("psutil")
    if name == "SIGINT" and signal.getsignal(signal.SIGINT) is signal.SIG_IGN:
        pytest.skip("SIGINT is ignored here, and so it is in the command")
    (tmp_path / "a").mkdir()
    (tmp_path / "a" / "sleeps.py").write_text(_SLEEPS_IN_LEAN, encoding="utf-8")
    (tmp_path / "b").mkdir()
    (tmp_path / "b" / "other.py").write_text("OTHER = 1\n", encoding="utf-8")
    command = subprocess.Popen(
        [sys.executable, "-m", "lanky.cli", "check", "a/sleeps.py", "b/other.py"],
        cwd=tmp_path,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    repl: list = []
    try:
        deadline = time.monotonic() + 120
        while not repl:
            assert command.poll() is None, "the command ended before its child started Lean"
            assert time.monotonic() < deadline, "no Lean REPL was started"
            time.sleep(0.1)
            try:
                descendants = psutil.Process(command.pid).children(recursive=True)
                servers = [process for process in descendants if process.name() == "repl"]
                repl = [*servers, *(process.parent() for process in servers)]
            except psutil.NoSuchProcess:  # one that came and went while it was looked at
                repl = []
        time.sleep(3)  # the attempt is under way
        assert all(process.is_running() for process in repl), "the REPL ended of itself"
        command.send_signal(getattr(signal, name))
        command.wait(timeout=30)
        _, alive = psutil.wait_procs(repl, timeout=15)
        assert alive == [], "the Lean REPL outlived the child that started it"
    finally:
        if command.poll() is None:
            command.kill()
            command.wait()
        for process in repl:
            try:
                process.kill()
            except psutil.NoSuchProcess:
                pass


#: #38's reproduction, with the two cases its review added: a goal whose
#: variables the induction strategy has to name, and a variable named like the
#: Boolean literal.
_KEYWORD_CLAIMS = '''\
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Bool, Fin, Fn, Nat


@theorem
def commutes(a: Nat, b: Nat) -> a + b == b + a:
    """A name Lean accepts."""


@theorem
def scoped(a: Nat, b: Nat) -> a + b == b + a:
    """The same claim under a name that is a Lean keyword."""


@theorem
def binders(fun: Nat, at: Nat) -> fun + at == at + fun:
    """The same claim over variables whose names are Lean keywords."""


@theorem
def named(h0: Nat, b: Nat) -> h0 + b == b + h0:
    """The same claim over a variable named like the first hypothesis."""


@theorem
def scan(
    size: Nat,
    cnt: Fn[Fin[size], Nat],
    off: Fn[Fin[size + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
) -> all(off(show) <= off(at) for show in Fin[size + 1] for at in Fin[size + 1] if show <= at):
    """The scan's monotonicity, with its goal's variables named like Lean keywords."""


@theorem
def truth(true: Bool) -> true == True:
    """False at true = False."""


@theorem
def empty(fun: Nat, at: Nat, h0: fun + at < 0) -> fun == at:
    """Vacuous: no two naturals sum below zero."""


@theorem
def unreached(n: Nat) -> all(show == n for show in Fin[n] if show > n + 5):
    """Vacuous: the goal's guard holds nowhere."""
'''


def test_lean_proves_claims_named_like_keywords(lean_oracle: LeanOracle, tmp_path) -> None:
    """#38: every row below ``commutes`` read ``tested``, with a parse error as its reason.

    ``scoped`` is a keyword theorem name, ``fun`` and ``at`` are keyword
    variables, the first hypothesis shadowed the variable ``h0``, and the
    scan's goal names its variables ``show`` and ``at``, which the induction
    strategy has to write as the statement does. ``truth`` is false, and Lean
    proved it, reading ``true = true``; the tester refutes it. The questions
    whether a claim is vacuous are printed the same way, and they failed the
    same way: ``empty``'s hypotheses and ``unreached``'s goal guard only got a
    warning that no draw satisfied them, and the check passed.
    """
    from lanky.check import check_path

    path = tmp_path / "p8_keywords.py"
    path.write_text(_KEYWORD_CLAIMS, encoding="utf-8")
    by_owner = {fact.owner: fact for fact in claims(check_path(path))}
    for owner in ("commutes", "scoped", "binders", "named", "scan"):
        fact = by_owner[owner]
        assert (fact.status, fact.decided_by) == (Status.PROVED, "lean"), (
            owner,
            fact.provenance.get("lean_reason"),
        )
    assert "theorem Lanky.«scoped» (a : Int)" in by_owner["scoped"].provenance["lean_source"]
    truth = by_owner["truth"]
    assert (truth.status, truth.decided_by) == (Status.REFUTED, "property-test")
    for owner in ("empty", "unreached"):
        assert by_owner[owner].is_vacuous, (owner, by_owner[owner].provenance)


#: #61 and #64: claims Lean proved and Python refutes, or cannot read at all.
_WRONG_PROOF_CLAIMS = '''\
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def free_goal() -> x - 1 >= 0:
    """x is bound by nothing, and false at x = 0 for whoever binds it as an integer."""


@theorem
def disjunctive_guard(m: Nat) -> any(x == -1 for x in Fin[m] if (x > 5) | (x < 1)):
    """False: the guard admits 0 and the points past 5, and none of them is -1."""


@theorem
def rounds_half_up() -> round(0.5) == 1:
    """False in Python, where round(0.5) is 0."""
'''


def test_lean_proves_no_claim_python_refutes(lean_oracle: LeanOracle, tmp_path) -> None:
    """#61 and #64: two wrong proofs, through ``lanky check`` with Lean.

    ``free_goal`` names an ``x`` nothing binds, which Lean bound implicitly as
    a natural, and ``omega`` proved ``x - 1 ≥ 0`` about it; it is declined
    now, and the tester cannot run it either, so it stays ``assumed``.
    ``disjunctive_guard`` printed its guard without brackets, and Lean proved
    the disjunction that made of it, at ``x = -1``; the tester refutes it.
    ``round`` is Python's now (#63), so ``rounds_half_up`` is ``0 == 1``.
    """
    from lanky.check import check_path

    path = tmp_path / "wrong_proofs.py"
    path.write_text(_WRONG_PROOF_CLAIMS, encoding="utf-8")
    by_owner = {fact.owner: fact for fact in claims(check_path(path))}
    free = by_owner["free_goal"]
    assert free.status is Status.ASSUMED, free.provenance
    assert free.decided_by is None
    for owner in ("disjunctive_guard", "rounds_half_up"):
        fact = by_owner[owner]
        assert (fact.status, fact.decided_by) == (Status.REFUTED, "property-test"), (
            owner,
            fact.provenance,
        )



#: #79, #80 and #88: claims whose term says something else than the annotation,
#: each proved by Lean on ``main`` (see ``tests/test_faithful.py`` for them all).
_MISREAD_CLAIMS = """\
from __future__ import annotations

import collections

from lanky import theorem
from lanky.prelude import Fin, Fn, Nat


def table(i):
    return {0: 1}.get(i, 0)


@theorem
def types_differ(n: Nat) -> (Fin[n] != Fin[3]) | (n == 4):
    \"\"\"#79: False at n = 3.\"\"\"


@theorem
def through_helper(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == table(i) for i in Fin[n]):
    \"\"\"#80: False at i = 0.\"\"\"


@theorem
def counted(n: Nat, f: Fn[Fin[n], Nat]) -> all(
    f(i) * 0 == collections.Counter([i, 0])[0] - 1 for i in Fin[n]
):
    \"\"\"#80: False at i = 0.\"\"\"


@theorem
def identity(n: Nat, f: Fn[Fin[n], Nat]) -> all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n]):
    \"\"\"#88: False at i = 0.\"\"\"


@theorem
def named(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == {"i": 0}.get(i.name, 1) for i in Fin[n]):
    \"\"\"#88: a number has no name.\"\"\"
"""


def test_lean_proves_no_claim_whose_reading_is_refuted(lean_oracle: LeanOracle, tmp_path) -> None:
    """#91: what #79, #80 and #88 made Lean prove is kept from it.

    Asked about the term alone, Lean proves each, as it did on ``main``
    through ``lanky check``: the term is true, and says something else than
    the annotation. Through ``lanky check`` each claim's reading is refuted
    at a point now, and the claim is offered to no oracle, Lean included.
    """
    from lanky.check import check_path
    from lanky.plugins import registry

    path = tmp_path / "misread.py"
    path.write_text(_MISREAD_CLAIMS, encoding="utf-8")
    with registry.collecting():
        module = import_path(path)
    for name in ("types_differ", "through_helper", "counted", "identity", "named"):
        proved = lean_oracle.establish(getattr(module, name).fact())
        assert (proved.status, proved.decided_by) == (Status.PROVED, "lean"), name
    ledger = check_path(path)
    for fact in ledger:
        if fact.is_reading:
            assert fact.status is Status.REFUTED, (fact.owner, fact.provenance)
        else:
            assert (fact.status, fact.decided_by) == (Status.ASSUMED, None), fact.owner
            assert "lean_tried" not in fact.provenance and "tactic" not in fact.provenance


def _disjunctive_guard():
    @theorem
    def disjunctive_guard(m: Nat) -> any(x == -1 for x in Fin[m] if (x > 5) | (x < 1)):
        """False: the guard admits 0 and the points past 5, and none of them is -1."""

    return disjunctive_guard


def test_a_proof_of_the_existential_lean_misread_is_refused(lean_oracle: LeanOracle) -> None:
    """#61: the witness ``-1`` proved an existential whose guard admits no ``-1``.

    The guard printed without brackets made the goal ``∃ x : Int, (0 ≤ x ∧ x
    < m ∧ x > 5) ∨ (x < 1 ∧ x = -1)``, and a script pinned with
    :func:`lanky.oracles.lean.use_tactic`, the way an existential is proved,
    closed it with ``-1`` as the witness: the kernel checked a proof of a
    statement Python refutes. Bracketed, the same script does not elaborate.
    """
    claim = _disjunctive_guard()
    assert claim.report().ok is False
    fact = claim.fact()
    lean_oracle.tactics[fact.id] = "exact ⟨-1, Or.inr ⟨by decide, rfl⟩⟩"
    try:
        result = lean_oracle.establish(fact)
    finally:
        lean_oracle.tactics.clear()
    assert result.status is Status.ASSUMED, result.provenance.get("lean_source")


def test_the_oracle_declines_a_free_name_and_says_why(lean_oracle: LeanOracle) -> None:
    """#64: asked directly, the oracle declines a statement with a free name, naming it."""
    fact = Fact(
        id="free:x",
        kind="theorem",
        statement="x - 1 >= 0",
        term=Forall((), Var("x") - 1 >= 0),
        owner="free_x",
    )
    assert not lean_oracle.can_establish(fact)
    declined = lean_oracle.establish(fact)
    assert declined.status is Status.ASSUMED
    assert "mentions x, which no parameter or binder of it binds" in (
        declined.provenance["declined"]
    )
    # the same statement with x bound as an integer is false, and not proved
    bound = Fact(
        id="bound:x",
        kind="theorem",
        statement="x : Int |- x - 1 >= 0",
        term=Forall(((Var("x"), Int),), Var("x") - 1 >= 0),
        owner="bound_x",
    )
    assert lean_oracle.establish(bound).status is Status.ASSUMED


#: #39 and #43: claims named like root declarations of core Lean, and
#: variables named like what the printer and the induction write.
_ROOT_NAME_CLAIMS = '''\
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Fn, Nat


@theorem
def and_comm(a: Nat, b: Nat) -> a + b == b + a:
    """Named like a root declaration of core Lean."""


@theorem
def trivial(a: Nat, b: Nat) -> a + b == b + a:
    """Another."""


@theorem
def id(a: Nat, b: Nat) -> a + b == b + a:
    """Another."""


@theorem
def absurd(a: Nat, b: Nat) -> a + b == b + a:
    """Another."""


@theorem
def congr(a: Nat, b: Nat) -> a + b == b + a:
    """Another."""


@theorem
def inferInstanceAs(a: Nat, b: Nat) -> a + b == b + a:
    """A keyword that is also a root declaration."""


@theorem
def True_(a: Nat, b: Nat) -> a + b == b + a:
    """Cleaned into True."""


@theorem
def typed(Int: Nat, b: Nat) -> Int + b == b + Int:
    """A variable named like the type a natural prints as."""


@theorem
def scan_int(
    Int: Nat,
    cnt: Fn[Fin[Int], Nat],
    off: Fn[Fin[Int + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[Int]),
) -> all(off(p) <= off(q) for p in Fin[Int + 1] for q in Fin[Int + 1] if p <= q):
    """The scan's monotonicity over a size named Int, which the induction names."""


@theorem
def scan_rfl(
    size: Nat,
    cnt: Fn[Fin[size], Nat],
    off: Fn[Fin[size + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
) -> all(off(a) <= off(rfl) for a in Fin[size + 1] for rfl in Fin[size + 1] if a <= rfl):
    """The scan's monotonicity, inducing on a variable named rfl."""
'''


def test_lean_proves_claims_named_like_what_lean_declares(
    lean_oracle: LeanOracle, tmp_path
) -> None:
    """#39 and #43: every row read ``tested``, each for its own reason.

    The first seven with "has already been declared". ``typed`` with "type
    expected", since the variable ``Int`` was the type of ``b``.
    ``scan_int``'s induction named ``Int.eq_ofNat_of_zero_le`` and the casts
    as fields of its size. ``scan_rfl``'s introduced its variable as ``rfl``,
    which ``intro`` and ``rcases`` read as a substitution.
    """
    from lanky.check import check_path

    path = tmp_path / "root_names.py"
    path.write_text(_ROOT_NAME_CLAIMS, encoding="utf-8")
    by_owner = {fact.owner: fact for fact in claims(check_path(path))}
    assert len(by_owner) == 10
    for owner, fact in by_owner.items():
        assert (fact.status, fact.decided_by) == (Status.PROVED, "lean"), (
            owner,
            fact.provenance.get("lean_reason"),
        )
    assert "theorem Lanky.and_comm (a : Int)" in by_owner["and_comm"].provenance["lean_source"]
    assert "(b : _root_.Int)" in by_owner["typed"].provenance["lean_source"]
    assert "induction x with" in by_owner["scan_rfl"].provenance["tactic"]


#: Lean source that prints every token of the parser's table, one to a line.
_PRINT_TOKENS = """\
open Lean Parser in
#eval show CoreM Unit from do
  for token in (getTokenTable (← getEnv)).findPrefix "" do
    IO.println token
"""


def _reserved_words(session: LeanSession, source: str) -> set[str]:
    """The words spelled like ASCII identifiers that Lean reads as tokens, as it prints them."""
    from lean_interact import Command

    assert session.start(), session.error
    response = session.server.run(Command(cmd=source), timeout=session.timeout)
    printed = "\n".join(
        str(item.data)
        for item in response.messages
        if str(getattr(item, "severity", "")).endswith("info")
    )
    return {word for word in printed.split() if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", word)}


def test_every_word_lean_reserves_is_quoted(lean_oracle: LeanOracle) -> None:
    """The keyword list is Lean's own, read from the Lean this suite runs against.

    A toolchain that reserves a word the list does not have fails here rather
    than in a proof. And a statement over a variable named after each word of
    the list elaborates, so every quoted name is one Lean reads.
    """
    # a session of its own, so that the module's does not keep Lean imported
    session = LeanSession(timeout=lean_oracle.session.timeout)
    try:
        reserved = _reserved_words(session, f"import Lean\n\n{_PRINT_TOKENS}")
    finally:
        session.close()
    assert {"fun", "at", "scoped", "show", "Type"} <= reserved
    assert sorted(word for word in reserved if not lean_identifier(word).startswith("«")) == []

    from lanky.lean import _KEYWORDS

    everything = Forall(tuple((Var(word), Int) for word in sorted(_KEYWORDS)), True)
    closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(everything)}\n")
    assert closed, detail


def test_a_session_runs_lean_source_directly(lean_oracle: LeanOracle) -> None:
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 0 = x := by omega\n")
    assert closed, detail
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 1 = x := by omega\n")
    assert not closed
    assert "omega" in detail


def test_lean_refuses_a_name_the_declaration_does_not_bind(lean_oracle: LeanOracle) -> None:
    """#68: an unbound name is an unknown identifier to Lean, and not an implicit variable.

    The printer declines a statement with a free name (#64). Behind it, Lean
    elaborates every declaration lanky sends with ``autoImplicit`` off, so
    one the printer let through is refused rather than bound at a type Lean
    infers: ``x - 1 ≥ 0`` with ``x`` bound by nothing was a statement about a
    natural ``x``, which ``omega`` proved, and still is with the option on.
    """
    from lanky.lean import ELABORATION_OPTIONS

    statement = LeanStatement("free_goal", (), (), "x - 1 ≥ 0")
    source = statement.source("omega")
    assert source.startswith(f"{ELABORATION_OPTIONS}\ntheorem Lanky.free_goal : ")
    closed, detail = lean_oracle.session.run(source)
    assert not closed
    assert "Unknown identifier" in detail or "unknown identifier" in detail, detail
    closed, detail = lean_oracle.session.run(source.removeprefix(f"{ELABORATION_OPTIONS}\n"))
    assert closed, detail


def test_checking_the_example_file_proves_the_scan(lean_oracle: LeanOracle) -> None:
    # The demo, end to end: the file is imported, the claims become facts, and
    # the strongest oracle that can take each one takes it.
    from pathlib import Path

    from lanky.check import check_path

    example = Path(__file__).resolve().parent.parent / "examples" / "gauss.py"
    ledger = check_path(example)
    by_owner = {fact.owner: fact for fact in claims(ledger)}
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
    # the proof, worth the reading it rests on, which the draws tested (#91)
    assert any(
        line.startswith("proved  tested     lean ") and "scan_monotone" in line for line in readme
    )


def test_the_quickstart_gap_transcripts_are_what_check_prints(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """The quickstart's ``gap.py`` blocks are what ``lanky check`` prints with Lean.

    They were kept by hand: the rendering of a refuted fact, the tester's
    counterexample and the semantics note could all drift from them. With
    Lean, ``truncated`` is still refuted by the tester, and ``div_zero`` reads
    ``proved lean`` with the ``SEMANTICS`` block the quickstart shows.
    """
    truncated, div_zero = _gap_rows(tmp_path, capsys)
    assert truncated == _printed_after("docs/quickstart.md", CHECK_GAP)
    assert div_zero[2].split()[:5] == ["proved", "tested", "lean", "gap.py:7", "div_zero"]
    semantics = _block_from("docs/quickstart.md", "SEMANTICS div_zero")
    assert semantics[0] in div_zero
    at = div_zero.index(semantics[0])
    assert div_zero[at : at + len(semantics)] == semantics


def test_lean_does_not_prove_an_integral_fraction_base_by_truncation(
    lean_oracle: LeanOracle,
) -> None:
    """``1 - Fraction(2, 1) ** n >= 0`` is false at ``n = 1``, and Lean must not prove it.

    Printed without the ``Int`` ascription it was a statement about ``Nat``,
    which Lean proved, and the check read ``proved`` for a claim that is false
    as Python computes it. Lean now fails to prove it, and the tester, which
    could not evaluate a ``Fraction`` literal either, refutes it.
    """
    from lanky.check import establish

    fact = Fact(
        id="fraction_base", kind="theorem", statement="1 - 2**n >= 0", term=_FRACTION_BASE
    )
    closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(_FRACTION_BASE)}\n")
    assert closed, detail
    assert lean_oracle.establish(fact).status is not Status.PROVED
    checked = establish(fact)
    assert checked.status is Status.REFUTED
    assert checked.decided_by == "property-test"


def test_lean_does_not_prove_a_closed_base_by_truncation(lean_oracle: LeanOracle) -> None:
    """``(1 - 2) ** n >= 0`` is false at ``n = 1``, and Lean must not prove it.

    Printed without the ``Int`` ascription its base was a truncated ``Nat``
    subtraction, and Lean proved the statement; the tester refutes it.
    """
    from lanky.check import establish

    fact = Fact(id="closed_base", kind="theorem", statement="(1 - 2)**n >= 0", term=_CLOSED_BASE)
    closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(_CLOSED_BASE)}\n")
    assert closed, detail
    assert lean_oracle.establish(fact).status is not Status.PROVED
    checked = establish(fact)
    assert checked.status is Status.REFUTED
    assert checked.decided_by == "property-test"


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
    (fact,) = claims(check_path(path))
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
    (fact,) = claims(check_path(path))
    assert fact.status is Status.PROVED
    assert fact.decided_by == "lean"
    assert fact.is_vacuous
    assert fact.provenance["vacuous_by"] == "lean"
    assert ": False := by" in fact.provenance["vacuous_evidence"]["lean_source"]
    assert cli.main(["check", str(path)]) == 1
    # worth the reading it rests on, which the draws tested (#91)
    assert "proved (vacuous)  tested     lean" in capsys.readouterr().out


_CLOSED = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Nat\n\n\n"
    "@theorem\n"
    "def closed_flipped() -> all(k >= 0 for k in Nat if (k > 5) & (k < 3)):\n"
    '    """No parameters: the goal\'s universal is the goal, not the statement."""\n\n\n'
    "@theorem\n"
    "def closed_rare() -> all(k >= 0 for k in Nat if k > 100):\n"
    '    """No parameters, and a guard no draw reaches."""\n\n\n'
    "@theorem\n"
    "def closed_nested() -> all(all(k >= j for k in Nat if (k > 5) & (k < 3)) for j in Nat):\n"
    '    """No parameters: the guard of the inner universal is not the goal\'s."""\n'
)


def test_lean_reads_a_parameterless_theorems_goal_as_its_goal(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """#35 with a real Lean: the theorem is stated with no parameters, and its goal quantifies.

    ``closed_flipped`` was proved from the goal's guard as though it were the
    hypotheses, and marked vacuous because "the hypotheses are inconsistent";
    it is vacuous because the guard of its goal is empty. ``closed_rare`` is
    proved, with no warning about hypotheses it does not have, and
    ``closed_nested``, whose goal's outermost quantifier reaches its points,
    is proved and not vacuous.
    """
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "closed.py"
    path.write_text(_CLOSED, encoding="utf-8")
    facts = {fact.owner: fact for fact in claims(check_path(path))}
    for fact in facts.values():
        assert fact.status is Status.PROVED
        assert fact.decided_by == "lean"
        assert "unsatisfied" not in fact.provenance
        assert f"theorem Lanky.{fact.owner} : ∀ " in fact.provenance["lean_source"]
    assert facts["closed_flipped"].provenance["vacuous"] == (
        "the goal's guard is empty wherever the hypotheses hold: proved by lean"
    )
    assert not facts["closed_rare"].is_vacuous
    assert not facts["closed_nested"].is_vacuous
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "hypotheses never satisfied" not in printed
    assert "VACUOUS closed_flipped" in printed
    assert "VACUOUS closed_nested" not in printed


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
    (fact,) = claims(check_path(path))
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
    (fact,) = claims(check_path(path))
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
    (fact,) = claims(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.is_vacuous
    assert cli.main(["check", str(path)]) == 1


_FLIPPED = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Fin, Fn, Nat\n\n\n"
    "@theorem\n"
    "def flipped(\n"
    "    n: Nat,\n"
    "    cnt: Fn[Fin[n], Nat],\n"
    "    off: Fn[Fin[n + 1], Nat],\n"
    "    h: (off(0) == 0) & all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),\n"
    ") -> all(off(p) <= off(q) for p in Fin[n + 1] for q in Fin[n + 1] if (p < q) & (p > q)):\n"
    '    """The guard can never hold, so the goal holds at every draw."""\n'
)


def test_lean_shows_a_goal_guard_empty_and_the_claim_vacuous(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """#17 with a real Lean: the goal is proved from its guard, which is shown empty.

    ``omega`` closes the goal from ``p < q`` and ``p > q``, which is a valid
    proof of a goal that says nothing. The tester finds that no draw got
    through the guard, and Lean proves the guard empty wherever the
    hypotheses hold (the goal's body replaced by ``False``).
    """
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "flipped.py"
    path.write_text(_FLIPPED, encoding="utf-8")
    (fact,) = claims(check_path(path))
    assert fact.status is Status.PROVED
    assert fact.decided_by == "lean"
    assert fact.is_vacuous
    assert fact.provenance["vacuous_by"] == "lean"
    assert fact.provenance["vacuous"].startswith("the goal's guard is empty")
    source = fact.provenance["vacuous_evidence"]["lean_source"]
    assert "p < q → p > q → False := by" in source
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "proved (vacuous)  tested     lean" in printed
    assert "VACUOUS flipped at flipped.py:7" in printed


def test_lean_leaves_a_goal_guard_the_sampler_misses_to_a_warning(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """``i == 7`` has a point once ``n`` is above 7, where no draw looks, and is not empty."""
    from lanky import cli
    from lanky.check import check_path

    path = tmp_path / "rare.py"
    path.write_text(
        _FLIPPED.replace(
            "all(off(p) <= off(q) for p in Fin[n + 1] for q in Fin[n + 1] if (p < q) & (p > q))",
            "all(off(p) >= 0 for p in Fin[n + 1] if p == 7)",
        ),
        encoding="utf-8",
    )
    (fact,) = claims(check_path(path))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert fact.provenance["goal_unreached"] == (
        "the goal's guard p == 7 never held in 200 valid draws"
    )
    assert cli.main(["check", str(path)]) == 0
    assert "WARNING flipped at rare.py:7" in capsys.readouterr().out


_SCOPED = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Fin, Fn, Nat\n\n\n"
    "@theorem\n"
    "def below_three(\n"
    "    n: Nat, off: Fn[Fin[n + 1], Nat], h: n < 3\n"
    ") -> all(off(i) >= 0 for i in Fin[n + 1] if i > 5):\n"
    '    """The guard has a point once n is 6, and none where the hypothesis holds."""\n'
)


def test_lean_asks_whether_a_goal_guard_is_empty_under_the_hypotheses(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """``i > 5`` is empty wherever ``n < 3`` holds, and has a point once ``n`` is 6.

    The question put to Lean keeps the hypotheses, so with ``h`` the guard is
    shown empty and the claim is vacuous. Without ``h`` no draw gets through
    the guard either, since the sizes drawn stay below 6, but it is not empty,
    so Lean cannot show it empty and the check only warns: a guard empty for
    some values of the variables is not vacuous.
    """
    from lanky import cli
    from lanky.check import check_path

    scoped = tmp_path / "scoped.py"
    scoped.write_text(_SCOPED, encoding="utf-8")
    (fact,) = claims(check_path(scoped))
    assert fact.status is Status.PROVED
    assert fact.is_vacuous
    assert fact.provenance["vacuous"] == (
        "the goal's guard is empty wherever the hypotheses hold: proved by lean"
    )
    assert cli.main(["check", str(scoped)]) == 1
    assert "VACUOUS below_three at scoped.py:7" in capsys.readouterr().out

    unscoped = tmp_path / "unscoped.py"
    unscoped.write_text(_SCOPED.replace(", h: n < 3", ""), encoding="utf-8")
    (fact,) = claims(check_path(unscoped))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert fact.provenance["goal_unreached"] == (
        "the goal's guard i > 5 never held in 200 valid draws"
    )
    assert cli.main(["check", str(unscoped)]) == 0
    printed = capsys.readouterr().out
    assert "WARNING below_three at unscoped.py:7" in printed
    assert "VACUOUS" not in printed


def test_lean_shows_the_quickstart_flipped_goal_guard_vacuous(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """What the quickstart says Lean does with the flipped guard: vacuous, and exit 1."""
    printed = _check_flipped_gauss(tmp_path / "flipped", capsys, 1)
    row = next(line for line in printed if "scan_monotone" in line and "gauss.py:39" in line)
    assert row.startswith("proved (vacuous)  tested     lean")
    assert any(line.startswith("VACUOUS scan_monotone at gauss.py:39") for line in printed)
    assert not any(line.startswith("WARNING") for line in printed)


def test_lean_leaves_the_quickstart_guard_the_sampler_misses_to_a_warning(
    lean_oracle: LeanOracle, tmp_path, capsys
) -> None:
    """What the quickstart says of ``a == 7``: the warning with Lean too, and exit 0.

    No draw has a point ``7``, since the sizes drawn stay below it, and Lean
    cannot show the guard empty, because it is not.
    """
    printed = _check_flipped_gauss(tmp_path / "rare", capsys, 0, guard="a == 7")
    assert (
        "WARNING scan_monotone at gauss.py:39: the goal's guard a == 7 never held "
        "in 200 valid draws"
    ) in printed
    assert "  no oracle could show it empty, so the goal may be vacuous" in printed
    assert not any(line.startswith("VACUOUS") for line in printed)


def test_the_statement_the_oracle_sends_is_the_one_it_records(
    lean_oracle: LeanOracle,
) -> None:
    proved = lean_oracle.establish(scan_monotone.fact())
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert isinstance(statement, LeanStatement)
    assert proved.provenance["lean_source"] == statement.source(proved.provenance["tactic"])


# }}}
