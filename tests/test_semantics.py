"""Where lanky's Python reading and Lean's reading still disagree, and where not.

Every oracle reads a statement as integer arithmetic (see ``lanky.lean``), so
subtraction over ``Nat`` and floor division over ``Int`` carry no note any
more. Division by something that may be zero is the gap that is left: Lean's
division is total and Python's raises.
"""

from __future__ import annotations

from lanky import semantics, theorem
from lanky.lean import print_lean
from lanky.prelude import Fin, Fn, Int, Nat


def _make_subtracts():
    """Build the statement ``n - 1 >= 0`` over ``Nat``.

    It lives in a function rather than at module level because it is *false*
    under lanky's Python reading, which is the whole point of it, and a
    module-level theorem is collected and run by lanky's own pytest plugin.
    """

    @theorem
    def subtracts(n: Nat) -> n - 1 >= 0:
        """False at n = 0, in Python and in the statement Lean is given."""

    return subtracts


_subtracts = _make_subtracts()


@theorem
def adds(n: Nat) -> n + 1 > n:
    """Index arithmetic: both readings agree."""


def _make_divides():
    """Build ``(k // 2) * 2 == k`` over ``Int``; false at every odd ``k``."""

    @theorem
    def divides(k: Int) -> (k // 2) * 2 == k:
        """Floor division by a literal: one reading, and it is false."""

    return divides


_divides = _make_divides()


@theorem
def divides_a_natural(n: Nat) -> (n // 2) * 2 <= n:
    """Over Nat the two readings agree, so this is not flagged."""


@theorem
def indexes(n: Nat, i: Fin[n]) -> i + 1 <= n:
    """A bounded index is a natural, which is what the note reads."""


def test_only_a_division_that_may_be_by_zero_is_flagged() -> None:
    """Subtraction and floor division mean the same thing to every oracle now.

    ``NAT_SUBTRACTION`` and ``INT_DIVISION`` were notes about two readings of
    one statement. With one reading there is nothing to note, and the notes
    and their cross-check are gone.
    """
    assert semantics.notes(_subtracts.term) == ()
    assert semantics.notes(adds.term) == ()
    assert semantics.notes(_divides.term) == ()
    assert semantics.notes(divides_a_natural.term) == ()
    assert semantics.notes(None) == ()
    assert not hasattr(semantics, "NAT_SUBTRACTION")
    assert not hasattr(semantics, "INT_DIVISION")


def test_a_bounded_index_counts_as_a_natural() -> None:
    """``Fin[n]`` is a natural below ``n``, so its sort is ``Nat``."""
    assert semantics.sorts_of(indexes.term) == {"Nat"}
    assert semantics.notes((indexes.term.body - 1) >= 0) == ()


def test_the_reading_lean_gets_is_the_one_python_runs() -> None:
    """Why subtraction needs no note, spelled out as a test.

    Under lanky's Python reading the statement is false at ``n = 0``. The Lean
    source the printer emits is over ``Int`` with ``0 ≤ n`` as a hypothesis,
    which is false at ``n = 0`` too, so Lean cannot prove what the tester
    refutes.
    """
    assert not _subtracts(n=0).holds
    assert print_lean(_subtracts.term) == "∀ n : Int, 0 ≤ n → n - 1 ≥ 0"
    assert not _divides(k=-1).holds
    assert print_lean(_divides.term) == "∀ k : Int, (k / 2) * 2 = k"


def _make_refined():
    """``n : Nat & (10 // n > 1) |- n > 0``: the division is in the refinement.

    The predicate is where the gap hides: Lean's ``Int.fdiv 10 0`` is ``0``,
    while the sampler cannot evaluate the refinement at ``n = 0`` at all. It is
    built inside a function because there is nothing here for the pytest
    plugin to run.
    """

    @theorem
    def refined(n: Nat & (10 // n > 1)) -> n > 0:
        """The refinement divides, and the walker has to see it."""

    return refined


_refined = _make_refined()


@theorem
def _sized_by_a_quotient(n: Nat, k: Nat, i: Fin[n // k]) -> i >= 0:
    """The division is in an index type's bound.

    Private, like the next one, so that the pytest plugin does not sample a
    domain whose size is a division by a drawn ``k``.
    """


@theorem
def _family_over_a_remainder(n: Nat, k: Nat, f: Fn[Fin[n % k], Nat]) -> n >= 0:
    """The division is inside a family's domain."""


def test_a_refinement_predicate_is_walked() -> None:
    """A domain is not a pymbolic node, so the walk has to open it by hand.

    Stopping at the domain object meant that every expression a sort carries
    (a refinement predicate, an index bound, a family's domain) was invisible
    to the check, and a statement whose only risky arithmetic lived there got
    no note at all.
    """
    assert semantics.divides_by_possible_zero(_refined.term)
    assert semantics.notes(_refined.term) == (semantics.DIVISION_BY_ZERO,)


def test_an_index_bound_and_a_family_domain_are_walked_too() -> None:
    assert semantics.notes(_sized_by_a_quotient.term) == (semantics.DIVISION_BY_ZERO,)
    assert semantics.notes(_family_over_a_remainder.term) == (semantics.DIVISION_BY_ZERO,)


def test_a_domain_without_arithmetic_is_still_not_flagged() -> None:
    """The walk got wider, not noisier: an ordinary domain says nothing."""
    assert semantics.notes(indexes.term) == ()
    assert semantics.notes(adds.term) == ()


def _make_divides_by_zero():
    """``n // 0 == 0`` over ``Nat``: a Lean theorem and a Python exception.

    Lean's division is total, so ``simp`` closes this; the property tester
    raises ``ZeroDivisionError`` at every draw. It is built inside a function
    because there is nothing here for the pytest plugin to run.
    """

    @theorem
    def div_zero(n: Nat) -> n // 0 == 0:
        """Division is total in Lean and undefined in Python."""

    return div_zero


_divides_by_zero = _make_divides_by_zero()


def _make_divides_by_a_variable():
    """``n // k * k <= n``: the divisor is a variable, so zero is one of its values."""

    @theorem
    def div_variable(n: Nat, k: Nat) -> (n // k) * k <= n:
        """Fine at every k but zero, and zero is drawn."""

    return div_variable


_divides_by_a_variable = _make_divides_by_a_variable()


@theorem
def divides_by_a_literal(n: Nat, i: Fin[n]) -> (i // 2) * 2 <= i:
    """A nonzero literal divisor is the one divisor that can be ruled out."""


def test_a_divisor_that_may_be_zero_is_a_gap_over_nat_and_int() -> None:
    """``n // 0`` is a theorem in Lean and an exception in Python.

    Lean's integer division is total where Python's raises, which a statement
    over ``Nat`` has as much as one over ``Int``.
    """
    assert semantics.divides_by_possible_zero(_divides_by_zero.term)
    assert semantics.notes(_divides_by_zero.term) == (semantics.DIVISION_BY_ZERO,)
    assert semantics.notes(_divides_by_a_variable.term) == (semantics.DIVISION_BY_ZERO,)
    assert "Int.fdiv x 0 is 0" in semantics.DIVISION_BY_ZERO


def test_a_nonzero_literal_divisor_carries_no_note() -> None:
    """A literal divisor that is not zero cannot divide by zero, over any sort."""
    assert not semantics.divides_by_possible_zero(divides_a_natural.term)
    assert semantics.notes(divides_a_natural.term) == ()
    assert not semantics.divides_by_possible_zero(divides_by_a_literal.term)
    assert semantics.notes(divides_by_a_literal.term) == ()
    assert semantics.notes(_divides.term) == ()


def test_an_int_divisor_that_may_be_zero_carries_one_note() -> None:
    """Rounding is no longer a gap, so totality is the only thing to note."""

    @theorem
    def both(k: Int, m: Int) -> (k // m) * m <= k:
        """m may be zero; the rounding of a negative operand is Python's in Lean too."""

    assert semantics.notes(both.term) == (semantics.DIVISION_BY_ZERO,)
    assert print_lean(both.term) == "∀ k : Int, ∀ m : Int, Int.fdiv k m * m ≤ k"
