"""The two places lanky's Python reading and Lean's reading disagree."""

from __future__ import annotations

from lanky import semantics, theorem
from lanky.prelude import Fin, Fn, Int, Nat


def _make_subtracts():
    """Build the statement ``n - 1 >= 0`` over ``Nat``.

    It lives in a function rather than at module level because it is *false*
    under lanky's Python reading, which is the whole point of it, and a
    module-level theorem is collected and run by lanky's own pytest plugin.
    """

    @theorem
    def subtracts(n: Nat) -> n - 1 >= 0:
        """True in Lean, where Nat subtraction truncates; false in Python at 0."""

    return subtracts


_subtracts = _make_subtracts()


@theorem
def adds(n: Nat) -> n + 1 > n:
    """Index arithmetic: both readings agree."""


def _make_divides():
    """Build ``(k // 2) * 2 <= k`` over ``Int``; false in Python at ``k = -1``."""

    @theorem
    def divides(k: Int) -> (k // 2) * 2 <= k:
        """Floor division over Int rounds differently in the two readings."""

    return divides


_divides = _make_divides()


@theorem
def divides_a_natural(n: Nat) -> (n // 2) * 2 <= n:
    """Over Nat the two readings agree, so this is not flagged."""


@theorem
def indexes(n: Nat, i: Fin[n]) -> i + 1 <= n:
    """A bounded index is a guarded Nat in Lean, which is what the note reads."""


def test_only_the_statements_that_can_differ_are_flagged() -> None:
    assert semantics.notes(_subtracts.term) == (semantics.NAT_SUBTRACTION,)
    assert semantics.notes(adds.term) == ()
    assert semantics.notes(_divides.term) == (semantics.INT_DIVISION,)
    assert semantics.notes(divides_a_natural.term) == ()
    assert semantics.notes(None) == ()


def test_a_bounded_index_counts_as_a_natural() -> None:
    """``Fin[n]`` prints as a guarded ``Nat``, so its arithmetic is Nat's."""
    assert semantics.sorts_of(indexes.term) == {"Nat"}
    assert not semantics.uses_subtraction(indexes.term)
    assert semantics.notes((indexes.term.body - 1) >= 0) == ()


def test_subtraction_is_recognized_under_a_quantifier() -> None:
    """The gap is about what the statement says anywhere in it, not at the top."""
    assert semantics.uses_subtraction(_subtracts.term)
    assert semantics.notes(_subtracts.term)


def test_the_two_readings_really_do_differ() -> None:
    """The reason the note exists, spelled out as a test.

    Under lanky's Python reading the statement is false at ``n = 0``; the Lean
    source the printer emits is the truncated one, which is why Lean can prove
    the same statement. The note is the only thing that connects the two.
    """
    from lanky.lean import print_lean

    assert not _subtracts(n=0).holds
    assert "n - 1" in print_lean(_subtracts.term)


def _make_refined():
    """``n : Nat & (n - 1 < n) |- n > 0``: the subtraction is in the refinement.

    The predicate is where the gap hides: Lean truncates ``n - 1`` at zero, so
    the refinement it elaborates is not the one the sampler filters with. The
    theorem is built inside a function because its refinement is false at
    ``n = 0`` under the Python reading, which is the point of it.
    """

    @theorem
    def refined(n: Nat & (n - 1 < n)) -> n > 0:
        """The refinement subtracts, and the walker has to see it."""

    return refined


_refined = _make_refined()


@theorem
def sized_by_a_difference(n: Nat, i: Fin[n - 1]) -> i >= 0:
    """The subtraction is in an index type's bound."""


@theorem
def family_over_a_difference(n: Nat, f: Fn[Fin[n - 1], Nat]) -> all(
    f(i) >= 0 for i in Fin[n - 1]
):
    """The subtraction is inside a family's domain."""


def test_a_refinement_predicate_is_walked() -> None:
    """A domain is not a pymbolic node, so the walk has to open it by hand.

    Stopping at the domain object meant that every expression a sort carries
    (a refinement predicate, an index bound, a family's domain) was invisible
    to the check, and a statement whose only subtraction lived there got no
    note at all.
    """
    assert semantics.uses_subtraction(_refined.term)
    assert semantics.notes(_refined.term) == (semantics.NAT_SUBTRACTION,)


def test_an_index_bound_and_a_family_domain_are_walked_too() -> None:
    assert semantics.notes(sized_by_a_difference.term) == (semantics.NAT_SUBTRACTION,)
    assert semantics.notes(family_over_a_difference.term) == (
        semantics.NAT_SUBTRACTION,
    )


def test_a_domain_without_arithmetic_is_still_not_flagged() -> None:
    """The walk got wider, not noisier: an ordinary domain says nothing."""
    assert semantics.notes(indexes.term) == ()
    assert semantics.notes(adds.term) == ()


def _make_divides_by_zero():
    """``n // 0 == 0`` over ``Nat``: a Lean theorem and a Python exception.

    Lean's ``Nat`` division is total, so ``omega`` and ``simp`` close this; the
    property tester raises ``ZeroDivisionError`` at every draw. It is built
    inside a function because there is nothing here for the pytest plugin to
    run.
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


def test_a_divisor_that_may_be_zero_is_a_gap_over_nat_too() -> None:
    """The gap the Int note does not cover: ``n // 0`` is a theorem in Lean.

    The division notes are about different things. One is how a negative
    operand rounds, which only ``Int`` has; this one is that Lean's division is
    total where Python's raises, which ``Nat`` has as much as ``Int``, so a
    statement over ``Nat`` used to be proved with no note and no cross-check
    while calling it raised.
    """
    assert semantics.divides_by_possible_zero(_divides_by_zero.term)
    assert semantics.notes(_divides_by_zero.term) == (semantics.DIVISION_BY_ZERO,)
    assert semantics.notes(_divides_by_a_variable.term) == (semantics.DIVISION_BY_ZERO,)


def test_a_nonzero_literal_divisor_carries_no_note() -> None:
    """Over ``Nat``, ``n // 2`` means the same thing in both readings."""
    assert not semantics.divides_by_possible_zero(divides_a_natural.term)
    assert semantics.notes(divides_a_natural.term) == ()
    assert not semantics.divides_by_possible_zero(divides_by_a_literal.term)
    assert semantics.notes(divides_by_a_literal.term) == ()
    # and the Int note is still only about rounding, which a literal does not fix
    assert semantics.notes(_divides.term) == (semantics.INT_DIVISION,)


def test_an_int_divisor_that_may_be_zero_carries_both_notes() -> None:
    """Rounding and totality are two gaps, and a statement can have both."""

    @theorem
    def both(k: Int, m: Int) -> (k // m) * m <= k:
        """A negative operand rounds differently, and m may be zero."""

    assert semantics.notes(both.term) == (
        semantics.INT_DIVISION,
        semantics.DIVISION_BY_ZERO,
    )
