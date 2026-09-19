"""The two places lanky's Python reading and Lean's reading disagree."""

from __future__ import annotations

from lanky import semantics, theorem
from lanky.prelude import Fin, Int, Nat


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
