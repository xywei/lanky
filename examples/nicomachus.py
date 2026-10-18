"""Nicomachus's theorem, proved by a chain through a fact lanky knows.

Check it and test it as ``gauss.py`` is checked and tested.

``uv run lanky check examples/nicomachus.py``
    The ledger. Where Mathlib is installed (see :mod:`lanky.mathlib`), Lean
    checks the proof below, and all three theorems read ``proved``:
    ``nicomachus`` by its proof, which cites ``gauss`` and ``one_more_term``
    from :mod:`lanky.known`, and ``gauss`` and ``cubes`` by lanky's own
    induction. Without Mathlib they read ``tested``, since every statement
    has a sum in it, which only Lean with Mathlib states, and a ``NOT
    CHECKED`` line says that the proof's steps were tested at drawn points
    instead.

``uv run pytest examples/nicomachus.py``
    All three statements are collected and sampled.

``nicomachus`` is Nicomachus's theorem: the sum of the first cubes is the
square of the sum of the first numbers (Nicomachus of Gerasa, Introduction to
Arithmetic). The proof is the induction a textbook writes, read aloud: "The
claim at n: if n is 0, it is routine. Otherwise, the cubes to n + 1 sum to the
cubes to n plus n cubed, by one more term; that is the square of the sum to n,
plus n cubed, by the claim at n - 1; that is the square of the sum to n plus
n, by Gauss at n - 1; and that is the square of the sum to n + 1, by one more
term."

``one_more_term`` is cited by its name alone, twice. It says that a sum to
``n + 1`` is the sum to ``n`` plus its last term, for any family ``f``, and
lanky finds the family and the point from the link it supports: ``f = i ↦
i**3`` at ``n`` for the first link, ``f = i ↦ i`` at ``n`` for the last. It is
stated over the reals, and these sums are of integers; Lean reads the integer
sums through the cast into the reals, where the fact holds, and the cast is
injective. ``gauss(n - 1)`` and ``claim(n - 1)`` keep their points, the second
because it is the induction.

``cubes`` is the closed form of the sum of cubes. It follows from
``nicomachus`` and ``gauss``, and says so with ``uses=``, which becomes the
``rests_on`` of its fact. ``examples/citation.py`` holds the same three
statements with ``nicomachus`` taken on its citation instead, which is how a
result enters the ledger before its proof is written.
"""

from __future__ import annotations

from lanky import theorem
from lanky.known import one_more_term
from lanky.prelude import Fin, Nat


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@theorem
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""

    def claim(n):
        if n == 0:
            return
        return (
            sum(i**3 for i in Fin[n + 1])
            .equals(sum(i**3 for i in Fin[n]) + n**3, by=one_more_term)
            .equals(sum(i for i in Fin[n]) ** 2 + n**3, by=claim(n - 1))
            .equals((sum(i for i in Fin[n]) + n) ** 2, by=gauss(n - 1))
            .equals(sum(i for i in Fin[n + 1]) ** 2, by=one_more_term)
        )

    return claim


@theorem(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """Four times the sum of the cubes of ``0 .. n`` is ``(n * (n + 1)) ** 2``.

    Square ``gauss`` and substitute it into ``nicomachus``.
    """
