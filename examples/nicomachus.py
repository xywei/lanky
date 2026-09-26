"""A result taken on a citation, and a theorem that rests on it.

Check it and test it as ``gauss.py`` is checked and tested.

``uv run lanky check examples/nicomachus.py``
    The ledger. The axiom is ``assumed (axiom)``, with its citation in the
    provenance, and the theorem that uses it reads ``tested under nicomachus``,
    with ``assumed`` in the ``EFFECTIVE`` column: evidence for a claim that
    rests on an assumption is worth no more than the assumption.

``uv run pytest examples/nicomachus.py``
    All three statements are collected and sampled, the axiom included.

``nicomachus`` is Nicomachus's theorem: the sum of the first cubes is the square
of the sum of the first numbers. lanky has no proof of it. A sum needs Mathlib's
``Finset`` in Lean, and the property tester's word is evidence rather than
proof, so the statement enters the ledger on the word of a reference, through
``@axiom(cite=...)``. It is not handed to a prover. It is still sampled for a
counterexample, because a citation copied down wrong says something the
reference does not.

``cubes`` is the closed form of the sum of cubes. It follows from
``nicomachus`` and ``gauss``, and says so with ``uses=``, which becomes the
``rests_on`` of its fact.
"""

from __future__ import annotations

from lanky import axiom, theorem
from lanky.prelude import Fin, Nat


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@theorem(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """Four times the sum of the cubes of ``0 .. n`` is ``(n * (n + 1)) ** 2``.

    Square ``gauss`` and substitute it into ``nicomachus``.
    """
