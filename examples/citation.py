"""A result taken on a citation, and a theorem that rests on it.

Check it and test it as ``gauss.py`` is checked and tested.

``uv run lanky check examples/citation.py``
    The ledger. The axiom is ``assumed (axiom)``, with its citation in the
    provenance, and the theorem that uses it reads ``tested under nicomachus``,
    with ``assumed`` in the ``EFFECTIVE`` column: evidence for a claim that
    rests on an assumption is worth no more than the assumption.

``uv run pytest examples/citation.py``
    All three statements are collected and sampled, the axiom included.

``nicomachus`` is Nicomachus's theorem: the sum of the first cubes is the square
of the sum of the first numbers. Here it enters the ledger on the word of a
reference, through ``@claim(cite=...)``, as a result does before its proof is
written, or where the proof needs more than the machine has: every statement
here has a sum in it, which only Lean with Mathlib states.
``examples/nicomachus.py`` proves it, by a chain through ``one_more_term``. It
is not handed to a prover here. It is still sampled for a counterexample,
because a citation copied down wrong says something the reference does not.

``cubes`` is the closed form of the sum of cubes. It follows from
``nicomachus`` and ``gauss``, and says so with ``uses=``, which becomes the
``rests_on`` of its fact.
"""

from __future__ import annotations

from lanky import claim
from lanky.prelude import Fin, Nat


@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@claim(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@claim(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """Four times the sum of the cubes of ``0 .. n`` is ``(n * (n + 1)) ** 2``.

    Square ``gauss`` and substitute it into ``nicomachus``.
    """
