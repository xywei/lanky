"""Every box of sumpy's compressed Taylor table, reconstructed: a proof written in Python.

``uv run lanky check examples/every_box.py``
    The ledger: one claim, that every derivative a box's table reconstructs
    is the derivative it stands for. With Lean and Mathlib it reads
    ``proved``, by the proof written in ``every_box``'s body, and the row
    says so in a line of its own: ``by its proof, every_box.py:...:
    induction on a, 3 cases, 3 steps``. Without them it reads ``tested``, and
    a ``NOT CHECKED`` line says why the proof was not checked.

The mathematics. sumpy's ``LinearPDEBasedExpansionTermsWrangler`` stores, for
each box ``i`` of ``n``, the derivatives ``D[i, a, b]`` of the 2-D Laplace
kernel with ``a < 2``, and reconstructs the rest by the PDE: a derivative with
``a >= 2`` is minus the one with two fewer ``x``'s and two more ``y``'s. In
sumpy's storage order a box's table ``c`` holds the centre, ``a + b == 0``, at
``c[i, 0]``, and the other stored derivative ``(a, b)`` at ``c[i, 2 * (a + b) -
1 + a]``; so the claim's base case, ``a < 2``, rests on two pairs of
hypotheses, the centre's copy and the centre at order zero, and the copies
and what is stored above it. lanky's search does not split a case on the
conditions of the facts it combines (lanky #140), so it does not find this
proof alone, and the claim read ``assumed``; the body says how.

Read aloud: "The claim at (i, a, b): at order zero, by the centre's copy and
the centre. If a < 2, by the copies and what is stored. Otherwise by the
recurrence, the claim at (i, a - 2, b + 2) and the PDE. That proves the
claim."

- ``def claim(i, a, b)``, returned, is the claim at one box and one order.
  ``claim(i, a - 2, b + 2)`` inside it is the claim at an order with two
  fewer ``x``'s, which is the induction: Lean checks that ``a`` gets smaller
  and stays a natural number.
- ``if a + b == 0`` is a case split. Among naturals it fixes ``a`` and ``b``
  at ``0``, and lanky substitutes both, so the case's claim is ``R[i, 0, 0]
  == D[i, 0, 0]``.
- ``return centre_copy, centre`` cites two hypotheses by name alone. Each is
  applied at the point found by matching it against the case's claim:
  ``centre_copy`` at ``R[i, 0, 0]`` and ``centre`` at ``D[i, 0, 0]``, both at
  ``i``. So are ``copies`` and ``stored`` in the next case, at ``(i, a, b)``.
- The last line keeps its points, because they carry the induction. Lean
  checks each fact's conditions there (``a - 2 >= 0`` follows from the case
  ``a >= 2``, and ``a - 2 + b + 2 <= p`` from the claim's ``a + b <= p``), and
  that the three facts give the claim, with the multipliers Python finds.

``python examples/every_box.py`` runs the claim as a property test on a table
that obeys it, and never runs the proof.
"""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Fn, Int, Nat, Real


@theorem
def every_box(
    n: Nat,
    p: Nat,
    c: Fn[Nat, Int, Real],
    D: Fn[Nat, Nat, Nat, Real],
    R: Fn[Nat, Nat, Nat, Real],
    pde: all(D[i, a + 2, b] + D[i, a, b + 2] == 0 for i in Fin[n] for a in Nat for b in Nat),
    centre: all(c[i, 0] == D[i, 0, 0] for i in Fin[n]),
    stored: all(
        c[i, 2 * (a + b) - 1 + a] == D[i, a, b]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a < 2
        if a + b >= 1
        if a + b <= p
    ),
    centre_copy: all(R[i, 0, 0] == c[i, 0] for i in Fin[n]),
    copies: all(
        R[i, a, b] == c[i, 2 * (a + b) - 1 + a]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a < 2
        if a + b >= 1
        if a + b <= p
    ),
    recurrence: all(
        R[i, a + 2, b] == -R[i, a, b + 2]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a + b + 2 <= p
    ),
) -> all(R[i, a, b] == D[i, a, b] for i in Fin[n] for a in Nat for b in Nat if a + b <= p):
    """Every derivative a box's table reconstructs is the derivative it stands for.

    ``D`` is any table of derivatives that satisfies Laplace's equation at
    every order, as the derivatives of a harmonic kernel do; ``c`` is a box's
    stored table in sumpy's order, which agrees with ``D`` where it stores;
    and ``R`` copies ``c`` where it is stored and follows the recurrence
    everywhere else up to the order ``p``.
    """

    def claim(i, a, b):
        if a + b == 0:
            return centre_copy, centre
        if a < 2:
            return copies, stored
        return recurrence(i, a - 2, b), claim(i, a - 2, b + 2), pde(i, a - 2, b)

    return claim


if __name__ == "__main__":
    report = every_box.report(n=50)
    print(f"every_box: {report.valid} valid draws, ok: {report.ok}")
