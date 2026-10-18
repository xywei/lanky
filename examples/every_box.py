"""Every box of sumpy's compressed Taylor table, reconstructed: a proof written in Python.

``python examples/every_box.py``
    Builds a few boxes' tables of a harmonic function's derivatives, stores
    them in sumpy's order, reconstructs every derivative through order 8 by
    the recurrence, and prints how far the reconstruction is from the
    derivatives: nowhere, in exact arithmetic. Running the file runs no
    proof.

``uv run lanky check examples/every_box.py``
    The ledger: one claim, that every derivative a box's table reconstructs
    is the derivative it stands for, for every order. With Lean and Mathlib
    it reads ``proved``, by the proof written in ``every_box``'s body, and the
    row says so in a line of its own::

        by its proof, every_box.py:110-116: induction on a, 3 cases, 3 steps

    Without them it reads ``assumed``, since the property tester draws no
    family over ``Nat``, and a ``NOT CHECKED`` line under the table says why
    the proof was not checked.

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

Read aloud: "For each point (i, a, b) of the conclusion: at order zero, by
the centre's copy and the centre. If a < 2, by the copies and what is
stored. Otherwise by the recurrence, the conclusion at (i, a - 2, b + 2) and
the PDE."

- ``for i, a, b in every_box.conclusion.domain:`` is a loop over the points
  of the conclusion's ``for``, the same loop the kernel runs over its table,
  and ``yield by(...)`` says why the conclusion holds at the point the loop
  is at. The proof fills in the table of true and false in order, and each
  entry may use one the loop filled in before:
  ``every_box.conclusion[i, a - 2, b + 2]`` is the conclusion at an order
  with two fewer ``x``'s, which is the induction. lanky checks that the loop
  has filled it in (``a``, smaller, comes first in the loop's order), and
  Lean that ``a`` gets smaller and stays a natural number.
- ``if a + b == 0`` is a case split. Among naturals it fixes ``a`` and ``b``
  at ``0``, and lanky substitutes both, so the case's conclusion is
  ``R[i, 0, 0] == D[i, 0, 0]``.
- ``by(centre_copy, centre)`` cites two conditions by name alone. Each is
  applied at the point found by matching it against the case's conclusion:
  ``centre_copy`` at ``R[i, 0, 0]`` and ``centre`` at ``D[i, 0, 0]``, both at
  ``i``. So are ``copies`` and ``stored`` in the next case, at ``(i, a, b)``,
  and ``recurrence`` and ``pde`` in the last, at ``(i, a - 2, b)``, the one
  point where each is about the conclusion's cells and the cells of the
  conclusion at ``(i, a - 2, b + 2)``. Lean checks each fact's conditions
  there (``a - 2 >= 0`` follows from the case ``a >= 2``, and ``a - 2 + b +
  2 <= p`` from the conclusion's ``a + b <= p``), and that the three facts
  give the conclusion, with the multipliers Python finds.
"""

from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fin, Fn, Int, Nat, Real


@claim
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
    for i, a, b in every_box.conclusion.domain:
        if a + b == 0:
            yield by(centre_copy, centre)
        elif a < 2:
            yield by(copies, stored)
        else:
            yield by(recurrence, every_box.conclusion[i, a - 2, b + 2], pde)


def tables(boxes: int, order: int) -> tuple[dict, dict, dict]:
    """``D``, ``c`` and ``R`` for ``boxes`` boxes through ``order``, keyed as the claim's tables.

    Box ``i``'s ``D`` holds the derivatives at the origin of ``Re(exp(z_i * (x
    + 1j * y)))``, which is harmonic, ``Re(z_i ** (a + b) * 1j ** b)``, with
    ``z_i`` a Gaussian integer so that every one is an exact integer. ``c``
    stores them in sumpy's order, and ``R`` copies ``c`` where it stores and
    follows the recurrence elsewhere, an order at a time, ``a`` rising.
    """
    D: dict = {}
    c: dict = {}
    R: dict = {}
    for i in range(boxes):
        z = complex(i + 1, 2 - i)
        for a in range(order + 1):
            for b in range(order + 1 - a):
                D[i, a, b] = round((z ** (a + b) * 1j**b).real)
        c[i, 0] = D[i, 0, 0]
        for a in range(2):
            for b in range(order + 1 - a):
                if a + b >= 1:
                    c[i, 2 * (a + b) - 1 + a] = D[i, a, b]
        for total in range(order + 1):
            for a in range(total + 1):
                b = total - a
                if total == 0:
                    R[i, a, b] = c[i, 0]
                elif a < 2:
                    R[i, a, b] = c[i, 2 * total - 1 + a]
                else:
                    R[i, a, b] = -R[i, a - 2, b + 2]
    return D, c, R


if __name__ == "__main__":
    BOXES, ORDER = 3, 8
    D, c, R = tables(BOXES, ORDER)
    worst = max(abs(R[key] - D[key]) for key in D)
    print(
        f"{BOXES} boxes through order {ORDER}: {len(D)} derivatives reconstructed from "
        f"{len(c)} stored, largest difference {worst}"
    )
