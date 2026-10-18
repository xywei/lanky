"""Sum factorization on hexahedra: a tensor-product operator as three one-axis passes.

Run it as ``gauss.py`` is run; numpy is all it needs.

``python examples/sum_factorization.py``
    Builds the weak derivative along the first axis of a hexahedral element
    on Gauss-Lobatto-Legendre points, at orders 1 to 7, and applies it two
    ways to a random field: as the dense ``n**3 x n**3`` matrix
    ``numpy.kron(H, numpy.kron(G, F))`` on the field flattened with its first
    axis fastest, and as three one-axis passes. It prints how far apart the
    two are and how many multiplications each takes, and then evaluates the
    claims below at small exact matrices.

``uv run lanky check examples/sum_factorization.py``
    The ledger. With Mathlib (see :mod:`lanky.mathlib`), the exchange of two
    sums, the factorization and the mixed product are ``proved`` by Lean for
    every size ``n``; without it they are ``tested``. The flattening reads
    ``tested`` either way: Lean is not asked about it (see below).

The mathematics. A tensor-product element of order ``p`` has ``n = p + 1``
nodes along each of its three axes, and an operator on it that is built from
one-dimensional ones, ``F`` along the first axis, ``G`` along the second and
``H`` along the third, has the entries ``H[c, r] * G[b, q] * F[a, p]`` at the
row ``(a, b, c)`` and the column ``(p, q, r)``: it is the Kronecker product
``H (x) G (x) F``. Applied to a field ``u[p, q, r]`` it sums over all three
column indices, ``n**3`` terms for each of the ``n**3`` rows. Sum
factorization does the same in three passes of ``n`` terms each: ``F`` along
the first axis, then ``G`` along the second, then ``H`` along the third. That
is grudge's ``_apply_operator_to_group`` (inducer/grudge PR #418): one
``einsum`` per reference axis, ``"ij,ejbc->eibc"`` and its two siblings,
where the escape hatch, ``"ij,ej->ei"``, takes the dense matrix modepy builds.

Why they agree is two steps. Distribute each factor into the sums inside it,
and exchange the sums until they are in the same order on both sides; the
summands are then one product. Lean takes both steps with lemmas Mathlib has,
and lanky finds which sums to exchange (see :mod:`lanky.sums`): the claim is
proved for every ``n`` and every three matrices, and not only at the sizes
grudge's tests run. The same two steps prove the Kronecker product's mixed
product property, ``(A (x) B)(C (x) D) = AC (x) BD``, entry by entry, which is
what lets an operator such as ``M^-1 S^T`` be formed one axis at a time.

What is left as ``tested`` is the order of the factors in the dense matrix:
which axis of the field is the fastest in its flattening, and so which factor
comes last in numpy's ``kron``. modepy flattens with the first axis fastest,
``a + n*b + n**2*c``, and so the dense matrix is ``kron(H, kron(G, F))``, with
``F`` last. Stating that for every ``n`` takes ``i // n**2`` and ``i % n`` of
a variable ``n``, which is not linear arithmetic, and lanky does not hand Lean
a family applied at an index it cannot show is in the family's domain by
linear arithmetic: the claim is left to the property tester, which checks it
at drawn sizes and entries (#126).

The rows and columns are parameters of the theorems rather than quantifiers
in their goals. That is the same statement, since a theorem's parameters are
universal, and the property tester then draws a row instead of walking all of
them, each a sum over all the columns (#125).
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from lanky import claim
from lanky.prelude import Fin, Fn, Nat, Real


@claim
def exchange(
    n: Nat, m: Nat, f: Fn[Fin[n], Fin[m], Real]
) -> sum(sum(f[i, j] for j in Fin[m]) for i in Fin[n]) == sum(
    sum(f[i, j] for i in Fin[n]) for j in Fin[m]
):
    """Two finite sums exchange: the step every identity below takes."""


def kron(H, G, F):
    """``H (x) G (x) F``, the operator that applies ``F``, ``G`` and ``H`` along the three axes.

    Its entry at the row ``(a, b, c)`` and the column ``(p, q, r)``.
    """

    def entry(a, b, c, p, q, r):
        return H[c, r] * G[b, q] * F[a, p]

    return entry


@claim
def sum_factorization(
    n: Nat,
    F: Fn[Fin[n], Fin[n], Real],
    G: Fn[Fin[n], Fin[n], Real],
    H: Fn[Fin[n], Fin[n], Real],
    u: Fn[Fin[n], Fin[n], Fin[n], Real],
    a: Fin[n],
    b: Fin[n],
    c: Fin[n],
) -> sum(
    kron(H, G, F)(a, b, c, p, q, r) * u[p, q, r] for p in Fin[n] for q in Fin[n] for r in Fin[n]
) == sum(
    H[c, r] * sum(G[b, q] * sum(F[a, p] * u[p, q, r] for p in Fin[n]) for q in Fin[n])
    for r in Fin[n]
):
    """The tensor-product operator applied to ``u`` is three one-axis passes, at every size.

    At every row ``(a, b, c)``: the left side is ``kron(H, G, F)`` applied to
    ``u``, and the right side applies ``F`` along the first axis, ``G``
    along the second and ``H`` along the third, innermost first.
    """


@claim
def mixed_product(
    n: Nat,
    A: Fn[Fin[n], Fin[n], Real],
    B: Fn[Fin[n], Fin[n], Real],
    C: Fn[Fin[n], Fin[n], Real],
    D: Fn[Fin[n], Fin[n], Real],
    i: Fin[n],
    k: Fin[n],
    p: Fin[n],
    q: Fin[n],
) -> sum(A[i, j] * B[k, s] * (C[j, p] * D[s, q]) for j in Fin[n] for s in Fin[n]) == sum(
    A[i, j] * C[j, p] for j in Fin[n]
) * sum(B[k, s] * D[s, q] for s in Fin[n]):
    """``(A (x) B)(C (x) D)`` is ``AC (x) BD``, at every row ``(i, k)`` and column ``(p, q)``."""


def dense(H, G, F, n):
    """modepy's dense matrix, numpy's ``kron(H, kron(G, F))``, as its entry at a row and a column.

    numpy's ``kron(X, Y)`` for an ``m x m`` matrix ``Y`` has ``X[i // m, j //
    m] * Y[i % m, j % m]`` at ``(i, j)``.
    """

    def entry(i, j):
        return H[i // n**2, j // n**2] * G[i // n % n, j // n % n] * F[i % n, j % n]

    return entry


@claim
def flattening(
    n: Nat,
    F: Fn[Fin[n], Fin[n], Real],
    G: Fn[Fin[n], Fin[n], Real],
    H: Fn[Fin[n], Fin[n], Real],
    a: Fin[n],
    b: Fin[n],
    c: Fin[n],
    p: Fin[n],
    q: Fin[n],
    r: Fin[n],
) -> dense(H, G, F, n)(a + n * b + n**2 * c, p + n * q + n**2 * r) == kron(H, G, F)(
    a, b, c, p, q, r
):
    """With the first axis fastest, the dense matrix is ``kron(H, kron(G, F))``: ``F`` is last.

    At every row ``(a, b, c)`` and column ``(p, q, r)``, flattened as modepy
    flattens them, ``a + n * b + n**2 * c``.
    """


# {{{ running it

#: How far apart the dense operator and the passes may be, in floating point.
TOLERANCE = 1e-13


def gll(n: int) -> tuple[np.ndarray, np.ndarray]:
    """The ``n`` Gauss-Lobatto-Legendre points on ``[-1, 1]`` and their weights."""
    legendre = np.polynomial.legendre.Legendre.basis(n - 1)
    inner = np.sort(legendre.deriv().roots().real) if n > 2 else np.array([])
    points = np.concatenate([[-1.0], inner, [1.0]])
    weights = 2 / (n * (n - 1) * legendre(points) ** 2)
    return points, weights


def differentiation(points: np.ndarray) -> np.ndarray:
    """The Lagrange differentiation matrix at ``points``, from the barycentric weights."""
    gaps = points[:, None] - points[None, :]
    np.fill_diagonal(gaps, 1.0)
    weights = 1 / gaps.prod(axis=1)
    matrix = (weights[None, :] / weights[:, None]) / gaps
    np.fill_diagonal(matrix, 0.0)
    np.fill_diagonal(matrix, -matrix.sum(axis=1))
    return matrix


def passes(F: np.ndarray, G: np.ndarray, H: np.ndarray, u: np.ndarray) -> np.ndarray:
    """``F`` along the first axis, ``G`` along the second, ``H`` along the third."""
    u = np.einsum("ap,pqr->aqr", F, u)
    u = np.einsum("bq,aqr->abr", G, u)
    return np.einsum("cr,abr->abc", H, u)


def main() -> int:
    """Apply the weak derivative both ways at orders 1 to 7, then the claims at small sizes."""
    rng = np.random.default_rng(0)
    print(
        "The weak derivative along the first axis on GLL hexahedra: H (x) G (x) F with\n"
        "F = S^T along the first axis and G = H = M, the mass matrix, along the others."
    )
    print()
    print("order  n  dense - passes   multiplications (dense / passes)")
    worst = 0.0
    for n in range(2, 9):
        points, weights = gll(n)
        mass = np.diag(weights)
        stiffness_t = differentiation(points).T @ mass
        F, G, H = stiffness_t, mass, mass
        u = rng.standard_normal((n, n, n))
        flat = u.reshape(-1, order="F")
        applied = (np.kron(H, np.kron(G, F)) @ flat).reshape((n, n, n), order="F")
        gap = float(np.abs(applied - passes(F, G, H, u)).max())
        worst = max(worst, gap)
        shown = f"within {TOLERANCE:.0e}" if gap <= TOLERANCE else f"{gap:.1e}"
        print(f"{n - 1:5d}  {n}  {shown:>15}  {n**6:7d} / {3 * n**4}")
    print()
    print(
        "numpy's kron(H, kron(G, F)) on the field flattened with its first axis fastest\n"
        f"is the three passes at every order here, to within {TOLERANCE:.0e}."
        if worst <= TOLERANCE
        else "The dense operator and the passes DISAGREE: see the table."
    )
    print()
    # the claims at exact matrices, where == means equal
    n = 3
    exact = rng.integers(-4, 5, size=(4, n, n)).tolist()
    F, G, H, other = ([[Fraction(x) for x in row] for row in m] for m in exact)
    u = rng.integers(-4, 5, size=(n, n, n)).tolist()
    pairs = [(x, y) for x in range(n) for y in range(n)]
    rows = [(a, b, c) for a in range(n) for b in range(n) for c in range(n)]
    verdicts = {
        "sum_factorization": all(
            sum_factorization(n=n, F=F, G=G, H=H, u=u, a=a, b=b, c=c) for a, b, c in rows
        ),
        "mixed_product": all(
            mixed_product(n=n, A=F, B=G, C=H, D=other, i=i, k=k, p=p, q=q)
            for i, k in pairs
            for p, q in pairs
        ),
        "flattening": all(
            flattening(n=n, F=F, G=G, H=H, a=a, b=b, c=c, p=p, q=q, r=r)
            for a, b, c in rows
            for p, q, r in rows
        ),
    }
    for name, holds in verdicts.items():
        print(f"{name} at n = {n}, at every row and column, exact integer matrices: {holds}")
    print()
    print(
        "`lanky check examples/sum_factorization.py` puts the claims in the ledger: proved\n"
        "for every size by Lean where Mathlib is installed, tested where it is not."
    )
    return 0 if worst <= TOLERANCE and all(verdicts.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())

# }}}
