"""What lanky knows: library facts with plain names, each proved once with Mathlib.

``from lanky.known import log_of_a_power`` reads "from what lanky knows".
Each entry is an ordinary :func:`~lanky.theory.theorem`: a statement in
Python, under a plain name, with a docstring that says the fact in words and
cites the Mathlib lemma it is (``Mathlib: Real.log_pow``). The Mathlib names
are book citations, and they never appear in a user's file: a proof cites the
fact by its Python name, as it cites a hypothesis or a theorem of its own::

    from lanky.known import log_of_a_power, modulus_squared


    @theorem
    def log_of_the_modulus(alpha: Complex, nonzero: alpha != 0) -> (
        log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
    ):
        \"\"\"log|alpha| with no square root: half the log of alpha times its conjugate.\"\"\"
        assert log(abs(alpha)) == log(abs(alpha) ** 2) / 2, by(log_of_a_power)
        return by(modulus_squared)

Each fact's Lean proof is written once, against the statement as lanky
prints it (the integer reading of :mod:`lanky.lean`: a natural is an ``Int``
with ``0 ≤ n`` among its hypotheses), and kept in a table the Lean oracle
reads, :mod:`lanky.oracles.known`. The table is screened for raw text before
Lean sees it (:func:`lanky.audit.screen`), and a CI job with Mathlib
proves every entry under the current printer, so a change to the printer
fails that job rather than silently turning the library into ``tested``. So
``lanky check`` on this file reads ``proved`` for every row where Mathlib is
installed, and ``tested`` without it, as any file does.

Importing this module builds the theorems below and nothing more: it pins no
tactic and reads no proof. The Lean oracle reads the table when it is asked
about one of these facts, under ``lanky check``, and only then does Lean
start. ``python file.py`` behaves exactly as it did before the import.

The sums are stated over the reals, and apply to sums of integers as they
are. ``one_more_term`` cited at ``sum(i**3 for i in Fin[n + 1])``, a sum of
naturals, has its family at ``i ↦ i**3``, whose values are integers; the
fact at that point is stated over the integers, as the step reads it, and
Lean shows it from the fact over the reals through the cast, which is
injective. So ``examples/nicomachus.py``'s proof cites it as it stands::

    assert (
        sum(i**3 for i in Fin[n + 1])
        == sum(i**3 for i in Fin[n]) + n**3
        == sum(i for i in Fin[n]) ** 2 + n**3
        == (sum(i for i in Fin[n]) + n) ** 2
        == sum(i for i in Fin[n + 1]) ** 2
    ), by(one_more_term, nicomachus.conclusion[n - 1], gauss(n - 1))

A fact here has no hypothesis it does not need. ``log_of_a_power`` holds for
every real ``x``, ``0`` and the negative numbers included, because Lean's
logarithm is total; Python's ``math.log`` has no value there, and where it
has one the two agree (see :mod:`lanky.semantics`). A theorem that cites it
keeps its own ``nonzero`` to say where ``log`` means what its reader thinks.

When Lean cannot prove a claim alone, ``lanky check`` names the facts of
this module whose shape occurs in it, which side of each fits and at what
values (:mod:`lanky.suggest`)::

    modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha
"""

from __future__ import annotations

from lanky.prelude import Complex, Fin, Fn, Nat, Real
from lanky.terms import conj, exp, log, real, sqrt
from lanky.theory import theorem

__all__ = [
    "abs_of_negative",
    "abs_of_positive",
    "complex_triangle_inequality",
    "distribute",
    "exp_of_a_sum",
    "fiber_exchange",
    "geometric_sum",
    "log_of_a_power",
    "log_of_a_product",
    "modulus_of_a_product",
    "modulus_squared",
    "one_more_term",
    "shifted_sum",
    "square_root_squared",
    "sum_exchange",
    "sum_of_a_constant",
    "sum_of_sums",
    "triangle_exchange",
    "triangle_inequality",
    "triangle_inequality_for_sums",
]

# {{{ logarithms, exponentials and roots


@theorem
def log_of_a_power(x: Real, n: Nat) -> log(x**n) == n * log(x):
    """The log of a power is the exponent times the log (Mathlib: Real.log_pow)."""


@theorem
def log_of_a_product(x: Real, y: Real, x_positive: x > 0, y_positive: y > 0) -> (
    log(x * y) == log(x) + log(y)
):
    """The log of a product of positive numbers is the sum of their logs
    (Mathlib: Real.log_mul)."""


@theorem
def exp_of_a_sum(x: Real, y: Real) -> exp(x + y) == exp(x) * exp(y):
    """The exponential of a sum is the product of the exponentials (Mathlib: Real.exp_add)."""


@theorem
def square_root_squared(x: Real, nonnegative: x >= 0) -> sqrt(x) ** 2 == x:
    """The square root of a number that is not negative, squared, is the number
    (Mathlib: Real.sq_sqrt)."""


# }}}


# {{{ absolute values and moduli


@theorem
def abs_of_positive(x: Real, positive: x > 0) -> abs(x) == x:
    """A positive number is its own absolute value (Mathlib: abs_of_pos)."""


@theorem
def abs_of_negative(x: Real, negative: x < 0) -> abs(x) == -x:
    """A negative number's absolute value is its negation (Mathlib: abs_of_neg)."""


@theorem
def modulus_squared(z: Complex) -> real(z * conj(z)) == abs(z) ** 2:
    """z times its conjugate is |z| squared, a real number
    (Mathlib: Complex.mul_conj, Complex.normSq_eq_norm_sq)."""


@theorem
def modulus_of_a_product(z: Complex, w: Complex) -> abs(z * w) == abs(z) * abs(w):
    """The modulus of a product is the product of the moduli (Mathlib: norm_mul)."""


@theorem
def triangle_inequality(x: Real, y: Real) -> abs(x + y) <= abs(x) + abs(y):
    """The absolute value of a sum is at most the sum of the absolute values
    (Mathlib: abs_add_le)."""


@theorem
def complex_triangle_inequality(z: Complex, w: Complex) -> abs(z + w) <= abs(z) + abs(w):
    """The modulus of a sum is at most the sum of the moduli (Mathlib: norm_add_le)."""


# }}}


# {{{ finite sums


@theorem
def one_more_term(f: Fn[Nat, Real], n: Nat) -> (
    sum(f[k] for k in Fin[n + 1]) == sum(f[k] for k in Fin[n]) + f[n]
):
    """The sum to n + 1 is the sum to n plus its last term (Mathlib: Finset.sum_range_succ)."""


@theorem
def shifted_sum(m: Nat, n: Nat, f: Fn[Nat, Real]) -> (
    sum(f[k] for k in Fin[n] if k >= m) == sum(f[k + m] for k in Fin[n - m])
):
    """The terms from m on, picked out by a guard, are a sum from 0 of the terms shifted
    by m (Mathlib: Finset.sum_filter, Finset.sum_nbij').

    The shape of a series that starts at order 1, ``for k in Fin[p + 1] if k >= 1``.
    """


@theorem
def geometric_sum(r: Real, n: Nat) -> (r - 1) * sum(r**k for k in Fin[n]) == r**n - 1:
    """The first n powers of r, summed, times r - 1 (Mathlib: geom_sum_mul)."""


@theorem
def sum_of_a_constant(c: Real, n: Nat) -> sum(c for k in Fin[n]) == n * c:
    """n terms that are all c add up to n times c (Mathlib: Finset.sum_const)."""


@theorem
def distribute(c: Real, f: Fn[Nat, Real], n: Nat) -> (
    c * sum(f[k] for k in Fin[n]) == sum(c * f[k] for k in Fin[n])
):
    """A factor of every term comes out of the sum (Mathlib: Finset.mul_sum)."""


@theorem
def sum_of_sums(f: Fn[Nat, Real], g: Fn[Nat, Real], n: Nat) -> (
    sum(f[k] + g[k] for k in Fin[n]) == sum(f[k] for k in Fin[n]) + sum(g[k] for k in Fin[n])
):
    """The sum of two terms, summed, is the two sums added (Mathlib: Finset.sum_add_distrib)."""


@theorem
def triangle_inequality_for_sums(f: Fn[Nat, Real], n: Nat) -> (
    abs(sum(f[k] for k in Fin[n])) <= sum(abs(f[k]) for k in Fin[n])
):
    """The absolute value of a sum is at most the sum of the absolute values of its terms
    (Mathlib: Finset.abs_sum_le_sum_abs)."""


@theorem
def sum_exchange(n: Nat, m: Nat, f: Fn[Fin[n], Fin[m], Real]) -> (
    sum(sum(f[i, j] for j in Fin[m]) for i in Fin[n])
    == sum(sum(f[i, j] for i in Fin[n]) for j in Fin[m])
):
    """Two finite sums exchange (Mathlib: Finset.sum_comm)."""


@theorem
def triangle_exchange(q: Nat, f: Fn[Fin[q], Fin[q], Real]) -> (
    sum(f[a, b] for a in Fin[q] for b in Fin[q - a])
    == sum(f[a, b] for b in Fin[q] for a in Fin[q - b])
):
    """A sum over the triangle a + b < q, by rows or by columns (Mathlib: Finset.sum_comm').

    The shape of a compressed Taylor expansion's coefficients, whose orders
    a + b stay below q.
    """


@theorem
def fiber_exchange(n: Nat, m: Nat, c: Fn[Fin[n], Fin[m]], y: Fn[Fin[n], Real]) -> (
    sum(sum(y[i] for i in Fin[n] if c[i] == j) for j in Fin[m]) == sum(y[i] for i in Fin[n])
):
    """A sum regrouped by a map: what each j receives, summed over j, is the total
    (Mathlib: Finset.sum_fiberwise_of_maps_to).

    The scatter of an assembly loop: c[i] is where term i goes.
    """


# }}}
