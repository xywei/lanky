"""Mathlib mode: the printer's Mathlib dialect, the project, and the oracle in it.

The printer is tested against golden source, as in ``test_lean.py``, and needs
no Lean. So do the project files, the switch that turns the mode on, and the
terms, draws and notes that come with ``Real``, ``Complex`` and ``exp``, ``log``
and ``sqrt``. The oracle in Mathlib mode is tested against a real Lean with a
real Mathlib, and those tests skip unless ``LANKY_LEAN_MATHLIB`` names a project
(``python -m lanky.mathlib DIR`` makes one). The CI job that fetches Mathlib
sets ``LANKY_LEAN_MATHLIB_TEST_REQUIRED=1``, under which they fail instead.
"""

from __future__ import annotations

import cmath
import json
import math
import os
import random
from collections.abc import Iterator
from fractions import Fraction
from pathlib import Path
from typing import NoReturn

import pymbolic.primitives as prim
import pytest

from lanky import exp, log, sqrt, theorem
from lanky import mathlib as mathlib_mode
from lanky.check import goal_guard_fact, hypotheses_fact
from lanky.intervals import ComplexValue, exp_value
from lanky.lean import (
    UnsupportedTerm,
    domain_guards,
    elementary_arguments,
    lean_identifier,
    lean_type,
    print_lean,
    statement_of,
)
from lanky.ledger import Fact, Status
from lanky.oracles.lean import (
    BASE_TACTICS,
    MATHLIB_TACTICS,
    LeanOracle,
    LeanSession,
    reduction_scripts,
    tactic_ladder,
)
from lanky.prelude import Complex, Fin, FinType, Fn, Nat, Real, Refined
from lanky.semantics import (
    DIVISION_BY_ZERO,
    OUTSIDE_THE_DOMAIN,
    TRUE_DIVISION_BY_ZERO,
    notes,
)
from lanky.terms import (
    Abs,
    Elementary,
    Exists,
    Forall,
    Product,
    Sum,
    UndefinedValue,
    Var,
    evaluate,
    render,
    structurally_equal,
)
from lanky.testing import check, in_sort, sample_value

ROOT = Path(__file__).resolve().parent.parent

x = Var("x")
y = Var("y")
z = Var("z")
w = Var("w")
n = Var("n")
m = Var("m")
i = Var("i")
j = Var("j")


def mathlib(expr: object, **sorts: object) -> str:
    """``expr`` printed in the Mathlib dialect, its free names bound at ``sorts``."""
    binders = tuple((Var(name), sort) for name, sort in sorts.items())
    text = print_lean(Forall(binders, expr) if binders else expr, mathlib=True)
    # drop the binders, and the guards naturals get, so a test reads the body
    for name, sort in sorts.items():
        text = text.removeprefix(f"∀ {name} : {lean_type(sort, mathlib=True)}, ")
        for guard in domain_guards(Var(name), sort, mathlib=True):
            text = text.removeprefix(f"{guard} → ")
    return text


# {{{ the claims used below

# A theorem under a public name is also collected as a property test (see
# lanky.pytest_plugin). The ones under a private name are not: a false one, and
# two it cannot draw. The exponential identities and the division undone were
# private while the tester read the reals in floating point and refuted them by
# rounding (#33); drawn exactly, they are tested like the rest.


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@theorem
def squares(n: Nat) -> 6 * sum(i**2 for i in Fin[n + 1]) == n * (n + 1) * (2 * n + 1):
    """The sum of the first squares."""


@theorem
def exp_add(x: Real, y: Real) -> exp(x + y) == exp(x) * exp(y):
    """The exponential turns sums into products."""


@theorem
def exp_positive(x: Real) -> exp(x) > 0:
    """The exponential is positive."""


@theorem
def complex_exp_add(z: Complex, w: Complex) -> exp(z + w) == exp(z) * exp(w):
    """And so does the complex exponential."""


@theorem
def binomial(x: Real.exact, y: Real.exact) -> (x + y) ** 2 == x**2 + 2 * x * y + y**2:
    """A ring identity over the reals."""


@theorem
def divided_back(x: Real, y: Real, hy: y != 0) -> x / y * y == x:
    """True division, undone, away from zero."""


@theorem
def _not_a_theorem(x: Real, y: Real) -> x * y <= x**3 + y**2:
    """False at x = -1, y = 1/2, so nothing proves it."""


@theorem
def _sqrt_of_negative(x: Real & (x < 0)) -> sqrt(x) == 0:
    """True of Mathlib's total square root, and never evaluable in Python."""


@theorem
def _contradictory(x: Real, h1: x > 1, h2: x < 0) -> x == 2:
    """Vacuous: no real is above one and below zero."""


@theorem
def commutes(a: Nat, b: Nat) -> a + b == b + a:
    """Core Lean's kind of claim, which Mathlib mode must still prove."""


@theorem
def scan_monotone(
    n: Nat,
    cnt: Fn[Fin[n], Nat],
    off: Fn[Fin[n + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),
) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
    """The scan from the README, which the core induction proves."""


@theorem
def exp_log_off_the_cut(x: Real) -> exp(log(x + 1j)) == x + 1j:
    """The principal logarithm undone, where the imaginary part keeps it off the cut."""


@theorem
def root_squared(x: Real, y: Real, hy: y != 0) -> sqrt(x + y * 1j) ** 2 == x + y * 1j:
    """The principal square root squared, where a hypothesis keeps it off the cut."""


@theorem
def exp_log_above_the_axis(x: Real, y: Real, hy: y > 0) -> exp(log(x + y * 1j)) == x + y * 1j:
    """The logarithm undone, where only a hypothesis shows its argument is not zero."""


@theorem
def exp_log_of_a_positive(x: Real) -> exp(log(x * x + 1 + 0j)) == x * x + 1 + 0j:
    """The logarithm undone on the positive real axis, which is off the cut."""


#: False in Python, ``log x - πi`` against ``log x + πi``, and true in Lean. A
#: term built here and not an annotation, where ``complex`` would be a variable.
_ACROSS_THE_CUT = Forall(
    ((x, Real),), log(x * complex(-1, -0.0)) == log(x * complex(-1, 0.0)), x > 0
)


# }}}


# {{{ core Lean is what it was


def test_core_lean_still_declines_what_only_mathlib_prints() -> None:
    """Without ``mathlib=True`` every function prints core Lean, as it always has."""
    with pytest.raises(UnsupportedTerm, match="Real needs Mathlib"):
        lean_type(Real)
    with pytest.raises(UnsupportedTerm):
        lean_type(Complex)
    for term in (
        gauss.term,
        exp_add.term,
        Forall(((x, Real),), Abs(x) >= 0),
        Forall(((n, Nat),), n / 2 >= 0),
        Forall(((n, Nat),), n + 0.5 >= 0),
    ):
        with pytest.raises(UnsupportedTerm):
            print_lean(term)
        with pytest.raises(UnsupportedTerm):
            statement_of(term)


def test_the_core_fragment_prints_the_same_in_both_dialects() -> None:
    """Mathlib mode reads more, and what core Lean read it reads the same way.

    The one difference is the ascription on a floor division by a literal,
    which keeps it integer division next to a real (see below); a statement
    without one is printed character for character as core Lean prints it.
    """
    for claim in (commutes, scan_monotone):
        assert print_lean(claim.term, mathlib=True) == print_lean(claim.term)
        core, full = statement_of(claim.term, "t"), statement_of(claim.term, "t", mathlib=True)
        assert (full.binders, full.hypotheses, full.goal) == (
            core.binders,
            core.hypotheses,
            core.goal,
        )
        assert full.mathlib and not core.mathlib


def test_the_dialect_does_not_outlive_the_call() -> None:
    assert print_lean(exp_positive.term, mathlib=True)
    with pytest.raises(UnsupportedTerm):
        print_lean(exp_positive.term)
    with pytest.raises(UnsupportedTerm):
        lean_type(Real)


def test_core_ladder_is_unchanged() -> None:
    assert tactic_ladder(statement_of(commutes.term, "commutes")) == list(BASE_TACTICS)
    assert reduction_scripts(statement_of(commutes.term, "commutes")) == []


# }}}


# {{{ the Mathlib dialect


def test_real_and_complex_are_mathlibs_types() -> None:
    assert lean_type(Real, mathlib=True) == "ℝ"
    assert lean_type(Real.exact, mathlib=True) == "ℝ"
    assert lean_type(Complex, mathlib=True) == "ℂ"
    assert lean_type(Fn[Fin[n], Real], mathlib=True) == "Int → ℝ"
    assert lean_type(Fn[Real, Complex], mathlib=True) == "ℝ → ℂ"
    assert lean_type(Real & (x > 0), mathlib=True) == "ℝ"
    # the index types and naturals are what they were
    assert lean_type(Nat, mathlib=True) == "Int"
    assert lean_type(FinType(n), mathlib=True) == "Int"


def test_a_float_is_the_rational_python_holds() -> None:
    """``0.1`` is not a tenth in Python, and it is not printed as one.

    Every float is ascribed ``ℝ``, the integral ones included: ``2.0 ** n`` is
    float arithmetic in Python, and a bare ``2`` would let Lean read it as
    natural arithmetic, where ``1 - 2 ** n`` truncates.
    """
    assert mathlib(x + 0.5, x=Real) == "x + (1 / 2 : ℝ)"
    assert mathlib(x * -0.5, x=Real) == "x * (-1 / 2 : ℝ)"
    assert mathlib(x + 0.1, x=Real) == "x + (3602879701896397 / 36028797018963968 : ℝ)"
    assert mathlib(1 - 2.0**n >= 0, n=Nat) == "1 - (2 : ℝ) ^ n.toNat ≥ 0"
    # pymbolic's operators refuse a Fraction, so a plugin builds these node by node
    assert mathlib(Product((x, Fraction(1, 3))), x=Real) == "x * (1 / 3 : ℝ)"
    # and an integral one is still the integer it equals
    assert mathlib(Product((n, Fraction(2, 1))), n=Nat) == "n * 2"
    with pytest.raises(UnsupportedTerm, match="not a real number"):
        print_lean(Forall(((x, Real),), x < math.inf), mathlib=True)


def test_a_complex_literal_is_its_parts_around_i() -> None:
    assert mathlib(z * complex(1.5, -2), z=Complex) == "z * (3 / 2 - 2 * Complex.I : ℂ)"
    assert mathlib(z + 1j, z=Complex) == "z + (0 + 1 * Complex.I : ℂ)"


def test_true_division_is_division_in_a_field() -> None:
    """Python's ``/`` never divides integers as integers, and neither does the print."""
    assert mathlib(x / y, x=Real, y=Real) == "(x : ℝ) / y"
    assert mathlib(n / 2 >= 0, n=Nat) == "(n : ℝ) / 2 ≥ 0"
    assert mathlib(z / w, z=Complex, w=Complex) == "(z : ℂ) / w"
    assert mathlib(n / z, n=Nat, z=Complex) == "(n : ℂ) / z"
    assert mathlib((x + 1) / (x - 1), x=Real) == "(x + 1 : ℝ) / (x - 1)"


def test_floor_division_stays_integer_division_next_to_a_real() -> None:
    """``x + n // 2`` must not become ``x + ↑n / 2``, which divides in ``ℝ``.

    Lean casts every leaf of an arithmetic tree to the widest type in it, so
    the floor division is ascribed, which makes it a leaf of type ``ℤ`` that is
    cast whole. ``Int.fdiv`` is an application and a leaf already. A floor
    division of a real is Python's float floor, which Lean does not have.
    """
    assert mathlib(x + n // 2, x=Real, n=Nat) == "x + (n / 2 : ℤ)"
    assert mathlib(x + n % 3, x=Real, n=Nat) == "x + (n % 3 : ℤ)"
    assert mathlib(x + n // m, x=Real, n=Nat, m=Nat) == "x + Int.fdiv n m"
    for term in (x // 2, x % 2, n // x):
        with pytest.raises(UnsupportedTerm, match="floor division or a remainder"):
            print_lean(Forall(((x, Real), (n, Nat)), term >= 0), mathlib=True)


def test_an_absolute_value_is_bars_or_a_norm() -> None:
    assert mathlib(Abs(x) >= 0, x=Real) == "|x| ≥ 0"
    assert mathlib(Abs(n - 3) >= 0, n=Nat) == "|n - 3| ≥ 0"
    # Python's abs of a complex number is its modulus, a real
    assert mathlib(Abs(z) >= 0, z=Complex) == "‖z‖ ≥ 0"
    # bars do not nest unambiguously, so the inner one is bracketed
    assert mathlib(Abs(Abs(x) - 1) >= 0, x=Real) == "|(|x| - 1)| ≥ 0"


def test_the_elementary_functions_are_mathlibs() -> None:
    assert mathlib(exp(x) > 0, x=Real) == "Real.exp x > 0"
    assert mathlib(log(x + 1) <= x, x=Real) == "Real.log (x + 1) ≤ x"
    assert mathlib(sqrt(x**2) == Abs(x), x=Real) == "Real.sqrt (x ^ 2) = |x|"
    assert mathlib(exp(z) != 0, z=Complex) == "Complex.exp z ≠ 0"
    # an integer argument is cast where the function is applied, as math.exp(n) casts
    assert mathlib(exp(n) >= 1, n=Nat) == "Real.exp n ≥ 1"
    # and the complex logarithm and square root are Mathlib's principal branches (#59)
    assert mathlib(sqrt(z) == z, z=Complex) == "Complex.sqrt z = z"
    assert mathlib(log(z) == log(z), z=Complex) == "Complex.log z = Complex.log z"
    assert mathlib(Abs(log(z + 2)) < 1, z=Complex) == "‖Complex.log (z + 2)‖ < 1"
    with pytest.raises(UnsupportedTerm, match="needs Real.exp"):
        print_lean(exp_positive.term)
    # a node built by hand with a function lanky has no Mathlib name for
    with pytest.raises(UnsupportedTerm, match="does not print"):
        print_lean(Forall(((x, Real),), Elementary("sin", x) <= 1), mathlib=True)


def test_a_complex_logarithm_carries_the_claim_that_it_is_off_the_cut() -> None:
    """``cmath.log`` picks a side of its cut by the sign of a zero, and Lean cannot (#59).

    At ``x = 1`` the two sides are ``-πi`` and ``πi`` in Python, while both
    print as ``Complex.log (x * (-1 + 0 * Complex.I : ℂ))``, which Lean's
    ``simp`` proves equal. Printed as it stands, the statement was a proof of
    something Python refutes at every positive ``x``, so it is printed with a
    side condition, that the argument is off the cut, which is false there,
    and which the Lean oracle has to prove before the statement counts.
    """
    assert evaluate(log(x * complex(-1.0, -0.0)), {"x": 1.0}) == pytest.approx(-math.pi * 1j)
    assert evaluate(log(x * complex(-1.0, 0.0)), {"x": 1.0}) == pytest.approx(math.pi * 1j)
    statement = statement_of(_ACROSS_THE_CUT, "across", mathlib=True)
    argument = "x * (-1 + 0 * Complex.I : ℂ)"
    assert statement.goal == f"Complex.log ({argument}) = Complex.log ({argument})"
    # the two arguments print alike, and the claim about them is made once
    (condition,) = statement.side_conditions
    assert condition.source("intros\nnorm_num") == (
        "theorem Lanky.across_branch_cut_0 (x : ℝ) (h0 : x > 0) : "
        f"0 < Complex.re ({argument}) ∨ Complex.im ({argument}) ≠ 0 := by\n"
        "  intros\n  norm_num\n"
    )
    # a square root's cut is the negative axis, and zero is on neither side of it
    root = statement_of(Forall(((z, Complex),), sqrt(z + 1j) == sqrt(z + 1j)), "r", mathlib=True)
    (condition,) = root.side_conditions
    assert condition.proposition == (
        "∀ z : ℂ, 0 ≤ Complex.re (z + (0 + 1 * Complex.I : ℂ)) "
        "∨ Complex.im (z + (0 + 1 * Complex.I : ℂ)) ≠ 0"
    )
    # the real logarithm of a real argument is Mathlib's, and claims nothing more
    assert mathlib(log(Abs(z)) <= Abs(z), z=Complex) == "Real.log ‖z‖ ≤ ‖z‖"
    for term in (Forall(((z, Complex),), log(Abs(z)) <= Abs(z)), exp_add.term):
        assert statement_of(term, mathlib=True).side_conditions == ()
    # and core Lean prints neither the numbers nor the functions, so it has nothing to claim
    with pytest.raises(UnsupportedTerm, match="Real needs Mathlib"):
        statement_of(_ACROSS_THE_CUT)
    with pytest.raises(UnsupportedTerm, match="needs Real.log"):
        statement_of(Forall(((n, Nat),), log(n * 1j) == log(n * 1j)))


def test_a_literal_on_the_cut_is_declined_and_one_off_it_needs_no_claim() -> None:
    """A literal argument is looked at where it is printed (#59).

    Only a node built by hand holds one, since ``lanky.log`` of a number is
    Python's value. ``log`` of a negative real or of zero is declined, the
    second because ``cmath.log`` raises where Lean's total logarithm is ``0``;
    ``sqrt`` of zero is ``0`` in both readings, and a literal off the cut is
    a point where the two branches agree, with nothing to claim.
    """
    for function, value in (("log", complex(-1, 0)), ("log", complex(-1, -0.0)), ("log", 0j)):
        with pytest.raises(UnsupportedTerm, match="branch cut"):
            print_lean(Forall(((x, Real),), Elementary(function, value) == x), mathlib=True)
    with pytest.raises(UnsupportedTerm, match="complex square root on its branch cut"):
        print_lean(Forall(((x, Real),), Elementary("sqrt", complex(-4, 0)) == x), mathlib=True)
    for function, value, printed in (
        ("sqrt", 0j, "Complex.sqrt (0 + 0 * Complex.I : ℂ)"),
        ("log", 1j, "Complex.log (0 + 1 * Complex.I : ℂ)"),
        ("log", complex(2, 0), "Complex.log (2 + 0 * Complex.I : ℂ)"),
        ("sqrt", complex(-4, 1), "Complex.sqrt (-4 + 1 * Complex.I : ℂ)"),
    ):
        term = Forall(((z, Complex),), Elementary(function, value) == z)
        statement = statement_of(term, "lit", mathlib=True)
        assert statement.goal == f"{printed} = z"
        assert statement.side_conditions == ()


def test_a_side_condition_assumes_what_python_has_evaluated_by_then() -> None:
    """The claim that an argument is off the cut is made under the guards around it (#59).

    A theorem's hypotheses, a refinement and the ``if`` of a generator around
    the argument hold wherever Python computes it, and a guard that takes a
    logarithm itself has a claim of its own, without its own guard. An
    existential's binder is quantified over, since the claim is about every
    point Python may reach.
    """

    def conditions(term: object) -> list[str]:
        statement = statement_of(term, "c", mathlib=True)
        return [condition.proposition for condition in statement.side_conditions]

    def off(argument: str) -> str:
        return f"0 < Complex.re ({argument}) ∨ Complex.im ({argument}) ≠ 0"

    xy = "x + y * (0 + 1 * Complex.I : ℂ)"
    assert conditions(exp_log_off_the_cut.term) == [
        f"∀ x : ℝ, {off('x + (0 + 1 * Complex.I : ℂ)')}"
    ]
    hypothesis = Forall(((x, Real), (y, Real)), exp(log(x + y * 1j)) == x + y * 1j, y > 0)
    assert conditions(hypothesis) == [f"∀ x : ℝ, ∀ y : ℝ, y > 0 → {off(xy)}"]
    nested = Forall(((x, Real),), Forall(((y, Real),), log(x + y * 1j) == 0, y > 0))
    assert conditions(nested) == [f"∀ x : ℝ, ∀ y : ℝ, y > 0 → {off(xy)}"]
    in_the_guard = Forall(((x, Real),), Forall(((y, Real),), y > 0, Abs(log(x + y * 1j)) < 1))
    assert conditions(in_the_guard) == [f"∀ x : ℝ, ∀ y : ℝ, {off(xy)}"]
    witness = Exists(((x, Real),), log(x + 1j) == 0)
    assert conditions(witness) == [f"∀ x : ℝ, {off('x + (0 + 1 * Complex.I : ℂ)')}"]
    summed = Forall(
        ((n, Nat),),
        Sum(((i, Refined(FinType(n), (i > 0,))),), Abs(log(i * 1j)), i % 2 == 0) >= 0,
    )
    assert conditions(summed) == [
        "∀ n : Int, 0 ≤ n → ∀ i : Int, 0 ≤ i → i < n → i > 0 → (i % 2 : ℤ) = 0 → "
        + off("i * (0 + 1 * Complex.I : ℂ)")
    ]
    # one claim per argument, however often it is taken
    twice = Forall(((x, Real),), log(x + 1j) + sqrt(x + 1j) == log(x + 1j))
    assert len(conditions(twice)) == 2
    # a refinement that takes one would have to be claimed before its binder exists
    refined = Forall(((z, Refined(Complex, (Abs(log(z)) < 1,))),), z == z)
    with pytest.raises(UnsupportedTerm, match="domain of z"):
        statement_of(refined, mathlib=True)
    # and a complex logarithm is a complex number, which Python does not order
    with pytest.raises(UnsupportedTerm, match="orders complex numbers"):
        print_lean(Forall(((x, Real),), log(x + 1j) < 1), mathlib=True)


def test_a_complex_logarithm_or_square_root_carries_no_note() -> None:
    """Lean proves one only off the cut and away from zero, where the readings are one (#59)."""
    assert notes(exp_log_off_the_cut.term, mathlib=True) == ()
    assert notes(root_squared.term, mathlib=True) == ()
    assert notes(Forall(((z, Complex),), sqrt(z) * sqrt(z) == z), mathlib=True) == ()
    # a real one beside it still has its note
    both = Forall(((x, Real),), log(x + 1j) == log(x) + 0j)
    assert notes(both, mathlib=True) == (OUTSIDE_THE_DOMAIN,)
    kinds = [(node.function, kind) for node, kind in elementary_arguments(both)]
    assert kinds == [("log", "Complex"), ("log", "Real")]
    summed = Forall(((n, Nat),), Sum(((i, FinType(n)),), log(i + 1j)) == 0)
    assert [kind for _, kind in elementary_arguments(summed)] == ["Complex"]


def test_complex_numbers_are_not_ordered() -> None:
    assert mathlib(z == w, z=Complex, w=Complex) == "z = w"
    assert mathlib(Abs(z) < 1, z=Complex) == "‖z‖ < 1"
    for term in (z < w, z >= 0, exp(z) > 0):
        with pytest.raises(UnsupportedTerm, match="orders complex numbers"):
            print_lean(Forall(((z, Complex), (w, Complex)), term), mathlib=True)


def test_a_reduction_is_a_finset_sum() -> None:
    """``Fin[n]`` is ``Finset.Ico (0 : ℤ) n``, so the binder is an integer.

    A sum that is an operand is bracketed, because the body of ``∑`` extends as
    far to the right as it can, and a guard or a refinement filters it with
    ``with``.
    """
    assert print_lean(gauss.term, mathlib=True) == (
        "∀ n : Int, 0 ≤ n → 2 * (∑ i ∈ Finset.Ico (0 : ℤ) (n + 1), i) = n * (n + 1)"
    )
    guarded = Sum(((i, FinType(n)),), i**2, i % 2 == 0)
    assert mathlib(guarded >= 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) n with (i % 2 : ℤ) = 0, i ^ 2) ≥ 0"
    )
    nested = Sum(((i, FinType(n)), (j, FinType(i))), i * j + 1)
    assert mathlib(nested == 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) n, ∑ j ∈ Finset.Ico (0 : ℤ) i, (i * j + 1)) = 0"
    )
    refined = Sum(((i, Refined(FinType(n), (i > 2,))),), x * i)
    assert mathlib(refined >= 0, n=Nat, x=Real) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) n with i > 2, x * i) ≥ 0"
    )
    with pytest.raises(UnsupportedTerm, match="no finite extent"):
        print_lean(Forall(((n, Nat),), Sum(((i, Nat),), i) >= 0), mathlib=True)


#: Two sums that are false in Python and true read over ``Nat``: ``i - 1``
#: truncates at ``i = 0``, so the first sum is ``1`` there and ``0`` in Python,
#: and a count ``- 3`` truncates to ``0`` at ``n = 0``, where Python has ``-3``.
_LITERAL_BOUND = Sum(((i, FinType(3)),), i - 1) == 1
_NUMERAL_BODY = Forall(((n, Nat),), Sum(((i, FinType(n)),), 1) - 3 >= 0)


def test_a_sum_is_over_integers_whatever_types_its_bound_and_body() -> None:
    """A numeral nothing types is a ``Nat`` to Lean, and ``Nat`` subtraction truncates.

    ``Finset.Ico 0 3`` is a set of naturals, and ``∑ i ∈ s, 1`` is a natural,
    so without the ascriptions both claims below were proved (by ``decide``
    and by ``omega``), while Python evaluates them to ``False``.
    """
    assert evaluate(_LITERAL_BOUND, {}) is False
    assert print_lean(_LITERAL_BOUND, mathlib=True) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) 3, (i - 1)) = 1"
    )
    assert print_lean(_NUMERAL_BODY, mathlib=True) == (
        "∀ n : Int, 0 ≤ n → (∑ i ∈ Finset.Ico (0 : ℤ) n, (1 : ℤ)) - 3 ≥ 0"
    )
    negative = Forall(((n, Nat),), Sum(((i, FinType(n)),), -2) <= 0)
    assert print_lean(negative, mathlib=True) == (
        "∀ n : Int, 0 ≤ n → (∑ i ∈ Finset.Ico (0 : ℤ) n, (-2 : ℤ)) ≤ 0"
    )
    # a float body is ascribed already, and a body with a variable in it is typed by it
    assert mathlib(Sum(((i, FinType(n)),), 0.5) >= 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) n, (1 / 2 : ℝ)) ≥ 0"
    )


#: Two claims whose operand is arithmetic on numerals alone, which only a term
#: built node by node holds: false in Python and true read over ``Nat``, where
#: ``1 - 2`` is ``0``. ``abs(-1) == 0`` is false, and so is ``-n == 0`` at
#: ``n = 1``.
_CLOSED_ABS = prim.Comparison(Abs(prim.Sum((1, -2))), "==", 0)
_CLOSED_BODY = Forall(
    ((n, Nat),), prim.Comparison(Sum(((i, FinType(n)),), prim.Sum((1, -2))), "==", 0)
)


def test_arithmetic_on_numerals_alone_is_ascribed_where_nothing_types_it() -> None:
    """``abs`` and ``∑`` take their type from the operand, which here has no type to give.

    A comparison with no variable on either side is ascribed ``Int``, and so is
    such a base of a power; an absolute value of one, and the body of a sum,
    are ascribed the same way, or Lean reads ``1 - 2`` as a truncated ``Nat``
    subtraction and proves both claims.
    """
    assert evaluate(_CLOSED_ABS, {}) is False
    assert evaluate(_CLOSED_BODY.body, {"n": 1}) is False
    assert print_lean(_CLOSED_ABS, mathlib=True) == "|(1 - 2 : ℤ)| = 0"
    assert print_lean(_CLOSED_BODY, mathlib=True) == (
        "∀ n : Int, 0 ≤ n → (∑ i ∈ Finset.Ico (0 : ℤ) n, (1 - 2 : ℤ)) = 0"
    )
    # an operand with a variable in it is typed by the variable, as before
    assert mathlib(Abs(x - 1) >= 0, x=Real) == "|x - 1| ≥ 0"
    assert mathlib(Sum(((i, FinType(n)),), i - 1) >= 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico (0 : ℤ) n, (i - 1)) ≥ 0"
    )


def test_an_index_type_with_a_real_bound_is_declined() -> None:
    """``Fin[2.5]`` is ``range(2)`` to the tester and three points to ``i < 5/2``."""
    for domain in (FinType(x), FinType(2.5), FinType(x + 1)):
        with pytest.raises(UnsupportedTerm, match="bound"):
            print_lean(Forall(((x, Real), (i, domain)), i >= 0), mathlib=True)
        with pytest.raises(UnsupportedTerm, match="bound"):
            print_lean(Forall(((x, Real),), Sum(((i, domain),), i) >= 0), mathlib=True)
    # an integral Fraction is an integer bound
    assert "i < 3" in print_lean(Forall(((i, FinType(Fraction(3, 1))),), i >= 0), mathlib=True)


#: ``round(0.5) == 1`` with ``round`` a free name, as an annotation read it
#: before #63 made it Python's: false in Python, where ``round(0.5)`` is ``0``,
#: and true of Mathlib's ``round``, which rounds half up (#64).
_FREE_ROUND = Forall((), Var("round")(0.5) == 1)


def test_a_free_name_is_not_handed_to_mathlib() -> None:
    """A free name is shown, and declined where Mathlib has a declaration of that name (#64)."""
    assert print_lean(_FREE_ROUND, mathlib=True) == "round (1 / 2 : ℝ) = 1"
    with pytest.raises(UnsupportedTerm, match="mentions round, which no parameter"):
        statement_of(_FREE_ROUND, "rounds_half_up", mathlib=True)
    a, b = Var("a"), Var("b")
    smaller = Forall(((a, Nat), (b, Nat)), Var("min")(a, b) <= a)
    with pytest.raises(UnsupportedTerm, match="mentions min, which no parameter"):
        statement_of(smaller, "minimum", mathlib=True)


def test_a_mathlib_statement_is_marked_and_arranged_as_a_theorem() -> None:
    statement = statement_of(gauss.term, "gauss", mathlib=True)
    assert statement.mathlib
    assert statement.binders == (("n", "Int"),)
    assert statement.hypotheses == (("h0", "0 ≤ n"),)
    assert statement.goal == "2 * (∑ i ∈ Finset.Ico (0 : ℤ) (n + 1), i) = n * (n + 1)"
    assert gauss.lean(mathlib=True) == print_lean(gauss.term, mathlib=True)
    divided = statement_of(divided_back.term, "divided_back", mathlib=True)
    assert divided.binders == (("x", "ℝ"), ("y", "ℝ"))
    assert divided.hypotheses == (("h0", "y ≠ 0"),)
    assert divided.goal == "((x : ℝ) / y) * y = x"
    assert divided.proposition == "∀ x : ℝ, ∀ y : ℝ, y ≠ 0 → ((x : ℝ) / y) * y = x"
    # declared in a namespace of its own, where no Mathlib lemma can already have the name
    assert statement.declared_name == "Lanky.gauss"
    assert statement.source("omega").startswith("theorem Lanky.gauss (n : Int) (h0 : 0 ≤ n) :")
    # and so is a core statement, where no root declaration of core Lean can (#39)
    core = statement_of(commutes.term, "commutes")
    assert core.declared_name == "Lanky.commutes"
    assert core.source("omega").startswith("theorem Lanky.commutes (a : Int)")


def test_the_mathlib_ladder_follows_the_core_one() -> None:
    """Core Lean's attempts come first, then Mathlib's, then the sum induction."""
    ladder = tactic_ladder(statement_of(exp_positive.term, "exp_positive", mathlib=True))
    assert ladder == [*BASE_TACTICS, *MATHLIB_TACTICS]
    (script,) = reduction_scripts(statement_of(gauss.term, "gauss", mathlib=True))
    assert script.startswith(
        "obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0\ninduction n with\n| zero =>\n"
    )
    assert "Finset.insert_Ico_right_eq_Ico_add_one" in script
    assert "first | (have hih := ih (by omega)) | (have hih := ih) | skip" in script
    assert tactic_ladder(statement_of(gauss.term, "gauss", mathlib=True))[-1] == script
    # a complex logarithm or square root gets two more whole-goal attempts (#59),
    # the second with a discharger that reads the hypotheses
    ladder = tactic_ladder(statement_of(exp_log_off_the_cut.term, "e", mathlib=True))
    assert ladder[: len(BASE_TACTICS) + len(MATHLIB_TACTICS)] == [*BASE_TACTICS, *MATHLIB_TACTICS]
    plain, discharged = ladder[len(BASE_TACTICS) + len(MATHLIB_TACTICS) :]
    assert plain.startswith("simp [Real.exp_add, ") and plain.endswith(", Complex.ext_iff]")
    assert "Complex.exp_log, Complex.sqrt" in plain
    assert discharged.startswith("simp (disch := (simp [Complex.ext_iff] <;> first | positivity")
    assert discharged.endswith(plain.removeprefix("simp "))
    # a quantified goal is the core induction's, and a sum over no natural bound is nobody's
    assert reduction_scripts(statement_of(scan_monotone.term, "s", mathlib=True)) == []
    constant = Forall(((x, Real),), Sum(((i, FinType(3)),), x) == 3 * x)
    assert reduction_scripts(statement_of(constant, "c", mathlib=True)) == []


# }}}


# {{{ the project, and the switch


def test_the_project_is_pinned_to_one_mathlib() -> None:
    """The three files lanky ships pin Mathlib, its toolchain and every dependency."""
    template = mathlib_mode.TEMPLATE
    assert sorted(path.name for path in template.iterdir()) == sorted(mathlib_mode.PROJECT_FILES)
    toolchain = (template / "lean-toolchain").read_text(encoding="utf-8").strip()
    assert toolchain == mathlib_mode.TOOLCHAIN == "leanprover/lean4:v4.29.1"
    lakefile = (template / "lakefile.toml").read_text(encoding="utf-8")
    assert f'rev = "{mathlib_mode.MATHLIB_REVISION}"' in lakefile
    manifest = json.loads((template / "lake-manifest.json").read_text(encoding="utf-8"))
    (entry,) = [package for package in manifest["packages"] if package["name"] == "mathlib"]
    assert entry["inputRev"] == mathlib_mode.MATHLIB_REVISION
    assert len(entry["rev"]) == 40
    # every dependency is pinned to a commit, not to a branch
    assert all(len(package["rev"]) == 40 for package in manifest["packages"])


def test_writing_the_project_copies_the_pinned_files(tmp_path) -> None:
    target = tmp_path / "mathlib"
    assert mathlib_mode.main([str(target), "--no-fetch"]) == 0
    for name in mathlib_mode.PROJECT_FILES:
        assert (target / name).read_bytes() == (mathlib_mode.TEMPLATE / name).read_bytes()
    assert mathlib_mode.revision(target) == (
        "v4.29.1 (5e932f97dd25535344f80f9dd8da3aab83df0fe6)"
    )
    # a hand-edited file is put back, and what Lake keeps is left alone
    (target / "lean-toolchain").write_text("leanprover/lean4:v4.34.0\n", encoding="utf-8")
    (target / ".lake").mkdir()
    mathlib_mode.write_project(target)
    assert (target / "lean-toolchain").read_text(encoding="utf-8").strip().endswith("v4.29.1")
    assert (target / ".lake").is_dir()


def test_a_project_that_is_not_ready_is_named_with_the_fix(tmp_path) -> None:
    missing = tmp_path / "nowhere"
    assert "not a directory" in mathlib_mode.problem(missing)
    assert "python -m lanky.mathlib" in mathlib_mode.problem(missing)
    assert "no lean-toolchain" in mathlib_mode.problem(tmp_path)
    mathlib_mode.write_project(tmp_path)
    assert "no Mathlib under .lake/packages" in mathlib_mode.problem(tmp_path)
    (tmp_path / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    assert mathlib_mode.problem(tmp_path) is None


def test_the_oracle_follows_the_variable_when_it_is_asked(monkeypatch, tmp_path) -> None:
    """The registered oracle is built at import; the mode is read when a session is wanted.

    Unset, it is core Lean, with a session of its own; set, a session in the
    project named, kept apart from the core one.
    """
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    oracle = LeanOracle()
    core = oracle.session
    assert core.mathlib is None
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path))
    assert oracle.session.mathlib == str(tmp_path)
    assert oracle.session is not core
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", "")
    assert oracle.session is core
    # an oracle given a session keeps it, whatever the variable says
    pinned = LeanSession()
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path))
    assert LeanOracle(session=pinned).session is pinned
    # and so does one a session is assigned to, as when session was an attribute
    oracle.session = pinned
    assert oracle.session is pinned


def test_mathlib_mode_takes_what_core_lean_declines(monkeypatch, tmp_path) -> None:
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path))
    oracle = LeanOracle()
    for claim in (gauss, exp_add, complex_exp_add, divided_back, _sqrt_of_negative):
        assert oracle.can_establish(claim.fact()), claim.__name__
    monkeypatch.delenv("LANKY_LEAN_MATHLIB")
    for claim in (gauss, exp_add, complex_exp_add, divided_back, _sqrt_of_negative):
        assert not oracle.can_establish(claim.fact()), claim.__name__
    assert oracle.can_establish(commutes.fact())


def test_an_unready_project_makes_the_oracle_unavailable(monkeypatch, tmp_path) -> None:
    """Asked for Mathlib and not given it, the oracle says why rather than fall back.

    Falling back to core Lean would hide the mistake: every claim that needs
    Mathlib would quietly read ``tested``.
    """
    import lanky.oracles.lean as lean_oracle

    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    monkeypatch.setattr(lean_oracle.shutil, "which", lambda name: f"/bin/{name}")
    monkeypatch.setattr(lean_oracle, "_lean_interact_installed", lambda: True)
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path / "missing"))
    oracle = LeanOracle()
    available, reason = oracle.availability()
    assert not available
    assert "not a directory" in reason and "python -m lanky.mathlib" in reason
    result = oracle.establish(exp_positive.fact())
    assert result.status is Status.ASSUMED
    assert reason in result.provenance["lean_declined"]
    # a project that looks ready is available, untested, and names where Mathlib is
    mathlib_mode.write_project(tmp_path)
    (tmp_path / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path))
    available, reason = oracle.availability()
    assert available
    assert reason.startswith("untested until the first fact") and str(tmp_path) in reason


def test_a_pinned_version_that_is_not_the_projects_is_refused(monkeypatch, tmp_path) -> None:
    """``LANKY_LEAN_VERSION`` says which Lean; a Mathlib project already has one."""
    pytest.importorskip("lean_interact")
    mathlib_mode.write_project(tmp_path)
    (tmp_path / ".lake" / "packages" / "mathlib").mkdir(parents=True)

    class Config:
        def __init__(self, project, **options) -> None:
            self.lean_version = "v4.29.1"

    class Server:
        def __init__(self, config) -> None:
            raise AssertionError("no server is started for a refused session")

    monkeypatch.setenv("LANKY_LEAN_VERSION", "v4.30.0")
    session = LeanSession(mathlib=str(tmp_path))
    assert not session._start_with_mathlib(Config, Server, {})
    assert "LANKY_LEAN_VERSION is v4.30.0" in session.error
    assert "runs Lean v4.29.1" in session.error


# }}}


# {{{ terms, draws and notes over the reals


def test_the_elementary_functions_are_pythons_at_numbers() -> None:
    assert exp(0) == 1.0
    assert log(Fraction(1)) == 0.0
    assert sqrt(4) == 2.0
    assert exp(0j) == 1 + 0j
    assert isinstance(exp(1j), complex)
    for value, function in ((0, log), (-1.0, log), (-1, sqrt), (1000, exp), (0j, log)):
        with pytest.raises(UndefinedValue, match="has no value in Python"):
            function(value)
    with pytest.raises(TypeError):
        exp(True)


def test_an_elementary_function_of_a_term_is_a_node() -> None:
    term = exp(x + 1)
    assert isinstance(term, Elementary)
    assert structurally_equal(term, Elementary("exp", x + 1))
    assert not structurally_equal(term, Elementary("log", x + 1))
    assert render(log(x) + sqrt(y)) == "log(x) + sqrt(y)"
    assert evaluate(exp(x) > 1, {"x": 0.5}) is True
    assert evaluate(log(z), {"z": -1 + 0j}) == pytest.approx(math.pi * 1j)
    with pytest.raises(UndefinedValue):
        evaluate(log(x), {"x": 0})


def test_complex_is_a_sort_that_draws_complex_numbers() -> None:
    """A draw of ``Complex`` has two fractions for parts, whatever its exactness class (#33)."""
    assert Complex.exactness == "approx"
    assert str(Complex) == "Complex"
    assert str(Complex.exact) == "Complex[exact]"
    rng = random.Random(0)
    for sort in (Complex, Complex.exact, Complex.reassoc):
        drawn = [sample_value(sort, rng, {}) for _ in range(20)]
        assert all(isinstance(value, ComplexValue) for value in drawn)
        assert all(
            isinstance(v.real, Fraction) and isinstance(v.imag, Fraction) for v in drawn
        )
    assert in_sort(1 + 2j, Complex, {})
    assert in_sort(0.5, Complex, {})
    assert in_sort(ComplexValue(Fraction(1), Fraction(2)), Complex, {})
    assert not in_sort(True, Complex, {})
    assert not in_sort("1j", Complex, {})


def test_real_is_drawn_exactly_whatever_its_exactness_class() -> None:
    """The exactness class says how a kernel computes, not what a statement means (#33)."""
    rng = random.Random(0)
    for sort in (Real, Real.exact, Real.reassoc, Real.approx):
        drawn = [sample_value(sort, rng, {}) for _ in range(50)]
        assert all(type(value) is Fraction for value in drawn)
        assert any(value == 0 for value in drawn)
        assert any(value.denominator > 1 for value in drawn)
    assert in_sort(exp_value(Fraction(1)), Real, {})


def test_identities_rounding_broke_are_tested(tmp_path) -> None:
    """#33: the float reading refuted these, and Lean proves them over ``ℝ``.

    Drawn as fractions, with ``exp`` enclosed, they hold at every draw: the
    ring identities exactly, and the exponential ones to within enclosures
    that agree to far more bits than a float has. ``lanky check`` exits 0 on
    them, where it exited 1. (``(x + 1) - 1 == x`` happened to hold at the
    floats the old draws made, which were multiples of ``2**-52``; a tenth
    is not one, and ``0.1`` is the rational the float holds.)
    """

    @theorem
    def add_one_back(x: Real) -> (x + 1) - 1 == x:
        """Exact in ``ℝ``."""

    @theorem
    def add_a_tenth_back(x: Real) -> (x + 0.1) - 0.1 == x:
        """Exact in ``ℝ``, and false at most floats."""

    for claim in (exp_add, add_one_back, add_a_tenth_back, divided_back, complex_exp_add):
        report = claim.report(100)
        assert report.ok, (claim.__name__, report.counterexample)
        assert report.valid == 100, claim.__name__
    source = (
        "from __future__ import annotations\n"
        "from lanky import exp, theorem\n"
        "from lanky.prelude import Real\n\n\n"
        "@theorem\n"
        "def exp_add(x: Real, y: Real) -> exp(x + y) == exp(x) * exp(y):\n"
        '    """The exponential turns sums into products."""\n\n\n'
        "@theorem\n"
        "def add_back(x: Real) -> (x + 0.1) - 0.1 == x:\n"
        '    """Adding a tenth and taking it away."""\n'
    )
    path = tmp_path / "reals.py"
    path.write_text(source, encoding="utf-8")
    from lanky import cli
    from lanky.check import check_path

    assert [fact.status for fact in check_path(str(path))] == [Status.TESTED, Status.TESTED]
    assert cli.main(["check", str(path)]) == 0


def test_a_false_real_identity_is_still_refuted() -> None:
    """A refutation is where the enclosures exclude the claim, so it is as definite as a proof."""
    cases = [
        ([("x", Real), ("y", Real)], exp(x + y) == exp(x) + exp(y)),
        ([("x", Real)], sqrt(x**2) == x),
        ([("x", Real)], log(exp(x) + 1) <= x),
        ([("z", Complex), ("w", Complex)], exp(z + w) == exp(z) + exp(w)),
    ]
    for variables, goal in cases:
        report = check(variables, [], goal)
        assert not report.ok, render(goal)
        assert report.reason == "the goal is false at this assignment"
    report = _not_a_theorem.report()
    assert not report.ok
    x_value, y_value = report.counterexample["x"], report.counterexample["y"]
    assert x_value * y_value > x_value**3 + y_value**2


def test_a_claim_rounding_hid_is_refuted() -> None:
    """``x + 1e-20 == x`` holds at every float the old draws reached, and at no rational."""
    report = check([("x", Real)], [], x + 1e-20 == x)
    assert not report.ok
    assert set(report.counterexample) == {"x"}


def test_an_exponential_that_underflows_a_float_is_no_counterexample() -> None:
    """``math.exp(x - 1000)`` is ``0.0``, and ``exp(x - 1000) > 0`` was refuted; it holds."""
    report = check([("x", Real)], [], exp(x - 1000) > 0)
    assert report.ok and report.valid == 200


def test_an_equality_is_evidence_only_where_it_is_asserted() -> None:
    """The negation of a true identity is refuted where it is decided, and only there.

    At most draws the two sides of ``exp(x + y) == exp(x) * exp(y)`` agree to
    within their enclosures, which is no certain ``True`` under a negation, so
    those draws decide nothing. Where ``x`` or ``y`` is ``0``, both sides are
    one enclosure, of the exponential of the other, since ``exp(0)`` is ``1``
    exactly and ``x + 0`` is ``x``, and there the negation is false.
    """
    report = check([("x", Real), ("y", Real)], [], ~(exp(x + y) == exp(x) * exp(y)))
    assert not report.ok
    assert 0 in report.counterexample.values()
    assert report.undecided > 0
    # an order the enclosures straddle is decided at x = 0 only, where it is exact
    report = check([("x", Real)], [], exp(x) * exp(-x) <= 1)
    assert report.ok and report.undecided > report.valid > 0
    # one enclosure is one number: exp(x) == exp(y) holds for certain where x is y
    report = check([("x", Real), ("y", Real)], [exp(x) == exp(y)], x == y)
    assert report.ok and report.valid > 0 and report.undecided == 0


def test_an_exact_complex_identity_is_tested_exactly() -> None:
    @theorem
    def difference_of_squares(z: Complex.exact, w: Complex.exact) -> (z + w) * (z - w) == (
        z * z - w * w
    ):
        """A ring identity, exact at the fractions a draw has for parts."""

    report = difference_of_squares.report(50)
    assert report.ok and report.valid == 50


def test_a_function_outside_its_python_domain_decides_nothing() -> None:
    """``sqrt`` of a negative number is a gap between the readings, not a refutation.

    Every draw of ``x < 0`` has no value in Python, so none decides anything,
    and the report says why; Mathlib's square root of a negative number is
    ``0``, where Lean proves the claim (see the Mathlib tests below).
    """
    report = _sqrt_of_negative.report(20)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0
    assert "has no value in Python" in report.reason
    # and a draw inside the domain is a draw like any other
    report = check([("x", Real)], [], log(exp(x)) <= x + 1)
    assert report.ok and report.valid > 0


def test_a_function_outside_its_python_domain_is_an_operand_with_no_answer() -> None:
    """A connective reads ``log(0)`` as it reads a division by zero (#25).

    Python has no value there and Mathlib's is total, so another operand
    still settles the connective, whichever side it is written on, and a
    conjunct the draw breaks refutes the goal however the other one fares.
    """
    for claim in ((log(x) > 1) & (x > 0), (x > 0) & (log(x) > 1)):
        assert evaluate(claim, {"x": 0}) is False
    for claim in ((log(x) > 1) | (x == 0), (x == 0) | (log(x) > 1)):
        assert evaluate(claim, {"x": 0}) is True
    with pytest.raises(UndefinedValue):
        evaluate((log(x) > 1) | (x > 0), {"x": 0})
    report = check([("x", Real)], [], (sqrt(x) >= 0) & (x >= 0))
    assert not report.ok
    assert report.counterexample["x"] < 0


def test_the_readings_gaps_over_the_reals_are_noted_in_mathlib_mode() -> None:
    assert TRUE_DIVISION_BY_ZERO in notes(divided_back.term, mathlib=True)
    assert notes(Forall(((x, Real),), x / 2 == x * 0.5), mathlib=True) == ()
    assert notes(_sqrt_of_negative.term, mathlib=True) == (OUTSIDE_THE_DOMAIN,)
    assert OUTSIDE_THE_DOMAIN in notes(
        Forall(((x, Real),), log(x * x) == 2 * log(x)), mathlib=True
    )
    assert notes(Forall(((x, Real),), Elementary("log", 2) > 0), mathlib=True) == ()
    assert notes(exp_add.term, mathlib=True) == ()
    # the integer note is the integer one, and the two can stand together
    both = Forall(((n, Nat), (x, Real)), n // n + x / x == 2)
    assert notes(both, mathlib=True) == (DIVISION_BY_ZERO, TRUE_DIVISION_BY_ZERO)


def test_core_mode_notes_what_it_always_noted(monkeypatch) -> None:
    """Core Lean declines a true division, a ``log`` and a ``sqrt``: no reading to part from.

    So out of Mathlib mode a statement with one records what it recorded before
    Mathlib mode existed, and the mode is read from the variable, as the
    oracle reads it.
    """
    both = Forall(((n, Nat), (x, Real)), n // n + x / x == 2)
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    assert notes(divided_back.term) == ()
    assert notes(_sqrt_of_negative.term) == ()
    assert notes(both) == (DIVISION_BY_ZERO,)
    assert notes(both, mathlib=False) == (DIVISION_BY_ZERO,)
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", "/nowhere")
    assert notes(both) == (DIVISION_BY_ZERO, TRUE_DIVISION_BY_ZERO)
    assert notes(_sqrt_of_negative.term) == (OUTSIDE_THE_DOMAIN,)


# }}}


# {{{ the oracle, with Lean and Mathlib


def _without_mathlib(reason: str) -> NoReturn:
    """Skip a test that needs Mathlib, or fail it where Mathlib was promised."""
    if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


@pytest.fixture(scope="module")
def mathlib_oracle(mathlib_project: str | None) -> Iterator[LeanOracle]:
    """One Mathlib session for the module, or a skip that says why not."""
    if mathlib_project is None:
        _without_mathlib("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        _without_mathlib("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    timeout = float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120"))
    oracle = LeanOracle(session=LeanSession(timeout, mathlib=mathlib_project))
    available, reason = oracle.availability()
    if not available:
        _without_mathlib(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        _without_mathlib(f"the Mathlib session did not open: {oracle.session.error}")
    yield oracle
    oracle.session.close()


def test_the_session_imports_mathlib_and_says_which(mathlib_oracle: LeanOracle) -> None:
    session = mathlib_oracle.session
    assert session.version == "v4.29.1"
    assert session.mathlib_revision == mathlib_mode.revision(session.mathlib)
    available, reason = mathlib_oracle.availability()
    assert available
    assert reason == f"Lean v4.29.1 with Mathlib {session.mathlib_revision}"
    closed, detail = session.run("example (x : ℝ) : 0 ≤ x ^ 2 := by positivity\n")
    assert closed, detail


def test_mathlib_proves_gauss_by_induction_on_its_bound(mathlib_oracle: LeanOracle) -> None:
    """The row the README shows as ``tested`` is ``proved`` with Mathlib."""
    proved = mathlib_oracle.establish(gauss.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert proved.provenance["tactic"].startswith("obtain ⟨n, rfl⟩")
    assert proved.provenance["lean_source"].startswith("import Mathlib\n\ntheorem Lanky.gauss")
    assert proved.provenance["lean_mathlib"] == mathlib_oracle.session.mathlib_revision
    assert mathlib_oracle.establish(squares.fact()).status is Status.PROVED


@pytest.mark.parametrize(
    "claim",
    [exp_add, exp_positive, complex_exp_add, binomial, divided_back, _sqrt_of_negative],
    ids=lambda claim: claim.__name__,
)
def test_mathlib_proves_real_and_complex_claims(mathlib_oracle: LeanOracle, claim) -> None:
    proved = mathlib_oracle.establish(claim.fact())
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")


def test_mathlib_mode_still_proves_what_core_lean_proves(mathlib_oracle: LeanOracle) -> None:
    proved = mathlib_oracle.establish(commutes.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "omega"
    proved = mathlib_oracle.establish(scan_monotone.fact())
    assert proved.status is Status.PROVED
    assert "induction" in proved.provenance["tactic"]


@pytest.mark.parametrize(
    ("owner", "term"),
    [
        ("mul_comm", Forall(((x, Real), (y, Real)), x * y == y * x)),
        ("sq_nonneg", Forall(((x, Real),), x**2 >= 0)),
        ("two_mul", Forall(((n, Nat),), 2 * n == n + n)),
    ],
    ids=["mul_comm", "sq_nonneg", "two_mul"],
)
def test_a_claim_named_after_a_mathlib_lemma_is_proved(
    mathlib_oracle: LeanOracle, owner: str, term: object
) -> None:
    """Mathlib has ``mul_comm`` at the root, and a claim of that name was never proved.

    Every attempt was refused with "`mul_comm` has already been declared",
    whatever its tactic; in the ``Lanky`` namespace the name is free.
    """
    fact = Fact(id=owner, kind="theorem", statement=owner, term=term, owner=owner)
    proved = mathlib_oracle.establish(fact)
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    assert f"\ntheorem Lanky.{owner} " in proved.provenance["lean_source"]


def test_a_claim_over_words_mathlib_reserves_is_proved(mathlib_oracle: LeanOracle) -> None:
    """#38 in Mathlib mode: Mathlib reserves words core Lean does not.

    A claim named ``lemma`` over variables named ``to`` and ``over``, three
    words Mathlib's parser takes as keywords, did not parse in the Mathlib
    dialect, and every attempt failed on it.
    """
    to, over = Var("to"), Var("over")
    term = Forall(((to, Real), (over, Real)), to * over == over * to)
    fact = Fact(id="lemma", kind="theorem", statement="lemma", term=term, owner="lemma")
    proved = mathlib_oracle.establish(fact)
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    assert "\ntheorem Lanky.«lemma» («to» : ℝ) («over» : ℝ) : " in proved.provenance["lean_source"]


_REAL, _COMPLEX, _FINSET, _RFL = Var("Real"), Var("Complex"), Var("Finset"), Var("rfl")


@pytest.mark.parametrize(
    ("owner", "term", "tactic"),
    [
        ("exp_named_Real", Forall(((_REAL, Real),), exp(_REAL) > 0), None),
        (
            "exp_add_named_Real",
            Forall(((_REAL, Real), (y, Real)), exp(_REAL + y) == exp(_REAL) * exp(y)),
            None,
        ),
        (
            "named_Complex",
            Forall(((_COMPLEX, Complex),), _COMPLEX + complex(0, 1) == complex(0, 1) + _COMPLEX),
            None,
        ),
        (
            "log_named_Complex",
            Forall(
                ((_COMPLEX, Real),),
                exp(log(_COMPLEX + complex(0, 1))) == _COMPLEX + complex(0, 1),
            ),
            None,
        ),
        (
            "gauss_named_rfl",
            Forall(((_RFL, Nat),), 2 * Sum(((i, FinType(_RFL + 1)),), i) == _RFL * (_RFL + 1)),
            "obtain ⟨x, rfl⟩ := Int.eq_ofNat_of_zero_le h0\ninduction x with",
        ),
        (
            "gauss_named_Finset",
            Forall(
                ((_FINSET, Nat),),
                2 * Sum(((i, FinType(_FINSET + 1)),), i) == _FINSET * (_FINSET + 1),
            ),
            "obtain ⟨Finset, rfl⟩ := Int.eq_ofNat_of_zero_le h0",
        ),
    ],
    ids=[
        "exp_named_Real",
        "exp_add_named_Real",
        "named_Complex",
        "log_named_Complex",
        "gauss_rfl",
        "gauss_Finset",
    ],
)
def test_names_lean_gives_a_meaning_to_are_kept_apart_in_mathlib(
    mathlib_oracle: LeanOracle, owner: str, term: object, tactic: str | None
) -> None:
    """#43 in Mathlib mode: a variable named ``Real``, ``Complex``, ``Finset`` or ``rfl``.

    After a binder named ``Real``, ``Real.exp`` and the lemma ``Real.exp_add``
    are fields of the variable, and so are ``Complex.I`` and ``Finset.Ico``
    and the lemmas the sum's peel names after one named so; they are named
    from the root, and so are ``Complex.re`` and ``Complex.im`` in the claim
    that a complex logarithm's argument is off the cut (#59). A parameter
    named ``rfl`` that the reduction's induction trades for a natural is
    traded under a fresh name, since the ``rcases`` pattern ``⟨rfl, rfl⟩``
    substitutes twice.
    """
    fact = Fact(id=owner, kind="theorem", statement=owner, term=term, owner=owner)
    proved = mathlib_oracle.establish(fact)
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    if tactic is not None:
        assert proved.provenance["tactic"].startswith(tactic), proved.provenance["tactic"]


#: Lean source that prints every token of the parser's table, one to a line.
_PRINT_TOKENS = """\
open Lean Parser in
#eval show CoreM Unit from do
  for token in (getTokenTable (← getEnv)).findPrefix "" do
    IO.println token
"""


def test_every_word_mathlib_reserves_is_quoted(mathlib_oracle: LeanOracle) -> None:
    """The keyword list has Mathlib's words too, read from the Mathlib this suite runs against."""
    import re

    from lean_interact import Command

    session = mathlib_oracle.session
    response = session.server.run(
        Command(cmd=_PRINT_TOKENS, env=session.environment), timeout=session.timeout
    )
    printed = "\n".join(
        str(item.data)
        for item in response.messages
        if str(getattr(item, "severity", "")).endswith("info")
    )
    reserved = {word for word in printed.split() if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", word)}
    assert {"fun", "lemma", "to", "over"} <= reserved
    assert sorted(word for word in reserved if not lean_identifier(word).startswith("«")) == []


def test_a_false_real_claim_is_not_proved_and_not_refuted(mathlib_oracle: LeanOracle) -> None:
    result = mathlib_oracle.establish(_not_a_theorem.fact())
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_tried"] == len(BASE_TACTICS) + len(MATHLIB_TACTICS)


def test_every_printed_statement_elaborates(mathlib_oracle: LeanOracle) -> None:
    """Lean reading each printed proposition as a ``Prop`` is the printer's type check."""
    terms = [
        gauss.term,
        squares.term,
        exp_add.term,
        complex_exp_add.term,
        divided_back.term,
        _sqrt_of_negative.term,
        Forall(((x, Real), (n, Nat)), x + n // 2 <= x + n),
        Forall(((z, Complex),), Abs(z * complex(1.5, -2)) >= 0),
        Forall(((n, Nat),), Sum(((i, FinType(n)),), i**2, i % 2 == 0) >= 0),
        Forall(((n, Nat), (x, Real)), Sum(((i, Refined(FinType(n), (i > 2,))),), x * i) >= 0),
        Forall(((x, Real),), Abs(Abs(x) - 1) + 0.1 >= 0),
        Forall(((n, Nat),), log(n + 1) >= 0),
        Forall(((z, Complex),), log(Abs(z) + 1) >= 0),
        Forall(((z, Complex),), log(Abs(z)) <= Abs(z)),
        _LITERAL_BOUND,
        _NUMERAL_BODY,
        Forall(((n, Nat),), Sum(((i, FinType(n)),), -2) <= 0),
        _CLOSED_ABS,
        _CLOSED_BODY,
        exp_log_off_the_cut.term,
        root_squared.term,
        _ACROSS_THE_CUT,
        Forall(((z, Complex),), Abs(log(z + 2)) + Abs(sqrt(z)) >= 0),
        Forall(((n, Nat),), Sum(((i, FinType(n)),), log(i + 1j), i % 2 == 0) == 0),
    ]
    for term in terms:
        source = f"example : Prop := {print_lean(term, mathlib=True)}\n"
        closed, detail = mathlib_oracle.session.run(source)
        assert closed, (source, detail)
        # and so does every claim that a complex argument is off the cut (#59)
        for condition in statement_of(term, "t", mathlib=True).side_conditions:
            source = f"example : Prop := {condition.proposition}\n"
            closed, detail = mathlib_oracle.session.run(source)
            assert closed, (source, detail)


def test_floor_division_next_to_a_real_is_integer_division(mathlib_oracle: LeanOracle) -> None:
    """``x + (2 * n + 1) // 2 == x + n`` is true in Python and false read in ``ℝ``.

    Printed without its ascription the floor division would be real division
    of the cast ``2 * n + 1``, which is ``n + 1/2``. The script pinned here
    proves the Python statement by rewriting the integer quotient, which it
    can only find if the print kept it an integer.
    """
    halved = Forall(((x, Real), (n, Nat)), x + (2 * n + 1) // 2 == x + n)
    fact = Fact(id="halved", kind="theorem", statement="halved", term=halved)
    mathlib_oracle.tactics[fact.id] = "have h : (2 * n + 1) / 2 = n := by omega\nrw [h]"
    try:
        proved = mathlib_oracle.establish(fact)
    finally:
        mathlib_oracle.tactics.clear()
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    assert "x + ((2 * n + 1) / 2 : ℤ) = x + n" in proved.provenance["lean_source"]


def test_a_sum_python_refutes_is_not_proved(mathlib_oracle: LeanOracle) -> None:
    """Read over ``Nat``, all four were theorems: ``decide`` and ``omega`` proved the first two."""
    for label, term in (
        ("literal_bound", _LITERAL_BOUND),
        ("numeral_body", _NUMERAL_BODY),
        ("closed_abs", _CLOSED_ABS),
        ("closed_body", _CLOSED_BODY),
    ):
        fact = Fact(id=label, kind="theorem", statement=label, term=term)
        result = mathlib_oracle.establish(fact)
        assert result.status is Status.ASSUMED, (label, result.provenance.get("tactic"))
    # and what Python computes is what Lean proves, read over the integers
    for label, term in (
        ("literal_bound_true", Sum(((i, FinType(3)),), i - 1) == 0),
        ("numeral_body_true", Forall(((n, Nat),), Sum(((i, FinType(n)),), 1) == n)),
        ("closed_abs_true", prim.Comparison(Abs(prim.Sum((1, -2))), "==", 1)),
        ("closed_body_true", prim.Comparison(Sum(((i, FinType(3)),), prim.Sum((1, -2))), "==", -3)),
    ):
        fact = Fact(id=label, kind="theorem", statement=label, term=term)
        proved = mathlib_oracle.establish(fact)
        assert proved.status is Status.PROVED, (label, proved.provenance.get("lean_reason"))


def test_mathlib_does_not_prove_a_statement_about_its_own_round(
    mathlib_oracle: LeanOracle,
) -> None:
    """#64: ``round(0.5) == 1`` read ``proved lean``, about Mathlib's ``round``.

    The theorem written with Python's ``round`` is ``0 == 1`` now (#63), and
    the free name, which only a term built by hand still holds, is declined.
    """
    fact = Fact(id="free:round", kind="theorem", statement="round(0.5) == 1", term=_FREE_ROUND)
    declined = mathlib_oracle.establish(fact)
    assert declined.status is Status.ASSUMED
    assert "mentions round" in declined.provenance["declined"]


def test_a_killed_server_is_started_again_with_mathlib(mathlib_oracle: LeanOracle) -> None:
    """The REPL driver kills a server whose command ran past its timeout.

    The next command starts it again and imports Mathlib first, so a slow
    attempt costs that attempt and not every one after it.
    """
    session = mathlib_oracle.session
    session.server.kill()
    closed, detail = session.run("example (x : ℝ) : Real.exp x > 0 := by positivity\n")
    assert closed, detail


def test_mathlib_shows_real_hypotheses_inconsistent(
    mathlib_project: str | None, mathlib_oracle: LeanOracle, monkeypatch
) -> None:
    """Vacuity is asked of the strongest oracle, and Mathlib's ``linarith`` answers it."""
    from lanky.check import establish

    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    fact = establish(_contradictory.fact())
    assert fact.provenance.get("vacuous"), fact.provenance
    assert fact.provenance["vacuous_by"] == "lean"


def test_a_ring_identity_needs_mathlib(
    mathlib_project: str | None, mathlib_oracle: LeanOracle, monkeypatch
) -> None:
    """``(x + y) ** 2`` expanded is tested in core mode and proved in Mathlib mode."""
    from lanky.check import establish

    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    core = establish(binomial.fact())
    assert (core.status, core.decided_by) == (Status.TESTED, "property-test")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    proved = establish(binomial.fact())
    assert (proved.status, proved.decided_by) == (Status.PROVED, "lean")
    assert proved.provenance["lean_source"].startswith("import Mathlib\n")


def test_the_quickstarts_mathlib_ledger_is_the_one_check_prints(
    mathlib_project: str | None, mathlib_oracle: LeanOracle, monkeypatch, capsys
) -> None:
    """``lanky check examples/gauss.py`` in Mathlib mode proves both rows, as documented."""
    from lanky import cli

    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    assert cli.main(["check", str(ROOT / "examples" / "gauss.py")]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    lines = (ROOT / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    command = "$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/gauss.py"
    at = lines.index(command)
    shown = []
    for line in lines[at + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line.rstrip())
    assert shown == printed
    assert [line.split()[:2] for line in printed[2:4]] == [["proved", "lean"]] * 2


def test_mathlibs_principal_branches_are_pythons_off_the_cut(
    mathlib_oracle: LeanOracle,
) -> None:
    """The conventions the printer relies on, read off the pinned Mathlib (#59).

    ``Complex.log z`` is ``Real.log ‖z‖ + arg z * I``, with the argument in
    ``(-π, π]``, and ``Complex.sqrt z`` is ``z ^ (2⁻¹ : ℂ)``, which away from
    zero is ``exp (log z * 2⁻¹)``, the root of half the argument: ``cmath``'s
    principal branches. On the cut Lean takes the side of ``π``, which
    ``cmath`` takes for a positive zero imaginary part and not for a negative
    one, and its logarithm of zero is ``0``, where ``cmath`` has none.
    """
    source = (
        "example (z : ℂ) : Complex.log z = Real.log ‖z‖ + Complex.arg z * Complex.I := rfl\n"
        "example (z : ℂ) : Complex.arg z ∈ Set.Ioc (-Real.pi) Real.pi := Complex.arg_mem_Ioc z\n"
        "example (z : ℂ) : Complex.sqrt z = z ^ (2⁻¹ : ℂ) := rfl\n"
        "example (z : ℂ) (h : z ≠ 0) : z ^ (2⁻¹ : ℂ) = Complex.exp (Complex.log z * 2⁻¹) :=\n"
        "  Complex.cpow_def_of_ne_zero h _\n"
        "example : Complex.log (-1) = Real.pi * Complex.I := Complex.log_neg_one\n"
        "example : Complex.sqrt (-1) = Complex.I := Complex.sqrt_neg_one\n"
        "example : Complex.log 0 = 0 := Complex.log_zero\n"
    )
    closed, detail = mathlib_oracle.session.run(source)
    assert closed, detail
    assert cmath.log(complex(-1, 0.0)) == pytest.approx(math.pi * 1j)
    assert cmath.log(complex(-1, -0.0)) == pytest.approx(-math.pi * 1j)
    assert cmath.sqrt(complex(-1, -0.0)) == pytest.approx(-1j)


@pytest.mark.parametrize(
    "claim",
    [exp_log_off_the_cut, root_squared, exp_log_above_the_axis, exp_log_of_a_positive],
    ids=lambda claim: claim.__name__,
)
def test_mathlib_proves_a_complex_logarithm_or_root_off_the_cut(
    mathlib_oracle: LeanOracle, claim
) -> None:
    """Printed, and proved once the claim that its argument is off the cut is (#59).

    The file that replays the proof proves that claim first, under a name of
    its own, and the provenance lists it. The last two need the ladder's
    ``simp`` with a discharger: ``Complex.exp_log`` wants the argument
    nonzero, which takes the hypothesis ``y > 0``, or ``positivity``.
    """
    owner = claim.__name__
    fact = Fact(id=owner, kind="theorem", statement=owner, term=claim.term, owner=owner)
    proved = mathlib_oracle.establish(fact)
    assert proved.status is Status.PROVED, (
        proved.provenance.get("lean_declined") or proved.provenance.get("lean_reason")
    )
    source = proved.provenance["lean_source"]
    assert source.startswith(f"import Mathlib\n\ntheorem Lanky.{owner}_branch_cut_0 ")
    assert f"\ntheorem Lanky.{owner} " in source
    (condition,) = statement_of(claim.term, owner, mathlib=True).side_conditions
    assert proved.provenance["lean_side_conditions"] == [condition.proposition]
    closed, detail = mathlib_oracle.session.run(source.removeprefix("import Mathlib\n\n"))
    assert closed, detail


def test_a_statement_that_may_reach_the_cut_is_declined(mathlib_oracle: LeanOracle) -> None:
    """Lean cannot keep the argument off the cut, so it does not prove the statement (#59).

    ``_ACROSS_THE_CUT`` is false in Python and true in Lean, whose ``ℂ`` has
    no signed zero; the claim that its argument is off the cut is false at
    every positive ``x``. ``exp(log(z)) == z`` for a nonzero ``z`` is true in
    both readings, and declined all the same: nothing keeps ``z`` off the cut.
    """
    for owner, term in (
        ("across", _ACROSS_THE_CUT),
        ("undone", Forall(((z, Complex),), exp(log(z)) == z, z != 0)),
    ):
        fact = Fact(id=owner, kind="theorem", statement=owner, term=term, owner=owner)
        result = mathlib_oracle.establish(fact)
        assert result.status is Status.ASSUMED
        declined = result.provenance["lean_declined"]
        assert declined.startswith("Lean could not prove ∀ "), declined
        assert "branch cut" in declined
        assert result.provenance["declined"] == f"lean: {declined}"
        assert "lean_tried" not in result.provenance


def test_a_pinned_tactic_does_not_skip_the_side_conditions(mathlib_oracle: LeanOracle) -> None:
    """A per-fact tactic proves the statement only after its side conditions (#59).

    ``simp`` proves ``_ACROSS_THE_CUT`` as printed, both sides being one
    ``Complex.log`` in Lean; pinned to the fact, it is still never tried,
    because the claim that the argument is off the cut fails first.
    """
    statement = statement_of(_ACROSS_THE_CUT, "across", mathlib=True)
    closed, detail = mathlib_oracle.session.run(statement.source("simp"))
    assert closed, detail
    oracle = LeanOracle(session=mathlib_oracle.session)
    oracle.tactics["across"] = "simp"
    fact = Fact(id="across", kind="theorem", statement="across", term=_ACROSS_THE_CUT)
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_declined"].startswith("Lean could not prove ∀ ")


def test_hypotheses_on_the_cut_are_not_shown_inconsistent(mathlib_oracle: LeanOracle) -> None:
    """The vacuity questions carry the side conditions of the guards they ask about (#59).

    ``log(x * complex(-1, -0.0)) != log(x * complex(-1, 0.0))`` holds at every
    positive ``x`` in Python, and is false in Lean, where both sides are one
    ``Complex.log``: ``simp_all`` shows hypotheses with it in them
    inconsistent, and a goal's guard with it in it empty, which would make
    the claim vacuous and fail the check. Neither question is answered.
    """
    unequal = log(x * complex(-1, -0.0)) != log(x * complex(-1, 0.0))
    on_the_cut = log(y * complex(-1, -0.0)) != log(y * complex(-1, 0.0))
    claims = (
        (Forall(((x, Real),), x == 7, (x > 0) & unequal), hypotheses_fact),
        (Forall(((x, Real),), Forall(((y, Real),), y == x, on_the_cut), x > 0), goal_guard_fact),
    )
    for term, question in claims:
        fact = question(Fact(id="c", kind="theorem", statement="c", term=term, owner="c"))
        statement = statement_of(fact.term, "c", mathlib=True)
        closed, detail = mathlib_oracle.session.run(statement.source("simp_all"))
        assert closed, detail
        result = mathlib_oracle.establish(fact)
        assert result.status is Status.ASSUMED, fact.kind
        assert result.provenance["lean_declined"].startswith("Lean could not prove ∀ ")


# }}}
