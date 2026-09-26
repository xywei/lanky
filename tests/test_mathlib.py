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

import json
import math
import os
import random
from collections.abc import Iterator
from fractions import Fraction
from pathlib import Path
from typing import NoReturn

import pytest

from lanky import exp, log, sqrt, theorem
from lanky import mathlib as mathlib_mode
from lanky.lean import (
    UnsupportedTerm,
    domain_guards,
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
# lanky.pytest_plugin). The ones under a private name are not: an identity the
# tester would refute by float rounding, a false one, and two it cannot draw.


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@theorem
def squares(n: Nat) -> 6 * sum(i**2 for i in Fin[n + 1]) == n * (n + 1) * (2 * n + 1):
    """The sum of the first squares."""


@theorem
def _exp_add(x: Real, y: Real) -> exp(x + y) == exp(x) * exp(y):
    """The exponential turns sums into products."""


@theorem
def exp_positive(x: Real) -> exp(x) > 0:
    """The exponential is positive."""


@theorem
def _complex_exp_add(z: Complex, w: Complex) -> exp(z + w) == exp(z) * exp(w):
    """And so does the complex exponential."""


@theorem
def binomial(x: Real.exact, y: Real.exact) -> (x + y) ** 2 == x**2 + 2 * x * y + y**2:
    """A ring identity over the reals."""


@theorem
def _divided_back(x: Real, y: Real, hy: y != 0) -> x / y * y == x:
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
        _exp_add.term,
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
    assert mathlib(log(z) == log(z), z=Complex) == "Complex.log z = Complex.log z"
    # an integer argument is cast where the function is applied, as math.exp(n) casts
    assert mathlib(exp(n) >= 1, n=Nat) == "Real.exp n ≥ 1"
    with pytest.raises(UnsupportedTerm, match="complex square root"):
        print_lean(Forall(((z, Complex),), sqrt(z) == z), mathlib=True)
    with pytest.raises(UnsupportedTerm, match="needs Real.exp"):
        print_lean(exp_positive.term)


def test_complex_numbers_are_not_ordered() -> None:
    assert mathlib(z == w, z=Complex, w=Complex) == "z = w"
    assert mathlib(Abs(z) < 1, z=Complex) == "‖z‖ < 1"
    for term in (z < w, z >= 0, exp(z) > 0):
        with pytest.raises(UnsupportedTerm, match="orders complex numbers"):
            print_lean(Forall(((z, Complex), (w, Complex)), term), mathlib=True)


def test_a_reduction_is_a_finset_sum() -> None:
    """``Fin[n]`` is ``Finset.Ico 0 n`` over ``Int``, so the binder is an integer.

    A sum that is an operand is bracketed, because the body of ``∑`` extends as
    far to the right as it can, and a guard or a refinement filters it with
    ``with``.
    """
    assert print_lean(gauss.term, mathlib=True) == (
        "∀ n : Int, 0 ≤ n → 2 * (∑ i ∈ Finset.Ico 0 (n + 1), i) = n * (n + 1)"
    )
    guarded = Sum(((i, FinType(n)),), i**2, i % 2 == 0)
    assert mathlib(guarded >= 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico 0 n with (i % 2 : ℤ) = 0, i ^ 2) ≥ 0"
    )
    nested = Sum(((i, FinType(n)), (j, FinType(i))), i * j + 1)
    assert mathlib(nested == 0, n=Nat) == (
        "(∑ i ∈ Finset.Ico 0 n, ∑ j ∈ Finset.Ico 0 i, (i * j + 1)) = 0"
    )
    refined = Sum(((i, Refined(FinType(n), (i > 2,))),), x * i)
    assert mathlib(refined >= 0, n=Nat, x=Real) == "(∑ i ∈ Finset.Ico 0 n with i > 2, x * i) ≥ 0"
    with pytest.raises(UnsupportedTerm, match="no finite extent"):
        print_lean(Forall(((n, Nat),), Sum(((i, Nat),), i) >= 0), mathlib=True)


def test_a_mathlib_statement_is_marked_and_arranged_as_a_theorem() -> None:
    statement = statement_of(gauss.term, "gauss", mathlib=True)
    assert statement.mathlib
    assert statement.binders == (("n", "Int"),)
    assert statement.hypotheses == (("h0", "0 ≤ n"),)
    assert statement.goal == "2 * (∑ i ∈ Finset.Ico 0 (n + 1), i) = n * (n + 1)"
    assert gauss.lean(mathlib=True) == print_lean(gauss.term, mathlib=True)
    divided = statement_of(_divided_back.term, "_divided_back", mathlib=True)
    assert divided.binders == (("x", "ℝ"), ("y", "ℝ"))
    assert divided.hypotheses == (("h0", "y ≠ 0"),)
    assert divided.goal == "((x : ℝ) / y) * y = x"
    assert divided.proposition == "∀ x : ℝ, ∀ y : ℝ, y ≠ 0 → ((x : ℝ) / y) * y = x"


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


def test_mathlib_mode_takes_what_core_lean_declines(monkeypatch, tmp_path) -> None:
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(tmp_path))
    oracle = LeanOracle()
    for claim in (gauss, _exp_add, _complex_exp_add, _divided_back, _sqrt_of_negative):
        assert oracle.can_establish(claim.fact()), claim.__name__
    monkeypatch.delenv("LANKY_LEAN_MATHLIB")
    for claim in (gauss, _exp_add, _complex_exp_add, _divided_back, _sqrt_of_negative):
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
    assert Complex.exactness == "approx"
    assert str(Complex) == "Complex"
    assert str(Complex.exact) == "Complex[exact]"
    rng = random.Random(0)
    drawn = [sample_value(Complex, rng, {}) for _ in range(20)]
    assert all(isinstance(value, complex) for value in drawn)
    exact = [sample_value(Complex.exact, rng, {}) for _ in range(20)]
    assert all((4 * v.real).is_integer() and (4 * v.imag).is_integer() for v in exact)
    assert in_sort(1 + 2j, Complex, {})
    assert in_sort(0.5, Complex, {})
    assert not in_sort(True, Complex, {})
    assert not in_sort("1j", Complex, {})


def test_an_exact_complex_identity_is_tested_exactly() -> None:
    @theorem
    def difference_of_squares(z: Complex.exact, w: Complex.exact) -> (z + w) * (z - w) == (
        z * z - w * w
    ):
        """A ring identity, which dyadic parts keep exact in floating point."""

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


def test_the_readings_gaps_over_the_reals_are_noted() -> None:
    assert TRUE_DIVISION_BY_ZERO in notes(_divided_back.term)
    assert notes(Forall(((x, Real),), x / 2 == x * 0.5)) == ()
    assert notes(_sqrt_of_negative.term) == (OUTSIDE_THE_DOMAIN,)
    assert OUTSIDE_THE_DOMAIN in notes(Forall(((x, Real),), log(x * x) == 2 * log(x)))
    assert notes(Forall(((x, Real),), Elementary("log", 2) > 0)) == ()
    assert notes(_exp_add.term) == ()
    # the integer note is the integer one, and the two can stand together
    both = Forall(((n, Nat), (x, Real)), n // n + x / x == 2)
    assert notes(both) == (DIVISION_BY_ZERO, TRUE_DIVISION_BY_ZERO)


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
    assert proved.provenance["lean_source"].startswith("import Mathlib\n\ntheorem gauss")
    assert proved.provenance["lean_mathlib"] == mathlib_oracle.session.mathlib_revision
    assert mathlib_oracle.establish(squares.fact()).status is Status.PROVED


@pytest.mark.parametrize(
    "claim",
    [_exp_add, exp_positive, _complex_exp_add, binomial, _divided_back, _sqrt_of_negative],
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


def test_a_false_real_claim_is_not_proved_and_not_refuted(mathlib_oracle: LeanOracle) -> None:
    result = mathlib_oracle.establish(_not_a_theorem.fact())
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_tried"] == len(BASE_TACTICS) + len(MATHLIB_TACTICS)


def test_every_printed_statement_elaborates(mathlib_oracle: LeanOracle) -> None:
    """Lean reading each printed proposition as a ``Prop`` is the printer's type check."""
    terms = [
        gauss.term,
        squares.term,
        _exp_add.term,
        _complex_exp_add.term,
        _divided_back.term,
        _sqrt_of_negative.term,
        Forall(((x, Real), (n, Nat)), x + n // 2 <= x + n),
        Forall(((z, Complex),), Abs(z * complex(1.5, -2)) >= 0),
        Forall(((n, Nat),), Sum(((i, FinType(n)),), i**2, i % 2 == 0) >= 0),
        Forall(((n, Nat), (x, Real)), Sum(((i, Refined(FinType(n), (i > 2,))),), x * i) >= 0),
        Forall(((x, Real),), Abs(Abs(x) - 1) + 0.1 >= 0),
        Forall(((n, Nat),), log(n + 1) >= 0),
    ]
    for term in terms:
        source = f"example : Prop := {print_lean(term, mathlib=True)}\n"
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


# }}}
