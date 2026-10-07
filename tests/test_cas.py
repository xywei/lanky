"""The CAS oracle and its bridge: identities sympy simplifies to zero, read strictly.

sympy is the ``cas`` extra and not a dependency, so everything here that needs
it asks for the ``cas`` fixture (see ``conftest.py``), which switches the
oracle on for the test and skips where sympy is not installed. What holds
without sympy, that lanky imports without it and says why the oracle is not
there, is tested without the fixture.
"""

from __future__ import annotations

import subprocess
import sys
import threading
import time
from fractions import Fraction

import pytest

from lanky import cli
from lanky.cas import Untranslatable, equations, from_sympy, symbol_for, to_sympy
from lanky.check import check_path
from lanky.ledger import Fact, Status
from lanky.oracles.cas import CasOracle, _deadline
from lanky.plugins import registry
from lanky.prelude import Bool, Complex, Fin, Int, Nat, Real, Sort
from lanky.terms import (
    Comparison,
    Elementary,
    Forall,
    LogicalAnd,
    Quotient,
    Var,
    abs_,
    exp,
    log,
    render,
    sqrt,
    structurally_equal,
)

x, y, z, n = Var("x"), Var("y"), Var("z"), Var("n")


def fact_of(term, owner: str = "claim") -> Fact:
    """A fact with ``term``, as a theory would hand it to the oracles."""
    statement = render(term)
    return Fact(id=f"theorem:{owner}", kind="theorem", statement=statement, term=term, owner=owner)


def write(tmp_path, body: str) -> str:
    """A file of theorems, with the imports every one of them needs."""
    path = tmp_path / "identities.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import abs_, exp, log, sqrt, theorem\n"
        "from lanky.prelude import Complex, Fin, Fn, Nat, Real\n\n" + body,
        encoding="utf-8",
    )
    return str(path)


# {{{ without sympy


def test_lanky_imports_without_importing_sympy() -> None:
    """The oracle is registered with lanky, and sympy is imported on the first fact."""
    code = "import sys, lanky; print('sympy' in sys.modules)"
    run = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True, timeout=120)
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip() == "False"


def test_the_oracle_is_registered_as_a_heuristic() -> None:
    """Between Lean, the kernel, and the property tester, the test."""
    import lanky  # noqa: F401 - registers the built-in oracles

    names = [oracle.name for oracle in registry.sorted_oracles()]
    assert names.index("lean") < names.index("cas") < names.index("property-test")
    (oracle,) = [oracle for oracle in registry.oracles if oracle.name == "cas"]
    assert isinstance(oracle, CasOracle)
    assert oracle.trust_class() == "heuristic"


def test_the_oracle_says_why_it_is_not_there(monkeypatch) -> None:
    """Switched off by the variable, or with no sympy to ask."""
    monkeypatch.setenv("LANKY_CAS_DISABLE", "1")
    assert CasOracle().availability() == (False, "disabled by LANKY_CAS_DISABLE")
    monkeypatch.delenv("LANKY_CAS_DISABLE")
    monkeypatch.setattr("lanky.oracles.cas.find_spec", lambda name: None)
    assert CasOracle().availability() == (
        False,
        "sympy is not installed (pip install lanky[cas])",
    )


def test_a_check_without_the_oracle_reads_as_it_did(tmp_path, monkeypatch) -> None:
    """With the oracle off, an identity sympy decides is the property tester's, as before."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = write(tmp_path, "@theorem\ndef double(x: Real) -> x + x == 2 * x:\n    pass\n")
    (fact,) = check_path(path)
    assert (fact.status, fact.decided_by) == (Status.TESTED, "property-test")
    assert "declined" not in fact.provenance


# }}}


# {{{ lanky to sympy


def test_each_sort_is_a_symbol_with_what_it_grants(cas) -> None:
    """A real symbol for ``Real``, and integers that are not negative for ``Nat`` and ``Fin``.

    A refinement is read as its sort, and the exactness class changes nothing.
    """
    assert symbol_for("x", Real).is_real is True
    assert symbol_for("x", Real.exact).is_real is True
    assert symbol_for("z", Complex).is_real is None
    assert symbol_for("k", Int).is_integer is True
    assert symbol_for("k", Int).is_nonnegative is None
    for domain in (Nat, Fin[n], Nat & (n > 2)):
        symbol = symbol_for("k", domain)
        assert (symbol.is_integer, symbol.is_nonnegative) == (True, True)


@pytest.mark.parametrize("domain", [Bool, Sort("Operator"), "C2Boundary"])
def test_a_sort_that_is_not_a_set_of_numbers_is_refused(cas, domain) -> None:
    """An operator need not commute, so a simplifier may not treat it as a number."""
    with pytest.raises(Untranslatable, match="not a set of numbers"):
        symbol_for("s", domain)


def test_numbers_cross_exactly(cas) -> None:
    """A float is the rational it holds, as the tester and the Lean printer read it."""
    sympy = cas
    assert to_sympy(3, {}) == sympy.Integer(3)
    assert to_sympy(Fraction(-2, 6), {}) == sympy.Rational(-1, 3)
    assert to_sympy(0.1, {}) == sympy.Rational(3602879701896397, 36028797018963968)
    assert to_sympy(1j, {}) == sympy.I
    assert to_sympy(0.5 - 2j, {}) == sympy.Rational(1, 2) - 2 * sympy.I
    for value in (True, float("inf"), float("nan"), "1", None):
        with pytest.raises(Untranslatable):
            to_sympy(value, {})


def test_arithmetic_and_the_elementary_functions_cross(cas) -> None:
    sympy = cas
    sx = symbol_for("x", Real)
    term = abs_(x) + exp(x) * log(x) / sqrt(x) - x**3
    assert to_sympy(term, {"x": sx}) == (
        sympy.Abs(sx) + sympy.exp(sx) * sympy.log(sx) / sympy.sqrt(sx) - sx**3
    )


@pytest.mark.parametrize(
    ("term", "reason"),
    [
        (x // 2, "floor division"),
        (x % 2, "remainder"),
        (Var("f")(x), "a family applied to an argument"),
        (Var("a")[x], "a subscript"),
        ((x > 1) + 1, "a proposition used as a number"),
        (y + 1, "y is not bound by a quantifier"),
    ],
)
def test_what_the_bridge_does_not_take_is_refused_with_the_reason(cas, term, reason) -> None:
    with pytest.raises(Untranslatable, match=reason):
        to_sympy(term, {"x": symbol_for("x", Real)})


def test_equations_are_read_through_conjunctions_and_universals(cas) -> None:
    """The binders give the symbols, nested ones included, and the guards are not read."""
    term = Forall(
        ((x, Real),),
        LogicalAnd((x + x == 2 * x, Forall(((n, Nat),), x**n == x**n, n > 3))),
        x > 0,
    )
    first, second = equations(term)
    assert first.left.free_symbols == {symbol_for("x", Real)}
    assert {symbol.name for symbol in second.left.free_symbols} == {"x", "n"}
    assert structurally_equal(second.term, x**n == x**n)


@pytest.mark.parametrize(
    "term",
    [
        Forall(((x, Real),), x <= x + 1),
        Forall(((x, Real),), x != x + 1),
        Forall(((x, Real),), (x == 1) | (x == 2)),
        Forall(((x, Real),), ~(x == 1)),
        LogicalAnd(()),
    ],
)
def test_a_statement_that_asserts_no_equation_is_refused(cas, term) -> None:
    with pytest.raises(Untranslatable):
        equations(term)


# }}}


# {{{ sympy to lanky


def test_a_sympy_expression_becomes_lanky_terms(cas) -> None:
    """Rationals as fractions, negative powers as quotients, half powers as square roots."""
    sympy = cas
    sx, sy = sympy.symbols("x y", real=True)
    assert from_sympy(sympy.Rational(3, 4)) == Fraction(3, 4)
    assert from_sympy(sympy.Integer(5)) == 5
    assert from_sympy(sympy.I) == 1j
    assert structurally_equal(from_sympy(sympy.E), Elementary("exp", 1))
    assert structurally_equal(from_sympy(sympy.sqrt(sx)), Elementary("sqrt", x))
    assert structurally_equal(from_sympy(1 / sympy.sqrt(sx)), Quotient(1, Elementary("sqrt", x)))
    assert structurally_equal(from_sympy(sx ** sympy.Rational(3, 2)), Elementary("sqrt", x) ** 3)
    term = from_sympy(-2 * sx / (sx**2 + sy**2))
    assert isinstance(term, Quotient)
    assert render(term) == "-2*x / (x**2 + y**2)"
    assert render(from_sympy(sx - 2 * sy - sx * sy / 3)) == "x - 2*y - 1/3*x*y"
    assert structurally_equal(from_sympy(sympy.Eq(sx, sy)), Comparison(x, "==", y))
    named = Var("x")
    assert from_sympy(sx, {"x": named}) is named


@pytest.mark.parametrize("expression", ["pi", "Float(0.1)", "sin(x)", "oo", "zoo"])
def test_what_has_no_lanky_counterpart_is_refused(cas, expression) -> None:
    sympy = cas
    with pytest.raises(Untranslatable):
        from_sympy(sympy.sympify(expression, locals={"x": sympy.Symbol("x")}))


def test_a_round_trip_keeps_the_expression(cas) -> None:
    """sympy to lanky and back is the same sympy expression, up to sympy's own normal form."""
    sympy = cas
    sx, sy = sympy.symbols("x y", real=True)
    symbols = {"x": sx, "y": sy}
    for expression in (
        (sx**2 - sy**2) / (sx**2 + sy**2) ** 3,
        sympy.log(sympy.sqrt(sx**2 + sy**2)),
        sympy.exp(-sx) * sympy.Abs(sy) - sympy.Rational(1, 3) * sympy.I,
        24 * sx * sy * (sx - sy) * (sx + sy) / (sx**2 + sy**2) ** 4,
    ):
        assert sympy.simplify(to_sympy(from_sympy(expression), symbols) - expression) == 0
        assert to_sympy(from_sympy(expression), symbols) == expression


# }}}


# {{{ the oracle


def test_an_identity_sympy_simplifies_to_zero_is_decided(cas) -> None:
    """``decided``, by ``cas``, with how many equations and which sympy."""
    oracle = CasOracle()
    term = Forall(((x, Real), (y, Real)), exp(x + y) == exp(x) * exp(y))
    fact = fact_of(term)
    assert oracle.can_establish(fact)
    result = oracle.establish(fact)
    assert (result.status, result.decided_by) == (Status.DECIDED, "cas")
    assert result.provenance["cas_equations"] == 1
    assert result.provenance["cas_version"] == f"sympy {cas.__version__}"


def test_a_difference_left_over_is_a_decline_and_not_a_refutation(cas) -> None:
    """sympy may not see an identity, so what it leaves is no counterexample."""
    oracle = CasOracle()
    fact = fact_of(Forall(((x, Real),), x + 1 == x))
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.provenance["declined"] == (
        "cas: sympy simplifies the difference of the sides of x + 1 == x to 1, not 0"
    )


def test_a_conjunction_is_decided_equation_by_equation(cas) -> None:
    oracle = CasOracle()
    good = Forall(((x, Real),), LogicalAnd((x + x == 2 * x, x * x == x**2)))
    assert oracle.establish(fact_of(good)).provenance["cas_equations"] == 2
    bad = Forall(((x, Real),), LogicalAnd((x + x == 2 * x, x * x == 2 * x)))
    declined = oracle.establish(fact_of(bad)).provenance["declined"]
    assert "x*x == 2*x" in declined
    assert "to x**2 - 2*x, not 0" in declined or "to x*(x - 2), not 0" in declined


def test_a_variable_is_read_with_its_sort(cas) -> None:
    """``sqrt(x**2)`` is ``abs(x)`` for a real ``x`` and a natural, and not for a complex one."""
    oracle = CasOracle()
    real = oracle.establish(fact_of(Forall(((x, Real),), sqrt(x**2) == abs_(x))))
    assert real.status is Status.DECIDED
    natural = oracle.establish(fact_of(Forall(((n, Nat),), sqrt(n**2) == n)))
    assert natural.status is Status.DECIDED
    complex_ = oracle.establish(fact_of(Forall(((z, Complex),), sqrt(z**2) == abs_(z))))
    assert complex_.status is Status.ASSUMED
    assert complex_.provenance["declined"].startswith("cas: sympy simplifies the difference")


def test_the_hypotheses_are_not_read(cas) -> None:
    """``sqrt(x**2) == x`` holds where ``x > 0``, and is declined: an identity is asked for."""
    oracle = CasOracle()
    fact = fact_of(Forall(((x, Real),), sqrt(x**2) == x, x > 0))
    assert oracle.establish(fact).status is Status.ASSUMED


def test_what_the_bridge_refuses_is_not_taken(cas) -> None:
    """Not taken at all, so nothing is recorded: the fact is left to the weaker oracles."""
    oracle = CasOracle()
    for term in (
        Forall(((x, Real),), x <= x + 1),
        Forall(((n, Nat),), n // 2 == n // 2),
        Forall(((Var("f"), "Fn"),), Var("f")(x) == Var("f")(x)),
        True,
        None,
    ):
        assert not oracle.can_establish(fact_of(term))


def test_the_deadline_declines_a_simplification_that_runs_long(cas, monkeypatch) -> None:
    """A fact gets its seconds, and is declined when they run out, as a Lean attempt is."""

    def slow(expression):
        time.sleep(30)
        return expression

    monkeypatch.setattr(cas, "simplify", slow)
    started = time.monotonic()
    result = CasOracle(timeout=0.2).establish(fact_of(Forall(((x, Real),), x == x)))
    assert time.monotonic() - started < 10
    assert result.status is Status.ASSUMED
    assert result.provenance["declined"] == "cas: sympy did not finish within 0.2 s"


def test_the_deadline_reads_the_variable(cas, monkeypatch) -> None:
    monkeypatch.setenv("LANKY_CAS_TIMEOUT", "7.5")
    assert CasOracle()._seconds() == 7.5
    assert CasOracle(timeout=3)._seconds() == 3


def test_no_deadline_off_the_main_thread_or_over_another_timer(cas) -> None:
    """The interval timer is the process's: the oracle leaves it alone where it cannot own it."""
    import signal

    found = []

    def run() -> None:
        with _deadline(0.01):
            time.sleep(0.05)
        found.append(CasOracle(timeout=1).establish(fact_of(Forall(((x, Real),), x == x))))

    thread = threading.Thread(target=run)
    thread.start()
    thread.join(30)
    assert found and found[0].status is Status.DECIDED

    signal.setitimer(signal.ITIMER_REAL, 100)
    try:
        with _deadline(0.01):
            time.sleep(0.05)
        assert signal.getitimer(signal.ITIMER_REAL)[0] > 90
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)


def test_a_simplifier_that_raises_declines(cas, monkeypatch) -> None:
    def broken(expression):
        raise RecursionError("too deep")

    monkeypatch.setattr(cas, "simplify", broken)
    result = CasOracle().establish(fact_of(Forall(((x, Real),), x == x)))
    assert result.provenance["declined"] == "cas: sympy raised RecursionError: too deep"


# }}}


# {{{ in a check


def test_a_check_decides_an_identity_and_says_it_is_a_heuristic(
    cas, tmp_path, monkeypatch, capsys
) -> None:
    """The row reads ``decided (heuristic)  cas``, and the property tester still samples it."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = write(
        tmp_path,
        "@theorem\n"
        "def product(x: Real, y: Real) -> exp(x + y) == exp(x) * exp(y):\n"
        "    pass\n\n\n"
        "@theorem\n"
        "def order(x: Real) -> x <= x + 1:\n"
        "    pass\n",
    )
    product, order = check_path(path)
    assert (product.status, product.decided_by) == (Status.DECIDED, "cas")
    assert product.provenance["trust_class"] == "heuristic"
    assert (order.status, order.decided_by) == (Status.TESTED, "property-test")
    assert "declined" not in order.provenance
    assert cli.main(["check", path, "--verbose"]) == 0
    printed = capsys.readouterr().out
    assert f"cas (heuristic): available (sympy {cas.__version__})" in printed
    rows = [line for line in printed.splitlines() if "product" in line and "|-" in line]
    assert rows[-1].startswith("decided (heuristic)  cas ")


def test_a_check_with_the_oracle_off_says_so(tmp_path, monkeypatch, capsys) -> None:
    monkeypatch.setenv("LANKY_CAS_DISABLE", "1")
    path = write(tmp_path, "@theorem\ndef double(x: Real) -> x + x == 2 * x:\n    pass\n")
    assert cli.main(["check", path, "--verbose"]) == 0
    assert "cas (heuristic): unavailable: disabled by LANKY_CAS_DISABLE" in capsys.readouterr().out


def test_a_counterexample_overrules_a_wrong_simplification(cas, tmp_path, monkeypatch) -> None:
    """A simplifier that took every difference to zero is overruled by the tester's draw."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    monkeypatch.setattr(cas, "simplify", lambda expression: 0)
    path = write(tmp_path, "@theorem\ndef wrong(x: Real) -> x + 1 == x:\n    pass\n")
    (fact,) = check_path(path)
    assert (fact.status, fact.decided_by) == (Status.REFUTED, "property-test")
    assert fact.provenance["overruled"] == "cas, a heuristic, decided it"


def test_a_decline_is_kept_when_the_tester_settles_the_fact(cas, tmp_path, monkeypatch) -> None:
    """``x + 1 == x``: sympy leaves ``1``, and the tester refutes it, with the decline kept."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = write(tmp_path, "@theorem\ndef off_by_one(x: Real) -> x + 1 == x:\n    pass\n")
    (fact,) = check_path(path)
    assert (fact.status, fact.decided_by) == (Status.REFUTED, "property-test")
    assert fact.provenance["declined"] == (
        "cas: sympy simplifies the difference of the sides of x + 1 == x to 1, not 0"
    )


# }}}
