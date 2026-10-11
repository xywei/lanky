"""The line-Taylor demonstration: sumpy's QBX expansion, decided through an order, proved for all.

It reads sumpy's own expansion, so it needs sumpy, which is never a dependency
of lanky: every test here skips where it is not importable. The decided row
needs the CAS oracle, and so sympy, which sumpy brings; the tests that read it
ask for the ``cas`` fixture. The proved row needs Lean with Mathlib, and its
test skips without a Mathlib project, as the tests in ``test_mathlib.py`` do.
"""

from __future__ import annotations

import importlib
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import claims
from lanky import cli
from lanky.check import check_path
from lanky.ledger import Status
from lanky.plugins import registry

pytest.importorskip("sumpy", reason="the demonstration checks sumpy's own expansion")

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
DEMO = EXAMPLES / "line_taylor.py"


@pytest.fixture(autouse=True)
def _examples_on_the_path(monkeypatch):
    """The demonstration imported by name, its registrations undone after each test."""
    monkeypatch.syspath_prepend(str(EXAMPLES))
    monkeypatch.setattr(registry, "theories", list(registry.theories))
    monkeypatch.setattr(registry, "oracles", list(registry.oracles))
    monkeypatch.delitem(sys.modules, "line_taylor", raising=False)


@pytest.fixture
def demo():
    """The demonstration, imported by name, with its claims kept out of the registry."""
    with registry.collecting():
        return importlib.import_module("line_taylor")


def _cells(line: str) -> list[str]:
    return re.split(r"\s{2,}", line.rstrip())


def _shown(command: str) -> list[str]:
    """The lines the quickstart shows under ``$ command``, up to the end of its block."""
    lines = (ROOT / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    start = lines.index(f"$ {command}")
    shown = []
    for line in lines[start + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line)
    return shown


def _same_table(shown: list[str], printed: list[str]) -> None:
    assert len(shown) == len(printed)
    for doc, real in zip(shown, printed, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)


def test_the_coefficients_are_read_off_sumpys_expansion(demo) -> None:
    """Seven coefficients through order 6; the first is ``log r`` and the second ``Re(b / a)``."""
    import sympy

    coefficients = demo.qbx_expansion.coefficients
    assert len(coefficients) == demo.ORDER + 1 == 7
    a0, a1, b0, b1 = sympy.symbols("a0 a1 b0 b1")
    assert sympy.simplify(coefficients[0] - sympy.log(sympy.sqrt(a0**2 + a1**2))) == 0
    assert sympy.simplify(coefficients[1] - (a0 * b0 + a1 * b1) / (a0**2 + a1**2)) == 0


def test_the_claim_is_one_statement_with_an_equation_per_order(demo) -> None:
    from lanky.prelude import Real
    from lanky.terms import Forall, render

    (fact,) = demo.qbx_expansion.facts()
    term = fact.term
    assert isinstance(term, Forall)
    assert [(var.name, domain) for var, domain in term.binders] == [
        ("a0", Real),
        ("a1", Real),
        ("b0", Real),
        ("b1", Real),
    ]
    assert render(term.guard) == "a0**2 + a1**2 > 0"
    assert len(term.body.children) == 7
    assert fact.statement.endswith("for 1 <= k <= 6")
    assert fact.owner == "qbx_expansion"


def test_lean_is_left_the_claim_for_every_order_and_not_the_one_through_the_order(demo) -> None:
    from lanky.oracles.lean import LeanOracle

    oracles = [oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)]
    assert oracles
    for oracle in oracles:
        assert oracle.declines[demo.qbx_expansion.fact_id()] == demo.FOR_THE_CAS
        assert demo.line_taylor.fact().id not in oracle.declines


def test_python_runs_the_demo_and_the_quickstart_shows_what_it_prints() -> None:
    run = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, cwd=ROOT, timeout=600
    )
    assert run.returncode == 0, run.stdout + run.stderr
    printed = [line.rstrip() for line in run.stdout.splitlines()]
    assert printed == _shown("uv run python examples/line_taylor.py")
    rows = [_cells(line) for line in printed[2:9]]
    assert [row[0] for row in rows] == [str(k) for k in range(7)]
    assert all(row[2] == "0" for row in rows)


def test_without_mathlib_the_claim_for_every_order_rests_on_the_ode(cas, capsys) -> None:
    """The axiom ``assumed`` on its citation, the claim ``assumed under`` it, sumpy's decided."""
    assert cli.main(["check", str(DEMO)]) == 0
    printed = capsys.readouterr().out
    statuses = [_cells(line)[0] for line in printed.splitlines()[2:7]]
    assert statuses == [
        "assumed (axiom)",
        "tested",
        "assumed under line_ode",
        "tested",
        "decided (heuristic)",
    ]
    assert "5 facts: 2 assumed, 1 decided, 2 tested" in printed
    assert re.search(r"^CITED line_ode at line_taylor\.py:\d+: L\. V\. Ahlfors, ", printed, re.M)


def test_without_the_cas_oracle_sumpys_coefficients_are_tested_exactly() -> None:
    by_owner = {fact.owner: fact for fact in claims(check_path(DEMO))}
    fact = by_owner["qbx_expansion"]
    assert (fact.status, fact.decided_by) == (Status.TESTED, "property-test")
    assert fact.provenance["valid"] > 0
    assert by_owner["line_taylor"].rests_on == (by_owner["line_ode"].id,)


def test_a_coefficient_off_by_its_order_is_refuted(cas, demo) -> None:
    """``k`` times the coefficient sumpy computes is not the series': no simplification, refuted."""
    from lanky.oracles.cas import CasOracle
    from lanky.oracles.test import TestOracle

    claim = demo.qbx_expansion
    original = claim.coefficients
    try:
        claim.coefficients = [
            coefficient * max(index, 1) for index, coefficient in enumerate(original)
        ]
        (fact,) = claim.facts()
    finally:
        claim.coefficients = original
    decided = CasOracle().establish(fact)
    assert decided is None or decided.status is not Status.DECIDED
    refuted = TestOracle(samples=40).establish(fact)
    assert refuted.status is Status.REFUTED


def test_with_mathlib_the_claim_for_every_order_is_proved_under_line_ode(
    cas, mathlib_project, monkeypatch, capsys
) -> None:
    """Proved by Lean, two orders at a time, with the step a combination Python found."""
    pytest.importorskip("lean_interact", reason="the Lean oracle needs lean-interact")
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but no project is named")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        pytest.skip("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    by_owner = {fact.owner: fact for fact in claims(check_path(DEMO))}
    every_order = by_owner["line_taylor"]
    assert (every_order.status, every_order.decided_by) == (Status.PROVED, "lean")
    tactic = every_order.provenance["tactic"]
    assert "induction n using Nat.strong_induction_on with" in tactic
    assert "by_cases hbase : n < 2" in tactic
    assert (by_owner["qbx_expansion"].status, by_owner["qbx_expansion"].decided_by) == (
        Status.DECIDED,
        "cas",
    )
    assert cli.main(["check", str(DEMO)]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    _same_table(
        _shown("LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/line_taylor.py"), printed
    )
