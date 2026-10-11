"""The sum-factorization demonstration: a tensor-product operator as three one-axis passes.

The program needs numpy only. The ledger's claims are ``tested`` without Lean
and, but for the flattening, ``proved`` with Mathlib; the tests that read the
proved rows skip without a Mathlib project, as those in ``test_mathlib.py``
do.
"""

from __future__ import annotations

import importlib
import os
import re
import subprocess
import sys
from pathlib import Path

import numpy as np
import pytest

from conftest import claims
from lanky import cli
from lanky.check import check_path
from lanky.ledger import Status
from lanky.plugins import registry

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
DEMO = EXAMPLES / "sum_factorization.py"


@pytest.fixture(autouse=True)
def _examples_on_the_path(monkeypatch):
    """The demonstration imported by name, its registrations undone after each test."""
    monkeypatch.syspath_prepend(str(EXAMPLES))
    monkeypatch.setattr(registry, "theories", list(registry.theories))
    monkeypatch.setattr(registry, "oracles", list(registry.oracles))
    monkeypatch.delitem(sys.modules, "sum_factorization", raising=False)


@pytest.fixture
def demo():
    """The demonstration, imported by name, with its claims kept out of the registry."""
    with registry.collecting():
        return importlib.import_module("sum_factorization")


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


def test_python_runs_the_demo_and_the_dense_operator_is_the_passes() -> None:
    """At orders 1 to 7, numpy's ``kron(H, kron(G, F))`` on the flattened field is the passes."""
    run = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, cwd=ROOT, timeout=600
    )
    assert run.returncode == 0, run.stdout + run.stderr
    rows = [line.split() for line in run.stdout.splitlines() if re.match(r"\s+\d\s+\d\s", line)]
    assert [row[:2] for row in rows] == [[str(n - 1), str(n)] for n in range(2, 9)]
    assert all(row[2:4] == ["within", "1e-13"] for row in rows)
    for name in ("sum_factorization", "mixed_product", "flattening"):
        assert f"{name} at n = 3, at every row and column, exact integer matrices: True" in (
            run.stdout
        )


def test_the_claims_are_over_matrices_with_two_indices(demo) -> None:
    """``Fn[Fin[n], Fin[n], Real]`` is a family of families, and ``kron`` is read as its entry."""
    from lanky.prelude import Fin, Fn, Real
    from lanky.terms import Var, render

    n = Var("n")
    assert dict(demo.sum_factorization.variables)["F"] == Fn[Fin[n], Fn[Fin[n], Real]]
    assert demo.sum_factorization.statement.startswith(
        "n : Nat, F : Fn[Fin(n), Fin(n), Real], G : Fn[Fin(n), Fin(n), Real], "
    )
    goal = demo.sum_factorization.goal
    assert render(goal.left).startswith("sum(H[c, r]*G[b, q]*F[a, p]*u[p, q, r] for p in Fin(n)")


def test_a_theorem_takes_arrays_for_its_matrices(demo) -> None:
    """Called natively with numpy arrays, each is read as a table of tables."""
    rng = np.random.default_rng(1)
    F, G, H = (rng.integers(-3, 4, size=(2, 2)) for _ in range(3))
    u = rng.integers(-3, 4, size=(2, 2, 2))
    for a, b, c in np.ndindex(2, 2, 2):
        assert demo.sum_factorization(n=2, F=F, G=G, H=H, u=u, a=a, b=b, c=c).holds


def test_without_lean_every_claim_is_tested() -> None:
    exchange, sum_factorization, mixed_product, flattening = claims(check_path(DEMO))
    for fact in (exchange, sum_factorization, mixed_product, flattening):
        assert (fact.status, fact.decided_by) == (Status.TESTED, "property-test"), fact
        assert fact.provenance["valid"] > 0


def test_lean_is_not_handed_the_flattening(demo) -> None:
    """``i // n**2`` of a size that is a variable is not linear: the printer declines it."""
    from lanky.lean import UnsupportedTerm, statement_of

    with pytest.raises(UnsupportedTerm, match="outside the domain it declares"):
        statement_of(demo.flattening.term, "flattening", mathlib=True)
    statement_of(demo.sum_factorization.term, "sum_factorization", mathlib=True)


def test_the_factors_in_the_wrong_order_are_refuted(tmp_path, demo) -> None:
    """``kron(F, kron(G, H))``, with the first axis fastest, is not the operator: refuted."""
    source = DEMO.read_text(encoding="utf-8").replace(
        "dense(H, G, F, n)(a + n * b + n**2 * c", "dense(F, G, H, n)(a + n * b + n**2 * c"
    )
    assert "dense(F, G, H, n)" in source
    path = tmp_path / "wrong_order.py"
    path.write_text(source, encoding="utf-8")
    by_owner = {fact.owner: fact for fact in claims(check_path(path))}
    assert by_owner["flattening"].status is Status.REFUTED
    assert by_owner["flattening"].provenance["counterexample"]


def test_with_mathlib_the_sums_are_proved_and_the_quickstart_shows_it(
    mathlib_project, monkeypatch, capsys
) -> None:
    """Three claims ``proved`` for every size; the flattening ``tested``."""
    pytest.importorskip("lean_interact", reason="the Lean oracle needs lean-interact")
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but no project is named")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        pytest.skip("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    exchange, sum_factorization, mixed_product, flattening = claims(check_path(DEMO))
    for fact in (exchange, sum_factorization, mixed_product):
        assert (fact.status, fact.decided_by) == (Status.PROVED, "lean"), fact.provenance.get(
            "lean_reason"
        )
        assert "rw [Finset.sum_comm]" in fact.provenance["tactic"]
    assert (flattening.status, flattening.decided_by) == (Status.TESTED, "property-test")
    assert cli.main(["check", str(DEMO)]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    shown = _shown("LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/sum_factorization.py")
    assert len(shown) == len(printed)
    for doc, real in zip(shown, printed, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)
