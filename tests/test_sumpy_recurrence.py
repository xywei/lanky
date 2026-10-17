"""The sumpy demonstration: one claim about a wrangler's recurrence, tested, decided and proved.

The demonstration checks sumpy's own wrangler, so it needs sumpy, and sumpy is
never a dependency of lanky: every test here skips where it is not
importable. The decided row needs the CAS oracle, and so sympy, which sumpy
brings; the tests that read it ask for the ``cas`` fixture. The proved row
needs Lean with Mathlib, and its test skips without a Mathlib project, as the
tests in ``test_mathlib.py`` do.
"""

from __future__ import annotations

import importlib
import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

from conftest import claims, without_lean_line
from lanky import cli
from lanky.check import check_path
from lanky.ledger import Status
from lanky.plugins import registry

pytest.importorskip("sumpy", reason="the demonstration checks sumpy's own wrangler")

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
DEMO = EXAMPLES / "sumpy_recurrence.py"


@pytest.fixture(autouse=True)
def _examples_on_the_path(monkeypatch):
    """A file may import the demonstration by name, which installs a theory and an oracle.

    Both are undone after each test: the path by ``monkeypatch``, and the
    plugins because the registry's lists are swapped for copies. So the
    module is imported afresh in each test, where it installs them again into
    that test's copies.
    """
    monkeypatch.syspath_prepend(str(EXAMPLES))
    monkeypatch.setattr(registry, "theories", list(registry.theories))
    monkeypatch.setattr(registry, "oracles", list(registry.oracles))
    monkeypatch.delitem(sys.modules, "sumpy_recurrence", raising=False)


@pytest.fixture
def demo():
    """The demonstration, imported by name, with its claim kept out of the registry."""
    with registry.collecting():
        return importlib.import_module("sumpy_recurrence")


def _rows(printed: str, start: str) -> list[list[str]]:
    lines = printed.splitlines()
    first = next(index for index, line in enumerate(lines) if line.startswith(start))
    rows = []
    for line in lines[first + 2 :]:
        if not line.strip():
            break
        rows.append(re.split(r"\s{2,}", line))
    return rows


# {{{ the recurrence, read off the wrangler


def test_the_recurrence_is_read_off_the_wrangler(demo) -> None:
    """13 of the 28 derivatives through order 6 are stored, and ``a >= 2`` is two ``y``'s back."""
    claim = demo.compressed_taylor
    assert len(claim.identifiers) == 28
    assert claim.stored == [mi for mi in claim.identifiers if mi[0] <= 1]
    assert len(claim.stored) == 13
    for index, (a, b) in enumerate(claim.identifiers):
        if a <= 1:
            assert claim.weights[index] == {claim.stored.index((a, b)): 1}
            continue
        # G_xx = -G_yy, applied a // 2 times
        back = (a % 2, b + 2 * (a // 2))
        assert claim.weights[index] == {claim.stored.index(back): (-1) ** (a // 2)}


def test_the_claim_is_one_statement_with_an_equation_per_coefficient(demo) -> None:
    """Over real ``x`` and ``y`` away from the origin, as ``Theorem.term`` would give it."""
    from lanky.prelude import Real
    from lanky.terms import Forall, render

    sampled, symbolic, _every_order, _triangle = demo.compressed_taylor.facts()
    term = symbolic.term
    assert isinstance(term, Forall)
    assert [(var.name, domain) for var, domain in term.binders] == [("x", Real), ("y", Real)]
    assert render(term.guard) == "x**2 + y**2 > 0"
    equations = term.body.children
    assert len(equations) == 28
    assert render(equations[0]) == "log(sqrt(x**2 + y**2)) == log(sqrt(x**2 + y**2))"
    index = demo.compressed_taylor.identifiers.index((2, 0))
    left, right = equations[index].left, equations[index].right
    # a negation, which renders as a unary minus (#69)
    assert render(left).startswith("-((1 - ")
    assert render(right) != render(left)
    assert sampled.owner == symbolic.owner == "compressed_taylor"
    assert sampled.id.endswith(":sampled") and symbolic.id.endswith(":symbolic")


def test_the_formulas_are_sympys_derivatives_as_the_bridge_reads_them(cas, demo) -> None:
    """Each equation is the wrangler's combination of sympy's derivatives, and sympy's derivative.

    The decided row is about the lanky terms ``from_sympy`` built, and the
    tester evaluates those same terms, so a sign lost in translating sympy's
    output would make both rows a claim about another kernel. Read back
    through the bridge, each side is the expression it was made from, up to
    how sympy groups it, which ``cancel``, a normal form for rational
    functions, confirms without asking ``simplify``.
    """
    from lanky.cas import equations

    sympy = cas
    claim = demo.compressed_taylor
    _, symbolic, *_ = claim.facts()
    stored = [claim.derivatives[claim.identifiers.index(mi)] for mi in claim.stored]
    found = equations(symbolic.term)
    assert len(found) == len(claim.identifiers) == 28
    for index, equation in enumerate(found):
        assert sympy.cancel(equation.right - claim.derivatives[index]) == 0
        assert sympy.cancel(equation.left - claim.combination(index, stored)) == 0


def test_the_claim_for_every_order_is_the_recurrence_sumpys_pde_gives(demo) -> None:
    """Laplace's PDE, solved for ``G_xx``: the derivatives with ``a >= 2`` are not stored.

    The term is over two tables, the derivatives ``D`` and the reconstruction
    ``R``: if ``D`` satisfies the PDE at every order, and ``R`` is ``D`` where
    the wrangler stores and follows the recurrence elsewhere, ``R`` is ``D``.
    """
    from lanky.prelude import Fn, Nat, Real
    from lanky.terms import Comparison, Forall, Product, Var, render, structurally_equal

    claim = demo.compressed_taylor
    assert claim.pde == {(2, 0): 1, (0, 2): 1}
    assert claim.leading == (2, 0)
    assert claim.recurrence_text() == "reconstructed(a + 2, b) == -reconstructed(a, b + 2)"
    assert claim.pde_text() == "G_xx + G_yy == 0"
    *_, cited, every_order, _triangle = claim.facts()
    assert every_order.id.endswith(":every-order")
    assert every_order.statement.startswith("every order: reconstructed(a, b) == diff(")
    # it rests on the PDE at every order, the one step taken on Kress's word,
    # which rests on harmonic, proved
    assert every_order.rests_on == (claim.fact_id("every-derivative"),) == (cited.id,)
    assert cited.rests_on == (demo.harmonic.fact_id,)
    term = every_order.term
    table = Fn[Nat, Fn[Nat, Real]]
    assert [(var.name, sort) for var, sort in term.binders] == [("D", table), ("R", table)]
    pde, stored, recurrence = term.guard.children
    assert render(pde) == "forall a in Nat, b in Nat. D(a + 2)(b) + D(a)(b + 2) == 0"
    assert render(stored) == "forall a in Nat, b in Nat where a < 2. R(a)(b) == D(a)(b)"
    # compared as a term, since how a negation is printed is the printer's business
    a, b, reconstructed = Var("a"), Var("b"), Var("R")
    expected = Forall(
        ((a, Nat), (b, Nat)),
        Comparison(reconstructed(a + 2)(b), "==", Product((-1, reconstructed(a)(b + 2)))),
    )
    assert structurally_equal(recurrence, expected)
    assert render(term.body) == "forall a in Nat, b in Nat. R(a)(b) == D(a)(b)"


def test_the_claim_on_the_triangle_is_the_one_a_wrangler_of_order_p_makes(demo) -> None:
    """The corollary of #86 a kernel of order ``p`` cites: the recurrence inside the order alone.

    Over the order ``p`` too, with the stored derivatives and the recurrence
    asked of ``R`` only where the order reaches, and ``R`` is ``D`` on the
    triangle ``a + b <= p``.
    """
    from lanky.prelude import Fn, Nat, Real
    from lanky.terms import render

    claim = demo.compressed_taylor
    *_, triangle = claim.facts()
    assert triangle.id.endswith(":on-the-triangle")
    assert triangle.statement.startswith("every order p: reconstructed(a, b) == diff(")
    assert triangle.statement.endswith(
        "for a + b <= p, by reconstructed(a + 2, b) == -reconstructed(a, b + 2) inside it"
    )
    assert triangle.rests_on == (claim.fact_id("every-derivative"),)
    term = triangle.term
    table = Fn[Nat, Fn[Nat, Real]]
    assert [(var.name, sort) for var, sort in term.binders] == [
        ("p", Nat),
        ("D", table),
        ("R", table),
    ]
    pde, stored, recurrence = term.guard.children
    assert render(pde) == "forall a in Nat, b in Nat. D(a + 2)(b) + D(a)(b + 2) == 0"
    assert render(stored) == (
        "forall a in Nat, b in Nat where a < 2 and a + b <= p. R(a)(b) == D(a)(b)"
    )
    assert render(recurrence.guard) == "a + b + 2 <= p"
    assert render(term.body) == "forall a in Nat, b in Nat where a + b <= p. R(a)(b) == D(a)(b)"


def test_lean_is_left_the_claim_for_every_order_and_not_the_one_through_the_order(demo) -> None:
    """The CAS oracle decides the 28 equations in a second; Lean's row is the one for every order.

    Asked first, Lean spent minutes on the conjunction before the CAS oracle
    decided it (#71), so the demonstration declines it for Lean.
    """
    from lanky.oracles.lean import LeanOracle

    oracles = [oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)]
    assert oracles
    claim = demo.compressed_taylor
    for oracle in oracles:
        assert oracle.declines[claim.fact_id("symbolic")] == demo.FOR_THE_CAS
        assert claim.fact_id("every-order") not in oracle.declines
        assert claim.fact_id("sampled") not in oracle.declines


# }}}


# {{{ the two commands


def test_python_runs_the_demo_and_every_coefficient_agrees() -> None:
    """The table of 28 coefficients, each simplified to 0 and within mpmath's tolerance."""
    run = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, cwd=ROOT, timeout=600
    )
    assert run.returncode == 0, run.stdout + run.stderr
    rows = _rows(run.stdout, "(a, b)")
    assert len(rows) == 28
    first = ["(0, 0)", "(0, 1)", "(1, 0)", "(0, 2)", "(1, 1)", "(2, 0)"]
    assert [row[0] for row in rows[:6]] == first
    assert rows[5][1:2] == ["-(0, 2)"]
    assert all(row[-2:] == ["0", "within 1e-20"] for row in rows)
    assert "Every reconstructed coefficient is the direct derivative" in run.stdout


def test_lanky_check_prints_the_claim_tested_decided_and_assumed_for_every_order(
    cas, capsys
) -> None:
    """One owner, five rows: ``tested`` by mpmath, ``decided (heuristic)`` by the CAS oracle.

    Then the PDE at every order, taken on Kress's word, and the claim for
    every order and its corollary on the triangle of every order, each
    ``assumed under harmonic at every order`` where Lean has no Mathlib to
    state it in. Above them the kernel's harmonicity, a theorem the CAS
    oracle decides without Lean.
    """
    assert cli.main(["check", str(DEMO)]) == 0
    printed = capsys.readouterr().out
    rows = [_cells(line) for line in _whole_rows(printed) if "  compressed_taylor  " in line]
    assert [row[:3] for row in rows] == [
        ["tested", "tested", "mpmath"],
        ["decided (heuristic)", "decided (heuristic)", "cas"],
        ["assumed (axiom)", "assumed", "-"],
        ["assumed under harmonic at every order", "assumed", "-"],
        ["assumed under harmonic at every order", "assumed", "-"],
    ]
    assert "diff(G, x, a + 2, y, b) + diff(G, x, a, y, b + 2) == 0" in " ".join(rows[2])
    assert "every order: reconstructed(a, b) == diff(" in " ".join(rows[3])
    assert "every order p: reconstructed(a, b) == diff(" in " ".join(rows[4])
    theorem_row, reading_row = [
        _cells(line) for line in printed.splitlines() if "  harmonic  " in line
    ]
    assert theorem_row[:3] == ["decided (heuristic)", "tested", "cas"]
    # the theorem's annotations, sympy's Laplacian included, run again at
    # drawn points, compute what its term does (#91)
    assert reading_row[:3] == ["tested", "tested", "python"]
    assert "7 facts: 3 assumed, 2 decided, 2 tested" in printed
    assert re.search(
        r"^CITED compressed_taylor at sumpy_recurrence\.py:\d+: R\. Kress, ", printed, re.M
    )
    assert re.search(r"^NOT CHECKED harmonic at sumpy_recurrence\.py:\d+: its proof", printed, re.M)


def _by_owner() -> tuple:
    """The demonstration's ledger: the theorem, then the claim at points, as formulas, every order.

    Before the claim for every order, the PDE at every order, which it rests
    on; and last the claim on the triangle of every order ``p``.
    """
    harmonic, sampled, symbolic, cited, every_order, triangle = claims(check_path(DEMO))
    assert harmonic.owner == "harmonic"
    assert sampled.owner == symbolic.owner == every_order.owner == "compressed_taylor"
    assert cited.owner == triangle.owner == "compressed_taylor"
    return harmonic, sampled, symbolic, cited, every_order, triangle


def test_without_the_cas_oracle_the_formulas_are_tested_exactly(capsys) -> None:
    """The property tester evaluates the same 28 equations in rational arithmetic."""
    _, sampled, symbolic, *_ = _by_owner()
    assert (sampled.status, sampled.decided_by) == (Status.TESTED, "mpmath")
    assert (symbolic.status, symbolic.decided_by) == (Status.TESTED, "property-test")
    assert symbolic.provenance["valid"] > 0


def test_the_pde_at_every_order_is_cited_and_the_claim_for_every_order_rests_on_it(cas) -> None:
    """The harmonicity a theorem; the step from it to every order an axiom of the claim's own.

    Each of the first two rows checks the reconstruction against the
    derivatives themselves; the proof for every order takes the PDE at every
    order as its hypothesis, which is the harmonicity, differentiated. That
    step is ``assumed`` on Kress's citation, with no term for an oracle, and
    rests on ``harmonic``. Without Mathlib the rows for every order are
    ``assumed``: Lean cannot state them in core, and the tester has no table
    over ``Nat`` to draw.
    """
    from lanky.ledger import Ledger

    harmonic, sampled, symbolic, cited, every_order, triangle = _by_owner()
    assert not harmonic.is_axiom
    assert harmonic.kind == "theorem"
    assert harmonic.statement.startswith("x : Real, y : Real | away: x**2 + y**2 > 0 |- ")
    assert harmonic.statement.endswith(" == 0")
    assert cited.is_axiom
    assert (cited.status, cited.decided_by, cited.term) == (Status.ASSUMED, None, None)
    assert cited.provenance["cite"].startswith("R. Kress, Linear Integral Equations")
    assert cited.provenance["label"] == "harmonic at every order"
    assert cited.statement.endswith(
        "diff(G, x, a + 2, y, b) + diff(G, x, a, y, b + 2) == 0 for every a, b, with "
        "G = log(sqrt(x**2 + y**2)): harmonic differentiated a times in x and b times in y"
    )
    assert cited.rests_on == (harmonic.id,)
    assert sampled.rests_on == symbolic.rests_on == ()
    assert every_order.rests_on == triangle.rests_on == (cited.id,)
    assert every_order.status is triangle.status is Status.ASSUMED
    ledger = Ledger([harmonic, sampled, symbolic, cited, every_order, triangle])
    assert ledger.support(every_order).under == (cited.id,)
    assert ledger.support(triangle).under == (cited.id,)
    assert "under harmonic at every order" in ledger.render()


def test_the_ledger_records_what_each_oracle_did(cas) -> None:
    _, sampled, symbolic, *_ = _by_owner()
    assert sampled.provenance["samples"] == 20
    assert sampled.provenance["digits"] == 30
    assert sampled.provenance["largest_difference"] <= 1e-20
    assert sampled.provenance["tolerance"] == (
        "1e-20, relative to the derivative or to 1, whichever is larger"
    )
    assert (symbolic.status, symbolic.decided_by) == (Status.DECIDED, "cas")
    assert symbolic.provenance["cas_equations"] == 28
    assert symbolic.provenance["trust_class"] == "heuristic"


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


def _cells(line: str) -> list[str]:
    return re.split(r"\s{2,}", line.rstrip())


def _whole_rows(printed: str) -> list[str]:
    """The lines ``lanky check`` printed, each wrapped statement joined back to its row.

    A statement too long for its column goes on under it, indented, and is
    broken only at spaces, so a line that starts with one continues the row
    above it.
    """
    rows: list[str] = []
    for line in printed.splitlines():
        if line.startswith(" ") and rows:
            rows[-1] += " " + line.strip()
        else:
            rows.append(line)
    return rows



def test_the_quickstart_shows_what_python_prints() -> None:
    """The quickstart's run of the demonstration is a real one, line for line."""
    run = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, cwd=ROOT, timeout=600
    )
    assert run.returncode == 0, run.stdout + run.stderr
    printed = [line.rstrip() for line in run.stdout.splitlines()]
    assert printed == _shown("uv run python examples/sumpy_recurrence.py")


def test_the_quickstart_shows_the_ledger_the_demo_prints(cas, capsys) -> None:
    """The quickstart's table for the demonstration is the real one, with the CAS oracle on.

    Every column is sized to what it holds, so the rows are compared cell by cell.
    The ``WITHOUT LEAN`` line a machine without Lean prints under the table
    is left out on both sides.
    """
    shown = without_lean_line(_shown("uv run lanky check examples/sumpy_recurrence.py"))
    assert cli.main(["check", str(DEMO)]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    printed = without_lean_line(printed)
    assert len(shown) == len(printed)
    for doc, real in zip(shown, printed, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)


# }}}


def test_the_tolerance_is_relative_to_the_derivative_or_to_1(demo) -> None:
    """#78: below a derivative of size 1 the tolerance is absolute, and is said to be.

    The difference was always measured against ``max(1, |derivative|)``, and
    the docstrings, the reason of a refutation and the run's last lines
    called it relative. A derivative of ``1e-30`` reconstructed as ``1e-21``
    passes, which is what an absolute floor allows; above ``1`` the same
    difference is relative.
    """
    from fractions import Fraction

    tolerance = demo.compressed_taylor.tolerance
    assert tolerance == Fraction(1, 10**20)
    assert demo.difference(Fraction(1, 10**21), Fraction(1, 10**30)) <= tolerance
    assert demo.difference(Fraction(1, 10**19), Fraction(1, 10**30)) > tolerance
    assert demo.difference(1000 + Fraction(1, 10**18), 1000) == Fraction(1, 10**21)
    assert demo.difference(Fraction(1, 2) + Fraction(1, 10**18), Fraction(1, 2)) == Fraction(
        1, 10**18
    )
    assert demo.TOLERANCE_POLICY == "relative to the derivative or to 1, whichever is larger"
    for name in ("tolerance", "sampled"):
        doc = getattr(demo.Reconstruction, name).__doc__
        assert "absolute" in doc and "relative to the derivative" not in doc.split(".")[0]


# {{{ a wrong recurrence


FLIPPED = '''
from __future__ import annotations

from sumpy_recurrence import log_r, reconstructs


class Flipped:
    """sumpy's wrangler, with the sign of one reconstructed coefficient flipped."""

    def __init__(self, wrangler):
        self.wrangler = wrangler

    def get_full_coefficient_identifiers(self):
        return self.wrangler.get_full_coefficient_identifiers()

    def get_coefficient_identifiers(self):
        return self.wrangler.get_coefficient_identifiers()

    def get_full_kernel_derivatives_from_stored(self, stored, rscale):
        rows = list(self.wrangler.get_full_kernel_derivatives_from_stored(stored, rscale))
        place = [tuple(mi) for mi in self.get_full_coefficient_identifiers()].index((2, 1))
        rows[place] = -rows[place]
        return rows


@reconstructs(log_r, order=4)
def flipped():
    """The 2-D Laplace wrangler through order 4, one sign wrong."""
    from sumpy.expansion import LinearPDEBasedExpansionTermsWrangler
    from sumpy.kernel import LaplaceKernel

    wrangler = LinearPDEBasedExpansionTermsWrangler(
        order=4, dim=2, max_mi=None, knl=LaplaceKernel(2)
    )
    return Flipped(wrangler)
'''


def test_a_wrong_recurrence_is_refuted_on_both_rows(cas, tmp_path, capsys) -> None:
    """mpmath finds the point, sympy declines, and the property tester finds another."""
    path = tmp_path / "flipped.py"
    path.write_text(FLIPPED, encoding="utf-8")
    sampled, symbolic = check_path(path)
    assert (sampled.status, sampled.decided_by) == (Status.REFUTED, "mpmath")
    found = sampled.provenance["counterexample"]
    assert (found["a"], found["b"]) == (2, 1)
    assert (symbolic.status, symbolic.decided_by) == (Status.REFUTED, "property-test")
    assert {"x", "y"} <= set(symbolic.provenance["counterexample"])
    assert symbolic.provenance["declined"].startswith(
        "cas: sympy simplifies the difference of the sides of "
    )
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "the reconstructed coefficient (2, 1) is" in printed


def test_a_weight_off_by_one_part_in_a_quadrillion_is_refuted_on_both_rows(cas, tmp_path) -> None:
    """Neither row is a comparison of floats: a weight of ``-(1 + 10**-15)`` fails both.

    mpmath works at 30 digits, and says how far apart the two sides are, and
    the tester evaluates the formulas exactly; sympy declines first.
    """
    text = FLIPPED.replace(
        "rows[place] = -rows[place]", "rows[place] = rows[place] + rows[place] / 10**15"
    )
    path = tmp_path / "nearly.py"
    path.write_text(text, encoding="utf-8")
    sampled, symbolic = check_path(path)
    assert (sampled.status, sampled.decided_by) == (Status.REFUTED, "mpmath")
    assert sampled.provenance["reason"].endswith(
        "apart, relative to the derivative or to 1, whichever is larger"
    )
    assert 0 < float(sampled.provenance["counterexample"]["difference"]) < 1e-14
    assert (symbolic.status, symbolic.decided_by) == (Status.REFUTED, "property-test")
    assert symbolic.provenance["declined"].startswith("cas: sympy simplifies the difference")


def test_a_wrangler_off_its_pdes_recurrence_makes_no_claim_for_every_order(tmp_path) -> None:
    """With its kernel to read the PDE off, the flipped wrangler still claims only through order 4.

    Its weights at ``(2, 1)`` are not what the PDE's recurrence gives, so the
    claim for every order would be about a recurrence it does not follow;
    the rows at points and as formulas refute it.
    """
    text = FLIPPED.replace(
        "        self.wrangler = wrangler\n",
        "        self.wrangler = wrangler\n        self.knl = wrangler.knl\n",
    )
    path = tmp_path / "flipped_with_kernel.py"
    path.write_text(text, encoding="utf-8")
    facts = check_path(path)
    assert [fact.id.rsplit(":", 1)[-1] for fact in facts] == ["sampled", "symbolic"]
    assert all(fact.status is Status.REFUTED for fact in facts)


def test_a_recurrence_that_reaches_past_the_order_makes_no_claim_for_every_order(demo) -> None:
    """``G_x + G_yy == 0``, solved for ``G_x``, takes ``(2, 0)`` from ``(1, 2)``, past order 2.

    A wrangler through order 2 has nothing there, so what it does at ``(2,
    0)`` and ``(1, 1)`` is not the recurrence, and its weights there are not
    checked against it: no claim for every order. Laplace's PDE, read the same
    way, stays within the order and makes the claim.
    """
    from collections import namedtuple
    from types import SimpleNamespace

    derivative = namedtuple("derivative", ["mi", "vec_idx"])

    def wrangler(pde):
        operator = SimpleNamespace(eqs=[{derivative(mi, 0): c for mi, c in pde.items()}])
        return SimpleNamespace(knl=SimpleNamespace(get_pde_as_diff_op=lambda: operator))

    identifiers = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
    # (1, 0) is minus (0, 2), as the recurrence has it; (2, 0) and (1, 1) are anything
    stored = [(0, 0), (0, 1), (0, 2)]
    weights = [{0: 1}, {2: -1}, {1: 1}, {0: 5}, {1: 7}, {2: 1}]
    found = demo._read_pde(wrangler({(1, 0): 1, (0, 2): 1}), identifiers, stored, weights)
    assert found is None
    stored = [(0, 0), (1, 0), (0, 1), (1, 1), (0, 2)]
    weights = [{0: 1}, {1: 1}, {2: 1}, {4: -1}, {3: 1}, {4: 1}]
    found = demo._read_pde(wrangler({(2, 0): 1, (0, 2): 1}), identifiers, stored, weights)
    assert found == ({(2, 0): 1, (0, 2): 1}, (2, 0))


def test_a_recurrence_that_is_not_linear_is_refused_where_it_is_written(tmp_path) -> None:
    text = FLIPPED.replace("rows[place] = -rows[place]", "rows[place] = rows[place] ** 2")
    path = tmp_path / "squared.py"
    path.write_text(text, encoding="utf-8")
    with pytest.raises(ValueError, match=r"reconstructs \(2, 1\) by .*, which is not linear"):
        check_path(path)


# }}}


# {{{ with Mathlib, the claim for every order is proved


def test_with_mathlib_the_claim_for_every_order_is_proved_under_the_pde_at_every_order(
    cas, mathlib_project, monkeypatch, capsys
) -> None:
    """The ledger #3 asks for: tested, decided by the CAS oracle, proved by Lean for every order.

    Lean proves the claim for every order by induction on ``a``, with the step
    a linear combination of the recurrence, the PDE and the induction
    hypothesis that Python found, under the PDE at every order, the one step
    taken on a citation; the CAS oracle still decides the claim through the
    order, which the demonstration declines for Lean. ``harmonic`` itself is
    proved, by the two steps of its body.
    """
    pytest.importorskip("lean_interact", reason="the Lean oracle needs lean-interact")
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but no project is named")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        pytest.skip("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    harmonic, sampled, symbolic, _cited, every_order, triangle = _by_owner()
    assert (harmonic.status, harmonic.decided_by) == (Status.PROVED, "lean")
    assert (sampled.status, sampled.decided_by) == (Status.TESTED, "mpmath")
    assert (symbolic.status, symbolic.decided_by) == (Status.DECIDED, "cas")
    declined = symbolic.provenance["declined"]
    reasons = declined if isinstance(declined, list | tuple) else [declined]
    assert reasons[0].startswith("lean: the claim through the order checked is the CAS")
    assert (every_order.status, every_order.decided_by) == (Status.PROVED, "lean")
    tactic = every_order.provenance["tactic"]
    assert "induction a using Nat.strong_induction_on with" in tactic
    assert "linear_combination" in tactic
    assert every_order.provenance["lean_mathlib"]
    # the corollary on the triangle, by the same induction, the order's guard
    # read off the claim's own (#86)
    assert (triangle.status, triangle.decided_by) == (Status.PROVED, "lean")
    assert "induction a using Nat.strong_induction_on with" in triangle.provenance["tactic"]
    assert cli.main(["check", str(DEMO)]) == 0
    printed = capsys.readouterr().out
    rows = [line for line in printed.splitlines() if "compressed_taylor" in line]
    assert [re.split(r"\s{2,}", row)[:3] for row in rows] == [
        ["tested", "tested", "mpmath"],
        ["decided (heuristic)", "decided (heuristic)", "cas"],
        ["assumed (axiom)", "assumed", "-"],
        ["proved under harmonic at every order", "assumed", "lean"],
        ["proved under harmonic at every order", "assumed", "lean"],
    ]
    # and harmonic, proved, and its reading of its annotations, tested (#91)
    assert "7 facts: 1 assumed, 1 decided, 3 proved, 2 tested" in printed
    # and that is the table the quickstart shows
    shown = _shown("LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/sumpy_recurrence.py")
    printed_lines = [line.rstrip() for line in printed.splitlines()]
    assert len(shown) == len(printed_lines)
    for doc, real in zip(shown, printed_lines, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)


# }}}
