"""The sumpy demonstration: one claim about a wrangler's recurrence, tested and decided.

The demonstration checks sumpy's own wrangler, so it needs sumpy, and sumpy is
never a dependency of lanky: every test here skips where it is not
importable. The decided row needs the CAS oracle, and so sympy, which sumpy
brings; the tests that read it ask for the ``cas`` fixture.
"""

from __future__ import annotations

import importlib
import re
import subprocess
import sys
from pathlib import Path

import pytest

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

    sampled, symbolic = demo.compressed_taylor.facts()
    term = symbolic.term
    assert isinstance(term, Forall)
    assert [(var.name, domain) for var, domain in term.binders] == [("x", Real), ("y", Real)]
    assert render(term.guard) == "x**2 + y**2 > 0"
    equations = term.body.children
    assert len(equations) == 28
    assert render(equations[0]) == "log(sqrt(x**2 + y**2)) == log(sqrt(x**2 + y**2))"
    index = demo.compressed_taylor.identifiers.index((2, 0))
    left, right = equations[index].left, equations[index].right
    assert render(left).startswith("-1*")
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
    _, symbolic = claim.facts()
    stored = [claim.derivatives[claim.identifiers.index(mi)] for mi in claim.stored]
    found = equations(symbolic.term)
    assert len(found) == len(claim.identifiers) == 28
    for index, equation in enumerate(found):
        assert sympy.cancel(equation.right - claim.derivatives[index]) == 0
        assert sympy.cancel(equation.left - claim.combination(index, stored)) == 0


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


def test_lanky_check_prints_the_claim_tested_and_decided(cas, capsys) -> None:
    """One owner, two rows: ``tested`` by mpmath, ``decided (heuristic)`` by the CAS oracle.

    Above them the kernel's harmonicity, ``assumed`` on its citation.
    """
    assert cli.main(["check", str(DEMO)]) == 0
    printed = capsys.readouterr().out
    rows = [line for line in printed.splitlines() if "compressed_taylor" in line]
    assert rows[0].startswith("tested               mpmath  sumpy_recurrence.py:")
    assert rows[1].startswith("decided (heuristic)  cas     sumpy_recurrence.py:")
    (axiom_row,) = [line for line in printed.splitlines() if "  harmonic  " in line]
    assert axiom_row.startswith("assumed (axiom)      -       sumpy_recurrence.py:")
    assert "3 facts: 1 assumed, 1 decided, 1 tested" in printed
    assert re.search(r"^CITED harmonic at sumpy_recurrence\.py:\d+: R\. Kress, ", printed, re.M)


def _by_owner() -> tuple:
    """The demonstration's ledger: the axiom, then the claim at points and as formulas."""
    harmonic, sampled, symbolic = check_path(DEMO)
    assert harmonic.owner == "harmonic"
    assert sampled.owner == symbolic.owner == "compressed_taylor"
    return harmonic, sampled, symbolic


def test_without_the_cas_oracle_the_formulas_are_tested_exactly(capsys) -> None:
    """The property tester evaluates the same 28 equations in rational arithmetic."""
    _, sampled, symbolic = _by_owner()
    assert (sampled.status, sampled.decided_by) == (Status.TESTED, "mpmath")
    assert (symbolic.status, symbolic.decided_by) == (Status.TESTED, "property-test")
    assert symbolic.provenance["valid"] > 0


def test_the_harmonicity_is_assumed_on_its_citation_and_nothing_rests_on_it(cas) -> None:
    """Sampled and not refuted; neither row rests on it, since each checks every order directly.

    A proof for every order would rest on it, and that row is not there yet.
    """
    harmonic, sampled, symbolic = _by_owner()
    assert harmonic.is_axiom
    assert (harmonic.status, harmonic.decided_by) == (Status.ASSUMED, None)
    assert harmonic.provenance["cite"].startswith("R. Kress, Linear Integral Equations")
    assert harmonic.statement.startswith("x : Real, y : Real | x**2 + y**2 > 0 |- ")
    assert harmonic.statement.endswith(" == 0")
    assert sampled.rests_on == symbolic.rests_on == ()


def test_the_ledger_records_what_each_oracle_did(cas) -> None:
    _, sampled, symbolic = _by_owner()
    assert sampled.provenance["samples"] == 20
    assert sampled.provenance["digits"] == 30
    assert sampled.provenance["largest_difference"] <= 1e-20
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
    """
    shown = _shown("uv run lanky check examples/sumpy_recurrence.py")
    assert cli.main(["check", str(DEMO)]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    assert len(shown) == len(printed)
    for doc, real in zip(shown, printed, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)


# }}}


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
    assert sampled.provenance["reason"].endswith("apart relative to it")
    assert 0 < float(sampled.provenance["counterexample"]["difference"]) < 1e-14
    assert (symbolic.status, symbolic.decided_by) == (Status.REFUTED, "property-test")
    assert symbolic.provenance["declined"].startswith("cas: sympy simplifies the difference")


def test_a_recurrence_that_is_not_linear_is_refused_where_it_is_written(tmp_path) -> None:
    text = FLIPPED.replace("rows[place] = -rows[place]", "rows[place] = rows[place] ** 2")
    path = tmp_path / "squared.py"
    path.write_text(text, encoding="utf-8")
    with pytest.raises(ValueError, match=r"reconstructs \(2, 1\) by .*, which is not linear"):
        check_path(path)


# }}}
