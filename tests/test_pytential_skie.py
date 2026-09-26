"""The pytential demonstration: five representations, a rule engine, and the axioms it reads.

The rule engine and its operator algebra are example code,
``examples/layer_potentials.py``, and everything here but the adapter runs
without pytential. The adapter from pytential's ``sym`` expressions is tested
where pytential imports and skipped elsewhere; pytential is never a lanky
dependency.
"""

from __future__ import annotations

import importlib
import importlib.metadata
import re
import subprocess
import sys
import tomllib
from pathlib import Path

import pymbolic.primitives as prim
import pytest

from lanky import cli
from lanky.check import check_path, import_path
from lanky.ledger import Status
from lanky.plugins import registry

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES = ROOT / "examples"
DEMO = EXAMPLES / "pytential_skie.py"

AXIOMS = [
    "jump_S",
    "jump_D",
    "jump_Sp",
    "jump_Dp",
    "compact_S",
    "compact_D",
    "compact_Sp",
    "hypersingular_Dp",
]

#: For each claim, the jump relations its rewrite applies, and what its verdict
#: is decided under, in the order the ledger names them.
EXPECTED = {
    "laplace_dirichlet_dlp": (["jump_D"], ["jump_D", "compact_D"]),
    "laplace_dirichlet_slp": (["jump_S"], ["jump_S", "compact_S"]),
    "laplace_neumann_slp": (["jump_Sp"], ["jump_Sp", "compact_Sp"]),
    "helmholtz_combined_field": (
        ["jump_D", "jump_S"],
        ["jump_D", "jump_S", "compact_D", "compact_S"],
    ),
    "helmholtz_burton_miller": (
        ["jump_Dp", "jump_Sp"],
        ["jump_Dp", "jump_Sp", "compact_Sp", "hypersingular_Dp"],
    ),
}


@pytest.fixture(autouse=True)
def _examples_on_the_path(monkeypatch):
    """The demonstration imports its rule engine by name, and installs an oracle.

    Both are undone after each test: the path by ``monkeypatch``, and the
    oracle because the registry's list is swapped for a copy, which a rule
    set built during the test installs itself into.
    """
    monkeypatch.syspath_prepend(str(EXAMPLES))
    monkeypatch.setattr(registry, "oracles", list(registry.oracles))


@pytest.fixture
def lp():
    """The rule engine."""
    return importlib.import_module("layer_potentials")


@pytest.fixture
def demo():
    """The demonstration, imported afresh, with its claims kept out of the registry."""
    with registry.collecting():
        return import_path(DEMO)


HEADER = '''
from __future__ import annotations

from layer_potentials import (
    EXTERIOR,
    INTERIOR,
    C2Boundary,
    D,
    Dp,
    I,
    RuleSet,
    S,
    Side,
    Sp,
    compact,
    normal_derivative,
    scalar_plus_compact,
    trace,
)

from lanky import axiom, theorem
from lanky.prelude import Nat
'''


def write(tmp_path, text: str) -> Path:
    path = tmp_path / "claims.py"
    path.write_text(text, encoding="utf-8")
    return path


def load(tmp_path, text: str):
    """Import a file of axioms and claims, keeping its objects out of the registry."""
    path = write(tmp_path, text)
    with registry.collecting():
        return import_path(path)


# {{{ the two commands


def test_python_runs_the_demo_and_prints_the_five_verdicts() -> None:
    """The acceptance table, the two refusals explained, and exit code 0."""
    run = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, cwd=ROOT, timeout=600
    )
    assert run.returncode == 0, run.stdout + run.stderr
    lines = run.stdout.splitlines()
    start = next(index for index, line in enumerate(lines) if line.startswith("problem"))
    rows = [re.split(r"\s{2,}", line) for line in lines[start + 2 : start + 7]]
    assert rows == [
        ["Laplace, interior Dirichlet", "u = D sigma", "(-1/2*I + D) sigma = f", "second kind"],
        ["Laplace, interior Dirichlet", "u = S sigma", "S sigma = f", "refused: no identity term"],
        ["Laplace, interior Neumann", "u = S sigma", "(1/2*I + S') sigma = g", "second kind"],
        [
            "Helmholtz, exterior Dirichlet (combined field)",
            "u = (D - 1j*eta*S) sigma",
            "(1/2*I + D - 1j*eta*S) sigma = f",
            "second kind",
        ],
        [
            "Helmholtz, exterior Neumann (Burton-Miller)",
            "u = (D - 1j*eta*S) sigma",
            "(1j/2*eta*I + D' - 1j*eta*S') sigma = g",
            "refused: D' is not c*I + compact",
        ],
    ]
    assert (
        "laplace_dirichlet_slp: the identity coefficient is 0 and the rest is compact "
        "(S by compact_S): the operator is compact. Under jump_S, compact_S." in lines
    )
    assert (
        "helmholtz_burton_miller: D' is not c*I + compact (hypersingular_Dp) and its "
        "coefficient is 1, not 0, while the rest is compact (S' by compact_Sp): the operator "
        "is not c*I + compact either. Under jump_Dp, jump_Sp, compact_Sp, hypersingular_Dp."
        in lines
    )
    assert any(
        line.startswith(("pytential is not importable here", "pytential: the five"))
        for line in lines
    )


def test_lanky_check_decides_each_verdict_under_the_axioms_it_applied() -> None:
    ledger = check_path(DEMO)
    facts = list(ledger)
    axioms = {fact.owner: fact for fact in facts if fact.kind == "axiom"}
    assert list(axioms) == AXIOMS
    for fact in axioms.values():
        assert (fact.status, fact.decided_by) == (Status.ASSUMED, None)
        assert "Colton and R. Kress" in fact.provenance["cite"]
    ids = {owner: fact.id for owner, fact in axioms.items()}
    claims: dict[str, dict] = {}
    for fact in facts:
        if fact.kind != "axiom":
            claims.setdefault(fact.owner, {})[fact.kind] = fact
    assert list(claims) == list(EXPECTED)
    for owner, (jumps, under) in EXPECTED.items():
        rewrite, verdict = claims[owner]["rewrite"], claims[owner]["verdict"]
        assert (rewrite.status, rewrite.decided_by) == (Status.DECIDED, "layer-rules")
        assert rewrite.provenance["trust_class"] == "decision-procedure"
        assert rewrite.rests_on == tuple(ids[name] for name in jumps)
        assert rewrite.statement.endswith("(jump relations)")
        assert (verdict.status, verdict.decided_by) == (Status.DECIDED, "layer-rules")
        assert verdict.rests_on[0] == rewrite.id
        support = ledger.support(verdict)
        assert support.under == tuple(ids[name] for name in under)
        assert support.effective is Status.ASSUMED
    coefficients = {
        owner: kinds["coefficient"] for owner, kinds in claims.items() if "coefficient" in kinds
    }
    assert {owner: fact.statement for owner, fact in coefficients.items()} == {
        "laplace_dirichlet_dlp": "coefficient of I: -1/2 != 0",
        "laplace_neumann_slp": "coefficient of I: 1/2 != 0",
        "helmholtz_combined_field": "coefficient of I: 1/2 != 0",
    }
    for owner, fact in coefficients.items():
        # the one part Lean touches: proved where it is installed, tested where not
        assert fact.status in (Status.PROVED, Status.TESTED)
        assert fact.id in claims[owner]["verdict"].rests_on
    statements = [claims[owner]["verdict"].statement for owner in EXPECTED]
    assert statements[1] == "S is first kind: no identity term"
    assert statements[4] == (
        "1j/2*eta*I + D' - 1j*eta*S' is not second kind: D' is not c*I + compact"
    )
    assert ledger.by_status(Status.REFUTED) == ()


def test_lanky_check_exits_0_and_shows_every_citation(capsys) -> None:
    assert cli.main(["check", str(DEMO)]) == 0
    out = capsys.readouterr().out
    cited = [line for line in out.splitlines() if line.startswith("CITED ")]
    assert [line.split()[1] for line in cited] == AXIOMS
    assert all("Colton and R. Kress" in line for line in cited)
    assert sum("Linear Integral Equations" in line for line in cited) == 7
    for _jumps, under in EXPECTED.values():
        assert f"decided under {', '.join(under)} " in out


def _cells(line: str) -> list[str]:
    return re.split(r"\s{2,}", line.rstrip())


def _with_lean(line: str) -> str:
    """A line of the quickstart's table, as it reads where Lean proves the coefficients."""
    cells = _cells(line)
    if cells[:3] == ["tested", "tested", "property-test"]:
        return "  ".join(["proved", "proved", "lean", *cells[3:]])
    return line.replace("10 decided, 3 tested", "10 decided, 3 proved")


def test_the_quickstart_shows_the_ledger_the_demo_prints(capsys) -> None:
    """The quickstart's table for the demonstration is the real one.

    The document shows it as a machine without Lean prints it. Where Lean
    proves the three coefficient rows, those rows and the summary read
    ``proved lean`` instead, and every column is sized to what it holds, so
    the rows are compared cell by cell.
    """
    lines = (ROOT / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    start = lines.index("$ uv run lanky check examples/pytential_skie.py")
    shown = []
    for line in lines[start + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line)
    proved = any(fact.status is Status.PROVED for fact in check_path(DEMO))
    if proved:
        shown = [_with_lean(line) for line in shown]
    assert cli.main(["check", str(DEMO)]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    assert len(shown) == len(printed)
    for doc, real in zip(shown, printed, strict=True):
        if doc and set(doc) <= {"-", " "}:
            assert len(_cells(doc)) == len(_cells(real))
        else:
            assert _cells(doc) == _cells(real)


# }}}


# {{{ the rule engine, without the ledger


def test_each_jump_relation_from_each_side(demo, lp) -> None:
    def resolved(operator):
        return str(lp.resolve(operator, demo.rules).operator)

    assert resolved(lp.trace(lp.D, lp.INTERIOR)) == "-1/2*I + D"
    assert resolved(lp.trace(lp.D, lp.EXTERIOR)) == "1/2*I + D"
    assert resolved(lp.trace(lp.S, lp.INTERIOR)) == resolved(lp.trace(lp.S, lp.EXTERIOR)) == "S"
    assert resolved(lp.normal_derivative(lp.S, lp.INTERIOR)) == "1/2*I + S'"
    assert resolved(lp.normal_derivative(lp.S, lp.EXTERIOR)) == "-1/2*I + S'"
    assert (
        resolved(lp.normal_derivative(lp.D, lp.INTERIOR))
        == resolved(lp.normal_derivative(lp.D, lp.EXTERIOR))
        == "D'"
    )
    assert lp.resolve(lp.trace(lp.D - lp.S, lp.INTERIOR), demo.rules).steps == (
        "trace(D, INTERIOR) = -1/2*I + D by jump_D",
        "trace(S, INTERIOR) = S by jump_S",
    )


def test_the_combined_field_from_the_interior_has_minus_one_half(demo, lp) -> None:
    """The sign the combined field equation is sometimes written with is the interior one."""
    u = lp.D - 1j * demo.eta * lp.S
    interior = lp.resolve(lp.trace(u, lp.INTERIOR), demo.rules).operator
    assert lp.same(interior, -lp.I / 2 + lp.D - 1j * demo.eta * lp.S)
    found = lp.classify(interior, demo.rules)
    assert (found.kind, str(found.identity)) == ("second kind", "-1/2")


def test_a_wrong_boundary_operator_is_refused_with_the_difference(demo, lp) -> None:
    wrong = lp.JumpRewrite(lp.trace(lp.D, lp.INTERIOR), lp.I / 2 + lp.D, lp.OBLIGATION, demo.rules)
    decision = lp.decide(wrong)
    assert not decision.holds
    assert decision.reason == (
        "the jump relations give trace(D, INTERIOR) = -1/2*I + D (jump_D), and the target "
        "is 1/2*I + D: they differ by -I"
    )


def test_a_verdict_that_does_not_hold_is_refused_naming_the_term(demo, lp) -> None:
    rules = demo.rules
    burton_miller = demo.helmholtz_burton_miller.target
    second = lp.decide(lp.VerdictQuestion(burton_miller, lp.SECOND_KIND, rules))
    assert not second.holds
    assert second.reason.startswith(
        "1j/2*eta*I + D' - 1j*eta*S' is not second kind: D' is not c*I + compact "
        "(hypersingular_Dp)"
    )
    single = lp.decide(lp.VerdictQuestion(lp.S, lp.SECOND_KIND, rules))
    assert not single.holds
    assert single.reason.startswith("S is first kind: the identity coefficient is 0")
    double = lp.decide(lp.VerdictQuestion(-lp.I / 2 + lp.D, lp.FIRST_KIND, rules))
    assert not double.holds
    assert double.reason.startswith("-1/2*I + D is second kind")
    named = lp.decide(
        lp.VerdictQuestion(burton_miller, lp.Verdict("not second kind", ("S'",)), rules)
    )
    assert not named.holds
    assert named.reason == "the operator that is not c*I + compact is D', not S'"


def test_what_the_rules_decline_and_why(demo, lp) -> None:
    """Outside the fragment the engine says so, rather than guessing."""
    rules, eta = demo.rules, demo.eta
    with pytest.raises(lp.OutsideFragment, match="identity coefficient eta mentions eta"):
        lp.classify(eta * lp.I + lp.D, rules)
    with pytest.raises(lp.OutsideFragment, match="coefficient eta of D' mentions eta"):
        lp.classify(eta * lp.Dp + lp.S, rules)
    with pytest.raises(lp.OutsideFragment, match="side that is a variable"):
        lp.resolve(lp.trace(lp.D, eta), rules)
    with pytest.raises(lp.OutsideFragment, match="product of operators"):
        lp.S * lp.D
    with pytest.raises(lp.OutsideFragment, match="only a layer potential"):
        lp.trace(lp.Sp, lp.INTERIOR)
    with pytest.raises(lp.OutsideFragment, match="two kernels"):
        laplace = lp.Operator({lp.Symbol("S"): lp.ONE}, kernel="Laplace(2)")
        helmholtz = lp.Operator({lp.Symbol("D"): lp.ONE}, kernel="Helmholtz(2, k=k)")
        laplace + helmholtz
    with pytest.raises(ValueError, match="a side is INTERIOR"):
        lp.trace(lp.D, 0)


def test_coefficients_are_exact(demo, lp) -> None:
    """A float is the binary number it is; a polynomial is kept canonical."""
    eta = demo.eta
    assert lp.scalar(0.5) == lp.scalar(1) * lp.Poly.constant(lp.Gauss(lp.Fraction(1, 2)))
    assert lp.scalar(0.1) != lp.Poly.constant(lp.Gauss(lp.Fraction(1, 10)))
    assert str(lp.scalar(1j * eta / 2 - eta * 1j / 2)) == "0"
    assert str(lp.scalar((eta + 1) ** 2)) == "1 + 2*eta + eta**2"
    with pytest.raises(lp.OutsideFragment, match="not a nonzero constant"):
        lp.scalar(1 / eta)
    assert str(1j * eta / 2 * lp.I + lp.Dp) == "1j/2*eta*I + D'"
    assert str((1 + eta) * lp.S) == "(1 + eta)*S"


PARTIAL = HEADER + '''

@axiom(cite="a test")
def jump_D(gamma: C2Boundary, s: Side) -> trace(D, s) == D + s / 2 * I:
    """The double-layer jump."""


@axiom(cite="a test")
def hyper_S(gamma: C2Boundary) -> ~scalar_plus_compact(S):
    """False, but an axiom may say it, and the rules then decline what it touches."""


@axiom(cite="a test")
def hyper_Dp(gamma: C2Boundary) -> ~scalar_plus_compact(Dp):
    """D' is hypersingular."""


rules = RuleSet(jump_D, hyper_S, hyper_Dp)
'''


def test_the_rules_are_exactly_the_axioms_given(tmp_path, lp) -> None:
    module = load(tmp_path, PARTIAL)
    with pytest.raises(lp.OutsideFragment, match="no axiom gives the trace of S"):
        lp.resolve(lp.trace(lp.S, lp.INTERIOR), module.rules)
    with pytest.raises(lp.OutsideFragment, match="no axiom says whether D is compact"):
        lp.classify(-lp.I / 2 + lp.D, module.rules)
    with pytest.raises(lp.OutsideFragment, match="S and D' are both not a multiple"):
        lp.classify(lp.S + lp.Dp, module.rules)


BAD_RULES = HEADER + '''

@axiom(cite="a test")
def jump_D(gamma: C2Boundary, s: Side) -> trace(D, s) == D + s / 2 * I:
    """The double-layer jump."""


@axiom(cite="a test")
def jump_D_again(gamma: C2Boundary, s: Side) -> trace(D, s) == D - s / 2 * I:
    """The same trace, given a second time."""


@axiom(cite="a test")
def compact_I(gamma: C2Boundary) -> compact(I):
    """The identity is not compact in infinite dimensions."""


@axiom(cite="a test")
def arithmetic(n: Nat) -> n + 0 == n:
    """Not a rule about operators."""


@axiom(cite="a test")
def one_side(gamma: C2Boundary) -> trace(D, INTERIOR) == -I / 2 + D:
    """A jump relation for one side, not stated for a side variable."""


@theorem
def not_an_axiom(gamma: C2Boundary) -> compact(S):
    """A theorem is not a rule."""
'''


def test_a_rule_set_refuses_what_is_not_one_rule(tmp_path, lp) -> None:
    module = load(tmp_path, BAD_RULES)
    with pytest.raises(ValueError, match="jump_D_again and jump_D both give the trace of D"):
        lp.RuleSet(module.jump_D, module.jump_D_again)
    with pytest.raises(TypeError, match="I is the identity"):
        lp.RuleSet(module.compact_I)
    with pytest.raises(TypeError, match="not a rule these operators have"):
        lp.RuleSet(module.arithmetic)
    with pytest.raises(TypeError, match="side variable of sort Side"):
        lp.RuleSet(module.one_side)
    with pytest.raises(TypeError, match="read off an @axiom"):
        lp.RuleSet(module.not_an_axiom)


# }}}


# {{{ claims that are wrong, through lanky check

MISCOPIED = HEADER + '''

@axiom(cite="Kress, with the sign copied down wrong")
def jump_D(gamma: C2Boundary, s: Side) -> trace(D, s) == D - s / 2 * I:
    """The double-layer jump, with its sign flipped."""


@axiom(cite="Kress")
def compact_D(gamma: C2Boundary) -> compact(D):
    """D is compact."""


rules = RuleSet(jump_D, compact_D)


@rules.second_kind
def dirichlet():
    """Laplace, interior Dirichlet."""
    return trace(D, INTERIOR), -I / 2 + D
'''


def test_a_jump_relation_copied_down_wrong_refutes_the_rewrite(tmp_path, capsys) -> None:
    """The engine applies the axioms as written, so a wrong one shows in what uses it."""
    path = write(tmp_path, MISCOPIED)
    ledger = check_path(path)
    jump, _compact, rewrite, coefficient, verdict = ledger
    assert (rewrite.status, rewrite.decided_by) == (Status.REFUTED, "layer-rules")
    assert rewrite.rests_on == (jump.id,)
    assert coefficient.status in (Status.PROVED, Status.TESTED)
    # the operator is still of the second kind, and worth what it rests on
    assert verdict.status is Status.DECIDED
    assert ledger.support(verdict).effective is Status.REFUTED
    assert cli.main(["check", str(path)]) == 1
    out = capsys.readouterr().out
    assert "REFUTED dirichlet at claims.py:" in out
    assert (
        "  the jump relations give trace(D, INTERIOR) = 1/2*I + D (jump_D), and the target "
        "is -1/2*I + D: they differ by I" in out
    )


SINGLE = HEADER + '''

@axiom(cite="Kress")
def jump_S(gamma: C2Boundary, s: Side) -> trace(S, s) == S:
    """S is continuous across the boundary."""


@axiom(cite="Kress")
def compact_S(gamma: C2Boundary) -> compact(S):
    """S is compact."""


rules = RuleSet(jump_S, compact_S)


@rules.second_kind
def single():
    """Laplace, interior Dirichlet, claimed of the wrong kind."""
    return trace(S, INTERIOR), S
'''


def test_claiming_the_second_kind_of_a_compact_operator_is_refuted(tmp_path) -> None:
    ledger = check_path(write(tmp_path, SINGLE))
    _jump, _compact, rewrite, coefficient, verdict = ledger
    assert rewrite.status is Status.DECIDED
    assert coefficient.statement == "coefficient of I: 0 != 0"
    assert coefficient.status is Status.REFUTED
    assert (verdict.status, verdict.decided_by) == (Status.REFUTED, "layer-rules")
    assert verdict.provenance["reason"] == (
        "S is first kind: the identity coefficient is 0 and the rest is compact "
        "(S by compact_S): the operator is compact"
    )


# }}}


# {{{ what lanky depends on


def test_pytential_and_sympy_are_never_lanky_dependencies() -> None:
    """Not declared, and not imported by lanky, the rule engine or the demonstration."""
    project = tomllib.loads((ROOT / "pyproject.toml").read_text(encoding="utf-8"))["project"]
    declared = [
        *project["dependencies"],
        *(entry for extra in project.get("optional-dependencies", {}).values() for entry in extra),
    ]
    assert not [entry for entry in declared if re.match(r"(pytential|sympy|sumpy)\b", entry)]
    code = (
        "import sys, lanky, lanky.cli, lanky.rewrites, layer_potentials\n"
        "from lanky.check import import_path\n"
        f"import_path({str(DEMO)!r})\n"
        "print(sorted({m.split('.')[0] for m in sys.modules} & {'pytential', 'sympy', 'sumpy'}))"
    )
    run = subprocess.run(
        [sys.executable, "-c", code], capture_output=True, text=True, cwd=EXAMPLES, timeout=300
    )
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip() == "[]"


def test_pytest_collects_the_axioms_and_skips_them(pytester) -> None:
    """They quantify over boundaries, which the property tester cannot draw."""
    plugins = {entry.name for entry in importlib.metadata.entry_points(group="pytest11")}
    arguments = [] if "lanky" in plugins else ["-p", "lanky.pytest_plugin"]
    with registry.collecting():
        result = pytester.runpytest(str(DEMO), *arguments)
    result.assert_outcomes(skipped=8)


# }}}


# {{{ the pytential adapter, on stand-ins for pytential's nodes


class LaplaceKernel:
    """Stands for sumpy's kernel, which the adapter reads by its class name and ``dim``."""

    def __init__(self, dim: int) -> None:
        self.dim = dim

    def __eq__(self, other: object) -> bool:
        return type(other) is type(self) and other.dim == self.dim

    def __hash__(self) -> int:
        return hash((type(self).__name__, self.dim))

    def __str__(self) -> str:
        return f"LaplaceKernel({self.dim})"


class IntG:
    """Stands for pytential's ``IntG``: the adapter reads its fields, and its class by name.

    ``source`` and ``target`` stand for its DOF descriptors, whose geometry
    the adapter reads, and a plain name is read as the geometry itself.
    """

    def __init__(self, density, limit, source=None, target=None) -> None:
        self.target_kernel = LaplaceKernel(2)
        self.source_kernels = (LaplaceKernel(2),)
        self.densities = (density,)
        self.qbx_forced_limit = limit
        self.kernel_arguments = {}
        self.source = source
        self.target = target


def test_the_adapter_reads_one_boundary_and_constant_factors(lp) -> None:
    """What the adapter refuses, checked without pytential, so that CI runs it.

    Two layer operators on two boundaries are two operators, and a limit on
    one boundary of a potential whose density is on another is no jump
    relation's business, so neither may be read as the one boundary's. A
    factor inside an operator comes out of it only when it is a constant: a
    parameter there could be a function on the boundary, and ``S(tau*sigma)``
    is not ``tau*S(sigma)``.
    """
    sigma, eta = prim.Variable("sigma"), prim.Variable("eta")
    assert str(lp.from_pytential(IntG(sigma, "avg"))) == "S"
    assert str(lp.from_pytential(IntG(sigma, -1, "a", "a"))) == "trace(S, INTERIOR)"
    assert str(lp.from_pytential(IntG(prim.Product((2, sigma)), "avg"))) == "2*S"
    # a potential evaluated elsewhere, off the boundary, is a representation
    assert str(lp.from_pytential(IntG(sigma, None, "a", "points"))) == "S"
    with pytest.raises(lp.OutsideFragment, match="two geometries in one expression"):
        lp.from_pytential(prim.Sum((IntG(sigma, "avg", "a", "a"), IntG(sigma, "avg", "b", "b"))))
    with pytest.raises(lp.OutsideFragment, match="two geometries in one expression"):
        lp.from_pytential(prim.Sum((IntG(sigma, "avg", "a", "a"), IntG(sigma, None, "a", "b"))))
    with pytest.raises(lp.OutsideFragment, match="the density on 'a' and the targets on 'b'"):
        lp.from_pytential(IntG(sigma, -1, "a", "b"))
    with pytest.raises(lp.OutsideFragment, match="density on the default and the targets on 'b'"):
        lp.from_pytential(IntG(sigma, "avg", None, "b"))
    with pytest.raises(lp.OutsideFragment, match="only a constant comes out of an operator"):
        lp.from_pytential(IntG(prim.Product((eta, sigma)), "avg"))
    with pytest.raises(lp.OutsideFragment, match="qbx_forced_limit=True"):
        lp.from_pytential(IntG(sigma, True))


# }}}


# {{{ the pytential adapter, where pytential imports


def _pytential():
    pytest.importorskip("pytential")
    from pytential import sym
    from sumpy.kernel import HelmholtzKernel, LaplaceKernel

    return sym, LaplaceKernel(2), HelmholtzKernel(2)


def test_the_adapter_reads_each_layer_operator_at_each_limit(lp) -> None:
    sym, laplace, _helmholtz = _pytential()
    sigma = sym.var("sigma")
    expected = {
        ("S", None): "S",
        ("D", None): "D",
        ("S", -1): "trace(S, INTERIOR)",
        ("S", +1): "trace(S, EXTERIOR)",
        ("D", +1): "trace(D, EXTERIOR)",
        ("S", "avg"): "S",
        ("D", "avg"): "D",
        ("Sp", "avg"): "S'",
        ("Dp", "avg"): "D'",
        ("Sp", -1): "normal_derivative(S, INTERIOR)",
        ("Dp", +1): "normal_derivative(D, EXTERIOR)",
    }
    for (name, limit), text in expected.items():
        operator = lp.from_pytential(getattr(sym, name)(laplace, sigma, qbx_forced_limit=limit))
        assert (str(operator), operator.kernel) == (text, "Laplace(2)"), (name, limit)
    with pytest.raises(lp.OutsideFragment, match="off the boundary"):
        lp.from_pytential(sym.Sp(laplace, sigma, qbx_forced_limit=None))


def test_the_adapter_reads_coefficients_and_the_identity(lp) -> None:
    sym, _laplace, helmholtz = _pytential()
    sigma, eta, k = sym.var("sigma"), sym.var("eta"), sym.var("k")
    operator = lp.from_pytential(
        0.5j * eta * sigma
        + sym.Dp(helmholtz, sigma, k=k, qbx_forced_limit="avg")
        - 1j * eta * sym.Sp(helmholtz, sigma, k=k, qbx_forced_limit="avg")
    )
    assert str(operator) == "1j/2*eta*I + D' - 1j*eta*S'"
    assert operator.kernel == "Helmholtz(2, k=k)"


def test_the_adapter_refuses_what_it_does_not_read(lp) -> None:
    sym, laplace, helmholtz = _pytential()
    from sumpy.kernel import BiharmonicKernel

    sigma = sym.var("sigma")
    with pytest.raises(lp.OutsideFragment, match="two kernels"):
        lp.from_pytential(
            sym.S(laplace, sigma, qbx_forced_limit="avg")
            + sym.D(helmholtz, sigma, k=sym.var("k"), qbx_forced_limit="avg")
        )
    with pytest.raises(lp.OutsideFragment, match="not to sigma"):
        lp.from_pytential(
            sym.S(laplace, sym.D(laplace, sigma, qbx_forced_limit="avg"), qbx_forced_limit="avg")
        )
    with pytest.raises(lp.OutsideFragment, match="not to sigma"):
        lp.from_pytential(sym.S(laplace, sym.var("tau"), qbx_forced_limit="avg"))
    with pytest.raises(lp.OutsideFragment, match="not a Laplace or Helmholtz kernel"):
        lp.from_pytential(sym.S(BiharmonicKernel(2), sigma, qbx_forced_limit="avg"))
    with pytest.raises(lp.OutsideFragment, match="mixes potentials"):
        lp.from_pytential(sym.S(laplace, sigma, qbx_forced_limit=None) + sigma)
    with pytest.raises(lp.OutsideFragment, match="two geometries in one expression"):
        lp.from_pytential(
            sym.D(laplace, sigma, qbx_forced_limit="avg", source="a", target="a")
            + sym.D(laplace, sigma, qbx_forced_limit="avg", source="b", target="b")
        )
    with pytest.raises(lp.OutsideFragment, match="the density on 'a' and the targets on 'b'"):
        lp.from_pytential(sym.D(laplace, sigma, qbx_forced_limit=-1, source="a", target="b"))
    with pytest.raises(lp.OutsideFragment, match="only a constant comes out of an operator"):
        lp.from_pytential(sym.D(laplace, sym.var("tau") * sigma, qbx_forced_limit="avg"))
    with pytest.raises(lp.OutsideFragment, match="a normal component, outside a normal derivative"):
        lp.from_pytential(
            sym.normal(2).as_vector()[0] * sym.S(laplace, sigma, qbx_forced_limit="avg")
        )


def test_the_five_rows_and_pytentials_own_operators_agree(demo) -> None:
    """The rows built with ``pytential.sym`` are the demonstration's, and its pairs check out."""
    _pytential()
    ok, lines = demo.pytential_lines()
    assert ok, lines
    assert lines[0] == (
        "pytential: the five representations and operators, built with pytential.sym, "
        "translate to the rows above."
    )
    assert (
        "pytential's DirichletOperator(LaplaceKernel(2), loc_sign=-1): operator 1/2*I - D, "
        "which is the jump relations image of trace(-D, INTERIOR); second kind" in lines
    )
    assert (
        "pytential's DirichletOperator(HelmholtzKernel(2), loc_sign=+1, alpha=1j): operator "
        "-1/2*I - D + 1j*trace(S, EXTERIOR), which is the jump relations image of "
        "trace(-D + 1j*S, EXTERIOR); second kind" in lines
    )


# }}}
