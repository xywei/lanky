"""Chains and citations of written proofs: the surface, the matcher, and the Lean of each step.

The surface and the matcher are Python and need no Lean. The Lean each step
compiles to is checked in two ways: as text, against what the design's
examples print, and, where a Lean with Mathlib is installed, by Lean itself,
inside the recursive theorem a written proof compiles to (the design's 1.1
and 1.2, as the check's T3 and T7 wrote them). The proof-trace mode that
runs a body and calls ``claim`` is not here: these tests build the scope a
step is compiled in by hand, as the tracer will.
"""

from __future__ import annotations

import os
from types import SimpleNamespace

import pytest

from lanky import theorem
from lanky.chains import Chain, ChainError, combined_relation
from lanky.citations import (
    Citation,
    Cited,
    CitedText,
    Hypothesis,
    citation_of,
    proved_texts,
    vacuity_question,
)
from lanky.induction import Lemma
from lanky.lean import UnsupportedTerm, lean_type, print_lean, proof_exponents, render_term
from lanky.matching import (
    FamilyValue,
    NoSinglePoint,
    candidate_points,
    higher_order_value,
    implied,
    instantiate,
    same,
    single_point,
)
from lanky.oracles.lean import CLOSED_WITH_HOLES, LeanOracle, LeanSession, holes_verdict
from lanky.oracles.steps import (
    StepError,
    StepScope,
    chain_script,
    draw_links,
    drawn_status,
    named_script,
    nonzero_lines,
    outline_text,
    shift_lines,
    step_script,
)
from lanky.prelude import Complex, Fin, Fn, Int, Nat, Real
from lanky.terms import Comparison, LogicalNot, Sum, Var, log, render, structurally_equal

D, R, a, b = Var("D"), Var("R"), Var("a"), Var("b")
n, r, k = Var("n"), Var("r"), Var("k")
alpha, beta, x = Var("alpha"), Var("beta"), Var("x")


@theorem
def compressed_taylor(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """The design's 1.1, its statement as l2p.py has it."""


@theorem
def line_taylor(
    alpha: Complex,
    beta: Complex,
    a: Fn[Nat, Complex],
    nonzero: alpha != 0,
    first_term: alpha * a[1] == beta,
    ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
) -> all(a[n] == -((-beta / alpha) ** n) / n for n in Nat if n >= 1):
    """The design's 1.2, with the coefficient written out."""


class Claim:
    """``claim`` as a proof body holds it: calling it cites the claim at a point."""

    def __init__(self, citation: Citation) -> None:
        self.citation = citation

    def __call__(self, *values):
        return Cited(self.citation.at(values))


def hypotheses(thm) -> dict[str, Hypothesis]:
    """The theorem's hypotheses as the handles a proof body holds."""
    return {name: Hypothesis(name, prop) for name, prop in thm.hypotheses}


def compressed_taylor_case():
    """The second case of 1.1: the chain, and the scope it is compiled in."""
    facts = hypotheses(compressed_taylor)
    pde, recurrence = facts["pde"], facts["recurrence"]
    claim = Claim(
        Citation(
            "the claim",
            compressed_taylor.goal,
            "Lanky.compressed_taylor.claim D R pde stored recurrence",
            kind="claim",
        )
    )
    # fmt: off
    chain = (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=recurrence)
        .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))
        .equals(D[a, b], by=pde)
    )
    # fmt: on
    types = {**dict(compressed_taylor.variables), "a": Nat, "b": Nat}
    scope = StepScope(
        types=types,
        facts=(LogicalNot(a < 2),),
        taken={"pde", "stored", "recurrence", "ha", "hb", "case_1"},
        path=__file__,
    )
    return chain, scope, claim, facts


def line_taylor_case():
    """The second case of 1.2: the named fact, the return's reasons, and the scope."""
    facts = hypotheses(line_taylor)
    ode = facts["ode"]
    claim = Claim(
        Citation(
            "the claim",
            line_taylor.goal,
            "Lanky.line_taylor.claim alpha beta a nonzero first_term ode",
            kind="claim",
        )
    )
    a_ = Var("a")
    ratio = -beta / alpha
    recurrence = a_[n].equals((n - 1) / n * ratio * a_[n - 1], by=ode)
    types = {**dict(line_taylor.variables), "n": Nat}
    scope = StepScope(
        types=types,
        facts=(n >= 1, LogicalNot(Comparison(n, "==", 1))),
        taken={"nonzero", "first_term", "ode", "hn0", "hn1", "case_1"},
        path=__file__,
    )
    return recurrence, claim(n - 1), scope


# {{{ the surface


def test_the_words_build_links_each_with_its_line() -> None:
    """A chain laid out a link to a line records each link's own line, as the textbook's column."""
    # fmt: off
    first = R[a, b].equals(-R[a - 2, b + 2])
    chain = (
        R[a, b]
        .equals(-R[a - 2, b + 2])
        .at_most(D[a, b])
        .less_than(D[a, b] + 1)
    )
    # fmt: on
    assert isinstance(chain, Chain)
    lines = [link.line for link in chain.links]
    assert lines[1] == lines[0] + 1 and lines[2] == lines[1] + 1
    assert first.line == lines[0] - 3
    assert [link.word for link in chain.links] == ["equals", "at_most", "less_than"]
    assert chain.relation == "<"
    assert render(chain.claim) == "R[a, b] < D[a, b] + 1"
    assert os.path.basename(chain.path) == "test_chains.py"
    assert all(link.algebra for link in chain.links)


def test_the_relations_combine_one_way() -> None:
    """Equalities keep the others' relation; a strict one wins; the two directions do not mix."""
    assert combined_relation(["==", "=="]) == "=="
    assert combined_relation(["==", "<=", "=="]) == "<="
    assert combined_relation(["<=", "<", "<="]) == "<"
    assert combined_relation([">", ">="]) == ">"
    with pytest.raises(ChainError, match="turns the chain the other way after .at_most"):
        R[a, b].at_most(D[a, b]).at_least(D[a, b] - 1)


def test_by_takes_facts_tuples_and_holes() -> None:
    """``by=`` is a fact, a tuple of facts, or ``...``; anything else is refused at its line."""
    pde = Hypothesis("pde", compressed_taylor.hypotheses[0][1])
    one = R[a, b].equals(D[a, b], by=pde)
    assert one.links[0].reasons == (pde,) and not one.links[0].hole
    two = R[a, b].equals(D[a, b], by=(pde, pde))
    assert len(two.links[0].reasons) == 2
    hole = R[a, b].equals(D[a, b], by=...)
    assert hole.links[0].hole and hole.holes == (hole.line,)
    with pytest.raises(ChainError, match="names no fact"):
        R[a, b].equals(D[a, b], by="pde")
    with pytest.raises(ChainError, match="takes no facts beside it"):
        R[a, b].equals(D[a, b], by=(pde, ...))
    with pytest.raises(ChainError, match="is a term, which is no reason"):
        R[a, b].equals(D[a, b], by=a + 1)
    with pytest.raises(ChainError, match="reaches a proposition"):
        R[a, b].equals(D[a, b] == 0)
    with pytest.raises(ChainError, match="a chain starts at a term"):
        (R[a, b] == D[a, b]).equals(D[a, b])


def test_a_chain_is_no_condition() -> None:
    """``if chain:`` is refused: a chain is a step of a proof."""
    chain = R[a, b].equals(D[a, b])
    with pytest.raises(ChainError, match="is a step of the proof and not a condition"):
        bool(chain)


def test_a_named_chain_is_named_by_its_assignment() -> None:
    """``recurrence = a[n].equals(...)`` is the fact ``recurrence``; a returned chain is unnamed."""
    recurrence = Var("a")[n].equals((n - 1) / n * Var("a")[n - 1])
    assert recurrence.name == "recurrence"
    # fmt: off
    longer = (
        R[a, b]
        .equals(-R[a - 2, b + 2])
        .equals(D[a, b])
    )
    # fmt: on
    assert longer.name == "longer"

    def returned():
        return R[a, b].equals(D[a, b])

    assert returned().name is None
    cited = citation_of(recurrence)
    assert cited.kind == "named" and cited.head == "recurrence" and cited.point == ()
    with pytest.raises(TypeError, match="cited without a name"):
        citation_of(returned())


def test_a_hypothesis_is_cited_at_a_point_or_uncalled() -> None:
    """``pde(a - 2, b)`` is the fact at a point, ``pde`` uncalled; a wrong count is refused."""
    pde = Hypothesis("pde", compressed_taylor.hypotheses[0][1])
    uncalled = citation_of(pde)
    assert uncalled.point is None and [v.name for v, _ in uncalled.binders] == ["a", "b"]
    at = citation_of(pde(a - 2, b))
    assert render(at.instance) == "D[a - 2 + 2, b] + D[a - 2, b + 2] == 0"
    assert at.described() == "pde, at (a - 2, b)"
    with pytest.raises(TypeError, match="pde is cited at 1 value, and it takes 2"):
        pde(a)


# }}}


# {{{ matching


def test_an_uncalled_fact_is_matched_by_solving_offsets() -> None:
    """1.1: ``recurrence`` and ``pde`` each fit their link at one point, ``(a - 2, b)``."""
    chain, scope, _, facts = compressed_taylor_case()
    recurrence = facts["recurrence"].__lanky_citation__().lemma
    first = [R[a, b], -R[a - 2, b + 2]]
    points = candidate_points(recurrence, first, scope.types)
    assert len(points) == 3
    point = single_point(recurrence, first, scope.types, scope.facts, "recurrence")
    assert [render(value) for value in point] == ["a - 2", "b"]
    pde = facts["pde"].__lanky_citation__().lemma
    last = [-D[a - 2, b + 2], D[a, b]]
    point = single_point(pde, last, scope.types, scope.facts, "pde")
    assert [render(value) for value in point] == ["a - 2", "b"]


def test_a_condition_follows_from_the_case() -> None:
    """``n >= 1`` and ``n != 1`` give ``n >= 2``; ``a >= 2`` gives ``a - 2 >= 0``, not ``a - 4``."""
    types = {"n": Nat, "a": Nat}
    case = (n >= 1, LogicalNot(Comparison(n, "==", 1)))
    assert implied(Comparison(n - 1, ">=", 1), case, types) is True
    assert implied(Comparison(n - 1, ">=", 1), (n >= 1,), types) is False
    assert implied(Comparison(0, "<=", a - 2), (LogicalNot(a < 2),), types) is True
    assert implied(Comparison(0, "<=", a - 4), (LogicalNot(a < 2),), types) is False
    assert implied(Comparison(n, "!=", 0), case, types) is True
    assert implied(Comparison(alpha, "!=", 0), (), {"alpha": Complex}) is None


def test_the_ode_fits_at_n_minus_one() -> None:
    """1.2: ``ode`` matched against ``a[n] == ... a[n - 1]`` is at ``n - 1``."""
    recurrence, _, scope = line_taylor_case()
    ode = Hypothesis("ode", dict(line_taylor.hypotheses)["ode"]).__lanky_citation__().lemma
    left, link = next(recurrence.steps())
    point = single_point(ode, [left, link.term], scope.types, scope.facts, "ode")
    assert [render(value) for value in point] == ["n - 1"]


def test_no_single_point_asks_for_the_point() -> None:
    """A fact that fits nowhere, or at two points, names the fix: write the point."""
    lemma = Lemma(
        "f",
        ((Var("i"), Nat),),
        (("value", "i"),),
        Comparison(R[Var("i"), 0], "==", R[Var("i"), 1]),
    )
    types = {"R": Fn[Nat, Nat, Real], "a": Nat}
    with pytest.raises(NoSinglePoint, match="no single point of f fits this step"):
        single_point(lemma, [D[a, 0]], types, (), "f")
    twice = Lemma(
        "g",
        ((Var("i"), Nat),),
        (("value", "i"),),
        Comparison(R[Var("i"), 0], "==", 0),
    )
    with pytest.raises(NoSinglePoint, match="fits this step at 2 points"):
        single_point(twice, [R[a, 0] + R[a + 1, 0]], types, (), "g")


def test_first_order_matching_binds_by_type() -> None:
    """``log(x ** n)`` at ``log(abs(alpha) ** 2)`` binds ``x`` and ``n``; a real is no ``n``."""
    log_of_a_power = Lemma(
        "log_of_a_power",
        ((x, Real), (n, Nat)),
        (("value", "x"), ("value", "n"), ("proof", Comparison(0, "<=", n))),
        Comparison(log(x**n), "==", n * log(x)),
    )
    types = {"alpha": Complex}
    target = log(abs(alpha) ** 2) / 2
    point = single_point(log_of_a_power, [log(abs(alpha)), target], types, (), "log_of_a_power")
    assert [render(value) for value in point] == ["abs(alpha)", "2"]
    # a real exponent is no value of n
    assert candidate_points(log_of_a_power, [log(abs(alpha) ** 0.5)], types) == []


def test_the_higher_order_rule_binds_a_family_to_a_function() -> None:
    """``one_more_term``'s ``f`` against ``sum(r ** k for k in Fin[n])`` is ``k ↦ r ** k``."""
    f, m, j = Var("f"), Var("m"), Var("j")
    one_more_term = Lemma(
        "one_more_term",
        ((f, Fn[Nat, Real]), (m, Nat)),
        (("value", "f"), ("value", "m"), ("proof", Comparison(0, "<=", m))),
        Comparison(
            Sum(((j, Fin[m + 1]),), f[j]),
            "==",
            Sum(((j, Fin[m]),), f[j]) + f[m],
        ),
    )
    types = {"r": Real, "n": Nat}
    target = Sum(((k, Fin[n]),), r**k)
    points = candidate_points(one_more_term, [target], types)
    assert len(points) == 1
    family, at = points[0]
    assert isinstance(family, FamilyValue) and family.shown() == "lambda k: r**k"
    assert render(at) == "n - 1"
    instance = instantiate(one_more_term.equation, {"f": family, "m": at})
    assert render(instance.right) == "sum(r**j for j in Fin(n - 1)) + r**(n - 1)"
    # the rule itself: distinct bound variables, none escaping
    assert higher_order_value((j,), r**k, {"j": "k"}).shown() == "lambda k: r**k"
    assert higher_order_value((j, j), r**k, {"j": "k"}) is None
    assert higher_order_value((j,), r**k + Var("l"), {"j": "k", "i": "l"}) is None
    assert higher_order_value((n,), r**k, {"j": "k"}) is None


def test_same_reads_indices_as_integers() -> None:
    """``R[a - 2 + 2, b]`` is ``R[a, b]``."""
    assert same(R[(a - 2) + 2, b], R[a, b])
    assert not same(R[a - 2, b], R[a, b])


# }}}


# {{{ the Lean of a step


def test_the_chain_of_compressed_taylor_is_a_calc() -> None:
    """1.1's chain prints as the check's T3: a ``calc``, each link with its fact at its point."""
    chain, scope, _, _ = compressed_taylor_case()
    script = chain_script(chain, scope, claim=R[a, b] == D[a, b])
    text = script.text()
    assert text.startswith("calc R a b\n    = (-1) * R (a - 2) (b + 2) := by\n")
    assert "have h := recurrence (a - 2) (by omega) b (by omega)" in text
    assert (
        "have ih := Lanky.compressed_taylor.claim D R pde stored recurrence "
        "(a - 2) (by omega) (b + 2) (by omega)"
    ) in text
    assert "have h_1 := pde (a - 2) (by omega) b (by omega)" in text
    assert "  _ = D a b := by" in text
    assert ") -ih\n" in text and ") -h_1\n" in text
    assert "set_option maxHeartbeats 400000 in" in text
    assert script.holes == [] and script.restated == {}
    # every line of the calc says where it came from
    lines = {line for _, line in script.lines if line is not None}
    assert lines == {link.line for link in chain.links}


def test_the_outline_reads_as_the_design_prints_it() -> None:
    """``--steps`` for 1.1's chain: one row a link, the points lanky found."""
    chain, scope, _, _ = compressed_taylor_case()
    script = chain_script(chain, scope, claim=R[a, b] == D[a, b])
    rows = outline_text(script.outline, __file__)
    first = chain.line
    assert rows == [
        f"test_chains.py:{first}  R[a, b] == -R[a - 2, b + 2]  by recurrence, at (a - 2, b)",
        f"test_chains.py:{first + 1}          == -D[a - 2, b + 2]  by the claim at (a - 2, b + 2)",
        f"test_chains.py:{first + 2}          == D[a, b]           by pde, at (a - 2, b)",
    ]


def test_a_chain_that_ends_elsewhere_is_a_fact_of_the_case() -> None:
    """Ends that do not print as the claim's sides: ``have chain := calc ...``, then the claim."""
    chain, scope, _, _ = compressed_taylor_case()
    script = chain_script(chain, scope, claim=D[a, b] == R[a, b])
    text = script.text()
    assert text.startswith("have chain := calc R a b\n")
    assert "| exact chain.symm" in text
    assert "(-1 : ℝ) * chain" in text


def test_a_chain_that_is_not_about_the_claim_is_refused() -> None:
    """A chain of equations whose end is not the claim's other side is named, with both terms."""
    pytest.importorskip("sympy")
    chain, scope, _, _ = compressed_taylor_case()
    with pytest.raises(StepError, match=r"the chain ends at D\[a, b\]; the claim's right side is"):
        chain_script(chain, scope, claim=R[a, b] == D[a, b] + D[a - 2, b + 2])


def test_a_hole_is_a_sorry_at_a_recorded_line() -> None:
    """``by=...`` compiles to ``sorry``, its Python line recorded and its command line found."""
    chain, scope, claim, facts = compressed_taylor_case()
    # fmt: off
    holed = (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=facts["recurrence"])
        .equals(-D[a - 2, b + 2], by=...)
        .equals(D[a, b], by=facts["pde"])
    )
    # fmt: on
    script = chain_script(holed, scope, claim=R[a, b] == D[a, b])
    assert script.holes == [holed.links[1].line]
    (sorry,) = script.sorry_lines(10)
    assert script.lines[sorry - 10][0].strip() == "sorry"
    assert script.python_line(sorry, 10) == holed.links[1].line


def test_a_named_step_is_a_have() -> None:
    """1.2's ``recurrence = a[n].equals(..., by=ode)``: ``have recurrence : ...``."""
    recurrence, _, scope = line_taylor_case()
    script = named_script(recurrence, scope)
    text = script.text()
    assert text.startswith("have recurrence : a n = ")
    assert "have h := ode (n - 1) (by omega) (by omega)" in text
    assert "try have nz : ((n : Int) : ℂ) ≠ 0" in text
    assert "linear_combination" in text


def test_a_return_cites_the_named_step_and_the_claim() -> None:
    """1.2's ``return recurrence, claim(n - 1)``: the shift, the nonzero facts, one combination."""
    recurrence, ih, scope = line_taylor_case()
    named_script(recurrence, scope)
    goal = line_taylor.goal.body
    script = step_script(goal, (recurrence, ih), scope, 99)
    text = script.text()
    assert "have ih := Lanky.line_taylor.claim alpha beta a nonzero first_term ode (n - 1)" in text
    assert "have recurrence_" not in text
    assert "rw [show n.toNat = (n - 1).toNat + 1 by omega, pow_succ]" in text
    assert "((n - 1 : Int) : ℂ) ≠ 0" in text
    assert "linear_combination" in text and "recurrence + " in text and "* ih" in text


def test_shifts_and_nonzero_facts_follow_from_the_case() -> None:
    """A shift only where the case shows the lower exponent natural; a nonzero fact likewise."""
    scope = StepScope(types={"n": Nat, "x": Real}, facts=(n >= 1,))
    assert shift_lines(x**n, [Comparison(x ** (n - 1), "==", 1)], scope) == [
        "rw [show n.toNat = (n - 1).toNat + 1 by omega, pow_succ]"
    ]
    assert shift_lines(x**n, [Comparison(x ** (n - 2), "==", 1)], scope) == []
    assert shift_lines(
        x**n,
        [Comparison(x ** (n - 2), "==", 1)],
        StepScope(types={"n": Nat, "x": Real}, facts=(n >= 2,)),
    ) == ["rw [show n.toNat = (n - 2).toNat + 2 by omega, pow_add]"]
    lines = nonzero_lines([x / n, x / (n - 1)], scope)
    assert any("((n : Int) : ℝ) ≠ 0" in line for line in lines)
    assert not any("n - 1" in line for line in lines)
    assert nonzero_lines([x / n], StepScope(types={"n": Nat, "x": Real}, mathlib=False)) == []


def test_an_exponent_the_case_shows_natural_prints_inside_a_step() -> None:
    """``x ** (n - 1)`` is declined in a statement and ``(n - 1).toNat`` inside a step."""
    types = {"x": Real, "n": Nat}
    with pytest.raises(UnsupportedTerm, match="the exponent n - 1"):
        render_term(x ** (n - 1), types, mathlib=True)
    with proof_exponents(lambda exponent: True):
        assert render_term(x ** (n - 1), types, mathlib=True) == "x ^ (n - 1).toNat"
    scope = StepScope(types=types, facts=(n >= 1,))
    assert scope.render(x ** (n - 1)) == "x ^ (n - 1).toNat"


def test_a_theorem_is_cited_by_its_proved_text_or_its_printed_one() -> None:
    """A theorem cited restates the text its own command proved, where the check recorded one."""
    citation = citation_of(compressed_taylor)
    assert citation.kind == "theorem" and not citation.proved_text
    assert citation.restated == print_lean(compressed_taylor.term, mathlib=True)
    assert citation.fact_id == compressed_taylor.fact_id
    with proved_texts({compressed_taylor.fact_id: "∀ D R, True"}):
        proved = citation_of(compressed_taylor)
    assert proved.proved_text and proved.restated == "∀ D R, True"


def test_a_step_that_cites_a_theorem_says_what_the_declaration_takes() -> None:
    """A cited theorem is a hypothesis of the declaration, and the claim rests on its id."""

    @theorem
    def doubled(f: Fn[Nat, Real], m: Nat) -> f[m] + f[m] == 2 * f[m]:
        """A fact to cite."""

    g, i = Var("g"), Var("i")
    scope = StepScope(types={"g": Fn[Nat, Real], "i": Nat})
    script = step_script(Comparison(g[i] + g[i], "==", 2 * g[i]), (doubled,), scope, 7)
    assert set(script.restated) == {"doubled"}
    assert script.rests_on == [doubled.fact_id]
    assert "have h := doubled g i (by omega)" in script.text()


def test_a_theorem_cited_restates_the_theorems_its_own_proof_cited() -> None:
    """``B``'s ``as_cited`` takes ``C``: citing ``B`` restates both, and rests on both."""

    @theorem
    def premise(f: Fn[Nat, Real], m: Nat) -> f[m] == f[m]:
        """C."""

    @theorem
    def doubled(f: Fn[Nat, Real], m: Nat) -> f[m] + f[m] == 2 * f[m]:
        """B, proved citing C."""

    g, i = Var("g"), Var("i")
    goal = Comparison(g[i] + g[i], "==", 2 * g[i])
    texts = {
        doubled.fact_id: CitedText("doubled", "∀ f m, B", (premise.fact_id,)),
        premise.fact_id: CitedText("premise", "∀ f m, C"),
    }
    scope = StepScope(types={"g": Fn[Nat, Real], "i": Nat})
    with proved_texts(texts):
        script = step_script(goal, (doubled,), scope, 7)
    assert {name: cited.restated for name, cited in script.restated.items()} == {
        "doubled": "∀ f m, B",
        "premise": "∀ f m, C",
    }
    assert script.rests_on == [doubled.fact_id, premise.fact_id]
    missing = {doubled.fact_id: CitedText("doubled", "∀ f m, B", (premise.fact_id,))}
    with proved_texts(missing), pytest.raises(StepError, match="which has no proved text"):
        step_script(goal, (doubled,), StepScope(types=scope.types), 7)
    circle = {
        doubled.fact_id: CitedText("doubled", "B", (premise.fact_id,)),
        premise.fact_id: CitedText("premise", "C", (doubled.fact_id,)),
    }
    with proved_texts(circle), pytest.raises(StepError, match="go round in a circle"):
        step_script(goal, (doubled,), StepScope(types=scope.types), 7)


def test_citations_without_a_proved_text_raise_the_vacuity_question() -> None:
    """Printed texts are asked whether together they prove ``False``; proved ones are not."""
    printed = citation_of(compressed_taylor)
    question = vacuity_question("theorem:t.owner@1", [printed], "t.py:1")
    assert question.kind == "hypotheses" and question.term.body is False
    assert structurally_equal(question.term.guard, compressed_taylor.term)
    assert "compressed_taylor" in question.statement
    with proved_texts({compressed_taylor.fact_id: "∀ D R, True"}):
        proved = citation_of(compressed_taylor)
    assert vacuity_question("theorem:t.owner@1", [proved]) is None


# }}}


# {{{ the verdict on holes


def _response(errors=(), sorries=()):
    """A REPL response with errors and sorries at lines, as lean_interact gives them."""
    messages = [
        SimpleNamespace(severity="error", data=text, start_pos=SimpleNamespace(line=line))
        for line, text in errors
    ]
    found = [SimpleNamespace(start_pos=SimpleNamespace(line=line)) for line in sorries]
    return SimpleNamespace(messages=messages, sorries=found)


def test_a_proof_with_sorries_only_at_its_holes_closes_with_holes() -> None:
    """Closed; closed with holes; and failed for an error or a sorry lanky did not write."""
    assert holes_verdict(_response(), ()) == ("closed", [])
    assert holes_verdict(_response(sorries=[12]), [12]) == (CLOSED_WITH_HOLES, [])
    verdict, messages = holes_verdict(_response(sorries=[12, 14]), [12])
    assert verdict == "failed" and messages == [
        (14, "a sorry lanky did not write for a step left open")
    ]
    verdict, messages = holes_verdict(_response(errors=[(9, "linarith failed")]), ())
    assert verdict == "failed" and messages == [(9, "linarith failed")]


# }}}


# {{{ without Lean: each step drawn


@theorem
def squares_differ(u: Real, v: Real) -> (u + v) * (u - v) == u**2 - v**2:
    """A claim to draw the steps of."""


def test_each_link_is_drawn_and_a_wrong_one_is_caught_at_its_line() -> None:
    """Without Lean the links are claims drawn at points: a wrong link is refuted at its line."""
    u, v = Var("u"), Var("v")
    # fmt: off
    chain = (
        ((u + v) * (u - v))
        .equals(u * u - u * v + v * u - v * v)
        .equals(u**2 + v**2)
    )
    # fmt: on
    draws = draw_links(chain, list(squares_differ.variables))
    assert [draw.outcome for draw in draws] == ["tested", "refuted"]
    outcome, message = drawn_status("squares_differ", draws, __file__)
    assert outcome == "refuted"
    assert message.startswith(f"the step at test_chains.py:{chain.links[1].line}")
    right = ((u + v) * (u - v)).equals(u**2 - v**2)
    outcome, message = drawn_status("squares_differ", draw_links(right, [("u", Real), ("v", Real)]))
    assert outcome == "tested"
    assert message == (
        "the proof of squares_differ was tested step by step at drawn points, not checked by Lean"
    )


def test_a_link_over_a_family_that_cannot_be_drawn_leaves_the_claim_assumed() -> None:
    """1.2's family over ``Nat`` cannot be drawn: the claim reads assumed, and says why."""
    recurrence, _, _ = line_taylor_case()
    variables = [*line_taylor.variables, ("n", Nat)]
    draws = draw_links(recurrence, variables, [prop for _, prop in line_taylor.hypotheses])
    assert [draw.outcome for draw in draws] == ["undrawn"]
    outcome, message = drawn_status("line_taylor", draws)
    assert outcome == "undrawn"
    assert message.startswith("line_taylor reads assumed: ")
    assert "cannot tabulate a family over Nat" in message


# }}}


# {{{ with Lean: the design's 1.1 and 1.2, checked


def _parameters(thm) -> str:
    """The declaration's parameters, the hypotheses under their Python names."""
    parts = [f"({name} : {lean_type(sort, mathlib=True)})" for name, sort in thm.variables]
    parts += [f"({name} : {print_lean(prop, mathlib=True)})" for name, prop in thm.hypotheses]
    return " ".join(parts)


def compressed_taylor_lean(chain_text: str) -> str:
    """The check's T3, with its second case the chain lanky compiled."""
    return f"""set_option autoImplicit false in
theorem Lanky.compressed_taylor.claim {_parameters(compressed_taylor)}
    (a : Int) (ha : 0 ≤ a) (b : Int) (hb : 0 ≤ b) : R a b = D a b := by
  by_cases case_1 : a < 2
  · exact stored a ha b hb case_1
  · {chain_text.lstrip()}
termination_by a.toNat
decreasing_by omega
"""


def line_taylor_lean(case_text: str) -> str:
    """The check's T7, with its second case what lanky compiled."""
    return f"""set_option autoImplicit false in
theorem Lanky.line_taylor.claim {_parameters(line_taylor)}
    (n : Int) (hn0 : 0 ≤ n) (hn1 : n ≥ 1) :
    a n = (-1) * ((-1) * beta / alpha) ^ n.toNat / (n : ℂ) := by
  by_cases case_1 : n = 1
  · subst case_1
    linear_combination (norm := ((try push_cast) <;> field_simp <;> ring1)) (1 / alpha) * first_term
  · {case_text.lstrip()}
termination_by n.toNat
decreasing_by omega
"""


def _first_line(source: str, script) -> int:
    """The line of the command, counted from 1, that the script's first line is on."""
    first = script.lines[0][0]
    for number, line in enumerate(source.splitlines(), start=1):
        if line.endswith(first) and line.strip().lstrip("· ") == first.strip():
            return number
    raise AssertionError("the script is not in the command")


@pytest.fixture(scope="module")
def mathlib_session(mathlib_project):
    """A Lean session with Mathlib, or a skip that says why not."""
    if mathlib_project is None or os.environ.get("LANKY_LEAN_DISABLE"):
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but there is no Mathlib session")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    timeout = float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "180"))
    oracle = LeanOracle(session=LeanSession(timeout, mathlib=mathlib_project))
    available, reason = oracle.availability()
    if not available or not oracle.session.start():
        pytest.skip(f"no Mathlib session here: {reason or oracle.session.error}")
    yield oracle.session
    oracle.session.close()


def test_compressed_taylor_by_its_chain_closes_in_lean(mathlib_session) -> None:
    """1.1: the chain lanky compiled closes the case, and a hole in it closes with holes."""
    chain, scope, _, facts = compressed_taylor_case()
    script = chain_script(chain, scope, claim=R[a, b] == D[a, b])
    source = compressed_taylor_lean(script.text(indent=4))
    verdict, messages, answered = mathlib_session.answer_with_holes(source)
    assert answered and (verdict, messages) == ("closed", [])

    # fmt: off
    holed = (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=facts["recurrence"])
        .equals(-D[a - 2, b + 2], by=...)
        .equals(D[a, b], by=facts["pde"])
    )
    # fmt: on
    script = chain_script(holed, scope, claim=R[a, b] == D[a, b])
    source = compressed_taylor_lean(script.text(indent=4))
    holes = script.sorry_lines(_first_line(source, script))
    verdict, messages, _ = mathlib_session.answer_with_holes(source, holes)
    assert (verdict, messages) == (CLOSED_WITH_HOLES, [])


def test_a_wrong_step_fails_at_its_line(mathlib_session) -> None:
    """The claim at ``(a - 2, b + 3)`` does not give the step; Lean says so at that link."""
    chain, scope, claim, facts = compressed_taylor_case()
    # fmt: off
    wrong = (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=facts["recurrence"])
        .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 3))
        .equals(D[a, b], by=facts["pde"])
    )
    # fmt: on
    script = chain_script(wrong, scope, claim=R[a, b] == D[a, b])
    source = compressed_taylor_lean(script.text(indent=4))
    verdict, messages, _ = mathlib_session.answer_with_holes(source)
    assert verdict == "failed" and messages
    first = _first_line(source, script)
    lines = {script.python_line(line, first) for line, _ in messages if line is not None}
    assert wrong.links[1].line in lines


def test_line_taylor_by_its_named_step_closes_in_lean(mathlib_session) -> None:
    """1.2: the named step and the return lanky compiled close the case, with clean axioms."""
    recurrence, ih, scope = line_taylor_case()
    named = named_script(recurrence, scope)
    final = step_script(line_taylor.goal.body, (recurrence, ih), scope, 99)
    body = named.text(indent=4).lstrip() + "\n" + final.text(indent=4)
    source = line_taylor_lean(body) + "\n#print axioms Lanky.line_taylor.claim\n"
    verdict, messages, answered = mathlib_session.answer_with_holes(source)
    assert answered and (verdict, messages) == ("closed", [])


# }}}


# {{{ core Lean: a claim over integers alone


@theorem
def compressed_taylor_over_integers(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """1.1 over integer tables: core Lean checks it, with no Mathlib."""


@pytest.fixture(scope="module")
def core_session():
    """A core Lean session, or a skip that says why not."""
    if os.environ.get("LANKY_LEAN_DISABLE"):
        if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_TEST_REQUIRED is set, but the Lean oracle is disabled")
        pytest.skip("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    timeout = float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120"))
    oracle = LeanOracle(session=LeanSession(timeout))
    available, reason = oracle.availability()
    if not available or not oracle.session.start():
        if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
            pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason or oracle.session.error}")
        pytest.skip(f"no Lean session here: {reason or oracle.session.error}")
    yield oracle.session
    oracle.session.close()


def test_a_chain_over_integers_closes_in_core_lean(core_session) -> None:
    """Without Mathlib a chain over integers is checked by ``omega``, its indices normalized."""
    facts = hypotheses(compressed_taylor_over_integers)
    claim = Claim(
        Citation(
            "the claim",
            compressed_taylor_over_integers.goal,
            "Lanky.compressed_taylor_over_integers.claim D R pde stored recurrence",
            kind="claim",
        )
    )
    # fmt: off
    chain = (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=facts["recurrence"])
        .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))
        .equals(D[a, b], by=facts["pde"])
    )
    # fmt: on
    types = {**dict(compressed_taylor_over_integers.variables), "a": Nat, "b": Nat}
    scope = StepScope(types=types, facts=(LogicalNot(a < 2),), mathlib=False)
    script = chain_script(chain, scope, claim=R[a, b] == D[a, b])
    assert "omega" in script.text() and "linear_combination" not in script.text()
    parameters = " ".join(
        [
            f"({name} : {lean_type(sort)})"
            for name, sort in compressed_taylor_over_integers.variables
        ]
        + [
            f"({name} : {print_lean(prop)})"
            for name, prop in compressed_taylor_over_integers.hypotheses
        ]
    )
    source = f"""set_option autoImplicit false in
theorem Lanky.compressed_taylor_over_integers.claim {parameters}
    (a : Int) (ha : 0 ≤ a) (b : Int) (hb : 0 ≤ b) : R a b = D a b := by
  by_cases case_1 : a < 2
  · exact stored a ha b hb case_1
  · {script.text(indent=4).lstrip()}
termination_by a.toNat
decreasing_by omega
"""
    verdict, messages, answered = core_session.answer_with_holes(source)
    assert answered and (verdict, messages) == ("closed", [])


# }}}
