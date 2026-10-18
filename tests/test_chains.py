"""Chains and citations of written proofs: the surface, the matcher, what the compiler adds.

The surface and the matcher are Python and need no Lean: there is one matcher
(:mod:`lanky.matching`), which lines up a fact a proof leaves uncalled with the
step it supports, and one :class:`lanky.citations.Citation`, which records
every fact cited, by a proof or by a plugin's part. The Lean a written proof
compiles to (:mod:`lanky.proofs.compile`, the one step compiler) is checked as
text for the design's 1.1 and 1.2, written here as the design writes them,
and, where a Lean with Mathlib is installed, by Lean itself.
"""

from __future__ import annotations

import os

import pytest

from lanky import theorem
from lanky.chains import Chain, ChainError, combined_relation
from lanky.citations import (
    Citation,
    CitedText,
    Premise,
    Proved,
    ProvedTexts,
    closed_with,
    premises_of,
    proved_texts,
    satisfiable,
    vacuity_question,
)
from lanky.induction import Lemma
from lanky.lean import UnsupportedTerm, print_lean, proof_exponents, render_term
from lanky.matching import (
    FamilyValue,
    NoSinglePoint,
    candidate_points,
    higher_order_value,
    implied,
    instantiate,
    same,
    single_point,
    touches,
)
from lanky.prelude import Complex, Fin, Fn, Int, Nat, Real
from lanky.proofs import compile_proof, trace_proof
from lanky.proofs.cases import shape_of
from lanky.proofs.compile import _Scope, cited_text, nonzero_lines, shift_lines
from lanky.proofs.report import verdict
from lanky.proofs.trace import ClaimDef, Given
from lanky.terms import (
    Comparison,
    LogicalNot,
    Sum,
    Var,
    log,
    render,
    structurally_equal,
)

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
    """The design's 1.1, its statement as l2p.py has it, and its proof by a chain."""

    def claim(a, b):
        if a < 2:
            return stored
        return (
            R[a, b]
            .equals(-R[a - 2, b + 2], by=recurrence)
            .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))
            .equals(D[a, b], by=pde)
        )

    return claim


@theorem
def line_taylor(
    alpha: Complex,
    beta: Complex,
    a: Fn[Nat, Complex],
    nonzero: alpha != 0,
    first_term: alpha * a[1] == beta,
    ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
) -> all(a[n] == -((-beta / alpha) ** n) / n for n in Nat if n >= 1):
    """The design's 1.2, with the coefficient written out, and its proof by a named step."""
    ratio = -beta / alpha

    def claim(n):
        if n == 1:
            return first_term
        recurrence = a[n].equals((n - 1) / n * ratio * a[n - 1], by=ode)
        return recurrence, claim(n - 1)

    return claim


@theorem
def doubled(f: Fn[Nat, Real], m: Nat) -> f[m] + f[m] == 2 * f[m]:
    """A fact to cite."""


def lemma(name: str, prop) -> Lemma:
    """A fact as the matcher takes it: its binders, the premises Lean applies it to, its body."""
    shape = shape_of(prop)
    return Lemma(name, shape.binders, shape.premises, shape.body)


def hypothesis(thm, name: str) -> Lemma:
    """A hypothesis of a theorem, as the matcher takes it."""
    return lemma(name, dict(thm.hypotheses)[name])


#: The scope of 1.1's second case, ``a >= 2``.
CT_TYPES = {**dict(compressed_taylor.variables), "a": Nat, "b": Nat}
CT_CASE = (LogicalNot(a < 2),)


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
    one = R[a, b].equals(D[a, b], by=doubled)
    assert one.links[0].reasons == (doubled,) and not one.links[0].hole
    two = R[a, b].equals(D[a, b], by=(doubled, doubled))
    assert len(two.links[0].reasons) == 2
    hole = R[a, b].equals(D[a, b], by=...)
    assert hole.links[0].hole and hole.holes == (hole.line,)
    with pytest.raises(ChainError, match="names no fact"):
        R[a, b].equals(D[a, b], by="pde")
    with pytest.raises(ChainError, match="takes no facts beside it"):
        R[a, b].equals(D[a, b], by=(doubled, ...))
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


# }}}


# {{{ one citation


def test_every_fact_a_proof_cites_is_one_citation() -> None:
    """1.1's chain cites hypotheses uncalled and the claim at a point, each a ``Citation``."""
    proof = trace_proof(compressed_taylor)
    stored, chain = proof.leaves
    (cited,) = stored.facts
    assert isinstance(cited, Citation) and isinstance(cited.source, Given)
    assert cited.values is None and cited.text() == "stored" and cited.fact == ""
    reasons = [fact for link in chain.chain.links for fact in link.facts]
    assert [type(reason) for reason in reasons] == [Citation, Citation, Citation]
    assert [reason.text() for reason in reasons] == ["recurrence", "claim(a - 2, b + 2)", "pde"]
    assert [reason.is_claim for reason in reasons] == [False, True, False]
    assert isinstance(reasons[1].source, ClaimDef)
    assert reasons[1].line == chain.chain.links[1].line


def test_a_part_cites_a_theorem_by_the_same_citation() -> None:
    """A plugin's part names the hypothesis that restates a theorem: the theorem, at a position."""
    cited = Citation(doubled, hypothesis=2)
    assert cited.name == "doubled" and cited.fact == doubled.fact_id
    assert cited.hypothesis == 2 and cited.values is None and not cited.is_claim


# }}}


# {{{ matching


def test_an_uncalled_fact_is_matched_by_solving_offsets() -> None:
    """1.1: ``recurrence`` and ``pde`` each fit their link at one point, ``(a - 2, b)``."""
    recurrence = hypothesis(compressed_taylor, "recurrence")
    first = [R[a, b], -R[a - 2, b + 2]]
    points = candidate_points(recurrence, first, CT_TYPES)
    assert len(points) == 3
    point = single_point(recurrence, first, CT_TYPES, CT_CASE, "recurrence")
    assert [render(value) for value in point] == ["a - 2", "b"]
    pde = hypothesis(compressed_taylor, "pde")
    last = [-D[a - 2, b + 2], D[a, b]]
    point = single_point(pde, last, CT_TYPES, CT_CASE, "pde")
    assert [render(value) for value in point] == ["a - 2", "b"]


def test_a_fact_that_gives_one_side_of_the_claim_is_at_the_point_that_lines_it_up() -> None:
    """``return stored`` fits the case's claim whole; ``pde`` alone touches it at two points."""
    claim = [R[a, b], D[a, b]]
    stored = hypothesis(compressed_taylor, "stored")
    point = single_point(stored, claim, CT_TYPES, (a < 2,), "stored")
    assert [render(value) for value in point] == ["a", "b"]
    pde = hypothesis(compressed_taylor, "pde")
    assert touches(pde, (a - 2, b), claim, CT_TYPES)
    with pytest.raises(NoSinglePoint, match="fits this step at 2 points") as raised:
        single_point(pde, claim, CT_TYPES, CT_CASE, "pde")
    assert raised.value.several
    # the point whose conditions the case shows first, the fix the message names
    assert [[render(value) for value in point] for point in raised.value.candidates] == [
        ["a - 2", "b"],
        ["a", "b - 2"],
    ]


def test_a_point_the_case_rules_out_is_dropped() -> None:
    """Touching at ``(a - 2, b)`` and ``(a, b - 2)``, with ``b < 2`` known, leaves the first."""
    pde = hypothesis(compressed_taylor, "pde")
    point = single_point(pde, [R[a, b], D[a, b]], CT_TYPES, (*CT_CASE, b < 2), "pde")
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
    a_ = Var("a")
    link = a_[n].equals((n - 1) / n * (-beta / alpha) * a_[n - 1])
    left, step = next(link.steps())
    types = {**dict(line_taylor.variables), "n": Nat}
    case = (n >= 1, LogicalNot(Comparison(n, "==", 1)))
    point = single_point(hypothesis(line_taylor, "ode"), [left, step.term], types, case, "ode")
    assert [render(value) for value in point] == ["n - 1"]


def test_no_single_point_asks_for_the_point() -> None:
    """A fact that fits nowhere, or at two points, names the fix: write the point."""
    fact = Lemma(
        "f",
        ((Var("i"), Nat),),
        (("value", "i"),),
        Comparison(R[Var("i"), 0], "==", R[Var("i"), 1]),
    )
    types = {"R": Fn[Nat, Nat, Real], "a": Nat}
    with pytest.raises(NoSinglePoint, match="no single point of f fits this step"):
        single_point(fact, [D[a, 0]], types, (), "f")
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


def test_an_index_with_two_unknowns_waits_for_one_of_them() -> None:
    """``R[x + y, y]`` against ``R[a, b]``: ``y`` from the second index, then ``x = a - b``."""
    xx, yy = Var("xx"), Var("yy")
    fact = Lemma(
        "f",
        ((xx, Nat), (yy, Nat)),
        (("value", "xx"), ("value", "yy")),
        Comparison(R[xx + yy, yy], "==", 0),
    )
    types = {"R": Fn[Nat, Nat, Real], "a": Nat, "b": Nat}
    (point,) = candidate_points(fact, [R[a, b]], types)
    assert [render(value) for value in point] == ["a - b", "b"]


def test_a_family_of_the_fact_binds_to_a_family_of_the_scope_first() -> None:
    """``f[j]`` against ``x[j]`` under a sum binds ``f`` to ``x``, not to ``j ↦ x[j]``."""
    f, m, j = Var("f"), Var("m"), Var("j")
    fact = Lemma(
        "total",
        ((f, Fn[Nat, Real]), (m, Nat)),
        (("value", "f"), ("value", "m")),
        Comparison(Sum(((j, Fin[m]),), f[j]), "==", 0),
    )
    types = {"x": Fn[Nat, Real], "n": Nat}
    (point,) = candidate_points(fact, [Sum(((k, Fin[n]),), Var("x")[k])], types)
    assert render(point[0]) == "x" and render(point[1]) == "n"


def test_same_reads_indices_as_integers() -> None:
    """``R[a - 2 + 2, b]`` is ``R[a, b]``."""
    assert same(R[(a - 2) + 2, b], R[a, b])
    assert not same(R[a - 2, b], R[a, b])


# }}}


# {{{ the Lean of a step, and what the compiler adds


def test_the_chain_of_compressed_taylor_is_a_calc() -> None:
    """1.1's chain prints as the check's T3: a ``calc``, each link with its fact at its point."""
    pytest.importorskip("sympy")  # the multipliers are found by sympy
    command = compile_proof(trace_proof(compressed_taylor), mathlib=True)
    text = command.source
    assert "  · calc R a b\n        = (-1) * R (a - 2) (b + 2) := by\n" in text
    assert "have f_2 := recurrence (a - 2) (by omega) b (by omega)" in text
    assert (
        "have f_3 := Lanky.compressed_taylor.claim D R (a - 2) (by omega) (b + 2) (by omega) "
        "pde stored recurrence"
    ) in text
    assert "have f_4 := pde (a - 2) (by omega) b (by omega)" in text
    assert "      _ = D a b := by" in text
    assert "(-1 : ℝ) * f_3\n" in text and "(-1 : ℝ) * f_4\n" in text
    assert "set_option maxHeartbeats 400000 in" in text
    assert command.holes == () and command.restated == ()
    assert command.summary == "induction on a, 2 cases, 4 steps"


def test_the_outline_reads_as_the_design_prints_it() -> None:
    """``--steps`` for 1.1: one row a link, the points the one matcher found."""
    command = compile_proof(trace_proof(compressed_taylor), mathlib=True)
    rows = [row[1:] for row in command.outline]
    assert rows == [
        ("if a < 2:", "R[a, b]", "==", "D[a, b]", "by stored, at (a, b)"),
        ("otherwise:", "R[a, b]", "==", "-R[a - 2, b + 2]", "by recurrence, at (a - 2, b)"),
        ("", "-R[a - 2, b + 2]", "==", "-D[a - 2, b + 2]", "by the claim at (a - 2, b + 2)"),
        ("", "-D[a - 2, b + 2]", "==", "D[a, b]", "by pde, at (a - 2, b)"),
    ]


def test_a_named_step_and_the_return_that_cites_it() -> None:
    """1.2: ``have recurrence : ...``, then the shift, the nonzero facts and one combination."""
    pytest.importorskip("sympy")  # the multipliers are found by sympy
    command = compile_proof(trace_proof(line_taylor), mathlib=True)
    text = command.source
    assert "  · have recurrence : a n = " in text
    assert "have f_2 := ode (n - 1) (by omega) (by omega)" in text
    assert "try have nz : ((n : Int) : ℂ) ≠ 0" in text
    assert (
        "have f_3 := Lanky.line_taylor.claim alpha beta a (n - 1) (by omega) nonzero first_term "
        "ode (by omega)"
    ) in text
    assert "rw [show n.toNat = (n - 1).toNat + 1 by omega, pow_succ]" in text
    assert "((n - 1 : Int) : ℂ) ≠ 0" in text
    assert "recurrence + " in text and "* f_3" in text
    assert command.summary == "induction on n, 2 cases, 3 steps, 1 named fact"


def test_shifts_and_nonzero_facts_follow_from_the_case() -> None:
    """A shift only where the case shows the lower exponent natural; a nonzero fact likewise."""
    scope = _Scope(types={"n": Nat, "x": Real}, facts=(n >= 1,))
    assert shift_lines(x**n, [Comparison(x ** (n - 1), "==", 1)], scope) == [
        "rw [show n.toNat = (n - 1).toNat + 1 by omega, pow_succ]"
    ]
    assert shift_lines(x**n, [Comparison(x ** (n - 2), "==", 1)], scope) == []
    assert shift_lines(
        x**n,
        [Comparison(x ** (n - 2), "==", 1)],
        _Scope(types={"n": Nat, "x": Real}, facts=(n >= 2,)),
    ) == ["rw [show n.toNat = (n - 2).toNat + 2 by omega, pow_add]"]
    lines = nonzero_lines([x / n, x / (n - 1)], scope)
    assert any("((n : Int) : ℝ) ≠ 0" in line for line in lines)
    assert not any("n - 1" in line for line in lines)
    assert nonzero_lines([x / n], _Scope(types={"n": Nat, "x": Real}, mathlib=False)) == []


def test_an_exponent_the_case_shows_natural_prints_inside_a_step() -> None:
    """``x ** (n - 1)`` is declined in a statement and ``(n - 1).toNat`` inside a step."""
    types = {"x": Real, "n": Nat}
    with pytest.raises(UnsupportedTerm, match="the exponent n - 1"):
        render_term(x ** (n - 1), types, mathlib=True)
    with proof_exponents(lambda exponent: True):
        assert render_term(x ** (n - 1), types, mathlib=True) == "x ^ (n - 1).toNat"
    scope = _Scope(types=types, facts=(n >= 1,))
    assert scope.render(x ** (n - 1)) == "x ^ (n - 1).toNat"


def test_a_family_bound_to_a_function_prints_as_a_fun() -> None:
    """``k ↦ r ** k``, the value of an ``f: Fn[Nat, Real]``, is ``(fun k => r ^ k.toNat)``."""
    scope = _Scope(types={"r": Real, "n": Nat}, facts=(n >= 1,))
    family = FamilyValue((k,), r**k)
    assert scope.render(family, atomic=True, sort=Fn[Nat, Real]) == "(fun k => r ^ k.toNat)"


# }}}


# {{{ citations by their proved texts


def test_a_theorem_is_cited_by_its_proved_text_or_its_printed_one() -> None:
    """A theorem cited restates the text its own command proved, where the check recorded one."""
    assert cited_text(compressed_taylor, True) == print_lean(compressed_taylor.term, mathlib=True)
    with proved_texts({compressed_taylor.fact_id: "∀ D R, True"}):
        assert cited_text(compressed_taylor, True) == "∀ D R, True"


def test_a_theorem_cited_restates_the_theorems_its_own_proof_cited() -> None:
    """``B``'s ``as_cited`` takes ``C``: citing ``B`` restates both, and a gap or circle refuses."""

    @theorem
    def premise(f: Fn[Nat, Real], m: Nat) -> f[m] == f[m]:
        """C."""

    texts = {
        doubled.fact_id: CitedText("doubled", "∀ f m, B", (premise.fact_id,)),
        premise.fact_id: CitedText("premise", "∀ f m, C"),
    }
    with proved_texts(texts):
        (found,) = premises_of(doubled.fact_id)
    assert isinstance(found, Premise)
    assert (found.__name__, found.fact_id, found.text) == ("premise", premise.fact_id, "∀ f m, C")
    missing = {doubled.fact_id: CitedText("doubled", "∀ f m, B", (premise.fact_id,))}
    with proved_texts(missing), pytest.raises(ValueError, match="which has no proved text"):
        premises_of(doubled.fact_id)
    circle = {
        doubled.fact_id: CitedText("doubled", "B", (premise.fact_id,)),
        premise.fact_id: CitedText("premise", "C", (doubled.fact_id,)),
    }
    with proved_texts(circle), pytest.raises(ValueError, match="go round in a circle"):
        premises_of(doubled.fact_id)


def test_a_text_is_kept_only_from_a_command_that_states_it() -> None:
    """The design's 3.5: the kept text is compared with the command that closed, its cache entry."""
    text = "∀ n : Int, 0 ≤ n → n ≥ 0"
    source = (
        "theorem Lanky.nonneg (n : Int) (h0 : 0 ≤ n) : n ≥ 0 := by\n  omega\n\n"
        f"theorem Lanky.nonneg.as_cited :\n    {text} :=\n  Lanky.nonneg\n"
    )
    assert closed_with(source, "Lanky.nonneg", text)
    assert not closed_with(source, "Lanky.nonneg", "∀ n : Int, n ≥ 0")
    assert not closed_with(source, "Lanky.other", text)
    written = "theorem Lanky.b.as_cited (c : ∀ x, C) :\n    ∀ y, B := by\n  exact Lanky.b c\n"
    assert closed_with(written, "Lanky.b", "∀ y, B")
    texts = ProvedTexts()
    term = compressed_taylor.term
    assert texts.record(Proved("t", "Lanky.nonneg", text, False, term, source=source))
    assert texts.get("t").text == text
    # a text the command that closed does not state is not kept, and what was kept goes
    assert not texts.record(Proved("t", "Lanky.nonneg", "∀ n, n ≥ 0", False, term, source=source))
    assert "t" not in texts


def test_a_restated_text_is_compared_with_the_kept_one() -> None:
    """A command that restates another text than the kept one is refused before Lean is asked."""
    texts = ProvedTexts()
    term = compressed_taylor.term
    texts.record(Proved("t", "Lanky.ct", "∀ D R, P", True, term))
    assert texts.mismatch([("ct", "t", "∀ D R, P", term)]) == ""
    assert texts.mismatch([("ct", "other", "anything", term)]) == ""
    said = texts.mismatch([("ct", "t", "∀ D R, Q", term)])
    assert said.startswith("the proof restates ct as a text other than the one its command proved")
    # a text kept for another statement of the theorem is no text of it
    assert texts.mismatch([("ct", "t", "∀ D R, Q", line_taylor.term)]) == ""


def test_citations_without_a_proved_text_raise_the_vacuity_question() -> None:
    """Printed texts are asked whether together they prove ``False``; proved ones are not."""
    question = vacuity_question("theorem:t.owner@1", [compressed_taylor], "t.py:1")
    assert question.kind == "hypotheses" and question.term.body is False
    assert structurally_equal(question.term.guard, compressed_taylor.term)
    assert "compressed_taylor" in question.statement
    with proved_texts({compressed_taylor.fact_id: "∀ D R, True"}):
        assert vacuity_question("theorem:t.owner@1", [compressed_taylor]) is None


def test_the_vacuity_question_is_asked_at_symbolic_points_in_a_case() -> None:
    """Inside an induction, the texts at ``(a - 2, b)``, ``a`` and ``b`` bound, the case assumed."""
    question = vacuity_question(
        "theorem:t.owner@1",
        [doubled],
        "t.py:1",
        [(doubled.fact_id, (Var("g"), a - 2))],
        variables=[(Var("g"), Fn[Nat, Real]), (a, Nat)],
        conditions=[LogicalNot(a < 2)],
        case="in the case at t.py:9",
    )
    assert question.id == "theorem:t.owner@1:citations@in-the-case-at-t-py-9"
    assert question.statement.endswith("are inconsistent in the case at t.py:9")
    (part,) = question.term.lean_obligation().parts
    assert [var.name for var, _ in part.term.binders] == ["g", "a"]
    assert render(part.term.guard).endswith(" and not (a < 2)")
    (instance,) = part.hints.instances
    assert instance.hypothesis == 0 and render(instance.arguments[1]) == "a - 2"
    # points with variables and no binders for them are not asked
    assert (
        vacuity_question(
            "theorem:t.owner@1", [doubled], variables=[(a, Nat)], conditions=[a >= 2]
        )
        is None
    )


def test_values_satisfying_a_case_are_looked_for_among_small_numbers() -> None:
    """And at the integers its conditions name; ``False`` is only that none was found."""
    assert satisfiable([(a, Nat), (b, Nat)], [LogicalNot(a < 2), b < 1])
    assert not satisfiable([(a, Nat)], [a < 0])
    assert satisfiable([(n, Int)], [n < 0])
    assert satisfiable([(Var("i"), Fin[n]), (n, Nat)], [Var("i") >= 1])
    assert not satisfiable([(alpha, Fn[Nat, Real])], [alpha[0] > 0])
    # a case only a large number reaches is met at the number it names (Codex, #182)
    assert satisfiable([(n, Nat)], [n == 100])
    assert satisfiable([(a, Nat), (b, Nat)], [a >= 10, b > a])
    assert not satisfiable([(n, Nat)], [n >= 100, n < 50])


# }}}


# {{{ with Lean: the design's 1.1 and 1.2, checked


@pytest.fixture(scope="module")
def mathlib_oracle(mathlib_project):
    """A Lean oracle with Mathlib, or a skip that says why not."""
    from lanky.oracles.lean import LeanOracle, LeanSession

    if mathlib_project is None or os.environ.get("LANKY_LEAN_DISABLE"):
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but there is no Mathlib session")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    timeout = float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "180"))
    oracle = LeanOracle(session=LeanSession(timeout, mathlib=mathlib_project))
    available, reason = oracle.availability()
    if not available or not oracle.session.start():
        pytest.skip(f"no Mathlib session here: {reason or oracle.session.error}")
    yield oracle
    oracle.session.close()


@pytest.mark.parametrize("thm", [compressed_taylor, line_taylor], ids=["1.1", "1.2"])
def test_the_designs_proofs_close_in_lean(mathlib_oracle, thm) -> None:
    """1.1 by its chain and 1.2 by its named step close, with the audit's three axioms."""
    proof = trace_proof(thm)
    command = compile_proof(proof, mathlib=True)
    record, said, _cached = mathlib_oracle.written(command.source)
    assert record is not None, said
    assert verdict(proof, command, record) == ("closed", [])


# }}}
