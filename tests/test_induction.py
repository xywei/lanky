"""Induction over families: the search for each case's certificate, and the script around it.

Nothing here needs Lean. The search (:mod:`lanky.induction`) is sympy's, so
its tests skip without sympy, and the script is text, tested against the
lines it must have. Lean checks the certificates in ``tests/test_mathlib.py``,
where Mathlib is.
"""

from __future__ import annotations

import pytest

from lanky import theorem
from lanky.induction import (
    Case,
    Lemma,
    Use,
    domain_conditions,
    find_certificate,
    lemma_of,
    substitute,
)
from lanky.lean import domain_guards, number_type, render_term, statement_of
from lanky.ledger import Fact, Status
from lanky.oracles.lean import (
    BASE_TACTICS,
    COMBINATION_NORM,
    LeanOracle,
    decline,
    family_induction_scripts,
    tactic_ladder,
    use_certificate,
)
from lanky.plugins import registry
from lanky.prelude import Fin, Fn, Nat, Real
from lanky.terms import Comparison, Forall, Var, render, structurally_equal

# {{{ claims for every order


@theorem
def laplace(
    D: Fn[Nat, Fn[Nat, Real]],
    R: Fn[Nat, Fn[Nat, Real]],
    pde: all(D(a + 2)(b) + D(a)(b + 2) == 0 for a in Nat for b in Nat),
    stored: all(R(a)(b) == D(a)(b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2)(b) == -R(a)(b + 2) for a in Nat for b in Nat),
) -> all(R(a)(b) == D(a)(b) for a in Nat for b in Nat):
    """The compressed Taylor reconstruction of a harmonic function's derivatives."""


@theorem
def helmholtz(
    k: Real,
    D: Fn[Nat, Fn[Nat, Real]],
    R: Fn[Nat, Fn[Nat, Real]],
    pde: all(D(a + 2)(b) + D(a)(b + 2) + k**2 * D(a)(b) == 0 for a in Nat for b in Nat),
    stored: all(R(a)(b) == D(a)(b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2)(b) == -R(a)(b + 2) - k**2 * R(a)(b) for a in Nat for b in Nat),
) -> all(R(a)(b) == D(a)(b) for a in Nat for b in Nat):
    """The same for Helmholtz's PDE, whose multipliers mention ``k``."""


@theorem
def telescoping(
    f: Fn[Nat, Real],
    start: f(0) == 0,
    step: all(f(n + 1) == f(n) + 1 / ((n + 1) * (n + 2)) for n in Nat),
) -> all(f(n) == n / (n + 1) for n in Nat):
    """A sum of ``1 / ((n + 1)(n + 2))``, whose step is a rational-function identity."""


@theorem
def wrong_sign(
    D: Fn[Nat, Fn[Nat, Real]],
    R: Fn[Nat, Fn[Nat, Real]],
    pde: all(D(a + 2)(b) + D(a)(b + 2) == 0 for a in Nat for b in Nat),
    stored: all(R(a)(b) == D(a)(b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2)(b) == R(a)(b + 2) for a in Nat for b in Nat),
) -> all(R(a)(b) == D(a)(b) for a in Nat for b in Nat):
    """False: the recurrence has lost its sign, so ``R(2)(0)`` is ``D(0)(2)``, not ``D(2)(0)``."""


@theorem
def helmholtz_from_zero(
    k: Real,
    D: Fn[Nat, Fn[Nat, Real]],
    R: Fn[Nat, Fn[Nat, Real]],
    pde: all(D(a + 2)(b) + D(a)(b + 2) + k**2 * D(a)(b) == 0 for a in Nat for b in Nat),
    stored: all(R(a)(b) == D(a)(b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2)(b) == -R(a)(b + 2) - k**2 * R(a)(b) for a in Nat for b in Nat),
) -> all(0 == R(a)(b) - D(a)(b) for a in Nat for b in Nat):
    """Helmholtz again, with the goal's left side a literal, which says nothing of its ring."""


@theorem
def shadowing(
    a: Nat,
    f: Fn[Nat, Real],
    start: f(0) == a,
    step: all(f(n + 1) == f(n) for n in Nat),
) -> all(f(a) == a for a in Nat):
    """The goal's ``a`` hides the parameter ``a`` that ``start`` is about, once it is introduced."""


@theorem
def increasing(
    f: Fn[Nat, Nat], step: all(f(n + 1) >= f(n) for n in Nat)
) -> all(f(n + 1) >= f(n) for n in Nat):
    """An order, not an equation: no linear combination is a proof of it."""


@theorem
def shifting(
    f: Fn[Nat, Fn[Nat, Real]],
    start: all(f(a)(0) == a for a in Nat),
    step: all(f(a)(n + 1) == f(a + 1)(n) for a in Nat for n in Nat),
) -> all(f(a)(n) == a + n for a in Nat for n in Nat):
    """Induced on ``n``, whose step takes the hypothesis at ``a + 1``: ``a`` is generalized too."""


@theorem
def counting(
    n: Nat,
    f: Fn[Nat, Fn[Nat, Real]],
    start: all(f(0)(b) == b for b in Nat),
    step: all(f(i + 1)(b) == f(i)(b) + 1 for i in Nat for b in Nat),
) -> all(f(i)(b) == i + b for i in Fin[n] for b in Nat):
    """Induced on a point of ``Fin[n]``, whose bound comes before the later ``b``."""


@pytest.fixture
def searching():
    """sympy, which the search needs; skipped without it."""
    return pytest.importorskip("sympy")


def _statement(claim, mathlib: bool = True):
    return statement_of(claim.term, claim.__name__, mathlib=mathlib)


# }}}


# {{{ the search


def test_the_search_finds_the_step_of_the_compressed_taylor_reconstruction(searching) -> None:
    """The recurrence at ``k``, the PDE at ``k`` and the hypothesis at ``k``, two ``y``'s up."""
    (script,) = family_induction_scripts(_statement(laplace))
    lines = script.splitlines()
    # only the order and its guard are introduced before the induction, so the
    # induction hypothesis takes the rest as the statement binds it
    assert lines[:6] == [
        "intro a hd",
        "obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hd",
        "clear hd",
        "induction a using Nat.strong_induction_on with",
        "| _ a ih =>",
        "  intro b hd_1",
    ]
    assert lines[6] == "  by_cases hbase : a < 2"
    # below the step, the stored derivatives are the derivatives, for every order there at once
    assert lines[7] == (
        f"  · linear_combination (norm := {COMBINATION_NORM}) h1 a (by omega) b (by omega) "
        "(by omega)"
    )
    assert lines[8] == "  · obtain ⟨k, rfl⟩ : ∃ k : Nat, a = k + 2 := ⟨a - 2, by omega⟩"
    step = lines[9]
    assert step.startswith(f"    linear_combination (norm := {COMBINATION_NORM}) h2 k ")
    assert "h2 k (by omega) b (by omega)" in step
    assert "- h0 k (by omega) b (by omega)" in step
    assert "- ih k (by omega) (b + 2) (by omega)" in step
    assert len(lines) == 10


def test_a_multiplier_can_be_an_expression_in_the_statements_variables(searching) -> None:
    """Helmholtz's step takes the hypothesis at ``(k, b)`` too, times ``-k**2``."""
    (script,) = family_induction_scripts(_statement(helmholtz))
    step = script.splitlines()[-1]
    assert "+ ((-1) * k ^ 2 : ℝ) * (ih k_1 (by omega) b (by omega))" in step
    assert "- ih k_1 (by omega) (b + 2) (by omega)" in step


def test_a_multiplier_is_in_the_ring_of_the_equation_whichever_side_says_so(searching) -> None:
    """``0 == R(a)(b) - D(a)(b)`` is an equation of reals, though its left side is an integer."""
    (script,) = family_induction_scripts(_statement(helmholtz_from_zero))
    assert "k ^ 2 : ℝ) * (ih k_1 (by omega) b (by omega))" in script.splitlines()[-1]


def test_the_variables_before_the_order_are_generalized_too(searching) -> None:
    """The step at ``n + 1`` takes the hypothesis at ``a + 1``, so it must hold at every ``a``."""
    (script,) = family_induction_scripts(_statement(shifting))
    lines = script.splitlines()
    assert lines[:7] == [
        "intro a hd n hd_1",
        "obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hd_1",
        "clear hd_1",
        "revert a hd",
        "induction n using Nat.strong_induction_on with",
        "| _ n ih =>",
        "  intro a hd",
    ]
    assert lines[-1].endswith("h1 a (by omega) k (by omega) + ih k (by omega) (a + 1) (by omega)")


def test_the_orders_own_guards_come_before_the_later_variables(searching) -> None:
    """``i < n`` is printed right after ``i``, so the hypothesis takes it before ``b``.

    The step uses the hypothesis at ``k``, which needs ``k < n``: the search
    reads it off the bound of the order, ``k + 1 <= n - 1``.
    """
    (script,) = family_induction_scripts(_statement(counting))
    lines = script.splitlines()
    assert lines[0] == "intro i hd"
    assert "revert" not in script
    assert lines[5] == "  intro hd_1 b hd_2"
    assert lines[-1].endswith("+ ih k (by omega) (by omega) b (by omega)")


def test_a_goal_variable_that_hides_a_parameter_is_not_induced_on(searching) -> None:
    """After ``intro a``, ``f 0 = a`` is about the hidden parameter, not the goal's ``a``."""
    assert family_induction_scripts(_statement(shadowing)) == []


def test_a_base_case_is_taken_one_order_at_a_time_when_it_has_to_be(searching) -> None:
    """``f(0) == 0`` says nothing about ``f(n)`` for an ``n`` below 1 until ``n`` is 0."""
    (script,) = family_induction_scripts(_statement(telescoping))
    lines = script.splitlines()
    assert lines[5] == "  by_cases hbase : n < 1"
    assert lines[6] == "  · interval_cases n"
    assert lines[7] == f"    · linear_combination (norm := {COMBINATION_NORM}) h0"
    assert lines[-1].endswith("h1 k (by omega) + ih k (by omega)")


def test_a_false_claim_has_no_certificate(searching) -> None:
    """The recurrence with its sign lost leaves no combination that is the goal."""
    assert family_induction_scripts(_statement(wrong_sign)) == []


def test_only_an_equation_between_families_in_mathlib_is_induced_on(searching) -> None:
    assert family_induction_scripts(_statement(increasing)) == []
    # core Lean has no linear_combination, nor a real number to state laplace with
    statement = _statement(laplace)
    statement.mathlib = False
    assert family_induction_scripts(statement) == []


def _successor_case(below: int) -> Case:
    """``f(k + 1) == 0``, with an induction hypothesis for the orders below ``k + below``."""
    f, k, m = Var("f"), Var("k"), Var("m")
    hypothesis = Lemma(
        "ih",
        ((m, Nat),),
        (("value", "m"), ("proof", Comparison(m, "<", k + below))),
        Comparison(f(m), "==", 0),
        conditions=(Comparison(0, "<=", m),),
    )
    return Case(
        name="step",
        goal=Comparison(f(k + 1), "==", 0),
        lemmas=(hypothesis,),
        variables={"f": Fn[Nat, Real], "k": Nat},
        bounds={"k": (0, None)},
        families=frozenset({"f"}),
    )


def test_the_induction_hypothesis_is_used_only_below_the_order_proved(searching) -> None:
    """At ``k + 1`` itself it would be the goal, and a use there would prove anything."""
    assert find_certificate(_successor_case(1)) is None
    (use,) = find_certificate(_successor_case(2))
    assert use.lemma == "ih"
    assert render(use.arguments[0]) == "k + 1"
    assert use.multiplier == 1


def test_a_hypothesis_is_not_used_outside_the_domain_it_quantifies(searching) -> None:
    """``f(0)`` is no instance of ``f(n + 1)`` for a natural ``n``: it would need ``n = -1``."""
    f, n = Var("f"), Var("n")
    successor = lemma_of("h0", Forall(((n, Nat),), Comparison(f(n + 1), "==", 0)))
    case = Case(
        name="0",
        goal=Comparison(f(0), "==", 0),
        lemmas=(successor,),
        variables={"f": Fn[Nat, Real]},
        bounds={},
        families=frozenset({"f"}),
    )
    assert find_certificate(case) is None


def test_a_lemmas_binder_is_never_taken_for_a_name_of_the_case(searching) -> None:
    """The binder ``n`` and a variable of the case named ``n__0`` are two things."""
    f, n, k = Var("f"), Var("n"), Var("n__0")
    step = lemma_of("h0", Forall(((n, Nat),), Comparison(f(n + 1), "==", f(n))))
    case = Case(
        name="step",
        goal=Comparison(f(k + 1), "==", f(k)),
        lemmas=(step,),
        variables={"f": Fn[Nat, Real], "n__0": Nat},
        bounds={"n__0": (0, None)},
        families=frozenset({"f"}),
    )
    (use,) = find_certificate(case)
    assert use.lemma == "h0"
    assert render(use.arguments[0]) == "n__0"


def test_without_sympy_the_search_finds_nothing(monkeypatch) -> None:
    import lanky.induction

    monkeypatch.setattr(lanky.induction, "_sympy", lambda: None)
    assert find_certificate(_successor_case(2)) is None
    assert family_induction_scripts(_statement(laplace)) == []


def test_a_lemmas_premises_are_the_ones_lean_takes(searching) -> None:
    """A binder, its domain's guards, then the guard of the generator, as the printer has them."""
    statement = _statement(laplace)
    stored = statement.hypothesis_terms[1]
    lemma = lemma_of("h1", stored)
    assert [kind for kind, _ in lemma.premises] == ["value", "proof", "value", "proof", "proof"]
    assert [render(term) for kind, term in lemma.premises if kind == "proof"] == [
        "0 <= a",
        "0 <= b",
        "a < 2",
    ]
    printed = "∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → a < 2 → R a b = D a b"
    assert statement.hypotheses[1][1] == printed
    i, m = Var("i"), Var("m")
    for domain in (Nat, Fin[m], Fin[m] & (i > 0)):
        assert len(domain_conditions(i, domain)) == len(domain_guards(i, domain))
    # an order or an existential is no lemma
    assert lemma_of("h", Forall(((i, Nat),), Comparison(i, ">=", 0))) is None


def test_substitution_leaves_a_bound_name_alone() -> None:
    i, j, n = Var("i"), Var("j"), Var("n")
    term = Forall(((i, Fin[n]),), Comparison(i + j, "<", n))
    replaced = substitute(term, {"i": 5, "j": n, "n": 3})
    assert render(replaced) == render(Forall(((i, Fin[3]),), Comparison(i + n, "<", 3)))


# }}}


# {{{ the certificate hook, and the ladder


def test_a_certificate_from_the_hook_is_what_the_script_combines(searching) -> None:
    """A finder that knows the multipliers hands them over; a wrong one is written as it is."""
    statement = _statement(laplace)
    k, b, a = Var("k"), Var("b"), Var("a")

    def from_the_pde(case: Case):
        if (case.order, case.step) != ("a", 2):
            return None
        if case.name == "base":
            return (Use("h1", (a, b)),)
        # wrong on purpose: the induction hypothesis added rather than taken away
        return (Use("h2", (k, b)), Use("h0", (k, b), -1), Use("ih", (k, b + 2), 1))

    (script,) = family_induction_scripts(statement, from_the_pde)
    # the uses taken once come first, so that the combination opens with no sign
    assert script.splitlines()[-1].endswith(
        "h2 k (by omega) b (by omega) + ih k (by omega) (b + 2) (by omega) "
        "- h0 k (by omega) b (by omega)"
    )


def test_a_hook_that_answers_for_every_step_gives_a_script_for_each(searching) -> None:
    """Lean judges: the script for the step the hook did not mean fails, and the next is tried."""
    statement = _statement(laplace)
    k, b, a = Var("k"), Var("b"), Var("a")
    steps = []

    def every_step(case: Case):
        if case.order != "a":
            return None
        steps.append((case.step, case.name))
        if case.name == "base":
            return (Use("h1", (a, b)),)
        return (Use("h2", (k, b)), Use("h0", (k, b), -1), Use("ih", (k, b + 2), -1))

    first, second = family_induction_scripts(statement, every_step)
    assert "by_cases hbase : a < 1" in first
    assert "by_cases hbase : a < 2" in second
    assert steps == [(1, "base"), (1, "step"), (2, "base"), (2, "step")]
    # the ladder keeps both, in that order
    steps.clear()
    ladder = tactic_ladder(statement, every_step)
    assert ladder[len(BASE_TACTICS) : len(BASE_TACTICS) + 2] == [first, second]


def test_a_hook_that_finds_nothing_or_fails_gives_no_script(searching) -> None:
    statement = _statement(laplace)
    assert family_induction_scripts(statement, lambda case: None) == []

    def broken(case: Case):
        raise RuntimeError("the hook is broken")

    assert family_induction_scripts(statement, broken) == []
    # a use of a lemma the case does not have, or at the wrong number of values
    assert family_induction_scripts(statement, lambda case: (Use("h9", ()),)) == []
    assert family_induction_scripts(statement, lambda case: (Use("h1", ()),)) == []


def test_the_family_induction_comes_after_the_core_attempts(searching) -> None:
    ladder = tactic_ladder(_statement(laplace))
    assert ladder[: len(BASE_TACTICS)] == list(BASE_TACTICS)
    assert ladder[len(BASE_TACTICS)].startswith("intro a hd\nobtain")
    assert "linear_combination" in ladder[len(BASE_TACTICS)]


def test_use_certificate_hands_the_oracle_a_finder(monkeypatch) -> None:
    oracle = LeanOracle()
    monkeypatch.setattr(registry, "oracles", [oracle])

    def finder(case: Case):
        return None

    use_certificate(laplace, finder)
    assert oracle.certificates == {laplace.fact_id: finder}


# }}}


# {{{ declining a claim


def test_a_declined_claim_is_returned_with_the_reason_and_no_lean() -> None:
    """No session is opened: the fact goes back as it came, saying why."""
    oracle = LeanOracle()
    fact = laplace.fact()
    oracle.declines[fact.id] = "this claim is the CAS oracle's"
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.provenance["declined"] == "lean: this claim is the CAS oracle's"
    assert result.provenance["lean_declined"] == "this claim is the CAS oracle's"
    assert oracle._sessions == {}


def test_decline_names_the_claim_as_use_tactic_does(monkeypatch) -> None:
    oracle = LeanOracle()
    monkeypatch.setattr(registry, "oracles", [oracle])
    decline(laplace, "a reason")
    fact = Fact(id="theorem:elsewhere@1", kind="theorem", statement="x")
    decline(fact, "another")
    decline("an:id", "a third")
    assert oracle.declines == {
        laplace.fact_id: "a reason",
        "theorem:elsewhere@1": "another",
        "an:id": "a third",
    }
    with pytest.raises(TypeError, match="needs the reason"):
        decline(laplace, " ")
    monkeypatch.setattr(registry, "oracles", [])
    with pytest.raises(LookupError, match="no Lean oracle"):
        decline(laplace, "a reason")


# }}}


# {{{ printing a term inside a proof


def test_a_term_inside_a_proof_is_printed_with_the_names_around_it() -> None:
    k, x, f = Var("k"), Var("x"), Var("f")
    types = {"k": Nat, "x": Real, "f": Fn[Nat, Nat]}
    assert render_term(k + 2, types, mathlib=True) == "k + 2"
    assert render_term(k + 2, types, mathlib=True, atomic=True) == "(k + 2)"
    assert render_term(k, types, mathlib=True, atomic=True) == "k"
    assert render_term(1 / (k + 1), types, mathlib=True) == "(1 : ℝ) / (k + 1)"
    # a family's natural value is cast, as in a statement
    assert render_term(f(k) + 1, types, mathlib=True) == "(f k : Int) + 1"
    assert render_term(k, types, mathlib=True, shadowed={"Int"}) == "k"
    assert render_term(f(k), types, mathlib=True, shadowed={"Int"}) == "(f k : _root_.Int)"
    assert number_type(k + 1, types, mathlib=True) == "Int"
    assert number_type(x * k, types, mathlib=True) == "ℝ"
    assert number_type(1 / (k + 1), types, mathlib=True) == "ℝ"
    assert structurally_equal(substitute(k + 2, {"k": x}), x + 2)


# }}}
