"""The Lean printer and the Lean oracle.

The printer is tested against golden source: what lanky sends to Lean is part of
the contract with the reader, not only with the elaborator, so the tests spell
the expected text out. The oracle is tested against a real Lean, and skips
cleanly when there is none, because a machine without Lean must still have a
green suite.
"""

from __future__ import annotations

import os
from collections.abc import Iterator

import pytest

from lanky import theorem
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    lean_type,
    print_lean,
    statement_of,
)
from lanky.ledger import Status
from lanky.oracles.lean import LeanOracle, LeanSession, tactic_ladder, use_tactic
from lanky.prelude import Bool, Fin, FinType, Fn, Int, Nat, Real
from lanky.terms import Abs, Exists, Forall, Sum, Var

# {{{ terms to print

n = Var("n")
i = Var("i")
a = Var("a")
b = Var("b")
f = Var("f")


# }}}


# {{{ types


def test_scalar_sorts_print_as_core_lean_types() -> None:
    assert lean_type(Nat) == "Nat"
    assert lean_type(Int) == "Int"
    assert lean_type(Bool) == "Bool"


def test_an_index_type_is_a_natural_number() -> None:
    # Fin[n] is not Fin n in Lean: its points are naturals and its bound is a
    # guard, so that omega sees linear arithmetic and no coercion.
    assert lean_type(FinType(n)) == "Nat"


def test_a_family_is_a_total_function() -> None:
    assert lean_type(Fn[Fin[n], Nat]) == "Nat → Nat"
    assert lean_type(Fn[Fin[n], Fn[Fin[n], Int]]) == "Nat → Nat → Int"


def test_real_has_no_core_lean_type() -> None:
    with pytest.raises(UnsupportedTerm):
        lean_type(Real)


# }}}


# {{{ expressions


def test_arithmetic_and_precedence() -> None:
    assert print_lean((a + b) * n) == "(a + b) * n"
    assert print_lean(a + b * n) == "a + b * n"
    assert print_lean(a**2 + 1) == "a ^ 2 + 1"
    assert print_lean(a // b) == "a / b"
    assert print_lean(a % b) == "a % b"


def test_subtraction_is_printed_as_written() -> None:
    # pymbolic has no subtraction node: a - b is a sum with (-1) * b in it, and
    # -1 is not a Nat, so the printer reads the negation back.
    assert print_lean(n - 1) == "n - 1"
    assert print_lean(a - b * n) == "a - b * n"


def test_comparisons_and_connectives() -> None:
    assert print_lean(a == b) == "a = b"
    assert print_lean(a != b) == "a ≠ b"
    assert print_lean(a <= b) == "a ≤ b"
    assert print_lean(a >= b) == "a ≥ b"
    assert print_lean((a < b) & (b < n)) == "a < b ∧ b < n"
    assert print_lean((a < b) | (b < n)) == "a < b ∨ b < n"
    assert print_lean(~(a < b)) == "¬(a < b)"


def test_a_family_is_applied_not_subscripted() -> None:
    assert print_lean(f(a)) == "f a"
    assert print_lean(f(a + 1)) == "f (a + 1)"
    assert print_lean(f[a]) == "f a"


def test_a_bounded_quantifier_is_a_guarded_nat_quantifier() -> None:
    assert print_lean(Forall(((i, FinType(n)),), f(i) <= n)) == "∀ i : Nat, i < n → f i ≤ n"
    assert print_lean(Forall(((i, Nat),), f(i) <= n)) == "∀ i : Nat, f i ≤ n"


def test_an_existential_conjoins_its_guard() -> None:
    assert print_lean(Exists(((i, FinType(n)),), f(i) == 0)) == "∃ i : Nat, i < n ∧ f i = 0"


def test_a_generator_guard_follows_the_last_binder() -> None:
    term = Forall(((a, FinType(n)), (b, FinType(n))), f(a) <= f(b), a <= b)
    assert print_lean(term) == "∀ a : Nat, a < n → ∀ b : Nat, b < n → a ≤ b → f a ≤ f b"


def test_a_reduction_needs_mathlib() -> None:
    with pytest.raises(UnsupportedTerm, match="Finset"):
        print_lean(Sum(((i, FinType(n)),), i))


def test_an_absolute_value_needs_mathlib() -> None:
    with pytest.raises(UnsupportedTerm, match="Mathlib"):
        print_lean(Abs(a))


def test_true_division_needs_a_field() -> None:
    with pytest.raises(UnsupportedTerm, match="field"):
        print_lean(a / b)


# }}}


# {{{ statements


@theorem
def commutes(x: Nat, y: Nat) -> x + y == y + x:
    """Addition on the naturals commutes."""


@theorem
def below(m: Nat, j: Fin[m]) -> j < m + 1:
    """A point of an index type is below the next bound."""


@theorem
def scan_monotone(
    size: Nat,
    cnt: Fn[Fin[size], Nat],
    off: Fn[Fin[size + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
) -> all(off(p) <= off(q) for p in Fin[size + 1] for q in Fin[size + 1] if p <= q):
    """The offsets of an exclusive scan over counts are monotone."""


@theorem
def gauss(size: Nat) -> 2 * sum(k for k in Fin[size + 1]) == size * (size + 1):
    """Gauss's schoolboy sum, which core Lean cannot even state."""


def test_a_statement_becomes_lean_binders_and_hypotheses() -> None:
    statement = statement_of(commutes.term, "commutes")
    assert statement.binders == (("x", "Nat"), ("y", "Nat"))
    assert statement.hypotheses == ()
    assert statement.goal == "x + y = y + x"
    assert statement.source("omega") == (
        "theorem commutes (x : Nat) (y : Nat) : x + y = y + x := by\n  omega\n"
    )


def test_an_index_typed_variable_carries_its_bound_as_a_hypothesis() -> None:
    statement = statement_of(below.term, "below")
    assert statement.binders == (("m", "Nat"), ("j", "Nat"))
    assert statement.hypotheses == (("h0", "j < m"),)
    assert statement.goal == "j < m + 1"


def test_the_scan_statement_prints_as_a_lean_theorem() -> None:
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert statement.source("omega").splitlines()[0] == (
        "theorem scan_monotone (size : Nat) (cnt : Nat → Nat) (off : Nat → Nat) "
        "(h0 : off 0 = 0) (h1 : ∀ r : Nat, r < size → off (r + 1) = off r + cnt r) : "
        "∀ p : Nat, p < size + 1 → ∀ q : Nat, q < size + 1 → p ≤ q → off p ≤ off q := by"
    )


def test_a_quantified_hypothesis_is_parenthesized_in_the_proposition() -> None:
    # To the left of an arrow a quantifier needs brackets; in binder syntax it
    # does not, which is why the proposition is rendered rather than pasted.
    proposition = statement_of(scan_monotone.term, "scan_monotone").proposition
    assert "(∀ r : Nat, r < size → off (r + 1) = off r + cnt r) →" in proposition
    assert proposition == print_lean(scan_monotone.term)


def test_a_theorem_prints_itself() -> None:
    assert commutes.lean() == "∀ x : Nat, ∀ y : Nat, x + y = y + x"


def test_a_reduction_statement_is_declined_by_the_printer() -> None:
    with pytest.raises(UnsupportedTerm):
        gauss.lean()


# }}}


# {{{ the tactic ladder, without Lean


def test_the_ladder_starts_cheap_and_ends_with_an_induction() -> None:
    ladder = tactic_ladder(statement_of(scan_monotone.term, "scan_monotone"))
    assert ladder[:4] == ["omega", "decide", "simp", "simp_all"]
    script = ladder[-2]
    # The strategy is read off the statement: q is the variable the guard p <= q
    # makes reachable by steps, p is what the successor case splits against, and
    # h1 is the recurrence to instantiate.
    assert "intro p " in script
    assert "induction q with" in script
    assert "rcases Nat.lt_or_ge k p with" in script
    assert "have hstep := h1 k (by omega)" in script


def test_a_statement_with_no_quantified_goal_has_only_the_cheap_ladder() -> None:
    assert tactic_ladder(statement_of(commutes.term, "commutes")) == [
        "omega",
        "decide",
        "simp",
        "simp_all",
    ]


def test_the_oracle_declines_what_it_cannot_print() -> None:
    oracle = LeanOracle(session=LeanSession())
    assert oracle.trust_class() == "kernel"
    assert oracle.can_establish(scan_monotone.fact())
    assert not oracle.can_establish(gauss.fact())


def test_a_disabled_oracle_is_a_clean_no_op(monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    assert not available
    assert "LANKY_LEAN_DISABLE" in reason
    fact = scan_monotone.fact()
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert reason in result.provenance["lean_declined"]


def test_without_lean_on_the_path_the_oracle_explains_itself(monkeypatch) -> None:
    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    monkeypatch.setenv("PATH", "")
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    assert not available
    assert reason == "lean is not on PATH"


def test_availability_does_not_claim_a_repl_it_has_not_built(monkeypatch) -> None:
    """The cheap question is cheap, and the answer says what it did not ask.

    ``lean`` on the PATH and a driver that imports is all this checks; whether
    a REPL can be built is discovered on the first fact. Reporting a bare
    "available" would be a promise the oracle cannot keep, so the line says it
    has not been tested yet.
    """
    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    oracle = LeanOracle(session=LeanSession())
    available, reason = oracle.availability()
    if not available:  # no Lean here: the reason is the one-line explanation
        assert reason
        return
    assert "untested until the first fact" in reason
    # and the line the CLI prints carries that reason rather than dropping it
    from lanky.check import oracle_lines

    (line,) = [one for one in oracle_lines() if one.startswith("lean ")]
    assert line.startswith("lean (kernel): available (") or "unavailable" in line


def test_the_repl_cache_is_outside_the_virtual_environment(monkeypatch) -> None:
    """A reinstall of the driver must not throw away a built REPL.

    lean-interact's own default is a directory inside its installed package,
    which any ``uv sync`` that reinstalls it deletes, costing another build.
    """
    from lanky.oracles.lean import default_cache_dir

    monkeypatch.delenv("LANKY_LEAN_CACHE_DIR", raising=False)
    monkeypatch.setenv("XDG_CACHE_HOME", "/tmp/xdg")
    assert default_cache_dir() == "/tmp/xdg/lanky/lean-repl"
    assert LeanSession().cache_dir == "/tmp/xdg/lanky/lean-repl"

    monkeypatch.delenv("XDG_CACHE_HOME", raising=False)
    assert default_cache_dir().endswith("/.cache/lanky/lean-repl")

    monkeypatch.setenv("LANKY_LEAN_CACHE_DIR", "/tmp/chosen")
    assert default_cache_dir() == "/tmp/chosen"
    assert "site-packages" not in default_cache_dir()


def test_an_unavailable_oracle_is_named_in_the_check_report(monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    import lanky.oracles  # noqa: F401 - registers the built-in oracles
    from lanky.check import oracle_lines

    lines = [line for line in oracle_lines() if line.startswith("lean ")]
    assert lines == ["lean (kernel): unavailable: disabled by LANKY_LEAN_DISABLE"]


def test_a_pinned_tactic_reaches_the_registered_oracle() -> None:
    from lanky.plugins import registry

    use_tactic(commutes, "omega")
    pinned = [
        oracle.tactics.get("theorem:commutes")
        for oracle in registry.oracles
        if isinstance(oracle, LeanOracle)
    ]
    assert pinned == ["omega"]


# }}}


# {{{ the oracle, with Lean


@pytest.fixture(scope="module")
def lean_oracle() -> Iterator[LeanOracle]:
    """One Lean session for the whole module, or a skip explaining why not.

    The first session ever opened on a machine builds the REPL, which takes
    minutes and wants the network; afterwards it is a second. A suite that
    cannot pay for that says so and moves on.
    """
    if os.environ.get("LANKY_LEAN_DISABLE"):
        pytest.skip("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    oracle = LeanOracle(timeout=float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120")))
    available, reason = oracle.availability()
    if not available:
        pytest.skip(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        pytest.skip(f"the Lean REPL could not be built: {oracle.session.error}")
    yield oracle
    oracle.session.close()


def test_lean_closes_a_nat_identity(lean_oracle: LeanOracle) -> None:
    proved = lean_oracle.establish(commutes.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert proved.provenance["tactic"] == "omega"
    assert "theorem commutes" in proved.provenance["lean_source"]


def test_lean_closes_a_bounded_implication(lean_oracle: LeanOracle) -> None:
    proved = lean_oracle.establish(below.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "omega"


def test_lean_proves_the_scan_is_monotone(lean_oracle: LeanOracle) -> None:
    # The demo theorem: the ladder has to find the induction itself.
    proved = lean_oracle.establish(scan_monotone.fact())
    assert proved.status is Status.PROVED
    assert proved.decided_by == "lean"
    assert "induction q with" in proved.provenance["tactic"]


def test_a_pinned_tactic_is_the_one_that_runs(lean_oracle: LeanOracle) -> None:
    lean_oracle.tactics[commutes.fact().id] = "exact Nat.add_comm x y"
    try:
        proved = lean_oracle.establish(commutes.fact())
    finally:
        lean_oracle.tactics.clear()
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == "exact Nat.add_comm x y"


def test_lean_reports_a_goal_it_cannot_close(lean_oracle: LeanOracle) -> None:
    @theorem
    def false_claim(x: Nat, y: Nat) -> x <= y:
        """Not a theorem at all, so no tactic closes it."""

    fact = false_claim.fact()
    assert lean_oracle.can_establish(fact)
    result = lean_oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert result.provenance["lean_tried"] >= 4
    assert result.provenance["lean_reason"]


def test_the_lean_oracle_never_refutes(lean_oracle: LeanOracle) -> None:
    """A failed proof is not a counterexample, and must never be read as one.

    Three ways the ladder can fail: a statement that is false, one that is true
    but out of the ladder's reach, and an attempt that times out. None of them
    is evidence against the claim, so the fact comes back with the status it
    arrived with and the weaker oracles still get their turn.
    """

    @theorem
    def plainly_false(x: Nat, y: Nat) -> x <= y:
        """False at x = 1, y = 0, and Lean will fail to prove it."""

    @theorem
    def true_but_hard(x: Nat, y: Nat) -> (x + y) * (x + y) >= x * x + y * y:
        """True, and nonlinear, so the core-Lean ladder does not close it."""

    for claim in (plainly_false, true_but_hard):
        result = lean_oracle.establish(claim.fact())
        assert result is not None
        assert result.status is not Status.REFUTED
        assert result.status is Status.ASSUMED
        assert result.decided_by is None
        assert result.provenance["lean_reason"]

    # a timeout is a failed attempt, not a refutation either
    impatient = LeanOracle(timeout=1e-6, session=lean_oracle.session)
    result = impatient.establish(plainly_false.fact())
    assert result.status is not Status.REFUTED


def test_a_session_runs_lean_source_directly(lean_oracle: LeanOracle) -> None:
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 0 = x := by omega\n")
    assert closed, detail
    closed, detail = lean_oracle.session.run("theorem t (x : Nat) : x + 1 = x := by omega\n")
    assert not closed
    assert "omega" in detail


def test_checking_the_example_file_proves_the_scan(lean_oracle: LeanOracle) -> None:
    # The demo, end to end: the file is imported, the claims become facts, and
    # the strongest oracle that can take each one takes it.
    from pathlib import Path

    from lanky.check import check_path

    example = Path(__file__).resolve().parent.parent / "examples" / "gauss.py"
    ledger = check_path(example)
    assert ledger["theorem:scan_monotone"].status is Status.PROVED
    assert ledger["theorem:scan_monotone"].decided_by == "lean"
    # Gauss's sum is outside core Lean, so the property tester keeps it.
    assert ledger["theorem:gauss"].status is Status.TESTED


def test_the_printed_proposition_elaborates(lean_oracle: LeanOracle) -> None:
    # Lean reading the proposition as a term of type Prop is the strongest
    # check the printer can get short of a proof: it says the source is not
    # only plausible but well typed, binders, coercions and all.
    for term in (commutes.term, below.term, scan_monotone.term):
        closed, detail = lean_oracle.session.run(f"example : Prop := {print_lean(term)}\n")
        assert closed, detail


def test_the_statement_the_oracle_sends_is_the_one_it_records(
    lean_oracle: LeanOracle,
) -> None:
    proved = lean_oracle.establish(scan_monotone.fact())
    statement = statement_of(scan_monotone.term, "scan_monotone")
    assert isinstance(statement, LeanStatement)
    assert proved.provenance["lean_source"] == statement.source(proved.provenance["tactic"])


# }}}
