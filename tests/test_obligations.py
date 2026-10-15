"""A plugin's claim checked by Lean part by part, with its solver's hints.

The scripts are text and are tested as text first, with no Lean. Then the
oracle is tested against a real Lean, which skips without one (or fails where
``LANKY_LEAN_TEST_REQUIRED`` promises one): every part proved, a part ``omega``
cannot close named, the hints that make a part provable (an instance of a
universal hypothesis, a witness for an existential goal, a case split where
``omega``'s shadows are missing), a wrong hint rejected, a counterexample
proved and a false one caught, the answers kept and read back, the parts
checked at once, and the ledger's lines.
"""

from __future__ import annotations

import os
from collections.abc import Iterator
from typing import Any

import pytest

from lanky.check import establish
from lanky.cli import CheckVerb, refutation_lines
from lanky.ledger import Fact, Ledger, Status
from lanky.obligations import (
    Application,
    Counterexample,
    Hints,
    Instance,
    Obligation,
    Part,
    Piece,
    attempts,
    negation_source,
    obligation_of,
    part_statement,
    theorem_name,
)
from lanky.oracles.lean import LeanOracle, ProofCache
from lanky.plugins import registry
from lanky.prelude import FinType, Fn, Int, Real
from lanky.terms import Exists, Forall, LogicalAnd, LogicalOr, Var

n, x, y, i, a, r, j = (Var(name) for name in ("n", "x", "y", "i", "a", "r", "j"))


def claim(binders: tuple, hypotheses: list, goal: Any) -> Forall:
    """``∀ binders, hypotheses → goal``, every binder an ``Int`` unless given a sort."""
    pairs = tuple(b if isinstance(b, tuple) else (b, Int) for b in binders)
    if not hypotheses:
        guard = None
    elif len(hypotheses) == 1:
        guard = hypotheses[0]
    else:
        guard = LogicalAnd(tuple(hypotheses))
    return Forall(pairs, goal, guard)


class Stated:
    """A plugin's term that states itself for Lean, counting how often it is asked."""

    def __init__(self, obligation: Obligation | None) -> None:
        self.obligation = obligation
        self.asked = 0

    def lean_obligation(self) -> Obligation | None:
        self.asked += 1
        return self.obligation

    def __str__(self) -> str:
        return "a plugin's claim"


def fact_of(obligation: Obligation | None, status: Status = Status.ASSUMED) -> Fact:
    return Fact(
        id="in-bounds:kernel@1:S0",
        kind="in-bounds",
        statement="x[i] is in bounds for every instance of S0",
        term=Stated(obligation),
        status=status,
        decided_by="isl" if status is not Status.ASSUMED else None,
        where="kernel.py:1",
        owner="kernel",
    )


#: ``x`` in bounds: ``0 ≤ x < n`` gives ``0 ≤ x < n + 1``.
IN_BOUNDS = Part(
    "S0",
    "x[x] over 0 <= x < n",
    claim((n, x), [n >= 0, x >= 0, x < n], (x >= 0) & (x < n + 1)),
)

#: Distinct instances write distinct cells: ``x ≠ y`` gives ``2x ≠ 2y``.
DISJOINT = Part(
    "S0_writes",
    "2 x for distinct x",
    claim((n, x, y), [x >= 0, x < n, y >= 0, y < n, ~(x == y)], ~(2 * x == 2 * y)),
)

#: Every point of ``0 ≤ i < n`` is ``4 io + ii`` with ``0 ≤ ii < 4``: the split's totality.
io, ii = Var("io"), Var("ii")
SPLIT_TOTAL = claim(
    (n, i),
    [i >= 0, i < n],
    Exists(((io, Int), (ii, Int)), (i == 4 * io + ii) & (ii >= 0) & (ii < 4)),
)


# {{{ the scripts, as text


def test_omega_alone_is_tried_first() -> None:
    statement = part_statement(IN_BOUNDS, "kernel_S0")
    assert attempts(IN_BOUNDS, statement) == [("omega", "omega")]
    assert "theorem Lanky.kernel_S0" in statement.source("omega")


def test_an_existential_goal_is_not_offered_to_omega_alone() -> None:
    part = Part("total", "the split is total", SPLIT_TOTAL)
    assert attempts(part, part_statement(part, "kernel_total")) == []


def test_a_witness_gives_each_binder_its_value_and_omega_the_rest() -> None:
    part = Part(
        "total",
        "the split is total",
        SPLIT_TOTAL,
        Hints(witness=(Piece((i // 4, i % 4)),)),
    )
    [(how, script)] = attempts(part, part_statement(part, "kernel_total"))
    assert how == "omega, with the witness"
    assert script.splitlines() == [
        "refine ⟨i / 4, ?_⟩",
        "refine ⟨i % 4, ?_⟩",
        "omega",
    ]


def test_pieces_are_a_case_split_on_where_each_applies() -> None:
    w = Var("w")
    goal = Exists(((w, Int),), ((w == a - 2) & (a >= 2)) | ((w == a + 2) & (a < 2)))
    part = Part(
        "defined",
        "the read has a writer",
        claim((n, a), [a >= 0, a < n], goal),
        Hints(witness=(Piece((a - 2,), a >= 2), Piece((a + 2,)))),
    )
    [(how, script)] = attempts(part, part_statement(part, "kernel_defined"))
    assert how == "omega, with a witness in 2 pieces"
    assert script.splitlines() == [
        "by_cases hp0 : a ≥ 2",
        "· refine ⟨a - 2, ?_⟩",
        "  omega",
        "· refine ⟨a + 2, ?_⟩",
        "  omega",
    ]


def test_an_instance_takes_a_universal_hypothesis_at_a_point() -> None:
    off, cnt, q, b = Var("off"), Var("cnt"), Var("q"), Var("b")
    recurrence = Forall(((q, FinType(n)),), off(q + 1) == off(q) + cnt(q))
    monotone = Forall(
        ((a, FinType(n + 1)), (b, FinType(n + 1))), off(a) <= off(b), a <= b
    )
    part = Part(
        "flat",
        "off[r] + j",
        claim(
            (n, (off, Fn[Int, Int]), (cnt, Fn[Int, Int]), r, j),
            [recurrence, monotone, r >= 0, r < n, j >= 0, j < cnt(r)],
            off(r) + j < off(n),
        ),
        Hints(instances=(Instance(0, (r,)), Instance(1, (r + 1, n)))),
    )
    statement = part_statement(part, "kernel_flat")
    [_, (how, script)] = attempts(part, statement)
    assert how == "omega, with the hypotheses taken at 2 points"
    first, second, last = script.splitlines()
    assert first == "have hi0 := h0 r"
    # the guards of the first binder are a function's arguments, and stay premises
    assert second == "have hi1 := fun g1_0 g1_1 => h1 (r + 1) g1_0 g1_1 n"
    assert last == "omega"


def test_a_split_is_proved_and_then_cased_on() -> None:
    part = Part(
        "pugh",
        "Pugh's example",
        claim(
            (x, y),
            [
                11 * x + 13 * y >= 27,
                11 * x + 13 * y <= 45,
                7 * x - 9 * y >= -10,
                7 * x - 9 * y <= 4,
            ],
            False,
        ),
        Hints(splits=(LogicalOr(((x == 1), (x == 2))),)),
    )
    [_, (how, script)] = attempts(part, part_statement(part, "pugh"))
    assert how == "omega, with a case split"
    assert script.splitlines() == [
        "have hs0 : x = 1 ∨ x = 2 := by omega",
        "rcases hs0 with hs0 | hs0",
        "all_goals omega",
    ]


#: Every read of ``off[r]`` sees a write: ``off[0]`` by the first statement, or
#: ``off[w + 1]`` by the second at ``w = r - 1``, the scan's last writer.
w = Var("w")
LAST_WRITER = claim(
    (n, r),
    [r >= 0, r < n],
    LogicalOr(
        (
            (r == 0),
            Exists(((w, Int),), (w >= 0) & (w < n) & (w + 1 == r) & (w < r)),
        )
    ),
)


def test_a_piece_can_pick_the_disjunct_it_proves() -> None:
    part = Part(
        "read",
        "off[r] has a writer",
        LAST_WRITER,
        Hints(witness=(Piece((), r == 0, 0), Piece((r - 1,), None, 1))),
    )
    [(how, script)] = attempts(part, part_statement(part, "scan_read"))
    assert how == "omega, with a witness in 2 pieces"
    assert script.splitlines() == [
        "by_cases hp0 : r = 0",
        "· refine Or.inl ?_",
        "  omega",
        "· refine Or.inr ?_",
        "  refine ⟨r - 1, ?_⟩",
        "  omega",
    ]


def test_an_instance_reading_a_cell_the_claim_reads_otherwise_is_equated() -> None:
    off, cnt, q = Var("off"), Var("cnt"), Var("q")
    recurrence = Forall(((r, FinType(n)),), off(r + 1) == off(r) + cnt(r))
    part = Part(
        "offsets",
        "off[q] is the offset of row q",
        claim(
            (n, (off, Fn[Int, Int]), (cnt, Fn[Int, Int]), q),
            [recurrence, q >= 1, q <= n],
            off(q) == off(q - 1) + cnt(q - 1),
        ),
        Hints(instances=(Instance(0, (q - 1,)),)),
    )
    [_, (_how, script)] = attempts(part, part_statement(part, "offsets"))
    assert script.splitlines() == [
        "have hi0 := h0 (q - 1)",
        "have hc0 : off (q - 1 + 1) = off q := by congr 1 <;> omega",
        "omega",
    ]


#: A table of reals over two indices, and a second one.
R2, c2, b = Var("R"), Var("c"), Var("b")
TABLE = Fn[Int, Fn[Int, Real]]

#: ``R`` follows the recurrence; the claim is that it does at ``(a + 2, b)``.
RECURRENCE = Forall(
    ((a, Int), (b, Int)), R2(a)(b) == -R2(a - 2)(b + 2), (a >= 2) & (b >= 0)
)
REAL_PART = Part(
    "post",
    "R[a + 2, b] == -R[a, b + 2]",
    claim(
        ((R2, TABLE), a, b),
        [RECURRENCE, a >= 0, b >= 0],
        R2(a + 2)(b) == -R2(a)(b + 2),
    ),
    Hints(instances=(Instance(0, (a + 2, b)),)),
    mathlib=True,
)


def test_a_part_about_reals_is_printed_in_mathlibs_dialect() -> None:
    statement = part_statement(REAL_PART, "post")
    assert statement.mathlib
    assert "(R : Int → Int → ℝ)" in statement.parameters


def test_a_part_about_reals_takes_instances_with_their_premises_shown() -> None:
    """``linarith`` reads equations, not the implications an instance of ``omega``'s keeps.

    Each premise is shown by ``omega`` at the point, the instance left out
    where one is not; an application of two arguments is equated with the
    claim's one argument at a time, where ``congr`` takes ``b + 2`` apart.
    """
    [_, (how, script)] = attempts(REAL_PART, part_statement(REAL_PART, "post"))
    assert how == "linarith, with the hypotheses taken at 1 point"
    lines = script.splitlines()
    assert lines[0] == "try have hi0 := h0 (a + 2) b (by omega) (by omega)"
    assert lines[1] == (
        "try have hc0 : R (a + 2 - 2) (b + 2) = R a (b + 2) := "
        "((congrArg (fun x_cong => R x_cong (b + 2)) (by omega : (a + 2 - 2) = a))"
        ".trans (congrArg (fun x_cong => R a x_cong) (by omega : (b + 2) = (b + 2))))"
    )
    assert lines[-1] == "linarith"


def test_a_theorem_a_hypothesis_is_is_applied_with_what_the_plugin_bound() -> None:
    """``apply h0 (p := p) (c := c)``: Lean finds the rest, and each premise is a hypothesis."""
    p, D = Var("p"), Var("D")
    theorem = Forall(
        ((p, Int), (c2, TABLE), (D, TABLE)),
        Forall(((a, Int),), c2(a)(0) == D(a)(0)),
        Forall(((a, Int),), D(a)(0) == c2(a)(0)),
    )
    copies = Forall(((a, Int),), D(a)(0) == c2(a)(0))
    part = Part(
        "applied",
        "the theorem applied",
        claim(
            ((c2, TABLE), (D, TABLE), p),
            [theorem, copies],
            Forall(((a, Int),), c2(a)(0) == D(a)(0)),
        ),
        Hints(applications=(Application(0, (("p", p), ("c", c2))),)),
        mathlib=True,
    )
    tried = attempts(part, part_statement(part, "applied"))
    assert ("the theorem applied", "intros\napply h0 (p := p) (c := c)\n"
            "all_goals first | assumption | omega | linarith") in tried


def test_without_mathlib_a_claim_about_reals_is_declined_saying_why(
    no_session, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    oracle, started = no_session
    fact = oracle.establish(fact_of(Obligation(parts=(REAL_PART,))))
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_declined"].startswith(
        "the claim is about real numbers, which core Lean does not have"
    )
    assert fact.provenance["lean_needs_mathlib"] is True
    assert started == []


def _declined_for_reals(fact_id: str, decider: str) -> Fact:
    reason = (
        "the claim is about real numbers, which core Lean does not have; where "
        "Mathlib is (LANKY_LEAN_MATHLIB), Lean checks it"
    )
    return Fact(
        id=fact_id, kind="postcondition", statement="R[a] == c[a]", term=None
    ).with_status(
        Status.DECIDED, decider, lean_declined=reason, lean_needs_mathlib=True
    )


def test_the_lean_line_counts_the_claims_about_reals_apart(capsys) -> None:
    """Core Lean has no reals: such a claim is not unstated, it waits for Mathlib.

    The line says where Lean checks it, rather than that it is not stated.
    Where no fact a solver decided is about anything else, there is no such
    line, and the ``WITHOUT MATHLIB`` line under it says it all.
    """
    from lanky.cli import report_proved

    proved = fact_of(Obligation(parts=(IN_BOUNDS,), decider="isl")).with_status(
        Status.PROVED,
        "lean",
        lean_parts=[{"name": "S0", "proved": True}],
        lean_decider="isl",
    )
    post = _declined_for_reals("postcondition:kernel@1", "isl")
    applied = _declined_for_reals("by-theorem:kernel@1:t", "theorem")
    report_proved(Ledger([proved, post, applied]))
    out = capsys.readouterr().out
    assert (
        "LEAN proved the one fact isl decided; 2 more are about real numbers, which "
        "Lean checks where Mathlib is (LANKY_LEAN_MATHLIB). "
    ) in out
    assert "not stated for Lean yet" not in out
    # with no fact a solver decided, the WITHOUT MATHLIB line is the one that
    # names them, with the command (report_missing)
    report_proved(Ledger([post]))
    assert capsys.readouterr().out == ""


def test_the_negation_instantiates_every_binder_at_the_point() -> None:
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    statement = part_statement(part, "kernel_S0")
    source = negation_source(part, statement, {"n": 2, "x": 1})
    proposition = "∀ n : Int, ∀ x : Int, x ≥ 0 → x < n → x + 1 < n"
    assert f"theorem Lanky.kernel_S0_false : ¬({proposition})" in source
    assert "have hw := h 2 1" in source
    assert source.rstrip().endswith("decide")
    assert negation_source(part, statement, {"n": 2, "x": -1}, decide=False).rstrip().endswith(
        "omega"
    )


def test_a_counterexample_must_value_every_variable() -> None:
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    statement = part_statement(part, "kernel_S0")
    from lanky.lean import UnsupportedTerm

    with pytest.raises(UnsupportedTerm, match="gives x no value"):
        negation_source(part, statement, {"n": 2})


def test_a_term_offers_its_obligation_through_one_method() -> None:
    obligation = Obligation(parts=(IN_BOUNDS,))
    assert obligation_of(Stated(obligation)) is obligation
    assert obligation_of(Stated(None)) is None
    assert obligation_of(object()) is None


def test_asking_whether_lean_takes_a_claim_does_not_state_it() -> None:
    term = Stated(Obligation(parts=(IN_BOUNDS,)))
    fact = Fact(id="f", kind="in-bounds", statement="s", term=term)
    assert LeanOracle().can_establish(fact)
    assert term.asked == 0


def test_a_long_theorem_is_shown_one_parameter_to_a_line() -> None:
    from lanky.cli import _wrapped

    long = (
        "theorem Lanky.jacobi_in_bounds (nt : Int) (nx : Int) (t : Int) (i : Int) "
        "(h0 : nt ≥ 0) (h1 : nx ≥ 0) (h2 : t + 1 < nt) : 0 ≤ t ∧ (t < nt) := by"
    )
    assert _wrapped(long).splitlines() == [
        "theorem Lanky.jacobi_in_bounds",
        "    (nt : Int)",
        "    (nx : Int)",
        "    (t : Int)",
        "    (i : Int)",
        "    (h0 : nt ≥ 0)",
        "    (h1 : nx ≥ 0)",
        "    (h2 : t + 1 < nt)",
        "    : 0 ≤ t ∧ (t < nt) := by",
    ]
    negation = "theorem Lanky.x_false : ¬(∀ n : Int, n + 1 > n) := by" + " " * 60
    assert _wrapped(negation) == negation
    assert _wrapped("  omega") == "  omega"


@pytest.fixture
def no_session(monkeypatch: pytest.MonkeyPatch, tmp_path) -> tuple[LeanOracle, list]:
    """An oracle with a proof cache of its own, whose sessions record that they were started.

    Lean is pinned to a version no toolchain has, and a session that is
    asked to start says it cannot, so nothing here needs Lean: what is
    tested is whether a check asks for one.
    """
    from lanky.oracles.lean import LeanSession

    monkeypatch.setenv("LANKY_LEAN_VERSION", "v0.0.0-test")
    monkeypatch.delenv("LANKY_LEAN_DISABLE", raising=False)
    started: list = []

    def start(session: LeanSession) -> bool:
        started.append(session)
        session.error = "no Lean in this test"
        return False

    monkeypatch.setattr(LeanSession, "start", start)
    oracle = LeanOracle()
    monkeypatch.setattr(oracle, "availability", lambda: (True, ""))
    oracle.proofs = ProofCache(str(tmp_path / "proofs"))
    return oracle, started


def _keep(oracle: LeanOracle, part: Part, closed: bool, which: int = 0) -> None:
    """Keep Lean's answer to the ``which``-th attempt at ``part`` in the oracle's cache."""
    statement = part_statement(part, theorem_name("kernel", part))
    _how, tactic = attempts(part, statement)[which]
    oracle.proofs.put("v0.0.0-test", statement.source(tactic), closed, "" if closed else "no")


def test_a_warm_check_reads_every_part_without_starting_lean(no_session) -> None:
    """#118: every part's answer is in the cache, so no REPL is started.

    The cache is keyed by the version a session would run, which the pin
    gives without one; the check used to start the REPL first to learn it.
    """
    oracle, started = no_session
    _keep(oracle, IN_BOUNDS, True)
    _keep(oracle, DISJOINT, True)
    fact = oracle.establish(fact_of(Obligation(parts=(IN_BOUNDS, DISJOINT), decider="isl")))
    assert fact.status is Status.PROVED
    assert [record["cached"] for record in fact.provenance["lean_parts"]] == [True, True]
    assert fact.provenance["lean_version"] == "v0.0.0-test"
    assert started == []


def test_an_attempt_the_cache_does_not_hold_starts_lean(no_session) -> None:
    """A part whose first attempt failed, and whose next one was never asked, needs Lean."""
    oracle, started = no_session
    _keep(oracle, IN_BOUNDS, True)
    split = Hints(splits=(LogicalOr(((x == 1), (x == 2))),))
    wrong = Part("S1", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n), split)
    _keep(oracle, wrong, False)
    fact = oracle.establish(fact_of(Obligation(parts=(IN_BOUNDS, wrong))))
    assert started
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_reason"] == "no Lean in this test"


def test_a_part_every_attempt_of_which_failed_is_read_back_too(no_session) -> None:
    """A part Lean found no proof of, every attempt kept, is a warm answer as well."""
    oracle, started = no_session
    wrong = Part("S1", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    statement = part_statement(wrong, theorem_name("kernel", wrong))
    for which in range(len(attempts(wrong, statement))):
        _keep(oracle, wrong, False, which)
    fact = oracle.establish(fact_of(Obligation(parts=(wrong,))))
    assert started == []
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_reason"] == "Lean found no proof"


def test_a_counterexample_is_read_back_without_starting_lean(no_session) -> None:
    oracle, started = no_session
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    statement = part_statement(part, theorem_name("kernel", part))
    source = negation_source(part, statement, {"n": 2, "x": 1})
    oracle.proofs.put("v0.0.0-test", source, True, "")
    obligation = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"n": 2, "x": 1}, "x=1 at n=2")
    )
    fact = oracle.establish(fact_of(obligation, Status.REFUTED))
    assert started == []
    assert fact.provenance["lean_refuted_by"] == "decide"
    assert fact.provenance["lean_version"] == "v0.0.0-test"


def _claim_fact(term: Any) -> Fact:
    """A claim of lanky's own, not a plugin's: Lean is asked its ladder."""
    return Fact(id="succ", kind="theorem", statement="n + 1 > n", term=term, owner="succ")


def test_a_claim_of_lankys_own_is_read_back_without_starting_lean(
    no_session, monkeypatch: pytest.MonkeyPatch
) -> None:
    """#118 for a theorem: its ladder's answers are kept as a part's are.

    The ladder is Python's, the same for the same statement, so the attempts
    a check made are read back in their order, and the first that closed
    proves the claim. A Mathlib theorem was the most of a warm check's time:
    every attempt before the one that closed was asked again.
    """
    from lanky.lean import statement_of
    from lanky.oracles.lean import tactic_ladder

    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    oracle, started = no_session
    term = claim((n,), [n >= 0], n + 1 > n)
    statement = statement_of(term, "succ", mathlib=False)
    ladder = tactic_ladder(statement)
    oracle.proofs.put("v0.0.0-test", statement.source(ladder[0]), False, "no")
    oracle.proofs.put("v0.0.0-test", statement.source(ladder[1]), True, "")
    fact = oracle.establish(_claim_fact(term))
    assert started == []
    assert fact.status is Status.PROVED
    assert fact.provenance["tactic"] == ladder[1]
    assert fact.provenance["lean_version"] == "v0.0.0-test"


def test_a_claim_with_an_attempt_the_cache_does_not_hold_starts_lean(
    no_session, monkeypatch: pytest.MonkeyPatch
) -> None:
    from lanky.lean import statement_of
    from lanky.oracles.lean import tactic_ladder

    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    oracle, started = no_session
    term = claim((n,), [n >= 0], n + 1 > n)
    statement = statement_of(term, "succ", mathlib=False)
    oracle.proofs.put("v0.0.0-test", statement.source(tactic_ladder(statement)[0]), False, "")
    fact = oracle.establish(_claim_fact(term))
    assert started
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_reason"] == "no Lean in this test"


@pytest.fixture
def fake_mathlib(monkeypatch: pytest.MonkeyPatch, tmp_path) -> str:
    """A Mathlib project's files, which the cache's key is read from, and no Mathlib."""
    import json

    project = tmp_path / "mathlib"
    project.mkdir()
    (project / "lean-toolchain").write_text("leanprover/lean4:v0.0.0-test\n")
    manifest = {"packages": [{"name": "mathlib", "inputRev": "v0.0.0-test", "rev": "abc"}]}
    (project / "lake-manifest.json").write_text(json.dumps(manifest))
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", str(project))
    return "v0.0.0-test+mathlib@v0.0.0-test (abc)"


def test_a_part_about_reals_is_read_back_without_starting_mathlib(
    no_session, fake_mathlib: str
) -> None:
    """The key of a Mathlib answer is the project's toolchain and Mathlib revision.

    Both are in its files, so a part about reals is read back as an integer
    part is, without the session that would import Mathlib (#118).
    """
    oracle, started = no_session
    u, v = Var("u"), Var("v")
    part = Part("S0", "u == v", claim(((u, Real), (v, Real)), [u == v], v == u), mathlib=True)
    statement = part_statement(part, theorem_name("kernel", part))
    _how, tactic = attempts(part, statement)[0]
    oracle.proofs.put(fake_mathlib, statement.source(tactic), True, "")
    fact = oracle.establish(fact_of(Obligation(parts=(part,), decider="isl")))
    assert started == []
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_version"] == "v0.0.0-test"
    assert fact.provenance["lean_mathlib"] == "v0.0.0-test (abc)"


def test_a_side_condition_every_attempt_of_which_failed_declines_from_the_cache(
    no_session, fake_mathlib: str
) -> None:
    """Every attempt at a side condition kept as failed: the claim is declined, no Lean.

    A complex square root that may reach its cut is declined, saying so, as
    the session would decline it, without the session.
    """
    from lanky import sqrt
    from lanky.lean import statement_of
    from lanky.oracles.lean import SIDE_CONDITION_TACTICS
    from lanky.prelude import Complex

    oracle, started = no_session
    z = Var("z")
    term = Forall(((z, Complex),), sqrt(z + 1j) == sqrt(z + 1j))
    (condition,) = statement_of(term, "succ", mathlib=True).side_conditions
    for tactic in SIDE_CONDITION_TACTICS:
        oracle.proofs.put(fake_mathlib, condition.source(f"intros\n{tactic}"), False, "no")
    fact = oracle.establish(_claim_fact(term))
    assert started == []
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_declined"].startswith("Lean could not prove ")
    assert "branch cut" in fact.provenance["lean_declined"]


def _slow_start(monkeypatch: pytest.MonkeyPatch, seconds: float = 0.5) -> None:
    """Sessions that take ``seconds`` to start, as importing Mathlib does, then close every part.

    An answer starts the session first, as :meth:`LeanSession.answer` does,
    and is the budget's to refuse once the budget is spent.
    """
    import time

    from lanky.oracles.lean import BUDGET_SPENT, LeanSession

    state = {"started": False}

    def ready(session: LeanSession) -> bool:
        if not state["started"]:
            time.sleep(seconds)
            state["started"] = True
        return True

    def answer(session: LeanSession, source: str, until: float | None = None) -> tuple:
        ready(session)
        if until is not None and until <= time.monotonic():
            return False, BUDGET_SPENT, False
        return True, "", True

    monkeypatch.setattr(LeanSession, "ready", ready)
    monkeypatch.setattr(LeanSession, "answer", answer)
    monkeypatch.setenv("LANKY_LEAN_BUDGET", str(seconds * 0.6))


def test_starting_lean_does_not_count_against_a_claims_budget(
    no_session, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The budget is Lean's: it starts once the session is ready, as before the cache."""
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    oracle, _started = no_session
    _slow_start(monkeypatch)
    fact = oracle.establish(_claim_fact(claim((n,), [n >= 0], n + 1 > n)))
    assert fact.status is Status.PROVED, fact.provenance.get("lean_reason")


def test_importing_mathlib_does_not_count_against_a_parts_budget(
    no_session, fake_mathlib: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A part about reals is checked in the Mathlib session, made ready before the budget."""
    oracle, _started = no_session
    _slow_start(monkeypatch)
    monkeypatch.setattr(oracle, "_part_sessions", lambda: [oracle.session])
    u, v = Var("u"), Var("v")
    part = Part("S0", "u == v", claim(((u, Real), (v, Real)), [u == v], v == u), mathlib=True)
    fact = oracle.establish(fact_of(Obligation(parts=(part,), decider="isl")))
    assert fact.status is Status.PROVED, fact.provenance.get("lean_reason")


def test_a_mathlib_without_a_revision_keeps_no_answer(
    no_session, monkeypatch: pytest.MonkeyPatch, tmp_path
) -> None:
    """A key that does not name the Mathlib would let another one's answers be read (Codex)."""
    from lanky.oracles.lean import LeanSession

    project = tmp_path / "unpinned"
    project.mkdir()
    (project / "lean-toolchain").write_text("leanprover/lean4:v0.0.0-test\n")
    (project / "lake-manifest.json").write_text('{"packages": []}')
    oracle, _started = no_session
    session = LeanSession(mathlib=str(project))
    session.version = "v0.0.0-test"
    monkeypatch.setattr(
        LeanSession, "answer", lambda self, source, until=None: (True, "", True)
    )
    assert oracle._ask(session, "theorem t : True := trivial\n", None)[2] is False
    assert not any((tmp_path / "proofs").rglob("*.json"))


def test_a_claim_all_about_reals_starts_no_core_lean(
    no_session, fake_mathlib: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Its parts are the Mathlib session's: the core pool is not built for it (Codex)."""
    oracle, _started = no_session
    _slow_start(monkeypatch, 0.01)
    pooled: list = []
    monkeypatch.setattr(oracle, "_part_sessions", lambda: pooled.append(1) or [])
    u, v = Var("u"), Var("v")
    part = Part("S0", "u == v", claim(((u, Real), (v, Real)), [u == v], v == u), mathlib=True)
    fact = oracle.establish(fact_of(Obligation(parts=(part,), decider="isl")))
    assert fact.status is Status.PROVED, fact.provenance.get("lean_reason")
    assert pooled == []


def test_a_counterexample_to_a_part_about_reals_goes_to_the_mathlib_session(
    no_session, fake_mathlib: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Printed with ``ℝ``, it elaborates only where Mathlib is imported (Codex)."""
    from lanky.oracles.lean import LeanSession

    oracle, _started = no_session
    asked: list[bool] = []

    def answer(session: LeanSession, source: str, until: float | None = None) -> tuple:
        asked.append(session.mathlib is not None)
        return True, "", True

    monkeypatch.setattr(LeanSession, "ready", lambda self: True)
    monkeypatch.setattr(LeanSession, "answer", answer)
    monkeypatch.setattr(oracle, "_part_sessions", lambda: [LeanSession()])
    u = Var("u")
    part = Part("S0", "u < 1", claim(((u, Real),), [u > 0], u < 1), mathlib=True)
    obligation = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"u": 2}, "u=2")
    )
    oracle.establish(fact_of(obligation, Status.REFUTED))
    assert asked and all(asked)


def test_a_mathlib_claim_of_lankys_own_is_read_back_without_starting_mathlib(
    no_session, fake_mathlib: str
) -> None:
    from lanky.lean import statement_of
    from lanky.oracles.lean import tactic_ladder

    oracle, started = no_session
    u = Var("u")
    term = claim(((u, Real),), [u > 0], u + 1 > u)
    statement = statement_of(term, "succ", mathlib=True)
    ladder = tactic_ladder(statement)
    oracle.proofs.put(fake_mathlib, statement.source(ladder[0]), True, "")
    fact = oracle.establish(_claim_fact(term))
    assert started == []
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_source"].startswith("import Mathlib\n")
    assert fact.provenance["lean_mathlib"] == "v0.0.0-test (abc)"


# }}}


# {{{ with Lean


def _without_lean(reason: str) -> None:
    if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


@pytest.fixture(scope="module")
def lean(tmp_path_factory: pytest.TempPathFactory) -> Iterator[LeanOracle]:
    """A Lean oracle with an open session and a proof cache of its own."""
    if os.environ.get("LANKY_LEAN_DISABLE"):
        _without_lean("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    oracle = LeanOracle(timeout=float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120")))
    available, reason = oracle.availability()
    if not available:
        _without_lean(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        _without_lean(f"the Lean REPL could not be built: {oracle.session.error}")
    oracle.proofs = ProofCache(str(tmp_path_factory.mktemp("proofs")))
    yield oracle
    for session in oracle._pool:
        session.close()
    oracle.session.close()


def test_lean_proves_every_part_and_says_how(lean: LeanOracle) -> None:
    fact = lean.establish(fact_of(Obligation(parts=(IN_BOUNDS, DISJOINT), decider="isl")))
    assert fact.status is Status.PROVED
    assert fact.decided_by == "lean"
    records = fact.provenance["lean_parts"]
    assert [record["name"] for record in records] == ["S0", "S0_writes"]
    assert all(record["proved"] and record["how"] == "omega" for record in records)
    assert fact.provenance["lean_decider"] == "isl"
    # one file replays the proof: a theorem per part
    source = fact.provenance["lean_source"]
    assert "theorem Lanky.kernel_S0 " in source
    assert "theorem Lanky.kernel_S0_writes " in source


def test_a_part_lean_cannot_prove_leaves_the_fact_and_is_named(lean: LeanOracle) -> None:
    wrong = Part("S1", "x[x + 1] over 0 <= x < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    handed = fact_of(Obligation(parts=(IN_BOUNDS, wrong)))
    fact = lean.establish(handed)
    assert fact.status is Status.ASSUMED
    reason = fact.provenance["lean_reason"]
    # in plain words, the part by its label; what Lean said is in its record
    assert reason == (
        "Lean proved 1 of its 2 parts, and found no proof for x[x + 1] over 0 <= x < n"
    )
    assert [record["proved"] for record in fact.provenance["lean_parts"]] == [True, False]
    assert "Lean said" in fact.provenance["lean_parts"][1]["reason"]


def test_an_existential_goal_is_proved_with_its_witness(lean: LeanOracle) -> None:
    bare = Part("total", "the split is total", SPLIT_TOTAL)
    fact = lean.establish(fact_of(Obligation(parts=(bare,))))
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_reason"] == (
        "Lean was given no witness for what it claims exists"
    )
    assert "no witness was given" in fact.provenance["lean_parts"][0]["reason"]
    hinted = Part(
        "total", "the split is total", SPLIT_TOTAL, Hints(witness=(Piece((i // 4, i % 4)),))
    )
    fact = lean.establish(fact_of(Obligation(parts=(hinted,))))
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_parts"][0]["how"] == "omega, with the witness"


def test_a_wrong_witness_is_rejected(lean: LeanOracle) -> None:
    wrong = Part(
        "total", "the split is total", SPLIT_TOTAL, Hints(witness=(Piece((i // 4, i % 4 + 1)),))
    )
    fact = lean.establish(fact_of(Obligation(parts=(wrong,))))
    assert fact.status is Status.ASSUMED


def test_a_piecewise_witness_is_checked_piece_by_piece(lean: LeanOracle) -> None:
    w = Var("w")
    goal = Exists(((w, Int),), ((w == a - 2) & (a >= 2)) | ((w == a + 2) & (a < 2)))
    term = claim((n, a), [a >= 0, a < n], goal)
    one_piece = Part("defined", "a writer", term, Hints(witness=(Piece((a - 2,)),)))
    assert lean.establish(fact_of(Obligation(parts=(one_piece,)))).status is Status.ASSUMED
    two = Part(
        "defined", "a writer", term, Hints(witness=(Piece((a - 2,), a >= 2), Piece((a + 2,))))
    )
    assert lean.establish(fact_of(Obligation(parts=(two,)))).status is Status.PROVED


def test_instances_let_omega_use_a_universal_hypothesis(lean: LeanOracle) -> None:
    # spmv's flat cell val[off[r] + j]: the scan's recurrence at r and its
    # monotone offsets at (r + 1, n), which omega never instantiates itself
    off, cnt, q, b = Var("off"), Var("cnt"), Var("q"), Var("b")
    recurrence = Forall(((q, FinType(n)),), off(q + 1) == off(q) + cnt(q))
    monotone = Forall(((a, FinType(n + 1)), (b, FinType(n + 1))), off(a) <= off(b), a <= b)
    term = claim(
        (n, (off, Fn[Int, Int]), (cnt, Fn[Int, Int]), r, j),
        [n >= 0, recurrence, monotone, r >= 0, r < n, j >= 0, j < cnt(r)],
        off(r) + j < off(n),
    )
    bare = Part("flat", "off[r] + j", term)
    assert lean.establish(fact_of(Obligation(parts=(bare,)))).status is Status.ASSUMED
    hinted = Part(
        "flat", "off[r] + j", term, Hints(instances=(Instance(1, (r,)), Instance(2, (r + 1, n))))
    )
    fact = lean.establish(fact_of(Obligation(parts=(hinted,))))
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_parts"][0]["how"] == "omega, with the hypotheses taken at 2 points"


def test_a_split_rescues_omega_where_its_shadows_are_missing(lean: LeanOracle) -> None:
    # Pugh's example: the rational relaxation has points, the integers none,
    # and omega, with no dark or grey shadow, cannot tell
    hypotheses = [
        11 * x + 13 * y >= 27,
        11 * x + 13 * y <= 45,
        7 * x - 9 * y >= -10,
        7 * x - 9 * y <= 4,
    ]
    bare = Part("pugh", "Pugh's example", claim((x, y), hypotheses, False))
    assert lean.establish(fact_of(Obligation(parts=(bare,)))).status is Status.ASSUMED
    split = Part(
        "pugh",
        "Pugh's example",
        claim((x, y), hypotheses, False),
        Hints(splits=(LogicalOr(((x == 1), (x == 2))),)),
    )
    assert lean.establish(fact_of(Obligation(parts=(split,)))).status is Status.PROVED


def test_every_case_a_split_makes_is_split_again(lean: LeanOracle) -> None:
    # Codex: a second split ran only in the first case the first one made. Here
    # the first split is of no use, and every case needs the second (Pugh's).
    hypotheses = [
        11 * x + 13 * y >= 27,
        11 * x + 13 * y <= 45,
        7 * x - 9 * y >= -10,
        7 * x - 9 * y <= 4,
    ]
    part = Part(
        "pugh",
        "Pugh's example",
        claim((x, y), hypotheses, False),
        Hints(splits=(LogicalOr(((y <= 0), (y > 0))), LogicalOr(((x == 1), (x == 2))))),
    )
    [_, (_how, script)] = attempts(part, part_statement(part, "pugh"))
    assert script.splitlines() == [
        "have hs0 : y ≤ 0 ∨ y > 0 := by omega",
        "rcases hs0 with hs0 | hs0",
        "all_goals",
        "  have hs1 : x = 1 ∨ x = 2 := by omega",
        "  rcases hs1 with hs1 | hs1",
        "all_goals omega",
    ]
    assert lean.establish(fact_of(Obligation(parts=(part,)))).status is Status.PROVED


def test_a_fallback_adds_to_the_hints_a_part_has(lean: LeanOracle) -> None:
    # Codex: the fallback's split took the place of the part's instance. Where
    # x <= 0 the claim needs f's hypothesis taken at x, and elsewhere (Pugh's
    # example, which has no integer point) the split by x's rational bounds.
    f, q = Var("f"), Var("q")
    zero = Forall(((q, Int),), f(q) == 0, q <= 0)
    pugh = LogicalAnd(
        (
            11 * x + 13 * y >= 27,
            11 * x + 13 * y <= 45,
            7 * x - 9 * y >= -10,
            7 * x - 9 * y <= 4,
        )
    )
    term = claim(((f, Fn[Int, Int]), x, y), [zero, LogicalOr(((x <= 0), pugh))], f(x) == 0)

    def splits() -> Hints:
        return Hints(splits=(LogicalOr(((x <= 0), (x == 1), (x == 2))),))

    part = Part("both", "an instance and a split", term, Hints(instances=(Instance(0, (x,)),)))
    assert lean.establish(fact_of(Obligation(parts=(part,)))).status is Status.ASSUMED
    both = Part("both", "an instance and a split", term, part.hints, fallback=splits)
    fact = lean.establish(fact_of(Obligation(parts=(both,))))
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_parts"][0]["how"] == (
        "omega, with the hypotheses taken at 1 point and a case split"
    )


def test_an_instance_that_cannot_be_written_leaves_the_others() -> None:
    # Codex: one unwritable instance dropped every instance
    off, cnt, q, b = Var("off"), Var("cnt"), Var("q"), Var("b")
    recurrence = Forall(((q, FinType(n)),), off(q + 1) == off(q) + cnt(q))
    monotone = Forall(
        ((a, FinType(n + 1)), (b, FinType(n + 1))), off(a) <= off(b), a <= b
    )
    part = Part(
        "flat",
        "off[r] + j",
        claim(
            (n, (off, Fn[Int, Int]), (cnt, Fn[Int, Int]), r, j),
            [recurrence, monotone, r >= 0, r < n, j >= 0, j < cnt(r)],
            off(r) + j < off(n),
        ),
        # the hypothesis r >= 0 is no universal: that instance cannot be written
        Hints(instances=(Instance(0, (r,)), Instance(2, (r,)), Instance(1, (r + 1, n)))),
    )
    [_, (how, script)] = attempts(part, part_statement(part, "kernel_flat"))
    assert how == "omega, with the hypotheses taken at 2 points"
    assert script.splitlines()[:2] == [
        "have hi0 := h0 r",
        "have hi1 := fun g1_0 g1_1 => h1 (r + 1) g1_0 g1_1 n",
    ]


def test_a_counterexample_lean_has_no_time_for_is_no_disagreement(
    lean: LeanOracle,
) -> None:
    # Codex: a check that ran out of time read as a disagreement
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    refuted = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"n": 2, "x": 1}, "x=1 at n=2")
    )
    hurried = LeanOracle(timeout=lean.timeout, session=lean.session, budget=1e-9)
    hurried.proofs = ProofCache(None)
    fact = hurried.establish(fact_of(refuted, Status.REFUTED))
    assert fact.status is Status.REFUTED
    assert "lean_disagrees" not in fact.provenance
    assert fact.provenance["lean_counterexample"] == (
        "Lean did not check the counterexample at x=1 at n=2: it ran out of time"
    )


def test_a_disjunction_is_proved_piece_by_piece(lean: LeanOracle) -> None:
    bare = Part("read", "off[r] has a writer", LAST_WRITER)
    assert lean.establish(fact_of(Obligation(parts=(bare,)))).status is Status.ASSUMED
    hinted = Part(
        "read",
        "off[r] has a writer",
        LAST_WRITER,
        Hints(witness=(Piece((), r == 0, 0), Piece((r - 1,), None, 1))),
    )
    assert lean.establish(fact_of(Obligation(parts=(hinted,)))).status is Status.PROVED
    swapped = Part(
        "read",
        "off[r] has a writer",
        LAST_WRITER,
        Hints(witness=(Piece((), r == 0, 1), Piece((r - 1,), None, 0))),
    )
    assert lean.establish(fact_of(Obligation(parts=(swapped,)))).status is Status.ASSUMED


def test_an_equated_cell_lets_omega_use_an_instance(lean: LeanOracle) -> None:
    off, cnt, q = Var("off"), Var("cnt"), Var("q")
    recurrence = Forall(((r, FinType(n)),), off(r + 1) == off(r) + cnt(r))
    part = Part(
        "offsets",
        "off[q] is the offset of row q",
        claim(
            (n, (off, Fn[Int, Int]), (cnt, Fn[Int, Int]), q),
            [recurrence, q >= 1, q <= n],
            off(q) == off(q - 1) + cnt(q - 1),
        ),
        Hints(instances=(Instance(0, (q - 1,)),)),
    )
    assert lean.establish(fact_of(Obligation(parts=(part,)))).status is Status.PROVED


def test_a_counterexample_is_proved_false_there(lean: LeanOracle) -> None:
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    refuted = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"n": 2, "x": 1}, "x=1 at n=2")
    )
    fact = lean.establish(fact_of(refuted, Status.REFUTED))
    assert fact.status is Status.REFUTED
    # the row says it in plain words; how, in the detail view
    assert fact.provenance["lean_counterexample"] == (
        "Lean confirmed the counterexample: the claim is false at x=1 at n=2"
    )
    assert fact.provenance["lean_refuted_by"] == "decide"
    assert "theorem Lanky.kernel_S0_false" in fact.provenance["lean_refutation"]
    assert refutation_lines(fact)[-1] == fact.provenance["lean_counterexample"]
    assert "decide" not in "\n".join(refutation_lines(fact))


def test_a_refuted_fact_with_no_counterexample_is_never_proved(lean: LeanOracle) -> None:
    # The parts hold, and the solver refuted the claim all the same, with no
    # counterexample to check: Lean only ever checks a refutation, and never
    # turns one into a proof, which would hide the solver's verdict.
    fact = lean.establish(fact_of(Obligation(parts=(IN_BOUNDS,)), Status.REFUTED))
    assert fact.status is Status.REFUTED
    assert "lean_parts" not in fact.provenance
    assert fact.provenance["lean_counterexample"].startswith(
        "Lean did not check the refutation"
    )


def test_a_counterexample_that_is_none_is_caught(lean: LeanOracle) -> None:
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    bogus = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"n": 3, "x": 0}, "x=0 at n=3")
    )
    fact = lean.establish(fact_of(bogus, Status.REFUTED))
    assert fact.provenance["lean_disagrees"] is True
    assert fact.provenance["lean_counterexample"].startswith(
        "the counterexample and Lean disagree: Lean could not prove the claim false "
        "at x=0 at n=3"
    )
    assert fact.provenance["lean_counterexample_detail"]


def test_lean_answers_are_kept_and_read_back(lean: LeanOracle, tmp_path) -> None:
    lean_cache = lean.proofs
    lean.proofs = ProofCache(str(tmp_path))
    try:
        first = lean.establish(fact_of(Obligation(parts=(IN_BOUNDS,))))
        second = lean.establish(fact_of(Obligation(parts=(IN_BOUNDS,))))
    finally:
        lean.proofs = lean_cache
    assert first.provenance["lean_parts"][0]["cached"] is False
    assert second.provenance["lean_parts"][0]["cached"] is True
    assert second.status is Status.PROVED


def test_parts_are_checked_at_once(lean: LeanOracle, monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_JOBS", "3")
    parts = tuple(
        Part(f"S{k}", f"x + {k}", claim((n, x), [x >= 0, x < n], x + k < n + k)) for k in range(5)
    )
    fact = lean.establish(fact_of(Obligation(parts=parts)))
    assert fact.status is Status.PROVED
    assert len(lean._pool) >= 3


def test_a_spent_budget_leaves_the_fact_with_the_reason(lean: LeanOracle) -> None:
    hurried = LeanOracle(timeout=lean.timeout, session=lean.session, budget=1e-9)
    hurried.proofs = ProofCache(None)
    fact = hurried.establish(fact_of(Obligation(parts=(IN_BOUNDS,))))
    assert fact.status is Status.ASSUMED
    assert fact.provenance["lean_parts"][0]["timed_out"] is True
    assert fact.provenance["lean_reason"] == "Lean ran out of time"
    assert "budget ran out" in fact.provenance["lean_parts"][0]["reason"]


class _Decider:
    """A decision procedure that decides the claims Lean is handed, as loopty's isl does."""

    name = "solver"

    def trust_class(self) -> str:
        return "decision-procedure"

    def can_establish(self, fact: Fact) -> bool:
        return isinstance(fact.term, Stated)

    def establish(self, fact: Fact) -> Fact:
        return fact.with_status(Status.DECIDED, self.name)


def test_a_fallback_is_asked_only_when_omega_and_the_hints_fail(lean: LeanOracle) -> None:
    asked: list[str] = []

    def splits() -> Hints:
        asked.append("asked")
        return Hints(splits=(LogicalOr(((x == 1), (x == 2))),))

    pugh = claim(
        (x, y),
        [
            11 * x + 13 * y >= 27,
            11 * x + 13 * y <= 45,
            7 * x - 9 * y >= -10,
            7 * x - 9 * y <= 4,
        ],
        False,
    )
    part = Part("pugh", "Pugh's example", pugh, fallback=splits)
    fact = lean.establish(fact_of(Obligation(parts=(part,))))
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_parts"][0]["how"] == "omega, with a case split"
    assert asked == ["asked"]
    easy = Part("S0", "x in bounds", IN_BOUNDS.term, fallback=splits)
    assert lean.establish(fact_of(Obligation(parts=(easy,)))).status is Status.PROVED
    assert asked == ["asked"]


def test_lean_goes_first_and_the_solver_decides_what_it_does_not_prove(
    lean: LeanOracle, monkeypatch
) -> None:
    monkeypatch.setattr(registry, "oracles", [lean, _Decider()])
    proved = establish(fact_of(Obligation(parts=(IN_BOUNDS,), decider="solver")))
    assert proved.status is Status.PROVED and proved.decided_by == "lean"
    wrong = Part("S1", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    decided = establish(fact_of(Obligation(parts=(wrong,), decider="solver")))
    assert decided.status is Status.DECIDED and decided.decided_by == "solver"
    assert decided.provenance["lean_reason"] == "Lean found no proof"


def test_the_ledger_names_what_lean_did_not_prove_and_shows_the_lean(
    lean: LeanOracle, capsys
) -> None:
    proved = lean.establish(
        fact_of(Obligation(parts=(IN_BOUNDS,), decider="isl", stated_by="kit"))
    )
    assert proved.provenance["lean_stated_by"] == "kit"
    wrong = Part("S1", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    handed = Fact(
        id="in-bounds:kernel@1:S1",
        kind="in-bounds",
        statement="x[x + 1] is in bounds for every instance of S1",
        term=Stated(Obligation(parts=(wrong,), decider="isl", stated_by="kit")),
        where="kernel.py:2",
        owner="kernel",
    )
    unproved = lean.establish(handed).with_status(Status.DECIDED, "isl")
    alone = Fact(
        id="layout:kernel@1:x",
        kind="layout",
        statement="the rows of x stay apart",
        term=Stated(Obligation(declined="stated for isl only")),
        where="kernel.py:3",
        owner="kernel",
    )
    alone = lean.establish(alone).with_status(Status.DECIDED, "isl")
    CheckVerb._report(Ledger([proved, unproved, alone]), show_lean="")
    out = capsys.readouterr().out
    assert (
        "LEAN proved 1 of the 3 facts isl decided; 1 is NOT PROVED below; 1 is not "
        "stated for Lean yet (--verbose says why). Lean's statements are kit's, "
        "from its own description, not isl's results, and isl's hints were "
        "checked, not trusted. --show-lean prints the Lean."
    ) in out
    assert "NOT PROVED kernel at kernel.py:2: x[x + 1] is in bounds for every instance of S1" in out
    assert (
        "  isl decided it; Lean found no proof (--show-lean shows what Lean said)" in out
    )
    assert "LEAN kernel at kernel.py:1: x[i] is in bounds for every instance of S0" in out
    assert "  proved by Lean (omega)" in out
    assert "    theorem Lanky.kernel_S0" in out
    assert "  part S1 (x + 1 < n): not proved: no script closed it" in out
    # the rows a text names, and only those
    CheckVerb._report(Ledger([proved, unproved]), show_lean="S1")
    shown = capsys.readouterr().out.split("\nLEAN kernel ", 1)[1]
    assert shown.startswith("at kernel.py:2")


# }}}
