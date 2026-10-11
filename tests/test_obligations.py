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
)
from lanky.oracles.lean import LeanOracle, ProofCache
from lanky.plugins import registry
from lanky.prelude import FinType, Fn, Int
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
    assert reason.startswith("Lean proved 1 of its 2 parts, and not S1 (x[x + 1] over 0 <= x < n)")
    assert "Lean said" in reason
    assert [record["proved"] for record in fact.provenance["lean_parts"]] == [True, False]


def test_an_existential_goal_is_proved_with_its_witness(lean: LeanOracle) -> None:
    bare = Part("total", "the split is total", SPLIT_TOTAL)
    fact = lean.establish(fact_of(Obligation(parts=(bare,))))
    assert fact.status is Status.ASSUMED
    assert "no witness was given" in fact.provenance["lean_reason"]
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
    assert fact.provenance["lean_counterexample"] == (
        "Lean proved the claim false at x=1 at n=2, by decide"
    )
    assert "theorem Lanky.kernel_S0_false" in fact.provenance["lean_refutation"]
    assert refutation_lines(fact)[-1] == fact.provenance["lean_counterexample"]


def test_a_counterexample_that_is_none_is_caught(lean: LeanOracle) -> None:
    part = Part("S0", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    bogus = Obligation(
        parts=(part,), counterexample=Counterexample("S0", {"n": 3, "x": 0}, "x=0 at n=3")
    )
    fact = lean.establish(fact_of(bogus, Status.REFUTED))
    assert fact.provenance["lean_disagrees"] is True
    assert fact.provenance["lean_counterexample"].startswith(
        "Lean could not prove the claim false at x=0 at n=3"
    )


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
    assert "budget ran out" in fact.provenance["lean_reason"]


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
    assert decided.provenance["lean_reason"].startswith("Lean did not prove it")


def test_the_ledger_names_what_lean_did_not_prove_and_shows_the_lean(
    lean: LeanOracle, capsys
) -> None:
    proved = lean.establish(fact_of(Obligation(parts=(IN_BOUNDS,), decider="isl")))
    wrong = Part("S1", "x + 1 < n", claim((n, x), [x >= 0, x < n], x + 1 < n))
    handed = Fact(
        id="in-bounds:kernel@1:S1",
        kind="in-bounds",
        statement="x[x + 1] is in bounds for every instance of S1",
        term=Stated(Obligation(parts=(wrong,), decider="isl")),
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
        "LEAN proved 1 of the 2 facts isl decided that were stated for it, each "
        "from the plugin's own statement of it, isl's hints checked and not "
        "trusted; 1 more isl decided was not stated for Lean (--verbose says "
        "why); --show-lean prints the Lean"
    ) in out
    assert "NOT PROVED kernel at kernel.py:2: x[x + 1] is in bounds for every instance of S1" in out
    assert "  isl decided it; Lean did not prove it: no script closed it" in out
    assert "LEAN kernel at kernel.py:1: x[i] is in bounds for every instance of S0" in out
    assert "  proved by Lean (omega)" in out
    assert "    theorem Lanky.kernel_S0" in out
    assert "  part S1 (x + 1 < n): not proved: no script closed it" in out
    # the rows a text names, and only those
    CheckVerb._report(Ledger([proved, unproved]), show_lean="S1")
    shown = capsys.readouterr().out.split("\nLEAN kernel ", 1)[1]
    assert shown.startswith("at kernel.py:2")


# }}}
