"""Written proofs that calculate: chains in a body, facts on the way, steps left open.

A proof's body may return a chain (:mod:`lanky.chains`), the calculation a
textbook displays, and name a step to cite it later. The trace reads each
link's reasons as citations, the compile makes the chain a ``calc`` whose
links are steps of their own, and an uncalled fact in a link is matched at the
one point that lines it up with the link (:mod:`lanky.matching`). The command
proves the claim's ``as_cited`` text too, which a proof that cites the claim
restates (:mod:`lanky.citations`), and it ends with the axiom audit of both
(:mod:`lanky.audit`). A link written ``by=...`` is left open: Lean accepts the
proof with holes, and the claim reads as the other oracles left it. Without
Lean, each link is drawn at points.

The Python half runs everywhere; the cases over the integers are checked with
core Lean where it is installed, and skip where it is not.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from conftest import claims
from lanky.check import check_path, import_path
from lanky.citations import CitedText, proved_texts
from lanky.ledger import Status
from lanky.proofs import ProofError, compile_proof, prove, trace_proof
from lanky.proofs.compile import Premise
from lanky.proofs.report import CLOSED_WITH_HOLES, verdict
from lanky.proofs.trace import Named

#: Proofs that calculate, over the integers, which core Lean checks.
CASES = '''\
"""Written proofs with chains, over the integers."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fn, Int, Nat


@theorem
def ct_chain(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
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
def ct_open(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    def claim(a, b):
        if a < 2:
            return stored
        return (
            R[a, b]
            .equals(-R[a - 2, b + 2], by=recurrence)
            .equals(-D[a - 2, b + 2], by=...)
            .equals(D[a, b], by=pde)
        )

    return claim


@theorem
def ct_reversed(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    def claim(a, b):
        if a < 2:
            return stored
        return (
            D[a, b]
            .equals(-D[a - 2, b + 2], by=pde)
            .equals(-R[a - 2, b + 2], by=claim(a - 2, b + 2))
            .equals(R[a, b], by=recurrence)
        )

    return claim


@theorem
def doubled(f: Fn[Nat, Int], h: all(f[k] == 2 * k for k in Nat)) -> f[3] + f[3] == 12:
    six = f[3].equals(6, by=h)
    return six


@theorem
def at_two(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> R[2, 0] == D[2, 0]:
    return ct_chain(D, R, 2, 0)


@theorem
def square(x: Int, y: Int, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    return (y * y).equals((x + 1) * (x + 1), by=h).equals(x * x + 2 * x + 1)


@theorem
def square_wrong(x: Int, y: Int, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    return (y * y).equals((x + 1) * (x + 1), by=h).equals(x * x + 2 * x + 2)


@theorem
def square_positional(x: Int, y: Int, /, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    return (y * y).equals((x + 1) * (x + 1), by=h).equals(x * x + 2 * x + 1)
'''


@pytest.fixture(scope="module")
def cases(tmp_path_factory) -> object:
    """The cases, imported."""
    path = tmp_path_factory.mktemp("chains") / "chains_cases.py"
    path.write_text(CASES, encoding="utf-8")
    return import_path(path)


def _line(module: object, text: str) -> int:
    """The line of the module's file that holds ``text``, the first one."""
    source = Path(module.__file__).read_text(encoding="utf-8").splitlines()
    return next(number for number, line in enumerate(source, 1) if text in line)


# {{{ the trace


def test_a_returned_chain_is_the_case_and_its_links_cite_facts(cases) -> None:
    proof = trace_proof(cases.ct_chain)
    (base, step) = proof.leaves
    assert base.chain is None and base.facts[0].name == "stored"
    chain = step.chain
    assert chain is not None and step.facts == ()
    assert [link.line for link in chain.links] == [
        _line(cases, ".equals(-R[a - 2, b + 2], by=recurrence)"),
        _line(cases, ".equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))"),
        _line(cases, ".equals(D[a, b], by=pde)"),
    ]
    reasons = [[citation.name for citation in link.facts] for link in chain.links]
    assert reasons == [["recurrence"], ["claim"], ["pde"]]
    assert [citation.text() for citation in proof.calls] == ["claim(a - 2, b + 2)"]


def test_a_named_step_is_a_fact_on_the_way(cases) -> None:
    proof = trace_proof(cases.doubled)
    (leaf,) = proof.leaves
    (named,) = leaf.named
    assert named.name == "six"
    (citation,) = leaf.facts
    assert isinstance(citation.source, Named) and citation.source.chain is named


def test_a_step_left_open_is_a_hole_at_its_line(cases) -> None:
    proof = trace_proof(cases.ct_open)
    assert proof.holes == [_line(cases, ".equals(-D[a - 2, b + 2], by=...)")]


# }}}


# {{{ the Lean a chain compiles to


def test_a_chain_is_a_calc_whose_links_are_steps(cases) -> None:
    command = compile_proof(trace_proof(cases.ct_chain), mathlib=False)
    source = command.source
    assert "  · calc R a b\n        = (-1) * R (a - 2) (b + 2) := by\n" in source
    assert "      _ = (-1) * D (a - 2) (b + 2) := by\n" in source
    # uncalled facts matched at the point that lines each up with its link
    assert "have f_2 := recurrence (a - 2) (by omega) b (by omega)" in source
    assert "have f_4 := pde (a - 2) (by omega) b (by omega)" in source
    assert "termination_by a.toNat" in source
    assert command.summary == "induction on a, 2 cases, 4 steps"
    assert [step.where for step in command.steps] == [
        _line(cases, "            return stored"),
        _line(cases, ".equals(-R[a - 2, b + 2], by=recurrence)"),
        _line(cases, ".equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))"),
        _line(cases, ".equals(D[a, b], by=pde)"),
    ]


def test_a_chain_the_other_way_round_gives_the_claim_from_it(cases) -> None:
    source = compile_proof(trace_proof(cases.ct_reversed), mathlib=False).source
    assert "  · have chain_1 :=\n      calc D a b\n" in source
    assert "      | exact chain_1.symm\n" in source


def test_a_chain_about_other_terms_than_the_claim_is_refused(cases) -> None:
    """Refused before Lean is asked where sympy can tell; without it, Lean refuses it."""
    pytest.importorskip("sympy", reason="the refusal compares the ends with sympy")
    with pytest.raises(ProofError) as raised:
        compile_proof(trace_proof(cases.square_wrong), mathlib=False)
    assert raised.value.kind == "chain"
    assert "the chain ends at x*x + 2*x + 2" in raised.value.message


def test_a_named_step_is_proved_in_a_have_and_cited_by_its_name(cases) -> None:
    command = compile_proof(trace_proof(cases.doubled), mathlib=False)
    assert "  have six : f 3 = 6 := by\n    have f_1 := h 3 (by omega)\n" in command.source
    assert command.summary == "2 steps, 1 named fact"
    assert [row[2] for row in command.outline] == ["six: f[3]", "f[3] + f[3]"]


def test_a_hole_is_a_sorry_whose_line_is_recorded(cases) -> None:
    command = compile_proof(trace_proof(cases.ct_open), mathlib=False)
    (hole,) = command.hole_lines
    assert command.source.splitlines()[hole - 1].strip() == "sorry"
    assert command.summary == "2 cases, 3 steps, 1 step left open"
    sorry = {"line": hole, "column": 10}
    audit = [
        {"severity": "info", "data": "'Lanky.ct_open' depends on axioms: [sorryAx]"},
    ]
    said, failures = verdict(None, command, {"messages": audit, "sorries": [sorry]})
    assert (said, failures) == (CLOSED_WITH_HOLES, [])
    stray = {"line": hole + 1, "column": 0}
    said, _ = verdict(None, command, {"messages": audit, "sorries": [stray]})
    assert said == "failed"


def test_a_theorem_with_positional_only_parameters_is_traced(cases) -> None:
    """Its parameters before ``/`` are passed by position (Codex, #171)."""
    traced = trace_proof(cases.square_positional)
    plain = trace_proof(cases.square)
    assert len(traced.leaves) == len(plain.leaves) == 1
    assert len(traced.leaves[0].chain.links) == len(plain.leaves[0].chain.links) == 2


def test_the_command_proves_the_text_a_citation_restates_and_audits_both(cases) -> None:
    command = compile_proof(trace_proof(cases.square), mathlib=False, as_cited="TEXT")
    assert "theorem Lanky.square.as_cited :\n    TEXT := by\n  intro x_1 x_2 x_3\n" in (
        command.source
    )
    assert "  exact Lanky.square x_1 x_2 x_3\n" in command.source
    assert command.audited == ("Lanky.square", "Lanky.square.as_cited")
    assert command.source.rstrip().endswith(
        "#print axioms _root_.Lanky.square\n#print axioms _root_.Lanky.square.as_cited"
    )


def test_a_cited_theorem_is_restated_by_the_text_its_command_proved(cases) -> None:
    """With its premises, the theorems its own proof cited, all the way down."""
    texts = {
        cases.ct_chain.fact_id: CitedText("ct_chain", "PROVED TEXT", ("theorem:other@1",)),
        "theorem:other@1": CitedText("other", "OTHER TEXT"),
    }
    with proved_texts(texts):
        command = compile_proof(trace_proof(cases.at_two), mathlib=False)
    assert "(ct_chain : PROVED TEXT)" in command.source
    assert "(other : OTHER TEXT)" in command.source
    assert command.rests_on == [cases.ct_chain.fact_id, "theorem:other@1"]
    assert isinstance(command.cited[-1], Premise)
    assert command.summary == "1 step, using ct_chain"


def test_a_text_proved_for_another_term_is_no_proved_text_of_the_theorem(cases) -> None:
    """A theorem changed under its fact id is restated by the printer (Codex, #171).

    In a long-lived process the oracle may still hold the text it proved for
    the theorem's earlier statement; a citation restates a text only while
    the term it was proved for is the theorem's.
    """
    from lanky.citations import Proved
    from lanky.proofs.compile import cited_text

    other = {"theorem:other@1": CitedText("other", "OTHER TEXT")}
    earlier = Proved(
        cases.ct_chain.fact_id,
        "Lanky.ct_chain",
        "PROVED TEXT",
        False,
        cases.square.term,
        ("theorem:other@1",),
    )
    with proved_texts({cases.ct_chain.fact_id: earlier, **other}):
        assert cited_text(cases.ct_chain, False) != "PROVED TEXT"
        command = compile_proof(trace_proof(cases.at_two), mathlib=False)
    assert "PROVED TEXT" not in command.source
    assert "OTHER TEXT" not in command.source
    assert command.rests_on == [cases.ct_chain.fact_id]
    current = Proved(
        cases.ct_chain.fact_id,
        "Lanky.ct_chain",
        "PROVED TEXT",
        False,
        cases.ct_chain.term,
        ("theorem:other@1",),
    )
    with proved_texts({cases.ct_chain.fact_id: current, **other}):
        assert cited_text(cases.ct_chain, False) == "PROVED TEXT"


# }}}


# {{{ without Lean


def test_without_lean_each_link_is_drawn_and_a_false_one_fails_at_its_line(
    cases, monkeypatch
) -> None:
    import lanky.proofs as proofs

    monkeypatch.setattr(proofs, "_lean_oracle", lambda: None)
    right = prove(cases.square, cases.square.fact())
    account = right.provenance["proof"]
    assert account["closed"] is None
    assert "tested step by step at drawn points" in account["reason"]
    wrong = prove(cases.square_wrong, cases.square_wrong.fact())
    account = wrong.provenance["proof"]
    assert account["closed"] is False
    (failure,) = account["failures"]
    assert failure["kind"] == "false"
    assert failure["line"] == _line(
        cases, "return (y * y).equals((x + 1) * (x + 1), by=h).equals(x * x + 2 * x + 2)"
    )


def test_without_lean_a_link_over_a_family_that_cannot_be_drawn_says_so(cases, monkeypatch) -> None:
    import lanky.proofs as proofs

    monkeypatch.setattr(proofs, "_lean_oracle", lambda: None)
    account = prove(cases.ct_chain, cases.ct_chain.fact()).provenance["proof"]
    assert account["closed"] is None
    assert "could not be drawn" in account["reason"]


# }}}


# {{{ with core Lean


def _lean_or_skip() -> None:
    """Skip a test that needs Lean, or fail it where Lean was promised."""
    from lanky.oracles.lean import LeanOracle

    reason = None
    if os.environ.get("LANKY_LEAN_DISABLE"):
        reason = "the Lean oracle is disabled by LANKY_LEAN_DISABLE"
    else:
        available, why = LeanOracle().availability()
        if not available:
            reason = f"no Lean oracle here: {why}"
    if reason is None:
        return
    if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


@pytest.fixture(scope="module")
def checked(tmp_path_factory) -> dict:
    """The cases checked with core Lean, by owner."""
    _lean_or_skip()
    path = tmp_path_factory.mktemp("lean_chains") / "chains_cases.py"
    path.write_text(CASES, encoding="utf-8")
    return {fact.owner: fact for fact in claims(check_path(path))}


@pytest.mark.parametrize(
    "owner", ["ct_chain", "ct_reversed", "doubled", "at_two", "square", "square_positional"]
)
def test_lean_accepts_the_proofs_that_calculate(checked, owner) -> None:
    fact = checked[owner]
    assert fact.provenance["proof"]["closed"] is True, fact.provenance["proof"]
    assert fact.status is Status.PROVED
    assert fact.provenance["lean_as_cited"]


def test_a_proof_cites_a_theorem_by_the_text_its_proof_proved(checked) -> None:
    cited = checked["ct_chain"]
    citing = checked["at_two"]
    assert cited.id in citing.rests_on
    assert (
        f"(ct_chain : {cited.provenance['lean_as_cited']})"
        in citing.provenance["proof"]["lean_source"]
    )


#: The design's T4 through a written proof: a cited statement that proves False.
T4_CASES = '''\
"""A proof whose citation, as lanky states it, proves False."""

from __future__ import annotations

from lanky import axiom, theorem
from lanky.prelude import Fn, Int, Nat


@axiom(cite="the design's T4: a printer that dropped a condition")
def every_integer_is_nonnegative(n: Int) -> n >= 0:
    """What a theorem about naturals would say if the printer dropped its condition."""


@theorem
def any_two_cells(f: Fn[Nat, Int]) -> f[0] == f[1]:
    return every_integer_is_nonnegative(-1)
'''


#: Two proofs that cite each other.
CIRCLE = '''\
"""Two proofs, each citing the other."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Int


@theorem
def ping(x: Int) -> x + 1 > x:
    return pong(x)


@theorem
def pong(x: Int) -> x + 1 > x:
    return ping(x)
'''


def test_every_proof_on_a_circle_of_citations_is_refused(tmp_path) -> None:
    """Both, not only the one whose citation closes the circle (Codex, #171)."""
    path = tmp_path / "circle_cases.py"
    path.write_text(CIRCLE, encoding="utf-8")
    facts = {fact.owner: fact for fact in claims(check_path(path))}
    for owner in ("ping", "pong"):
        account = facts[owner].provenance["proof"]
        assert account["closed"] is False, account
        (failure,) = account["failures"]
        assert failure["headline"] == "the proofs cite each other in a circle"


def test_a_proof_citing_a_fact_about_reals_is_left_to_mathlib_in_core_lean() -> None:
    """``log_of_the_modulus`` cites ``log_of_a_power``, which core Lean cannot state.

    Its proof is not checked there, and says that Mathlib would check it: it
    is no fault of the proof, which ``lanky check`` with Lean and without
    Mathlib reported as a failure, exiting 1 on the demonstration.
    """
    _lean_or_skip()
    path = Path(__file__).resolve().parent.parent / "examples" / "log_of_the_modulus.py"
    fact = {fact.owner: fact for fact in claims(check_path(path))}["log_of_the_modulus"]
    account = fact.provenance["proof"]
    assert account["closed"] is None, account
    assert "only Lean with Mathlib can state it" in account["reason"]


def test_t4_a_proof_from_citations_that_prove_false_fails(tmp_path) -> None:
    """The cited statement proves ``-1 >= 0``, and so anything; the proof is refused.

    The claim is false and about a table over ``Nat``, which no draw tests, so
    without the question the proof would read proved by Lean, resting on the
    axiom: the design's T4, a citation without a proved text, restated as the
    printer gives it. The oracles are asked whether the cited statements
    alone prove False, and they do.
    """
    _lean_or_skip()
    path = tmp_path / "t4_cases.py"
    path.write_text(T4_CASES, encoding="utf-8")
    fact = {fact.owner: fact for fact in claims(check_path(path))}["any_two_cells"]
    account = fact.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite"
    assert failure["headline"] == ("the theorem its proof cites without a proved text proves False")
    assert failure["lines"][0].startswith(
        "every_integer_is_nonnegative, as lanky states it for Lean, proves False (proved by "
    )
    assert fact.status is not Status.PROVED
    assert fact.provenance.get("tactic") != "its written proof"


def test_lean_accepts_a_proof_with_a_step_left_open_and_names_it(checked) -> None:
    fact = checked["ct_open"]
    account = fact.provenance["proof"]
    assert account["closed"] == "holes", account
    line = 1 + next(
        index
        for index, text in enumerate(CASES.splitlines())
        if ".equals(-D[a - 2, b + 2], by=...)" in text
    )
    assert account["holes"] == [f"chains_cases.py:{line}"]
    # the proof does not prove the claim: it reads as the other oracles left it
    assert fact.provenance.get("tactic") != "its written proof"


# }}}


def test_proofs_names_a_written_proof_where_the_search_found_none() -> None:
    from lanky.ledger import Fact
    from lanky.outline import proof_lines

    fact = Fact(
        id="theorem:m.t@3",
        kind="theorem",
        statement="t",
        status=Status.PROVED,
        decided_by="lean",
        provenance={"proof": {"closed": True, "where": "m.py:5-9"}},
        where="m.py:3",
        owner="t",
    )
    assert proof_lines(fact) == ["PROOF t at m.py:3, by its proof as written, m.py:5-9"]
