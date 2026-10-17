"""What lanky sends Lean, and what Lean has to answer, before a claim reads proved.

Four guards, each tested here without Lean, and against Lean where it is
installed:

- *names*: a theorem's hypotheses keep their Python names in the printed
  Lean (``pde``, ``stored_1``), quoted or printed from the root where Lean
  would read them otherwise;
- *the axiom audit*: every command ends with ``#print axioms _root_.<name>``
  of each theorem it declares, and only a positive answer is a proof. The
  design's V3 (a tactic ending in ``#exit``, which skips the audit, and
  ``native_decide``, whose axiom the audit shows) and V4 (a decoy theorem in
  another namespace) fail closed;
- *the screen*: ``use_tactic`` refuses a script with a command in it;
- *citations*: a part that cites a claim restates the text the claim's own
  command proved (``as_cited``). The design's T4, a citation restated
  without its condition, which proves ``1 = 0``, is refused before Lean is
  asked.
"""

from __future__ import annotations

import os
import subprocess
import sys
import textwrap
from collections.abc import Iterator
from typing import Any

import pytest

from lanky import theorem
from lanky.audit import TRUSTED_AXIOMS, audit_failure, audit_lines, audited, screen
from lanky.citations import Proved, ProvedTexts, restatements
from lanky.lean import LeanStatement, statement_of
from lanky.ledger import Fact, Status
from lanky.obligations import Citation, Hints, Instance, Obligation, Part, part_statement
from lanky.oracles.lean import (
    UNAUDITED,
    LeanOracle,
    LeanSession,
    ProofCache,
    claim_statement,
    use_tactic,
)
from lanky.prelude import Fin, Fn, Int, Nat
from lanky.terms import Forall, LogicalAnd, Var

# {{{ claims


@theorem
def compressed_taylor(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D(a + 2, b) + D(a, b + 2) == 0 for a in Nat for b in Nat),
    stored: all(R(a, b) == D(a, b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2, b) == -R(a, b + 2) for a in Nat for b in Nat),
) -> all(R(a, b) == D(a, b) for a in Nat for b in Nat):
    """The l2p claim, its hypotheses named as the file names them."""


@theorem
def both(n: Nat, m: Nat, bounds: (n < 10) & (m < 10)) -> n + m < 20:
    """A hypothesis written ``p & q`` is two hypotheses of the Lean theorem."""


@theorem
def guarded(n: Nat, h0: n > 3) -> n - 1 > 2:
    """A hypothesis named like the ones lanky names: lanky's take another name."""


@theorem
def keyworded(n: Nat, fun: n > 0) -> n - 1 >= 0:
    """A hypothesis named like a Lean keyword is quoted."""


@theorem
def rooted(n: Nat, m: Nat, Int: m > 0) -> n // m >= 0:
    """A hypothesis named like a root name has that name printed from the root."""


@theorem
def nonneg(n: Nat) -> n >= 0:
    """The core Lean analogue of the design's ``log_of_a_power``: its condition is ``0 ≤ n``."""


@theorem
def picks_a_cell(nc: Nat, nv: Nat, cell: Fn[Fin[nc], Fin[nv]]) -> all(
    cell(c) < nv for c in Fin[nc]
):
    """A family whose values are cells: its bound is a hypothesis of the Lean theorem."""


@theorem
def bounded_by_goal(k: Nat, n: Nat, k_small: k < n) -> all(k < n + j for j in Nat if j > 0):
    """A goal binder that is not named like a hypothesis keeps its name."""


# }}}


# {{{ names


def test_hypotheses_keep_their_python_names() -> None:
    fact = compressed_taylor.fact()
    assert fact.provenance["hypothesis_names"] == ["pde", "stored", "recurrence"]
    statement = claim_statement(fact, False)
    names = [name for name, _ in statement.hypotheses]
    assert names[-3:] == ["pde", "stored", "recurrence"]
    source = statement.source("omega")
    assert "(pde : ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → " in source
    assert "(stored : ∀ a : Int, " in source
    assert "(recurrence : ∀ a : Int, " in source
    # the hypotheses lanky adds are named apart from them, as before
    assert not any(name.startswith("h") for name in names[-3:])


def test_a_conjunction_names_its_parts() -> None:
    assert both.hypothesis_names == ("bounds_1", "bounds_2")
    statement = claim_statement(both.fact(), False)
    assert ("bounds_1", "n < 10") in statement.hypotheses
    assert ("bounds_2", "m < 10") in statement.hypotheses


def test_lankys_own_names_keep_clear_of_the_pythons() -> None:
    statement = claim_statement(guarded.fact(), False)
    assert statement.hypotheses[0] == ("h0_1", "0 ≤ n")
    assert statement.hypotheses[-1] == ("h0", "n > 3")


def test_a_keyword_is_quoted_and_a_root_name_is_printed_from_the_root() -> None:
    statement = claim_statement(keyworded.fact(), False)
    assert statement.hypotheses[-1] == ("«fun»", "n > 0")
    rooted_statement = claim_statement(rooted.fact(), False)
    assert rooted_statement.hypotheses[-1] == ("Int", "m > 0")
    assert rooted_statement.goal == "_root_.Int.fdiv n m ≥ 0"
    assert rooted_statement.binders[0] == ("n", "_root_.Int")
    assert "Int" in rooted_statement.shadowed


def test_a_goal_variable_named_like_a_hypothesis_is_introduced_apart() -> None:
    from lanky.oracles.lean import _goal_intro

    @theorem
    def shadowing(n: Nat, j: n > 0) -> all(n + j > 0 for j in Nat):
        """The hypothesis j and the goal's j."""

    statement = claim_statement(shadowing.fact(), False)
    names, _, _, _, introduced = _goal_intro(statement)
    assert introduced["j"] == "j_1"
    assert names[0] == "j_1"
    plain = claim_statement(bounded_by_goal.fact(), False)
    assert _goal_intro(plain)[4]["j"] == "j"


def test_the_names_do_not_change_the_text_a_citation_restates() -> None:
    """``as_cited`` is the claim as one proposition, whatever its hypotheses are called."""
    named = claim_statement(compressed_taylor.fact(), False)
    plain = statement_of(compressed_taylor.term, "compressed_taylor")
    assert named.as_cited == plain.as_cited


# }}}


# {{{ the command, and its audit


def test_every_command_ends_with_the_audit_of_what_it_declares() -> None:
    statement = claim_statement(nonneg.fact(), False)
    source = statement.source("omega")
    assert source.endswith(
        "\n#print axioms _root_.Lanky.nonneg\n#print axioms _root_.Lanky.nonneg.as_cited\n"
    )
    assert audited(source) == ("Lanky.nonneg", "Lanky.nonneg.as_cited")
    assert (
        "theorem Lanky.nonneg.as_cited :\n    ∀ n : Int, 0 ≤ n → n ≥ 0 :=\n  Lanky.nonneg\n"
    ) in source
    # a part, a side condition or a question proves no as_cited text
    part = statement_of(nonneg.term, "nonneg")
    assert audited(part.source("omega")) == ("Lanky.nonneg",)


def test_a_familys_bound_is_bracketed_in_the_text_a_citation_restates() -> None:
    """``as_cited`` puts the bound of a family of cells to the left of an arrow.

    Printed as a parameter it needs no brackets; as the antecedent of the
    rest it does, or its ``∀`` would take the rest in, and the command's
    ``as_cited`` would not follow from the theorem.
    """
    statement = claim_statement(picks_a_cell.fact(), False)
    assert statement.as_cited == (
        "∀ nc : Int, 0 ≤ nc → ∀ nv : Int, 0 ≤ nv → ∀ cell : Int → Nat, "
        "(∀ cell_arg : Int, 0 ≤ cell_arg → cell_arg < nc → (cell cell_arg : Int) < nv) → "
        "∀ c : Int, 0 ≤ c → c < nc → (cell c : Int) < nv"
    )


def test_a_script_cannot_write_lankys_audit() -> None:
    """Every line of a script is indented, so it is never read as lanky's audit."""
    statement = statement_of(nonneg.term, "nonneg")
    source = statement.source("native_decide\n#print axioms _root_.Lanky.clean")
    assert audited(source) == ("Lanky.nonneg",)
    assert audit_lines(("Lanky.a", "Lanky.«fun»")) == (
        "#print axioms _root_.Lanky.a\n#print axioms _root_.Lanky.«fun»"
    )


@pytest.mark.parametrize(
    ("messages", "names", "found"),
    [
        (["'Lanky.t' does not depend on any axioms"], ["Lanky.t"], None),
        (
            ["'Lanky.t' depends on axioms: [propext, Classical.choice, Quot.sound]"],
            ["Lanky.t"],
            None,
        ),
        (["'Lanky.fun' depends on axioms: [propext]"], ["Lanky.«fun»"], None),
        (
            ["'Lanky.t' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"],
            ["Lanky.t"],
            None,
        ),
        # V3: a script ending in #exit stops Lean before the audit
        (["using 'exit' to interrupt Lean"], ["Lanky.t"], "did not answer the axiom audit"),
        # V4: a decoy in another namespace answers about another theorem
        (["'Decoy.Lanky.t' does not depend on any axioms"], ["Lanky.t"], "did not answer"),
        # native_decide's axiom, and sorry's
        (
            ["'Lanky.t' depends on axioms: [Lanky.t._native.native_decide.ax_1_1]"],
            ["Lanky.t"],
            "rests on Lanky.t._native.native_decide.ax_1_1",
        ),
        (["'Lanky.t' depends on axioms: [propext, sorryAx]"], ["Lanky.t"], "rests on sorryAx"),
        (
            ["'Lanky.t' does not depend on any axioms"] * 2,
            ["Lanky.t"],
            "answered the axiom audit of Lanky.t 2 times",
        ),
        (
            ["'Lanky.t' does not depend on any axioms"],
            ["Lanky.t", "Lanky.t.as_cited"],
            "did not answer the axiom audit of Lanky.t.as_cited",
        ),
    ],
)
def test_only_a_positive_audit_passes(messages: list, names: list, found: str | None) -> None:
    failure = audit_failure(messages, names)
    if found is None:
        assert failure is None
    else:
        assert failure is not None and found in failure, failure
    assert {"propext", "Classical.choice", "Quot.sound"} == TRUSTED_AXIOMS


class _Server:
    """A REPL that answers each command with the messages it is given."""

    def __init__(self, messages: list[str]) -> None:
        self.messages = messages

    def is_alive(self) -> bool:
        return True

    def run(self, command, timeout=None):
        from types import SimpleNamespace

        return SimpleNamespace(
            messages=tuple(
                SimpleNamespace(severity="info", data=message) for message in self.messages
            ),
            sorries=(),
        )


@pytest.fixture
def fake_repl(monkeypatch: pytest.MonkeyPatch) -> Iterator[Any]:
    from types import SimpleNamespace

    monkeypatch.setitem(
        sys.modules, "lean_interact", SimpleNamespace(Command=lambda **fields: fields)
    )

    def session(messages: list[str]) -> LeanSession:
        made = LeanSession(timeout=60)
        made.server = _Server(messages)
        return made

    yield session


def test_a_session_takes_a_command_only_on_its_positive_audit(fake_repl) -> None:
    statement = statement_of(nonneg.term, "nonneg")
    source = statement.source("omega")
    clean = fake_repl(["'Lanky.nonneg' depends on axioms: [propext]"])
    assert clean.answer(source) == (True, "", True)
    # V3 and V4, as Lean answers them: no answer, and an answer about a decoy
    for said in ([], ["'Decoy.Lanky.nonneg' does not depend on any axioms"]):
        closed, detail, answered = fake_repl(said).answer(source)
        assert not closed and answered
        assert detail.startswith("Lean did not answer the axiom audit of Lanky.nonneg")
    # a source that audits nothing is not audited by the session, which runs what it is given
    assert fake_repl([]).answer("theorem t : True := trivial\n") == (True, "", True)


def test_the_oracle_sends_no_command_without_its_audit(fake_repl) -> None:
    oracle = LeanOracle()
    session = fake_repl([])
    assert oracle._ask(session, "theorem t : True := trivial\n", None) == (
        False,
        UNAUDITED,
        False,
        True,
    )


# }}}


# {{{ the screen


@pytest.mark.parametrize(
    ("script", "found"),
    [
        ("native_decide\n#exit", "#exit"),  # V3
        ("omega\n  #print axioms Lanky.t", "#print"),
        ("native_decide", "native_decide"),
        ("decide +native", "native"),
        ("native_decide\nnamespace Decoy\ntheorem Lanky.t : True := trivial", "native_decide"),
        ("trivial\nnamespace Decoy\ntheorem Lanky.t : True := trivial", "namespace"),  # V4
        ("trivial\nend\ntheorem Lanky.t : True := trivial", "end"),
        ("set_option debug.skipKernelTC true in omega", "set_option"),
        ("exact Lean.ofReduceBool _ _ rfl", "ofReduceBool"),
        ("omega\n/- the audit is in here", "block comment"),
        ("open Classical in simp", "open"),
        ("run_tac pure ()", "run_tac"),
    ],
)
def test_the_screen_refuses_what_a_proof_never_needs(script: str, found: str) -> None:
    refused = screen(script)
    assert refused is not None and found in refused, refused


@pytest.mark.parametrize(
    "script",
    [
        "omega",
        "intro a ha0 ha b hb0 hb hab\nobtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hb0\n"
        "induction b with\n| zero => omega\n| succ k ih => omega",
        "exact ⟨-1, Or.inr ⟨by decide, rfl⟩⟩",
        "have h : (2 * n + 1) / 2 = n := by omega\nrw [h]",
        "infer_instance",
        "simp [Function.update_def, Nat.succ_le_iff]",
        "omega -- the end of the proof, and #exit in a comment",
        "/- a closed comment -/ omega",
        "sleep 60000\n  omega",
    ],
)
def test_the_screen_passes_a_proof(script: str) -> None:
    assert screen(script) is None


def test_a_library_proof_may_give_a_step_its_heartbeats() -> None:
    script = "set_option maxHeartbeats 400000 in\nnlinarith [sq_nonneg x]"
    assert screen(script, library=True) is None
    assert "set_option" in screen(script)
    assert "set_option" in screen("set_option maxRecDepth 4000 in simp", library=True)


def test_use_tactic_refuses_a_script_where_it_is_written() -> None:
    with pytest.raises(ValueError, match=r"use_tactic\(nonneg, \.\.\.\): .* it has #exit"):
        use_tactic(nonneg, "native_decide\n#exit")
    assert all(nonneg.fact_id not in oracle.tactics for oracle in _oracles())


def test_a_script_set_by_hand_is_screened_before_lean(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    fact = nonneg.fact()
    oracle.tactics[fact.id] = "native_decide\n#exit"
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    assert result.provenance["lean_declined"].startswith(
        "the tactic script given for it is not sent to Lean: it has #exit"
    )


def _oracles() -> list[LeanOracle]:
    from lanky.oracles.lean import _lean_oracles

    return _lean_oracles()


# }}}


# {{{ citations


def _no_lean(monkeypatch: pytest.MonkeyPatch, tmp_path) -> LeanOracle:
    """An oracle whose session cannot start, with a proof cache of its own."""
    monkeypatch.setenv("LANKY_LEAN_VERSION", "v0.0.0-test")
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)

    def start(session: LeanSession) -> bool:
        session.error = "no Lean in this test"
        return False

    monkeypatch.setattr(LeanSession, "start", start)
    oracle = LeanOracle()
    monkeypatch.setattr(oracle, "availability", lambda: (True, ""))
    oracle.proofs = ProofCache(str(tmp_path / "proofs"))
    return oracle


def _answering(monkeypatch: pytest.MonkeyPatch) -> list[str]:
    """Every command closes; the sources sent, in order."""
    sent: list[str] = []

    def answer(session: LeanSession, source: str, until: float | None = None) -> tuple:
        sent.append(source)
        return True, "", True

    monkeypatch.setattr(LeanSession, "ready", lambda session: True)
    monkeypatch.setattr(LeanSession, "answer", answer)
    return sent


class _Stated:
    """A plugin's claim that states itself for Lean."""

    def __init__(self, obligation: Obligation) -> None:
        self.obligation = obligation

    def lean_obligation(self) -> Obligation:
        return self.obligation

    def __str__(self) -> str:
        return "a plugin's claim"


def _cited_fact(*parts: Part) -> Fact:
    return Fact(
        id="applied:kernel@1:nonneg",
        kind="applied",
        statement="nonneg applied to the kernel",
        term=_Stated(Obligation(parts=parts, rests_on=(nonneg.fact_id,))),
        status=Status.DECIDED,
        decided_by="theorem",
        where="kernel.py:1",
        owner="kernel",
    )


m = Var("m")
n = Var("n")

#: ``nonneg`` restated without its condition: every integer is not negative.
MISRESTATED = Forall(((n, Int),), n >= 0)

#: The part T4 is: a misrestated citation, and a claim it proves, ``m = m + 1``.
T4_TERM = Forall(((m, Int),), m == m + 1, MISRESTATED)
T4_HINTS = Hints(instances=(Instance(0, (-1,)),))


def _cited(term: Any, hints: Hints | None = None) -> Part:
    return Part(
        "applied",
        "nonneg applied",
        term,
        hints or Hints(),
        citations=(Citation(0, nonneg.fact_id, "nonneg"),),
    )


def test_a_proved_claim_keeps_its_as_cited_text(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    sent = _answering(monkeypatch)
    proved = oracle.establish(nonneg.fact())
    assert proved.status is Status.PROVED
    text = "∀ n : Int, 0 ≤ n → n ≥ 0"
    assert proved.provenance["lean_as_cited"] == text
    kept = oracle.proved_texts.get(nonneg.fact_id)
    assert kept is not None and kept.text == text and kept.name == "Lanky.nonneg"
    assert f"theorem Lanky.nonneg.as_cited :\n    {text} :=" in sent[0]


def test_a_part_restates_a_citation_from_the_text_its_command_proved(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    sent = _answering(monkeypatch)
    oracle.establish(nonneg.fact())
    sent.clear()
    good = _cited(Forall(((m, Nat),), m + 1 > 0, nonneg.term))
    result = oracle.establish(_cited_fact(good))
    assert result.status is Status.PROVED, result.provenance.get("lean_reason")
    head = sent[0].splitlines()[1]
    # the restated hypothesis comes first, before any variable of the part
    assert head.startswith("theorem Lanky.kernel_applied (h1 : ∀ n : Int, 0 ≤ n → n ≥ 0) (m : Int)")
    (record,) = result.provenance["lean_parts"]
    assert record["cited"][0]["restated"] == "as Lanky.nonneg.as_cited, which its command proved"
    assert "lean_restated_by_printer" not in result.provenance


def test_t4_a_misrestated_citation_is_refused_before_lean(monkeypatch, tmp_path) -> None:
    """T4: ``nonneg`` restated without ``0 ≤ n`` proves ``m = m + 1``; cited, Lean is not asked."""
    oracle = _no_lean(monkeypatch, tmp_path)
    sent = _answering(monkeypatch)
    oracle.establish(nonneg.fact())
    sent.clear()
    result = oracle.establish(_cited_fact(_cited(T4_TERM, T4_HINTS)))
    assert result.status is Status.DECIDED
    assert sent == []
    assert result.provenance["lean_reason"] == (
        "Lean was not asked, since the part restates a cited theorem other than as "
        "Lean proved it"
    )
    (record,) = result.provenance["lean_parts"]
    assert not record["proved"]
    assert record["reason"].startswith(
        "the part restates nonneg as something other than the statement Lean proved of it"
    )


def test_a_citation_with_no_proved_text_is_restated_by_the_printer(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    sent = _answering(monkeypatch)
    good = _cited(Forall(((m, Nat),), m + 1 > 0, nonneg.term))
    result = oracle.establish(_cited_fact(good))
    assert result.status is Status.PROVED
    assert result.provenance["lean_restated_by_printer"] == ["nonneg"]
    (record,) = result.provenance["lean_parts"]
    assert record["cited"][0]["restated"] == "by the printer"
    # printed where it always was, after the variables
    assert "(m : Int) (h0 : 0 ≤ m) (h1 : ∀ n : Int, 0 ≤ n → n ≥ 0)" in sent[0]


def test_a_claim_checked_again_and_not_proved_keeps_no_text(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    _answering(monkeypatch)
    oracle.establish(nonneg.fact())
    assert nonneg.fact_id in oracle.proved_texts
    oracle.declines[nonneg.fact_id] = "left to the tester"
    oracle.establish(nonneg.fact())
    assert nonneg.fact_id not in oracle.proved_texts


def test_a_text_that_changes_drops_the_texts_whose_proofs_cited_it() -> None:
    """Citations of citations: a premise's text changed, its citers' texts go (Codex, #171).

    ``b``'s proof cited ``a``, and ``c``'s cited ``b``: their ``as_cited``
    theorems take ``a``'s old text as a hypothesis, all the way up, so a
    citation of ``c`` would restate it. A new text for ``a``, ``a`` no
    longer proved, or ``a`` changed under its fact id, drops both.
    """
    from dataclasses import replace

    a = Proved("a", "Lanky.a", "A", False, nonneg.term)
    b = Proved("b", "Lanky.b", "B", False, T4_TERM, ("a",))
    c = Proved("c", "Lanky.c", "C", False, MISRESTATED, ("b",))
    texts = ProvedTexts()
    for proved in (a, b, c):
        texts.record(proved)
    texts.record(a)
    assert len(texts) == 3, "the same text again keeps its citers"
    texts.record(replace(a, text="A, changed"))
    assert "b" not in texts and "c" not in texts and texts.get("a").text == "A, changed"
    for proved in (a, b, c):
        texts.record(proved)
    texts.forget("a")
    assert len(texts) == 0
    for proved in (a, b, c):
        texts.record(proved)
    assert texts.stale({"a": MISRESTATED, "b": T4_TERM, "c": MISRESTATED}) == ["a"]
    assert len(texts) == 0


def test_restatements_are_refused_for_a_hypothesis_the_part_does_not_have() -> None:
    texts = ProvedTexts()
    texts.record(
        Proved(nonneg.fact_id, "Lanky.nonneg", "∀ n : Int, 0 ≤ n → n ≥ 0", False, nonneg.term)
    )
    part = Part(
        "p", "p", Forall(((m, Nat),), m >= 0), citations=(Citation(3, nonneg.fact_id, "nonneg"),)
    )
    assert restatements(part, texts).refused.startswith("the part cites nonneg at hypothesis 3")
    stated = part_statement(
        Part("p", "p", Forall(((m, Nat),), m >= 0, LogicalAnd((nonneg.term, m < 5)))),
        "kernel_p",
        {0: "∀ n : Int, 0 ≤ n → n ≥ 0"},
    )
    assert stated.restated == ((1, "∀ n : Int, 0 ≤ n → n ≥ 0"),)
    assert stated.parameters.startswith("(h1 : ∀ n : Int, 0 ≤ n → n ≥ 0) (m : Int) (h0 : 0 ≤ m)")
    assert stated.proposition.startswith("(∀ n : Int, 0 ≤ n → n ≥ 0) → ∀ m : Int, 0 ≤ m → ")


# }}}


# {{{ show-lean


def test_show_lean_renames_a_theorem_everywhere_its_row_names_it() -> None:
    from lanky.cli import _named_apart

    row = statement_of(nonneg.term, "nonneg", citable=True).source("omega").splitlines()
    first, second = _named_apart([row, list(row)])
    assert first == row
    assert "theorem Lanky.nonneg_2 : ∀ n : Int, 0 ≤ n → n ≥ 0 := by" not in second
    assert any(line.startswith("theorem Lanky.nonneg_2 ") for line in second)
    assert "theorem Lanky.nonneg_2.as_cited :" in second
    assert "  Lanky.nonneg_2" in second
    assert second[-2:] == [
        "#print axioms _root_.Lanky.nonneg_2",
        "#print axioms _root_.Lanky.nonneg_2.as_cited",
    ]


# }}}


# {{{ the same source on every run


_SOURCES = textwrap.dedent(
    """
    from __future__ import annotations

    from lanky import theorem
    from lanky.oracles.lean import claim_statement, tactic_ladder
    from lanky.prelude import Fin, Fn, Nat

    @theorem
    def scan(
        size: Nat,
        cnt: Fn[Fin[size], Nat],
        off: Fn[Fin[size + 1], Nat],
        first: off(0) == 0,
        step: all(off(r + 1) == off(r) + cnt(r) for r in Fin[size]),
        both: (size < 100) & (size >= 0),
    ) -> all(off(p) <= off(q) for p in Fin[size + 1] for q in Fin[size + 1] if p <= q):
        ...

    statement = claim_statement(scan.fact(), False)
    for tactic in tactic_ladder(statement):
        print(statement.source(tactic))
    """
)


def test_a_claim_is_sent_as_the_same_source_whatever_the_hash_seed() -> None:
    """The proof cache is keyed by the source, so a warm check needs the same source."""
    outputs = []
    for seed in ("1", "2"):
        environment = {**os.environ, "PYTHONHASHSEED": seed}
        done = subprocess.run(
            [sys.executable, "-c", _SOURCES],
            capture_output=True,
            text=True,
            env=environment,
            timeout=300,
            check=False,
        )
        assert done.returncode == 0, done.stderr
        outputs.append(done.stdout)
    assert outputs[0] == outputs[1]
    assert "(first : (off 0 : Int) = 0)" in outputs[0]


# }}}


# {{{ against Lean


@pytest.fixture(scope="module")
def lean() -> Iterator[LeanOracle]:
    from test_lean import _open_lean_oracle

    oracle = _open_lean_oracle()
    yield oracle
    oracle.session.close()


#: A statement ``native_decide`` closes, written as lanky would print it.
_DECIDED = LeanStatement("nd", (), (), "(12345 : Nat) * 6789 = 83810205")


def test_v3_a_script_that_skips_the_audit_is_no_proof(lean: LeanOracle) -> None:
    closed, detail = lean.session.run(_DECIDED.source("native_decide\n#exit"))
    assert not closed
    assert detail.startswith("Lean did not answer the axiom audit of Lanky.nd"), detail
    closed, detail = lean.session.run(_DECIDED.source("native_decide"))
    assert not closed
    assert detail.startswith("Lanky.nd rests on Lanky.nd._native.native_decide.ax_1_1"), detail
    assert lean.session.run(_DECIDED.source("decide")) == (True, "")


def test_v4_a_decoy_in_another_namespace_is_no_proof(lean: LeanOracle) -> None:
    for first in ("native_decide", "sorry"):
        closed, detail = lean.session.run(
            _DECIDED.source(f"{first}\nnamespace Decoy\ntheorem Lanky.nd : True := trivial")
        )
        assert not closed, detail


def test_a_claim_is_proved_with_its_names_and_its_as_cited_text(lean: LeanOracle) -> None:
    proved = lean.establish(guarded.fact())
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    source = proved.provenance["lean_source"]
    assert "(h0_1 : 0 ≤ n) (h0 : n > 3)" in source
    assert "theorem Lanky.guarded.as_cited :" in source
    assert proved.provenance["lean_as_cited"] == "∀ n : Int, 0 ≤ n → n > 3 → n - 1 > 2"


def test_the_as_cited_text_of_a_family_of_cells_follows_from_its_theorem(
    lean: LeanOracle,
) -> None:
    proved = lean.establish(picks_a_cell.fact())
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    assert "theorem Lanky.picks_a_cell.as_cited :" in proved.provenance["lean_source"]


def test_t4_against_lean(lean: LeanOracle) -> None:
    """The misrestated citation proves ``m = m + 1`` when it is trusted, and is refused cited."""
    assert lean.establish(nonneg.fact()).status is Status.PROVED
    trusted = Part("trusted", "trusted", T4_TERM, T4_HINTS)
    shown = lean.establish(_cited_fact(trusted))
    assert shown.status is Status.PROVED, "T4 no longer reproduces: the control proves nothing"
    refused = lean.establish(_cited_fact(_cited(T4_TERM, T4_HINTS)))
    assert refused.status is Status.DECIDED
    good = lean.establish(_cited_fact(_cited(Forall(((m, Nat),), m + 1 > 0, nonneg.term))))
    assert good.status is Status.PROVED, good.provenance.get("lean_reason")
    assert "(h1 : ∀ n : Int, 0 ≤ n → n ≥ 0) (m : Int)" in good.provenance["lean_source"]


# }}}
