"""Written proofs that calculate: asserted steps, chains, steps left open.

A proof's body states its steps with ``assert``, Python's chained comparison
for a calculation a textbook displays, ``by(...)`` the reasons after it. The
trace reads each step by running the body again past it (:mod:`lanky.proofs.trace`),
the compile makes a chain a ``calc`` whose links are steps of their own, a
``have`` the rest of the case knows, and a fact cited by name alone is
matched at the one point that lines it up with the link it fits
(:mod:`lanky.matching`). The command proves the claim's ``as_cited`` text
too, which a proof that cites the claim restates (:mod:`lanky.citations`),
and it ends with the axiom audit of both (:mod:`lanky.audit`). A step
written ``by(...)`` is left open: Lean accepts the proof with holes, and the
claim reads as the other oracles left it. Without Lean, each link is drawn
at points.

The Python half runs everywhere; the cases over the integers are checked with
core Lean where it is installed, and skip where it is not.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from conftest import claims
from lanky.check import check_path, import_path
from lanky.citations import CitedText, Premise, proved_texts
from lanky.ledger import Status
from lanky.proofs import ProofError, compile_proof, prove, trace_proof
from lanky.proofs.report import CLOSED_WITH_HOLES, verdict
from lanky.proofs.trace import TracedChain

#: Proofs that calculate, over the integers, which core Lean checks.
CASES = '''\
"""Written proofs with chains, over the integers."""

from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fn, Int, Nat


@claim
def ct_chain(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in claim.dom:
        if a < 2:
            yield by(stored)
        else:
            assert (
                R[a, b]
                == -R[a - 2, b + 2]
                == -D[a - 2, b + 2]
                == D[a, b]
            ), by(recurrence, claim[a - 2, b + 2], pde)


@claim
def ct_open(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in claim.dom:
        if a < 2:
            yield by(stored)
        else:
            assert R[a, b] == -R[a - 2, b + 2], by(recurrence)
            assert -R[a - 2, b + 2] == -D[a - 2, b + 2], by(...)
            assert -D[a - 2, b + 2] == D[a, b], by(pde)


@claim
def ct_reversed(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in claim.dom:
        if a < 2:
            yield by(stored)
        else:
            assert D[a, b] == -D[a - 2, b + 2] == -R[a - 2, b + 2] == R[a, b], by(
                pde, claim[a - 2, b + 2], recurrence
            )


@claim
def doubled(f: Fn[Nat, Int], h: all(f[k] == 2 * k for k in Nat)) -> f[3] + f[3] == 12:
    assert f[3] == 6, by(h)


@claim
def at_two(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> R[2, 0] == D[2, 0]:
    return by(ct_chain(D, R, 2, 0))


@claim
def square(x: Int, y: Int, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    assert y * y == (x + 1) * (x + 1) == x * x + 2 * x + 1, by(h)


@claim
def square_wrong(x: Int, y: Int, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    assert y * y == (x + 1) * (x + 1) == x * x + 2 * x + 2, by(h)


@claim
def square_positional(x: Int, y: Int, /, h: y == x + 1) -> y * y == x * x + 2 * x + 1:
    assert y * y == (x + 1) * (x + 1) == x * x + 2 * x + 1, by(h)


@claim
def mixed(x: Int, y: Int, h: y == x + 1) -> y * y >= x * x + 2 * x:
    assert y * y == (x + 1) * (x + 1) == x * x + 2 * x + 1 >= x * x + 2 * x, by(h)
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


def test_an_asserted_chain_is_one_step_whose_links_share_its_reasons(cases) -> None:
    proof = trace_proof(cases.ct_chain)
    (base, step) = proof.leaves
    assert base.steps == () and base.facts[0].name == "stored"
    (asserted,) = step.steps
    assert step.facts is None  # the point yields nothing: the assert is its proof
    (chain,) = asserted.parts
    assert isinstance(chain, TracedChain)
    assert asserted.line == _line(cases, "            assert (")
    # each link at the line of the term it reaches
    assert [link.line for link in chain.links] == [
        _line(cases, "                == -R[a - 2, b + 2]"),
        _line(cases, "                == -D[a - 2, b + 2]"),
        _line(cases, "                == D[a, b]"),
    ]
    assert [citation.text() for citation in asserted.facts] == [
        "recurrence",
        "claim[a - 2, b + 2]",
        "pde",
    ]
    assert all(link.facts == asserted.facts for link in chain.links)
    assert [citation.text() for citation in proof.calls] == ["claim[a - 2, b + 2]"]


def test_a_chain_mixes_relations_as_python_does(cases) -> None:
    proof = trace_proof(cases.mixed)
    ((chain,),) = [step.parts for step in proof.leaves[0].steps]
    assert [link.relation for link in chain.links] == ["==", "==", ">="]
    assert chain.relation == ">="


def test_a_step_left_open_is_a_hole_at_its_line(cases) -> None:
    proof = trace_proof(cases.ct_open)
    assert proof.holes == [_line(cases, "assert -R[a - 2, b + 2] == -D[a - 2, b + 2], by(...)")]


# }}}


# {{{ the Lean a chain compiles to


def test_a_chain_is_a_have_by_calc_whose_links_are_steps(cases) -> None:
    command = compile_proof(trace_proof(cases.ct_chain), mathlib=False)
    source = command.source
    assert "  · have step_1 : R a b = D a b := by\n      calc R a b\n" in source
    assert "_ = (-1) * D (a - 2) (b + 2) := by\n" in source
    # facts cited by name, matched at the point that lines each up with its link
    assert "recurrence (a - 2) (by omega) b (by omega)" in source
    assert "pde (a - 2) (by omega) b (by omega)" in source
    assert "termination_by a.toNat" in source
    # the point yields nothing: the assert states its claim
    assert "    exact step_1\n" in source
    assert command.summary == "induction on a, 2 cases, 4 steps"
    assert [step.where for step in command.steps] == [
        _line(cases, "            yield by(stored)"),
        _line(cases, "                == -R[a - 2, b + 2]"),
        _line(cases, "                == -D[a - 2, b + 2]"),
        _line(cases, "                == D[a, b]"),
    ]


def test_a_chain_the_other_way_round_gives_the_claim_turned_round(cases) -> None:
    source = compile_proof(trace_proof(cases.ct_reversed), mathlib=False).source
    assert "have step_1 : D a b = R a b := by" in source
    assert "exact step_1.symm\n" in source


def test_a_step_the_case_asserted_is_known_to_the_rest_of_it(cases) -> None:
    command = compile_proof(trace_proof(cases.doubled), mathlib=False)
    assert "  have step_1 : f 3 = 6 := by\n" in command.source
    assert command.summary == "1 step, 1 routine"
    assert [row[2] for row in command.outline] == ["f[3]"]


def test_a_hole_is_a_sorry_whose_line_is_recorded(cases) -> None:
    command = compile_proof(trace_proof(cases.ct_open), mathlib=False)
    (hole,) = command.hole_lines
    assert command.source.splitlines()[hole - 1].strip() == "sorry"
    # three steps, the point finished from them, no claim cited: no induction
    assert command.summary == "2 cases, 3 steps, 1 routine, 1 step left open"
    sorry = {"line": hole, "column": 10}
    audit = [
        {"severity": "info", "data": "'Lanky.ct_open' depends on axioms: [sorryAx]"},
    ]
    said, failures = verdict(None, command, {"messages": audit, "sorries": [sorry]})
    assert (said, failures) == (CLOSED_WITH_HOLES, [])
    stray = {"line": hole + 1, "column": 0}
    said, _ = verdict(None, command, {"messages": audit, "sorries": [stray]})
    assert said == "failed"


def test_a_citation_given_too_many_values_or_one_twice_is_refused(tmp_path) -> None:
    """``h(a, b, k=c)`` of a fact of one variable is refused, not read as ``h(c)``.

    And so is ``h(a, k=c)``, which gives ``k`` twice (Codex, #171).
    """
    path = tmp_path / "surplus_cases.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import by, claim\n"
        "from lanky.prelude import Fn, Int, Nat\n\n\n"
        "@claim\n"
        "def surplus(f: Fn[Nat, Int], h: all(f[k] == k for k in Nat)) -> f[3] == 3:\n"
        "    return by(h(1, 2, k=3))\n\n\n"
        "@claim\n"
        "def twice(f: Fn[Nat, Int], h: all(f[k] == k for k in Nat)) -> f[3] == 3:\n"
        "    return by(h(1, k=3))\n",
        encoding="utf-8",
    )
    module = import_path(path)
    with pytest.raises(ProofError, match="takes 1 value, its variable k, and is given 3"):
        trace_proof(module.surplus)
    with pytest.raises(ProofError, match="is given k twice"):
        trace_proof(module.twice)


def test_a_theorem_with_positional_only_parameters_is_traced(cases) -> None:
    """Its parameters before ``/`` are passed by position (Codex, #171)."""
    traced = trace_proof(cases.square_positional)
    plain = trace_proof(cases.square)
    assert len(traced.leaves) == len(plain.leaves) == 1
    ((one,),) = [step.parts for step in traced.leaves[0].steps]
    ((two,),) = [step.parts for step in plain.leaves[0].steps]
    assert len(one.links) == len(two.links) == 2


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
        cases.ct_chain.fact_id: CitedText("ct_chain", "PROVED TEXT", ("claim:other@1",)),
        "claim:other@1": CitedText("other", "OTHER TEXT"),
    }
    with proved_texts(texts):
        command = compile_proof(trace_proof(cases.at_two), mathlib=False)
    assert "(ct_chain : PROVED TEXT)" in command.source
    assert "(other : OTHER TEXT)" in command.source
    assert command.rests_on == [cases.ct_chain.fact_id, "claim:other@1"]
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

    other = {"claim:other@1": CitedText("other", "OTHER TEXT")}
    earlier = Proved(
        cases.ct_chain.fact_id,
        "Lanky.ct_chain",
        "PROVED TEXT",
        False,
        cases.square.term,
        ("claim:other@1",),
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
        ("claim:other@1",),
    )
    with proved_texts({cases.ct_chain.fact_id: current, **other}):
        assert cited_text(cases.ct_chain, False) == "PROVED TEXT"


# }}}


# {{{ without Lean


def test_without_lean_a_false_step_fails_at_its_line(cases, monkeypatch) -> None:
    """The native run finds it at the check's draws, with the two sides, and needs no Lean."""
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
        cases, "assert y * y == (x + 1) * (x + 1) == x * x + 2 * x + 2, by(h)"
    )
    (said,) = failure["lines"]
    assert said.startswith("At x = ") and "(it needs ==)" not in said


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
    "owner",
    ["ct_chain", "ct_reversed", "doubled", "at_two", "square", "square_positional", "mixed"],
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

from lanky import claim, by
from lanky.prelude import Fn, Int, Nat


@claim(cite="the design's T4: a printer that dropped a condition")
def every_integer_is_nonnegative(n: Int) -> n >= 0:
    """What a theorem about naturals would say if the printer dropped its condition."""


@claim
def any_two_cells(f: Fn[Nat, Int]) -> f[0] == f[1]:
    return by(every_integer_is_nonnegative(-1))
'''


#: Two proofs that cite each other.
CIRCLE = '''\
"""Two proofs, each citing the other."""

from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Int


@claim
def ping(x: Int) -> x + 1 > x:
    return by(pong(x))


@claim
def pong(x: Int) -> x + 1 > x:
    return by(ping(x))
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


#: The design's T4 inside an induction: the citation is at the claim's own ``n``.
T4_INDUCTION = '''\
"""A proof that takes its citation at a point with a variable, inside an induction."""

from __future__ import annotations

from lanky import claim, by
from lanky.prelude import Fn, Int, Nat


@claim(cite="a table that does not change from one cell to the next")
def steady(g: Fn[Nat, Int], m: Nat) -> g[m + 1] == g[m]:
    """Each cell is the one before it."""


@claim(cite="a printer that dropped a condition, inside an induction")
def grows(g: Fn[Nat, Int], m: Nat) -> g[m] < g[m] + m:
    """What a statement about the cells past the first would say with m >= 1 dropped."""


@claim
def every_cell_is_seven(f: Fn[Nat, Int]) -> all(f[n] == 7 for n in Nat):
    for n in claim.dom:
        if n >= 1:
            yield by(steady(f, n - 1), claim[n - 1])
        else:
            yield by(grows(f, n))
'''


def test_t4_inside_an_induction_is_asked_at_the_claims_own_point(tmp_path) -> None:
    """``grows`` is cited at ``(f, n)`` in the case ``n < 1``, where its statement proves False.

    The claim is false, and about a table over ``Nat``, which no draw tests;
    no point of the proof is a number, so the question at numbers alone has
    no instance to take, and the proof read proved by Lean. In the case,
    with ``f`` and ``n`` bound and ``n >= 1`` false, ``grows`` at ``(f, n)``
    says ``f[n] < f[n] + n`` where ``n`` is ``0``, and ``omega`` finds
    False: the proof is refused, at the line of the case.
    """
    _lean_or_skip()
    path = tmp_path / "t4_induction_cases.py"
    path.write_text(T4_INDUCTION, encoding="utf-8")
    fact = {fact.owner: fact for fact in claims(check_path(path))}["every_cell_is_seven"]
    account = fact.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite"
    assert failure["headline"] == (
        "the theorems its proof cites without a proved text prove False"
    )
    assert failure["lines"][0].startswith("steady and grows, as lanky states them for Lean")
    assert failure["line"] == 1 + next(
        index
        for index, text in enumerate(T4_INDUCTION.splitlines())
        if "yield by(grows(f, n))" in text
    )
    assert fact.provenance.get("tactic") != "its written proof"


#: T4 inside an induction, with the citation by name alone: the compiler finds its point.
T4_BY_NAME = T4_INDUCTION.replace("yield by(grows(f, n))", "yield by(grows)")


def test_t4_by_name_alone_is_asked_at_the_point_the_compiler_found(tmp_path) -> None:
    """``by(grows)`` is taken at ``(f, n)``, matched against ``f[n] == 7`` (Codex, #177).

    The point is written nowhere, so the case's question had no point to
    take ``grows`` at, and was not asked: the false claim read proved by
    Lean. The compiler's instance is the point now, and the case at ``n <
    1`` is refused as when the point is written.
    """
    _lean_or_skip()
    path = tmp_path / "t4_by_name_cases.py"
    path.write_text(T4_BY_NAME, encoding="utf-8")
    fact = {fact.owner: fact for fact in claims(check_path(path))}["every_cell_is_seven"]
    account = fact.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite"
    assert failure["lines"][0].startswith("steady and grows, as lanky states them for Lean")
    assert fact.provenance.get("tactic") != "its written proof"


#: T4 inside an induction, the citation at a function: ``grows`` at ``(k ↦ f[k] + 1, n)``.
T4_AT_A_FUNCTION = T4_INDUCTION.replace(
    "yield by(grows(f, n))", "yield by(grows(lambda k: f[k] + 1, n))"
)


def test_t4_at_a_function_is_asked_at_that_function(tmp_path) -> None:
    """A point that binds a family to a function is asked about too (Codex, #182).

    ``grows`` taken at ``(k ↦ f[k] + 1, n)`` in the case ``n < 1`` says
    ``f[0] + 1 < f[0] + 1``, which proves anything; the case's question left
    out points with a function in them, and the false claim read proved by
    Lean. The function is now written in the question, as a ``fun``.
    """
    _lean_or_skip()
    path = tmp_path / "t4_function_cases.py"
    path.write_text(T4_AT_A_FUNCTION, encoding="utf-8")
    fact = {fact.owner: fact for fact in claims(check_path(path))}["every_cell_is_seven"]
    account = fact.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite", failure
    assert failure["lines"][0].startswith("steady and grows, as lanky states them for Lean")
    assert fact.provenance.get("tactic") != "its written proof"


#: T4 in a case no small number reaches, and in one whose condition reads a table.
T4_UNSAMPLED = '''\
"""Proofs that take a citation in a case the search for values does not reach."""

from __future__ import annotations

from lanky import claim, by
from lanky.prelude import Fn, Int, Nat


@claim(cite="a printer that dropped a condition")
def grows(g: Fn[Nat, Int], m: Nat) -> g[m] < g[m] + m:
    """What a statement about the cells past the first would say with m >= 1 dropped."""


@claim
def cell_one_hundred(f: Fn[Nat, Int]) -> all(f[n] == 7 for n in Nat if n == 100):
    for n in claim.dom:
        yield by(grows(f, n - 100))


@claim
def threes_are_sevens(f: Fn[Nat, Int]) -> all(f[n] == 7 for n in Nat):
    for n in claim.dom:
        if f[n] == 3:
            yield by(grows(f, 0))
        else:
            yield by(grows(f, 0))


@claim
def past_a_hundred(
    f: Fn[Nat, Int], seven: all(f[m] == 7 for m in Nat if m >= 100)
) -> all(f[n] == 7 for n in Nat if n >= 100):
    for n in claim.dom:
        if n < 50:
            yield by(grows(f, n))
        else:
            yield by(seven(n))
'''


@pytest.fixture(scope="module")
def unsampled(tmp_path_factory) -> dict:
    """:data:`T4_UNSAMPLED` checked with core Lean, by owner."""
    _lean_or_skip()
    path = tmp_path_factory.mktemp("t4_unsampled") / "t4_unsampled_cases.py"
    path.write_text(T4_UNSAMPLED, encoding="utf-8")
    return {fact.owner: fact for fact in claims(check_path(path))}


@pytest.mark.parametrize("owner", ["cell_one_hundred", "threes_are_sevens"])
def test_t4_in_a_case_no_small_number_reaches_is_asked(unsampled, owner) -> None:
    """A search that finds no values shows nothing about the case (Codex, #177 and #182).

    ``n == 100`` is met by no small number, and ``f[n] == 3`` cannot be
    evaluated at numbers, so neither case had its question asked, and both
    false claims read proved by Lean from ``grows`` at a point where its
    statement is ``f[0] < f[0]``. The case is asked now unless its
    conditions alone prove False, which these do not.
    """
    fact = unsampled[owner]
    account = fact.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite"
    assert failure["headline"] == (
        "the theorem its proof cites without a proved text proves False"
    )
    assert fact.provenance.get("tactic") != "its written proof"


def test_a_case_its_conditions_rule_out_is_not_asked(unsampled) -> None:
    """``n < 50`` under the guard ``n >= 100`` is a case nothing reaches; its citation is idle.

    Asked, the question would prove False from the case's conditions alone
    and refuse a sound proof; the conditions are shown inconsistent first,
    and the case is passed over.
    """
    account = unsampled["past_a_hundred"].provenance["proof"]
    assert account["closed"] is True, account


def test_a_restated_text_other_than_the_kept_one_is_refused_before_lean(cases) -> None:
    """The design's 3.5: a citation is compared with the text the cited command closed with.

    The oracle keeps one text for ``ct_chain``, and the proof of ``at_two``
    is compiled against another: the check refuses it before Lean is asked,
    and before the proof cache is read, warm or not.
    """
    _lean_or_skip()
    from lanky.citations import Proved
    from lanky.proofs import _lean_oracle

    oracle = _lean_oracle()
    texts = oracle.proved_texts
    kept = Proved(cases.ct_chain.fact_id, "Lanky.ct_chain", "KEPT", False, cases.ct_chain.term)
    texts.record(kept)
    try:
        with proved_texts({cases.ct_chain.fact_id: "RESTATED"}):
            checked = prove(cases.at_two, cases.at_two.fact())
    finally:
        texts.forget(cases.ct_chain.fact_id)
    account = checked.provenance["proof"]
    assert account["closed"] is False, account
    (failure,) = account["failures"]
    assert failure["kind"] == "cite"
    assert failure["headline"] == (
        "a theorem its proof cites is restated other than as Lean proved it"
    )
    assert "(ct_chain : RESTATED)" in account["lean_source"]


def test_lean_accepts_a_proof_with_a_step_left_open_and_names_it(checked) -> None:
    fact = checked["ct_open"]
    account = fact.provenance["proof"]
    assert account["closed"] == "holes", account
    line = 1 + next(
        index
        for index, text in enumerate(CASES.splitlines())
        if "assert -R[a - 2, b + 2] == -D[a - 2, b + 2], by(...)" in text
    )
    assert account["holes"] == [f"chains_cases.py:{line}"]
    # the proof does not prove the claim: it reads as the other oracles left it
    assert fact.provenance.get("tactic") != "its written proof"


# }}}


def test_proofs_names_a_written_proof_where_the_search_found_none() -> None:
    from lanky.ledger import Fact
    from lanky.outline import proof_lines

    fact = Fact(
        id="claim:m.t@3",
        kind="claim",
        statement="t",
        status=Status.PROVED,
        decided_by="lean",
        provenance={"proof": {"closed": True, "where": "m.py:5-9"}},
        where="m.py:3",
        owner="t",
    )
    assert proof_lines(fact) == ["PROOF t at m.py:3, by its proof as written, m.py:5-9"]
