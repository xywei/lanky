"""Probes that try to make lanky claim something it has not established.

Ways a checker like this goes quietly wrong, one test each: a statement nobody
could actually test reported as tested, a name that means two things at once
read as one of them, a refutation that does not survive being written down, a
false statement no oracle would take, and a draw that raises where it should
decline. Each of these is about the *report* rather than about the mathematics:
the failure mode that matters here is a ledger that reads better than the
evidence.
"""

from __future__ import annotations

import json

import pytest

from lanky import cli, theorem
from lanky.check import check_path
from lanky.ledger import Fact, Ledger, Status
from lanky.oracles.test import TestOracle
from lanky.prelude import Bool, Fin, Fn, Nat
from lanky.terms import Exists, Forall, Undecided, Var, render, structurally_equal

# {{{ a hypothesis no draw can satisfy


@theorem
def unsatisfiable(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1:
    """Nothing satisfies the hypotheses, so nothing is tested by sampling."""


def test_a_vacuous_pass_is_never_reported_as_tested() -> None:
    """Sampling finds no valid case, so the tester must not claim a pass.

    ``report.ok`` is ``True`` here, and that is the trap: no draw refuted the
    goal because no draw ever reached it. What makes the difference is
    ``valid``, and the oracle has to read it.
    """
    report = unsatisfiable.report(n=50)
    assert report.ok
    assert report.valid == 0
    assert "hypotheses" in report.reason

    result = TestOracle(samples=50).establish(unsatisfiable.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert result.provenance["valid"] == 0
    assert "hypotheses" in result.provenance["untested"]


VACUOUS = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Fin, Nat\n\n\n"
    "@theorem\n"
    "def vacuous(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1:\n"
    '    """No natural satisfies the hypotheses, so the goal is never at stake."""\n'
)

SATISFIABLE = VACUOUS.replace("(n > 2) & (n < 1)) -> n == n + 1", "n > 2) -> n > 1")


class ProvesEverything:
    """A kernel-class stand-in for Lean that proves every fact it is offered.

    It is what Lean does with ``vacuous``: from ``n > 2`` and ``n < 1`` any
    goal follows, and ``omega`` finds that at once. A stand-in lets the whole
    path be checked on a machine without Lean.
    """

    name = "stub-kernel"

    def __init__(self, trust: str = "kernel") -> None:
        self.trust = trust

    def trust_class(self) -> str:
        return self.trust

    def can_establish(self, fact: Fact, /) -> bool:
        return fact.term is not None

    def establish(self, fact: Fact, /) -> Fact:
        return fact.with_status(Status.PROVED, self.name, tactic="stub")


class ProvesAllButInconsistency(ProvesEverything):
    """The same stand-in, declining the question whether hypotheses are inconsistent.

    That is Lean faced with hypotheses that hold somewhere the sampler does not
    look: the claim is proved, and ``False`` does not follow.
    """

    def can_establish(self, fact: Fact, /) -> bool:
        return fact.kind != "hypotheses" and super().can_establish(fact)


class ProvesOnlyInconsistency(ProvesEverything):
    """A stand-in that takes nothing but the question of inconsistency.

    That is Lean faced with a goal it cannot state, a reduction say, under
    hypotheses it can refute.
    """

    def can_establish(self, fact: Fact, /) -> bool:
        return fact.kind == "hypotheses"


@pytest.fixture
def oracles(monkeypatch):
    """Replace the registered oracles by the ones a test names, for that test.

    Entry points are loaded first, so that ``check_path`` finds nothing left
    to add to the list the test installed.
    """
    import lanky.oracles  # noqa: F401 - registers the built-in oracles
    from lanky.plugins import registry

    registry.load_entry_points()

    def install(*chosen) -> None:
        monkeypatch.setattr(registry, "oracles", list(chosen))

    return install


def _write(tmp_path, text: str, name: str = "vacuous.py") -> str:
    path = tmp_path / name
    path.write_text(text, encoding="utf-8")
    return str(path)


def test_a_vacuous_pass_is_assumed_in_the_ledger(tmp_path, oracles, capsys) -> None:
    """With the tester as the only oracle the row reads ``assumed``, and says why.

    This used to hold only because the test switched Lean off; with Lean the
    same file was ``proved`` and nothing said it was vacuous. The oracles are
    chosen here instead, so the test means the same thing on every machine.
    Nothing can show the hypotheses inconsistent, so the check warns and exits
    0: the row is ``assumed``, which never passes for evidence.
    """
    oracles(TestOracle())
    path = _write(tmp_path, VACUOUS)
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.provenance["valid"] == 0
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    assert not fact.is_vacuous
    assert "assumed" in ledger.render()
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "WARNING vacuous at vacuous.py:7: hypotheses never satisfied in 4000 draws" in printed
    assert "VACUOUS" not in printed
    assert fact.provenance["unsatisfied_detail"] is None


@pytest.mark.parametrize("trust", ["kernel", "decision-procedure"])
def test_a_proof_from_inconsistent_hypotheses_is_marked_vacuous(
    tmp_path, oracles, capsys, trust
) -> None:
    """#5: a claim nothing is at stake in says so, and fails the check.

    The stand-in proves the claim, as Lean does, and the tester's cross-check
    finds that no draw satisfied the hypotheses. The stand-in is then asked
    whether the hypotheses alone prove ``False``; it says yes, so the fact is
    marked ``vacuous`` in its provenance, the table reads ``proved (vacuous)``,
    ``--json`` carries the mark, and ``lanky check`` exits 1. The status stays
    ``proved``, because that is true. A decision procedure is stronger than a
    test as well, and gets the same treatment.
    """
    oracles(ProvesEverything(trust), TestOracle())
    path = _write(tmp_path, VACUOUS)
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert fact.status is Status.PROVED
    assert fact.decided_by == "stub-kernel"
    assert fact.is_vacuous
    assert fact.provenance["vacuous"] == "the hypotheses are inconsistent: proved by stub-kernel"
    assert fact.provenance["vacuous_by"] == "stub-kernel"
    assert fact.provenance["vacuous_evidence"] == {"tactic": "stub"}
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    rendered = ledger.render()
    assert "proved (vacuous)  stub-kernel" in rendered
    assert "1 facts: 1 proved; 1 vacuous" in rendered

    out_json = tmp_path / "ledger.json"
    assert cli.main(["check", path, "--json", str(out_json)]) == 1
    printed = capsys.readouterr().out
    assert "VACUOUS vacuous at vacuous.py:7: n : Nat | n > 2 and n < 1 |- n == n + 1" in printed
    assert "the hypotheses are inconsistent: proved by stub-kernel" in printed
    assert "WARNING" not in printed
    (entry,) = json.loads(out_json.read_text(encoding="utf-8"))
    assert entry["status"] == "proved"
    assert entry["provenance"]["vacuous"]


def test_a_satisfiable_hypothesis_under_a_proved_goal_carries_no_flag(
    tmp_path, oracles, capsys
) -> None:
    """``h: n > 2`` with the goal ``n > 1``: a draw satisfies it, nothing changes."""
    oracles(ProvesEverything(), TestOracle())
    path = _write(tmp_path, SATISFIABLE)
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert "unsatisfied" not in fact.provenance
    assert "semantics_disagreement" not in fact.provenance
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "WARNING" not in printed
    assert "VACUOUS" not in printed
    assert "(vacuous)" not in printed


def test_hypotheses_no_oracle_can_refute_leave_a_warning(tmp_path, oracles, capsys) -> None:
    """No draw satisfied them and nothing proves them inconsistent: warn, exit 0.

    That is the record ``n == 1000`` leaves with naturals drawn up to five, and
    the tester cannot tell it from hypotheses that hold nowhere, so the check
    says what it saw and does not fail.
    """
    oracles(ProvesAllButInconsistency(), TestOracle())
    path = _write(tmp_path, VACUOUS)
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "WARNING vacuous at vacuous.py:7: hypotheses never satisfied in 4000 draws" in printed
    assert "no oracle could show them inconsistent" in printed
    assert "(vacuous)" not in printed


VACUOUS_AXIOM = (
    "from __future__ import annotations\n\n"
    "from lanky import axiom\n"
    "from lanky.prelude import Fin, Nat\n\n\n"
    '@axiom(cite="a textbook, with a hypothesis copied down wrong")\n'
    "def miscopied(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1:\n"
    '    """No natural satisfies the hypotheses, so the axiom says nothing."""\n'
)


def test_an_axiom_with_inconsistent_hypotheses_is_vacuous(tmp_path, oracles, capsys) -> None:
    """An axiom's hypotheses are examined as a theorem's are, and it stays ``assumed``.

    Hypotheses copied down wrong are as likely as a goal copied down wrong,
    and they used to go unremarked: the tester's pass over an axiom was thrown
    away, what it said about the hypotheses with it. The stand-in proves
    whatever it is shown, and is shown the question whether the hypotheses are
    inconsistent, never the axiom.
    """
    shown: list[str] = []

    class Recording(ProvesEverything):
        def establish(self, fact: Fact, /) -> Fact:
            shown.append(fact.kind)
            return super().establish(fact)

    oracles(Recording(), TestOracle())
    path = _write(tmp_path, VACUOUS_AXIOM)
    (fact,) = list(check_path(path))
    assert shown == ["hypotheses"]
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.is_vacuous
    assert fact.provenance["vacuous_by"] == "stub-kernel"
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    assert fact.provenance["cite"] == "a textbook, with a hypothesis copied down wrong"
    assert cli.main(["check", path]) == 1
    printed = capsys.readouterr().out
    assert "assumed (axiom) (vacuous)  -" in printed
    assert "VACUOUS miscopied at vacuous.py:7:" in printed


def test_an_axiom_whose_hypotheses_no_draw_satisfied_is_warned_about(
    tmp_path, oracles, capsys
) -> None:
    """With nothing to show them inconsistent, the axiom gets the theorem's warning."""
    oracles(TestOracle())
    path = _write(tmp_path, VACUOUS_AXIOM)
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert not fact.is_vacuous
    assert "valid" not in fact.provenance
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "WARNING miscopied at vacuous.py:7: hypotheses never satisfied in 4000 draws" in printed
    # a satisfiable axiom leaves nothing of its sampling behind
    satisfiable = VACUOUS_AXIOM.replace("(n > 2) & (n < 1)) -> n == n + 1", "n > 2) -> n > 1")
    path = _write(tmp_path, satisfiable)
    (fact,) = list(check_path(path))
    assert set(fact.provenance) == {"path", "line", "cite"}


def test_a_goal_no_oracle_can_state_does_not_hide_vacuous_hypotheses(
    tmp_path, oracles, capsys
) -> None:
    """The hypotheses are examined whoever established the fact, or nobody.

    A reduction is outside core Lean, so the claim stays ``assumed``, but
    hypotheses Lean can refute are refuted all the same, and a claim that
    nothing is ever at stake in fails the check.
    """
    oracles(ProvesOnlyInconsistency(), TestOracle())
    path = _write(
        tmp_path,
        VACUOUS.replace("-> n == n + 1", "-> 2 * sum(i for i in Fin[n + 1]) == 7"),
    )
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.is_vacuous
    assert cli.main(["check", path]) == 1
    assert "assumed (vacuous)" in capsys.readouterr().out


def test_an_empty_domain_is_an_inconsistent_hypothesis(tmp_path, oracles) -> None:
    """``i : Fin[0]`` assumes ``0 ≤ i < 0``, which is exactly as vacuous."""
    oracles(ProvesEverything(), TestOracle())
    path = _write(
        tmp_path,
        VACUOUS.replace("n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1", "i: Fin[0]) -> i == 1"),
    )
    (fact,) = list(check_path(path))
    assert fact.is_vacuous
    assert fact.provenance["unsatisfied_detail"] == "a draw could not be completed: Fin(0) is empty"


def test_a_family_with_nowhere_to_put_its_values_is_an_inconsistent_hypothesis(
    tmp_path, oracles, capsys
) -> None:
    """``f : Fn[Fin[1], Nat & False]`` has no member, so no draw has an ``f``.

    Only a guard, a ``Fin`` or a refinement used to count as a hypothesis, so
    a statement over such a family was never examined: the row read
    ``assumed`` and nothing was printed. A family whose values are restricted
    counts now. Lean erases the restriction, so only the warning can say it.
    """
    from lanky.check import has_hypotheses

    oracles(TestOracle())
    path = _write(
        tmp_path,
        VACUOUS.replace(
            "n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1",
            "f: Fn[Fin[1], Nat & False]) -> f(0) == 1",
        ).replace("import Fin, Nat", "import Fin, Fn, Nat"),
    )
    (fact,) = list(check_path(path))
    assert fact.provenance["unsatisfied"] == "hypotheses never satisfied in 4000 draws"
    assert cli.main(["check", path]) == 0
    assert "WARNING vacuous at vacuous.py:7" in capsys.readouterr().out
    f = Var("f")
    assert has_hypotheses(Forall(((f, Fn[Fin[2], Fin[3]]),), f(0) >= 0))
    assert has_hypotheses(Forall(((f, Fn[Fin[2], Fn[Fin[2], Nat & False]]),), f(0)(0) >= 0))
    assert not has_hypotheses(Forall(((f, Fn[Fin[2], Nat]),), f(0) >= 0))


def test_a_refinement_that_never_evaluates_is_undecided_not_unsatisfied(
    tmp_path, oracles, capsys
) -> None:
    """``Nat & (10 // (n - n) > 1)`` raises at every draw, as the same guard would.

    A guard that divides by zero makes its draw undecided, which is no evidence
    against the hypotheses. A refinement that did the same was counted as a
    draw the hypotheses rejected, so the stronger oracles were asked about
    ``Int.fdiv 10 0 > 1``, which Lean's total division makes false, and the
    claim was marked vacuous on a reading Python never ran. The refinement's
    draw is undecided now too.
    """
    oracles(ProvesEverything(), TestOracle())
    path = _write(
        tmp_path,
        VACUOUS.replace("n: Nat, h: (n > 2) & (n < 1))", "n: Nat & (10 // (n - n) > 1))"),
    )
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert not fact.is_vacuous
    assert "unsatisfied" not in fact.provenance
    assert "cannot be evaluated" in fact.provenance["semantics_undecided"]
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "VACUOUS" not in printed
    assert "WARNING" not in printed


UNTABULATED = VACUOUS.replace(
    "n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1",
    "f: Fn[Nat, Nat], n: Nat, h: f(n) >= 1) -> f(n) + 1 >= 2",
).replace("import Fin, Nat", "import Fin, Fn, Nat")


@pytest.mark.parametrize("stronger", [True, False])
def test_a_sort_the_tester_cannot_draw_is_not_unsatisfied_hypotheses(
    tmp_path, oracles, capsys, stronger
) -> None:
    """A family over ``Nat`` stops every draw before the hypotheses are reached.

    The record then has no valid draw, as a vacuous claim's has, and it used to
    be reported as one: "hypotheses never satisfied in 4000 draws", with a
    warning, for a hypothesis that was never evaluated and that holds wherever
    ``f(n)`` is positive. Now the tester says that no draw could be completed,
    the fact carries no ``unsatisfied``, and nothing is printed under the
    table, with a stronger oracle that proves the claim or with the tester
    alone.
    """
    if stronger:
        oracles(ProvesAllButInconsistency(), TestOracle())
    else:
        oracles(TestOracle())
    path = _write(tmp_path, UNTABULATED)
    (fact,) = list(check_path(path))
    assert fact.status is (Status.PROVED if stronger else Status.ASSUMED)
    assert "unsatisfied" not in fact.provenance
    assert not fact.is_vacuous
    if stronger:
        assert fact.provenance["untestable"] == (
            "no draw could be completed: cannot tabulate a family over Nat"
        )
    else:
        assert fact.provenance["untested"] == (
            "no draw could be completed: cannot tabulate a family over Nat"
        )
        assert fact.provenance["unsampleable"] == 4000
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "WARNING" not in printed
    assert "VACUOUS" not in printed


def test_inconsistent_hypotheses_over_a_sort_the_tester_cannot_draw_are_vacuous(
    tmp_path, oracles, capsys
) -> None:
    """The tester draws nothing, and the stronger oracle is still asked.

    No draw is not evidence that the hypotheses fail, but a proof that they do
    is, whatever the tester managed: ``n > 2`` and ``n < 1`` are inconsistent
    next to a family over ``Nat`` as anywhere else.
    """
    oracles(ProvesEverything(), TestOracle())
    path = _write(
        tmp_path,
        VACUOUS.replace("n: Nat, h:", "f: Fn[Nat, Nat], n: Nat, h:").replace(
            "import Fin, Nat", "import Fin, Fn, Nat"
        ),
    )
    (fact,) = list(check_path(path))
    assert fact.is_vacuous
    assert "unsatisfied" not in fact.provenance
    assert cli.main(["check", path]) == 1
    printed = capsys.readouterr().out
    assert "VACUOUS vacuous at vacuous.py:7" in printed
    assert "  no draw could be completed: cannot tabulate a family over Nat" in printed
    assert "WARNING" not in printed


def test_a_refutation_under_a_stronger_proof_is_recorded(tmp_path, oracles, capsys) -> None:
    """The cross-check keeps a counterexample it finds, with or without a note.

    With one reading of arithmetic a counterexample to a proved claim means
    one of the oracles is wrong, which a ledger must not swallow; the proof's
    status stands and the disagreement is printed under ``SEMANTICS``.
    """
    oracles(ProvesEverything(), TestOracle())
    path = _write(tmp_path, VACUOUS.replace("(n > 2) & (n < 1)) -> n == n + 1", "n > 2) -> n > 5"))
    (fact,) = list(check_path(path))
    assert fact.status is Status.PROVED
    assert "semantics" not in fact.provenance
    assert fact.provenance["semantics_counterexample"]["n"] in (3, 4, 5)
    assert cli.main(["check", path]) == 0
    assert "SEMANTICS vacuous at vacuous.py:7" in capsys.readouterr().out


def test_hypotheses_fact_asks_for_false_under_the_same_hypotheses() -> None:
    """The question put to the stronger oracles, as the fact they are offered."""
    from lanky.check import has_hypotheses, hypotheses_fact

    fact = unsatisfiable.fact()
    question = hypotheses_fact(fact)
    assert question.kind == "hypotheses"
    assert question.id == f"{fact.id}:hypotheses"
    assert question.term.body is False
    assert structurally_equal(question.term.guard, fact.term.guard)
    assert structurally_equal(question.term.binders, fact.term.binders)
    assert has_hypotheses(fact.term)
    assert not has_hypotheses(Forall(((Var("n"), Nat),), Var("n") >= 0))
    assert has_hypotheses(Forall(((Var("i"), Fin[3]),), Var("i") >= 0))
    assert not has_hypotheses(Var("n") >= 0)
    with pytest.raises(ValueError, match="no hypotheses"):
        hypotheses_fact(Fact(id="t", kind="theorem", statement="t", term=Var("n") >= 0))


# }}}


# {{{ a name that is both a parameter and a size


@theorem
def bounded_family(
    n: Nat,
    f: Fn[Fin[n], Nat],
    h: all(f(i) <= n for i in Fin[n]),
) -> all(f(i) <= n + 1 for i in Fin[n]):
    """``n`` is a variable of the statement and the size of ``f``'s domain."""


@theorem
def size_named_before_it_is_bound(
    f: Fn[Fin[n], Nat],
    n: Nat,
) -> all(f(i) >= 0 for i in Fin[n]):
    """The same two roles, with the size written after what it sizes."""


def test_a_name_that_is_a_parameter_and_a_size_is_one_variable() -> None:
    """``n`` is drawn once and the family is tabulated over that same ``n``.

    Two readings of one name would show up as two: a variable ``n`` and a free
    size ``n`` that nothing draws. The evidence that there is only one is that
    the domain of ``f`` is the variable ``n`` itself, and that sampling
    produces tables whose length is the drawn ``n``.
    """
    names = [name for name, _ in bounded_family.variables]
    assert names == ["n", "f"]
    domain = dict(bounded_family.variables)["f"].domain
    assert structurally_equal(domain.bound, Var("n"))

    report = bounded_family.report(n=40)
    assert report.ok
    assert report.valid == 40

    verdict = bounded_family(n=3, f=[0, 1, 2])
    assert verdict.hypotheses["h"] and verdict.goal


def test_a_size_written_after_what_it_sizes_is_still_drawn_first() -> None:
    """Signature order is not draw order when a sort names another variable.

    Drawing ``f`` first would ask for a value of ``n`` that does not exist yet.
    The tester orders the draws by what they depend on, so this statement is
    testable rather than reported as an oracle that could not run.
    """
    from lanky.testing import sampling_order

    ordered = [name for name, _ in sampling_order(size_named_before_it_is_bound.variables)]
    assert ordered == ["n", "f"]

    report = size_named_before_it_is_bound.report(n=25)
    assert report.ok
    assert report.valid == 25


# }}}


# {{{ a refuted fact, rendered and round-tripped


def test_a_refuted_fact_renders_and_round_trips() -> None:
    """A refutation has to survive the table and the JSON with its witness.

    The witness is the whole value of ``REFUTED``, and it is the part most
    likely to be lost: it is an arbitrary object in an untyped provenance, so
    the JSON writer has to cope with something that is not JSON to begin with.
    """
    fact = Fact(
        id="theorem:false_claim",
        kind="theorem",
        statement="n : Nat |- n == n + 1",
        term=Var("n") == Var("n") + 1,
        status=Status.ASSUMED,
        where="claims.py:7",
        owner="false_claim",
        provenance={"path": "/tmp/claims.py", "line": 7},
    )
    refuted = fact.with_status(
        Status.REFUTED,
        "property-test",
        counterexample={"n": 0, "table": (1, 2, 3)},
        witness=Var("n"),
        samples=1,
        valid=1,
    )

    ledger = Ledger([refuted])
    assert ledger.counts() == {"refuted": 1}
    assert ledger.by_status(Status.REFUTED) == (refuted,)

    table = ledger.render()
    assert "refuted" in table
    assert "property-test" in table
    assert "claims.py:7" in table
    assert "false_claim" in table
    assert "1 facts: 1 refuted" in table

    entries = json.loads(ledger.to_json())
    assert len(entries) == 1
    (entry,) = entries
    assert entry["status"] == "refuted"
    assert entry["decided_by"] == "property-test"
    assert entry["term"] == "n == n + 1"
    assert entry["provenance"]["counterexample"]["n"] == 0
    # a term in the provenance is not JSON, and is written as its text rather
    # than lost or raised over
    assert entry["provenance"]["witness"] == "n"
    # the fact this refutation replaced keeps its place and its own provenance
    assert entry["provenance"]["line"] == 7
    assert entry["where"] == "claims.py:7"


def test_two_files_with_one_basename_are_told_apart_in_the_table() -> None:
    """``where`` is ``basename:line``; two files can share one basename."""
    facts = [
        Fact(
            id=f"theorem:{owner}",
            kind="theorem",
            statement="n : Nat |- True",
            status=Status.REFUTED,
            where="claims.py:7",
            owner=owner,
            provenance={"path": path},
        )
        for owner, path in (
            ("first", "/work/one/claims.py"),
            ("second", "/work/two/claims.py"),
        )
    ]
    table = Ledger(facts).render()
    assert "one/claims.py:7" in table
    assert "two/claims.py:7" in table


# }}}


# {{{ a sampled existential that finds no witness


def _unwitnessed_existential():
    """``any(x == 100 for x in Nat)``: true, and outside what sampling draws.

    It is built inside a function so lanky's pytest plugin does not collect a
    statement this suite means to leave undecided, and the witness is 100
    because the sampler draws naturals in ``0 .. MAX_NAT``: no draw can find it,
    which is exactly the situation being tested.
    """

    @theorem
    def somewhere() -> any(x == 100 for x in Nat):
        """True: 100 is a natural. Unreachable: sampling never draws it."""

    return somewhere


def test_a_sampled_existential_is_undecided_rather_than_refuted() -> None:
    """Four draws with no witness say nothing, and must not say ``REFUTED``.

    ``Nat`` is sampled rather than enumerated, so "no witness among the points
    I looked at" is not "no witness". Answering ``False`` there turns a true
    theorem into a counterexample, which is the worst thing a ledger can do.
    """
    claim = _unwitnessed_existential()
    report = claim.report(n=5)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0
    assert "witness" in report.reason

    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert "witness" in result.provenance["untested"]


def test_an_existential_over_an_enumerated_domain_is_still_decided() -> None:
    """The other side of it: ``Fin`` is the whole domain, so both answers hold.

    Declining a sampled existential must not cost the refutations that are
    real, and over a bounded index type every point is visited.
    """
    from lanky.terms import evaluate, exists

    assert evaluate(exists(i == 1 for i in Fin[3]), {}) is True
    assert evaluate(exists(i == 7 for i in Fin[3]), {}) is False


def test_a_sampled_existential_under_a_quantifier_is_undecided_too() -> None:
    """The same care applies wherever the existential sits in the statement."""

    @theorem
    def bigger_exists(n: Nat) -> any(x == n + 100 for x in Nat):
        """True for every n, and no draw of x will ever witness it."""

    result = TestOracle(samples=5).establish(bigger_exists.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.provenance["valid"] == 0
    assert result.provenance["undecided"] > 0


def test_a_witnessed_existential_still_tests() -> None:
    """Declining is for the unwitnessed case only; a witness is still evidence."""

    @theorem
    def small_witness(n: Nat) -> any(x == 0 for x in Nat):
        """0 is drawn often, so this is genuinely tested."""

    result = TestOracle(samples=5).establish(small_witness.fact())
    assert result is not None
    assert result.status is Status.TESTED
    assert result.decided_by == "property-test"


# }}}


# {{{ hypotheses of a theorem with no sort variables


def _false_hypothesis_and_goal():
    """A theorem whose only parameter is a hypothesis, and a false one.

    ``all(x < 0 for x in Nat)`` is false, and it is both the hypothesis and the
    goal, so the statement is the valid implication ``p -> p``. It is built
    inside a function because the pytest plugin collects module-level theorems.
    """

    @theorem
    def self_implication(
        h: all(x < 0 for x in Nat),
    ) -> all(x < 0 for x in Nat):
        """An implication whose antecedent is false is not a refuted claim."""

    return self_implication


def test_hypotheses_survive_a_theorem_with_no_sort_variables() -> None:
    """The guard has to reach the oracles even when there is nothing to bind.

    Dropping the binderless guard would hand the oracles the bare goal, and the
    bare goal here is false, so a valid implication would be reported
    ``REFUTED`` with its own hypothesis as the counterexample.
    """
    claim = _false_hypothesis_and_goal()
    assert claim.variables == ()
    assert len(claim.hypotheses) == 1

    term = claim.term
    assert isinstance(term, Forall)
    assert term.binders == ()
    assert term.guard is not None

    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert result.provenance["valid"] == 0


def test_a_theorem_with_no_variables_and_no_hypotheses_is_unchanged() -> None:
    """A goal with nothing in front of it is still just the goal.

    The binderless wrapper is for the guard. With no guard to carry there is
    nothing to wrap, and the term stays the goal itself.
    """

    @theorem
    def plain() -> all(x >= 0 for x in Nat):
        """No variables, no hypotheses, no wrapper."""

    assert plain.term is plain.goal


# }}}


# {{{ two theorems that share a name


def test_two_same_named_theorems_are_two_facts(tmp_path, monkeypatch) -> None:
    """A ledger keyed by qualified name alone would keep one and drop the other.

    Two modules each with a ``claim`` is the ordinary case: a project that
    checks a directory would silently lose half of it.
    """
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    source = (
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def claim(n: Nat) -> n + 1 > n:\n"
        '    """Same name, different module."""\n'
    )
    facts = []
    for name in ("first", "second"):
        path = tmp_path / f"{name}.py"
        path.write_text(source, encoding="utf-8")
        facts += [fact for fact in check_path(path)]

    assert [fact.owner for fact in facts] == ["claim", "claim"]
    assert len({fact.id for fact in facts}) == 2
    ledger = Ledger(facts)
    assert len(ledger) == 2
    assert ledger.counts() == {"tested": 2}


def test_one_module_with_two_definitions_of_a_name_keeps_both() -> None:
    """The line settles what the module name cannot: one module, two defs.

    Two ``def claim`` statements in one module have the same qualified name
    here, because the enclosing function is the same. The line they were
    written on is what tells them apart.
    """

    @theorem
    def claim(n: Nat) -> n + 1 >= n:
        """The first of two definitions sharing a name."""

    first = claim

    @theorem
    def claim(n: Nat) -> n + 2 >= n:  # noqa: F811 - two definitions, on purpose
        """The second."""

    assert first.qualname == claim.qualname
    assert first.fact().id != claim.fact().id
    assert len(Ledger([first.fact(), claim.fact()])) == 2


# }}}


# {{{ a definitional hypothesis that leaves the codomain


def _definition_outside_the_codomain():
    """``f(0) == -1`` for an ``f : Fn[Fin[1], Nat]``, with the goal ``f(0) >= 0``.

    The hypothesis and the declared codomain cannot both hold, so the theorem
    is vacuously true and there is nothing to test. Writing ``-1`` into the
    table anyway would refute the goal with a point the statement excludes.
    """

    @theorem
    def negative_entry(
        f: Fn[Fin[1], Nat],
        h: f(0) == -1,
    ) -> f(0) >= 0:
        """No natural is -1, so no draw satisfies the hypothesis."""

    return negative_entry


def test_a_synthesized_value_outside_the_codomain_is_not_a_counterexample() -> None:
    """The assignment pass must stay inside the sort it is filling in.

    This is the one place where the tester puts a value into a draw that the
    sampler did not choose, so it is the one place where a draw can leave its
    sort without anything noticing.
    """
    claim = _definition_outside_the_codomain()
    report = claim.report(n=20)
    assert report.ok
    assert report.valid == 0
    assert any("outside" in reason for reason in report.skipped)

    result = TestOracle(samples=20).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert result.provenance["valid"] == 0


def test_a_definition_inside_the_codomain_still_fills_the_table() -> None:
    """The check must not cost the prefix sums the assignment pass exists for."""

    @theorem
    def scan(
        n: Nat,
        cnt: Fn[Fin[n], Nat],
        off: Fn[Fin[n + 1], Nat],
        h0: off(0) == 0,
        hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),
    ) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
        """The worked example: every draw is satisfied by construction."""

    report = scan.report(n=25)
    assert report.ok
    assert report.valid == 25


# }}}


# {{{ a statement Python has already answered


def test_a_closed_boolean_goal_is_a_fact_like_any_other() -> None:
    """``-> 1 == 2`` is the shortest false theorem there is, and it was ignored.

    Python answers the annotation before lanky sees it, so the term is the
    ``bool`` ``False`` rather than a pymbolic node. The property oracle used to
    decline anything that was not a node, the Lean oracle has no proof of a
    false statement, and the false claim sat in the ledger as ``ASSUMED`` with
    the check exiting 0.
    """
    claim = _closed_false()
    assert claim.term is False
    fact = claim.fact()
    oracle = TestOracle(samples=5)
    assert oracle.can_establish(fact)
    result = oracle.establish(fact)
    assert result is not None
    assert result.status is Status.REFUTED
    assert result.decided_by == "property-test"
    # the counterexample is empty on purpose: no assignment is what makes this
    # statement false, and the reason says so rather than leaving a bare {}
    assert result.provenance["counterexample"] == {}
    assert "constant False" in result.provenance["reason"]


def test_a_closed_true_goal_is_tested_rather_than_assumed() -> None:
    result = TestOracle(samples=5).establish(closed_true.fact())
    assert result is not None
    assert result.status is Status.TESTED
    assert result.decided_by == "property-test"
    assert result.provenance["valid"] == 1


def test_every_way_of_running_a_closed_statement_agrees() -> None:
    """The call, the report, the test and the pytest item say the same thing."""
    claim = _closed_false()
    assert claim().goal is False
    assert claim().holds is False
    ok, counterexample = claim.test(n=5)
    assert not ok
    assert counterexample == {}
    report = claim.report(n=5)
    assert report.valid == 1
    assert report.samples == 1

    assert closed_true().holds is True
    assert closed_true.test(n=5) == (True, None)
    assert closed_true.report(n=5).valid == 1


def test_a_satisfied_hypothesis_does_not_shield_a_false_closed_goal() -> None:
    """The binderless guard from the round of fixes before, with a bool body."""
    claim = _guarded_closed_goal()
    term = claim.term
    assert isinstance(term, Forall)
    assert term.binders == ()
    assert term.body is False
    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.REFUTED
    assert result.provenance["counterexample"] == {}


def test_a_constant_false_hypothesis_is_vacuous_rather_than_refuted() -> None:
    """A parameter annotated with a concrete bool is a hypothesis, not a sort.

    ``h: 1 == 2`` used to be read as a variable whose sort is ``False``, which
    nothing can sample; as the hypothesis it is, the statement is the valid
    implication nobody can test, which is ``ASSUMED``.
    """
    claim = _constant_false_hypothesis()
    assert claim.variables == ()
    assert len(claim.hypotheses) == 1
    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.provenance["valid"] == 0


# }}}


# {{{ a draw the statement cannot be answered at


def test_a_division_by_zero_is_an_undecided_draw_rather_than_a_crash() -> None:
    """Lean's ``Nat`` division is total and Python's raises; that is a gap.

    Neither reading is a counterexample to the other, so the draw is dropped
    the way an unwitnessed existential is, and the tester reports rather than
    propagating a ``ZeroDivisionError`` to whoever called it.
    """
    claim = _divides_by_a_variable()
    report = claim.report(n=5)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0
    assert "zero" in report.reason

    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert "zero" in result.provenance["untested"]


def test_a_family_applied_outside_its_domain_is_an_undecided_draw() -> None:
    """``f(n)`` for an ``f : Fn[Fin[n], Nat]`` raised an ``IndexError``.

    The statement names a point its own types say the family does not have.
    That is not a counterexample and it is not evidence either, so the draw
    decides nothing, which is the same reading the Lean printer takes when it
    declines to erase the family (see ``tests/test_lean.py``).
    """
    claim = _applies_outside_its_domain()
    report = claim.report(n=5)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0
    assert "outside the domain" in report.reason

    result = TestOracle(samples=5).establish(claim.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert "outside the domain" in result.provenance["untested"]


def test_a_shadowed_binder_does_not_survive_a_short_circuit() -> None:
    """A nested quantifier that leaks its last point turns a false goal into a pass.

    ``all(any(i == 0 for i in Fin[1]) & (i < 2) for i in Fin[3])`` is false at
    ``i = 2``. The inner existential returns at its witness, and the binder
    restoration used to sit after the loop it returned out of, so the outer
    ``i < 2`` was answered at the inner ``i = 0`` and the tester reported the
    statement as ``TESTED``.
    """
    i = Var("i")
    shadowing = Forall(((i, Fin[3]),), Exists(((i, Fin[1]),), i == 0) & (i < 2))
    fact = Fact(
        id="theorem:shadowed_binder",
        kind="theorem",
        statement=render(shadowing),
        term=Forall((), shadowing),
    )
    result = TestOracle(samples=5).establish(fact)
    assert result is not None
    assert result.status is Status.REFUTED
    assert result.decided_by == "property-test"

    # the same shape with nothing shadowed is unaffected
    j = Var("j")
    nested = Forall(((i, Fin[3]),), Exists(((j, Fin[3]),), j == i) & (i < 3))
    unshadowed = TestOracle(samples=5).establish(
        Fact(
            id="theorem:unshadowed_binder",
            kind="theorem",
            statement=render(nested),
            term=Forall((), nested),
        )
    )
    assert unshadowed is not None
    assert unshadowed.status is Status.TESTED


def test_a_table_declines_a_point_it_does_not_have() -> None:
    """And a negative index is not the last entry, which Python would make it."""
    from lanky.testing import Table

    table = Table([1, 2, 3], name="f")
    assert table(0) == 1
    assert table[2] == 3
    with pytest.raises(Undecided, match="outside the domain"):
        table(3)
    with pytest.raises(Undecided, match="outside the domain"):
        table(-1)


def _closed_false():
    """``-> 1 == 2``: no binders, no hypotheses, and false.

    Built inside a function because lanky's pytest plugin collects module-level
    theorems, and this one is meant to be refuted rather than run.
    """

    @theorem
    def impossible() -> 1 == 2:
        """Python answers this annotation: the term is the bool False."""

    return impossible


@theorem
def closed_true() -> 1 == 1:
    """The same shape, and true: a closed statement is still a claim."""


def _guarded_closed_goal():
    """A hypothesis that holds, and a goal Python already answered ``False``."""

    @theorem
    def guarded(h: all(i >= 0 for i in Fin[3])) -> 1 == 2:
        """The guard is satisfied, so nothing stands between this and refuted."""

    return guarded


def _constant_false_hypothesis():
    """A hypothesis that is the constant ``False``, which nothing satisfies."""

    @theorem
    def vacuous(h: 1 == 2) -> 1 == 3:
        """An implication with a false antecedent: valid, and untestable."""

    return vacuous


def _divides_by_a_variable():
    """``n // 0 == 0``: a Lean theorem and a Python ZeroDivisionError."""

    @theorem
    def div_zero(n: Nat) -> n // 0 == 0:
        """Total in Lean, undefined in Python."""

    return div_zero


def _applies_outside_its_domain():
    """``f(n)`` for an ``f : Fn[Fin[n], Nat]``: one point past the domain."""

    @theorem
    def outside(n: Nat, f: Fn[Fin[n], Nat]) -> f(n) == f(n):
        """A tautology in Lean once the family is erased, and ill typed here."""

    return outside


# }}}


# {{{ the membership test


def test_in_sort_knows_the_sorts_it_can_judge() -> None:
    """The membership test itself, including what it declines to judge."""
    from lanky.testing import in_sort

    assert in_sort(0, Nat, {})
    assert not in_sort(-1, Nat, {})
    assert not in_sort(True, Nat, {})
    assert in_sort(2, Fin[Var("n")], {"n": 3})
    assert not in_sort(3, Fin[Var("n")], {"n": 3})
    # an unevaluable bound cannot rule a value out, so it does not
    assert in_sort(3, Fin[Var("n")], {})
    # a sort with no membership test accepts, rather than rejecting every draw
    assert in_sort(object(), Fn[Fin[1], Nat], {})


# }}}


# {{{ a refutation names the quantified point that made it false


def test_a_refutation_under_a_quantifier_names_the_point() -> None:
    """The failing binder value used to be lost with the evaluator's context.

    ``all(i < 2 for i in Fin[n + 3])`` is false because of ``i = 2``, and the
    counterexample said only what ``n`` was drawn as, so it did not say why.
    A nest of quantifiers lost every point the same way, in the ledger too.
    """

    @theorem
    def bad(n: Nat) -> all(i < 2 for i in Fin[n + 3]):
        """False at every ``n``, and always because of ``i = 2``."""

    report = bad.report(n=5)
    assert not report.ok
    assert set(report.counterexample) == {"n", "i"}
    assert report.counterexample["i"] == 2

    @theorem
    def nested(n: Nat) -> all(
        all(i + j < 3 for j in Fin[n + 1] if j >= i) for i in Fin[n + 1]
    ):
        """False from ``n = 2`` on: at ``i = 1, j = 2``, and from 3 on at ``i = 0, j = 3``."""

    def first_failure(size: int) -> tuple[int, int]:
        # the points are visited in order, outer binder first, so the first
        # failure is the one the report should name
        return (1, 2) if size == 2 else (0, 3)

    report = nested.report(n=50)
    assert not report.ok
    witness = report.counterexample
    assert witness["n"] >= 2
    assert (witness["i"], witness["j"]) == first_failure(witness["n"])

    result = TestOracle(samples=50).establish(nested.fact())
    assert result is not None
    assert result.status is Status.REFUTED
    witness = result.provenance["counterexample"]
    assert (witness["i"], witness["j"]) == first_failure(witness["n"])


def test_a_quantified_point_does_not_overwrite_a_drawn_variable() -> None:
    """A binder that shadows a parameter is detail; the parameter is the witness.

    ``i`` is drawn, and the generator binds another ``i`` over ``Fin[i]``. The
    statement is false at every drawn ``i`` from 1 on, where the inner ``i = 0``
    fails, and the value that reproduces that is the drawn one.
    """

    @theorem
    def shadowing(i: Nat) -> all(i > 0 for i in Fin[i]):
        """The binder's own domain names the parameter it shadows."""

    report = shadowing.report(n=50)
    assert not report.ok
    assert report.counterexample["i"] >= 1


# }}}


# {{{ a theorem with no goal


def test_a_theorem_without_a_goal_is_refused_where_it_is_written() -> None:
    """A missing return annotation is a ``TypeError`` at the decorator.

    Such a theorem claims nothing. It read as ``True`` when it was called or
    sampled, and as ``assumed`` under ``lanky check``, because its fact had no
    term for an oracle to take: one statement with two answers. It is now
    refused where it is written, and so is ``-> None``, which evaluates to
    the same missing goal.
    """
    with pytest.raises(TypeError, match="a theorem needs a goal"):

        @theorem
        def no_goal(n: Nat, h: n > 1):
            """Hypotheses and no conclusion: it claims nothing."""

    with pytest.raises(TypeError, match="no_none_goal at .*: a theorem needs a goal"):

        @theorem
        def no_none_goal(n: Nat) -> None:
            """``None`` is not a proposition either."""


def test_a_file_with_a_goalless_theorem_does_not_import(tmp_path, capsys) -> None:
    """Under ``lanky check`` the refusal is an import failure with its reason."""
    from lanky import cli

    path = tmp_path / "goalless.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def goalless(n: Nat, h: n > 1):\n"
        '    """No return annotation."""\n',
        encoding="utf-8",
    )
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" in printed
    assert "TypeError: goalless at goalless.py:7: a theorem needs a goal" in printed


def test_the_tester_still_reads_a_missing_goal_as_true() -> None:
    """``lanky.testing.check`` takes ``goal=None`` from a direct caller as ``True``."""
    from lanky.testing import check

    report = check([("n", Nat)], [], None, samples=5)
    assert report.ok
    assert report.valid == 5


# }}}


# {{{ a statement that is not a proposition


def test_a_goal_that_is_not_a_proposition_is_never_tested() -> None:
    """``-> n + 1`` claims nothing, and Python's truthiness made it a pass.

    Lean declines it because its goal has type ``Nat``, while the tester read
    every nonzero draw as true and the ledger said ``tested``. The value is now
    refused wherever the statement is run, and the oracle's fact stays
    assumed with the reason in its provenance.
    """

    @theorem
    def not_a_prop(n: Nat) -> n + 1:
        """A number where a proposition should be."""

    with pytest.raises(TypeError, match="not a proposition"):
        not_a_prop.report(n=5)
    with pytest.raises(TypeError, match="not a proposition"):
        not_a_prop(n=1)
    result = TestOracle(samples=5).establish(not_a_prop.fact())
    assert result is not None
    assert result.status is Status.ASSUMED
    assert result.decided_by is None
    assert "not a proposition" in result.provenance["reason"]


def test_a_hypothesis_that_is_not_a_proposition_is_refused_too() -> None:
    """A hypothesis was coerced the same way, so it filtered by truthiness."""

    @theorem
    def not_a_hypothesis(n: Nat, h: n + 1) -> n >= 0:
        """A number where a hypothesis should be."""

    with pytest.raises(TypeError, match="not a proposition"):
        not_a_hypothesis.report(n=5)
    with pytest.raises(TypeError, match="not a proposition"):
        not_a_hypothesis(n=1)


def test_a_numpy_boolean_is_a_truth_value() -> None:
    """A comparison of numpy values answers a numpy bool, and that is one."""
    import numpy as np

    from lanky.testing import truth_value

    assert truth_value(np.bool_(True), "p") is True
    assert truth_value(np.int64(3) > np.int64(2), "p") is True
    assert truth_value(False, "p") is False
    with pytest.raises(TypeError, match="not a proposition"):
        truth_value(np.int64(1), "p")

    @theorem
    def ordered(f: Fn[Fin[2], Nat]) -> f(1) >= f(0):
        """Run at a numpy array, whose comparisons answer numpy bools."""

    assert ordered(f=np.array([0, 1])).holds
    assert not ordered(f=np.array([1, 0])).holds


def test_a_number_inside_a_proposition_is_refused_too() -> None:
    """One connective down, a number still passed as a proposition.

    Only the value of the whole goal and of each hypothesis was checked. The
    connectives and the quantifiers read their operands by Python's
    truthiness, so ``(n + 1) | (n > 5)`` and ``any(i + 1 for i in Fin[n + 2])``
    were ``TESTED``, and calling them answered that they held. A family of
    ``Bool`` given as numbers was refused as ``mask(0)`` and accepted under
    ``all``, and a refinement by a number refined by nothing.
    """

    @theorem
    def in_a_disjunction(n: Nat) -> (n + 1) | (n > 5):
        """A number as one side of a disjunction."""

    @theorem
    def as_a_witness(n: Nat) -> any(i + 1 for i in Fin[n + 2]):
        """A number as the body of an existential."""

    @theorem
    def in_a_hypothesis(n: Nat, h: (n + 1) | (n < 0)) -> n >= 0:
        """A number inside a disjunctive hypothesis."""

    for statement in (in_a_disjunction, as_a_witness, in_a_hypothesis):
        with pytest.raises(TypeError, match="not a proposition"):
            statement.report(n=5)
        result = TestOracle(samples=5).establish(statement.fact())
        assert result is not None
        assert result.status is Status.ASSUMED
        assert "not a proposition" in result.provenance["reason"]
    with pytest.raises(TypeError, match="not a proposition"):
        in_a_disjunction(n=1)
    with pytest.raises(TypeError, match="not a proposition"):
        as_a_witness(n=1)

    @theorem
    def all_set(n: Nat, mask: Fn[Fin[n], Bool]) -> all(mask(i) for i in Fin[n]):
        """Every entry of a family of Booleans is set."""

    with pytest.raises(TypeError, match="not a proposition"):
        all_set(n=2, mask=[1, 1])
    assert all_set(n=2, mask=[True, True]).holds

    k = Var("k")
    with pytest.raises(TypeError, match="not a proposition"):
        (Nat & (k + 1)).holds({"k": 3})


# }}}


# {{{ a family's codomain, and equality of families


def test_a_family_into_an_empty_codomain_is_not_a_counterexample() -> None:
    """``Fn[Fin[1], Nat & False]`` has no inhabitant, so ``-> False`` over it holds.

    An entry has no name to bind a refinement to, so the refinement of a
    codomain was dropped when an entry was drawn: the table held an ordinary
    natural, and a statement that is true because no such ``f`` exists was
    refuted by it. Now no draw is taken, and the fact stays assumed.
    """

    @theorem
    def vacuous(f: Fn[Fin[1], Nat & False]) -> False:
        """True, because nothing can be passed for ``f``."""

    report = vacuous.report(n=20)
    assert report.ok
    assert report.valid == 0
    assert "empty" in report.skipped[0]
    result = TestOracle(samples=20).establish(vacuous.fact())
    assert result is not None
    assert result.status is Status.ASSUMED


def test_a_codomain_refinement_is_judged_where_it_can_be() -> None:
    """A refinement naming only drawn variables is a condition, and it is kept.

    As a codomain ``Nat & (n > 0)`` is empty at ``n = 0`` and all of ``Nat``
    otherwise, so a draw at ``n = 0`` is not taken; it used to be, and it
    refuted the statement. A refinement that names nothing drawn cannot be
    judged at an entry, and its draw is not taken either. A family over an
    empty domain needs no entry, so its codomain is never consulted.
    """
    import random

    from lanky.testing import SkipSample, sample_value

    @theorem
    def sized(n: Nat, f: Fn[Fin[2], Nat & (n > 0)]) -> n > 0:
        """Whenever such an ``f`` exists, ``n`` is positive."""

    report = sized.report(n=30)
    assert report.ok
    assert report.valid == 30

    rng = random.Random(0)
    with pytest.raises(SkipSample, match="names x"):
        sample_value(Fn[Fin[1], Nat & (Var("x") > 0)], rng, {}, "f")
    assert sample_value(Fn[Fin[0], Nat & False], rng, {}, "f").values == []
    table = sample_value(Fn[Fin[2], Nat & (Var("n") > 0)], rng, {"n": 1}, "f")
    assert len(table) == 2


def test_a_refinement_that_cannot_be_evaluated_skips_the_draw() -> None:
    """``Nat & (10 // n > 1)`` has no answer at ``n = 0``, and that is one draw.

    The ``ZeroDivisionError`` escaped the sampler and ended the whole test at
    the first draw of ``n = 0``: a named refinement always did that, and once a
    codomain's refinement was evaluated too, a statement that used to be tested
    could no longer run at all. The goal is false at ``n = 0``, so a draw taken
    there regardless would refute it.
    """

    @theorem
    def into_a_ratio(n: Nat, f: Fn[Fin[2], Nat & (10 // n > 1)]) -> n >= 1:
        """Such an ``f`` exists only where ``10 // n > 1``, so ``n`` is positive."""

    @theorem
    def named_ratio(n: Nat, k: Nat & (10 // n > 1)) -> n >= 1:
        """The same condition on a named variable."""

    for statement in (into_a_ratio, named_ratio):
        report = statement.report(n=30)
        assert report.ok
        assert report.valid == 30
        assert any("cannot be evaluated" in reason for reason in report.skipped)


def test_two_families_compare_by_their_values() -> None:
    """Two empty families over ``Fin[0]`` are the one function there is.

    A table had no equality of its own, so ``f == g`` compared two drawn
    tables by identity and was refuted by the only pair there is.
    """
    from lanky.testing import Table

    @theorem
    def empty_equal(f: Fn[Fin[0], Nat], g: Fn[Fin[0], Nat]) -> f == g:
        """There is exactly one function out of an empty domain."""

    report = empty_equal.report(n=10)
    assert report.ok
    assert report.valid == 10
    result = TestOracle(samples=10).establish(empty_equal.fact())
    assert result is not None
    assert result.status is Status.TESTED
    assert empty_equal(f=[], g=[]).holds

    assert Table([1, 2]) == Table([1, 2])
    assert Table([1, 2]) != Table([2, 1])
    assert Table([Table([0])]) == Table([Table([0])])
    assert Table([Table([0])]) != Table([Table([1])])


# }}}


# {{{ a quantifier over a refined domain


def _establish(name: str, term) -> Fact:
    """What the property tester makes of a statement a plugin built by hand."""
    fact = TestOracle().establish(Fact(id=name, kind="theorem", statement=name, term=term))
    assert fact is not None
    return fact


def test_a_true_statement_about_a_refined_domain_is_not_refuted_outside_it() -> None:
    """``k > 0`` holds on ``Fin[n + 2] & (k > 0)`` by the domain's own refinement.

    The tester sampled the binder from ``Fin[n + 2]`` as if the refinement were
    not there, and refuted the statement at ``k = 0``, a point outside the
    domain, so ``lanky check`` exited 1 on a true statement that Lean proves.
    """
    n, k = Var("n"), Var("k")
    positive = Forall(((n, Nat),), Forall(((k, Fin[n + 2] & (k > 0)),), k > 0))
    fact = _establish("positive", positive)
    assert fact.status is Status.TESTED
    assert fact.provenance["valid"] == 200


def test_a_false_existential_over_a_refined_domain_is_refuted_with_the_reason() -> None:
    """No point of ``Fin[n + 2] & (k > 0)`` is zero, and the tester says that.

    It used to find its witness at ``k = 0``, which the refinement excludes,
    and report the statement ``tested``. The base is enumerated, so the
    refutation is that no point of the domain is a witness, not that a draw
    missed one.
    """
    n, k = Var("n"), Var("k")
    zero = Forall(((n, Nat),), Exists(((k, Fin[n + 2] & (k > 0)),), k == 0))
    fact = _establish("zero", zero)
    assert fact.status is Status.REFUTED
    assert set(fact.provenance["counterexample"]) == {"n"}
    assert fact.provenance["reason"] == (
        "the goal is false at this assignment: no point of k in Fin(n + 2) & (k > 0) "
        "is a witness to k == 0, and every point was tried, because the domain is "
        "enumerated"
    )
    # a witness inside the domain is still found
    last = Forall(((n, Nat),), Exists(((k, Fin[n + 2] & (k > 0)),), k == n + 1))
    assert _establish("last", last).status is Status.TESTED


def test_a_sampled_refined_domain_never_yields_a_point_outside_it() -> None:
    """``Nat & (k > 0)`` as a binder domain is sampled from the refined domain.

    The true statement used to be refuted at ``k = 0``; the false one is
    refuted, and always at ``k = 1``, the one point of the domain that breaks
    it.
    """
    n, k = Var("n"), Var("k")
    domain = Nat & (k > 0)
    for seed in range(10):
        oracle = TestOracle(samples=50, seed=seed)
        true = Forall(((n, Nat),), Forall(((k, domain),), k > 0))
        fact = oracle.establish(Fact(id="true", kind="theorem", statement="", term=true))
        assert fact.status is Status.TESTED
        false = Forall(((n, Nat),), Forall(((k, domain),), k >= 2))
        fact = oracle.establish(Fact(id="false", kind="theorem", statement="", term=false))
        assert fact.status is Status.REFUTED
        assert fact.provenance["counterexample"]["k"] == 1


def test_a_refinement_that_rejects_every_draw_leaves_the_fact_assumed() -> None:
    """``Nat & (k == 1000)`` rejects every draw of ``Nat``, so nothing is tested.

    The ``forall`` used to be read over the unfiltered draws and refuted at
    one of them; read over the refined domain it holds at no point, which is
    a vacuous pass and not evidence. The existential over ``Nat & (k > 0)``
    used to be witnessed at ``k = 0``, outside its domain, and reported
    ``tested``; no draw of the domain witnesses it, and over a sampled domain
    that decides nothing either.
    """
    n, k = Var("n"), Var("k")
    far = Forall(((n, Nat),), Forall(((k, Nat & (k == 1000)),), k == 1000))
    fact = _establish("far", far)
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.provenance["valid"] == 0
    assert "satisfied its refinement" in fact.provenance["untested"]

    unwitnessed = Forall(((n, Nat),), Exists(((k, Nat & (k > 0)),), k == 0))
    fact = _establish("unwitnessed", unwitnessed)
    assert fact.status is Status.ASSUMED
    assert fact.provenance["valid"] == 0
    assert "witness" in fact.provenance["untested"]


def test_a_refinement_that_rejects_every_draw_stops_at_the_draw_budget() -> None:
    """Every draw is undecided, and the test ends at its budget of draws.

    The binder's draws are a fixed handful per assignment and the refinement
    only filters them, so nothing redraws until the refinement is satisfied:
    the test is ``samples * REJECTION_FACTOR`` attempts, each of them counted
    as undecided, and it ends.
    """
    from lanky.testing import REJECTION_FACTOR

    n, k = Var("n"), Var("k")
    far = Forall(((n, Nat),), Forall(((k, Nat & (k > 100)),), k < 0))
    fact = TestOracle(samples=30).establish(
        Fact(id="far", kind="theorem", statement="far", term=far)
    )
    assert fact.status is Status.ASSUMED
    assert fact.provenance["samples"] == 30 * REJECTION_FACTOR
    assert fact.provenance["undecided"] == 30 * REJECTION_FACTOR


def test_a_refinement_that_admits_few_draws_is_tested_on_the_ones_it_admits() -> None:
    """``Nat & (k == 3)`` admits about one draw in six: tested, and never at another k.

    A walk that admitted no draw is undecided and is not counted as valid, so
    the valid draws are the ones that evaluated the body at ``k = 3``.
    """
    n, k = Var("n"), Var("k")
    true = Forall(((n, Nat),), Forall(((k, Nat & (k == 3)),), k == 3))
    fact = _establish("three", true)
    assert fact.status is Status.TESTED
    assert fact.provenance["valid"] == 200
    assert fact.provenance["undecided"] > 0
    false = Forall(((n, Nat),), Forall(((k, Nat & (k == 3)),), k == 4))
    fact = _establish("four", false)
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"]["k"] == 3


def test_a_refinement_that_names_an_earlier_binder_is_read_at_its_point() -> None:
    """``k`` in ``Fin[n] & (k > j)`` ranges above the ``j`` bound just before it.

    Both quantifiers see exactly the pairs with ``j < k``: the universal is
    refuted at a pair inside the domain and the existential that needs
    ``k == j`` has no witness among them.
    """
    n, j, k = Var("n"), Var("j"), Var("k")
    binders = ((j, Fin[n]), (k, Fin[n] & (k > j)))
    assert _establish("above", Forall(((n, Nat),), Forall(binders, k > j))).status is (
        Status.TESTED
    )
    fact = _establish("far_above", Forall(((n, Nat),), Forall(binders, k > j + 1)))
    assert fact.status is Status.REFUTED
    point = fact.provenance["counterexample"]
    assert point["j"] < point["k"] < point["n"]
    assert point["k"] == point["j"] + 1
    fact = _establish("equal", Forall(((n, Nat),), Exists(binders, k == j)))
    assert fact.status is Status.REFUTED
    assert "every point was tried" in fact.provenance["reason"]
    # nested rather than grouped, the inner refinement reads the outer binder
    nested = Forall(((j, Fin[n]),), Exists(((k, Fin[n] & (k > j)),), k == j + 1))
    fact = _establish("next", Forall(((n, Nat),), nested))
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"]["j"] == fact.provenance["counterexample"]["n"] - 1


def test_a_definition_over_a_refined_domain_is_assigned_only_inside_it() -> None:
    """``f(i) == 0`` at the points of ``Fin[3] & (i > 0)`` says nothing of ``f(0)``.

    A refined domain could not be walked without a sampler, so the assignment
    pass raised and the whole test with it. It is walked now, and only at the
    points the refinement admits: ``f(0)`` stays as drawn, a goal about it is
    refuted, and one about ``f(2)`` is tested.
    """
    from lanky.testing import check

    f, i = Var("f"), Var("i")
    definition = Forall(((i, Fin[3] & (i > 0)),), f(i) == 0)
    report = check([("f", Fn[Fin[3], Nat])], [definition], f(0) == 0, samples=50)
    assert not report.ok
    assert report.counterexample["f"][0] != 0
    assert report.counterexample["f"][1:] == [0, 0]
    report = check([("f", Fn[Fin[3], Nat])], [definition], f(2) == 0, samples=50)
    assert report.ok
    assert report.valid == 50


def test_a_definition_over_a_refinement_that_cannot_be_answered_drops_the_draw() -> None:
    """The walk meets ``6 // i`` at ``i = 0``; the draw is undecided, not a crash."""
    from lanky.testing import check

    f, i = Var("f"), Var("i")
    definition = Forall(((i, Fin[3] & (6 // i > 1)),), f(i) == 0)
    report = check([("f", Fn[Fin[3], Nat])], [definition], f(1) == 0, samples=20)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0


def test_an_unnamed_draw_of_a_refined_sort_honours_the_refinement() -> None:
    """A value drawn without a name used to come from the base, unchecked.

    That is how the sampler drew a quantifier's points over a refined domain.
    It is now judged as a family's entry is: a refinement naming only drawn
    variables is a condition, and one naming anything else cannot be judged.
    """
    import random

    from lanky.testing import SkipSample, sample_value

    rng = random.Random(0)
    with pytest.raises(SkipSample, match="names k"):
        sample_value(Nat & (Var("k") > 0), rng, {})
    with pytest.raises(SkipSample, match="empty"):
        sample_value(Nat & (Var("n") > 0), rng, {"n": 0})
    assert sample_value(Nat & (Var("n") > 0), rng, {"n": 1}) in range(6)


# }}}


# {{{ a guarded universal over a sampled domain


GUARD_PROBE = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Nat\n\n\n"
    "@theorem\n"
    "def never_reached(n: Nat) -> all(k < 0 for k in Nat if k > 100):\n"
    '    """False at k = 101, and no draw of k gets past the guard."""\n'
)


def test_a_guard_no_draw_passes_leaves_the_fact_assumed(tmp_path, oracles, capsys) -> None:
    """``never_reached`` is false at ``k = 101``, and no draw of ``k`` gets that far.

    Every draw of ``k`` failed the guard, so the ``forall`` held at no point,
    and the fact was reported ``tested`` over 200 valid draws of which not one
    evaluated the body. It is ``assumed`` now, with the reason, and the check
    exits 0, because nothing refuted it either.
    """
    oracles(TestOracle())
    path = _write(tmp_path, GUARD_PROBE, "guard_probe.py")
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.provenance["valid"] == 0
    assert "no draw of Nat passed the guard k > 100" in fact.provenance["untested"]
    assert cli.main(["check", path]) == 0
    assert "assumed" in capsys.readouterr().out


def test_a_guarded_universal_over_an_index_type_is_unchanged() -> None:
    """Over ``Fin`` the guarded domain is enumerated, so both answers stand.

    A guard nothing passes leaves a domain that really is empty, and the
    vacuous pass is a pass; a guard some point passes is a statement about
    those points, and a false one is refuted at one of them.
    """
    n, k = Var("n"), Var("k")
    empty = Forall(((n, Nat),), Forall(((k, Fin[n]),), k < 0, k > 100))
    assert _establish("empty", empty).status is Status.TESTED
    false = Forall(((n, Nat),), Forall(((k, Fin[n + 3]),), k < 2, k > 0))
    fact = _establish("false", false)
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"]["k"] == 2


def test_the_guard_and_the_refinement_spellings_agree() -> None:
    """``k`` in ``Nat`` where ``p`` and ``k`` in ``Nat & p`` are one statement.

    The Lean printer reads both as ``p →``, and the tester read the guard as
    a pass where it declined the refinement. They agree now: undecided when
    no draw gets through, tested when some do and the body holds, refuted at
    a draw that gets through when it does not.
    """
    n, k = Var("n"), Var("k")

    def both(guard, body):
        return (
            Forall(((n, Nat),), Forall(((k, Nat),), body, guard)),
            Forall(((n, Nat),), Forall(((k, Nat & guard),), body)),
        )

    for claim in both(k > 100, k < 0):
        fact = _establish("far", claim)
        assert fact.status is Status.ASSUMED
        assert fact.provenance["valid"] == 0
    for claim in both(k == 3, k == 3):
        assert _establish("three", claim).status is Status.TESTED
    for claim in both(k == 3, k == 4):
        fact = _establish("four", claim)
        assert fact.status is Status.REFUTED
        assert fact.provenance["counterexample"]["k"] == 3


def test_a_hypothesis_whose_guard_no_draw_passes_admits_no_draw() -> None:
    """``h: all(k < m for k in Nat if k > 100)`` is false for every ``m``.

    So the statement is vacuously true, and it used to be refuted: the guard
    rejected every draw of ``k``, the hypothesis read as ``True``, and the goal
    ``m < 0`` failed at a draw the statement excludes.
    """

    @theorem
    def beyond(m: Nat, h: all(k < m for k in Nat if k > 100)) -> m < 0:
        """True vacuously: every natural above 100 bounds no natural m."""

    fact = TestOracle().establish(beyond.fact())
    assert fact.status is Status.ASSUMED
    assert fact.provenance["valid"] == 0
    assert "passed the guard" in fact.provenance["untested"]


# }}}


# {{{ where a sampled universal stands


POLARITY = (
    "from __future__ import annotations\n\n"
    "from lanky import theorem\n"
    "from lanky.prelude import Nat\n\n\n"
    "@theorem\n"
    "def negated(n: Nat) -> ~all(k < 100 for k in Nat):\n"
    '    """True: not every natural is below 100 (k = 100 is not)."""\n\n\n'
    "@theorem\n"
    "def assumed_bound(m: Nat, h: all(k < m for k in Nat)) -> m < 0:\n"
    '    """True vacuously: no natural m bounds every natural."""\n\n\n'
    "@theorem\n"
    "def summed(n: Nat) -> sum(1 for k in Nat) < 3:\n"
    '    """Not a statement about a finite sum at all."""\n'
)


def test_a_sampled_universal_that_is_not_asserted_is_never_refuted(
    tmp_path, oracles, capsys
) -> None:
    """A pass over draws is evidence only where the statement asserts the universal.

    Under a negation it turned into a refutation of a true statement, in a
    hypothesis it admitted a draw the statement excludes, and a sum over
    draws of ``Nat`` was read as a finite sum; all three were ``refuted``, at
    counterexamples that do not replay. They are ``assumed`` now, each with
    the reason, and the check exits 0.
    """
    oracles(TestOracle())
    path = _write(tmp_path, POLARITY, "polarity.py")
    facts = {fact.owner: fact for fact in check_path(path)}
    for fact in facts.values():
        assert fact.status is Status.ASSUMED, fact.owner
        assert fact.provenance["valid"] == 0
    assert "assumes or denies it" in facts["negated"].provenance["untested"]
    assert "assumes or denies it" in facts["assumed_bound"].provenance["untested"]
    assert "sum over draws is not the sum" in facts["summed"].provenance["untested"]
    assert cli.main(["check", path]) == 0
    assert "REFUTED" not in capsys.readouterr().out


def test_a_sampled_universal_in_a_goal_is_still_refuted() -> None:
    """A counterexample is real wherever it is drawn: ``k < 3`` fails at ``k = 3``."""

    @theorem
    def below_three(n: Nat) -> all(k < 3 for k in Nat):
        """False: 3 is a natural."""

    fact = TestOracle().establish(below_three.fact())
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"]["k"] >= 3

    @theorem
    def denied(n: Nat) -> ~~all(k < 3 for k in Nat):
        """The same claim under two negations, which is where it started."""

    assert TestOracle().establish(denied.fact()).status is Status.REFUTED


def test_an_antecedent_is_read_where_it_stands_however_it_is_spelled() -> None:
    """``~p | q`` is how an implication is written, and ``p`` stands under the ``~``.

    Each of these is true, and each was refuted on the strength of four draws
    of ``k``: the antecedent of an implication, the guard of an existential
    under a negation, and an existential hypothesis whose guard is the sampled
    universal. They are ``assumed`` now. The consequent of an implication is
    asserted, and a draw that breaks a universal there still refutes it.
    """

    @theorem
    def implied(n: Nat) -> ~all(k < 100 for k in Nat) | (n < 0):
        """True: the antecedent is false, since k = 100 is a natural."""

    @theorem
    def unwitnessed(n: Nat) -> ~any(i >= 0 for i in Fin[n + 1] if all(k < 100 for k in Nat)):
        """True: the guard is false, so nothing is a witness."""

    @theorem
    def admitted(n: Nat, h: any(i == 0 for i in Fin[n + 1] if all(k < 100 for k in Nat))) -> n < 0:
        """True vacuously: the hypothesis is false at every n."""

    for claim in (implied, unwitnessed, admitted):
        fact = TestOracle().establish(claim.fact())
        assert fact.status is Status.ASSUMED, claim.__name__
        assert fact.provenance["valid"] == 0
        assert "assumes or denies it" in fact.provenance["untested"]

    @theorem
    def consequent(n: Nat) -> ~(n >= 0) | all(k < 3 for k in Nat):
        """False: 3 is a natural."""

    fact = TestOracle().establish(consequent.fact())
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"]["n"] >= 0


def test_a_sampled_universal_used_as_a_value_is_undecided() -> None:
    """Compared with a truth value, or counted by a sum, a pass over draws is a value.

    ``all(k < 100 for k in Nat) == False`` is true, and it was refuted
    because four draws made the universal ``True``; a sum counting the points
    of ``Fin[n + 1]`` at which the same universal holds is ``0``, and it was
    refuted at ``n + 1``. A guard that is the same universal is its
    antecedent, and ``all(i < 0 for i in Fin[n + 1] if ...)`` is vacuously
    true.
    """

    @theorem
    def compared(n: Nat) -> all(k < 100 for k in Nat) == False:  # noqa: E712
        """True: some natural is not below 100."""

    @theorem
    def counted(n: Nat) -> sum(1 for i in Fin[n + 1] if all(k < 100 for k in Nat)) == 0:
        """True: the guard is false, so nothing is counted."""

    @theorem
    def guarded(n: Nat) -> all(i < 0 for i in Fin[n + 1] if all(k < 100 for k in Nat)):
        """True vacuously: the guard is false."""

    for claim in (compared, counted, guarded):
        fact = TestOracle().establish(claim.fact())
        assert fact.status is Status.ASSUMED, claim.__name__
        assert fact.provenance["valid"] == 0


def test_a_quantified_definition_over_a_sampled_domain_is_left_to_the_filter() -> None:
    """``h: all(f(k) == 0 for k in Nat)`` has no points to assign at.

    The assignment pass walked it without a sampler, which raised "cannot
    enumerate the binder domain" and ended the test. It is a hypothesis the
    filter reads now, and a pass of it over draws admits no draw.
    """
    from lanky.testing import check

    f, k, n = Var("f"), Var("k"), Var("n")
    definition = Forall(((k, Nat),), f(k) == 0)
    report = check([("n", Nat), ("f", Fn[Fin[n], Nat])], [definition], f(0) == 0, samples=20)
    assert report.ok
    assert report.valid == 0
    assert report.undecided > 0


def test_an_existential_whose_enumerated_binders_are_empty_is_refuted() -> None:
    """``any(k >= 0 for i in Fin[n] for k in Nat)`` is false at ``n = 0``.

    No point of ``Fin[0]`` means no point of the domain, so the walk never
    drew a ``k`` and its ``False`` is exact. It used to be undecided because a
    binder domain was sampled, and the statement was ``tested`` on the draws
    with ``n > 0``.
    """

    @theorem
    def somewhere(n: Nat) -> any(k >= 0 for i in Fin[n] for k in Nat):
        """False at n = 0, where there is no i."""

    fact = TestOracle().establish(somewhere.fact())
    assert fact.status is Status.REFUTED
    assert fact.provenance["counterexample"] == {"n": 0}
    assert fact.provenance["reason"].endswith(
        "every point was tried, because the enumerated binders before the first "
        "sampled one have no point"
    )


# }}}


# {{{ a later binder's domain names an earlier binder


def test_a_codomain_refined_by_a_nested_quantifier_is_tested() -> None:
    """A codomain whose refinement names only drawn variables is judged once per table.

    ``all(j < n for i in Fin[n] for j in Fin[i])`` names ``n`` alone, but its
    inner ``Fin[i]`` was read as naming a free ``i``, so the tester refused
    to draw the family's entries and the fact stayed ``assumed``.
    """
    from lanky.terms import forall
    from lanky.testing import check

    f, n = Var("f"), Var("n")
    nested = Nat & forall(j < n for i in Fin[n] for j in Fin[i])
    report = check([("n", Nat), ("f", Fn[Fin[2], nested])], [], f(0) >= 0, samples=20)
    assert report.ok
    assert report.valid == 20
    assert report.unsampleable == 0


def test_an_inner_binder_named_like_a_parameter_does_not_order_the_draws() -> None:
    """A sort is drawn after the variables it names, and an inner binder is not one of them.

    ``m``'s refinement binds its own ``i``, which ``Fin[i]`` names; read as
    the parameter ``i``, it made ``m`` and ``i`` wait for each other, and the
    order was left as written, so ``i`` was drawn before the ``m`` it names.
    """
    from lanky.terms import forall
    from lanky.testing import check, sampling_order

    i, m = Var("i"), Var("m")
    i_sort = Nat & (i >= m)
    m_sort = Nat & forall(j <= i for i in Fin[m] for j in Fin[i])
    order = sampling_order([("i", i_sort), ("m", m_sort)])
    assert [name for name, _ in order] == ["m", "i"]
    report = check([("i", i_sort), ("m", m_sort)], [], i >= m, samples=20)
    assert report.ok
    assert report.valid == 20


# }}}
