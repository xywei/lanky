"""Probes that try to make lanky claim something it has not established.

Three ways a checker like this goes quietly wrong, one test each: a statement
nobody could actually test reported as tested, a name that means two things at
once read as one of them, and a refutation that does not survive being written
down. Each of these is about the *report* rather than about the mathematics: the
failure mode that matters here is a ledger that reads better than the evidence.
"""

from __future__ import annotations

import json

from lanky import theorem
from lanky.check import check_path
from lanky.ledger import Fact, Ledger, Status
from lanky.oracles.test import TestOracle
from lanky.prelude import Fin, Fn, Nat
from lanky.terms import Forall, Var, structurally_equal

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


def test_a_vacuous_pass_is_assumed_in_the_ledger(tmp_path, monkeypatch) -> None:
    """End to end: the row reads ``assumed`` and says why, and the check passes."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    from lanky.check import check_path

    path = tmp_path / "vacuous.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def nothing_satisfies(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1:\n"
        '    """Vacuous."""\n',
        encoding="utf-8",
    )
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.provenance["valid"] == 0
    assert "assumed" in ledger.render()


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
