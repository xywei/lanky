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

from lanky import theorem
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


def test_a_theorem_without_a_goal_claims_true_everywhere() -> None:
    """A missing return annotation reads as ``True`` in every way of running it.

    ``statement`` and ``__call__`` said ``True`` while ``report`` handed
    ``None`` to the tester, which read it as false and returned a
    counterexample, so the pytest plugin failed a theorem its own call passed.
    The second round of fixes on the MVP made them agree; this pins it.
    """

    @theorem
    def no_goal(n: Nat, h: n > 1):
        """Hypotheses and no conclusion: it claims nothing."""

    assert no_goal.statement == "n : Nat | n > 1 |- True"
    assert no_goal(n=3).holds
    assert no_goal.test(n=5) == (True, None)
    report = no_goal.report(n=5)
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
