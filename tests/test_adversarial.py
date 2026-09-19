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
from lanky.ledger import Fact, Ledger, Status
from lanky.oracles.test import TestOracle
from lanky.prelude import Fin, Fn, Nat
from lanky.terms import Var, structurally_equal

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
