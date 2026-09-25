"""The ledger: statuses, rendering, JSON, and refutation."""

from __future__ import annotations

import json

from lanky.ledger import Fact, Ledger, Status
from lanky.terms import Var


def test_statuses_include_refuted() -> None:
    assert {s.value for s in Status} == {
        "tested",
        "decided",
        "proved",
        "certified",
        "assumed",
        "refuted",
    }


def make_fact(fact_id: str, status: Status = Status.ASSUMED, **kwargs: object) -> Fact:
    return Fact(
        id=fact_id,
        kind="theorem",
        statement=f"{fact_id} holds",
        term=Var("n") >= 0,
        status=status,
        where="demo.py:1",
        owner=fact_id,
        **kwargs,
    )


def test_add_iter_and_by_status() -> None:
    ledger = Ledger([make_fact("a", Status.TESTED), make_fact("b")])
    assert [fact.id for fact in ledger] == ["a", "b"]
    assert len(ledger) == 2
    assert "a" in ledger
    assert ledger.by_status(Status.TESTED) == (ledger["a"],)
    assert ledger.counts() == {"tested": 1, "assumed": 1}


def test_add_replaces_in_place_so_an_oracle_can_upgrade() -> None:
    ledger = Ledger([make_fact("a"), make_fact("b")])
    ledger.add(ledger["a"].with_status(Status.PROVED, "lean", tactic="omega"))
    assert [fact.id for fact in ledger] == ["a", "b"]
    assert ledger["a"].status is Status.PROVED
    assert ledger["a"].decided_by == "lean"
    assert ledger["a"].provenance == {"tactic": "omega"}


def test_refuted_carries_its_witness() -> None:
    refuted = make_fact("c").with_status(
        Status.REFUTED, "property-test", counterexample={"n": -1}
    )
    ledger = Ledger([refuted])
    assert ledger.by_status(Status.REFUTED) == (refuted,)
    assert refuted.provenance["counterexample"] == {"n": -1}


def test_render_is_a_fixed_width_table() -> None:
    ledger = Ledger(
        [
            make_fact("a", Status.TESTED, decided_by="property-test"),
            make_fact("b", Status.REFUTED, decided_by="property-test"),
        ]
    )
    text = ledger.render()
    lines = text.splitlines()
    assert lines[0].split() == ["STATUS", "BY", "WHERE", "OWNER", "STATEMENT"]
    assert set(lines[1]) == {"-", " "}
    assert "tested" in lines[2]
    assert "refuted" in lines[3]
    assert "2 facts" in lines[-1]
    assert Ledger().render() == "ledger is empty"


def test_a_vacuous_fact_is_marked_beside_its_status() -> None:
    """``proved`` is true of a vacuous fact, and the table says what else is.

    The mark is the provenance's ``vacuous`` entry; the status column reads
    ``proved (vacuous)``, the summary counts vacuous facts after the statuses,
    and a ledger with none renders exactly as before.
    """
    vacuous = make_fact(
        "v",
        Status.PROVED,
        decided_by="lean",
        provenance={"vacuous": "the hypotheses are inconsistent: proved by lean"},
    )
    plain = make_fact("p", Status.PROVED, decided_by="lean")
    ledger = Ledger([vacuous, plain])
    assert vacuous.is_vacuous
    assert not plain.is_vacuous
    assert ledger.vacuous() == (vacuous,)
    lines = ledger.render().splitlines()
    assert lines[2].startswith("proved (vacuous)  lean")
    assert lines[3].startswith("proved            lean")
    assert lines[-1] == "2 facts: 2 proved; 1 vacuous"
    assert Ledger([plain]).render().splitlines()[-1] == "1 facts: 1 proved"
    assert ledger.counts() == {"proved": 2}


def test_to_json_round_trips() -> None:
    ledger = Ledger([make_fact("a", Status.TESTED, decided_by="property-test")])
    data = json.loads(ledger.to_json())
    assert data == [
        {
            "id": "a",
            "kind": "theorem",
            "statement": "a holds",
            "term": "n >= 0",
            "status": "tested",
            "decided_by": "property-test",
            "provenance": {},
            "where": "demo.py:1",
            "owner": "a",
        }
    ]
