"""The ledger: statuses, rendering, JSON, and refutation."""

from __future__ import annotations

import json

import pytest

from lanky.ledger import Fact, Ledger, Status, Support
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
    kwargs.setdefault("owner", fact_id)
    return Fact(
        id=fact_id,
        kind="theorem",
        statement=f"{fact_id} holds",
        term=Var("n") >= 0,
        status=status,
        where="demo.py:1",
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
            "rests_on": [],
            "effective": "tested",
            "under": [],
        }
    ]


# {{{ facts rest on facts


def axiom_fact(fact_id: str, owner: str = "") -> Fact:
    """An axiom, as ``@axiom`` builds one: assumed, on a citation."""
    return Fact(
        id=fact_id,
        kind="axiom",
        statement=f"{fact_id} holds",
        status=Status.ASSUMED,
        provenance={"cite": "a textbook"},
        where="demo.py:1",
        owner=owner or fact_id,
    )


def test_rests_on_holds_fact_ids_as_a_tuple() -> None:
    assert make_fact("a").rests_on == ()
    fact = make_fact("a", rests_on=["b", "c"])
    assert fact.rests_on == ("b", "c")
    assert fact.with_status(Status.PROVED, "lean").rests_on == ("b", "c")
    # one id is a tuple of one, not one id per character
    with pytest.raises(TypeError, match=r"a single id is written \('bc',\)"):
        make_fact("a", rests_on="bc")
    with pytest.raises(TypeError, match="names facts by id"):
        make_fact("a", rests_on=[make_fact("b")])


def test_a_fact_that_rests_on_nothing_is_worth_its_own_status() -> None:
    ledger = Ledger([make_fact("a", Status.PROVED), make_fact("b")])
    assert ledger.support("a") == Support(effective=Status.PROVED, under=())
    assert ledger.support(ledger["b"]) == Support(effective=Status.ASSUMED, under=())
    assert not make_fact("a").is_axiom
    assert axiom_fact("x").is_axiom


def test_a_proof_from_an_axiom_is_worth_the_axiom_and_is_under_it() -> None:
    ledger = Ledger(
        [
            axiom_fact("jump"),
            make_fact("second_kind", Status.PROVED, decided_by="lean", rests_on=("jump",)),
        ]
    )
    assert ledger.support("second_kind") == Support(effective=Status.ASSUMED, under=("jump",))
    # the axiom itself rests on nothing and is worth what it says
    assert ledger.support("jump") == Support(effective=Status.ASSUMED, under=())


def test_the_effective_status_is_the_weakest_over_the_closure() -> None:
    """Established facts below lower the worth without being assumptions."""
    ledger = Ledger(
        [
            make_fact("top", Status.CERTIFIED, rests_on=("middle",)),
            make_fact("middle", Status.DECIDED, rests_on=("bottom",)),
            make_fact("bottom", Status.TESTED),
        ]
    )
    assert ledger.support("top") == Support(effective=Status.TESTED, under=())
    assert ledger.support("middle") == Support(effective=Status.TESTED, under=())
    # a fact is never worth more than its own status
    weak = Ledger(
        [make_fact("weak", Status.TESTED, rests_on=("strong",)), make_fact("strong", Status.PROVED)]
    )
    assert weak.support("weak").effective is Status.TESTED


def test_under_lists_every_assumption_in_the_closure_once_in_order() -> None:
    """Depth first, in the order each fact names what it rests on."""
    ledger = Ledger(
        [
            make_fact("t", Status.PROVED, rests_on=("lemma", "a1", "a2")),
            make_fact("lemma", Status.PROVED, rests_on=("a2", "a3")),
            axiom_fact("a1"),
            axiom_fact("a2"),
            make_fact("a3"),  # assumed for want of an oracle, not on a citation
        ]
    )
    assert ledger.support("t") == Support(effective=Status.ASSUMED, under=("a2", "a3", "a1"))
    assert ledger.support("lemma").under == ("a2", "a3")


def test_resting_on_a_refuted_fact_is_worth_a_refutation() -> None:
    ledger = Ledger(
        [
            make_fact("t", Status.PROVED, rests_on=("lemma",)),
            make_fact("lemma", Status.PROVED, rests_on=("wrong",)),
            make_fact("wrong", Status.REFUTED, provenance={"counterexample": {"n": 0}}),
        ]
    )
    assert ledger.support("t") == Support(effective=Status.REFUTED, under=("wrong",))


def test_an_id_the_ledger_does_not_hold_counts_as_an_assumption() -> None:
    """A claim in a file this check did not collect: nothing here established it."""
    ledger = Ledger([make_fact("t", Status.DECIDED, rests_on=("theorem:helpers.lemma@12",))])
    assert ledger.support("t") == Support(
        effective=Status.ASSUMED, under=("theorem:helpers.lemma@12",)
    )


def test_a_circular_argument_establishes_nothing() -> None:
    """Every fact on a circle, and every fact above one, is worth ``assumed`` at most."""
    ledger = Ledger(
        [
            make_fact("a", Status.PROVED, rests_on=("b",)),
            make_fact("b", Status.PROVED, rests_on=("a",)),
            make_fact("c", Status.TESTED, rests_on=("a",)),
            make_fact("self", Status.DECIDED, rests_on=("self",)),
        ]
    )
    assert ledger.support("a") == Support(effective=Status.ASSUMED, under=("b", "a"))
    assert ledger.support("b") == Support(effective=Status.ASSUMED, under=("a", "b"))
    assert ledger.support("c") == Support(effective=Status.ASSUMED, under=("a", "b"))
    assert ledger.support("self") == Support(effective=Status.ASSUMED, under=("self",))


def test_the_table_says_what_a_fact_is_under_and_what_it_is_worth() -> None:
    """``proved under jump``, and an ``EFFECTIVE`` column once some fact is weaker.

    An assumption is named by its owner when that owner names one fact, and by
    its id otherwise: a plugin's kernel owns many facts, and an id the ledger
    does not hold has no owner at all.
    """
    ledger = Ledger(
        [
            axiom_fact("axiom:demo.jump@3", owner="jump"),
            make_fact(
                "t",
                Status.PROVED,
                decided_by="lean",
                rests_on=("axiom:demo.jump@3", "k:post", "elsewhere"),
            ),
            make_fact("k:post", owner="k"),
            make_fact("k:bounds", Status.DECIDED, decided_by="isl", owner="k"),
        ]
    )
    lines = ledger.render().splitlines()
    assert lines[0].split() == ["STATUS", "EFFECTIVE", "BY", "WHERE", "OWNER", "STATEMENT"]
    assert lines[2].split("  ")[0] == "assumed (axiom)"
    assert lines[3].startswith("proved under jump, k:post, elsewhere  assumed    lean ")
    assert lines[4].split()[:2] == ["assumed", "assumed"]
    assert lines[5].split()[:3] == ["decided", "decided", "isl"]
    assert lines[-1] == "4 facts: 2 assumed, 1 decided, 1 proved"


def test_a_ledger_where_nothing_is_weaker_keeps_its_columns() -> None:
    """An assumed fact under an assumed one is worth what it says: no new column."""
    ledger = Ledger([make_fact("post"), make_fact("restated", rests_on=("post",))])
    lines = ledger.render().splitlines()
    assert lines[0].split() == ["STATUS", "BY", "WHERE", "OWNER", "STATEMENT"]
    assert lines[3].startswith("assumed under post  -")


def test_the_json_carries_what_each_fact_is_worth_and_under_what() -> None:
    ledger = Ledger(
        [
            axiom_fact("jump"),
            make_fact("t", Status.PROVED, decided_by="lean", rests_on=("jump",)),
        ]
    )
    data = json.loads(ledger.to_json())
    assert [(row["id"], row["status"], row["effective"], row["under"]) for row in data] == [
        ("jump", "assumed", "assumed", []),
        ("t", "proved", "assumed", ["jump"]),
    ]
    assert data[1]["rests_on"] == ["jump"]
    assert data[0]["provenance"] == {"cite": "a textbook"}
    assert ledger["t"].to_dict()["rests_on"] == ["jump"]
    assert "effective" not in ledger["t"].to_dict()


# }}}
