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


#: A kernel's postcondition, as lanky check printed it cut at 72 characters
#: before #142: two claims, each with a guard.
POSTCONDITION = (
    "(forall i in Fin(nb), a in Nat, b in Nat where a < 2 and a + b <= 10. "
    "R[i, a, b] == C[i, a, b]) and (forall i in Fin(nb), a in Nat, b in Nat "
    "where a + b + 2 <= 10. R[i, a + 2, b] == -R[i, a, b + 2])"
)


def test_a_statement_too_long_for_its_column_is_wrapped_under_it_not_cut() -> None:
    """#142: the table prints every statement whole.

    One that fits is one line, as it always was. A longer one goes on under
    the statement column, broken at spaces only, so its lines read back the
    statement; the row's other cells are on its first line, and the lines
    after it are blank up to the statement column.
    """
    short = make_fact("short", Status.DECIDED, decided_by="isl")
    post = Fact(
        id="post",
        kind="postcondition",
        statement=POSTCONDITION,
        status=Status.DECIDED,
        decided_by="isl",
        where="l2p.py:240",
        owner="reconstruct",
    )
    for width, count in ((72, 4), (100, 3)):
        lines = Ledger([short, post]).render(width).splitlines()
        at = lines[0].index("STATEMENT")
        assert lines[2][at:] == "short holds"
        rows = lines[3:-2]
        assert rows[0].startswith("decided  isl  l2p.py:240  reconstruct")
        assert len(rows) == count
        assert all(not line[:at].strip() for line in rows[1:])
        assert " ".join(line[at:].strip() for line in rows) == POSTCONDITION
        assert max(len(line) - at for line in rows) <= width
        assert lines[-1] == "2 facts: 2 decided"
    # the default is 100 characters
    assert Ledger([short, post]).render() == Ledger([short, post]).render(100)


def test_a_long_statement_breaks_between_claims_and_not_inside_a_guard() -> None:
    """The ``and`` that joins two claims starts a line; a guard's own ``and`` does not.

    A break inside brackets is indented a step for each bracket, so that
    the second line of a claim reads as that claim's; a guard too long for
    a line is broken before its ``where``, so the guard stays whole.
    """
    from lanky.ledger import wrap

    assert wrap(POSTCONDITION, 72) == [
        "(forall i in Fin(nb), a in Nat, b in Nat where a < 2 and a + b <= 10.",
        "    R[i, a, b] == C[i, a, b])",
        "  and (forall i in Fin(nb), a in Nat, b in Nat where a + b + 2 <= 10.",
        "    R[i, a + 2, b] == -R[i, a, b + 2])",
    ]
    hypothesis = (
        "| stored: forall i in Fin(n), a in Nat, b in Nat where a < 2 and a + b <= p. "
        "c[i, a, b] == D[i, a, b]"
    )
    assert wrap(hypothesis, 72, indent="    ") == [
        "| stored: forall i in Fin(n), a in Nat, b in Nat",
        "    where a < 2 and a + b <= p. c[i, a, b] == D[i, a, b]",
    ]
    # a word longer than the line is kept whole, on a line of its own
    assert wrap("a " + "b" * 20 + " c", 10) == ["a", "  " + "b" * 20, "  c"]


def test_a_theorem_too_long_for_one_line_is_printed_a_part_to_a_line() -> None:
    """Its variables, each hypothesis under its parameter's name, then ``|-`` and the goal.

    On one line the hypotheses are joined by ``, ``, as the binders of a
    ``forall`` are, and where one ends cannot be told. The parts come from
    the ``sequent`` the theorem's fact carries; one that fits is one line.
    """
    from lanky.ledger import statement_lines

    sequent = {
        "variables": "D : Fn[Nat, Nat, Real], R : Fn[Nat, Nat, Real]",
        "hypotheses": [
            ["pde", "forall a in Nat, b in Nat. D[a + 2, b] + D[a, b + 2] == 0"],
            ["stored", "forall a in Nat, b in Nat where a < 2. R[a, b] == D[a, b]"],
        ],
        "goal": "forall a in Nat, b in Nat. R[a, b] == D[a, b]",
    }
    fact = Fact(
        id="compressed_taylor",
        kind="theorem",
        statement=(
            f"{sequent['variables']} | "
            + ", ".join(text for _, text in sequent["hypotheses"])
            + f" |- {sequent['goal']}"
        ),
        owner="compressed_taylor",
        provenance={"sequent": sequent},
    )
    assert statement_lines(fact) == [
        "D : Fn[Nat, Nat, Real], R : Fn[Nat, Nat, Real]",
        "| pde: forall a in Nat, b in Nat. D[a + 2, b] + D[a, b + 2] == 0",
        "| stored: forall a in Nat, b in Nat where a < 2. R[a, b] == D[a, b]",
        "|- forall a in Nat, b in Nat. R[a, b] == D[a, b]",
    ]
    assert statement_lines(fact, width=400) == [fact.statement]


def test_in_a_terminal_the_statement_column_takes_what_the_others_leave() -> None:
    """``columns`` sizes the statement column to the terminal, within 40 and 100 characters."""
    from lanky.ledger import NARROWEST, WIDEST

    post = Fact(
        id="post",
        kind="postcondition",
        statement=POSTCONDITION,
        status=Status.DECIDED,
        decided_by="isl",
        where="l2p.py:240",
        owner="reconstruct",
    )
    ledger = Ledger([post])
    others = len("decided  isl  l2p.py:240  reconstruct  ")

    def widest(columns: int | None) -> int:
        rows = ledger.render(columns=columns).splitlines()[2:-2]
        return max(len(line) for line in rows) - others

    assert widest(None) <= 100
    assert widest(others + 80) <= 80 < widest(others + 400) <= WIDEST
    assert widest(others + 10) <= NARROWEST
    assert len(ledger.render(columns=others + 400).splitlines()) < len(
        ledger.render(columns=others + 10).splitlines()
    )


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


def test_a_fact_a_heuristic_decided_is_marked_beside_its_status() -> None:
    """``decided (heuristic)`` is not read as a decision procedure's ``decided``."""
    ledger = Ledger(
        [
            Fact(
                id="a",
                kind="theorem",
                statement="x == x",
                status=Status.DECIDED,
                decided_by="simplifier",
                provenance={"trust_class": "heuristic"},
            ),
            Fact(
                id="b",
                kind="theorem",
                statement="y == y",
                status=Status.DECIDED,
                decided_by="isl",
                provenance={"trust_class": "decision-procedure"},
            ),
        ]
    )
    assert ledger["a"].is_heuristic
    assert not ledger["b"].is_heuristic
    rows = ledger.render().splitlines()
    assert rows[2].startswith("decided (heuristic)  simplifier")
    assert rows[3].startswith("decided              isl")
    assert rows[-1] == "2 facts: 2 decided"


def test_what_rests_on_a_heuristics_answer_is_worth_a_heuristics_answer() -> None:
    """Of two facts with one status, the one a heuristic settled is the weaker.

    A proof or a decision procedure's ``decided`` that rests on a lemma a
    heuristic decided is worth ``decided (heuristic)``, which the
    ``EFFECTIVE`` column and the JSON say, though the decision procedure's
    status is the same as the lemma's. Anything weaker than ``decided`` is
    worth what it is, and a heuristic's answer that rests on nothing is worth
    its own status, marked as it is.
    """
    heuristic = {"trust_class": "heuristic"}
    ledger = Ledger(
        [
            make_fact("lemma", Status.DECIDED, decided_by="simplifier", provenance=heuristic),
            make_fact("proof", Status.PROVED, decided_by="lean", rests_on=("lemma",)),
            make_fact("decision", Status.DECIDED, decided_by="isl", rests_on=("lemma",)),
            make_fact("sample", Status.TESTED, decided_by="property-test", rests_on=("lemma",)),
            make_fact("alone", Status.DECIDED, decided_by="isl"),
        ]
    )
    assert ledger.support("lemma") == Support(Status.DECIDED, (), heuristic=True)
    assert ledger.support("proof") == Support(Status.DECIDED, (), heuristic=True)
    assert ledger.support("decision") == Support(Status.DECIDED, (), heuristic=True)
    assert ledger.support("sample") == Support(Status.TESTED, ())
    assert ledger.support("alone") == Support(Status.DECIDED, ())
    rows = ledger.render().splitlines()
    assert rows[0].split()[:3] == ["STATUS", "EFFECTIVE", "BY"]
    # both columns are as wide as "decided (heuristic)", and two spaces apart
    cells = [(row[:19].rstrip(), row[21:40].rstrip()) for row in rows[2:7]]
    assert cells == [
        ("decided (heuristic)", "decided (heuristic)"),
        ("proved", "decided (heuristic)"),
        ("decided", "decided (heuristic)"),
        ("tested", "tested"),
        ("decided", "decided"),
    ]
    data = json.loads(ledger.to_json())
    assert [(row["id"], row["effective"], row["effective_heuristic"]) for row in data] == [
        ("lemma", "decided", True),
        ("proof", "decided", True),
        ("decision", "decided", True),
        ("sample", "tested", False),
        ("alone", "decided", False),
    ]


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
            "effective_heuristic": False,
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
    """A claim of another file, or an id written wrong: nothing here established it."""
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


def test_a_fact_added_later_can_close_a_circle() -> None:
    """What is circular is read again once the ledger changes."""
    ledger = Ledger([make_fact("a", Status.PROVED, rests_on=("b",))])
    assert ledger.support("a") == Support(effective=Status.ASSUMED, under=("b",))
    ledger.add(make_fact("b", Status.PROVED))
    assert ledger.support("a") == Support(effective=Status.PROVED, under=())
    ledger.add(make_fact("b", Status.PROVED, rests_on=("a",)))
    assert ledger.support("a") == Support(effective=Status.ASSUMED, under=("b", "a"))


def test_a_long_chain_and_a_long_circle_are_read_quickly() -> None:
    """1200 facts, each resting on the next: every row, in a second or two.

    Whether a fact is on a circle used to be asked by walking the graph from
    it, once per fact per fact, and ``to_dicts`` over a chain of 1500 took
    minutes. It is now found once for the ledger. The walk keeps its own
    stack, so a chain longer than Python's recursion limit is no trouble
    either. The bound is loose, for a slow machine; the old reading took
    minutes here.
    """
    import time

    length = 1200
    chain = [
        make_fact(f"f{i}", Status.PROVED, rests_on=(f"f{i + 1}",)) for i in range(length - 1)
    ]
    chain.append(make_fact(f"f{length - 1}", Status.TESTED))
    circle = [
        make_fact(f"c{i}", Status.PROVED, rests_on=(f"c{(i + 1) % 500}",)) for i in range(500)
    ]
    start = time.perf_counter()
    chained = Ledger(chain)
    rows = chained.to_dicts()
    chained.render()
    circled = Ledger(circle).to_dicts()
    assert time.perf_counter() - start < 30
    assert {row["effective"] for row in rows} == {"tested"}
    assert all(row["under"] == [] for row in rows)
    assert {row["effective"] for row in circled} == {"assumed"}
    assert circled[0]["under"][:2] == ["c1", "c2"]
    assert len(circled[0]["under"]) == 500


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


def test_a_plugin_names_a_fact_its_kernel_owns_with_many_by_its_label() -> None:
    """A schedule's assumption is one of many facts of its kernel: its label names it.

    Its id spells the whole schedule it belongs to, which made the status
    column of every cast that rests on it as wide as that id.
    """
    assumption = make_fact(
        "assumption:demo.k@4:[c].assume('n % 4 == 0')",
        owner="k",
        provenance={"label": "assume('n % 4 == 0')"},
    )
    ledger = Ledger(
        [
            assumption,
            make_fact(
                "k:split",
                Status.DECIDED,
                decided_by="isl",
                owner="k",
                rests_on=(assumption.id,),
            ),
            make_fact("k:other", Status.DECIDED, decided_by="isl", owner="k"),
        ]
    )
    lines = ledger.render().splitlines()
    assert lines[3].startswith("decided under assume('n % 4 == 0')  assumed")


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
