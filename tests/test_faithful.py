"""The faithfulness fact: a claim's term computes what its annotations compute (#91).

lanky reads an annotation by running its Python on terms, and a Python
operation that answers from the term object rather than through its overloads
gives one answer at every value: the term then says something other than the
claim, and an oracle proves the term. These tests hold the check that closes
the class to #91's acceptance: every example of #79, #80 and #88 is refuted by
the claim's ``faithful`` fact, with a point, and offered to no oracle that
decides or proves; so are the cases of #73, #63 and #70 with their own
refusals switched off; a true claim is proved as before, under a tested
reading; and what the check cannot run leaves the fact ``assumed``, saying why.
Each test fails on ``main``, which has no such fact.
"""

from __future__ import annotations

import json

import pytest

from conftest import claims, plugin_arguments
from lanky import cli, terms
from lanky.check import check_path, establish
from lanky.faithful import CORNERS, DrawnFamily
from lanky.ledger import Fact, Status
from lanky.oracles.test import TestOracle
from lanky.plugins import registry
from lanky.terms import SymbolicBoolError

HEADER = """\
from __future__ import annotations

import builtins
import collections

from lanky import theorem
from lanky.prelude import Fin, Fn, Nat, Real, Sort
"""


class Proves:
    """A kernel-class stand-in for Lean that proves every claim it is shown, and says which.

    It is what Lean did with every misread claim below on ``main``: the term
    the reading left was true, so ``omega``, ``simp`` or ``decide`` closed it.
    """

    name = "stub-kernel"

    def __init__(self) -> None:
        self.shown: list[str] = []

    def trust_class(self) -> str:
        return "kernel"

    def can_establish(self, fact: Fact, /) -> bool:
        return fact.term is not None

    def establish(self, fact: Fact, /) -> Fact:
        self.shown.append(fact.owner)
        return fact.with_status(Status.PROVED, self.name, tactic="stub")


@pytest.fixture
def prover(monkeypatch) -> Proves:
    """The stand-in prover and the property tester, as the only oracles of the test."""
    import lanky.oracles  # noqa: F401 - registers the built-in oracles

    registry.load_entry_points()
    stand_in = Proves()
    monkeypatch.setattr(registry, "oracles", [stand_in, TestOracle()])
    return stand_in


def _write(tmp_path, body: str, name: str = "claims.py") -> str:
    path = tmp_path / name
    path.write_text(HEADER + body, encoding="utf-8")
    return str(path)


def _pairs(ledger) -> dict[str, tuple[Fact, Fact]]:
    """Each claim of a ledger and its reading, by owner."""
    facts = list(ledger)
    return {
        fact.owner: (fact, next(r for r in facts if r.is_reading and r.owner == fact.owner))
        for fact in facts
        if not fact.is_reading
    }


# {{{ the examples of #79, #80 and #88


#: Every example in #79, #80 and #88 and their comments, each false at the
#: point the check reports, and each proved by Lean on ``main``.
MISREAD = '''

def table(i):
    return {0: 1}.get(i, 0)


def flag(x):
    return 1 if x else 0


def digit(x):
    return {"0": 1}.get(f"{x}", 0)


def big(i):
    return 1 if isinstance(i, int) and i > 0 else 0


@theorem
def types_differ(n: Nat) -> (Fin[n] != Fin[3]) | (n == 4):
    """#79: False at n = 3."""


@theorem
def keyed_type(n: Nat) -> {Fin[3]: 1}.get(Fin[n], 0) == 0:
    """#79: False at n = 3."""


@theorem
def families_differ(n: Nat) -> (Fn[Fin[n], Nat] != Fn[Fin[3], Nat]) | (n == 4):
    """#79's FnType: False at n = 3."""


@theorem
def refinements_differ(n: Nat) -> ((Nat & (n > 2)) != (Nat & (3 > 2))) | (n == 4):
    """#79's Refined: False at n = 3 and at n = 5."""


@theorem
def sums_differ(n: Nat) -> ((Fin[n] + Fin[1]) != (Fin[3] + Fin[1])) | (n == 4):
    """#79's SumType: False at n = 3."""


@theorem
def through_helper(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == table(i) for i in Fin[n]):
    """#80: False at i = 0."""


@theorem
def counted(n: Nat, f: Fn[Fin[n], Nat]) -> all(
    f(i) * 0 == collections.Counter([i, 0])[0] - 1 for i in Fin[n]
):
    """#80, first comment: False at i = 0, where 0 is counted twice."""


@theorem
def chained(n: Nat, f: Fn[Fin[n], Nat]) -> all(
    f(i) * 0 == collections.ChainMap({0: 1}).get(i, 0) for i in Fin[n]
):
    """#80, first comment: False at i = 0."""


@theorem
def flagged(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 + flag(i) == 1 for i in Fin[n]):
    """#80, second comment: a number's truth value in a helper; false at i = 0."""


@theorem
def digits(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == digit(i) for i in Fin[n]):
    """#80, second comment: a term's text in a helper; false at i = 0."""


@theorem
def identity(n: Nat, f: Fn[Fin[n], Nat]) -> all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n]):
    """#88: False at i = 0."""


@theorem
def named(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == {"i": 0}.get(i.name, 1) for i in Fin[n]):
    """#88: a number has no name."""


@theorem
def typed(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == big(i) for i in Fin[n]):
    """A helper that asks a value for its type, which no rule refuses; false at i = 1."""
'''

#: The point each claim is refuted at: the first corner draw at which the
#: annotation and its term disagree, small values first.
FIRST_POINT = {
    "types_differ": {"n": 3},
    "keyed_type": {"n": 3},
    "families_differ": {"n": 3},
    "refinements_differ": {"n": 5},
    "sums_differ": {"n": 3},
    "through_helper": {"n": 1, "f": [1]},
    "counted": {"n": 1, "f": [1]},
    "chained": {"n": 1, "f": [1]},
    "flagged": {"n": 1, "f": [1]},
    "digits": {"n": 1, "f": [1]},
    "identity": {"n": 1, "f": [1]},
    "named": {"n": 1, "f": [1]},
    "typed": {"n": 5, "f": [5, 5, 5, 5, 5]},
}


def test_every_example_of_79_80_and_88_is_refuted_and_never_proved(
    prover, tmp_path, capsys
) -> None:
    """Each reading is refuted at a point, and the claim is offered to no oracle.

    On ``main`` the stand-in prover, as Lean, proved every one of them: the
    term the reading left (``True or n == 4``, ``f(i)*0 == 0``, ``f(i)*0 ==
    1 or True``) is true. The claim now stays ``assumed``, resting on its
    refuted reading, so it is worth ``refuted``, and ``lanky check`` exits 1
    with the point, the annotation as written and both answers under the
    table.
    """
    path = _write(tmp_path, MISREAD)
    ledger = check_path(path)
    pairs = _pairs(ledger)
    assert list(pairs) == list(FIRST_POINT)
    assert prover.shown == []
    for owner, (claim, reading) in pairs.items():
        assert (reading.kind, reading.status, reading.decided_by) == (
            "faithful",
            Status.REFUTED,
            "python",
        ), (owner, reading.provenance)
        assert reading.provenance["counterexample"] == FIRST_POINT[owner], owner
        assert reading.provenance["witness"].startswith("the goal, "), owner
        assert reading.id == claim.id.replace("theorem:", "faithful:", 1)
        assert (claim.status, claim.decided_by) == (Status.ASSUMED, None), owner
        assert claim.provenance["unfaithful"] == reading.provenance["reason"]
        assert claim.rests_on == (reading.id,)
        assert ledger.support(claim).effective is Status.REFUTED
    identity = pairs["identity"][1].provenance
    assert identity["witness"] == (
        "the goal, all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n])"
    )
    assert identity["python_answer"] == "computes False"
    assert identity["term_answer"] == "computes True"
    assert "its term, forall i in Fin(n). f(i)*0 == 1 or True, computes True" in (
        identity["reason"]
    )
    named = pairs["named"][1].provenance
    assert named["python_answer"].startswith("raises AttributeError")

    assert cli.main(["check", path]) == 1
    printed = capsys.readouterr().out
    assert printed.count("REFUTED ") == len(FIRST_POINT)
    block = printed.split("REFUTED identity at claims.py:", 1)[1].splitlines()
    assert block[1:3] == [
        "  counterexample: {'n': 1, 'f': [1]}",
        "  witness: the goal, all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n])",
    ]
    assert block[3].startswith("  the goal, run again as Python at these values, computes False")
    row = next(
        line for line in printed.splitlines() if line.startswith("assumed under faithful:identity")
    )
    assert row.split()[3] == "refuted"


# }}}


# {{{ the earlier rules, switched off


def _always_a_guard(frame, code, prop=None) -> str:
    return "guard"


#: The cases of #73, #63 and #70, with the rule that refuses each on ``main``,
#: what the reading made of it with the rule switched off, and the point at
#: which the check finds the term says something else.
SWITCHED_OFF = [
    pytest.param(
        "_refuse_hashing",
        "def looked_up(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all(f(i) * 0 == {0: 1}.get(i, 0) for i in Fin[n])",
        {"n": 1, "f": [1]},
        id="73-dict",
    ),
    pytest.param(
        "_refuse_hashing",
        "def member(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all((f(i) * 0 == 1) | (i in {0, 1}) for i in Fin[n])",
        {"n": 1, "f": [1]},
        id="73-set",
    ),
    pytest.param(
        "_refuse_text",
        "def spelled(n: Nat, f: Fn[Fin[n], Nat]) -> "
        'all(f(i) * 0 == {"0": 1}.get(f"{i}", 0) for i in Fin[n])',
        {"n": 1, "f": [1]},
        id="73-text",
    ),
    pytest.param(
        "_refuse_truth",
        "def truthy(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all(f(i) * 0 + (1 if i else 0) == 1 for i in Fin[n])",
        {"n": 1, "f": [1]},
        id="73-truth",
    ),
    pytest.param(
        "_asking_context",
        "def smallest(n: Nat) -> all(builtins.min(i, j) == j for i in Fin[n] for j in Fin[n])",
        {"n": 5},
        id="63-min",
    ),
    pytest.param(
        "_asking_context",
        "def branch(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all((f(i) if i < 3 else -1) >= 0 for i in Fin[n])",
        {"n": 5, "f": [5, 5, 5, 5, 5]},
        id="70-conditional",
    ),
    pytest.param(
        "_asking_context",
        "def negated(n: Nat, k: Nat) -> ~any(not (i < k) for i in Fin[n])",
        None,
        id="70-not",
    ),
    pytest.param(
        "_asking_context",
        "def pairs(n: Nat, k: Nat) -> all((i, 0) == (k, 0) for i in Fin[n])",
        {"n": 1, "k": 1},
        id="70-tuples",
    ),
]


@pytest.mark.parametrize(("rule", "claim", "point"), SWITCHED_OFF)
def test_the_earlier_rules_switched_off_are_refuted_by_the_check(
    prover, monkeypatch, tmp_path, rule, claim, point
) -> None:
    """With its own refusal switched off, each case is refuted by its reading.

    The refusals of #73 (a term's hash, text and truth value as a number in
    the annotation's code), #63 (a truth value a builtin asks for, read as a
    guard) and #70 (a conditional, ``not`` and tuples compared, read as a
    guard) each closed one case. Switched off, the reading makes a term that
    says something else, which the stand-in prover proves on ``main``; the
    check refutes it at a point, as a test of the general check.
    """
    body = f'\n\n@theorem\n{claim}:\n    """Misread without its rule."""\n'
    path = _write(tmp_path, body)
    with pytest.raises((TypeError, SymbolicBoolError)):
        check_path(path)
    replacement = _always_a_guard if rule == "_asking_context" else (lambda term, frame: None)
    monkeypatch.setattr(terms, rule, replacement)
    ledger = check_path(_write(tmp_path, body, "switched_off.py"))
    ((claim_fact, reading),) = _pairs(ledger).values()
    assert reading.status is Status.REFUTED, reading.provenance
    found = reading.provenance["counterexample"]
    if point is None:
        # every corner draw has n == k, where ``not (i < k)`` holds nowhere,
        # and the first draw past them with n > k is the point
        assert found["n"] > found["k"], found
    else:
        assert found == point
    assert claim_fact.status is Status.ASSUMED
    assert prover.shown == []


# }}}


# {{{ true claims, as before


TRUE = '''

@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Gauss."""


@theorem
def scan_monotone(
    n: Nat,
    cnt: Fn[Fin[n], Nat],
    off: Fn[Fin[n + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),
) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
    """The offsets of a scan are monotone."""


@theorem
def guarded(n: Nat, f: Fn[Fin[n], Nat]) -> all((i == 0) | (f(i - 1) >= 0) for i in Fin[n]):
    """Python's | asks f(-1) at i = 0; lanky's disjunction is true there first."""


@theorem
def negation(n: Nat) -> ~(n < 0):
    """~ of a truth value is not, where Python's ~True is -2."""


@theorem
def sampled(k: Nat) -> all(j + k >= j for j in Nat):
    """A quantifier over a sort, run over the same sample on both sides."""


@theorem
def closed() -> 1 + 1 == 2:
    """No variables: one draw, the empty one."""
'''


def test_a_true_claim_is_proved_as_before_under_a_tested_reading(
    prover, tmp_path, capsys
) -> None:
    """Every claim is proved, and rests on its reading, which the draws tested.

    The proof is worth ``tested`` now, in the ``EFFECTIVE`` column: it is a
    proof of the term, and of the claim as far as the term reads the
    annotations, which a sample shows.
    """
    path = _write(tmp_path, TRUE)
    ledger = check_path(path)
    for owner, (claim, reading) in _pairs(ledger).items():
        assert (claim.status, claim.decided_by) == (Status.PROVED, "stub-kernel"), owner
        assert (reading.status, reading.decided_by) == (Status.TESTED, "python"), (
            owner,
            reading.provenance,
        )
        assert claim.rests_on == (reading.id,)
        assert ledger.support(claim).effective is Status.TESTED
        assert reading.provenance["compared"] > 0
        # Python's | and ~ would have had no answer, or another, at these
        assert "open" not in reading.provenance, owner
    assert _pairs(ledger)["gauss"][1].provenance["draws"] >= CORNERS
    assert _pairs(ledger)["closed"][1].provenance["draws"] == 1
    assert cli.main(["check", path, "--json", str(tmp_path / "out.json")]) == 0
    lines = capsys.readouterr().out.splitlines()
    assert lines[0].split()[:3] == ["STATUS", "EFFECTIVE", "BY"]
    assert lines[2].split()[:4] == ["proved", "tested", "stub-kernel", "claims.py:10"]
    assert lines[3].split()[:3] == ["tested", "tested", "python"]
    assert lines[3].endswith("the term computes what the annotations compute")
    rows = json.loads((tmp_path / "out.json").read_text(encoding="utf-8"))
    assert [row["kind"] for row in rows[:2]] == ["theorem", "faithful"]
    assert rows[0]["rests_on"] == [rows[1]["id"]]
    assert rows[0]["effective"] == "tested"


def test_every_example_reads_its_annotations_faithfully(capsys) -> None:
    """Every claim in the examples has its reading tested, but the axioms about boundaries.

    No value of a boundary can be drawn, so the eight axioms of the
    pytential demonstration leave their readings ``assumed``; nothing rests
    on them, since an axiom is assumed on its citation.
    """
    from pathlib import Path

    examples = Path(__file__).resolve().parent.parent / "examples"
    for name in ("gauss.py", "nicomachus.py"):
        ledger = check_path(examples / name)
        readings = [fact for fact in ledger if fact.is_reading]
        assert len(readings) == len(claims(ledger))
        assert all(fact.status is Status.TESTED for fact in readings), name
    ledger = check_path(examples / "pytential_skie.py")
    readings = [fact for fact in ledger if fact.is_reading]
    assert len(readings) == 8
    assert all(fact.status is Status.ASSUMED for fact in readings)
    assert cli.main(["check", str(examples / "pytential_skie.py")]) == 0
    # nothing rests on them, so they add no DECLINED line
    assert "DECLINED jump_S" not in capsys.readouterr().out


# }}}


# {{{ what is compared, and how


def test_a_sum_rounds_alike_and_nothing_is_put_down_to_rounding(prover, tmp_path) -> None:
    """The term's sum is added by Python's ``sum``, and a close disagreement is one all the same.

    ``sum(0.1 for i in Fin[2 * n])`` is ``1.0`` in Python 3.12 and later at
    ``n = 5``, which compensates as it adds, and ``0.9999999999999999`` added
    one by one. The term's sum is added by Python's ``sum`` over the same
    values, so both readings compare ``1.0 == 1.0`` and agree. Nothing is put
    down to rounding any more: a helper that answers ``x * (1 + 1e-12)`` at a
    number and ``x`` at a term left the term ``1.0*x == x``, whose truth
    differed only where the term compared two numbers within ``1e-9`` of each
    other, which a tolerance did not count, and the CAS decided the term.
    """
    assert sum([0.1] * 10) == 1.0  # compensated, since Python 3.12
    path = _write(
        tmp_path,
        "\nfrom fractions import Fraction\n\n\n"
        "def nudged(x):\n"
        "    if isinstance(x, int | float | Fraction) and x > 0:\n"
        "        return x * (1 + 1e-12)\n"
        "    return x\n\n\n"
        "@theorem\n"
        "def tenths(n: Nat) -> sum(0.1 for i in Fin[2 * n]) == n / 5:\n"
        '    """Rounding decides it, alike on both sides."""\n\n\n'
        "@theorem\n"
        "def halves(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all((f(i) * 0.5 == 1.0) | (i is not 0) for i in Fin[n]):\n"
        '    """A float in the claim does not hide a misreading."""\n\n\n'
        "@theorem\n"
        "def close(x: Real) -> 1.0 * x == nudged(x):\n"
        '    """False wherever x > 0; its term is 1.0*x == x."""\n',
    )
    pairs = _pairs(check_path(path))
    tenths = pairs["tenths"][1]
    assert tenths.status is Status.TESTED, tenths.provenance
    assert "rounding" not in tenths.provenance
    halves = pairs["halves"][1]
    assert halves.status is Status.REFUTED
    assert halves.provenance["counterexample"] == {"n": 1, "f": [1]}
    claim, close = pairs["close"]
    assert close.status is Status.REFUTED, close.provenance
    assert close.provenance["counterexample"]["x"] > 0
    assert close.provenance["python_answer"] == "computes False"
    assert close.provenance["term_answer"] == "computes True"
    assert claim.status is Status.ASSUMED
    assert prover.shown == ["tenths"]


def test_an_exception_on_one_side_only_is_a_disagreement(prover, tmp_path) -> None:
    """Where Python has no answer and the term has one, the reading is refuted.

    At ``i = 0`` Python raises on ``1 // i`` and the rest of the ``|`` is
    ``0 is not 0``, which is false, so the point has no value, and nor does
    the quantifier, which no other point settles; its term, ``... or True``,
    is true there whatever the left side is, and true at every other point
    too. Read as Lean's total division, the annotation is false at ``i = 0``
    (``1 / 0 + 1`` is ``1``), and the term is what Lean would prove. A point
    with no answer is passed over on both sides alike, and an answer on one
    side only is a disagreement.
    """
    path = _write(
        tmp_path,
        "\n\n@theorem\n"
        "def stops(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all((f(i) * 0 == 1 // i + 1) | (i is not 0) for i in Fin[n]):\n"
        '    """Python stops at i = 0; the term reads or True."""\n',
    )
    ((claim, reading),) = _pairs(check_path(path)).values()
    assert reading.status is Status.REFUTED, reading.provenance
    assert reading.provenance["counterexample"] == {"n": 1, "f": [1]}
    assert reading.provenance["python_answer"].startswith("raises ZeroDivisionError")
    assert reading.provenance["term_answer"] == "computes True"
    assert claim.status is Status.ASSUMED
    assert prover.shown == []


def test_both_readings_pass_over_a_point_with_no_answer(tmp_path) -> None:
    """A quantifier and a connective pass over what a point raised, on both sides alike.

    ``all(f(i - 1) <= f(i) for i in Fin[n])`` has no value at ``i = 0``,
    where ``f(-1)`` is outside the domain. Read three-valued, as lanky reads
    it, both readings pass over that point and are false wherever ``f``
    decreases later on, and agree. Python's ``**`` overflows past ``1`` on
    both sides, and both readings of ``|`` pass over it and answer ``x ==
    x``.
    """
    path = _write(
        tmp_path,
        "\n\n@theorem\n"
        "def ordered(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i - 1) <= f(i) for i in Fin[n]):\n"
        '    """No value in Python wherever n >= 1."""\n\n\n'
        "@theorem\n"
        "def overflows(x: Real) -> ((x + 2) ** 2000.0 > 0) | (x == x):\n"
        '    """Python\'s float power overflows past 1, on both sides."""\n',
    )
    pairs = _pairs(check_path(path))
    for owner in ("ordered", "overflows"):
        reading = pairs[owner][1]
        assert reading.status is Status.TESTED, (owner, reading.provenance)
        assert "silent" not in reading.provenance, owner


#: Claims whose term says something else only after a point where both
#: readings have no answer, each false, and the point where the check finds it.
PAST_A_STOP = """

def table(i):
    return {1: 1}.get(i, 0)


@theorem
def divides(n: Nat, f: Fn[Fin[n], Nat]) -> all(
    f(i) * 0 + (1 // i) * 0 == table(i) for i in Fin[n]
):
    \"\"\"False at i = 1, after both readings stop at i = 0.\"\"\"


@theorem
def overflows(n: Nat) -> ((1.0 * n + 2) ** 2000 >= 0) & (n * 0 == table(n)):
    \"\"\"False at n = 1, where 3.0 ** 2000 overflows first.\"\"\"


@theorem
def sums(n: Nat, f: Fn[Fin[n], Nat]) -> sum(f(i - 1) * 0 + table(i) for i in Fin[n]) == 0:
    \"\"\"f(-1) leaves the sum with no value; at i = 1 the term adds 0 where Python adds 1.\"\"\"


@theorem
def named(n: Nat, f: Fn[Fin[n], Nat]) -> all(
    y * 0 + (1 // i) * 0 == table(i) for i in Fin[n] if (y := f(i)) >= 0
):
    \"\"\"As divides, with a name bound by := in the clause.\"\"\"
"""


def test_a_point_after_one_where_both_readings_stop_is_compared(prover, tmp_path) -> None:
    """A point where both readings have no answer does not hide the points after it.

    Python's ``all`` stops at the first point that raises, and a term read as
    ``all`` reads it stopped there too, so ``1 // i`` stopped both readings at
    ``i = 0`` at every draw, and ``table(1)``, misread as ``0``, was never
    compared: the reading was ``tested``, and Lean proved the term ``f(i)*0 +
    (1 // i)*0 == 0`` with ``omega``. Both readings now pass over such a
    point, as lanky reads a quantifier, and reach ``i = 1``. So do ``&`` and
    ``|`` past any exception, an overflow included, and a sum, which has no
    value at such a draw, is compared point by point.
    """
    path = _write(tmp_path, PAST_A_STOP)
    pairs = _pairs(check_path(path))
    assert prover.shown == []
    fives = [5] * 5
    expected = {
        "divides": {"n": 5, "f": fives},
        "overflows": {"n": 1},
        "sums": {"n": 5, "f": fives},
        "named": {"n": 5, "f": fives},
    }
    for owner, point in expected.items():
        claim, reading = pairs[owner]
        assert reading.status is Status.REFUTED, (owner, reading.provenance)
        assert reading.provenance["counterexample"] == point, owner
        assert claim.status is Status.ASSUMED
    divides = pairs["divides"][1].provenance
    assert divides["python_answer"] == "computes False"
    assert divides["term_answer"].startswith("raises ZeroDivisionError")
    sums = pairs["sums"][1].provenance
    assert sums["python_answer"].endswith(
        "its sums with no value coming to [no value (Undecided), 1, 0, 0, 0] at their points"
    )
    assert sums["term_answer"].endswith(
        "its sums with no value coming to [no value (Undecided), 0, 0, 0, 0] at their points"
    )


#: Claims misread only at a value the claim writes, past the corners and the
#: tester's draws, and the point where the check finds each.
WRITTEN_VALUES = """

TABLE = {1000: 1}


def past(i):
    return 1 if isinstance(i, int) and i == 6 else 0


def last(i):
    return 1 if isinstance(i, int) and i == 5 else 0


def far(i):
    return TABLE.get(i, 0)


@theorem
def just_past(n: Nat) -> n * 0 == past(n):
    \"\"\"False at n = 6, one past the largest natural the tester draws.\"\"\"


@theorem
def at_the_end(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == last(i) for i in Fin[n]):
    \"\"\"False at i = 5, past the last point of any Fin the tester draws.\"\"\"


@theorem
def in_a_table(n: Nat) -> n * 0 == far(n):
    \"\"\"False at n = 1000, a key of a module-level table the helper reads.\"\"\"


@theorem
def over_a_sort() -> all(k * 0 == past(k) for k in Nat):
    \"\"\"False at k = 6, which the sample of Nat now holds.\"\"\"
"""


def test_a_value_written_in_the_claim_is_drawn_at(prover, tmp_path) -> None:
    """A helper that answers otherwise only at a value the claim writes is reached there.

    The corners take a natural up to ``5``, and so do the tester's draws, so a
    point of a ``Fin`` is at most ``4``. A misreading only at ``6``, at ``5``
    as a point, or at a key ``1000`` of a table a helper reads, was compared
    nowhere, and the CAS decided ``n*0 == 0``. The integers written in the
    claim, in the helpers it calls and in what they read, and next to them,
    are drawn at, and join the samples of the sorts.
    """
    path = _write(tmp_path, WRITTEN_VALUES)
    pairs = _pairs(check_path(path))
    assert prover.shown == []
    expected = {
        "just_past": ({"n": 6}, "written 6"),
        "at_the_end": ({"n": 6, "f": [6] * 6}, "written 6"),
        "in_a_table": ({"n": 1000}, "written 1000"),
        "over_a_sort": ({}, "corner 0"),
    }
    for owner, (point, draw) in expected.items():
        claim, reading = pairs[owner]
        assert reading.status is Status.REFUTED, (owner, reading.provenance)
        assert (reading.provenance["counterexample"], reading.provenance["draw"]) == (
            point,
            draw,
        ), owner
        assert claim.status is Status.ASSUMED
    assert "{'Nat': [0, 1, 2" in pairs["over_a_sort"][1].provenance["reason"]


def test_a_written_value_keeps_a_draw_small_enough_to_run(tmp_path) -> None:
    """A written value is drawn at only up to a size the check can walk, and to a bound.

    ``2 ** n`` at a written ``2 ** 63`` would not end, so no value past
    :data:`~lanky.faithful.WRITTEN_MAX` is drawn at, while ``63`` and next to
    it are. A size takes a written value only up to the root of
    :data:`~lanky.faithful.SIZE_POINTS` by how deeply the claim nests its
    domains: a misreading at ``1000`` under two nested quantifiers over
    ``Fin[n]`` is past what a draw walks, a limit of the check, and the
    reading is ``tested``. A draw whose walk takes more than
    :data:`~lanky.faithful.WALK_POINTS` points all the same, ``Fin[2 ** n]``
    at a written ``63``, is given up.
    """
    from lanky import faithful

    path = _write(
        tmp_path,
        "\n\ndef thousand(i):\n"
        "    return 1 if isinstance(i, int) and i == 1000 else 0\n\n\n"
        "@theorem\n"
        "def powers(n: Nat, h: n < 63) -> 2 ** n < 2 ** 63:\n"
        '    """Drawn at 62, 63 and 64, and not at 2 ** 63."""\n\n\n'
        "@theorem\n"
        "def bits(n: Nat, h: n < 64) -> all(x < 2 ** n for x in Fin[2 ** n]):\n"
        '    """Drawn at 63, 64 and 65, which are given up as too large to walk."""\n\n\n'
        "@theorem\n"
        "def nested(n: Nat, f: Fn[Fin[n], Nat]) -> all(\n"
        "    all(f(i) * 0 + f(j) * 0 == thousand(i) for j in Fin[n]) for i in Fin[n]\n"
        "):\n"
        '    """Misread at i = 1000, past the size a draw walks here."""\n',
    )
    pairs = _pairs(check_path(path))
    powers = pairs["powers"][1]
    assert powers.status is Status.TESTED, powers.provenance
    assert powers.provenance["draws"] == faithful.CORNERS + 3 + faithful.SAMPLES
    bits = pairs["bits"][1]
    assert bits.status is Status.TESTED, bits.provenance
    assert bits.provenance["unwalked"] == 3
    assert bits.provenance["draws"] == faithful.CORNERS + faithful.SAMPLES
    nested = pairs["nested"][1]
    assert nested.status is Status.TESTED, nested.provenance
    assert nested.provenance["draws"] == faithful.CORNERS + 3 + faithful.SAMPLES


def test_the_if_clauses_are_one_conjunction_in_either_order(tmp_path) -> None:
    """Both readings read the ``if`` clauses as one conjunction of guards, three-valued (#97).

    Python asks the clauses in order and stops at the first with no answer,
    so ``if f(i - 1) > 0 if i > 0`` stops at ``f(-1)`` at ``i = 0``, where the
    term, one conjunction, is false and skips the point. Read as the term
    holds it on both sides, the later clause rejects the point either way.
    So does ``and`` in one clause, which lanky records as two guards. A name
    bound with ``:=`` in a clause is bound where Python binds it, in the
    annotation's globals, where the body reads it.
    """
    path = _write(
        tmp_path,
        "\n\n@theorem\n"
        "def later_guard(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all(f(i) >= 0 for i in Fin[n] if f(i - 1) > 0 if i > 0):\n"
        '    """Python stops at f(-1) at i = 0; the term skips i = 0."""\n\n\n'
        "@theorem\n"
        "def and_guard(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all(f(i) >= 0 for i in Fin[n] if (f(i - 1) > 0) and (i > 0)):\n"
        '    """The same, in one clause."""\n\n\n'
        "@theorem\n"
        "def named_guard(n: Nat, f: Fn[Fin[n], Nat]) -> "
        "all(y >= 0 for i in Fin[n] if (y := f(i)) >= 0):\n"
        '    """A name bound by := in a clause, which the body reads."""\n',
    )
    for owner, (_claim, reading) in _pairs(check_path(path)).items():
        assert reading.status is Status.TESTED, (owner, reading.provenance)


def test_a_helper_reads_the_module_as_it_was_when_the_claim_was_read(tmp_path) -> None:
    """A helper the annotation calls sees the globals of the module as the reading saw them.

    The rerun runs in a copy of the module's globals taken when the claim was
    read, and a function of the module read the live module all the same. A
    ``K`` rebound later made the rerun answer otherwise than the reading, and
    refuted a faithful reading; a table rebound later to one without the key
    the reading missed made the rerun agree with the misread term, and hid
    the misreading. The module's functions are bound to the copy, and to
    what a factory's helper closed over then, which a ``nonlocal`` rebinds
    later just as a module rebinds a global.
    """
    path = _write(
        tmp_path,
        "\n\nK = 0\nTABLE = {0: 1}\n\n\n"
        "def k():\n    return K\n\n\n"
        "def table(i):\n    return TABLE.get(i, 0)\n\n\n"
        "@theorem\n"
        "def constant(n: Nat) -> n * 0 == k():\n"
        '    """Read with K = 0, which the module rebinds after it."""\n\n\n'
        "@theorem\n"
        "def looked_up(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == table(i) for i in Fin[n]):\n"
        '    """Misread at i = 0, where the table read then gives 1."""\n\n\n'
        "def make():\n"
        "    at, held = 0, {0: 1}\n\n"
        "    def closed():\n        return at\n\n"
        "    def held_at(i):\n        return held.get(i, 0)\n\n"
        "    def rebind():\n"
        "        nonlocal at, held\n"
        "        at, held = 1, {}\n\n"
        "    return closed, held_at, rebind\n\n\n"
        "closed, held_at, rebind = make()\n\n\n"
        "@theorem\n"
        "def closed_over(n: Nat) -> n * 0 == closed():\n"
        '    """Read with at = 0, which rebind changes after it."""\n\n\n'
        "@theorem\n"
        "def held(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == held_at(i) for i in Fin[n]):\n"
        '    """Misread at i = 0, where the table closed over then gives 1."""\n\n\n'
        "K = 1\nTABLE = {}\nrebind()\n",
    )
    pairs = _pairs(check_path(path))
    for owner in ("constant", "closed_over"):
        assert pairs[owner][1].status is Status.TESTED, (owner, pairs[owner][1].provenance)
    for owner in ("looked_up", "held"):
        reading = pairs[owner][1]
        assert reading.status is Status.REFUTED, (owner, reading.provenance)
        assert reading.provenance["counterexample"] == {"n": 1, "f": [1]}


def test_a_family_over_a_sort_is_drawn_as_it_is_applied(tmp_path) -> None:
    """The tester cannot tabulate ``Fn[Nat, Nat]``; the check draws it point by point.

    Both readings apply the family at the same points of the sample and see
    the same values there, so a misreading over such a family is refuted,
    and the counterexample shows the values drawn, by point.
    """
    path = _write(
        tmp_path,
        "\n\n@theorem\n"
        "def misread(f: Fn[Nat, Nat]) -> all((f(k) * 0 == 1) | (k is not 0) for k in Nat):\n"
        '    """False at k = 0."""\n\n\n'
        "@theorem\n"
        "def over_naturals(f: Fn[Nat, Fn[Nat, Real]]) -> "
        "all(f(a)(b) - f(a)(b) == 0 for a in Nat for b in Nat):\n"
        '    """A family of families over Nat, read faithfully."""\n',
    )
    pairs = _pairs(check_path(path))
    assert pairs["over_naturals"][1].status is Status.TESTED
    claim, reading = pairs["misread"]
    assert reading.status is Status.REFUTED
    # the corner draw is 0 at every point either reading applied the family at
    drawn = reading.provenance["counterexample"]["f"]
    assert drawn[0] == 0
    assert set(drawn.values()) == {0}
    assert "each sort iterating its sample {'Nat': [0, 1, 2" in reading.provenance["reason"]
    assert claim.status is Status.ASSUMED


def test_a_refutation_over_a_family_of_reals_is_written_as_json(tmp_path) -> None:
    """A family over ``Real`` is applied at fractions, which a JSON object cannot key by."""
    path = _write(
        tmp_path,
        "\n\ndef table(x):\n    return {0: 1}.get(x, 0)\n\n\n"
        "@theorem\n"
        "def halved(f: Fn[Real, Nat]) -> all(f(x / 2) * 0 == table(x) for x in Real):\n"
        '    """Misread: the table gives 0 for a term, and 1 at x = 0."""\n',
    )
    out = tmp_path / "out.json"
    assert cli.main(["check", path, "--json", str(out)]) == 1
    rows = json.loads(out.read_text(encoding="utf-8"))
    (reading,) = [row for row in rows if row["kind"] == "faithful"]
    assert reading["status"] == "refuted"
    assert all(isinstance(key, str) for key in reading["provenance"]["counterexample"]["f"])


def test_a_drawn_family_has_no_value_outside_its_domain() -> None:
    """``f(-1)`` of an ``f`` over ``Nat`` is no point of it, as a table's ``f(n)`` is not."""
    import random

    from lanky.prelude import Nat

    family = DrawnFamily(Nat, Nat, random.Random(0), {}, "f")
    first = family(2)
    assert family(2) == first
    assert list(family.values) == [2]
    with pytest.raises(terms.Undecided, match="f is applied at -1"):
        family(-1)
    with pytest.raises(terms.Undecided):
        family(True)


def test_a_hypothesis_and_a_sort_are_compared_too(tmp_path) -> None:
    """A misread hypothesis or sort is refuted, and the witness names it."""
    path = _write(
        tmp_path,
        "\n\n@theorem\n"
        "def assumes(n: Nat, h: (n is not 0) | (n == 5)) -> n >= 0:\n"
        '    """The hypothesis is read as True."""\n\n\n'
        "@theorem\n"
        "def sized(n: Nat, f: Fn[Fin[3 if n is 0 else n], Nat]) -> n >= 0:\n"
        '    """The sort is read as Fin[n], and is Fin[3] at n = 0."""\n',
    )
    pairs = _pairs(check_path(path))
    assumes = pairs["assumes"][1].provenance
    assert assumes["witness"] == "the hypothesis h, (n is not 0) | (n == 5)"
    assert assumes["counterexample"] == {"n": 0}
    sized = pairs["sized"][1].provenance
    assert sized["witness"] == "the sort of f, Fn[Fin[3 if n is 0 else n], Nat]"
    assert sized["counterexample"] == {"n": 0, "f": []}


def test_a_reading_that_cannot_be_run_is_assumed_and_a_proof_rests_on_it(
    prover, tmp_path, capsys
) -> None:
    """A sort no value can be drawn of leaves the reading ``assumed``, saying why.

    A proof of the claim is then worth ``assumed``, under the reading, which
    is named ``faithful:`` and the claim's owner, and since the proof rests
    on it the reason is printed under the table.
    """
    path = _write(
        tmp_path,
        '\n\nBoundary = Sort("Boundary")\n\n\n'
        "@theorem\n"
        "def opaque(g: Boundary, n: Nat) -> n + 0 == n:\n"
        '    """No boundary can be drawn."""\n',
    )
    ledger = check_path(path)
    ((claim, reading),) = _pairs(ledger).values()
    assert reading.status is Status.ASSUMED
    assert reading.provenance["declined"].startswith("python: no draw could be made")
    assert "no sampler for Sort(name='Boundary'" in reading.provenance["declined"]
    assert claim.status is Status.PROVED
    assert ledger.support(claim).under == (reading.id,)
    assert cli.main(["check", path]) == 0
    printed = capsys.readouterr().out
    assert "proved under faithful:opaque" in printed
    assert f"DECLINED opaque at {reading.where}: {reading.statement}" in printed


def test_an_annotation_python_evaluated_holds_no_source_to_run(tmp_path) -> None:
    """Without ``from __future__ import annotations`` an annotation is a value, not a source."""
    path = tmp_path / "eager.py"
    path.write_text(
        "from lanky import Var, theorem\n"
        "from lanky.prelude import Nat\n\n"
        'x = Var("x")\n\n\n'
        "@theorem\n"
        "def eager(x: Nat) -> x + 0 == x:\n"
        '    """Python built the term itself."""\n',
        encoding="utf-8",
    )
    ((_claim, reading),) = _pairs(check_path(path)).values()
    assert reading.status is Status.ASSUMED
    assert "evaluated by Python when the function was defined" in reading.provenance["declined"]


def test_a_refuted_reading_is_offered_to_no_oracle() -> None:
    """``establish`` returns a claim whose reading is refuted unasked, resting on the reading."""
    claim = Fact(
        id="theorem:m.c@1",
        kind="theorem",
        statement="c",
        term=True,
        provenance={"faithful": "faithful:m.c@1", "unfaithful": "misread"},
    )
    result = establish(claim)
    assert result.status is Status.ASSUMED
    assert result.rests_on == ("faithful:m.c@1",)
    reading = Fact(id="faithful:m.c@1", kind="faithful", statement="r", status=Status.TESTED)
    assert establish(reading) is reading


# }}}


# {{{ under pytest


PYTEST_MODULE = """
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Fn, Nat


@theorem
def identity(n: Nat, f: Fn[Fin[n], Nat]) -> all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n]):
    \"\"\"False at i = 0, and every draw of its term passes.\"\"\"
"""


@pytest.mark.parametrize("found", ["entry point", "named"])
def test_a_theorem_whose_reading_is_refuted_fails_under_pytest(
    pytester, monkeypatch, found
) -> None:
    """The draws would test the term, which holds; the item fails with the point instead."""
    if found == "named":
        monkeypatch.setenv("PYTEST_DISABLE_PLUGIN_AUTOLOAD", "1")
    pytester.makepyfile(test_misread=PYTEST_MODULE)
    result = pytester.runpytest(*plugin_arguments(), "-v")
    result.assert_outcomes(failed=1)
    result.stdout.fnmatch_lines(
        [
            "*the term is not what the annotations compute: the goal, all(*",
            "*counterexample: {'n': 1, 'f': ?1?}*",
        ]
    )
    result.stdout.no_fnmatch_line("*Traceback*")


# }}}


def test_the_quickstart_shows_what_check_prints_for_a_misread_claim(tmp_path, capsys) -> None:
    """The quickstart's ``misread.py`` block is a real run, with Lean and without.

    The file is written from the quickstart's own snippet, after the imports
    ``examples/gauss.py`` has, as the quickstart has a reader write it. No
    oracle is asked about the claim, so the output is the same either way.
    """
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    doc = (root / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    marker = next(index for index, line in enumerate(doc) if "Put this in `misread.py`" in line)
    start = doc.index("```python", marker) + 1
    snippet = "\n".join(doc[start : doc.index("```", start)]) + "\n"
    lines = (root / "examples" / "gauss.py").read_text(encoding="utf-8").splitlines(keepends=True)
    head = next(index for index, line in enumerate(lines) if line.startswith("from __future__"))
    end = next(index for index, line in enumerate(lines) if line.startswith("@theorem"))
    path = tmp_path / "misread.py"
    path.write_text("".join(lines[head:end]) + snippet, encoding="utf-8")
    assert cli.main(["check", str(path)]) == 1
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    at = doc.index("$ uv run lanky check misread.py") + 1
    shown = []
    for line in doc[at:]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line.rstrip())
    assert printed == shown
