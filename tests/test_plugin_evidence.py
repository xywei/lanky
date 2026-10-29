"""A compiler-free plugin fixture exercising the existing evidence contract."""

from dataclasses import dataclass, replace

import pytest

from lanky.check import establish
from lanky.ledger import Fact, Ledger, Status
from lanky.plugins import registry


@dataclass(frozen=True)
class Record:
    input_id: str = "input-v1"
    output_id: str = "output-v1"
    schema: int = 1
    holds: bool = True


class Checker:
    name = "fixture-correspondence"

    def trust_class(self):
        return "decision-procedure"

    def can_establish(self, fact):
        return isinstance(fact.term, Record)

    def establish(self, fact):
        record = fact.term
        if record.schema != 1:
            return fact.with_status(fact.status, declined="unsupported evidence schema")
        if (record.input_id, record.output_id) != ("input-v1", "output-v1"):
            return fact.with_status(Status.REFUTED, self.name, reason="stale evidence")
        return fact.with_status(
            Status.DECIDED if record.holds else Status.REFUTED,
            self.name,
            evidence_scope="fixture correspondence",
            checker_version=1,
        )


def claim():
    return Fact(
        "correspondence",
        "plugin-evidence",
        "record is valid correspondence evidence for the selected input and output",
        term=Record(),
        rests_on=("reading", "contract"),
    )


@pytest.fixture
def checker(monkeypatch):
    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [Checker()])


@pytest.mark.parametrize(
    "reading,expected",
    [
        (Status.TESTED, Status.TESTED),
        (Status.ASSUMED, Status.ASSUMED),
        (Status.REFUTED, Status.REFUTED),
        (None, Status.ASSUMED),
    ],
)
def test_decisions_do_not_hide_their_reading_or_missing_prerequisites(checker, reading, expected):
    result = establish(claim())
    assert result.status is Status.DECIDED
    assert result.provenance["trust_class"] == "decision-procedure"
    facts = [result, Fact("contract", "contract", "arguments valid", status=Status.DECIDED)]
    if reading is not None:
        facts.append(Fact("reading", "faithful", "source reading", status=reading))
    ledger = Ledger(facts)
    assert ledger.support(result).effective is expected
    row = next(row for row in ledger.to_dicts() if row["id"] == result.id)
    assert row["effective"] == expected.value
    assert row["provenance"]["evidence_scope"] == "fixture correspondence"


def test_stale_and_unsupported_evidence_are_distinct(checker):
    stale = establish(replace(claim(), term=Record(output_id="changed")))
    assert stale.status is Status.REFUTED
    unsupported = establish(replace(claim(), term=Record(schema=2)))
    assert unsupported.status is Status.ASSUMED
    assert "unsupported" in str(unsupported.provenance["declined"])
    rows = [Ledger([fact]).to_dicts()[0] for fact in (stale, unsupported)]
    assert rows[0]["provenance"]["reason"] == "stale evidence"
    assert "unsupported" in str(rows[1]["provenance"]["declined"])
    assert establish(claim()).status is not Status.CERTIFIED


@pytest.mark.parametrize(
    "error", [TimeoutError("budget exhausted"), RuntimeError("checker failed")]
)
def test_checker_errors_never_become_refutations(checker, monkeypatch, error):
    class Broken(Checker):
        def establish(self, fact):
            raise error

    monkeypatch.setattr(registry, "oracles", [Broken()])
    result = establish(claim())
    assert result.status is Status.ASSUMED
    assert type(error).__name__ in str(result.provenance["raised"])
    row = Ledger([result]).to_dicts()[0]
    assert type(error).__name__ in str(row["provenance"]["raised"])


def test_a_stronger_result_keeps_scope_and_effective_strength(checker, monkeypatch):
    # A stub tests dispatch, not a real Lean proof. The plugin owns statement
    # reconstruction; lanky preserves the existing evidence and prerequisites.
    class Prover(Checker):
        name = "fixture-kernel"

        def trust_class(self):
            return "kernel"

        def establish(self, fact):
            return fact.with_status(Status.PROVED, self.name, proof_scope="same predicate")

    decided = establish(claim())
    monkeypatch.setattr(registry, "oracles", [Prover()])
    proved = establish(decided)
    assert proved.status is Status.PROVED
    assert proved.provenance["evidence_scope"] == "fixture correspondence"
    assert proved.rests_on == decided.rests_on
    ledger = Ledger([proved, Fact("reading", "faithful", "reading", status=Status.TESTED)])
    assert ledger.support(proved).effective is Status.ASSUMED  # missing contract
