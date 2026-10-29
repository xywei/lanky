"""Display names for unresolved claims do not supply evidence for them."""

from lanky.ledger import Fact, Ledger, Status


def dependent(*ids):
    return Fact("result", "agreement", "result agrees", status=Status.TESTED, rests_on=ids)


def test_a_missing_claim_is_readable_but_stays_unresolved_in_support_and_json():
    key = "claim:layer_potential.conjugate_form@236"
    fact = dependent(key)
    ledger = Ledger([fact])
    assert "tested under conjugate_form" in ledger.render()
    assert ledger.support(fact).effective is Status.ASSUMED
    assert ledger.support(fact).under == (key,)
    assert ledger.to_dicts()[0]["under"] == [key]
    assert ledger.to_dicts()[0]["effective"] == "assumed"


def test_collision_uses_qualified_name_then_definition_line():
    ledger = Ledger([dependent("claim:a.lemma@1", "claim:b.lemma@2")])
    assert "under a.lemma, b.lemma" in ledger.render()
    ledger = Ledger([dependent("claim:a.lemma@1", "claim:a.lemma@2")])
    assert "under a.lemma@1, a.lemma@2" in ledger.render()


def test_missing_name_does_not_impersonate_a_held_fact():
    ledger = Ledger(
        [
            dependent("claim:a.lemma@1", "held"),
            Fact("held", "claim", "something else", owner="lemma"),
        ]
    )
    assert "under a.lemma, lemma" in ledger.render()


def test_unknown_and_malformed_ids_are_not_parsed_as_claims():
    ids = ("requirement:travel.flat@189:weigh:element:off", "claim:x@no", "claim:x@1:part")
    ledger = Ledger([dependent(*ids)])
    for key in ids:
        assert key in ledger.render()


def test_adding_the_real_fact_changes_strength_through_evidence_not_the_label():
    key = "claim:helpers.lemma@12"
    fact = dependent(key)
    ledger = Ledger([fact])
    assert ledger.support(fact).effective is Status.ASSUMED
    ledger.add(Fact(key, "claim", "lemma", owner="lemma", status=Status.PROVED))
    assert ledger.support(fact).effective is Status.TESTED
    assert ledger.to_dicts()[0]["under"] == []


def test_a_missing_plugin_id_also_reserves_its_display_name():
    ledger = Ledger([dependent("claim:helpers.lemma@12", "lemma")])
    assert "under helpers.lemma, lemma" in ledger.render()
