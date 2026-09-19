"""Checking a file: import it, collect facts, run oracles, exit on a refutation."""

from __future__ import annotations

import json

from lanky import cli
from lanky.check import check_path, oracle_lines
from lanky.ledger import Status

FILE = '''
"""Two claims, one of them false."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def true_claim(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Gauss."""


@theorem
def false_claim(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
    """False as soon as n is at least two."""
'''


def write_file(tmp_path, text: str = FILE) -> str:
    path = tmp_path / "claims.py"
    path.write_text(text, encoding="utf-8")
    return str(path)


def test_check_path_yields_a_ledger(tmp_path) -> None:
    ledger = check_path(write_file(tmp_path))
    assert [fact.owner for fact in ledger] == ["true_claim", "false_claim"]

    tested = ledger.by_status(Status.TESTED)
    assert [fact.owner for fact in tested] == ["true_claim"]
    assert tested[0].decided_by == "property-test"
    assert tested[0].provenance["valid"] > 0

    refuted = ledger.by_status(Status.REFUTED)
    assert [fact.owner for fact in refuted] == ["false_claim"]
    assert refuted[0].decided_by == "property-test"
    assert "n" in refuted[0].provenance["counterexample"]
    assert refuted[0].where.startswith("claims.py:")


def test_checking_twice_keeps_the_ledgers_apart(tmp_path) -> None:
    path = write_file(tmp_path)
    assert len(check_path(path)) == 2
    assert len(check_path(path)) == 2


def test_oracle_lines_name_the_trust_classes() -> None:
    lines = oracle_lines()
    assert any(line.startswith("lean (kernel):") for line in lines)
    assert any(line.startswith("property-test (test): available") for line in lines)


def test_cli_exits_one_on_a_refutation(tmp_path, capsys) -> None:
    out_json = tmp_path / "ledger.json"
    code = cli.main(["check", write_file(tmp_path), "--json", str(out_json)])
    assert code == 1
    printed = capsys.readouterr().out
    assert "REFUTED false_claim" in printed
    assert "counterexample" in printed
    data = json.loads(out_json.read_text(encoding="utf-8"))
    assert {entry["status"] for entry in data} == {"tested", "refuted"}


def test_cli_exits_zero_when_nothing_is_refuted(tmp_path, capsys) -> None:
    text = FILE.split("@theorem\ndef false_claim")[0]
    code = cli.main(["check", write_file(tmp_path, text), "--verbose"])
    assert code == 0
    printed = capsys.readouterr().out
    assert "property-test (test): available" in printed
    assert "1 facts: 1 tested" in printed


def test_cli_without_a_verb_prints_help(capsys) -> None:
    assert cli.main([]) == 0
    assert "check" in capsys.readouterr().out


def test_checking_a_file_does_not_accumulate_its_objects(tmp_path) -> None:
    """A process that checks many files must not keep every one of them.

    The decorators register into one process-wide registry, so a check has to
    scope itself to the objects its own import made and then let them go.
    """
    from lanky.plugins import registry

    path = write_file(tmp_path)
    check_path(path)
    after_one = len(registry.objects)
    check_path(path)
    assert len(registry.objects) == after_one


def test_an_imported_file_does_not_stay_in_sys_modules(tmp_path) -> None:
    """Two files with one basename would otherwise share a module entry."""
    import sys

    check_path(write_file(tmp_path))
    assert not [name for name in sys.modules if name.startswith("lanky_checked_")]


def test_a_semantics_gap_is_recorded_and_cross_checked(tmp_path, monkeypatch) -> None:
    """``n - 1 >= 0`` is true in Lean and false in Python at ``n = 0``.

    Whatever establishes it, the ledger has to say that the statement has two
    readings. With no Lean here the property tester refutes it outright; with
    Lean it is proved and the disagreement is recorded instead. Both are
    honest, and neither is silent.
    """
    from lanky.semantics import NAT_SUBTRACTION

    path = tmp_path / "gap.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def truncated(n: Nat) -> n - 1 >= 0:\n"
        '    """Nat subtraction truncates in Lean and goes negative in Python."""\n',
        encoding="utf-8",
    )
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert NAT_SUBTRACTION in fact.provenance["semantics"]
    if fact.status is Status.REFUTED:
        assert fact.provenance["counterexample"] == {"n": 0}
    else:
        assert fact.status is Status.PROVED
        assert fact.provenance["semantics_counterexample"] == {"n": 0}


def test_a_file_that_does_not_exist_is_a_mistake_in_the_command(capsys) -> None:
    assert cli.main(["check", "/no/such/file.py"]) == 2
    assert "no such file" in capsys.readouterr().out


def test_a_file_that_raises_on_import_fails_the_check(tmp_path, capsys) -> None:
    """A file that does not import is a broken claim, not a clean ledger."""
    from lanky.plugins import registry

    path = tmp_path / "boom.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def fine(n: Nat) -> n + 0 == n:\n"
        '    """Registered before the file blows up."""\n\n\n'
        "raise RuntimeError('boom')\n",
        encoding="utf-8",
    )
    before = len(registry.objects)
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" in printed
    assert "RuntimeError: boom" in printed
    # whatever the file managed to register is released again
    assert len(registry.objects) == before
