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


CLOSED = '''
"""Two claims Python answers on its own."""

from __future__ import annotations

from lanky import theorem


@theorem
def certainly() -> 1 == 1:
    """True, with no variable to draw and no hypothesis to satisfy."""


@theorem
def impossible() -> 1 == 2:
    """False, and nothing in the file says otherwise."""
'''


def test_cli_exits_one_on_a_false_closed_claim(tmp_path, capsys) -> None:
    """The shortest false theorem there is used to leave the check green.

    ``1 == 2`` is answered by Python while the annotation is evaluated, so the
    term is a ``bool``. The property oracle declined anything that was not a
    pymbolic node and Lean has no proof of a false statement, so the row read
    ``assumed`` and ``lanky check`` exited 0.
    """
    path = tmp_path / "closed.py"
    path.write_text(CLOSED, encoding="utf-8")
    code = cli.main(["check", str(path)])
    printed = capsys.readouterr().out
    assert code == 1
    assert "REFUTED impossible" in printed
    # empty on purpose, and printed rather than dropped: no assignment is what
    # makes this statement false
    assert "counterexample: {}" in printed
    assert "constant False" in printed


def test_a_true_closed_claim_is_tested_rather_than_assumed(tmp_path, monkeypatch) -> None:
    """The other side of it, with Lean out of the way so the decider is fixed."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "closed.py"
    path.write_text(CLOSED.split("@theorem\ndef impossible")[0], encoding="utf-8")
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert fact.status is Status.TESTED
    assert fact.decided_by == "property-test"


def test_a_division_by_zero_is_a_gap_the_ledger_records(tmp_path) -> None:
    """``n // 0 == 0`` is a Lean theorem and a Python ZeroDivisionError.

    Whatever establishes it, the note has to be in the provenance and the
    sampled reading has to have been tried: with Lean the fact is proved and
    the cross-check records that the Python reading could not be run, without
    Lean the tester declines the draws and the row stays assumed.
    """
    from lanky.semantics import DIVISION_BY_ZERO

    path = tmp_path / "divzero.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def div_zero(n: Nat) -> n // 0 == 0:\n"
        '    """Total in Lean, undefined in Python."""\n',
        encoding="utf-8",
    )
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert DIVISION_BY_ZERO in fact.provenance["semantics"]
    assert fact.status is not Status.REFUTED
    if fact.status is Status.ASSUMED:
        assert "zero" in fact.provenance["untested"]
    else:
        assert fact.status is Status.PROVED
        assert "zero" in fact.provenance["semantics_undecided"]


def test_an_application_outside_its_domain_is_never_proved(tmp_path, capsys) -> None:
    """A family applied past its own domain must not come back ``proved``.

    Lean sees a total ``Nat -> Nat`` once the family is erased, so the claim is
    a tautology there; the statement lanky wrote has no value at that point at
    all. The printer declines it, the tester cannot answer it either, and the
    ledger says assumed and why rather than proved.
    """
    path = tmp_path / "outside.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Fin, Fn, Nat\n\n\n"
        "@theorem\n"
        "def outside(n: Nat, f: Fn[Fin[n], Nat]) -> f(n) == f(n):\n"
        '    """One point past the domain f declares."""\n',
        encoding="utf-8",
    )
    assert cli.main(["check", str(path)]) == 0
    assert "assumed" in capsys.readouterr().out
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.status is not Status.PROVED
    assert "outside the domain" in fact.provenance["untested"]


def test_a_file_that_does_not_exist_is_a_mistake_in_the_command(capsys) -> None:
    assert cli.main(["check", "/no/such/file.py"]) == 2
    assert "no such file" in capsys.readouterr().out


def test_a_missing_file_the_checked_file_opens_is_the_file_failing(tmp_path, capsys) -> None:
    """A ``FileNotFoundError`` raised inside the file is the file's, not the command's.

    The command-error branch used to catch every ``FileNotFoundError`` out of
    ``check_path``, so a file that exists and opens a data file that does not
    was reported as missing itself, with exit code 2 and no traceback.
    """
    path = tmp_path / "reads_data.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from pathlib import Path\n\n"
        "DATA = (Path(__file__).parent / 'missing-data.json').read_text()\n",
        encoding="utf-8",
    )
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "no such file" not in printed
    assert "could not be imported" in printed
    assert "FileNotFoundError" in printed
    assert "missing-data.json" in printed


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


def test_an_oracle_whose_availability_probe_raises_does_not_stop_the_check(
    tmp_path, monkeypatch, capsys
) -> None:
    """One broken optional oracle costs itself, not the check.

    The probe used to raise straight out of ``establish`` and ``oracle_lines``,
    so ``lanky check`` reported the checked file as unimportable and the
    weaker oracles never ran.
    """
    from lanky.plugins import registry

    class BrokenProbe:
        name = "broken-probe"

        def trust_class(self) -> str:
            return "decision-procedure"

        def availability(self) -> tuple[bool, str]:
            raise ImportError("libdemo.so: cannot open shared object file")

        def can_establish(self, fact, /) -> bool:
            return True

        def establish(self, fact, /):
            raise AssertionError("an unavailable oracle is never asked")

    # load everything first, so that nothing registered during the test is
    # lost when the patched list is put back
    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, BrokenProbe()])

    ledger = check_path(write_file(tmp_path))
    assert [fact.status for fact in ledger] == [Status.TESTED, Status.REFUTED]
    (line,) = [line for line in oracle_lines() if line.startswith("broken-probe ")]
    assert line.startswith(
        "broken-probe (decision-procedure): unavailable: its availability check raised "
        "ImportError: libdemo.so"
    )

    assert cli.main(["check", write_file(tmp_path), "--verbose"]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" not in printed
    assert "REFUTED false_claim" in printed


HELPER = '''
"""A claim that lives in a module the checked file imports."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Nat


@theorem
def helper_claim(n: Nat) -> n + 0 == n:
    """Collected when the file that imports this module is checked."""
'''


def test_a_claim_imported_from_a_neighbour_is_collected_on_every_check(
    tmp_path, monkeypatch
) -> None:
    """Checking a file twice must collect the claims it imports twice.

    Python imports a module once per process. The first check of the file
    executed its neighbour and collected the neighbour's theorem; the second
    found the neighbour cached, executed nothing, and returned a ledger
    without it. A module found elsewhere on the path is not the checked file's
    to release, and it stays imported.
    """
    import sys

    neighbour = "lanky_test_neighbour_claims"
    elsewhere = tmp_path / "elsewhere"
    elsewhere.mkdir()
    (elsewhere / "lanky_test_elsewhere.py").write_text("VALUE = 1\n", encoding="utf-8")
    monkeypatch.syspath_prepend(str(elsewhere))

    project = tmp_path / "project"
    project.mkdir()
    (project / f"{neighbour}.py").write_text(HELPER, encoding="utf-8")
    main = project / "main_claims.py"
    main.write_text(
        FILE.replace(
            "from lanky.prelude import Fin, Nat\n",
            "from lanky.prelude import Fin, Nat\n"
            f"from {neighbour} import helper_claim\n"
            "from lanky_test_elsewhere import VALUE\n",
        ),
        encoding="utf-8",
    )

    try:
        first = [fact.owner for fact in check_path(main)]
        second = [fact.owner for fact in check_path(main)]
        assert first == ["helper_claim", "true_claim", "false_claim"]
        assert second == first
        assert neighbour not in sys.modules
        assert "lanky_test_elsewhere" in sys.modules
    finally:
        for name in (neighbour, "lanky_test_elsewhere"):
            sys.modules.pop(name, None)
