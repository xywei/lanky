"""Smoke tests: the package imports, re-exports, and answers on the command line."""

from __future__ import annotations

import pytest

import lanky
from lanky import cli


def test_version() -> None:
    assert lanky.__version__ == "0.1.0.dev0"


def test_module_has_docstring() -> None:
    assert lanky.__doc__ and "Lean" in lanky.__doc__


def test_the_package_re_exports_the_interface() -> None:
    for name in (
        "theorem",
        "sum",
        "forall",
        "exists",
        "Var",
        "Scope",
        "Fact",
        "Status",
        "Ledger",
        "registry",
        "Nat",
        "Int",
        "Real",
        "Bool",
        "Fin",
        "Fn",
        "Prop",
        "__version__",
    ):
        assert hasattr(lanky, name), name


def test_the_built_in_plugins_are_registered() -> None:
    assert [theory.name for theory in lanky.registry.theories] == ["theorem"]
    assert {oracle.name for oracle in lanky.registry.oracles} >= {
        "lean",
        "property-test",
    }


def test_cli_version(capsys) -> None:
    with pytest.raises(SystemExit) as exit_info:
        cli.main(["--version"])
    assert exit_info.value.code == 0
    assert lanky.__version__ in capsys.readouterr().out


def test_cli_check_is_a_verb(capsys) -> None:
    with pytest.raises(SystemExit):
        cli.main(["--help"])
    assert "check" in capsys.readouterr().out


def test_checking_the_worked_example() -> None:
    from pathlib import Path

    example = Path(__file__).resolve().parent.parent / "examples" / "gauss.py"
    ledger = lanky.check_path(example)
    assert [fact.owner for fact in ledger] == ["gauss", "scan_monotone"]
    # Every claim is established by someone. Which oracle depends on what is
    # installed: with Lean present, scan_monotone is PROVED rather than TESTED.
    established = {lanky.Status.TESTED, lanky.Status.DECIDED, lanky.Status.PROVED}
    assert all(fact.status in established for fact in ledger)
