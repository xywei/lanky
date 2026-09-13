"""Smoke tests for the placeholder release."""

from __future__ import annotations

import lanky
from lanky import cli


def test_version() -> None:
    assert lanky.__version__ == "0.0.1"


def test_module_has_docstring() -> None:
    assert lanky.__doc__ and "Lean" in lanky.__doc__


def test_cli_main(capsys) -> None:
    assert cli.main() == 0
    out = capsys.readouterr().out
    assert "lanky" in out
    assert lanky.__version__ in out
    assert "work in progress: placeholder release" in out
    assert "https://github.com/xywei/lanky" in out


def test_ledger_and_plugins_import() -> None:
    from lanky.ledger import Fact, Status
    from lanky.plugins import ENTRY_POINT_GROUPS, Executor, Oracle, Theory, Verb

    assert {s.value for s in Status} == {
        "tested",
        "decided",
        "proved",
        "certified",
        "assumed",
    }
    fact = Fact(statement="1 + 1 = 2", status=Status.ASSUMED, decided_by=None, provenance={})
    assert fact.status is Status.ASSUMED
    assert ENTRY_POINT_GROUPS == (
        "lanky.theories",
        "lanky.oracles",
        "lanky.executors",
        "lanky.verbs",
    )
    assert all(p is not None for p in (Theory, Oracle, Executor, Verb))
