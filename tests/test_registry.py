"""The registry: in-process registration and entry-point discovery."""

from __future__ import annotations

from importlib.metadata import EntryPoint

import pytest

from lanky import plugins
from lanky.oracles.test import TestOracle
from lanky.plugins import ENTRY_POINT_GROUPS, Executor, Oracle, Registry, Theory, Verb
from lanky.terms import Sum


class DemoOracle:
    """An oracle that establishes nothing, for testing the registry."""

    name = "demo"

    def trust_class(self) -> str:
        return "decision-procedure"

    def can_establish(self, fact, /) -> bool:
        return False

    def establish(self, fact, /) -> None:
        return None


class BrokenProbeOracle(DemoOracle):
    """An optional oracle whose probe for a native dependency raises."""

    name = "broken-probe"

    def availability(self) -> tuple[bool, str]:
        raise ImportError("libdemo.so: cannot open shared object file")


def test_the_entry_point_groups_are_part_of_the_contract() -> None:
    assert ENTRY_POINT_GROUPS == (
        "lanky.theories",
        "lanky.oracles",
        "lanky.executors",
        "lanky.verbs",
    )
    assert all(protocol is not None for protocol in (Theory, Oracle, Executor, Verb))


def test_in_process_registration() -> None:
    registry = Registry()
    assert registry.register_oracle(DemoOracle()).name == "demo"
    registry.register_theory("theory")
    registry.register_executor("executor")
    registry.register_verb("verb")
    obj = object()
    assert registry.register_object(obj) is obj
    assert registry.objects == [obj]
    assert len(registry.oracles) == 1
    assert "oracles=1" in repr(registry)


def test_oracles_are_sorted_strongest_first() -> None:
    registry = Registry()
    registry.register_oracle(TestOracle())
    registry.register_oracle(DemoOracle())
    assert [oracle.name for oracle in registry.sorted_oracles()] == [
        "demo",
        "property-test",
    ]


def test_term_lowerings_are_a_table_a_plugin_fills() -> None:
    registry = Registry()

    def lower(term):
        return "lowered"

    registry.register_term_lowering(Sum, lower)
    assert registry.term_lowerings[Sum] is lower


def test_entry_point_loading(monkeypatch: pytest.MonkeyPatch) -> None:
    points = {
        "lanky.oracles": [
            EntryPoint(
                name="demo",
                value="lanky.oracles.test:TestOracle",
                group="lanky.oracles",
            )
        ]
    }
    monkeypatch.setattr(
        plugins, "entry_points", lambda group: points.get(group, [])
    )
    registry = Registry()
    registry.load_entry_points()
    assert [oracle.name for oracle in registry.oracles] == ["property-test"]
    # a class named by an entry point is instantiated, and groups load once
    assert isinstance(registry.oracles[0], TestOracle)
    registry.load_entry_points()
    assert len(registry.oracles) == 1


def test_a_plugin_registered_twice_under_one_name_is_installed_once() -> None:
    """Two copies of one theory would compute every fact twice.

    A plugin can arrive twice: loopty registers its kernel theory when its
    module is imported and again through the ``lanky.theories`` entry point.
    The registry keeps the first and ignores the second, so a check does the
    work once.
    """
    registry = Registry()
    first, second = DemoOracle(), DemoOracle()
    assert registry.register_oracle(first) is first
    assert registry.register_oracle(second) is second
    assert registry.oracles == [first]

    # ... unless the caller says so, which is the only way to displace one
    registry.register_oracle(second, replace=True)
    assert registry.oracles == [second]

    # an object with no name has nothing to compare, so it is never dropped
    registry.register_theory("theory")
    registry.register_theory("theory")
    assert len(registry.theories) == 2


def test_entry_points_do_not_duplicate_an_already_registered_plugin(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The real shape of the duplicate: in-process first, entry point second."""
    points = {
        "lanky.oracles": [
            EntryPoint(
                name="property-test",
                value="lanky.oracles.test:TestOracle",
                group="lanky.oracles",
            )
        ]
    }
    monkeypatch.setattr(plugins, "entry_points", lambda group: points.get(group, []))
    registry = Registry()
    registered = registry.register_oracle(TestOracle())
    registry.load_entry_points()
    assert registry.oracles == [registered]


def test_collecting_scopes_and_releases_decorated_objects() -> None:
    """``lanky check`` wants this import's objects, and wants them gone after."""
    registry = Registry()
    before = object()
    registry.register_object(before)
    inside = object()
    with registry.collecting() as collected:
        registry.register_object(inside)
    assert collected == [inside]
    assert registry.objects == [before]


def test_an_availability_probe_that_raises_is_an_unavailable_oracle() -> None:
    """Probing for a missing native dependency is how an optional oracle fails.

    The exception used to escape ``oracle_availability``, which the check
    calls before it reaches its per-oracle handler, so one broken optional
    oracle aborted the whole check. It is now the reason the oracle is
    unavailable, and an oracle with no probe is still available.
    """
    available, reason = plugins.oracle_availability(BrokenProbeOracle())
    assert available is False
    assert "ImportError" in reason
    assert "libdemo.so" in reason
    assert plugins.oracle_availability(DemoOracle()) == (True, "")
