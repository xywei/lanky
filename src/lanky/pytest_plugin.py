"""A pytest plugin: theorems are collected as test items.

The design idea. A theorem is already a property test, so a test file that
contains one should not have to wrap it in a function named ``test_``. This
plugin collects every :class:`~lanky.theory.Theorem` it finds in a collected
module under a public name and runs it, reporting a counterexample as the
failure. A theorem whose hypotheses no draw satisfied is reported as skipped
rather than passed: a vacuous pass is not evidence and must not read like one.
Nor is a pass of a goal whose quantifier's guard held at no draw, which is
skipped as well, with the guard in the reason.
A theorem bound to a name starting with an underscore is not collected, which
is how a module keeps a statement it does not want run.

An axiom is collected too. The ledger takes it on its citation, and a
counterexample to the statement as written is how a citation copied down wrong
shows up, here as in ``lanky check``.

The plugin is installed under the ``pytest11`` entry-point group, so it is
active wherever lanky is installed.
"""

from __future__ import annotations

from typing import Any

import pytest

from lanky.theory import Theorem

__all__ = ["TheoremItem", "pytest_pycollect_makeitem"]


class TheoremFailure(AssertionError):
    """A theorem was refuted by a draw."""


class TheoremItem(pytest.Item):
    """One collected theorem, run as a property test."""

    def __init__(self, *, theorem: Theorem, **kwargs: Any) -> None:
        super().__init__(**kwargs)
        self.theorem = theorem

    def runtest(self) -> None:
        """Sample the statement; fail on a counterexample, skip on a vacuous pass."""
        report = self.theorem.report()
        if not report.ok:
            raise TheoremFailure(
                f"{self.theorem.statement}\n"
                f"counterexample: {report.counterexample}"
            )
        if report.valid == 0:
            # The reason comes from the report, because "no valid draw" has
            # more than one cause: hypotheses nothing satisfied, a draw that
            # could not be completed, or a statement no draw could decide.
            reason = report.reason or "no draw satisfied the hypotheses"
            pytest.skip(f"{reason}: {self.name}")
        if report.goal_reached == 0:
            # The goal held at every valid draw because its quantifier got
            # through to no point at any of them: its guard never held.
            pytest.skip(f"{report.reason}: {self.name}")

    def repr_failure(self, excinfo: Any, style: Any = None) -> str:
        """Report the counterexample without a Python traceback."""
        if isinstance(excinfo.value, TheoremFailure):
            return str(excinfo.value)
        return super().repr_failure(excinfo, style)

    def reportinfo(self) -> tuple[Any, int, str]:
        """Point at the theorem's source line."""
        return self.path, self.theorem.line - 1, f"{self.theorem.noun} {self.name}"


def pytest_pycollect_makeitem(collector: Any, name: str, obj: object) -> Any:
    """Collect a theorem as a test item, unless its name is private.

    A module may hold a theorem it does not want run: one that is deliberately
    false, or one kept as an example of a statement. Python's own convention
    for that is a leading underscore, and it is the convention here too.
    """
    if isinstance(obj, Theorem) and not name.startswith("_"):
        return TheoremItem.from_parent(collector, name=name, theorem=obj)
    return None
