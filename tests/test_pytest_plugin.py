"""The pytest plugin: theorems in a test module are collected and run."""

from __future__ import annotations

MODULE = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def true_claim(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Gauss."""


@theorem
def false_claim(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
    """False as soon as n is at least two."""


@theorem
def vacuous(n: Nat, h: n < 0) -> n == n:
    """No draw satisfies the hypothesis, so nothing is tested."""
'''


def test_theorems_are_collected_as_items(pytester) -> None:
    """A true theorem passes, a false one fails with its counterexample, a
    theorem no draw could satisfy is skipped rather than reported as passing."""
    pytester.makepyfile(test_claims=MODULE)
    result = pytester.runpytest("-v")
    result.assert_outcomes(passed=1, failed=1, skipped=1)
    result.stdout.fnmatch_lines(["*counterexample*"])


PRIVATE = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def _false_on_purpose(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
    """Kept as an example of a false statement, and not run."""


def test_the_statement_is_still_readable() -> None:
    assert "sum" in _false_on_purpose.statement
'''


def test_a_private_theorem_is_not_collected(pytester) -> None:
    """A module may keep a theorem it does not want run: underscore it."""
    pytester.makepyfile(test_private=PRIVATE)
    result = pytester.runpytest("-v")
    result.assert_outcomes(passed=1)


ONE = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Nat


@theorem
def claim(n: Nat) -> n + 0 == n:
    """Addition of zero, module one."""
'''

TWO = ONE.replace("module one", "module two")


def test_theorems_do_not_leak_between_modules(pytester) -> None:
    """Two modules, one theorem name: each module reports its own, once.

    The decorators register into one process-wide registry, so the question is
    worth asking: collection has to follow the module, not the registry.
    """
    pytester.makepyfile(test_one=ONE, test_two=TWO)
    result = pytester.runpytest("-v")
    result.assert_outcomes(passed=2)
    result.stdout.fnmatch_lines(["*test_one.py::claim*", "*test_two.py::claim*"])
