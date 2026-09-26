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


AXIOMS = '''
from __future__ import annotations

from lanky import axiom
from lanky.prelude import Fin, Nat


@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@axiom(cite="the same, copied down wrong")
def miscopied(n: Nat) -> sum(i**2 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """A square where the reference has a cube."""
'''


def test_axioms_are_collected_and_sampled(pytester) -> None:
    """An axiom is a statement, and a test run is where a miscopied one shows up."""
    pytester.makepyfile(test_axioms=AXIOMS)
    result = pytester.runpytest("-v", "-rA")
    result.assert_outcomes(passed=1, failed=1)
    result.stdout.fnmatch_lines(["*test_axioms.py::nicomachus PASSED*", "*counterexample*"])


GUARDED = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def ordered(n: Nat) -> all(a <= b for a in Fin[n] for b in Fin[n] if a <= b):
    """The guard holds at a = b, whenever n is positive."""


@theorem
def flipped(n: Nat) -> all(a <= b for a in Fin[n] for b in Fin[n] if (a < b) & (a > b)):
    """The guard holds nowhere, so the goal holds at every draw for no reason."""
'''


def test_a_goal_whose_guard_never_held_is_skipped(pytester) -> None:
    """A pass of a goal no draw got through the guard of is not evidence either.

    Every draw is valid, and ``flipped`` held at each because its guard held
    at no point; it is skipped with the guard in the reason, as a theorem
    whose hypotheses no draw satisfied is.
    """
    pytester.makepyfile(test_guarded=GUARDED)
    result = pytester.runpytest("-v", "-rs")
    result.assert_outcomes(passed=1, skipped=1)
    result.stdout.fnmatch_lines(
        ["*the goal's guard a < b and a > b never held in 200 valid draws: flipped*"]
    )
