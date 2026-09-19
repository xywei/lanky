"""The property tester: a statement is a predicate, so run it.

The design idea. An annotation is an expression, so evaluating it at concrete
values yields a ``bool``. That makes every theorem a property test for free: draw
values for the variables, keep the draws the hypotheses accept, evaluate the goal.
No separate test has to be written and none can drift from the statement.

Sampling follows the sort. Discrete sorts draw small integers, because the
interesting failures of an index argument are near zero and the quantifiers are
enumerated. ``Real`` draws :class:`~fractions.Fraction` when its exactness class
is ``exact``, so that an exact claim is tested exactly and not defeated by
rounding, and floats otherwise. ``Fn[Fin[n], B]`` draws a table over the domain,
which is how a theorem talks about data a kernel produced.

Hypotheses are filters, but a random table almost never satisfies a recurrence,
so before filtering the sampler tries to *satisfy* the definitional ones: a
hypothesis of the form ``f(i) == e`` (possibly under quantifiers) is read as an
assignment to the table ``f`` at the point ``i``, walked in domain order. That
turns ``off(0) == 0`` and ``all(off(r + 1) == off(r) + cnt(r) for r in Fin[n])``
into an actual prefix sum, and the theorem about it gets tested rather than
vacuously passed. Whatever the assignment pass does not match is still filtered,
and the report says how many draws survived, so a vacuous test is visible rather
than reported as a pass.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import Forall, binder_assignments, evaluate, free_variables

__all__ = [
    "SkipSample",
    "Table",
    "TestReport",
    "check",
    "sample_value",
    "sampling_order",
]

#: Largest natural number drawn. Small on purpose: quantifiers are enumerated.
MAX_NAT = 5

#: How many values a quantifier over an unbounded sort draws.
SORT_SAMPLE_POINTS = 4

#: How many draws per requested sample before giving up on the hypotheses.
REJECTION_FACTOR = 20


class SkipSample(Exception):
    """This draw cannot be completed (an empty domain, say); take another."""


class Table:
    """A finite family: what a property test supplies for an ``Fn[A, B]``.

    It is callable, because a theorem writes ``off(r)``, and indexable and
    mutable, because the sampler fills it in when a hypothesis defines it.
    """

    def __init__(self, values: Any) -> None:
        self.values = list(values)

    def __call__(self, index: Any) -> Any:
        """The value at ``index``, as a family application."""
        return self.values[int(index)]

    def __getitem__(self, index: Any) -> Any:
        """The value at ``index``."""
        return self.values[int(index)]

    def __setitem__(self, index: Any, value: Any) -> None:
        """Set the value at ``index``."""
        self.values[int(index)] = value

    def __len__(self) -> int:
        """The size of the domain."""
        return len(self.values)

    def __iter__(self) -> Any:
        """Iterate the values."""
        return iter(self.values)

    def __repr__(self) -> str:
        """Print as the list of values."""
        return f"Table({self.values!r})"


def sample_value(
    sort: Any,
    rng: random.Random,
    context: dict[str, Any],
    name: str | None = None,
) -> Any:
    """Draw one value of ``sort``, using ``context`` for any symbolic size.

    ``name`` is the variable the value is for, which a refinement needs: the
    propositions of ``Nat & (n > 0)`` talk about ``n``.
    """
    if isinstance(sort, Refined):
        for _ in range(64):
            value = sample_value(sort.base, rng, context, name)
            if name is None or sort.holds({**context, name: value}):
                return value
        raise SkipSample(f"no draw of {sort} satisfied its refinement")
    if isinstance(sort, FinType):
        bound = int(evaluate(sort.bound, context))
        if bound <= 0:
            raise SkipSample(f"{sort} is empty")
        return rng.randrange(bound)
    if isinstance(sort, FnType):
        domain = sort.domain
        if not isinstance(domain, FinType):
            raise SkipSample(f"cannot tabulate a family over {domain}")
        bound = int(evaluate(domain.bound, context))
        if bound < 0:
            raise SkipSample(f"{domain} has a negative size")
        return Table(sample_value(sort.codomain, rng, context) for _ in range(bound))
    if isinstance(sort, Sort):
        if sort.name == "Nat":
            return rng.randrange(MAX_NAT + 1)
        if sort.name == "Int":
            return rng.randrange(-MAX_NAT, MAX_NAT + 1)
        if sort.name in ("Bool", "Prop"):
            return rng.random() < 0.5
        if sort.name == "Real":
            if sort.exactness == "exact":
                return Fraction(rng.randrange(-8, 9), rng.randrange(1, 5))
            return rng.uniform(-1.0, 1.0)
    if sort is int:
        return rng.randrange(-MAX_NAT, MAX_NAT + 1)
    if sort is float:
        return rng.uniform(-1.0, 1.0)
    if sort is bool:
        return rng.random() < 0.5
    raise SkipSample(f"no sampler for {sort!r}")


def sort_names(sort: Any) -> frozenset[str]:
    """The variable names a sort's own expressions mention.

    ``Fn[Fin[n], Nat]`` mentions ``n``, and a value for it cannot be drawn
    before one has been drawn for ``n``.
    """
    if isinstance(sort, Refined):
        names = sort_names(sort.base)
        for prop in getattr(sort, "props", ()):
            names |= free_variables(prop)
        return names
    if isinstance(sort, FinType):
        return free_variables(sort.bound)
    if isinstance(sort, FnType):
        return sort_names(sort.domain) | sort_names(sort.codomain)
    return frozenset()


def sampling_order(variables: Any) -> list[tuple[str, Any]]:
    """The variables reordered so that a size is drawn before what it sizes.

    Signature order is the order a reader expects and almost always the right
    one, so this is stable: a variable moves only when another variable's name
    appears in its sort. ``def t(f: Fn[Fin[n], Nat], n: Nat)`` is the case that
    needs it, and without the reordering the draw for ``f`` asks for a value of
    ``n`` that does not exist yet. A cycle (two sorts naming each other) cannot
    be ordered and is left alone, to be reported as the draw failing.
    """
    remaining = list(variables)
    names = {name for name, _ in remaining}
    ordered: list[tuple[str, Any]] = []
    drawn: set[str] = set()
    while remaining:
        for index, (name, sort) in enumerate(remaining):
            if not (sort_names(sort) & names) - drawn - {name}:
                ordered.append(remaining.pop(index))
                drawn.add(name)
                break
        else:  # a cycle: keep what is left in the order it was written
            ordered.extend(remaining)
            break
    return ordered


def sort_sampler(rng: random.Random, context: dict[str, Any]) -> Any:
    """A sampler for quantifier domains that are sorts rather than index types.

    ``Fin`` is enumerated by the evaluator; a quantifier over ``Nat`` has to be
    sampled, and this is where the draws come from.
    """

    def sample(domain: Any) -> list[Any]:
        return [
            sample_value(domain, rng, context) for _ in range(SORT_SAMPLE_POINTS)
        ]

    return sample


# {{{ satisfying definitional hypotheses


def _definition(prop: Any) -> tuple[Any, Any] | None:
    """Read ``f(i) == e`` as the pair ``(f(i), e)``, or answer ``None``."""
    if not isinstance(prop, prim.Comparison) or prop.operator != "==":
        return None
    for left, right in ((prop.left, prop.right), (prop.right, prop.left)):
        if isinstance(left, prim.Call) and isinstance(left.function, prim.Variable):
            if len(left.parameters) == 1:
                return left, right
    return None


def _assign_definition(call: Any, value_expr: Any, context: dict[str, Any]) -> None:
    """Perform one assignment ``f(i) = e`` into a sampled table."""
    table = context.get(call.function.name)
    if not isinstance(table, Table):
        return
    index = int(evaluate(call.parameters[0], context))
    if 0 <= index < len(table):
        table[index] = evaluate(value_expr, context)


def satisfy_hypotheses(hypotheses: Any, context: dict[str, Any]) -> None:
    """Make the definitional hypotheses true by construction, where possible.

    Each hypothesis is tried in the order written, so a recurrence that reads
    earlier entries sees the entries an earlier hypothesis set. Anything that
    does not match the pattern is left for the rejection filter.
    """
    for prop in hypotheses:
        definition = _definition(prop)
        if definition is not None:
            _try(lambda d=definition: _assign_definition(d[0], d[1], context))
            continue
        if isinstance(prop, Forall) and prop.guard is None:
            definition = _definition(prop.body)
            if definition is None:
                continue
            for _ in binder_assignments(prop.binders, context):
                _try(lambda d=definition: _assign_definition(d[0], d[1], context))


def _try(action: Any) -> None:
    """Run an assignment, ignoring the draws it cannot complete."""
    try:
        action()
    except (TypeError, ValueError, KeyError, IndexError, ZeroDivisionError):
        return


# }}}


@dataclass
class TestReport:
    """What a property test found.

    ``valid`` is the number of draws the hypotheses accepted. When it is zero
    the test proves nothing, and saying so is the whole reason this field
    exists: an oracle must not report a vacuous pass as evidence.
    """

    ok: bool
    counterexample: dict[str, Any] | None = None
    samples: int = 0
    valid: int = 0
    reason: str = ""
    skipped: list[str] = field(default_factory=list)


def check(
    variables: Any,
    hypotheses: Any,
    goal: Any,
    samples: int = 200,
    seed: int = 0,
) -> TestReport:
    """Test ``goal`` under ``hypotheses`` by drawing values for ``variables``.

    ``variables`` is a sequence of ``(name, sort)`` pairs in signature order.
    They are drawn in that order unless a sort names another variable, in which
    case that one is drawn first (see :func:`sampling_order`): a size has to
    exist before the family it sizes can be tabulated. ``hypotheses`` is a
    sequence of propositions.
    """
    rng = random.Random(seed)
    variables = sampling_order(variables)
    report = TestReport(ok=True)
    for _ in range(samples * REJECTION_FACTOR):
        if report.valid >= samples:
            break
        report.samples += 1
        context: dict[str, Any] = {}
        try:
            for name, sort in variables:
                context[name] = sample_value(sort, rng, context, name)
        except SkipSample as exc:
            if len(report.skipped) < 3:
                report.skipped.append(str(exc))
            continue
        satisfy_hypotheses(hypotheses, context)
        sampler = sort_sampler(rng, context)
        if not all(bool(evaluate(h, context, sampler)) for h in hypotheses):
            continue
        report.valid += 1
        if not bool(evaluate(goal, context, sampler)):
            report.ok = False
            report.counterexample = {k: _describe(v) for k, v in context.items()}
            report.reason = "the goal is false at this assignment"
            return report
    if report.valid == 0:
        report.reason = (
            "no draw satisfied the hypotheses, so nothing was tested"
            if hypotheses
            else "no draw could be completed"
        )
    return report


def _describe(value: Any) -> Any:
    """Render a sampled value for a counterexample report."""
    if isinstance(value, Table):
        return list(value.values)
    return value
