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
than reported as a pass. An assignment has to land inside the family's codomain
(:func:`in_sort`): a hypothesis that demands ``f(0) == -1`` of an
``Fn[Fin[1], Nat]`` is unsatisfiable rather than a licence to put ``-1`` into the
draw, so the draw is dropped instead.

A draw that the statement cannot be answered at is dropped the same way. That is
what an existential over a sampled domain does when no draw witnesses it
(:class:`~lanky.terms.Undecided`): four points out of ``Nat`` finding no witness
is not a refutation, so the draw counts as neither evidence nor counterexample.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Forall,
    Undecided,
    binder_assignments,
    evaluate,
    free_variables,
    render,
)

__all__ = [
    "SkipSample",
    "Table",
    "TestReport",
    "check",
    "in_sort",
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


def in_sort(value: Any, sort: Any, context: dict[str, Any]) -> bool:
    """Whether ``value`` is an inhabitant of ``sort`` at the sizes in ``context``.

    This is the counterpart of :func:`sample_value`, and it exists because the
    sampler is not the only thing that puts a value into a draw: a definitional
    hypothesis *assigns* one (see :func:`satisfy_hypotheses`), and an assignment
    that lands outside the declared sort would make the draw a counterexample to
    a statement that never claimed anything about it.

    A sort this function does not know how to test is accepted, because the
    question here is whether the value is provably outside its sort, not whether
    it is provably inside. A :class:`~lanky.prelude.Refined` sort is tested on
    its base only: its propositions name the variable they refine, and a table
    entry has no name to bind them to.
    """
    if isinstance(sort, Refined):
        return in_sort(value, sort.base, context)
    if isinstance(sort, FinType):
        if not isinstance(value, int) or isinstance(value, bool):
            return False
        try:
            bound = int(evaluate(sort.bound, context))
        except Exception:  # noqa: BLE001 - an unevaluable bound cannot exclude a value
            return True
        return 0 <= value < bound
    if isinstance(sort, Sort):
        if sort.name == "Nat":
            return isinstance(value, int) and not isinstance(value, bool) and value >= 0
        if sort.name == "Int":
            return isinstance(value, int) and not isinstance(value, bool)
        if sort.name in ("Bool", "Prop"):
            return isinstance(value, bool)
        if sort.name == "Real":
            return isinstance(value, int | float | Fraction) and not isinstance(
                value, bool
            )
    if sort is int:
        return isinstance(value, int) and not isinstance(value, bool)
    if sort is float:
        return isinstance(value, int | float) and not isinstance(value, bool)
    if sort is bool:
        return isinstance(value, bool)
    return True


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


def _assign_definition(
    call: Any,
    value_expr: Any,
    context: dict[str, Any],
    sorts: dict[str, Any],
) -> None:
    """Perform one assignment ``f(i) = e`` into a sampled table.

    Raises:
        SkipSample: If the value the hypothesis defines is outside the family's
            codomain. The hypothesis and the declared sort cannot both hold, so
            there is no draw here to test: writing the value anyway would put a
            point outside its sort into the context and let the goal be
            "refuted" by a counterexample the statement excludes.
    """
    name = call.function.name
    table = context.get(name)
    if not isinstance(table, Table):
        return
    index = int(evaluate(call.parameters[0], context))
    if not 0 <= index < len(table):
        return
    value = evaluate(value_expr, context)
    sort = sorts.get(name)
    codomain = sort.codomain if isinstance(sort, FnType) else None
    if codomain is not None and not in_sort(value, codomain, context):
        raise SkipSample(
            f"{name}({index}) = {value!r} is outside {codomain}, so no draw "
            f"satisfies {render(call)} == {render(value_expr)} at this sort"
        )
    table[index] = value


def satisfy_hypotheses(
    hypotheses: Any,
    context: dict[str, Any],
    sorts: Any = None,
) -> None:
    """Make the definitional hypotheses true by construction, where possible.

    Each hypothesis is tried in the order written, so a recurrence that reads
    earlier entries sees the entries an earlier hypothesis set. Anything that
    does not match the pattern is left for the rejection filter.

    ``sorts`` maps a variable name to its declared sort, and is what keeps a
    synthesized value inside the family's codomain.

    Raises:
        SkipSample: If a definition demands a value the codomain does not have.
    """
    sorts = dict(sorts or {})
    for prop in hypotheses:
        definition = _definition(prop)
        if definition is not None:
            _try(lambda d=definition: _assign_definition(d[0], d[1], context, sorts))
            continue
        if isinstance(prop, Forall) and prop.guard is None:
            definition = _definition(prop.body)
            if definition is None:
                continue
            for _ in binder_assignments(prop.binders, context):
                _try(lambda d=definition: _assign_definition(d[0], d[1], context, sorts))


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

    ``undecided`` counts the draws that were dropped because the statement
    could not be answered at them, which today means an existential over a
    sampled domain that no draw witnessed (:class:`~lanky.terms.Undecided`).
    Such a draw is neither evidence nor a counterexample, so it is not counted
    as valid.
    """

    ok: bool
    counterexample: dict[str, Any] | None = None
    samples: int = 0
    valid: int = 0
    undecided: int = 0
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

    A draw is dropped rather than counted when it cannot be completed
    (:class:`SkipSample`, including a definitional hypothesis that would put a
    value outside its codomain) and when the statement cannot be answered at it
    (:class:`~lanky.terms.Undecided`, an existential over a sampled domain that
    found no witness). Neither is a counterexample, and neither is evidence.
    """
    rng = random.Random(seed)
    variables = sampling_order(variables)
    sorts = dict(variables)
    report = TestReport(ok=True)
    for _ in range(samples * REJECTION_FACTOR):
        if report.valid >= samples:
            break
        report.samples += 1
        context: dict[str, Any] = {}
        try:
            for name, sort in variables:
                context[name] = sample_value(sort, rng, context, name)
            satisfy_hypotheses(hypotheses, context, sorts)
        except SkipSample as exc:
            if len(report.skipped) < 3:
                report.skipped.append(str(exc))
            continue
        sampler = sort_sampler(rng, context)
        try:
            if not all(bool(evaluate(h, context, sampler)) for h in hypotheses):
                continue
            satisfied = bool(evaluate(goal, context, sampler))
        except Undecided as exc:
            report.undecided += 1
            if len(report.skipped) < 3:
                report.skipped.append(str(exc))
            continue
        report.valid += 1
        if not satisfied:
            report.ok = False
            report.counterexample = {k: _describe(v) for k, v in context.items()}
            report.reason = "the goal is false at this assignment"
            return report
    if report.valid == 0:
        if report.undecided:
            report.reason = (
                "no draw could decide the statement: an existential over a "
                "sampled domain found no witness, which is not a refutation"
            )
        else:
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
