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

A draw that the statement cannot be answered at is dropped the same way. Three
things do that, and all three raise or are read as
:class:`~lanky.terms.Undecided` rather than as a counterexample, because none of
them is one:

*An existential over a sampled domain that no draw witnesses.* Four points out
of ``Nat`` finding no witness is not a refutation.

*A division or remainder by zero.* Python raises ``ZeroDivisionError`` where
Lean's integer division is total (``Int.fdiv x 0`` is ``0``, ``Int.fmod x 0``
is ``x``), so the sampled reading has no answer at that draw while the Lean
reading does. That is a gap between the two readings (:mod:`lanky.semantics`
records it in the fact's provenance), not evidence against the statement.

*A family applied outside the domain it declares.* ``f(n)`` for an
``f : Fn[Fin[n], Nat]`` names a point the statement's own types say is not
there, so the table has no value for it and the draw decides nothing. The Lean
printer refuses such an application outright (see :mod:`lanky.lean`), and this
is the same reading on the Python side.

A statement that is already a concrete ``True`` or ``False``, because it binds
no variable and assumes nothing, is not sampled at all: there is nothing to
draw, so it is reported once, as a pass or as a refutation with an empty
counterexample.
"""

from __future__ import annotations

import random
from contextlib import closing
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
    truth_value,
)

__all__ = [
    "SkipSample",
    "Table",
    "TestReport",
    "Unevaluable",
    "Unsampleable",
    "check",
    "in_sort",
    "sample_value",
    "sampling_order",
    "truth_value",
]

#: Largest natural number drawn. Small on purpose: quantifiers are enumerated.
MAX_NAT = 5

#: How many values a quantifier over an unbounded sort draws.
SORT_SAMPLE_POINTS = 4

#: How many draws per requested sample before giving up on the hypotheses.
REJECTION_FACTOR = 20


class SkipSample(Exception):
    """This draw cannot be completed (an empty domain, say); take another."""


class Unsampleable(SkipSample):
    """No draw of this sort can be completed here, because the tester has no sampler for it.

    A family over ``Nat`` cannot be tabulated, and neither can a sort nothing
    here knows how to draw. That is the tester's limit and says nothing about
    the statement, where an empty ``Fin`` or a refinement no draw satisfied is
    a hypothesis failing: a report that no draw satisfied the hypotheses must
    not be made of draws that never reached them (see :class:`TestReport`).
    """


class Unevaluable(SkipSample):
    """A refinement has no answer at this draw, as ``Nat & (10 // n > 1)`` at ``n = 0``.

    That is the refinement's counterpart of a guard that divides by zero, and
    it is counted the same way, as a draw the statement could not be answered
    at (``undecided``), not as a draw the hypotheses rejected.
    """


class Table:
    """A finite family: what a property test supplies for an ``Fn[A, B]``.

    It is callable, because a theorem writes ``off(r)``, and indexable and
    mutable, because the sampler fills it in when a hypothesis defines it.

    A point outside the domain is :class:`~lanky.terms.Undecided` and not an
    ``IndexError``, and a negative one is not the Python index it looks like.
    ``f(n)`` for an ``f : Fn[Fin[n], Nat]`` is a point the statement's own
    types say the family does not have: there is no value to compare, so the
    draw decides nothing, and reading ``f(-1)`` as the last entry would answer
    a question the statement never asked.
    """

    def __init__(self, values: Any, name: str = "a family") -> None:
        self.values = list(values)
        self.name = name

    def _position(self, index: Any) -> int:
        """The index as a point of the domain, or decline to answer there."""
        position = int(index)
        if not 0 <= position < len(self.values):
            extent = f"0 .. {len(self.values) - 1}" if self.values else "no points"
            raise Undecided(
                f"{self.name} is applied at {position}, which is outside the "
                f"domain it declares ({extent}), so this draw decides nothing"
            )
        return position

    def __call__(self, index: Any) -> Any:
        """The value at ``index``, as a family application."""
        return self.values[self._position(index)]

    def __getitem__(self, index: Any) -> Any:
        """The value at ``index``."""
        return self.values[self._position(index)]

    def __setitem__(self, index: Any, value: Any) -> None:
        """Set the value at ``index``."""
        self.values[self._position(index)] = value

    def __len__(self) -> int:
        """The size of the domain."""
        return len(self.values)

    def __iter__(self) -> Any:
        """Iterate the values."""
        return iter(self.values)

    def __eq__(self, other: Any) -> bool:
        """Compare two families by their values, which is what equality of families is.

        A statement such as ``f == g`` over two families is evaluated by
        comparing the tables the sampler drew, and without this the comparison
        fell back to identity: two empty tables over ``Fin[0]`` are the one
        function there is out of an empty domain, and they were reported as a
        counterexample to their own equality. The values are compared as lists,
        so a family of families compares its entries by this same rule.
        Defining equality makes a table unhashable, like the mutable list it
        wraps, and nothing keys a container by one.
        """
        if not isinstance(other, Table):
            return NotImplemented
        return self.values == other.values

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
            if name is None or _refinement_holds(sort, {**context, name: value}):
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
            raise Unsampleable(f"cannot tabulate a family over {domain}")
        bound = int(evaluate(domain.bound, context))
        if bound < 0:
            raise SkipSample(f"{domain} has a negative size")
        # A family over an empty domain exists whatever its codomain is, so the
        # codomain is only consulted when there is an entry to draw.
        codomain = _entry_sort(sort.codomain, context) if bound else sort.codomain
        return Table(
            (sample_value(codomain, rng, context) for _ in range(bound)),
            name=name or "a family",
        )
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
    raise Unsampleable(f"no sampler for {sort!r}")


def _entry_sort(codomain: Any, context: dict[str, Any]) -> Any:
    """The sort a family's entries are drawn from, with its refinement settled.

    An entry has no name, so :func:`sample_value` is asked for one without a
    ``name`` and used to accept every value of a refined codomain's base
    unchecked: ``f : Fn[Fin[1], Nat & False]`` got a table holding an ordinary
    natural, and a statement that is true because no such ``f`` exists was
    refuted by it. A refinement that names only variables already drawn is a
    condition on the codomain as a whole, and it is settled here once: when it
    holds, every value of the base is an entry, and when it fails the codomain
    is empty and no family with a point in its domain exists, so there is no
    draw to take. A refinement that names anything else cannot be judged at an
    entry, and drawing from the base as though it were absent would put values
    outside the declared sort into the table, so that draw is not taken either.

    Raises:
        SkipSample: If the codomain is empty at these values.
        Unsampleable: If its refinement names a variable nothing here gives a
            value.
        Unevaluable: If its refinement cannot be evaluated at these values.
    """
    if not isinstance(codomain, Refined):
        return codomain
    unbound = sorted(free_variables(codomain.props) - set(context))
    if unbound:
        raise Unsampleable(
            f"cannot draw the entries of a family into {codomain}: its "
            f"refinement names {', '.join(unbound)}, which no entry binds"
        )
    if not _refinement_holds(codomain, context):
        raise SkipSample(
            f"{codomain} is empty at this draw, so there is no family into it "
            "with a point in its domain"
        )
    return codomain.base


def _refinement_holds(sort: Refined, context: dict[str, Any]) -> bool:
    """Whether the refinement of ``sort`` holds here; skip a draw it cannot judge.

    A refinement is evaluated like any other proposition, and one that divides
    by a drawn size, ``Nat & (10 // n > 1)``, has no answer at ``n = 0``. That
    is one draw that cannot be completed and not a test that cannot run, but
    the ``ZeroDivisionError`` used to escape the sampler and end the whole
    test at the first such draw.

    Raises:
        Unevaluable: If the refinement cannot be evaluated at these values.
    """
    try:
        return sort.holds(context)
    except (Undecided, ZeroDivisionError) as exc:
        raise Unevaluable(
            f"the refinement of {sort} cannot be evaluated at this draw: "
            f"{type(exc).__name__}: {exc}"
        ) from exc


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
    """Run an assignment, ignoring the ones that cannot be carried out.

    :class:`~lanky.terms.Undecided` is in the list because the value a
    definition assigns can itself read the table (a recurrence does), and a
    read outside the domain declines rather than raising ``IndexError``. The
    assignment is skipped either way and the hypothesis is left to the filter.
    """
    try:
        action()
    except (TypeError, ValueError, KeyError, IndexError, ZeroDivisionError, Undecided):
        return


# }}}


@dataclass
class TestReport:
    """What a property test found.

    ``valid`` is the number of draws the hypotheses accepted. When it is zero
    the test proves nothing, and saying so is the whole reason this field
    exists: an oracle must not report a vacuous pass as evidence.

    ``undecided`` counts the draws that were dropped because the statement
    could not be answered at them: an existential over a sampled domain that no
    draw witnessed, a division by zero, a family applied outside its domain
    (see the module docstring), or a refinement that cannot be evaluated
    (:class:`Unevaluable`). Such a draw is neither evidence nor a
    counterexample, so it is not counted as valid.

    ``unsampleable`` counts the draws that could not be completed because a
    sort has no sampler (:class:`Unsampleable`). Such a draw never reached the
    hypotheses, so a report with any of them cannot say that no draw satisfied
    them, and its reason says that no draw could be completed instead.
    """

    ok: bool
    counterexample: dict[str, Any] | None = None
    samples: int = 0
    valid: int = 0
    undecided: int = 0
    unsampleable: int = 0
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
    (:class:`~lanky.terms.Undecided` or a ``ZeroDivisionError``: an existential
    over a sampled domain that found no witness, a division by zero, a family
    applied outside its domain, and a refinement that raises one of them,
    :class:`Unevaluable`). Neither is a counterexample, and neither is
    evidence.

    A counterexample names the drawn variables and, when the goal is a
    universal statement, the quantified point at which it fails (see
    :func:`_falsify`), so that the refutation can be replayed from what the
    report says.

    A goal that is already a concrete value is not sampled. A theorem with no
    binders and no hypotheses whose return annotation evaluated to a ``bool``
    has nothing to draw, so it is answered once. A ``goal`` of ``None``
    claims nothing and is read as ``True``; only a direct caller can pass
    one, because :class:`lanky.theory.Theorem` refuses a function with no
    return annotation.
    """
    if goal is None:
        goal = True
    if not variables and not hypotheses and not isinstance(goal, prim.ExpressionNode):
        return _constant_report(goal)
    rng = random.Random(seed)
    variables = sampling_order(variables)
    sorts = dict(variables)
    report = TestReport(ok=True)
    undecided_reason = ""
    unsampleable_reason = ""
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
            if isinstance(exc, Unsampleable):
                report.unsampleable += 1
                unsampleable_reason = unsampleable_reason or str(exc)
            elif isinstance(exc, Unevaluable):
                report.undecided += 1
                undecided_reason = undecided_reason or str(exc)
            if len(report.skipped) < 3:
                report.skipped.append(str(exc))
            continue
        sampler = sort_sampler(rng, context)
        try:
            if not all(truth_value(evaluate(h, context, sampler), h) for h in hypotheses):
                continue
            satisfied, witness = _falsify(goal, context, sampler)
        except (Undecided, ZeroDivisionError) as exc:
            report.undecided += 1
            undecided_reason = undecided_reason or _undecided_reason(exc)
            if len(report.skipped) < 3:
                report.skipped.append(_undecided_reason(exc))
            continue
        report.valid += 1
        if not satisfied:
            report.ok = False
            # The drawn variables come first and win a clash of names: they are
            # what the statement is false at, and a quantified point that
            # shadows one of them is detail about why.
            found = {**context, **{k: v for k, v in witness.items() if k not in context}}
            report.counterexample = {k: _describe(v) for k, v in found.items()}
            report.reason = "the goal is false at this assignment"
            return report
    if report.valid == 0:
        if report.undecided:
            report.reason = f"no draw could decide the statement: {undecided_reason}"
        elif report.unsampleable:
            report.reason = f"no draw could be completed: {unsampleable_reason}"
        else:
            report.reason = (
                "no draw satisfied the hypotheses, so nothing was tested"
                if hypotheses
                else "no draw could be completed"
            )
    return report


def _falsify(
    goal: Any,
    context: dict[str, Any],
    sampler: Any,
) -> tuple[bool, dict[str, Any]]:
    """Evaluate ``goal``, and when it is false say at which quantified point.

    The drawn variables are not the whole of a counterexample when the goal
    quantifies: ``all(i < 2 for i in Fin[n + 3])`` is false because of
    ``i = 2``, and the evaluator's binding of ``i`` lives in its own copy of
    the context and is gone by the time the report is written, so the
    refutation used to name ``n`` alone, which does not say why. This walks the
    part of the goal where "the point that made it false" is well defined, a
    universal quantifier and a conjunction and whatever nests in them, one
    point at a time in the order the evaluator visits them, and returns the
    first failing assignment along with the answer. Everything else is left to
    :func:`~lanky.terms.evaluate`, so the answer is the one it gives. A name
    already in the counterexample is not overwritten by an inner binder that
    shadows it.
    """
    if isinstance(goal, Forall):
        scope = dict(context)
        with closing(binder_assignments(goal.binders, scope, sampler)) as walk:
            for _ in walk:
                if goal.guard is not None and not truth_value(
                    evaluate(goal.guard, scope, sampler), goal.guard
                ):
                    continue
                holds, witness = _falsify(goal.body, scope, sampler)
                if not holds:
                    point = {var.name: scope[var.name] for var, _ in goal.binders}
                    point.update((k, v) for k, v in witness.items() if k not in point)
                    return False, point
        return True, {}
    if isinstance(goal, prim.LogicalAnd):
        for child in goal.children:
            holds, witness = _falsify(child, context, sampler)
            if not holds:
                return False, witness
        return True, {}
    return truth_value(evaluate(goal, context, sampler), goal), {}


def _constant_report(goal: Any) -> TestReport:
    """The report for a statement that is already a concrete value.

    ``@theorem def impossible() -> 1 == 2`` has no binders and no hypotheses,
    so Python answered the annotation itself and the term is the ``bool``
    ``False``. There is nothing to sample, and declining it would leave a false
    claim in the ledger as ``ASSUMED``, so it is answered here: ``True`` is a
    pass over the one draw there is, and ``False`` is a refutation whose
    counterexample is empty on purpose, because no assignment is what makes the
    statement false.
    """
    if truth_value(goal, goal):
        return TestReport(ok=True, samples=1, valid=1)
    return TestReport(
        ok=False,
        counterexample={},
        samples=1,
        valid=1,
        reason=(
            "the statement is the constant False: it binds no variable and "
            "assumes nothing, so there is no assignment to blame and nothing "
            "that could make it true"
        ),
    )


def _undecided_reason(exc: Exception) -> str:
    """Why a draw decided nothing, as a line for a report."""
    if isinstance(exc, ZeroDivisionError):
        return (
            "the statement divides by zero at this draw, which Python raises on "
            "and Lean's total integer division does not, so the two readings "
            "differ here rather than the statement being false"
        )
    return str(exc)


def _describe(value: Any) -> Any:
    """Render a sampled value for a counterexample report."""
    if isinstance(value, Table):
        return list(value.values)
    return value
