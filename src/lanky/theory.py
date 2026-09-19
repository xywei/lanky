"""The ``@theorem`` theory: a typed Python function is a statement.

The design idea. A theorem needs no syntax of its own. Its variables are the
parameters annotated with sorts, its hypotheses are the parameters annotated
with propositions, and its goal is the return annotation. Annotations are
evaluated, not parsed, so ``Fn[Fin[n + 1], Nat]`` and
``all(off(r + 1) == off(r) + cnt(r) for r in Fin[n])`` are ordinary Python
expressions that happen to build terms.

The decorator is inert and registering: it returns a :class:`Theorem` that runs
natively (evaluating the statement at concrete values, and sampling it as a
property test) and records itself in :data:`lanky.plugins.registry`, so that
``lanky check FILE`` only has to import the file. The body is a proof script for
a future oracle and is never executed by lanky.
"""

from __future__ import annotations

import functools
import os
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

from lanky.ledger import Fact, Status, fact_id
from lanky.plugins import registry
from lanky.prelude import FnType
from lanky.terms import Forall, LogicalAnd, Var, evaluate, evaluate_annotations, render
from lanky.testing import Table, TestReport, check

__all__ = ["Theorem", "TheoremTheory", "Verdict", "theorem"]


@dataclass(frozen=True)
class Verdict:
    """What a theorem answers when it is called at concrete values.

    ``holds`` is the honest reading of an implication: a statement whose
    hypotheses fail is not violated by those values. ``bool(verdict)`` is
    ``holds``, so a theorem can be used in an ``assert``.
    """

    hypotheses: dict[str, bool]
    goal: bool

    @property
    def hypotheses_hold(self) -> bool:
        """Whether every hypothesis is satisfied at these values."""
        return all(self.hypotheses.values())

    @property
    def holds(self) -> bool:
        """Whether the statement is satisfied: the goal, or a failed hypothesis."""
        return self.goal or not self.hypotheses_hold

    def __bool__(self) -> bool:
        """Whether the statement is satisfied at these values."""
        return self.holds


class Theorem:
    """A statement read off a typed Python function.

    Attributes:
        variables: ``(name, type)`` pairs, in signature order, so a size comes
            before the domains that mention it.
        hypotheses: ``(name, proposition)`` pairs.
        goal: The return annotation, as a term.
    """

    def __init__(self, fn: Any) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        annotations = evaluate_annotations(fn)
        self.goal = annotations.pop("return", None)
        variables: list[tuple[str, Any]] = []
        hypotheses: list[tuple[str, Any]] = []
        for name, annotation in annotations.items():
            # A concrete bool is a proposition Python already answered, as in
            # ``h: 1 == 2``, so it is a hypothesis and not a sort: nothing in
            # the prelude is a bool value, and reading it as one used to send
            # the sampler looking for an inhabitant of ``False``.
            if isinstance(annotation, prim.ExpressionNode | bool):
                hypotheses.append((name, annotation))
            else:
                variables.append((name, annotation))
        self.variables = tuple(variables)
        self.hypotheses = tuple(hypotheses)
        code = fn.__code__
        self.path = code.co_filename
        self.line = code.co_firstlineno
        self.where = f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        self.module = getattr(fn, "__module__", "") or ""

    # {{{ the statement

    @property
    def statement(self) -> str:
        """The statement as a sequent: variables, hypotheses, then the goal."""
        variables = ", ".join(f"{name} : {sort}" for name, sort in self.variables)
        hypotheses = ", ".join(render(prop) for _, prop in self.hypotheses)
        parts = [variables] if variables else []
        if hypotheses:
            parts.append(hypotheses)
        head = " | ".join(parts)
        goal = render(self.goal) if self.goal is not None else "True"
        return f"{head} |- {goal}" if head else goal

    @property
    def term(self) -> Any:
        """The statement as one closed term: the goal under its binders and guard.

        The variables become the binders and the hypotheses the guard, which is
        exactly the shape an oracle wants: for all values of the variables
        satisfying the hypotheses, the goal.

        A theorem with hypotheses and no sort-valued parameters still has a
        guard, and the binder tuple is then empty rather than the whole
        :class:`~lanky.terms.Forall` being dropped. Dropping it would hand the
        oracles the bare goal, which is a different and stronger claim: the
        hypotheses are what make an implication with a false antecedent valid,
        and without them such a theorem is refuted by its own hypothesis.

        With neither binders nor a guard the term is the goal itself, and for a
        closed statement such as ``-> 1 == 2`` the goal is a concrete ``bool``
        rather than a term. That is a fact like any other: the property-test
        oracle takes a ``bool`` and answers ``TESTED`` or ``REFUTED``.
        """
        if self.goal is None:
            return None
        binders = tuple((Var(name), sort) for name, sort in self.variables)
        guard: Any = None
        props = [prop for _, prop in self.hypotheses]
        if len(props) == 1:
            guard = props[0]
        elif props:
            guard = LogicalAnd(tuple(props))
        if not binders and guard is None:
            return self.goal
        return Forall(binders, self.goal, guard)

    # }}}

    def __call__(self, **concrete: Any) -> Verdict:
        """Evaluate the hypotheses and the goal at concrete values.

        The proof body is not run: it is a script for an oracle, not code. What
        running a theorem means is checking what it says. A value for a family
        parameter may be given as a sequence, which is read as a table.

        Raises:
            lanky.terms.Undecided: If the statement applies a family outside
                the domain it declares at these values. There is no value to
                compare there, so there is no verdict either; the property
                tester drops such a draw for the same reason.
        """
        missing = [name for name, _ in self.variables if name not in concrete]
        if missing:
            raise TypeError(f"{self.__name__} needs values for {', '.join(missing)}")
        sorts = dict(self.variables)
        context = {
            name: Table(value, name=name)
            if isinstance(sorts.get(name), FnType) and not callable(value)
            else value
            for name, value in concrete.items()
        }
        return Verdict(
            hypotheses={
                name: bool(evaluate(prop, context)) for name, prop in self.hypotheses
            },
            goal=True if self.goal is None else bool(evaluate(self.goal, context)),
        )

    # {{{ property testing

    def report(self, n: int = 200, seed: int = 0) -> TestReport:
        """Sample the statement and report what the draws found."""
        return check(self.variables, [p for _, p in self.hypotheses], self.goal, n, seed)

    def test(self, n: int = 200, seed: int = 0) -> tuple[bool, dict | None]:
        """Property-test the statement: ``(ok, counterexample or None)``.

        A pass here is evidence, not proof, and a pass over zero valid draws is
        not even evidence; :meth:`report` says how many draws the hypotheses
        accepted.
        """
        report = self.report(n, seed)
        return report.ok, report.counterexample

    # }}}

    @property
    def fact_id(self) -> str:
        """The id this theorem's fact carries, unique per definition.

        Two theorems can share a qualified name (one per module, or one
        decorator used twice), and a ledger keyed only by that name would keep
        one of them and drop the other. The module and the definition's line
        settle it; :func:`lanky.ledger.fact_id` is the shared builder, so a
        plugin theory can key its own facts the same way.
        """
        return fact_id("theorem", self.qualname, module=self.module, line=self.line)

    def fact(self) -> Fact:
        """This theorem as a ledger entry, before any oracle has seen it."""
        return Fact(
            id=self.fact_id,
            kind="theorem",
            statement=self.statement,
            term=self.term,
            status=Status.ASSUMED,
            decided_by=None,
            provenance={"path": self.path, "line": self.line},
            where=self.where,
            owner=self.qualname,
        )

    def lean(self) -> str:
        """The statement in Lean 4 syntax, when the printer supports it."""
        from lanky.lean import print_lean

        return print_lean(self.term)

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<theorem {self.__name__}: {self.statement}>"


class TheoremTheory:
    """The built-in theory: ``@theorem`` over typed Python functions."""

    name = "theorem"

    def __call__(self, obj: Any, /) -> Theorem:
        """Decorate ``obj`` as a theorem and register it."""
        return registry.register_object(Theorem(obj))

    def facts(self, obj: Any, /) -> tuple:
        """The one fact a theorem claims, or nothing for an object it does not own."""
        return (obj.fact(),) if isinstance(obj, Theorem) else ()


#: The theory itself, also usable as the ``@theorem`` decorator.
theorem_theory = TheoremTheory()
registry.register_theory(theorem_theory)


def theorem(fn: Any) -> Theorem:
    """Turn a typed function into a :class:`Theorem` and register it.

    Parameters annotated with sorts are the variables, parameters annotated with
    propositions are the hypotheses, and the return annotation is the goal.
    """
    return theorem_theory(fn)
