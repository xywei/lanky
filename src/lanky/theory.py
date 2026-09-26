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

Two more things are said the same way. ``@axiom(cite=...)`` states a result
lanky takes on a citation rather than establishes: its fact is ``assumed``,
with the citation in its provenance, and no oracle is asked to establish it,
though the property tester still looks for a counterexample to it as written.
And ``@theorem(uses=[...])`` names the facts a theorem rests on, which the
ledger counts when it says what the theorem is worth (see
:meth:`lanky.ledger.Ledger.support`): a theorem proved from an axiom is proved
*under* that axiom.
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
from lanky.terms import (
    Forall,
    LogicalAnd,
    Var,
    evaluate,
    evaluate_annotations,
    render,
    truth_value,
)
from lanky.testing import Table, TestReport, check

__all__ = ["Axiom", "Theorem", "TheoremTheory", "Verdict", "axiom", "fact_ids", "theorem"]


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


def fact_ids(uses: Any) -> tuple[str, ...]:
    """The fact ids a ``uses=`` argument names, in order and without repeats.

    Each entry is a fact id, a :class:`~lanky.ledger.Fact`, or an object that
    names one fact through a string ``fact_id``, as a :class:`Theorem` and an
    :class:`Axiom` do. A single entry need not be wrapped in a list, and
    ``None`` names nothing. An id is a string, so a plugin's fact is named the
    same way: loopty's scan postcondition is ``"scan:postcondition"``.

    Raises:
        TypeError: For anything else, such as a plugin's decorated object that
            owns several facts, which would leave open which one is meant.
    """
    if uses is None:
        return ()
    if isinstance(uses, str | Fact) or isinstance(getattr(uses, "fact_id", None), str):
        uses = (uses,)
    try:
        entries = list(uses)
    except TypeError:
        raise TypeError(
            f"uses= names facts: a theorem, an axiom, a Fact or a fact id, or a "
            f"list of them; got {uses!r}"
        ) from None
    out: list[str] = []
    for entry in entries:
        if isinstance(entry, str):
            name = entry
        elif isinstance(entry, Fact):
            name = entry.id
        elif isinstance(getattr(entry, "fact_id", None), str):
            name = entry.fact_id
        else:
            raise TypeError(
                f"uses= names facts: a theorem, an axiom, a Fact or a fact id; "
                f"{entry!r} is none of them (an object that owns several facts is "
                "named by the id of the one meant)"
            )
        if name not in out:
            out.append(name)
    return tuple(out)


class Theorem:
    """A statement read off a typed Python function.

    Attributes:
        variables: ``(name, type)`` pairs, in signature order, so a size comes
            before the domains that mention it.
        hypotheses: ``(name, proposition)`` pairs.
        goal: The return annotation, as a term.
        uses: The ids of the facts the statement rests on, from ``uses=``
            (see :func:`fact_ids`). They go into its fact's ``rests_on``. No
            oracle is handed the statements they name: what ``uses=`` records
            is what the theorem is worth, not a hypothesis for its proof.

    Raises:
        TypeError: If the function has no return annotation (or ``-> None``).
            A theorem needs a goal. Without one it used to read as ``True``
            when it was called or tested and as ``assumed`` in the ledger,
            where no oracle takes a fact with no term, so one statement had
            two answers; it is refused where it is written instead.
    """

    #: What the statement is called in messages, in its fact's kind and id.
    noun = "theorem"

    def __init__(self, fn: Any, *, uses: Any = ()) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        self.uses = fact_ids(uses)
        annotations = evaluate_annotations(fn)
        self.goal = annotations.pop("return", None)
        if self.goal is None:
            code = fn.__code__
            article = "an" if self.noun[0] in "aeiou" else "a"
            raise TypeError(
                f"{getattr(fn, '__qualname__', fn.__name__)} at "
                f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}: "
                f"{article} {self.noun} needs a goal; write the proposition it "
                "claims as the return annotation, as in `-> n + 0 == n`"
            )
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
        goal = render(self.goal)
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
            TypeError: If a hypothesis or the goal, or any proposition inside
                one (an operand of ``&``, ``|`` or ``~``, the body of a
                quantifier), evaluates to something other than a truth value
                (:func:`lanky.terms.truth_value`): such a statement claims
                nothing, and the property tester refuses it the same way.
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
                name: truth_value(evaluate(prop, context), prop)
                for name, prop in self.hypotheses
            },
            goal=truth_value(evaluate(self.goal, context), self.goal),
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
        return fact_id(self.noun, self.qualname, module=self.module, line=self.line)

    def fact(self) -> Fact:
        """This theorem as a ledger entry, before any oracle has seen it."""
        return Fact(
            id=self.fact_id,
            kind=self.noun,
            statement=self.statement,
            term=self.term,
            status=Status.ASSUMED,
            decided_by=None,
            provenance={"path": self.path, "line": self.line},
            where=self.where,
            owner=self.qualname,
            rests_on=self.uses,
        )

    def lean(self) -> str:
        """The statement in Lean 4 syntax, when the printer supports it."""
        from lanky.lean import print_lean

        return print_lean(self.term)

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<{self.noun} {self.__name__}: {self.statement}>"


class Axiom(Theorem):
    """A statement taken on a citation: read like a theorem, and never established.

    An axiom is how a result lanky cannot establish enters the ledger on the
    word of a reference, such as a jump relation taken from a textbook. It is
    written like a theorem and read the same way, and its fact differs in
    three things: its kind is ``"axiom"``, its status stays ``assumed``, and
    its provenance carries the citation as ``cite``. No oracle is asked to
    establish it, since the point of an axiom is that its author vouches for
    it, and a theorem that ``uses`` it is established *under* it in the
    ledger.

    It is still a statement, so it can still be run and still be refuted:
    calling it evaluates it at concrete values, the pytest plugin samples it
    as it samples a theorem, and ``lanky check`` has the property tester look
    for a counterexample (see :func:`lanky.check.establish`). That is where a
    citation copied down wrong shows up, and a refuted axiom fails the check
    like any refuted fact.

    Attributes:
        cite: The citation, as given.

    Raises:
        TypeError: If the citation is missing, empty, or not a string. An
            axiom with no citation is a claim with nothing behind it, which is
            what an ``assumed`` theorem already is.
    """

    noun = "axiom"

    def __init__(self, fn: Any, *, cite: Any, uses: Any = ()) -> None:
        name = getattr(fn, "__qualname__", None) or getattr(fn, "__name__", None) or repr(fn)
        self.cite = _citation(name, cite)
        super().__init__(fn, uses=uses)

    def fact(self) -> Fact:
        """This axiom as a ledger entry: ``assumed``, with its citation."""
        fact = super().fact()
        return fact.with_status(Status.ASSUMED, cite=self.cite)


def _citation(name: str, cite: Any) -> str:
    """The citation an axiom was given, or ``TypeError`` saying how to give one."""
    if cite is None:
        raise TypeError(
            f"{name}: an axiom needs a citation, the reference its author takes it "
            'on; write @axiom(cite="...") above it'
        )
    if not isinstance(cite, str):
        raise TypeError(f"{name}: an axiom's citation is a string, not {cite!r}")
    if not cite.strip():
        raise TypeError(f"{name}: an axiom's citation is empty; name the reference")
    return cite


class TheoremTheory:
    """The built-in theory: ``@theorem`` and ``@axiom`` over typed Python functions."""

    name = "theorem"

    def __call__(self, obj: Any, /) -> Theorem:
        """Decorate ``obj`` as a theorem and register it."""
        return registry.register_object(Theorem(obj))

    def facts(self, obj: Any, /) -> tuple:
        """The one fact a theorem or an axiom claims, or nothing for an object it does not own."""
        return (obj.fact(),) if isinstance(obj, Theorem) else ()


#: The theory itself, also usable as the ``@theorem`` decorator.
theorem_theory = TheoremTheory()
registry.register_theory(theorem_theory)


def theorem(fn: Any = None, /, *, uses: Any = ()) -> Any:
    """Turn a typed function into a :class:`Theorem` and register it.

    Parameters annotated with sorts are the variables, parameters annotated with
    propositions are the hypotheses, and the return annotation is the goal.

    Written bare, ``@theorem``, or with the facts the theorem rests on,
    ``@theorem(uses=[jump, compact])``: theorems, axioms, facts or fact ids
    (see :func:`fact_ids`), which become its fact's ``rests_on``. A bad entry
    is refused where the decorator is written, not when the file is checked.
    """
    rests_on = fact_ids(uses)

    def decorate(fn: Any) -> Theorem:
        return registry.register_object(Theorem(fn, uses=rests_on))

    return decorate if fn is None else decorate(fn)


def axiom(fn: Any = None, /, *, cite: Any = None, uses: Any = ()) -> Any:
    """Take a typed function as an :class:`Axiom`, on a citation, and register it.

    Written ``@axiom(cite="Kress, Linear Integral Equations, ch. 6")``;
    ``uses=`` works as it does for :func:`theorem`. The statement is read as a
    theorem's is, and its fact is ``assumed``, with the citation in its
    provenance, unless the property tester finds a counterexample to it.

    Raises:
        TypeError: When the citation is missing, which is what ``@axiom``
            written bare amounts to, or empty.
    """
    if fn is not None:
        return registry.register_object(Axiom(fn, cite=cite, uses=uses))
    _citation("@axiom", cite)
    rests_on = fact_ids(uses)

    def decorate(fn: Any) -> Axiom:
        return registry.register_object(Axiom(fn, cite=cite, uses=rests_on))

    return decorate
