"""``@claim``: a typed Python function is a statement.

The design idea. A claim needs no syntax of its own. Its variables are the
parameters annotated with sorts, its conditions are the parameters annotated
with propositions, and its goal is the return annotation. Annotations are
evaluated, not parsed, so ``Fn[Fin[n + 1], Nat]`` and
``all(off(r + 1) == off(r) + cnt(r) for r in Fin[n])`` are ordinary Python
expressions that happen to build terms.

The decorator is inert and registering: it returns a :class:`Claim` that runs
natively (evaluating the statement at concrete values, and sampling it as a
property test) and records itself in :data:`lanky.plugins.registry`, so that
``lanky check`` only has to import the file. The body is the proof: a body
that holds only a docstring, ``...`` or ``pass`` leaves the proof to lanky,
and any other is a written proof, which ``lanky check`` traces after every
run and draw of the check and has Lean check (:mod:`lanky.proofs`). Running
the file never calls the body.

Two more things are said the same way. ``@claim(cite=...)`` states a result
lanky takes on a source rather than establishes: its fact is ``assumed``,
with the source in its provenance, and no oracle is asked to establish it,
though the property tester still looks for a counterexample to it as written.
And ``@claim(uses=[...])`` names the facts a claim rests on, which the ledger
counts when it says what the claim is worth (see
:meth:`lanky.ledger.Ledger.support`): a claim proved from a cited one is
proved *under* it.

A claim is asked at values with parentheses, ``gauss(n=4)``: natively the
answer is ``True`` or ``False``, and where one of its conditions fails there
the question does not apply, and :class:`~lanky.conditions.ConditionNotMet`
says which. In an annotation the call is the claim's statement at those
values. lanky 0.5's ``@theorem`` and ``@axiom`` are refused, with the line to
write.
"""

from __future__ import annotations

import ast
import builtins
import functools
import inspect
import os
import sys
from collections.abc import Mapping
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

from lanky.check import module_name
from lanky.conditions import (
    Assuming,
    Condition,
    ConditionNotMet,
    Conditions,
    _call_arguments,
    _holds_term,
)
from lanky.ledger import Fact, Status, fact_id
from lanky.plugins import registry
from lanky.prelude import FinType, FnType, Refined, SumType
from lanky.terms import (
    BuiltinName,
    Exists,
    Forall,
    LogicalAnd,
    Sum,
    Var,
    conjuncts,
    evaluate,
    evaluate_annotations,
    init_args,
    render,
    truth_value,
)
from lanky.testing import Table, TestReport, apply_at, check

__all__ = [
    "Axiom",
    "CitedClaim",
    "Claim",
    "ClaimTheory",
    "Theorem",
    "TheoremTheory",
    "axiom",
    "claim",
    "fact_ids",
    "theorem",
]


def _module_of(fn: Any) -> str:
    """The module a definition's fact id names: the one its file's path gives it.

    That is :func:`lanky.check.module_name` of the file the function's code
    was compiled from, which is the same whether the file was checked
    directly or imported by another, and ``__module__`` only for a function
    with no file behind it, such as one compiled from a string.
    """
    code = getattr(fn, "__code__", None)
    derived = module_name(code.co_filename) if code is not None else None
    return derived or getattr(fn, "__module__", "") or ""


def fact_ids(uses: Any) -> tuple[str, ...]:
    """The fact ids a ``uses=`` argument names, in order and without repeats.

    Each entry is a fact id, a :class:`~lanky.ledger.Fact`, or an object that
    names one fact through a string ``fact_id``, as a :class:`Claim` and a
    :class:`~lanky.conditions.Condition` do. A single entry need not be wrapped in a list, and an
    empty list names nothing. An id is a string, so a plugin's fact is named
    the same way: the postcondition of loopty's ``scan`` in ``spmv.py`` is
    ``"postcondition:spmv.scan@69"``, keyed as a claim's is (see
    :func:`lanky.ledger.fact_id`).

    Raises:
        TypeError: For anything else, such as a plugin's decorated object that
            owns several facts, which would leave open which one is meant, or
            ``None``, which is what a name bound to nothing by mistake holds:
            a claim that uses nothing leaves ``uses=`` out.
    """
    if uses is None:
        raise TypeError(
            "uses=None names no fact, which is what a name bound to nothing by "
            "mistake holds; a statement that uses nothing leaves uses= out"
        )
    if isinstance(uses, str | Fact) or isinstance(getattr(uses, "fact_id", None), str):
        uses = (uses,)
    try:
        entries = list(uses)
    except TypeError:
        raise TypeError(
            f"uses= names facts: a claim, a Fact or a fact id, or a list of them; "
            f"got {uses!r}"
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
                f"uses= names facts: a claim, a Fact or a fact id; "
                f"{entry!r} is none of them (an object that owns several facts is "
                "named by the id of the one meant)"
            )
        if name not in out:
            out.append(name)
    return tuple(out)


def _as_family(value: Any, sort: Any, name: str) -> Any:
    """A value given for a parameter, with a sequence given for a family read as a table.

    A family with several indices, ``Fn[A, B, C]``, is a family of families,
    so a nested sequence, or an array of as many dimensions, is a table of
    tables, each row read the same way: ``F[i, j]`` and ``F(i)(j)`` then
    both reach an entry. A function is applied at all of the indices at once
    or one at a time, as it takes them (:class:`_Function`), whichever way the
    statement writes the entry. A table, or anything else that is both called
    and indexed, is taken as it is, and so is anything given for a parameter
    that is not a family.

    Raises:
        TypeError: If the value has another shape than the family: a
            mapping, a single value, a flat list for a matrix, or a nested
            list or array with more levels than the family has indices. The
            message names the parameter, its type and the shape it takes.
    """
    while isinstance(sort, Refined):
        sort = sort.base
    if not isinstance(sort, FnType):
        return value
    shape = _Shape(name, sort)
    return _as_table(value, sort, shape, name)


@dataclass(frozen=True)
class _Shape:
    """A family parameter, as the messages about a value of the wrong shape name it."""

    name: str
    sort: FnType

    def wanted(self) -> str:
        """What the parameter takes, in a message."""
        count = len(self.sort.indices)
        if count == 1:
            return f"a list, {self.name}=[...], an array with one axis, or a function"
        return (
            f"nested lists, one level per index, {self.name}=[[...], [...]], an array "
            f"with {count} axes, or a function"
        )

    def __str__(self) -> str:
        """``F, a family with 2 indices (Fn[Fin(n), Fin(n), Real])``."""
        count = len(self.sort.indices)
        indices = "one index" if count == 1 else f"{count} indices"
        return f"{self.name}, a family with {indices} ({self.sort})"


def _as_table(value: Any, sort: FnType, shape: _Shape, at: str) -> Any:
    """``value``, the part ``at`` of the parameter, as a family of type ``sort``.

    ``at`` is ``F`` and then ``F[0]``, ``F[0][1]``: the part of the value
    being read, which a message names.
    """
    if callable(value):
        if callable(getattr(value, "__getitem__", None)):
            return value  # a table, or a family of a plugin's
        return _Function(value, len(sort.indices), at)
    if isinstance(value, (Mapping, str, bytes)) or not _iterable(value):
        raise TypeError(
            f"{at} is {_short(value)}, where {shape}, needs "
            f"{'a family' if at == shape.name else 'a row'}: give {shape.name} as "
            f"{shape.wanted()}"
        )
    inner = sort.codomain
    while isinstance(inner, Refined) and isinstance(inner.base, FnType):
        inner = inner.base
    rows = []
    for index, item in enumerate(value):
        where = f"{at}[{index}]"
        if isinstance(inner, FnType):
            rows.append(_as_table(item, inner, shape, where))
        elif _iterable(item) and not isinstance(item, (str, bytes)):
            raise TypeError(
                f"{where} is {_short(item)}, where {shape}, has an entry: the value "
                f"has more levels than {shape.name} has indices; give {shape.name} as "
                f"{shape.wanted()}"
            )
        else:
            rows.append(item)
    return Table(rows, name=at)


def _iterable(value: Any) -> bool:
    """Whether ``value`` can be iterated: a list, a tuple, an array of one axis or more."""
    if getattr(value, "ndim", 1) == 0:
        return False
    try:
        iter(value)
    except TypeError:
        return False
    return True


def _short(value: Any) -> str:
    """A value as a message names it, cut short."""
    if isinstance(value, Mapping):
        return "a dict"
    text = repr(value)
    return text if len(text) <= 40 else f"{text[:37]}..."


class _Function:
    """A Python function given for a family, applied as the statement writes the entry.

    ``F[i, j]``, ``F(i, j)`` and ``F(i)(j)`` are one entry of a family with
    two indices, and a function given for it may take both indices at once,
    ``lambda i, j: ...``, or one at a time, ``lambda i: lambda j: ...``.
    The indices are collected until there are as many as the family has,
    and the function is then called as it takes them: at all of them at once
    if its signature admits that many, else at one after another.
    """

    def __init__(self, fn: Any, count: int, name: str, given: tuple[Any, ...] = ()) -> None:
        self.fn, self.count, self.name, self.given = fn, count, name, given

    def _at(self, index: Any) -> Any:
        """The function at one more index: a row until every index is given."""
        given = (*self.given, index)
        if len(given) < self.count:
            return _Function(self.fn, self.count, self.name, given)
        if _takes(self.fn, len(given)):
            return self.fn(*given)
        value = self.fn(given[0])
        for later in given[1:]:
            value = value(later) if callable(value) else value[later]
        return value

    def __call__(self, *indices: Any) -> Any:
        """The value at ``indices``: ``f(i)``, ``f(i, j)``, or a row for fewer."""
        return apply_at(self._at, indices, self.name)

    def __getitem__(self, index: Any) -> Any:
        """The same as a call: ``f[i, j]`` is ``f(i, j)``."""
        return apply_at(self._at, index if isinstance(index, tuple) else (index,), self.name)

    def __repr__(self) -> str:
        """Print as the function, with the indices given so far."""
        return f"{self.fn!r}" + "".join(f"[{index!r}]" for index in self.given)


def _takes(fn: Any, count: int) -> bool:
    """Whether ``fn`` can be called with ``count`` positional arguments, as far as Python says."""
    try:
        inspect.signature(fn).bind(*range(count))
    except TypeError:
        return False
    except ValueError:  # no signature to read, as for some builtins: call it at all of them
        return True
    return True


class Claim(Assuming):
    """A statement read off a typed Python function: its variables, its conditions, its goal.

    Attributes:
        variables: ``(name, type)`` pairs, in signature order, so a size comes
            before the domains that mention it. Those of what the claim holds
            under come first, then the sorts a condition used as a hypothesis
            brings (``ok: cfl(c, dt, h)`` brings ``c``, ``dt`` and ``h`` with
            cfl's sorts), then the claim's own.
        hypotheses: ``(name, proposition)`` pairs: the named conditions.
        goal: The return annotation, as a term.
        uses: The ids of the facts the statement rests on, from ``uses=``
            (see :func:`fact_ids`), and a whole claim's that a ``with`` block
            assumes. They go into its fact's ``rests_on``. No oracle is
            handed the statements they name: what ``uses=`` records is what
            the claim is worth, not a hypothesis for its proof.
        under: What the claim holds under, outermost first
            (:class:`lanky.conditions.Under`): the ``with`` blocks it is
            defined in.
        bound: The names those blocks put in its statement, which its
            annotations and body read from its namespace, not as parameters.
        snapshot: What the annotations reach, copied just before they were
            read (:func:`lanky.faithful.capture`): the names they read, the
            functions of the user's modules they call, bound to the copy,
            and what those read and close over, tables, lists and arrays
            included. The faithfulness check runs the annotations again in a
            copy of it at each draw (:meth:`faithful_fact`), so a module that
            rebinds a name later, or changes a table in place, does not
            change what the annotation said; what could not be copied is
            listed, and leaves the reading untested.
        namespace: The function's globals as they were when the annotations
            were read, the snapshot's (:attr:`lanky.faithful.Snapshot.namespace`).

    Raises:
        TypeError: If the function has no return annotation (or ``-> None``):
            a claim needs a goal, and a named set of assumptions with no goal
            is a ``@condition``, which the refusal says. And if a parameter or
            the goal is annotated with a builtin of Python's, ``x: int``, or
            names one anywhere in its annotation without calling it, ``f:
            Fn[Fin[n], float]`` (see :func:`_refuse_a_builtin_annotation`).
            And if an annotation reads ``all``, ``any``, ``sum`` or ``abs``,
            which no parameter is named, and the module binds that name to
            something other than Python's builtin or lanky's own, which lanky
            would read in its place (see
            :func:`lanky.terms.evaluate_annotations`, #100).
    """

    #: What the statement is called in messages, and the first word of its id.
    noun = "claim"

    #: The kind of its fact.
    kind = "claim"

    #: What a refusal of ``with`` calls its parts.
    what = "variables and conditions"

    def __init__(self, fn: Any, *, uses: Any = ()) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        given = fact_ids(uses)
        from lanky.conditions import in_force
        from lanky.faithful import capture

        self.under = in_force()
        bound = _bound_values(self.under)
        parts = [name for entry in self.under for name in entry.parts]
        self.bound = tuple(dict.fromkeys((*bound, *parts)))
        rests = [fact for entry in self.under for fact in entry.condition.rests_on]
        self.uses = tuple(dict.fromkeys((*given, *rests)))
        _refuse_a_bound_parameter(fn, self.under)
        #: Each hypothesis written as a call of a condition, ``ok: cfl(c, dt, h)``,
        #: by its name: the text as written, which the statement prints.
        self.written: dict[str, str] = {}
        brought = _brought_sorts(fn, self.bound, self.written)
        #: The variables a condition used as a hypothesis brings, with its sorts.
        self.brought = tuple(brought)
        _refuse_a_name_bound_elsewhere(fn, {**bound, **dict(brought)})
        # taken before the annotations are read, which may run a helper that
        # changes what it reads
        self.snapshot = capture(fn, bound=(*self.bound, *(name for name, _ in brought)))
        self.namespace = self.snapshot.namespace
        annotations = evaluate_annotations(fn, bound or None)
        self.goal = annotations.pop("return", None)
        if self.goal is None:
            code = fn.__code__
            raise TypeError(
                f"{getattr(fn, '__qualname__', fn.__name__)} at "
                f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}: "
                f"a {self.noun} needs a goal; write the proposition it claims as the "
                "return annotation, as in `-> n + 0 == n`. A named set of assumptions "
                "with no goal is a @condition"
            )
        variables, hypotheses = _condition_parts(self.under)
        variables += [(name, sort) for name, sort in brought if name not in dict(variables)]
        _refuse_a_builtin_annotation(fn, "return", self.goal)
        for name, annotation in annotations.items():
            _refuse_a_builtin_annotation(fn, name, annotation)
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
        self.module = _module_of(fn)
        self._faithful: Fact | None = None
        self._conditions = Conditions(self)

    # {{{ the statement

    def _shown(self, name: str, prop: Any) -> str:
        """A hypothesis as the statement prints it: as written for a condition's call."""
        return self.written.get(name) or render(prop)

    @property
    def statement(self) -> str:
        """The statement as a sequent: variables, hypotheses, then the goal.

        A claim defined in a ``with`` block says so first, by what it holds
        under and its named conditions, and then states its own variables and
        hypotheses, as the file does: ``under away_from_zero (nonzero): a :
        Fn[Nat, Complex] | ... |- ...``. A hypothesis that calls a condition
        is printed as it is written, ``cfl(c, dt, h)``.
        """
        variables = ", ".join(f"{name} : {sort}" for name, sort in self.own_variables)
        hypotheses = ", ".join(self._shown(name, prop) for name, prop in self.own_hypotheses)
        parts = [variables] if variables else []
        if hypotheses:
            parts.append(hypotheses)
        head = " | ".join(parts)
        goal = render(self.goal)
        said = f"{head} |- {goal}" if head else goal
        return f"under {self.under_label}: {said}" if self.under else said

    @property
    def sequent(self) -> dict[str, Any]:
        """The parts of :attr:`statement`, as text: variables, named hypotheses, goal.

        The variables and the hypotheses are all of them, those of what the
        claim holds under first, so that a reader pairing each hypothesis
        with a conjunct of the term's guard pairs them all. Under a
        condition, ``under`` names it as the statement does, and ``own``
        holds the claim's own variables and hypotheses, which the ledger
        prints after it.
        """
        sequent: dict[str, Any] = {
            "variables": ", ".join(f"{name} : {sort}" for name, sort in self.variables),
            "hypotheses": [[name, self._shown(name, prop)] for name, prop in self.hypotheses],
            "goal": render(self.goal),
        }
        if self.under:
            sequent["under"] = self.under_label
            sequent["own"] = {
                "variables": ", ".join(f"{name} : {sort}" for name, sort in self.own_variables),
                "hypotheses": [
                    [name, self._shown(name, prop)] for name, prop in self.own_hypotheses
                ],
            }
        return sequent

    @property
    def own_variables(self) -> tuple[tuple[str, Any], ...]:
        """The variables the claim declares itself, without those of what it holds under."""
        return tuple((name, sort) for name, sort in self.variables if name not in self.bound)

    @property
    def own_hypotheses(self) -> tuple[tuple[str, Any], ...]:
        """The hypotheses the claim declares itself, without those of what it holds under."""
        return tuple((name, prop) for name, prop in self.hypotheses if name not in self.bound)

    @property
    def conditions(self) -> Conditions:
        """The claim's own conditions, the half before its goal.

        A :class:`~lanky.conditions.Conditions`:
        ``line_taylor.conditions.ode`` is one of them, and ``with
        line_taylor.conditions as (a, first_term, ode):`` assumes them all.
        """
        return self._conditions

    @property
    def held_under(self) -> tuple[Any, ...]:
        """What the claim holds under, outermost first: conditions, claims' conditions, claims."""
        return tuple(entry.condition for entry in self.under)

    # {{{ the tree: name.conclusion (name.conditions is above)

    @property
    def conclusion(self) -> Any:
        """The half of the claim it concludes: ``.domain``, and ``[p]`` at a point of it.

        See :class:`lanky.surface.Conclusion`. Inside the claim's own proof it
        is the conclusion for that proof's inputs: ``for n in
        line_taylor.conclusion.domain:`` loops over its points, and
        ``line_taylor.conclusion[n - 1]`` is the conclusion at an earlier one.
        """
        from lanky.surface import Conclusion

        return Conclusion(self)

    @property
    def domain(self) -> Any:
        """Refused: a claim has no domain of its own; its conclusion has (the tree's spelling)."""
        raise self._not_on_the_tree(".domain", "conclusion.domain")

    @property
    def dom(self) -> Any:
        """Refused: ``.dom`` is spelled ``.conclusion.domain``."""
        raise self._not_on_the_tree(".dom", "conclusion.domain")

    def __getitem__(self, point: Any) -> Any:
        """Refused: a claim has no points of its own; its conclusion has (the tree's spelling)."""
        from lanky.surface import _shown

        values = point if isinstance(point, tuple) else (point,)
        shown = ", ".join(_shown(value) for value in values)
        raise self._not_on_the_tree(f"[{shown}]", f"conclusion[{shown}]")

    #: A claim is not iterated: ``__getitem__`` only refuses, and Python's
    #: fallback from ``iter`` to it would make every claim look iterable.
    __iter__ = None

    def _not_on_the_tree(self, written: str, spelled: str) -> Exception:
        """The refusal of ``name.domain`` or ``name[p]``, with the part of the tree meant."""
        from lanky.surface import FormError

        name = self.qualname
        return FormError(
            f"{name}{written}: a claim has no {'points' if written.startswith('[') else 'domain'} "
            f"of its own; its conclusion has, addressed through the claim's tree as "
            f"{name}.{spelled}",
            f"{name}.{spelled}",
        )

    # }}}

    @property
    def under_label(self) -> str:
        """``away_from_zero (nonzero)``: what it holds under, as its statement says; or ``""``."""
        from lanky.conditions import under_label

        return under_label(self.under)

    @property
    def cited_under(self) -> str:
        """``under away_from_zero``: what a row citing the claim says of its conditions; or ``""``.

        A row that applies the claim, or names it as the reason of a step,
        puts it after the claim's name: ``by line_taylor under
        away_from_zero``.
        """
        if not self.under:
            return ""
        return "under " + ", ".join(entry.condition.__name__ for entry in self.under)

    @property
    def hypothesis_names(self) -> tuple[str, ...]:
        """A name for each conjunct of the term's guard: the parameter's, as Python has it.

        ``pde``, ``stored`` and ``recurrence`` are what the Lean theorem calls
        its hypotheses (:func:`lanky.lean.statement_of`), so that the printed
        theorem, and a proof that cites a hypothesis, read as the file does.
        A hypothesis written ``p & q`` is two conjuncts of the guard, which
        are its name with ``_1`` and ``_2`` after it, ``stored_1`` and
        ``stored_2``; a name another parameter already has gets ``_`` after
        it until it is its own.
        """
        taken = {name for name, _ in self.variables} | {name for name, _ in self.hypotheses}
        names: list[str] = []
        for name, prop in self.hypotheses:
            parts = conjuncts(prop)
            if len(parts) == 1:
                names.append(name)
                continue
            for index in range(1, len(parts) + 1):
                part = f"{name}_{index}"
                while part in taken:
                    part += "_"
                taken.add(part)
                names.append(part)
        return tuple(names)

    @property
    def term(self) -> Any:
        """The statement as one closed term: the goal under its binders and guard.

        The variables become the binders and the hypotheses the guard, which is
        exactly the shape an oracle wants: for all values of the variables
        satisfying the hypotheses, the goal.

        A claim with hypotheses and no sort-valued parameters still has a
        guard, and the binder tuple is then empty rather than the whole
        :class:`~lanky.terms.Forall` being dropped. Dropping it would hand the
        oracles the bare goal, which is a different and stronger claim: the
        hypotheses are what make an implication with a false antecedent valid,
        and without them such a claim is refuted by its own hypothesis.

        With neither binders nor a guard the binder tuple is empty too, and
        the term is still a :class:`~lanky.terms.Forall`, whose body is the
        goal (#35). Every reader of a term takes a ``Forall`` apart into
        variables, hypotheses and goal, so the goal itself handed over as the
        term was taken apart in its place when it was a universal:
        ``-> all(k >= 0 for k in Nat if k > 100)`` had ``k`` read as the
        statement's variable and its guard as the statement's hypotheses, so
        the ledger warned about hypotheses the claim does not have, while
        :meth:`report`, which hands the oracle the goal as a goal, read the
        same claim as a goal whose guard no draw passed. The empty binders
        print as nothing, in the ledger and in Lean, so a statement reads as
        it always did.

        A closed statement such as ``-> 1 == 2`` is the exception: its goal
        is a concrete ``bool`` rather than a term, and the term is that
        ``bool``. That is a fact like any other: the property-test oracle
        takes a ``bool`` and answers ``TESTED`` or ``REFUTED``.
        """
        binders = tuple((Var(name), sort) for name, sort in self.variables)
        guard: Any = None
        props = [prop for _, prop in self.hypotheses]
        if len(props) == 1:
            guard = props[0]
        elif props:
            guard = LogicalAnd(tuple(props))
        if not binders and guard is None and not isinstance(self.goal, prim.ExpressionNode):
            return self.goal
        return Forall(binders, self.goal, guard)

    # }}}

    # {{{ as what a with statement assumes

    @property
    def names(self) -> tuple[str, ...]:
        """The claim's parameters, in its signature's order: what ``with name as (...)`` binds."""
        return tuple(inspect.signature(self.fn).parameters)

    @property
    def assumed_variables(self) -> tuple[tuple[str, Any], ...]:
        """What ``with line_taylor as (...)`` puts in each claim's statement: its variables."""
        return self.own_variables

    @property
    def assumed_hypotheses(self) -> tuple[tuple[str, Any], ...]:
        """Its conditions, and its goal, under its own name."""
        return (*self.own_hypotheses, (self.__name__, self.goal))

    @property
    def required(self) -> tuple[Any, ...]:
        """What the claim holds under itself, which has to be in force to assume it."""
        return self.held_under

    @property
    def rests_on(self) -> tuple[str, ...]:
        """A claim built on this one, by ``with``, rests on it: ``under line_taylor``."""
        return (self.fact_id,)

    @property
    def source_fn(self) -> Any:
        """The function its annotations are read from."""
        return self.fn

    @property
    def annotation_keys(self) -> dict[str, str]:
        """Each part's annotation: a parameter's own, and the goal's for the claim's name."""
        return {**{name: name for name in self.names}, self.__name__: "return"}

    @property
    def world_parameters(self) -> tuple[str, ...]:
        """Its parameters and what its own ``with`` blocks bound, drawn where it is read again."""
        return (*self.names, *self.bound)

    @property
    def label(self) -> str:
        """``line_taylor``: a claim built on it reads ``under line_taylor``."""
        return self.__name__

    @property
    def signature(self) -> str:
        """``line_taylor(a: Fn[Nat, Complex], first_term: ..., ode: ...)``, as written."""
        from lanky.conditions import signature_text

        return signature_text(self.fn, self.names, self.__name__)

    # }}}

    # {{{ asked at values

    def __call__(self, *values: Any, **concrete: Any) -> Any:
        """The claim for given inputs: natively whether it holds; in an annotation, the statement.

        The inputs are the claim's variables, by position or by name:
        ``gauss(4)`` or ``gauss(n=4)``, those of what it holds under first.
        Inside a ``with`` block of what it holds under, the block gives those,
        and the call gives the claim's own: ``line_taylor(c)``. A value for a
        family parameter may be given as a sequence, which is read as a
        table, and one for a family with several indices as nested
        sequences or an array, ``F=[[1, 2], [3, 4]]`` for ``F: Fn[Fin[2],
        Fin[2], Nat]``.

        Natively the answer is ``True`` or ``False``: whether the goal holds
        at these values. Where one of the claim's conditions fails, the
        question does not apply, and :class:`~lanky.conditions.ConditionNotMet`
        names the condition. Where a value is symbolic, as in an annotation,
        the answer is the claim's statement at those values, its conditions
        then its goal, which a hypothesis or a goal reads as a proposition.
        Calling a claim evaluates its statement; it never runs its proof
        (:meth:`run_proof` does).

        Inside a written proof (:mod:`lanky.proofs`), which only ``lanky
        check`` runs, calling a claim is citing it for those inputs, its
        parameters, positional or by name (``gauss(n - 1)``); its
        conclusion's point, where it has one, is lanky's to find, or given
        in brackets, ``other(x).conclusion[p]``. What decides is whether a
        proof is running, not the arguments' types. Calling a claim never
        runs its proof. A claim that calls itself in its own proof is
        refused: to argue from an earlier case, the variable belongs in the
        conclusion's ``for``, and the earlier case is
        ``name.conclusion[n - 1]``.

        Raises:
            lanky.conditions.ConditionNotMet: Natively, where a condition of
                the claim fails at these values.
            lanky.terms.Undecided: If the statement applies a family outside
                the domain it declares at these values. There is no value to
                compare there, so there is no answer either; the property
                tester drops such a draw for the same reason.
            TypeError: If an input is missing, given twice, or unknown, or a
                value is given for a condition, which the call answers; and if
                a hypothesis or the goal, or any proposition inside one,
                evaluates to something other than a truth value
                (:func:`lanky.terms.truth_value`).
        """
        from lanky.proofs.trace import active

        runner = active()
        if runner is not None:
            frame = sys._getframe(1)
            values = self._block_inputs(runner, values, concrete, frame)
            return runner.cite_theorem(self, values, concrete, frame)
        inputs = _call_arguments(
            self.__name__,
            self.variables,
            self.hypotheses,
            values,
            concrete,
            self._filled_by_block(),
        )
        if any(_holds_term(value) for value in inputs.values()):
            return self._statement_at(inputs)
        return self._answer_at(inputs)

    def _filled_by_block(self) -> dict[str, Any]:
        """The values a ``with`` block running here gives the claim's conditions; ``{}`` else."""
        if not self.under:
            return {}
        from lanky.conditions import in_force

        here = in_force()
        filled: dict[str, Any] = {}
        for entry in self.under:
            running = next((other for other in here if other.condition is entry.condition), None)
            if running is None:
                return {}
            for name, value in running.values:
                if name in dict(entry.condition.assumed_variables):
                    filled.setdefault(name, value)
        return filled

    def _block_inputs(
        self, runner: Any, values: tuple, named: Mapping[str, Any], frame: Any
    ) -> tuple:
        """A sibling's inputs in a proof under the same conditions: the block's, then the call's.

        Inside the proof of a claim that holds under what this one holds
        under, the block's names fill this claim's conditions' variables, at
        the values the proof reads them at (symbolic in a trace, drawn in a
        native run), and the call gives the claim's own inputs only.

        Raises:
            TypeError: Where the call gives one of the block's names too.
        """
        proving = getattr(runner, "theorem", None)
        if proving is None or proving is self or not self.under:
            return values
        theirs = [entry.condition for entry in getattr(proving, "under", ())]
        if not all(any(entry.condition is other for other in theirs) for entry in self.under):
            return values
        block = [name for name, _ in self.variables if name in self.bound]
        own = ", ".join(name for name, _ in self.own_variables) or "none"
        where = ", ".join(entry.condition.__name__ for entry in self.under)
        fills = tuple(frame.f_globals.get(name, Var(name)) for name in block)
        given_block = [name for name in named if name in block]
        repeated = len(values) >= len(fills) > 0 and all(
            value is fill for value, fill in zip(values, fills, strict=False)
        )
        if given_block or repeated:
            raise TypeError(
                f"inside with {where}, {self.__name__} takes its own inputs, {own}; "
                f"{', '.join(block)} are the block's, and come from it: give "
                f"{self.__name__} its own inputs only"
            )
        return (*fills, *values)

    def _answer_at(self, inputs: Mapping[str, Any]) -> bool:
        """Whether the goal holds at concrete ``inputs``, its conditions holding there."""
        from lanky.terms import rerunning

        sorts = dict(self.variables)
        context = {
            name: _as_family(value, sorts.get(name), name) for name, value in inputs.items()
        }
        if rerunning():
            # the statement as a proposition, read where the faithfulness check
            # runs an annotation that calls the claim
            for _name, prop in self.hypotheses:
                if not truth_value(evaluate(prop, context), prop):
                    return True
            return truth_value(evaluate(self.goal, context), self.goal)
        for name, prop in self.hypotheses:
            if not truth_value(evaluate(prop, context), prop):
                raise ConditionNotMet(self._not_met(name, prop), self.__name__, name)
        return truth_value(evaluate(self.goal, context), self.goal)

    def _not_met(self, name: str, prop: Any) -> str:
        """Why the claim does not apply at the values it was asked at."""
        of = next(
            (
                f" of {entry.condition.__name__}"
                for entry in self.under
                if name in dict(entry.condition.assumed_hypotheses)
            ),
            "",
        )
        return (
            f"{self.__name__} does not apply at these values: its condition {name}{of}, "
            f"{self._shown(name, prop)}, fails there"
        )

    def _statement_at(self, inputs: Mapping[str, Any]) -> Any:
        """The statement at symbolic inputs: its goal, under its conditions where it has any."""
        from lanky.induction import substitute

        def put(prop: Any) -> Any:
            return substitute(prop, inputs) if isinstance(prop, prim.ExpressionNode) else prop

        goal = put(self.goal)
        props = [put(prop) for _, prop in self.hypotheses]
        if not props:
            return goal
        guard = props[0] if len(props) == 1 else LogicalAnd(tuple(props))
        return Forall((), goal, guard)

    def run_proof(self, **values: Any) -> None:
        """Run the written proof as plain Python at ``values``, as a REPL or pdb would.

        The values are given by name, as :meth:`__call__` takes them.
        ``name.conclusion.domain`` gives the conclusion's first points, to
        the tester's draw bound, a citation is inert, and ``by(...)`` is read
        only where a step fails. A false step raises Python's own ``AssertionError``, its
        message the step's ``by(...)``; a point where the claim is false
        raises :class:`lanky.proofs.native.PointFalse`. It only tests: Lean
        checks the proof under ``lanky check``. Floats compare exactly here,
        so a step can fail on rounding: give ``Fraction`` values.
        """
        from lanky.proofs.native import run_by_hand

        run_by_hand(self, **values)

    # }}}

    # {{{ property testing

    def report(self, n: int = 200, seed: int = 0) -> TestReport:
        """Sample the statement and report what the draws found.

        Raises:
            lanky.testing.OpenStatement: If the statement mentions a name
                nothing in it binds, a misspelt parameter or sort, which no
                draw gives a value.
        """
        return check(self.variables, [p for _, p in self.hypotheses], self.goal, n, seed)

    def test(self, n: int = 200, seed: int = 0) -> tuple[bool, dict | None]:
        """Property-test the statement: ``(ok, counterexample or None)``.

        A pass here is evidence, not proof, and a pass over zero valid draws is
        not even evidence; :meth:`report` says how many draws the hypotheses
        accepted.

        Raises:
            lanky.testing.OpenStatement: As :meth:`report` does, for a
                statement that mentions a name nothing in it binds.
        """
        report = self.report(n, seed)
        return report.ok, report.counterexample

    # }}}

    @property
    def fact_id(self) -> str:
        """The id this claim's fact carries, unique per definition.

        Two claims can share a qualified name (one per module, or one
        decorator used twice), and a ledger keyed only by that name would keep
        one of them and drop the other. The module and the definition's line
        settle it; :func:`lanky.ledger.fact_id` is the shared builder, so a
        plugin theory can key its own facts the same way.

        The module is the one the file's path gives it
        (:func:`lanky.check.module_name`), not the name it was imported
        under, so the id is the same in the ledger of the claim's own file,
        which ``lanky check`` imports under a name of its own, and in the
        ``uses=`` of a claim in another file that imports it:
        ``claim:helpers.lemma@12`` either way.
        """
        return fact_id(self.noun, self.qualname, module=self.module, line=self.line)

    def fact(self, reading: Fact | None = None) -> Fact:
        """This claim as a ledger entry, before any oracle has seen it.

        ``reading`` is the claim's ``faithful`` fact (:meth:`faithful_fact`),
        which ``lanky check`` passes: its id is recorded as ``faithful``, so
        that :func:`lanky.check.establish` rests a pass, a decision or a proof
        of the claim on it, and when it is refuted, why, as ``unfaithful``, so
        that no oracle is asked about a term that says something else than
        the claim. Without it the fact is the claim alone, as it always was.

        The provenance carries the statement's parts as ``sequent``: the
        variables, each hypothesis with the name of its parameter, and the
        goal, as text, so that the ledger can print a statement too long for
        one line a part to a line (see :func:`lanky.ledger.statement_lines`).
        It carries as ``hypothesis_names`` the name of each conjunct of the
        term's guard (:attr:`hypothesis_names`), which the Lean oracle names
        the theorem's hypotheses by.
        """
        provenance: dict[str, Any] = {
            "path": self.path,
            "line": self.line,
            "sequent": self.sequent,
            "hypothesis_names": list(self.hypothesis_names),
        }
        if self.under:
            provenance["cited_under"] = self.cited_under
        if reading is not None:
            provenance["faithful"] = reading.id
            if reading.status is Status.REFUTED:
                provenance["unfaithful"] = reading.provenance.get("reason") or (
                    "its faithful fact is refuted"
                )
        return Fact(
            id=self.fact_id,
            kind=self.kind,
            statement=self.statement,
            term=self.term,
            status=Status.ASSUMED,
            decided_by=None,
            provenance=provenance,
            where=self.where,
            owner=self.qualname,
            rests_on=self.uses,
        )

    def faithful_fact(self) -> Fact:
        """The claim's ``faithful`` fact: whether the term computes what the annotations do.

        Each annotation is run again as Python at drawn concrete values, and
        the term evaluated there, and the two have to agree (see
        :mod:`lanky.faithful`, #91). The comparison is made once per claim
        and kept.
        """
        if self._faithful is None:
            from lanky.faithful import faithful_fact

            self._faithful = faithful_fact(self)
        return self._faithful

    @property
    def read_names(self) -> tuple[str, ...]:
        """The names its annotations read at drawn values: parameters, the blocks', the brought."""
        return tuple(
            dict.fromkeys(
                (
                    *inspect.signature(self.fn).parameters,
                    *self.bound,
                    *(name for name, _ in self.brought),
                )
            )
        )

    def lean(self, mathlib: bool = False) -> str:
        """The statement in Lean 4 syntax, when the printer supports it.

        ``mathlib=True`` prints it for a Lean that has imported Mathlib, which
        reads ``Real``, ``Complex``, sums and ``exp``, ``log`` and ``sqrt``
        (see :mod:`lanky.lean`). A complex ``log`` or ``sqrt`` means in Lean
        what it means in Python only off its branch cut, which the proposition
        alone does not say: :func:`lanky.lean.statement_of` gives it with the
        side conditions that do, which the Lean oracle proves first.
        """
        from lanky.lean import print_lean

        return print_lean(self.term, mathlib=mathlib)

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<{self.noun} {self.__name__}: {self.statement}>"


def _brought_sorts(
    fn: Any, bound: tuple[str, ...], written: dict[str, str]
) -> list[tuple[str, Any]]:
    """The variables a condition called in a hypothesis brings: ``ok: cfl(c, dt, h)``.

    A hypothesis whose annotation is one call of a :class:`Condition` (or of
    a claim's :class:`~lanky.conditions.Conditions`) is printed as it is
    written, and is recorded in ``written``. Each argument that is a bare
    name the claim does not declare, and no ``with`` block binds, is a
    variable of the claim with the sort the condition gives it there, in the
    order the calls name them, so that ``courant(ok: cfl(c, dt, h)) -> ...``
    needs no ``c: Real``.
    """
    try:
        raw = inspect.get_annotations(fn, eval_str=False)
    except Exception:  # noqa: BLE001 - the reading says what is wrong with them
        return []
    parameters = set(inspect.signature(fn).parameters)
    namespace = getattr(fn, "__globals__", {})
    brought: dict[str, Any] = {}
    for name, annotation in raw.items():
        if name == "return" or not isinstance(annotation, str):
            continue
        try:
            node = ast.parse(annotation.strip(), mode="eval").body
        except SyntaxError:
            continue
        called = _called_condition(node, namespace)
        if called is None:
            continue
        written[name] = " ".join(annotation.split())
        sorts = list(called.assumed_variables)
        given: list[tuple[str, Any]] = []
        for index, argument in enumerate(node.args):
            if index < len(sorts) and isinstance(argument, ast.Name):
                given.append((argument.id, sorts[index][1]))
        by_name = dict(sorts)
        for keyword in node.keywords:
            if keyword.arg in by_name and isinstance(keyword.value, ast.Name):
                given.append((keyword.value.id, by_name[keyword.arg]))
        for variable, sort in given:
            if variable in parameters or variable in bound or variable in brought:
                continue
            brought[variable] = sort
    return list(brought.items())


def _called_condition(node: Any, namespace: Mapping[str, Any]) -> Any:
    """The condition an annotation calls, ``cfl(c, dt, h)`` or ``k.conditions(a)``; or ``None``."""
    if not isinstance(node, ast.Call):
        return None
    func = node.func
    if isinstance(func, ast.Name):
        found = namespace.get(func.id)
        return found if isinstance(found, Condition) else None
    if (
        isinstance(func, ast.Attribute)
        and func.attr == "conditions"
        and isinstance(func.value, ast.Name)
    ):
        owner = namespace.get(func.value.id)
        found = getattr(owner, "conditions", None) if isinstance(owner, Claim) else None
        return found if isinstance(found, Conditions) else None
    return None


def _bound_values(under: Any) -> dict[str, Any]:
    """What the ``with`` statements in force bound, by name: a ``Var``, or a proposition."""
    values: dict[str, Any] = {}
    for entry in under:
        for name, value in entry.values:
            values.setdefault(name, value)
    return values


def _condition_parts(under: Any) -> tuple[list[tuple[str, Any]], list[tuple[str, Any]]]:
    """The variables and the hypotheses of what is in force, outermost first, each once.

    A whole claim assumed by ``with`` brings its goal among the hypotheses,
    under the claim's name (:class:`lanky.conditions.Assuming`).
    """
    variables: list[tuple[str, Any]] = []
    hypotheses: list[tuple[str, Any]] = []
    seen: set[str] = set()
    for entry in under:
        for name, sort in entry.condition.assumed_variables:
            if name not in seen:
                seen.add(name)
                variables.append((name, sort))
        for name, prop in entry.condition.assumed_hypotheses:
            if name not in seen:
                seen.add(name)
                hypotheses.append((name, prop))
    return variables, hypotheses


def _where(fn: Any) -> str:
    """``line_taylor at layer_potential.py:195``."""
    code = fn.__code__
    name = getattr(fn, "__qualname__", fn.__name__)
    return f"{name} at {os.path.basename(code.co_filename)}:{code.co_firstlineno}"


def _refuse_a_bound_parameter(fn: Any, under: Any) -> None:
    """Refuse a claim in a ``with`` block that declares one of the block's names itself.

    ``with away_from_zero as (alpha, beta, nonzero):`` binds ``alpha``, and
    the claims in the block take it from there; a parameter ``alpha`` would
    be a second variable of the same name, and which one an annotation means
    would not show. A whole claim assumed by ``with`` holds in the block
    under its own name, which a parameter cannot take either.
    """
    if not under:
        return
    parameters = inspect.signature(fn).parameters
    for entry in under:
        for name in entry.parts:
            if name in parameters:
                condition = entry.condition
                raise TypeError(
                    f"{_where(fn)}: {name} is {condition.__name__}'s, which with "
                    f"{condition.__name__} as ({', '.join(entry.names)}) assumes for every "
                    f"claim in the block; drop the parameter {name}, or define "
                    f"{fn.__name__} outside the block"
                )


def _refuse_a_name_bound_elsewhere(fn: Any, bound: Mapping[str, Any]) -> None:
    """Refuse a claim that reads a name a ``with`` block bound, outside that block.

    After ``with away_from_zero as (alpha, beta, nonzero):`` ends, ``alpha``
    still holds what the block bound it to, as any name a ``with`` statement
    binds does in Python. A claim after the block that reads it, in an
    annotation or in its body, would be about away_from_zero's ``alpha``
    without holding under it, so it is refused, with the block to put it in.
    """
    from lanky.conditions import anything_bound, bound_by
    from lanky.terms import code_reads

    if not anything_bound():
        return
    namespace = getattr(fn, "__globals__", {})
    parameters = set(inspect.signature(fn).parameters)
    reads: list[str] = []
    try:
        raw = inspect.get_annotations(fn, eval_str=False)
    except Exception:  # noqa: BLE001 - the reading says what is wrong with them
        raw = {}
    for annotation in raw.values():
        if isinstance(annotation, str):
            try:
                code = compile(annotation.lstrip(" \t"), "<string>", "eval")
            except (SyntaxError, ValueError):
                continue
            reads.extend(code_reads(code).names)
    reads.extend(_global_loads(fn.__code__))
    for name in dict.fromkeys(reads):
        if name in parameters or name in bound or name not in namespace:
            continue
        found = bound_by(namespace[name])
        if found is None:
            continue
        condition, _ = found
        raise TypeError(
            f"{_where(fn)}: {name} belongs to {condition.__name__}; use it inside with "
            f"{condition.__name__} as ({', '.join(condition.names)}):"
        )


def _global_loads(code: Any) -> list[str]:
    """The names ``code`` and the code compiled inside it load from the globals."""
    import dis
    import types

    names: list[str] = []
    stack = [code]
    seen = set()
    while stack:
        current = stack.pop()
        if id(current) in seen:
            continue
        seen.add(id(current))
        for instruction in dis.get_instructions(current):
            if instruction.opname in ("LOAD_GLOBAL", "LOAD_NAME"):
                names.append(str(instruction.argval))
        stack.extend(c for c in current.co_consts if isinstance(c, types.CodeType))
    return names


#: What to write in place of a builtin type a parameter is annotated with.
_SORT_HINTS = {
    "int": "write Int from lanky.prelude, or Nat for a natural",
    "float": "write Real from lanky.prelude",
    "complex": "write Complex from lanky.prelude",
    "bool": "write Bool from lanky.prelude",
}


def _refuse_a_builtin_annotation(fn: Any, name: str, annotation: Any) -> None:
    """Raise ``TypeError`` for a parameter or a goal annotated with one of Python's builtins.

    Under ``from __future__ import annotations`` an annotation is a string
    lanky evaluates, where a builtin's name is a variable no parameter binds
    (:class:`lanky.terms.BuiltinName`), and not the builtin: ``x: int``
    annotated ``x`` with a proposition, the free name ``int``, so ``x`` was
    no variable of the statement, its hypotheses were ``int``, and ``x``
    stood in the goal as a free name too, which Lean bound implicitly as a
    natural and proved ``x - 1 >= 0`` about (#63, #64). Without that import
    the annotation is the type ``int``, which is no sort either. Either way
    the claim is refused where it is written, naming the lanky sort meant.

    So is a builtin named anywhere inside an annotation without being called:
    as the sort of a family's values, ``f: Fn[Fin[n], float]``, which the
    tester passed on the draws where the family is empty, and Lean could not
    print; as its index, as the base of a refinement, or as a value in a
    proposition, ``n >= int``. Called at concrete values a builtin is
    Python's, and leaves nothing behind to find; named and not called, it is
    a free name, which no oracle can read as Python does.
    """
    builtin = _builtin_in(annotation)
    if builtin is None:
        return
    code = fn.__code__
    where = f"{getattr(fn, '__qualname__', fn.__name__)} at {os.path.basename(code.co_filename)}"
    where = f"{where}:{code.co_firstlineno}"
    what = "the goal" if name == "return" else f"the parameter {name}"
    if builtin in _SORT_HINTS:
        advice = _SORT_HINTS[builtin]
    elif isinstance(annotation, BuiltinName | type):
        advice = (
            "annotate a variable with a sort from lanky.prelude (Nat, Int, Real, "
            "Complex, Bool, Fin[n], Fn[A, B]) and a hypothesis or the goal with a "
            "proposition"
        )
    else:
        advice = (
            f"a builtin is Python's where it is called at concrete values; bind "
            f"{builtin} as a parameter if a variable of that name is meant"
        )
    if isinstance(annotation, BuiltinName | type):
        raise TypeError(
            f"{where}: {what} is annotated with {builtin}, which is Python's {builtin} "
            f"and not a lanky sort or a proposition; {advice}"
        )
    shown = render(annotation) if isinstance(annotation, prim.ExpressionNode) else annotation
    raise TypeError(
        f"{where}: {what} is annotated with {shown}, which names Python's {builtin} "
        f"without calling it, and that is not a lanky sort or a variable of the "
        f"statement; {advice}"
    )


def _builtin_in(annotation: Any) -> str | None:
    """The name of a builtin of Python's that ``annotation`` names without calling it.

    ``None`` if there is none. A term is walked through its operands and a
    quantifier through its binders' domains, and a sort through what it is
    built of: a family's index and values, a refinement's base and
    propositions, a ``Fin``'s bound and the pieces of a sum. A builtin is the
    :class:`~lanky.terms.BuiltinName` a :class:`~lanky.terms.Scope` gives its
    name, or, without ``from __future__ import annotations``, the type itself.
    """
    stack = [annotation]
    while stack:
        node = stack.pop()
        if isinstance(node, BuiltinName):
            return node.name
        if isinstance(node, type):
            if getattr(builtins, node.__name__, None) is node:
                return node.__name__
            continue
        if isinstance(node, Forall | Exists | Sum):
            stack.extend(domain for _var, domain in node.binders)
            stack.extend(part for part in (node.body, node.guard) if part is not None)
        elif isinstance(node, Refined):
            stack.append(node.base)
            stack.extend(node.props)
        elif isinstance(node, FinType):
            stack.append(node.bound)
        elif isinstance(node, FnType):
            stack.extend((node.domain, node.codomain))
        elif isinstance(node, SumType):
            stack.extend(node.pieces)
        elif isinstance(node, prim.ExpressionNode):
            for child in init_args(node):
                stack.extend(child if isinstance(child, tuple) else (child,))
    return None



class CitedClaim(Claim):
    """A claim taken on a source: read like any claim, and never established.

    ``@claim(cite="Kress, Linear Integral Equations, ch. 6")`` is how a result
    lanky cannot establish enters the ledger on the word of a reference, such
    as a jump relation taken from a textbook. It is written like a claim and
    read the same way, and its fact differs in three things: its kind is
    ``"cited"``, its status stays ``assumed``, and its provenance carries the
    source as ``cite``. No oracle is asked to establish it, since the point of
    citing it is that its author vouches for it, and a claim that ``uses`` it
    is established *under* it in the ledger.

    It is still a statement, so it can still be run and still be refuted:
    calling it evaluates it at concrete values, the pytest plugin samples it
    as it samples any claim, and ``lanky check`` has the property tester look
    for a counterexample (see :func:`lanky.check.establish`). That is where a
    source copied down wrong shows up, and a refuted cited claim fails the
    check like any refuted fact.

    Attributes:
        cite: The source, as given.

    Raises:
        TypeError: If the source is empty or not a string.
    """

    kind = "cited"

    def __init__(self, fn: Any, *, cite: Any, uses: Any = ()) -> None:
        name = getattr(fn, "__qualname__", None) or getattr(fn, "__name__", None) or repr(fn)
        self.cite = _citation(name, cite)
        super().__init__(fn, uses=uses)

    def fact(self, reading: Fact | None = None) -> Fact:
        """This claim as a ledger entry: ``assumed``, with its source."""
        fact = super().fact(reading)
        return fact.with_status(Status.ASSUMED, cite=self.cite)


#: lanky 0.5's names of the classes, kept for plugins that check a claim's type.
Theorem = Claim
Axiom = CitedClaim


def _citation(name: str, cite: Any) -> str:
    """The source a claim was cited on, or ``TypeError`` saying how to give one."""
    if not isinstance(cite, str):
        raise TypeError(f'{name}: a claim\'s source is a string, cite="...", not {cite!r}')
    if not cite.strip():
        raise TypeError(f"{name}: a claim's source is empty; name the reference")
    return cite


class ClaimTheory:
    """The built-in theory: ``@claim`` and ``@condition`` over typed Python functions."""

    name = "claim"

    def __call__(self, obj: Any, /) -> Claim:
        """Decorate ``obj`` as a claim and register it."""
        return registry.register_object(Claim(obj))

    def facts(self, obj: Any, /) -> tuple:
        """A claim's fact and its ``faithful`` fact; a condition's row; nothing for anything else.

        The claim comes first, as written, and its reading after it: whether
        the term computes what the annotations compute (#91, see
        :mod:`lanky.faithful`). The claim's fact names the reading, so that
        :func:`lanky.check.establish` rests a pass, a decision or a proof on
        it, and offers a claim whose reading is refuted to no oracle. A
        condition's row is the check that its conditions can hold
        (:meth:`lanky.conditions.Condition.fact`).
        """
        if isinstance(obj, Condition):
            return (obj.fact(),)
        if not isinstance(obj, Claim):
            return ()
        reading = obj.faithful_fact()
        return (obj.fact(reading), reading)


#: lanky 0.5's name of the theory.
TheoremTheory = ClaimTheory

#: The theory itself, also usable as the ``@claim`` decorator.
claim_theory = ClaimTheory()
theorem_theory = claim_theory
registry.register_theory(claim_theory)


def claim(fn: Any = None, /, *, cite: Any = None, uses: Any = ()) -> Any:
    """Turn a typed function into a :class:`Claim` and register it.

    Parameters annotated with sorts are the variables, parameters annotated
    with propositions are the conditions, and the return annotation is the
    goal::

        @claim
        def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
            \"\"\"Twice the sum of the first n numbers is n times n + 1.\"\"\"

    Written bare, ``@claim``; with the facts the claim rests on,
    ``@claim(uses=[jump, compact])``: claims, facts or fact ids (see
    :func:`fact_ids`), which become its fact's ``rests_on``; and on a source,
    ``@claim(cite="Ahlfors 1979, ch. 5")``, a :class:`CitedClaim`, which
    lanky takes on that source and never establishes. A bad entry is refused
    where the decorator is written, not when the file is checked, and so is a
    positional argument that is not the function to decorate:
    ``@claim(gauss)`` is ``@claim(uses=[gauss])`` written wrong, and
    ``@claim("Kress")`` is ``@claim(cite="Kress")``.

    Raises:
        lanky.surface.FormError: When it is called inside a claim's own
            proof, where a claim does not call itself: the earlier case is
            its conclusion at an earlier point.
    """
    _refuse_inside_a_proof(fn)
    _refuse_a_misplaced_argument(fn)
    rests_on = fact_ids(uses)
    if cite is not None:
        _citation("@claim", cite)

    def decorate(fn: Any) -> Claim:
        if cite is not None:
            return registry.register_object(CitedClaim(fn, cite=cite, uses=rests_on))
        return registry.register_object(Claim(fn, uses=rests_on))

    return decorate if fn is None else decorate(fn)


def _refuse_inside_a_proof(fn: Any) -> None:
    """Refuse ``claim(...)`` inside a running proof: the claim proved is spelled by its name."""
    from lanky.proofs.trace import active

    run = active()
    if run is None or (callable(fn) and hasattr(fn, "__code__")):
        return
    from lanky.surface import FormError

    own = getattr(getattr(run, "theorem", None), "__qualname__", "name")
    raise FormError(
        "claim is the decorator that states a claim; in a proof the claim being proved "
        f"is spelled by its name, and an earlier case of it is {own}.conclusion[...]",
        f"{own}.conclusion[n - 1]",
    )


def theorem(fn: Any = None, /, **given: Any) -> Any:
    """Refused: lanky 0.5's ``@theorem`` is ``@claim`` in 0.6.

    Raises:
        lanky.surface.RemovedForm: Always, with the line to write.
    """
    from lanky.surface import RemovedForm

    uses = "(uses=[...])" if "uses" in given else ""
    raise RemovedForm("@theorem is lanky 0.5's word for a claim", f"@claim{uses}")


def axiom(fn: Any = None, /, *, cite: Any = None, **given: Any) -> Any:
    """Refused: lanky 0.5's ``@axiom(cite=...)`` is ``@claim(cite=...)`` in 0.6.

    Raises:
        lanky.surface.RemovedForm: Always, with the line to write.
    """
    from lanky.surface import RemovedForm

    source = '"' + cite.replace('"', '\\"') + '"' if isinstance(cite, str) else '"..."'
    uses = ", uses=[...]" if "uses" in given else ""
    raise RemovedForm(
        "@axiom is lanky 0.5's word for a claim taken on a source",
        f"@claim(cite={source}{uses})",
    )


def _refuse_a_misplaced_argument(fn: Any) -> None:
    """Raise ``TypeError`` if ``@claim`` was handed something other than a function.

    ``@claim(gauss)`` and ``@claim("Kress")`` are ``uses=`` and ``cite=``
    written without their keywords. Read as the function to decorate, the
    first fails on a claim having no code object and the second on a string
    having none, and neither says what went wrong. ``None`` is the decorator
    called with parentheses, and passes.
    """
    if fn is None or (callable(fn) and not isinstance(fn, Claim | Assuming)):
        return
    if isinstance(fn, str):
        raise TypeError(
            f'@claim decorates a typed function, and {fn!r} is not one; a claim\'s source '
            f'goes in cite="..."'
        )
    raise TypeError(
        f"@claim decorates a typed function, and {fn!r} is not one; what a claim rests on "
        "goes in uses=[...]"
    )
