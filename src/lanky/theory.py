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
``lanky check FILE`` only has to import the file. The body is the proof: a body
that holds only a docstring, ``...`` or ``pass`` leaves the proof to lanky, and
any other is a written proof, which ``lanky check`` traces after every run and
draw of the check and has Lean check (:mod:`lanky.proofs`). Running the file
never calls the body.

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
    names one fact through a string ``fact_id``, as a :class:`Theorem` and an
    :class:`Axiom` do. A single entry need not be wrapped in a list, and an
    empty list names nothing. An id is a string, so a plugin's fact is named
    the same way: the postcondition of loopty's ``scan`` in ``spmv.py`` is
    ``"postcondition:spmv.scan@69"``, keyed as a theorem's is (see
    :func:`lanky.ledger.fact_id`).

    Raises:
        TypeError: For anything else, such as a plugin's decorated object that
            owns several facts, which would leave open which one is meant, or
            ``None``, which is what a name bound to nothing by mistake holds:
            a theorem that uses nothing leaves ``uses=`` out.
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
        TypeError: If the function has no return annotation (or ``-> None``).
            A theorem needs a goal. Without one it used to read as ``True``
            when it was called or tested and as ``assumed`` in the ledger,
            where no oracle takes a fact with no term, so one statement had
            two answers; it is refused where it is written instead. And if a
            parameter or the goal is annotated with a builtin of Python's,
            ``x: int``, or names one anywhere in its annotation without
            calling it, ``f: Fn[Fin[n], float]`` (see
            :func:`_refuse_a_builtin_annotation`). And if an annotation reads
            ``all``, ``any``, ``sum`` or ``abs``, which no parameter is named,
            and the module binds that name to something other than Python's
            builtin or lanky's own, which lanky would read in its place (see
            :func:`lanky.terms.evaluate_annotations`, #100).
    """

    #: What the statement is called in messages, in its fact's kind and id.
    noun = "theorem"

    def __init__(self, fn: Any, *, uses: Any = ()) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        self.uses = fact_ids(uses)
        from lanky.faithful import capture

        # taken before the annotations are read, which may run a helper that
        # changes what it reads
        self.snapshot = capture(fn)
        self.namespace = self.snapshot.namespace
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
    def sequent(self) -> dict[str, Any]:
        """The parts of :attr:`statement`, as text: variables, named hypotheses, goal."""
        return {
            "variables": ", ".join(f"{name} : {sort}" for name, sort in self.variables),
            "hypotheses": [[name, render(prop)] for name, prop in self.hypotheses],
            "goal": render(self.goal),
        }

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

        A theorem with hypotheses and no sort-valued parameters still has a
        guard, and the binder tuple is then empty rather than the whole
        :class:`~lanky.terms.Forall` being dropped. Dropping it would hand the
        oracles the bare goal, which is a different and stronger claim: the
        hypotheses are what make an implication with a false antecedent valid,
        and without them such a theorem is refuted by its own hypothesis.

        With neither binders nor a guard the binder tuple is empty too, and
        the term is still a :class:`~lanky.terms.Forall`, whose body is the
        goal (#35). Every reader of a term takes a ``Forall`` apart into
        variables, hypotheses and goal, so the goal itself handed over as the
        term was taken apart in its place when it was a universal:
        ``-> all(k >= 0 for k in Nat if k > 100)`` had ``k`` read as the
        statement's variable and its guard as the statement's hypotheses, so
        the ledger warned about hypotheses the theorem does not have, while
        :meth:`report`, which hands the oracle the goal as a goal, read the
        same theorem as a goal whose guard no draw passed. The empty binders
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

    def __call__(self, *values: Any, **concrete: Any) -> Any:
        """Evaluate the hypotheses and the goal at concrete values; or, in a proof, cite it.

        The proof body is not run: it is a proof for Lean, not code. What
        running a theorem means is checking what it says. A value for a family
        parameter may be given as a sequence, which is read as a table, and
        one for a family with several indices as nested sequences or an
        array, ``F=[[1, 2], [3, 4]]`` for ``F: Fn[Fin[2], Fin[2], Nat]``.

        Inside the trace of a written proof (:mod:`lanky.proofs`), which only
        ``lanky check`` runs, calling a theorem is citing it, at the values
        given, its variables outermost first and then the goal's, positional
        or by name. What decides is whether a trace is running, not the
        arguments' types. A theorem that cites itself by name in its own
        proof is refused, with ``claim(...)`` or ``claim[...]`` as the fix.

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
                And outside a proof, if a value is given by position: a
                theorem is evaluated at values given by name.
        """
        from lanky.proofs.trace import active

        tracer = active()
        if tracer is not None:
            return tracer.cite_theorem(self, values, concrete, sys._getframe(1))
        if values:
            raise TypeError(
                f"{self.__name__} is evaluated at values given by name, as "
                f"{self.__name__}({', '.join(f'{name}=...' for name, _ in self.variables)}); "
                "a call at symbolic values is a citation, inside a written proof"
            )
        missing = [name for name, _ in self.variables if name not in concrete]
        if missing:
            raise TypeError(f"{self.__name__} needs values for {', '.join(missing)}")
        sorts = dict(self.variables)
        context = {
            name: _as_family(value, sorts.get(name), name) for name, value in concrete.items()
        }
        return Verdict(
            hypotheses={
                name: truth_value(evaluate(prop, context), prop)
                for name, prop in self.hypotheses
            },
            goal=truth_value(evaluate(self.goal, context), self.goal),
        )

    def run_proof(self, **values: Any) -> None:
        """Run the written proof as plain Python at ``values``, as a REPL or pdb would.

        The values are given by name, as :meth:`__call__` takes them.
        ``claim.dom`` gives the conclusion's first points, to the tester's
        draw bound, a citation is inert, and ``by(...)`` is read only where a
        step fails. A false step raises Python's own ``AssertionError``, its
        message the step's ``by(...)``; a point where the claim is false
        raises :class:`lanky.proofs.native.PointFalse`. It only tests: Lean
        checks the proof under ``lanky check``. Floats compare exactly here,
        so a step can fail on rounding: give ``Fraction`` values.
        """
        from lanky.proofs.native import run_by_hand

        run_by_hand(self, **values)

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
        """The id this theorem's fact carries, unique per definition.

        Two theorems can share a qualified name (one per module, or one
        decorator used twice), and a ledger keyed only by that name would keep
        one of them and drop the other. The module and the definition's line
        settle it; :func:`lanky.ledger.fact_id` is the shared builder, so a
        plugin theory can key its own facts the same way.

        The module is the one the file's path gives it
        (:func:`lanky.check.module_name`), not the name it was imported
        under, so the id is the same in the ledger of the theorem's own file,
        which ``lanky check`` imports under a name of its own, and in the
        ``uses=`` of a theorem in another file that imports it:
        ``theorem:helpers.lemma@12`` either way.
        """
        return fact_id(self.noun, self.qualname, module=self.module, line=self.line)

    def fact(self, reading: Fact | None = None) -> Fact:
        """This theorem as a ledger entry, before any oracle has seen it.

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
        if reading is not None:
            provenance["faithful"] = reading.id
            if reading.status is Status.REFUTED:
                provenance["unfaithful"] = reading.provenance.get("reason") or (
                    "its faithful fact is refuted"
                )
        return Fact(
            id=self.fact_id,
            kind=self.noun,
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
        :mod:`lanky.faithful`, #91). The comparison is made once per theorem
        and kept.
        """
        if self._faithful is None:
            from lanky.faithful import faithful_fact

            self._faithful = faithful_fact(self)
        return self._faithful

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
    the theorem is refused where it is written, naming the lanky sort meant.

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

    def fact(self, reading: Fact | None = None) -> Fact:
        """This axiom as a ledger entry: ``assumed``, with its citation."""
        fact = super().fact(reading)
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
        """The claim of a theorem or an axiom and its ``faithful`` fact; nothing for anything else.

        The claim comes first, as written, and its reading after it: whether
        the term computes what the annotations compute (#91, see
        :mod:`lanky.faithful`). The claim's fact names the reading, so that
        :func:`lanky.check.establish` rests a pass, a decision or a proof on
        it, and offers a claim whose reading is refuted to no oracle.
        """
        if not isinstance(obj, Theorem):
            return ()
        reading = obj.faithful_fact()
        return (obj.fact(reading), reading)


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
    is refused where the decorator is written, not when the file is checked,
    and so is a positional argument that is not the function to decorate:
    ``@theorem(gauss)`` is ``@theorem(uses=[gauss])`` written wrong.
    """
    _refuse_a_misplaced_argument("theorem", fn)
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
            written bare amounts to, or empty; and when the positional
            argument is not the function to decorate, as in
            ``@axiom("Kress")``, where the citation belongs in ``cite=``.
    """
    _refuse_a_misplaced_argument("axiom", fn)
    if fn is not None:
        return registry.register_object(Axiom(fn, cite=cite, uses=uses))
    _citation("@axiom", cite)
    rests_on = fact_ids(uses)

    def decorate(fn: Any) -> Axiom:
        return registry.register_object(Axiom(fn, cite=cite, uses=rests_on))

    return decorate


def _refuse_a_misplaced_argument(noun: str, fn: Any) -> None:
    """Raise ``TypeError`` if a decorator was handed something other than a function.

    ``@theorem(gauss)`` and ``@axiom("Kress")`` are ``uses=`` and ``cite=``
    written without their keywords. Read as the function to decorate, the
    first fails on a theorem having no code object and the second on a
    missing citation, and neither says what went wrong. ``None`` is the
    decorator called with parentheses, and passes.
    """
    if fn is None or (callable(fn) and not isinstance(fn, Theorem)):
        return
    if noun == "axiom":
        where = 'what an axiom rests on goes in uses=[...], and its citation in cite="..."'
    else:
        where = f"what a {noun} rests on goes in uses=[...]"
    raise TypeError(f"@{noun} decorates a typed function, and {fn!r} is not one; {where}")
