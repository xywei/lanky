"""Tracing a written proof: the body run on symbolic values, once per path.

The design idea. A theorem's body is ordinary Python, and running it on the
symbolic terms its annotations were read with records the proof: which steps
each ``assert`` states and why, which facts each ``yield`` or ``return``
gives, at which points, and under which case. Nothing is read from the body's
syntax but whether there is a proof at all (:func:`written_lines`), which line
an ``assert`` is on, and that no form of lanky 0.5 is left in it. The body
runs only under ``lanky check``, after every native run and every draw of the
check, never when the file is imported or run, in a namespace built at check
time (:func:`namespace`): the module's live globals, the snapshot's copies of
what the annotations read laid over them, and lanky's ``all``, ``any``,
``sum`` and ``abs``.

While a body is traced:

- Its parameters are symbolic values: a variable is the :class:`~lanky.terms.Var`
  of its name, and a condition a :class:`Given`, a fact the body cites by
  name, ``by(stored)``, or at a point of its domain, ``by(pde[i, a - 2,
  b])``. A name of the statement the function does not take as a
  parameter, one bound outside the claim, is given its symbolic value in
  the namespace instead (:func:`body_arguments`).
- An ``if`` in the body's own code is a case split. The truth value of its
  proposition is scheduled (:meth:`_Tracer.ask`): the body runs once per path,
  each branch with its condition as a fact, and a proposition asked twice on
  one path gets the same answer. A condition the path's facts already decide
  (a condition on the bounds of naturals, say) is answered so, and makes no
  split. Asked anywhere else, by pymbolic, by ``in``, by a sort, the
  question raises as it does outside a trace, so that no silent case split
  is made.
- An ``assert`` is a step. Python reads its message, ``by(...)``, only when
  the step fails, so the first time a path reaches an ``assert`` its
  question is answered "false", the reason is read from the
  ``AssertionError``, and the body runs again with the step answered "true"
  (:meth:`_Tracer._assertion`). This is the per-path re-run an ``if`` already
  makes, one more run per ``assert``. An assert is told from an ``if`` by the
  bytecode, as :func:`_branches_on` tells an ``if`` from other questions: its
  failing branch is ``LOAD_ASSERTION_ERROR`` (:func:`_assert_answer`). Python's
  chained comparison, ``x == y == z``, asks a question per link, and the
  links are one chain. A step is known for the rest of its case.
- The claim's own name is the decorated claim, which Python resolves in the
  module's globals, and its parts are addressed through its tree
  (:mod:`lanky.surface`). ``for n in name.conclusion.domain:`` gives one
  symbolic point, the variables of the conclusion's ``for``, with its guard
  known (:class:`_Dom`), and a nested ``for`` its own loop over
  ``name.conclusion[i].domain``. A body with ``yield`` is a generator,
  driven here: ``yield by(...)`` closes the conclusion at the point of the
  innermost loop over a domain.
- ``name.conclusion[p]`` is the conclusion at an earlier point of the loops,
  which is the induction; it is refused here when the loops have not
  filled it in (:func:`_earlier`). A claim that calls itself is refused,
  and so is every form of lanky 0.5's proofs.
- Every case ends with a closing line, ``yield by(...)`` or ``return
  by(...)``: a bare ``return``, ``continue``, a bare ``yield`` or a path
  that ends is refused, at its line (:meth:`_Tracer._unclosed`).

The result is a :class:`Proof`: the claim's definition, if the proof uses
one, and a tree of cases whose leaves are what each path gives, with the
steps asserted on the way. What it means in Lean is
:mod:`lanky.proofs.compile`'s business.
"""

from __future__ import annotations

import ast
import dis
import functools
import inspect
import linecache
import os
import sys
import textwrap
import types as pytypes
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
from typing import Any

from lanky.citations import Citation
from lanky.proofs.cases import decide, negated, offset_of, shape_of
from lanky.surface import By, RemovedForm, reason_text
from lanky.terms import (
    BUILTIN_OVERRIDES,
    Forall,
    SymbolicBoolError,
    Var,
    asking_proof_questions,
    code_reads,
    conjuncts,
    lift,
    render,
)

__all__ = [
    "MAX_PATHS",
    "MAX_QUESTIONS",
    "MAX_RUNS",
    "Asserted",
    "ClaimDef",
    "Given",
    "Leaf",
    "LinkStep",
    "Node",
    "Proof",
    "ProofError",
    "Question",
    "TracedChain",
    "active",
    "body_arguments",
    "namespace",
    "trace_proof",
    "written_lines",
]

#: How many paths a body may take, its cases, before it is refused.
MAX_PATHS = 64

#: How many truth values one run of a body may ask for, a guard against a
#: ``while`` over a symbolic condition, which asks the same question for ever.
MAX_QUESTIONS = 256

#: How many times a body may be run in all: once per path, and once more per
#: ``assert`` on it.
MAX_RUNS = 1024


# {{{ whether there is a proof


def written_lines(fn: Any) -> tuple[int, int] | None:
    """The lines of ``fn``'s body that hold a proof, first and last; ``None`` for no proof.

    A body that holds only a docstring, ``...`` or ``pass`` is no proof, and
    lanky's search runs as it always has: ``def every_box(...) -> ...: ...``
    keeps that meaning. Read off the source, which is the only way that is
    the same on every Python: the bytecode of a docstring and of ``...``
    differs between versions. A function whose source cannot be read has no
    written proof, as far as lanky can tell.
    """
    try:
        lines, start = inspect.getsourcelines(fn)
    except (OSError, TypeError):
        return None
    try:
        tree = ast.parse(textwrap.dedent("".join(lines)))
    except SyntaxError:
        return None
    function = next(
        (node for node in tree.body if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef)),
        None,
    )
    if function is None:
        return None
    body = list(function.body)
    if body and _is_docstring(body[0]):
        body = body[1:]
    meaningful = [statement for statement in body if not _is_placeholder(statement)]
    if not meaningful:
        return None
    first = meaningful[0].lineno + start - 1
    last = (function.end_lineno or meaningful[-1].lineno) + start - 1
    return first, last


def _is_docstring(statement: ast.stmt) -> bool:
    """Whether a statement is a string standing alone, a docstring."""
    return (
        isinstance(statement, ast.Expr)
        and isinstance(statement.value, ast.Constant)
        and isinstance(statement.value.value, str)
    )


def _is_placeholder(statement: ast.stmt) -> bool:
    """Whether a statement says nothing: ``pass``, ``...``, or a string standing alone."""
    if isinstance(statement, ast.Pass):
        return True
    return (
        isinstance(statement, ast.Expr)
        and isinstance(statement.value, ast.Constant)
        and (statement.value.value is Ellipsis or isinstance(statement.value.value, str))
    )


# }}}


# {{{ what a trace records


class ProofError(Exception):
    """A written proof lanky refuses before Lean is asked, at a line of the body.

    Attributes:
        kind: What went wrong, one word: ``self-reference``, ``removed``,
            ``later``, ``no-point``, ``measure``, ``negative``, ``claim``,
            ``return``, ``yield``, ``assert``, ``false``, ``question``,
            ``raised``, ``paths``.
        message: What to say, in lanky's notation.
        line: The line of the body it is about, when there is one.
        fix: What to write instead, when there is a fix to name.
    """

    def __init__(
        self, kind: str, message: str, line: int | None = None, fix: str | None = None
    ) -> None:
        super().__init__(message)
        self.kind = kind
        self.message = message
        self.line = line
        self.fix = fix


class Given:
    """A condition of the claim, as its proof cites it: a fact with a name.

    Written alone, ``by(stored)``, it is cited at the point lanky finds by
    matching it against the step it supports; at a point of its domain,
    ``pde[i, a - 2, b]``, it is cited there, its variables outermost first.
    A condition written ``p & q`` is cited as both parts. Brackets give a
    point; lanky 0.5's ``pde(i, a - 2, b)`` is refused with the bracket
    written.
    """

    def __init__(self, name: str, prop: Any, tracer: _Tracer | None) -> None:
        self.name = name
        self.prop = prop
        self._tracer = tracer

    @property
    def parts(self) -> tuple[Any, ...]:
        """The parts of a condition written as a conjunction; the condition itself otherwise."""
        return conjuncts(self.prop) or (self.prop,)

    def written(self, values: tuple[Any, ...], bracket: bool = True) -> str:
        """The condition at a point, as a proof writes it: ``pde[i, a - 2, b]``."""
        del bracket
        return f"{self.name}[{', '.join(shown(value) for value in values)}]"

    def __getitem__(self, point: Any) -> Citation:
        """The condition at a point of its domain: a citation."""
        assert self._tracer is not None
        values = point if isinstance(point, tuple) else (point,)
        return self._tracer.cite(self, values, {}, sys._getframe(1))

    def __call__(self, *values: Any, **named: Any) -> Citation:
        """Refused: a point is given in brackets, ``pde[i, a - 2, b]``."""
        given = [shown(value) for value in values]
        given += [f"{key}={shown(value)}" for key, value in named.items()]
        if named:
            fix = f"{self.name}[...], its values in the order of its for, outermost first"
        else:
            fix = f"{self.name}[{', '.join(given)}]"
        raise RemovedForm(
            f"{self.name}({', '.join(given)}) is how lanky 0.5 cited a condition at a point; "
            "brackets give a point of its domain, and parentheses inputs to a claim",
            fix,
        )

    def __bool__(self) -> bool:
        """Refused: a fact has no truth value to ask for."""
        raise SymbolicBoolError(
            f"{self.name} is a fact, and a fact has no truth value to ask for; cite it "
            f"as the reason for a step, as by({self.name})"
        )

    def __repr__(self) -> str:
        """The hypothesis's name."""
        return self.name


@dataclass(frozen=True, eq=False)
class ClaimDef:
    """The claim's conclusion at the points of its domain, which its proof loops over and cites.

    Lean has it as a theorem of its own, ``Lanky.<name>.claim``, recursive,
    with the theorem's variables and the conclusion's as its parameters; a
    citation of ``name.conclusion[p]`` inside the proof is a recursive call.

    Attributes:
        name: How a proof writes it, ``line_taylor.conclusion``.
        params: The parameters a citation of it gives values for: the
            variables of the conclusion's ``for``, those of each nested
            ``for`` the proof loops over after them.
        domains: The sort each parameter ranges over.
        generalized: Kept empty: a claim never calls itself for other
            inputs, so none of its parameters is generalized.
        line: The line of the loop over the conclusion's domain, or of the
            first citation of it.
        levels: How many of ``params`` each nested ``for`` has, outermost first.
        directions: For each parameter, ``1`` where the loop over its domain
            walks it in increasing order, ``-1`` where it walks it reversed.
    """

    name: str
    params: tuple[str, ...]
    domains: tuple[Any, ...]
    generalized: tuple[str, ...]
    line: int
    levels: tuple[int, ...] = ()
    directions: tuple[int, ...] = ()

    def written(self, values: tuple[Any, ...], bracket: bool = True) -> str:
        """A citation of the claim, as written: ``every_box.conclusion[i][a - 2, b + 2]``."""
        del bracket
        sizes = self.levels or (len(self.params),)
        out = self.name
        start = 0
        for size in sizes:
            part = values[start : start + size]
            start += size
            if all(value is None for value in part):
                break
            out += f"[{', '.join(shown(value) for value in part)}]"
        return out


def shown(value: Any) -> str:
    """A value as lanky writes it in a citation or a report.

    A family's value is the ``lambda`` a proof writes for it, ``lambda i:
    i**3``, so that a point lanky found reads as the citation that would
    give it.
    """
    from lanky.matching import FamilyValue

    if isinstance(value, FamilyValue):
        return value.shown()
    if value is None:
        return "_"
    return render(value) if hasattr(value, "mapper_method") else repr(value)


def family_value(value: Any) -> Any:
    """A function written at a family's place in a citation, as the family's value it gives.

    ``one_more_term(lambda i: i**3, n)`` cites the fact with its family
    ``f`` at ``i ↦ i**3``: the function is called once, at a variable per
    parameter named as it names them, and what it returns is the body of
    the value (:class:`lanky.matching.FamilyValue`). Anything else is
    returned as it is.
    """
    from lanky.matching import FamilyValue

    if not isinstance(value, pytypes.FunctionType):
        return value
    try:
        signature = inspect.signature(value)
    except (TypeError, ValueError):
        return value
    parameters = list(signature.parameters.values())
    if not parameters or any(
        parameter.kind not in (parameter.POSITIONAL_ONLY, parameter.POSITIONAL_OR_KEYWORD)
        for parameter in parameters
    ):
        return value
    variables = tuple(Var(parameter.name) for parameter in parameters)
    return FamilyValue(variables, lift(value(*variables)))


@dataclass(frozen=True, eq=False)
class Question:
    """A case split: the condition an ``if`` asked, where, and the answer on this path.

    Attributes:
        prop: The proposition the ``if`` asked the truth value of.
        line: The line of the ``if``.
        answer: Its truth value on this path.
        forced: Whether the path's facts decided it, so that it splits nothing.
    """

    prop: Any
    line: int
    answer: bool
    forced: bool = False

    @property
    def condition(self) -> Any:
        """What holds on this path: the proposition, or its negation."""
        return self.prop if self.answer else negated(self.prop)


@dataclass(frozen=True, eq=False)
class LinkStep:
    """One link of an asserted chain: the relation, the term it reaches, and its reasons.

    Attributes:
        relation: ``"=="``, ``"<="``, ``"<"``, ``">="`` or ``">"``.
        term: The term the link reaches.
        facts: The reasons of its ``assert``, each a :class:`Citation`;
            empty for algebra alone. Every link of one ``assert`` has the
            same, and lanky finds which serve which.
        hole: Whether the step was written ``by(...)``, left open.
        line: The line the link's term is written on.
    """

    relation: str
    term: Any
    facts: tuple[Citation, ...]
    hole: bool
    line: int | None


@dataclass(frozen=True, eq=False)
class TracedChain:
    """A chain of comparisons an ``assert`` states, ``x == y <= z``, one link per comparison.

    Attributes:
        start: The term it starts at.
        links: Its links, in order.
        name: Kept for the outline; ``None``.
        line: The line of the ``assert``.
    """

    start: Any
    links: tuple[LinkStep, ...]
    name: str | None
    line: int | None

    @property
    def end(self) -> Any:
        """The term the chain ends at."""
        return self.links[-1].term

    @property
    def relation(self) -> str:
        """The relation the chain states between its ends."""
        from lanky.chains import combined_relation

        return combined_relation(link.relation for link in self.links)

    @property
    def claim(self) -> Any:
        """What the chain shows: its start, its relation, its end."""
        from lanky.terms import Comparison

        return Comparison(self.start, self.relation, self.end)

    def steps(self) -> Iterator[tuple[Any, LinkStep]]:
        """Each link with the term it starts from, in order."""
        left = self.start
        for link in self.links:
            yield left, link
            left = link.term

    @property
    def holes(self) -> tuple[int | None, ...]:
        """The lines of the links left open."""
        return tuple(link.line for link in self.links if link.hole)


@dataclass(frozen=True, eq=False)
class Asserted:
    """A step of a proof, ``assert x == y, by(f, g)``: what it states, why, and where.

    Attributes:
        line: The line of the ``assert``.
        parts: What it states: a :class:`TracedChain` for a comparison or a
            chain of them, or a proposition for anything else. An ``assert p
            and q`` states two parts.
        facts: The facts ``by(...)`` gave, each a :class:`Citation`; empty
            for algebra alone and for a step left open.
        hole: Whether the step was left open, ``by(...)``.
        depth: How many case splits came before it on its path.
    """

    line: int
    parts: tuple[Any, ...]
    facts: tuple[Citation, ...]
    hole: bool
    depth: int

    @property
    def name(self) -> str:
        """How a report names it, as a fact a later step uses: ``the step at line 30``."""
        return f"the step at line {self.line}"

    @property
    def chains(self) -> tuple[TracedChain, ...]:
        """The chains among its parts."""
        return tuple(part for part in self.parts if isinstance(part, TracedChain))

    @property
    def props(self) -> tuple[Any, ...]:
        """What it shows, as propositions: a chain's ends, and the parts that are no chain."""
        return tuple(part.claim if isinstance(part, TracedChain) else part for part in self.parts)


@dataclass(frozen=True, eq=False)
class Leaf:
    """One path of a proof: the cases on the way, the steps asserted, and what it ends with.

    Attributes:
        questions: The case splits on the way, in order, each with its answer.
        facts: The facts the path's ``yield by(...)`` or ``return by(...)``
            gives; ``None`` for a case closed with ``by()``, which lanky
            finishes from the steps asserted for it.
        line: The line of that ``yield`` or ``return``.
        order: The questions and the steps (:class:`Asserted`) of the path,
            in the order the body reached them.
        hole: Whether its ``by(...)`` left it open.
        point: Whether it closes a point of the conclusion's domain, with ``yield``.
    """

    questions: tuple[Question, ...]
    facts: tuple[Citation, ...] | None
    line: int | None
    order: tuple[Any, ...] = ()
    hole: bool = False
    point: bool = False

    @property
    def conditions(self) -> list[tuple[Any, int]]:
        """What holds in this case, each with the line of its ``if``."""
        return [(question.condition, question.line) for question in self.questions]

    @property
    def steps(self) -> tuple[Asserted, ...]:
        """The steps asserted on the path, in order."""
        return tuple(item for item in self.order if isinstance(item, Asserted))

    @property
    def citations(self) -> list[Citation]:
        """Every citation of the case: the steps', and what it ends with."""
        out: list[Citation] = []
        for step in self.steps:
            out.extend(step.facts)
        out.extend(self.facts or ())
        return out

    @property
    def holes(self) -> tuple[int | None, ...]:
        """The lines of the steps left open, ``by(...)``."""
        lines = [step.line for step in self.steps if step.hole]
        if self.hole:
            lines.append(self.line)
        return tuple(lines)


@dataclass(eq=False)
class Node:
    """A node of the case tree: the steps before its split, then the split, or a leaf.

    ``items`` are what the body reached at this node before its split or its
    end: the steps asserted, and the questions the path's facts decided,
    which split nothing.
    """

    question: Question | None = None
    then: Node | None = None
    otherwise: Node | None = None
    leaf: Leaf | None = None
    items: list[Any] = field(default_factory=list)


@dataclass(eq=False)
class Proof:
    """A written proof, traced: what Lean is asked to check, and where each part was written.

    Attributes:
        theorem: The :class:`~lanky.theory.Theorem` it proves.
        claim: The claim's conclusion at the points of its domain, which the
            proof loops over (``for n in name.conclusion.domain:``) and cites
            (``name.conclusion[n - 1]``); ``None`` for a proof with no loop.
        root: The tree of cases.
        leaves: The paths, in the order they were traced.
        lines: The body's lines, first and last.
        path: The file it is written in.
        goal: The conclusion as the proof closes it: the theorem's goal, with
            the nested ``for`` levels the proof loops over taken as one
            (``all(... for i in A for a in B)`` for a loop over ``i`` and
            one over ``every_box.conclusion[i].domain``).
    """

    theorem: Any
    claim: ClaimDef | None
    root: Node
    leaves: tuple[Leaf, ...]
    lines: tuple[int, int]
    path: str
    goal: Any = None

    @property
    def conclusion(self) -> Any:
        """The conclusion as the proof closes it: :attr:`goal`, or the theorem's own."""
        return self.goal if self.goal is not None else self.theorem.goal

    @property
    def calls(self) -> list[Citation]:
        """Every citation of the claim, in the order they were traced, each once."""
        out: list[Citation] = []
        for leaf in self.leaves:
            for citation in leaf.citations:
                if citation.is_claim and all(citation is not seen for seen in out):
                    out.append(citation)
        return out

    @property
    def cited(self) -> list[Any]:
        """The theorems the proof cites, each once, in order."""
        out: list[Any] = []
        for leaf in self.leaves:
            for citation in leaf.citations:
                source = citation.source
                if not isinstance(source, Given | ClaimDef) and all(
                    source is not seen for seen in out
                ):
                    out.append(source)
        return out

    @property
    def holes(self) -> list[int]:
        """The lines of the steps left open, ``by(...)``, each once, in order."""
        return list(
            dict.fromkeys(line for leaf in self.leaves for line in leaf.holes if line is not None)
        )

    @property
    def where(self) -> str:
        """``file.py:41-48``: where the proof is written."""
        first, last = self.lines
        span = f"{first}-{last}" if last != first else f"{first}"
        return f"{os.path.basename(self.path)}:{span}"


# }}}


# {{{ the namespace and the values a body runs with


#: The trace in progress, which a theorem called inside it cites rather than evaluates.
_ACTIVE: ContextVar[Any] = ContextVar("lanky_proof_trace", default=None)


def active() -> Any:
    """The trace of a written proof in progress, or the native run of one, or ``None``.

    :meth:`lanky.theory.Theorem.__call__` asks: inside a trace, calling a
    theorem is citing it, whatever its arguments are, and outside one it
    evaluates the claim at concrete values, as it always has.
    """
    return _ACTIVE.get()


@contextmanager
def running(runner: Any) -> Iterator[None]:
    """Have ``runner`` answer :func:`active` while the block runs."""
    token = _ACTIVE.set(runner)
    try:
        yield
    finally:
        _ACTIVE.reset(token)


def namespace(theorem: Any) -> dict[str, Any]:
    """The globals a theorem's body runs in when it is traced.

    The module's live globals, so that a theorem defined later in the file
    can be cited; then the snapshot's copies of what the annotations read
    (:attr:`lanky.theory.Theorem.snapshot`), so that a name the module
    rebound after the claim was read means in the proof what it meant in the
    claim; then lanky's ``all``, ``any``, ``sum`` and ``abs``.
    """
    fn = theorem.fn
    out = dict(getattr(fn, "__globals__", {}))
    snapshot = getattr(theorem, "snapshot", None)
    if snapshot is not None:
        copied = snapshot.namespace
        for code in snapshot.codes:
            for name in code_reads(code).names:
                if name in copied:
                    out[name] = copied[name]
    out.update(BUILTIN_OVERRIDES)
    return out


def body_arguments(
    fn: Any, values: Mapping[str, Any]
) -> tuple[tuple[Any, ...], dict[str, Any], dict[str, Any]]:
    """How a body takes the statement's values: by position, by name, and in its namespace.

    ``values`` holds a value for each variable and hypothesis of the
    statement: symbolic ones in a trace, drawn ones in a native run. A name
    the function takes as a parameter is passed to it, its positional-only
    parameters by position; a name it does not take, a variable or a
    condition the statement has from outside the function (a name bound by
    ``with segment as (alpha, beta, nonzero):``, say), is the third answer,
    which the caller lays over the namespace the body runs in, so that the
    body reads it there at the same value. That is the one hook such a
    statement needs: its theorem lists the outside names among its variables
    and hypotheses, and the body sees them as it sees its own.
    """
    code = fn.__code__
    taken = code.co_varnames[: code.co_argcount + code.co_kwonlyargcount]
    named: dict[str, Any] = {}
    outer: dict[str, Any] = {}
    for name, value in values.items():
        if name in taken:
            named[name] = value
        else:
            outer[name] = value
    positional: list[Any] = []
    for name in code.co_varnames[: code.co_posonlyargcount]:
        if name not in named:
            break
        positional.append(named.pop(name))
    return tuple(positional), named, outer


def is_generator(fn: Any) -> bool:
    """Whether the body yields: a generator function, driven point by point."""
    return bool(getattr(fn, "__code__", None) and fn.__code__.co_flags & inspect.CO_GENERATOR)


def _own_codes(code: Any) -> frozenset[Any]:
    """``code`` and every code object compiled inside it: the body, its helpers, generators."""
    found = {code}
    stack = [code]
    while stack:
        current = stack.pop()
        for constant in current.co_consts:
            if isinstance(constant, pytypes.CodeType) and constant not in found:
                found.add(constant)
                stack.append(constant)
    return frozenset(found)


# }}}


# {{{ reading the bytecode: an if, an assert


@functools.lru_cache(maxsize=64)
def _instructions(code: Any) -> tuple[tuple[Any, ...], dict[int, int]]:
    """The instructions of a code object, and an offset-to-index table."""
    listing = tuple(dis.get_instructions(code))
    return listing, {instruction.offset: index for index, instruction in enumerate(listing)}


def _branches_on(frame: Any) -> bool:
    """Whether the truth value ``frame`` asks for is a conditional jump's: an ``if``.

    CPython 3.12 asks at the jump itself, ``POP_JUMP_IF_FALSE``; 3.13 and
    later at a ``TO_BOOL``, or a comparison told to answer a bool, right
    before it. An ``and`` or an ``or`` used as a value copies its operand
    first (``COPY``), and ``not`` used as a value negates it, and neither is
    a case split.
    """
    listing, index_of = _instructions(frame.f_code)
    position = index_of.get(frame.f_lasti)
    if position is None:
        return False
    current = listing[position]
    if current.opname.startswith("POP_JUMP_IF"):
        pass
    elif current.opname == "TO_BOOL" or (
        current.opname == "COMPARE_OP" and str(current.argrepr).startswith("bool(")
    ):
        following = position + 1
        if following >= len(listing) or not listing[following].opname.startswith("POP_JUMP_IF"):
            return False
    else:
        return False
    previous = listing[position - 1] if position else None
    return previous is None or previous.opname != "COPY"


def _the_jump(frame: Any) -> tuple[int, Any] | None:
    """The conditional jump the truth value ``frame`` asks for decides: ``(index, instruction)``."""
    listing, index_of = _instructions(frame.f_code)
    position = index_of.get(frame.f_lasti)
    if position is None:
        return None
    current = listing[position]
    if current.opname.startswith("POP_JUMP_IF"):
        return position, current
    if current.opname == "TO_BOOL" or (
        current.opname == "COMPARE_OP" and str(current.argrepr).startswith("bool(")
    ):
        following = position + 1
        if following < len(listing) and listing[following].opname.startswith("POP_JUMP_IF"):
            return following, listing[following]
    return None


def _lands_on_the_assertion(code: Any, index: int | None) -> bool:
    """Whether the instructions from ``index`` raise an assert's error before anything else."""
    listing, index_of = _instructions(code)
    for _ in range(8):
        if index is None or index >= len(listing):
            return False
        instruction = listing[index]
        if instruction.opname == "LOAD_ASSERTION_ERROR":
            return True
        if instruction.opname in ("NOP", "POP_TOP", "NOT_TAKEN", "EXTENDED_ARG", "CACHE"):
            index += 1
        elif instruction.opname in ("JUMP_FORWARD", "JUMP", "JUMP_NO_INTERRUPT"):
            index = index_of.get(instruction.argval)
        else:
            return False
    return False


def _assert_answer(frame: Any) -> bool | None:
    """The answer that fails the ``assert`` whose question ``frame`` asks; ``None`` for no assert.

    An ``assert``'s test jumps past it when it holds and falls, or jumps,
    to ``LOAD_ASSERTION_ERROR`` when it does not; each link of a chained
    comparison, and each operand of an ``and``, is such a jump of its own.
    So the answer that lands on the assertion error is the one that fails the
    step: ``False`` for a comparison, ``True`` for ``assert not ...``.
    """
    found = _the_jump(frame)
    if found is None:
        return None
    index, jump = found
    if jump.opname not in ("POP_JUMP_IF_TRUE", "POP_JUMP_IF_FALSE"):
        return None
    code = frame.f_code
    _listing, index_of = _instructions(code)
    taken = index_of.get(jump.argval)
    fall = index + 1
    on_true, on_false = (taken, fall) if jump.opname == "POP_JUMP_IF_TRUE" else (fall, taken)
    if _lands_on_the_assertion(code, on_false):
        return False
    if _lands_on_the_assertion(code, on_true):
        return True
    return None


@functools.lru_cache(maxsize=32)
def _module_tree(path: str, stamp: tuple[int, int]) -> ast.Module | None:
    """The parsed source of ``path``, or ``None`` where it cannot be read."""
    del stamp  # in the key alone, so that an edited file is read again
    lines = linecache.getlines(path)
    if not lines:
        return None
    try:
        return ast.parse("".join(lines), filename=path)
    except SyntaxError:
        return None


def _stamp(path: str) -> tuple[int, int]:
    """What tells one version of a file from another: its time and size."""
    try:
        status = os.stat(path)
    except OSError:
        return (0, 0)
    return (status.st_mtime_ns, status.st_size)


@functools.lru_cache(maxsize=32)
def _asserts_of(path: str, stamp: tuple[int, int]) -> tuple[ast.Assert, ...]:
    """The ``assert`` statements of the file at ``path``, in this version of it."""
    tree = _module_tree(path, stamp)
    if tree is None:
        return ()
    return tuple(node for node in ast.walk(tree) if isinstance(node, ast.Assert))


def _asserts_in(code: Any) -> tuple[ast.Assert, ...]:
    """The ``assert`` statements of the file ``code`` was compiled from."""
    return _asserts_of(code.co_filename, _stamp(code.co_filename))


def _assert_at(frame: Any) -> ast.Assert | None:
    """The ``assert`` whose test the instruction ``frame`` runs is in, read off the source."""
    listing, index_of = _instructions(frame.f_code)
    position = index_of.get(frame.f_lasti)
    where = listing[position].positions if position is not None else None
    line = frame.f_lineno
    best: ast.Assert | None = None
    for node in _asserts_in(frame.f_code):
        test = node.test
        first, last = test.lineno, test.end_lineno or test.lineno
        if where is not None and where.lineno is not None:
            start = (where.lineno, where.col_offset or 0)
            end = (where.end_lineno or where.lineno, where.end_col_offset or 0)
            inside = (first, test.col_offset) <= start and end <= (
                last,
                test.end_col_offset or 0,
            )
        else:
            inside = first <= line <= last
        if inside and (best is None or node.lineno >= best.lineno):
            best = node
    return best


def _assert_at_line(code: Any, line: int) -> ast.Assert | None:
    """The ``assert`` of ``code``'s file whose statement spans ``line``, the innermost."""
    best: ast.Assert | None = None
    for node in _asserts_in(code):
        if node.lineno <= line <= (node.end_lineno or node.lineno) and (
            best is None or node.lineno >= best.lineno
        ):
            best = node
    return best


def _link_line(node: ast.Assert | None, index: int, fallback: int) -> int:
    """The line of the ``index``-th question of an ``assert``: the term its link reaches."""
    if node is None:
        return fallback
    test = node.test
    if isinstance(test, ast.Compare) and index < len(test.comparators):
        return test.comparators[index].lineno
    if isinstance(test, ast.BoolOp) and index < len(test.values):
        return test.values[index].lineno
    return node.lineno


# }}}


# {{{ the trace


@dataclass(frozen=True, eq=False)
class _Reasons:
    """What an ``assert``'s ``by(...)`` gave, as citations, learned from its failing run."""

    facts: tuple[Citation, ...]
    hole: bool


class _Stopped(Exception):  # noqa: N818 - not an error: a run stopped to learn a reason
    """A run stopped at an ``assert`` answered "false", once its reason is read."""


@dataclass(eq=False)
class _Open:
    """An ``assert`` being run: its questions so far, each with what holds when it passes."""

    index: int
    code: Any
    node: ast.Assert | None
    line: int
    offset: int
    depth: int
    holds: list[tuple[Any, int]] = field(default_factory=list)


@dataclass(eq=False)
class _Loop:
    """A loop over a domain of the conclusion, open on a path.

    Attributes:
        level: Which nested ``for`` of the conclusion it walks, ``0`` the outermost.
        names: The variables of its point.
        reverse: Whether it walks the domain from the top down, ``reversed(...)``.
        line: The line of the ``for``.
        inner: Whether a loop over the next level ran at its point, which
            closes the point.
    """

    level: int
    names: tuple[str, ...]
    reverse: bool
    line: int | None
    inner: bool = False


@dataclass(eq=False)
class _Path:
    """One run of the body: the answers it was given, and what it asked, asserted and cited."""

    schedule: list[bool]
    reasons: list[_Reasons]
    facts: list[Any] = field(default_factory=list)
    memo: dict[str, bool] = field(default_factory=dict)
    questions: list[Question] = field(default_factory=list)
    branches: list[bool] = field(default_factory=list)
    branch_events: list[int] = field(default_factory=list)
    branch_asserts: list[int] = field(default_factory=list)
    events: list[tuple[str, str]] = field(default_factory=list)
    returns: dict[Any, int] = field(default_factory=dict)
    order: list[Any] = field(default_factory=list)
    asked: int = 0
    asserts: int = 0
    open: _Open | None = None
    learned: _Reasons | None = None
    failing: _Open | None = None
    complete: bool = True
    state: str = "before"
    loops: int = 0
    closed: int | None = None
    open_loops: list[_Loop] = field(default_factory=list)
    closings: int = 0
    leaf_facts: tuple[Citation, ...] | None = None
    leaf_line: int | None = None
    leaf_hole: bool = False
    leaf: Leaf | None = None


def _takes(name: str, names: list[str], given: int) -> str:
    """``h takes 1 value, its variable k, and is given 3``."""
    plural = "" if len(names) == 1 else "s"
    variables = f"its variable{plural} {', '.join(names)}" if names else "no variables"
    return f"{name} takes {len(names)} value{plural}, {variables}, and is given {given}"


class _ClaimRef:
    """What a citation of the claim's own conclusion cites while the body is traced.

    The claim's parameters are known only once every path is traced (how
    many nested ``for`` levels the proof loops over), so a citation of
    ``name.conclusion[p]`` cites this, and :meth:`_Tracer.define_claim`
    puts the :class:`ClaimDef` in its place.
    """

    def __init__(self, name: str) -> None:
        self.__name__ = name
        self.name = name

    def written(self, values: tuple[Any, ...], bracket: bool = True) -> str:
        """``line_taylor.conclusion[n - 1]``, the values as given."""
        del bracket
        return f"{self.name}[{', '.join(shown(value) for value in values)}]"


@dataclass(frozen=True, eq=False)
class _Called(Citation):
    """A claim called for inputs in a proof, ``gauss(n - 1)``: a citation, and a tree to go on in.

    ``other(x, y).conclusion[p]`` is the conclusion at ``p`` for those inputs.

    Attributes:
        inputs: How many of :attr:`values` are the claim's inputs; the rest
            are its conclusion's point, ``None`` until lanky finds it.
    """

    inputs: int = 0

    @property
    def conclusion(self) -> Any:
        """The conclusion for the inputs this call gave."""
        from lanky.surface import Conclusion

        assert self.values is not None
        return Conclusion(self.source, (), inputs=tuple(self.values[: self.inputs]))


class _Dom:
    """A loop over a domain of the conclusion in a trace: one symbolic point, the guard known."""

    def __init__(self, tracer: _Tracer, level: int, reverse: bool, line: int | None) -> None:
        self.tracer = tracer
        self.level = level
        self.reverse = reverse
        self.line = line
        self.started = False

    def __iter__(self) -> _Dom:
        """A loop over it takes it as its own iterator."""
        return self

    def __next__(self) -> Any:
        """The one point, the first time; then the loop is done."""
        if not self.started:
            self.started = True
            return self.tracer.enter(self)
        self.tracer.leave(self)
        raise StopIteration

    def __repr__(self) -> str:
        """``<the loop over line_taylor.conclusion.domain>``."""
        return f"<the loop over {self.tracer.name}.conclusion.domain at level {self.level}>"


class _Tracer:
    """The trace of one theorem's body: its runs, one per path and per assert, and their record."""

    def __init__(self, theorem: Any) -> None:
        from lanky.surface import levels

        self.theorem = theorem
        self.fn = theorem.fn
        self.name = getattr(theorem, "qualname", None) or theorem.__name__
        self.codes = _own_codes(self.fn.__code__)
        self.namespace = namespace(theorem)
        self.variables: dict[str, Any] = dict(theorem.variables)
        self.hypotheses: dict[str, Any] = dict(theorem.hypotheses)
        self.goal = theorem.goal
        #: The nested ``for`` levels of the conclusion, ``(binders, guard)`` each.
        self.levels = levels(self.goal)
        self.path: _Path | None = None
        self.claim_ref = _ClaimRef(f"{self.name}.conclusion")
        self.loop_line: int | None = None
        self.claim_line: int | None = None
        #: How many levels deep a ``yield`` closes the conclusion, the same on every path.
        self.point_depth: int | None = None
        #: The line of the first ``yield`` at that depth.
        self.point_line: int | None = None
        #: Whether each level's loop runs reversed, the same on every path.
        self.reversed: dict[int, bool] = {}
        self.deepest = 0

    # {{{ what the body sees

    @property
    def binders(self) -> list[tuple[Var, Any]]:
        """The variables of every level of the conclusion, outermost first."""
        return [binder for binders, _ in self.levels for binder in binders]

    def types(self) -> dict[str, Any]:
        """The sort of every name the proof's terms mention: the theorem's and the conclusion's."""
        types = dict(self.variables)
        for var, domain in self.binders:
            types.setdefault(var.name, domain)
        return types

    def _base_facts(self) -> list[Any]:
        """What holds on every path before any split: the theorem's hypotheses."""
        return [part for _name, prop in self.hypotheses.items() for part in conjuncts(prop)]

    def ask(self, prop: Any, frame: Any) -> bool:
        """The truth value of a question the body's own ``if`` or ``assert`` asks (see the module).

        Raises:
            SymbolicBoolError: If the question does not come from an ``if``
                or an ``assert`` in the body's own code.
            ProofError: If one run asks more than :data:`MAX_QUESTIONS`.
        """
        if frame is None or frame.f_code not in self.codes:
            raise SymbolicBoolError(
                f"the truth value of {render(prop)} was asked for outside the proof's own "
                "code, by a function it calls, by an `in` test or by sorting: in a proof only "
                "an if of the proof's own is a case split, and an assert a step"
            )
        path = self.path
        assert path is not None
        path.asked += 1
        if path.asked > MAX_QUESTIONS:
            raise ProofError(
                "question",
                f"the proof asks the truth value of {render(prop)} again and again: a while "
                "loop over a symbolic condition never ends; split the case with if",
                frame.f_lineno,
            )
        failing = _assert_answer(frame)
        node = _assert_at(frame)
        if failing is not None:
            return self._assert_question(prop, frame, node, failing)
        if node is not None:
            raise ProofError(
                "assert",
                f"the assert at line {node.lineno} asks for the truth value of {render(prop)} "
                "in a way that is no step: an assert states a comparison, a chain of them, "
                "or several joined by and",
                node.lineno,
            )
        if not _branches_on(frame):
            raise SymbolicBoolError(
                f"the truth value of {render(prop)} was asked for by the proof, but not by "
                "an if: and, or and not used as values, and a comparison of tuples, would "
                "keep one side of the question; split the case with if"
            )
        self._close(path)
        key = render(prop)
        if key in path.memo:
            return path.memo[key]
        decided = decide(prop, path.facts, self.types())
        if decided is None:
            if path.closed is not None:
                raise ProofError(
                    "yield",
                    f"the point was closed at line {path.closed} by its yield; a case split "
                    "after it splits nothing the point needs: split before the yield",
                    frame.f_lineno,
                )
            index = len(path.branches)
            answer = path.schedule[index] if index < len(path.schedule) else True
            path.branches.append(answer)
            path.branch_asserts.append(path.asserts)
            forced = False
        else:
            answer, forced = decided, True
        path.memo[key] = answer
        question = Question(prop, frame.f_lineno, answer, forced)
        path.questions.append(question)
        path.order.append(question)
        path.facts.append(question.condition)
        path.events.append(("ask", key))
        if not forced:
            path.branch_events.append(len(path.events))
        return answer

    def _assert_question(self, prop: Any, frame: Any, node: Any, failing: bool) -> bool:
        """A question of an ``assert``: "false" the first time, "true" once its reason is read."""
        path = self.path
        assert path is not None
        offset = frame.f_lasti
        current = path.open
        if (
            current is None
            or current.code is not frame.f_code
            or current.node is not node
            or offset <= current.offset
        ):
            self._close(path)
            if path.state == "after":
                raise ProofError(
                    "assert",
                    f"this step comes after the loop over {self.name}.conclusion.domain, and "
                    "belongs to no point; move it into the loop",
                    node.lineno if node is not None else frame.f_lineno,
                )
            if path.closed is not None:
                raise ProofError(
                    "assert",
                    f"the point was closed at line {path.closed}; a step after it is for "
                    "nothing: assert it before the yield",
                    node.lineno if node is not None else frame.f_lineno,
                )
            line = node.lineno if node is not None else frame.f_lineno
            current = _Open(path.asserts, frame.f_code, node, line, offset, len(path.branches))
            path.asserts += 1
            path.open = current
        current.offset = offset
        if current.index >= len(path.reasons):
            # the first time on this path: fail it, so that Python reads its by(...)
            path.failing = current
            return failing
        holds = prop if not failing else negated(prop)
        current.holds.append((holds, _link_line(current.node, len(current.holds), frame.f_lineno)))
        path.facts.append(holds)
        return not failing

    def _close(self, path: _Path) -> None:
        """Record the ``assert`` being run as a step of the path, once its questions are asked."""
        current = path.open
        if current is None:
            return
        path.open = None
        reasons = path.reasons[current.index]
        parts = _parts(current.holds, reasons, current.line)
        path.order.append(Asserted(current.line, parts, reasons.facts, reasons.hole, current.depth))
        path.events.append(("assert", str(current.line)))

    def number(self, term: Any, frame: Any) -> None:
        """Refuse a number's truth value to the body's own code: compare it instead."""
        if frame is not None and frame.f_code in self.codes:
            raise SymbolicBoolError(
                f"the truth value of {render(term)} was asked for by the proof, and a number "
                f"is no truth value; compare it, as in if {render(term)} != 0:"
            )

    def cite(self, source: Any, values: tuple, named: Mapping[str, Any], frame: Any) -> Citation:
        """A condition at a point, ``pde[i, a - 2, b]``, written at the line ``frame`` runs."""
        line = self._line(frame)
        names = self._binder_names(source)
        called = Citation(source).name
        if len(values) != len(names):
            example = f"{called}[{', '.join(names)}]" if names else None
            raise ProofError(
                "cite",
                _takes(called, names, len(values))
                + (
                    "; it is cited whole, by its name alone"
                    if not names
                    else f", one per variable of its for, as {example}"
                ),
                line,
                fix=example if names else called,
            )
        citation = Citation(
            source, tuple(family_value(value) for value in values), line, bracket=True
        )
        if self.path is not None:
            self.path.events.append(("cite", citation.text()))
        return citation

    def cite_theorem(
        self, theorem: Any, values: tuple, named: Mapping[str, Any], frame: Any
    ) -> Citation:
        """Another claim called for inputs, ``gauss(n - 1)``: a citation; the claim itself refused.

        The values are the claim's inputs, its parameters, by position or by
        name. Inside a ``with`` block the claims share, the block's names
        fill the condition's inputs, and the call gives the claim's own. The
        claim's conclusion's point, where it has one, is left for lanky to
        find, or given after, ``other(x).conclusion[p]``.
        """
        line = self._line(frame)
        if theorem is self.theorem:
            raise self._self_call(line, values, named)
        from lanky.surface import levels

        inputs = [name for name, _ in getattr(theorem, "variables", ())]
        own = [name for name, _ in getattr(theorem, "own_variables", theorem.variables)]
        bound = set(getattr(theorem, "bound", ()))
        names = inputs
        filled: dict[str, Any] = {}
        mine = set(getattr(self.theorem, "bound", ()))
        if bound and bound <= mine and len(values) + len(named) <= len(own):
            # a sibling in the same block: the block's names are this proof's too
            names = own
            filled = {name: Var(name) for name in inputs if name not in own}
        called = getattr(theorem, "__name__", "the claim")
        if len(values) > len(names):
            raise ProofError(
                "cite",
                f"{called} takes {len(names)} input{'' if len(names) == 1 else 's'}, "
                f"{', '.join(names) or 'none'}, and is given {len(values) + len(named)}; a "
                f"point of its conclusion is given after, as {called}(...).conclusion[...]",
                line,
                fix=f"{called}({', '.join(names)})" if names else called,
            )
        given = dict(zip(names, values, strict=False))
        for key, value in named.items():
            if key not in names:
                raise ProofError(
                    "cite",
                    f"{called} has no input {key}: its inputs are {', '.join(names) or 'none'}",
                    line,
                )
            if key in given:
                # each value is written once, as Python itself asks of a call
                raise ProofError(
                    "cite", f"{called} is given {key} twice, by its place and by its name", line
                )
            given[key] = value
        missing = [name for name in names if name not in given]
        if missing:
            raise ProofError(
                "cite",
                f"{called} needs a value for {', '.join(missing)}: a claim called for inputs "
                "is given each of them, or cited by its name alone, where lanky finds them",
                line,
                fix=f"{called}({', '.join(names)})",
            )
        given.update(filled)
        point = sum(len(binders) for binders, _ in levels(theorem.goal))
        full = (
            *(family_value(given[name]) for name in inputs),
            *(None for _ in range(point)),
        )
        citation = _Called(theorem, full, line, inputs=len(inputs))
        if self.path is not None:
            self.path.events.append(("cite", citation.text()))
        return citation

    def _self_call(
        self, line: int | None, values: tuple = (), named: Mapping[str, Any] | None = None
    ) -> ProofError:
        """The refusal of a claim that calls itself in its own proof, with the fix (design 3.4)."""
        name = self.name
        given = [shown(value) for value in values]
        given += [f"{key}={shown(value)}" for key, value in (named or {}).items()]
        written = f"{name}({', '.join(given)})"
        binders = [var.name for var, _ in self.binders]
        own = [variable for variable, _ in getattr(self.theorem, "own_variables", ())]
        changed = [
            (variable, value)
            for variable, value in zip(own, values, strict=False)
            if not (isinstance(value, Var) and value.name == variable)
        ]
        if binders and len(values) == len(binders) and not named:
            fix = f"{name}.conclusion[{', '.join(given)}]"
            how = (
                "an earlier case is the conclusion at an earlier point of its domain, "
                "in brackets"
            )
        elif changed:
            variable, value = changed[0]
            fix = f"{name}.conclusion[{shown(value)}]"
            how = (
                f"to argue from an earlier case, put {variable} in the conclusion's for, "
                f"-> all(... for {variable} in ...), and cite {fix}"
            )
        else:
            fix = f"{name}.conclusion[n - 1]"
            how = (
                "to argue from an earlier case, put the variable in the conclusion's for and "
                f"cite {fix}"
            )
        where = f"{os.path.basename(self.theorem.path)}:{line}" if line else "its body"
        return ProofError(
            "self-reference",
            f"{written} at {where} calls the claim in its own proof, and a claim does not "
            f"call itself; {how}",
            line,
            fix=fix,
        )

    def condition(self, claim: Any, name: str, frame: Any) -> Any:
        """``name.conditions.ode``: in the claim's own proof, the fact ``ode`` names there."""
        if claim is not self.theorem:
            raise ProofError(
                "cite",
                f"{name} is a condition of {claim.__name__}, which {claim.__name__}'s proof "
                f"assumes; {self.name}'s proof cites {claim.__name__} itself, its conclusion "
                "for inputs it is given",
                self._line(frame),
            )
        return Given(name, self.hypotheses[name], self)

    def _binder_names(self, source: Any) -> list[str]:
        """The variables a fact takes values for, outermost first."""
        if isinstance(source, Given):
            parts = [shape_of(part) for part in source.parts]
            with_binders = [part for part in parts if part.binders]
            if not with_binders:
                return []
            return [var.name for var, _ in with_binders[0].binders]
        term = getattr(source, "term", None)
        if term is None:
            return []
        return [var.name for var, _ in shape_of(term).binders]

    def _line(self, frame: Any) -> int | None:
        """The line of the body that ``frame``, or the body's frame it was called from, runs."""
        while frame is not None:
            if frame.f_code in self.codes:
                return frame.f_lineno
            frame = frame.f_back
        return None

    # }}}

    # {{{ the conclusion's domain, its points and the claim's own conclusion

    def _current(self) -> tuple[list[str], list[int]]:
        """The point the loops are at, by name, and each name's direction, ``1`` or ``-1``."""
        path = self.path
        assert path is not None
        names: list[str] = []
        directions: list[int] = []
        for loop in path.open_loops:
            names += loop.names
            directions += [-1 if loop.reverse else 1] * len(loop.names)
        return names, directions

    def _current_point(self) -> str:
        """The point the loop is at, as a message says it: ``n``, ``(i, a, b)``."""
        names, _ = self._current()
        return names[0] if len(names) == 1 else f"({', '.join(names)})"

    def loop(self, conclusion: Any, reverse: bool, frame: Any) -> _Dom:
        """``for n in name.conclusion.domain:``, or ``reversed(...)``: the loop over a level."""
        path = self.path
        assert path is not None
        line = self._line(frame)
        name = self.name
        level = len(conclusion.point)
        if conclusion.inputs is not None:
            raise ProofError(
                "claim",
                f"inside {name}'s own proof its conclusion is for this proof's inputs, and "
                f"{conclusion.text()} gives it others; a claim does not call itself",
                line,
                fix=f"for ... in {name}.conclusion.domain:",
            )
        opened = path.open_loops
        if level > len(opened):
            outer = conclusion._spelled(len(opened))
            raise ProofError(
                "claim",
                f"{conclusion.text()}.domain is the domain at a point of {outer}.domain, and "
                "no loop is at that point here; loop over the outer domain first",
                line,
                fix=f"for ... in {outer}.domain:",
            )
        if level < len(opened):
            raise ProofError(
                "claim",
                f"the body loops over {conclusion.text()}.domain inside a loop over it; a "
                "proof is one loop over the conclusion's points, each closed with "
                "yield by(...)",
                line,
            )
        for index, values in enumerate(conclusion.point):
            expected = opened[index].names
            if len(values) != len(expected) or not all(
                isinstance(value, Var) and value.name == want
                for value, want in zip(values, expected, strict=False)
            ):
                at = ", ".join(expected)
                spelled = f"{name}.conclusion" + "".join(
                    f"[{', '.join(loop.names)}]" for loop in opened[: index + 1]
                )
                raise ProofError(
                    "claim",
                    f"{conclusion.text()}.domain is the domain at another point than the one "
                    f"the loop is at, ({at}); the inner loop walks the conclusion at the "
                    "point the outer one is at",
                    line,
                    fix=f"for ... in {spelled}.domain:",
                )
        if reverse:
            self._refuse_unbounded(conclusion, level, line)
        return _Dom(self, level, reverse, line)

    def _bounded(self, level: int) -> bool:
        """Whether every variable of a level's domain has a top: ``Fin[p]``, or ``k <= p``."""
        from lanky.proofs.compile import _upper_bound

        binders, guard = self.levels[level]
        conditions = [*self._base_facts(), *conjuncts(guard)]
        return all(
            _upper_bound(var.name, domain, conditions) is not None for var, domain in binders
        )

    def _refuse_unbounded(self, conclusion: Any, level: int, line: int | None) -> None:
        """Refuse ``reversed(...)`` over a domain with no top to start from."""
        from lanky.proofs.compile import _upper_bound

        binders, guard = self.levels[level]
        conditions = [*self._base_facts(), *conjuncts(guard)]
        for var, domain in binders:
            if _upper_bound(var.name, domain, conditions) is None:
                raise ProofError(
                    "claim",
                    f"reversed({conclusion.text()}.domain) walks the domain from the top down, "
                    f"and {var.name} in {domain} has no top; reversed fits a bounded domain, "
                    f"as {var.name} in Fin[p] or {var.name} <= p in the conclusion's for",
                    line,
                    fix=f"for ... in {conclusion.text()}.domain:",
                )

    def enter(self, dom: _Dom) -> Any:
        """The loop's one point: the level's variables, its guard known on the path."""
        path = self.path
        assert path is not None
        level = dom.level
        if level == 0 and path.loops:
            raise ProofError(
                "claim",
                f"the body loops over {self.name}.conclusion.domain twice; a proof is one loop "
                "over the conclusion's points, each closed with yield by(...)",
                dom.line,
            )
        self._close(path)
        if path.open_loops:
            outer = path.open_loops[-1]
            if outer.inner:
                raise ProofError(
                    "claim",
                    "the body loops over the domain at this point twice; a proof is one loop "
                    "over each domain's points, each closed with yield by(...)",
                    dom.line,
                )
            if path.closed is not None:
                raise ProofError(
                    "yield",
                    f"the point was closed at line {path.closed} by its yield; a loop after it "
                    "closes nothing it needs",
                    dom.line,
                )
            outer.inner = True
        else:
            path.loops += 1
        previous = self.reversed.setdefault(level, dom.reverse)
        if previous != dom.reverse:
            raise ProofError(
                "paths",
                "the loop over this domain runs reversed on one path and not on another; a "
                "proof walks each domain one way",
                dom.line,
            )
        binders, guard = self.levels[level]
        names = tuple(var.name for var, _ in binders)
        path.open_loops.append(_Loop(level, names, dom.reverse, dom.line))
        self.deepest = max(self.deepest, len(path.open_loops))
        path.state = "at"
        if self.loop_line is None:
            self.loop_line = dom.line
        path.facts.extend(conjuncts(guard))
        path.events.append(("point", str(level)))
        variables = [var for var, _ in binders]
        return variables[0] if len(variables) == 1 else tuple(variables)

    def leave(self, dom: _Dom) -> None:
        """The loop is done on this path: its point has to be closed (the closing rule)."""
        path = self.path
        assert path is not None
        self._close(path)
        current = path.open_loops[-1] if path.open_loops else None
        if current is None or current.level != dom.level:  # pragma: no cover - Python's own loops
            return
        if not current.inner and path.closed is None:
            raise self._unclosed(path, dom.line)
        path.open_loops.pop()
        if path.open_loops:
            # the outer point is closed by the loop over its own domain
            path.closed = path.closed or dom.line
        else:
            path.state = "after"

    def _unclosed(self, path: _Path, line: int | None, word: str = "yield") -> ProofError:
        """The refusal of a case that ends with no closing line, at the line that ends it.

        ``line`` is where the run noticed, the line of the loop or of the
        return; the case is found from the source (:func:`_case_end`).
        """
        from lanky.proofs.report import case_text

        loop_line = path.open_loops[-1].line if path.open_loops else None
        kind, end = _case_end(self.fn, path.questions, loop_line)
        case = case_text(
            [
                (question.condition, question.line)
                for question in path.questions
                if not question.forced
            ],
            self.theorem.path,
        )
        if case:
            case = case[0].lower() + case[1:] + ", "
        if kind == "continue":
            said = f"{case}continue at line {end} ends the case with no closing line"
        elif kind == "return":
            said = f"{case}a bare return at line {end} ends the case with no closing line"
        elif end is not None:
            said = f"{case}the case ends at line {end} with no closing line"
        else:
            said = f"{case}the case ends with no closing line"
        return ProofError(
            "close",
            f"{said}: close it with {word} by() if it follows directly, or give its reasons, "
            f"{word} by(f, g)",
            end if end is not None else line,
            fix=f"{word} by()",
        )

    def conclusion_fact(self, conclusion: Any, line: int | None) -> Citation:
        """A conclusion cited in ``by(...)``: the claim's own at an earlier point, or another's."""
        theorem = conclusion.claim
        if theorem is not self.theorem:
            return self._other_conclusion(conclusion, line)
        path = self.path
        assert path is not None
        name = self.name
        if conclusion.inputs is not None:
            raise ProofError(
                "self-reference",
                f"{conclusion.text()} gives {name} inputs in its own proof, and a claim does "
                "not call itself; inside its proof the conclusion is for this proof's inputs",
                line,
                fix=f"{name}.conclusion[...]",
            )
        if not conclusion.point:
            earlier = f"{name}.conclusion[{_earlier_text(self._next_names())}]"
            raise ProofError(
                "claim",
                f"{name}.conclusion alone is the whole conclusion, the one being proved; cite "
                f"it at an earlier point, as {earlier}",
                line,
                fix=earlier,
            )
        values = conclusion.values
        written = conclusion.text()
        if not path.open_loops:
            raise ProofError(
                "claim",
                f"{written} is the conclusion at an earlier point of the loop over "
                f"{name}.conclusion.domain, and it is cited outside that loop; cite it inside "
                f"for {_point_text(self._next_names())} in {name}.conclusion.domain:",
                line,
            )
        names, directions = self._current()
        verdict = _earlier(names, values, directions, path.facts, self.types())
        if verdict == "later":
            message = f"{written} is not filled in yet when the loop is at {self._current_point()}"
            fix = (
                f"cite the conclusion at a point the loop has filled in, as "
                f"{name}.conclusion{_earlier_example(path.open_loops)}"
            )
            loop = path.open_loops[0]
            if len(path.open_loops) == 1 and not loop.reverse and self._bounded(0):
                # an argument from the point above: the loop runs from the top down
                message += (
                    "; an argument from the point above runs the loop over the bounded "
                    "domain from the top down"
                )
                fix = f"for {', '.join(loop.names)} in reversed({name}.conclusion.domain):"
            raise ProofError("later", message, line, fix=fix)
        if verdict == "same":
            what = (
                f"the point the loop is at, {self._current_point()}, which this step is "
                "filling in"
                if len(values) == len(names)
                else f"a part of the conclusion that holds the point the loop is at, "
                f"{self._current_point()}, which this step is filling in"
            )
            raise ProofError(
                "later",
                f"{written} is {what}",
                line,
                fix=f"cite the conclusion at a point the loop has filled in, as "
                f"{name}.conclusion{_earlier_example(path.open_loops)}",
            )
        if self.claim_line is None:
            self.claim_line = line
        citation = Citation(
            self.claim_ref, tuple(family_value(value) for value in values), line, bracket=True
        )
        path.events.append(("cite", written))
        return citation

    def _next_names(self) -> list[str]:
        """The variables of the conclusion's outermost ``for``, as an example names them."""
        return [var.name for var, _ in self.levels[0][0]] if self.levels else ["n"]

    def _other_conclusion(self, conclusion: Any, line: int | None) -> Citation:
        """Another claim's conclusion, whole or at a point, for inputs given or found by lanky."""
        from lanky.surface import levels

        theorem = conclusion.claim
        inputs = conclusion.inputs
        if inputs is None and not conclusion.point:
            return Citation(theorem, None, line)
        count = len(getattr(theorem, "variables", ()))
        total = sum(len(binders) for binders, _ in levels(theorem.goal))
        given = tuple(inputs) if inputs is not None else (None,) * count
        point = conclusion.values
        values = (*given, *point, *(None for _ in range(total - len(point))))
        citation = Citation(
            theorem, tuple(family_value(value) for value in values), line, bracket=True
        )
        if self.path is not None:
            self.path.events.append(("cite", conclusion.text()))
        return citation

    # }}}

    # {{{ a run

    @contextmanager
    def _tracing(self, path: _Path) -> Iterator[None]:
        """Run with this tracer answering the body's questions and recording its returns."""
        self.path = path
        previous = sys.getprofile()

        def profile(frame: Any, event: str, arg: Any) -> None:
            if event == "return" and frame.f_code in self.codes:
                path.returns[frame.f_code] = frame.f_lineno
            if previous is not None:
                previous(frame, event, arg)

        sys.setprofile(profile)
        try:
            with running(self), asking_proof_questions(self):
                yield
        finally:
            sys.setprofile(previous)

    def run(self, schedule: list[bool], reasons: list[_Reasons]) -> _Path:
        """Run the body once, splits answered by ``schedule``, asserts by ``reasons``."""
        path = _Path(list(schedule), list(reasons))
        path.facts = self._base_facts()
        fn = self.fn
        values: dict[str, Any] = {name: Var(name) for name in self.variables}
        values.update({name: Given(name, prop, self) for name, prop in self.hypotheses.items()})
        positional, named, outer = body_arguments(fn, values)
        globals_ = dict(self.namespace)
        globals_.update(outer)
        body = pytypes.FunctionType(
            fn.__code__, globals_, fn.__name__, fn.__defaults__, fn.__closure__
        )
        body.__kwdefaults__ = fn.__kwdefaults__
        with self._tracing(path):
            try:
                if is_generator(fn):
                    self._drive(body, positional, named, path)
                else:
                    result = self._call(lambda: body(*positional, **named), path)
                    self._returned(result, path)
                self._close(path)
                path.leaf = Leaf(
                    tuple(path.questions),
                    path.leaf_facts,
                    path.leaf_line,
                    tuple(path.order),
                    path.leaf_hole,
                    path.loops > 0,
                )
            except _Stopped:
                path.complete = False
        return path

    def _drive(self, body: Any, positional: tuple, named: dict[str, Any], path: _Path) -> None:
        """Drive a body that yields: each ``yield by(...)`` closes the point the loop is at."""
        generator = self._call(lambda: body(*positional, **named), path)
        while True:
            try:
                value = self._call(lambda: generator.send(None), path)
            except StopIteration as stop:
                self._ended(stop.value, path)
                return
            frame = generator.gi_frame
            self._yielded(value, path, frame.f_lineno if frame is not None else None)

    def _ended(self, value: Any, path: _Path) -> None:
        """A body that yields has returned: refuse a return that leaves a case open, or mixes."""
        line = path.returns.get(self.fn.__code__)
        self._close(path)
        name = self.name
        if path.open_loops:
            if value is None and path.closed is None:
                raise self._unclosed(path, line)
            if value is None:
                raise ProofError(
                    "close",
                    f"a bare return at line {line} ends the loop over {name}.conclusion.domain "
                    "at its first point; drop it, and the loop goes on to its next point",
                    line,
                )
            raise ProofError(
                "return",
                f"return by(...) ends the loop over {name}.conclusion.domain at its first "
                "point; in a proof that loops, each case closes with yield by(...)",
                line,
                fix=f"yield {_by_text(value)}",
            )
        if value is not None:
            raise ProofError(
                "return",
                "this proof closes its cases with yield and ends with return by(...): one "
                "proof does not mix the two; the cases of a loop close with yield by(...), and "
                "a proof with no loop closes with return by(...)",
                line,
                fix="yield by(...) in the loop, and no return",
            )
        if not path.closings:
            raise self._unclosed(path, line)

    def _call(self, thunk: Any, path: _Path) -> Any:
        """Run part of the body, turning what it raises into a refusal at its line."""
        from lanky.surface import FormError, OutsideAProof

        try:
            return thunk()
        except (ProofError, _Stopped, StopIteration):
            raise
        except AssertionError as exc:
            self._assertion(exc, path)
            raise AssertionError("unreachable") from None  # pragma: no cover
        except FormError as exc:
            raise ProofError(exc.kind, exc.message, self._raised_at(exc), exc.fix) from None
        except OutsideAProof as exc:
            raise ProofError("claim", str(exc), self._raised_at(exc)) from None
        except SymbolicBoolError as exc:
            raise ProofError("question", str(exc), self._raised_at(exc)) from None
        except RecursionError:
            raise ProofError(
                "raised",
                "the proof calls itself without end; an earlier case of the claim is its "
                f"conclusion at an earlier point, {self.name}.conclusion[...]",
                None,
            ) from None
        except NameError as exc:
            missing = getattr(exc, "name", None)
            if missing == "by":
                raise ProofError(
                    "raised",
                    "by is one of the words of a proof, and the file does not import it",
                    self._raised_at(exc),
                    fix="from lanky import by",
                ) from None
            raise ProofError(
                "raised", f"the proof raised NameError: {exc}", self._raised_at(exc)
            ) from None
        except Exception as exc:  # noqa: BLE001 - the body is the user's, so say what it raised
            raise ProofError(
                "raised", f"the proof raised {type(exc).__name__}: {exc}", self._raised_at(exc)
            ) from None

    def _assertion(self, exc: AssertionError, path: _Path) -> None:
        """An ``assert`` answered "false": read its ``by(...)``, and stop the run to learn it.

        Raises:
            _Stopped: With the reason learned, for the path to run again.
            ProofError: For an assert that fails as Python evaluates it,
                before anything is drawn, and for a message that is no
                ``by(...)``.
        """
        failing = path.failing
        if failing is None:
            line = self._raised_at(exc)
            raise ProofError(
                "false",
                "this step is false as Python evaluates it, with nothing drawn: "
                f"{_source_line(self.theorem.path, line)}",
                line,
            ) from None
        message = exc.args[0] if exc.args else None
        if message is None:
            given = By((), False)
        elif isinstance(message, By):
            given = message
        else:
            raise ProofError(
                "assert",
                "an assert in a proof gives its reason as by(...), or none for a step by "
                f"algebra alone; this one gives {_described(message)}",
                failing.line,
                fix="assert ..., by(f, g)",
            ) from None
        facts = tuple(self._fact(item, failing.line) for item in given.facts)
        path.learned = _Reasons(facts, given.hole)
        raise _Stopped

    def _raised_at(self, exc: BaseException) -> int | None:
        """The line of the body an exception was raised at, the innermost one."""
        line = None
        trace = exc.__traceback__
        while trace is not None:
            if trace.tb_frame.f_code in self.codes:
                line = trace.tb_lineno
            trace = trace.tb_next
        return line

    def _returned(self, result: Any, path: _Path) -> None:
        """What a body that does not yield returned: ``by(...)``, or a refused form or nothing."""
        code = self.fn.__code__
        line = path.returns.get(code)
        self._close(path)
        name = self.name
        if path.open_loops and result is None:
            raise self._unclosed(path, line)
        if path.open_loops:
            raise ProofError(
                "return",
                f"return by(...) leaves the loop over {name}.conclusion.domain at its first "
                "point; close each case of the loop with yield by(...)",
                line,
                fix=f"yield {_by_text(result)}",
            )
        if result is None:
            raise self._unclosed(path, line, "return")
        if isinstance(result, By):
            facts = tuple(self._fact(item, line) for item in result.facts)
            path.leaf_facts = facts if facts or result.hole else None
            path.leaf_hole = result.hole
            path.leaf_line = line
            path.closings += 1
            return
        raise self._refused_reason(result, line, "return")

    def _yielded(self, value: Any, path: _Path, line: int | None) -> None:
        """What a ``yield`` gives: ``by(...)`` for the point of the innermost loop over a domain."""
        self._close(path)
        name = self.name
        if not path.open_loops:
            where = (
                f"after the loop over {name}.conclusion.domain"
                if path.state == "after"
                else f"outside a loop over {name}.conclusion.domain"
            )
            names = _point_text(self._next_names()) if self.levels else "n"
            raise ProofError(
                "yield",
                f"yield by(...) closes the point the loop over {name}.conclusion.domain is at, "
                f"and this one is {where}; a claim proved without a loop ends with "
                "return by(...)",
                line,
                fix=f"for {names} in {name}.conclusion.domain:"
                if not path.loops and self.levels
                else "return by(...)",
            )
        current = path.open_loops[-1]
        if current.inner:
            raise ProofError(
                "yield",
                f"the point ({', '.join(current.names)}) was closed by the loop over the "
                "conclusion's domain there; a point is closed once",
                line,
            )
        if path.closed is not None:
            raise ProofError(
                "yield",
                f"the point was closed already at line {path.closed}; a point is closed once, "
                "by one yield: split the cases with if and else",
                line,
            )
        depth = len(path.open_loops)
        if self.point_depth is None:
            self.point_depth, self.point_line = depth, line
        elif self.point_depth != depth:
            raise ProofError(
                "yield",
                f"this yield closes the conclusion {depth} for-levels deep, and the one at line "
                f"{self.point_line} {self.point_depth} deep; every case closes the conclusion at "
                "points of one loop",
                line,
            )
        path.closed = line
        path.closings += 1
        path.events.append(("yield", str(line)))
        path.leaf_line = line
        if value is None:
            raise ProofError(
                "close",
                "a bare yield closes the case with nothing said; close it with yield by() if "
                "it follows directly, or give its reasons, yield by(f, g)",
                line,
                fix="yield by()",
            )
        if isinstance(value, By):
            # by() adds nothing: the case is lanky's to close, after the steps it asserted
            facts = tuple(self._fact(item, line) for item in value.facts)
            path.leaf_facts = facts if facts or value.hole else None
            path.leaf_hole = value.hole
            return
        raise self._refused_reason(value, line, "yield")

    def _refused_reason(self, value: Any, line: int | None, word: str) -> ProofError:
        """A ``return`` or ``yield`` of what is no ``by(...)``: 0.5's forms, with the fix."""
        from lanky.surface import Conclusion

        items = value if isinstance(value, tuple | list) else (value,)
        from lanky.theory import Theorem

        if items and all(
            isinstance(item, Given | Citation | Theorem | Conclusion) for item in items
        ):
            texts = ", ".join(reason_text(item) for item in items)
            written = f"{word} {texts}"
            return ProofError(
                "removed",
                f"{written} is how lanky 0.5 gave a case's reasons; the reasons are by(...)",
                line,
                fix=f"{word} by({texts})",
            )
        return ProofError(
            word,
            f"a proof's {word} gives by(...), the reasons for its case; this {word} gives "
            f"{_described(value)}",
            line,
            fix=f"{word} by(...)",
        )

    def _fact(self, item: Any, line: int | None) -> Citation:
        """A fact ``by(...)`` was given, as a citation; anything but a fact is refused."""
        from lanky.surface import ClaimCondition, Conclusion, Conditions
        from lanky.theory import Theorem

        if isinstance(item, Citation):
            return item
        if isinstance(item, Given):
            return Citation(item, None, line)
        if isinstance(item, Conclusion):
            return self.conclusion_fact(item, line)
        if isinstance(item, Theorem):
            if item is self.theorem:
                raise ProofError(
                    "claim",
                    f"{self.name} alone is the whole claim, the one being proved; cite its "
                    f"conclusion at an earlier point, as "
                    f"{self.name}.conclusion[{_earlier_text(self._next_names())}]",
                    line,
                    fix=f"{self.name}.conclusion[{_earlier_text(self._next_names())}]",
                )
            return Citation(item, None, line)
        if isinstance(item, Conditions | ClaimCondition):
            raise ProofError(
                "cite",
                f"{reason_text(item)} is a condition of another claim, which that claim "
                "assumes; cite the claim itself",
                line,
            )
        raise ProofError(
            "return",
            f"by(...) takes facts: a condition, a claim or a conclusion at a point; it is "
            f"given {_described(item)}",
            line,
        )

    # }}}

    # {{{ the claim, once every path is traced

    def define_claim(self, leaves: list[Leaf]) -> tuple[ClaimDef | None, list[Leaf]]:
        """The conclusion's points the proof loops over and cites, and the citations made final.

        A citation of the claim's own conclusion is recorded while the body
        runs with the point it was given. Once every path is traced the
        claim's parameters are known: the variables of each nested ``for``
        the proof loops over down to where its ``yield`` closes the
        conclusion. A point given for fewer levels is completed with
        ``None``, which lanky finds by matching.
        """
        citations = [
            citation
            for leaf in leaves
            for citation in leaf.citations
            if citation.source is self.claim_ref
        ]
        if self.loop_line is None and not citations:
            return None, leaves
        depth = self.point_depth or self.deepest or 1
        looped = self.levels[:depth]
        binders = [binder for level, _guard in looped for binder in level]
        names = [var.name for var, _ in binders]
        shadowing = [name for name in names if name in self.variables or name in self.hypotheses]
        if shadowing:
            raise ProofError(
                "claim",
                f"the conclusion's variable {shadowing[0]} has the name of a parameter of "
                f"{self.name}, so the two cannot be told apart in the proof; rename the "
                "conclusion's",
                self.loop_line or self.claim_line,
            )
        sizes = tuple(len(level) for level, _guard in looped)
        directions = tuple(
            -1 if self.reversed.get(index) else 1
            for index, size in enumerate(sizes)
            for _ in range(size)
        )
        line = self.loop_line or self.claim_line or self.theorem.line
        claim = ClaimDef(
            f"{self.name}.conclusion",
            tuple(names),
            tuple(domain for _var, domain in binders),
            (),
            line,
            sizes,
            directions,
        )
        made: dict[int, Citation] = {}
        for citation in citations:
            values = tuple(citation.values or ())
            if len(values) > len(names):
                outer = claim.written((*values[: len(names)],))
                raise ProofError(
                    "claim",
                    f"{citation.text()} is a point inside {outer}, which this proof closes "
                    f"whole; cite {outer}, where lanky finds the point, or loop over "
                    f"{outer}.domain too",
                    citation.line,
                    fix=outer,
                )
            values = (*values, *(None for _ in range(len(names) - len(values))))
            made[id(citation)] = replace(citation, source=claim, values=values)

        def final(facts: tuple[Citation, ...] | None) -> tuple[Citation, ...] | None:
            if facts is None:
                return None
            return tuple(made.get(id(citation), citation) for citation in facts)

        def step(asserted: Asserted) -> Asserted:
            facts = final(asserted.facts) or ()
            parts = tuple(
                replace(
                    part,
                    links=tuple(replace(link, facts=facts) for link in part.links),
                )
                if isinstance(part, TracedChain)
                else part
                for part in asserted.parts
            )
            return replace(asserted, facts=facts, parts=parts)

        out = []
        for leaf in leaves:
            order = tuple(step(item) if isinstance(item, Asserted) else item for item in leaf.order)
            out.append(replace(leaf, facts=final(leaf.facts), order=order))
        return claim, out

    def flat_goal(self) -> Any:
        """The conclusion with the levels the proof loops over taken as one ``for``."""
        depth = self.point_depth or self.deepest or 0
        return flattened(self.goal, depth)

    # }}}


def flattened(goal: Any, depth: int) -> Any:
    """``goal`` with its first ``depth`` nested ``for`` levels as one: binders, then guards."""
    from lanky.surface import levels

    if depth <= 1:
        return goal
    found = levels(goal)[:depth]
    body = goal
    for _ in found:
        body = body.body
    binders = tuple(binder for level, _guard in found for binder in level)
    guards = [part for _level, guard in found for part in conjuncts(guard)]
    from lanky.terms import LogicalAnd

    guard: Any = None
    if len(guards) == 1:
        guard = guards[0]
    elif guards:
        guard = LogicalAnd(tuple(guards))
    return Forall(binders, body, guard)


def _point_text(names: list[str]) -> str:
    return ", ".join(names) if names else "n"


def _earlier_text(names: list[str]) -> str:
    """``n - 1``, or ``a - 1, b``: the first variable one smaller."""
    first, *rest = names or ["n"]
    return ", ".join([f"{first} - 1", *rest])


def _case_end(
    fn: Any, questions: Sequence[Question], loop_line: int | None
) -> tuple[str, int | None]:
    """How a case with no closing line ends: ``continue``, a bare ``return`` or its last line.

    The case is found by walking the body's source along the path's ``if``
    statements, each to the branch its question was answered with: in the
    loop at ``loop_line``, or in the whole body for a proof with no loop.
    ``("end", None)`` where the source cannot be read.
    """
    try:
        lines, start = inspect.getsourcelines(fn)
        tree = ast.parse(textwrap.dedent("".join(lines)))
    except (OSError, TypeError, SyntaxError):
        return "end", None
    offset = start - 1
    function = next(
        (node for node in tree.body if isinstance(node, ast.FunctionDef | ast.AsyncFunctionDef)),
        None,
    )
    if function is None:
        return "end", None
    statements: list[ast.stmt] = list(function.body)
    if loop_line is not None:
        loop = next(
            (
                node
                for node in ast.walk(function)
                if isinstance(node, ast.For) and node.lineno + offset == loop_line
            ),
            None,
        )
        if loop is None:
            return "end", None
        statements = list(loop.body)
    asked = [(question.line, question.answer) for question in questions]

    def answer_of(node: ast.If) -> bool | None:
        first = node.test.lineno + offset
        last = (node.test.end_lineno or node.test.lineno) + offset
        for line, answer in asked:
            if first <= line <= last:
                return answer
        return None

    def walk(block: list[ast.stmt]) -> tuple[str, int | None] | None:
        last: int | None = None
        for statement in block:
            last = (statement.end_lineno or statement.lineno) + offset
            if isinstance(statement, ast.Continue):
                return "continue", statement.lineno + offset
            if isinstance(statement, ast.Return) and statement.value is None:
                return "return", statement.lineno + offset
            if isinstance(statement, ast.If):
                answer = answer_of(statement)
                if answer is None:
                    continue
                inner = walk(statement.body if answer else statement.orelse)
                if inner is not None and inner[0] != "end":
                    return inner
        return ("end", last) if last is not None else None

    found = walk(statements)
    return found if found is not None else ("end", None)


def _parts(holds: list[tuple[Any, int]], reasons: _Reasons, line: int) -> tuple[Any, ...]:
    """What an ``assert`` states, from what held at each of its questions: chains, and the rest.

    The comparisons of Python's chained comparison share their middle terms,
    the very objects, ``y`` in ``x == y <= z``, so a comparison that starts
    where the one before ended is the next link of its chain, unless it turns
    the chain the other way, ``x <= y >= z``, which starts another.
    """
    from lanky.terms import Comparison

    parts: list[Any] = []
    start: Any = None
    links: list[LinkStep] = []
    previous: Any = None

    def flush() -> None:
        nonlocal start, links
        if links:
            parts.append(TracedChain(start, tuple(links), None, line))
        start, links = None, []

    from lanky.chains import combined_relation

    for prop, at in holds:
        if isinstance(prop, Comparison) and prop.operator in ("==", "<=", "<", ">=", ">"):
            follows = bool(
                links
                and previous is not None
                and (prop.left is previous or render(prop.left) == render(previous))
            )
            if follows:
                try:
                    combined_relation([*(link.relation for link in links), prop.operator])
                except ValueError:
                    # x <= y >= z says x <= y and y >= z: two chains, as Python reads it
                    follows = False
            if not follows:
                flush()
                start = prop.left
            links.append(LinkStep(prop.operator, prop.right, reasons.facts, reasons.hole, at))
            previous = prop.right
            continue
        flush()
        previous = None
        parts.append(prop)
    flush()
    return tuple(parts)


def _earlier(
    names: Sequence[str],
    values: Sequence[Any],
    directions: Sequence[int],
    facts: Sequence[Any] = (),
    types: Mapping[str, Any] | None = None,
) -> str | None:
    """Whether a point comes earlier in the loops than the one they are at (design 3.5).

    ``names`` is the point the loops are at, ``values`` the point cited,
    outermost first, and ``directions`` for each variable ``1`` where its
    loop walks up and ``-1`` where it walks down, ``reversed(...)``. The
    loops fill the conclusion in their order, which is lexicographic in the
    binders, outer domains first, and strict: the first variable where the
    two points differ decides. ``None`` for a point that comes earlier;
    ``later`` for one that comes after; ``same`` for the point the loop is
    at, or a part of the conclusion that holds it. A value that is no
    variable plus a whole number is decided by the path's facts where they
    decide it, and else left to the measure Lean is given (``None``).
    """
    from lanky.terms import Comparison

    for name, value, direction in zip(names, values, directions, strict=False):
        if value is None:
            return None
        change = offset_of(value, name)
        if change is None:
            if types is None:
                return None
            before = "<" if direction > 0 else ">"
            below = decide(Comparison(value, before, Var(name)), facts, types)
            if below is True:
                return None
            same = decide(Comparison(value, "==", Var(name)), facts, types)
            if same is True:
                continue
            after = ">" if direction > 0 else "<"
            above = decide(Comparison(value, after, Var(name)), facts, types)
            return "later" if above is True else None
        if change * direction < 0:
            return None
        if change * direction > 0:
            return "later"
    return "same"


def earlier_point(claim: ClaimDef, values: Sequence[Any]) -> bool:
    """Whether the claim's conclusion at ``values`` comes earlier in its proof's loops."""
    directions = claim.directions or (1,) * len(claim.params)
    return _earlier(claim.params, values, directions) is None and any(
        value is not None and offset_of(value, name) not in (None, 0)
        for name, value in zip(claim.params, values, strict=False)
    )


def _names_in(value: Any) -> frozenset[str]:
    """The names a value mentions; none for a number."""
    from lanky.terms import free_variables

    try:
        return frozenset(free_variables(value)) if hasattr(value, "mapper_method") else frozenset()
    except Exception:  # noqa: BLE001 - a value that cannot be read mentions nothing lanky can name
        return frozenset()


def _earlier_example(loops: Sequence[_Loop]) -> str:
    """``[n - 1]``, or ``[i][a - 1, b]``: the point one before in the innermost loop's order."""
    out = ""
    for index, loop in enumerate(loops):
        names = list(loop.names)
        if index == len(loops) - 1:
            names[0] = f"{names[0]} + 1" if loop.reverse else f"{names[0]} - 1"
        out += f"[{', '.join(names)}]"
    return out


def _by_text(value: Any) -> str:
    """``by(f, g)`` for what a ``return`` gave, as a fix writes it."""
    if isinstance(value, By):
        return repr(value)
    items = value if isinstance(value, tuple | list) else (value,)
    return f"by({', '.join(reason_text(item) for item in items)})"


def _described(value: Any) -> str:
    """A value as a refusal names it: a term rendered, else its kind."""
    if hasattr(value, "mapper_method"):
        return render(value)
    if isinstance(value, str):
        return f"the text {value!r}"
    return f"a {type(value).__name__}"


def _source_line(path: str, line: int | None) -> str:
    """The text of ``path``'s line ``line``, stripped, or the line's number."""
    if line is None:
        return "the step"
    text = linecache.getline(path, line).strip()
    return text or f"line {line}"


def _tree(leaves: list[Leaf]) -> Node:
    """The case tree of the paths' splits, each node with the steps before its split."""
    root = Node()
    filled: set[int] = set()
    for leaf in leaves:
        node = root
        fresh = id(node) not in filled
        for item in leaf.order:
            if isinstance(item, Question) and not item.forced:
                filled.add(id(node))
                if node.question is None:
                    node.question = item
                elif render(node.question.prop) != render(item.prop):
                    raise ProofError(
                        "paths",
                        "the body asks other questions on paths that agree so far; a proof "
                        "has to run the same way on every path up to each split",
                        item.line,
                    )
                if item.answer:
                    node.then = node.then or Node()
                    node = node.then
                else:
                    node.otherwise = node.otherwise or Node()
                    node = node.otherwise
                fresh = id(node) not in filled
            elif fresh:
                node.items.append(item)
        filled.add(id(node))
        node.leaf = leaf
    return root


def _refuse_def_claim(theorem: Any) -> None:
    """Refuse 0.5's ``def claim`` inside the body, with the loop to write instead."""
    from lanky.surface import levels

    found = levels(theorem.goal)
    binders = [var.name for var, _ in found[0][0]] if found else []
    name = getattr(theorem, "qualname", None) or theorem.__name__
    for constant in theorem.fn.__code__.co_consts:
        if not (isinstance(constant, pytypes.CodeType) and constant.co_name == "claim"):
            continue
        params = list(constant.co_varnames[: constant.co_argcount])
        signature = f"def claim({', '.join(params)})"
        if any(param in binders for param in params):
            point = ", ".join(binders)
            raise ProofError(
                "removed",
                f"{signature} is how lanky 0.5 wrote a proof; in 0.6 the proof is a loop over "
                f"the conclusion's points, for {point} in {name}.conclusion.domain:, each case "
                f"closed with yield by(...), and {name}.conclusion[...] is the conclusion at an "
                "earlier point",
                constant.co_firstlineno,
                fix=f"for {point} in {name}.conclusion.domain:",
            )
        first = params[0] if params else "n"
        raise ProofError(
            "removed",
            f"{signature} is how lanky 0.5 wrote an induction on the claim's parameters; in "
            f"0.6 a variable one inducts on belongs in the conclusion's for, -> all(... for "
            f"{first} in ...), and the proof loops over {name}.conclusion.domain",
            constant.co_firstlineno,
            fix=f"for {first} in {name}.conclusion.domain:",
        )


def _refuse_rewritten_asserts(theorem: Any, lines: tuple[int, int]) -> None:
    """Refuse a proof whose ``assert`` steps pytest rewrote into reports of its own.

    pytest rewrites the asserts of the modules it collects as tests, and a
    rewritten assert asks its question in pytest's code and raises with
    pytest's message: the steps are no longer the proof's.
    """
    globals_ = getattr(theorem.fn, "__globals__", {})
    if "@py_builtins" not in globals_ and "@pytest_ar" not in globals_:
        return
    first, last = lines
    asserts = [node for node in _asserts_in(theorem.fn.__code__) if first <= node.lineno <= last]
    if not asserts:
        return
    raise ProofError(
        "assert",
        "pytest rewrote the asserts of this file, and a proof's asserts are its steps; add "
        "PYTEST_DONT_REWRITE to the module's docstring, or keep the theorem in a file pytest "
        "does not collect as a test",
        asserts[0].lineno,
    )


def trace_proof(theorem: Any) -> Proof:
    """Trace a theorem's written proof (see the module).

    Raises:
        ValueError: If the theorem's body holds no proof (:func:`written_lines`).
        ProofError: For a proof lanky refuses before Lean is asked.
    """
    lines = written_lines(theorem.fn)
    if lines is None:
        raise ValueError(f"{theorem.__name__} has no written proof")
    _refuse_def_claim(theorem)
    _refuse_rewritten_asserts(theorem, lines)
    tracer = _Tracer(theorem)
    leaves: list[Leaf] = []
    pending: list[tuple[list[bool], list[tuple[str, str]] | None, list[_Reasons]]] = [
        ([], None, [])
    ]
    runs = 0
    while pending:
        if len(leaves) >= MAX_PATHS:
            raise ProofError(
                "paths",
                f"the proof has more than {MAX_PATHS} cases; split the claim into lemmas",
                None,
            )
        schedule, expected, reasons = pending.pop()
        while True:
            runs += 1
            if runs > MAX_RUNS:
                raise ProofError(
                    "paths",
                    f"the proof takes more than {MAX_RUNS} runs to trace, one per case and one "
                    "more per assert; split the claim into lemmas",
                    None,
                )
            path = tracer.run(schedule, reasons)
            if path.complete:
                break
            assert path.learned is not None
            reasons = [*reasons, path.learned]
        if expected is not None and path.events[: len(expected)] != expected:
            raise ProofError(
                "paths",
                "the body does not run the same way on every path: it cites, asks or asserts "
                "something else before a split than it did before, and a proof has to give the "
                "same steps each time",
                path.leaf.line if path.leaf else None,
            )
        assert path.leaf is not None
        leaves.append(path.leaf)
        for index in reversed(range(len(schedule), len(path.branches))):
            prefix = path.branches[:index] + [False]
            known = path.reasons[: path.branch_asserts[index]]
            pending.append((prefix, path.events[: path.branch_events[index]], list(known)))
    claim, leaves = tracer.define_claim(leaves)
    root = _tree(leaves)
    return Proof(
        theorem=theorem,
        claim=claim,
        root=root,
        leaves=tuple(leaves),
        lines=lines,
        path=theorem.path,
        goal=tracer.flat_goal() if claim is not None else None,
    )
