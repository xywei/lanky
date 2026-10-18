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
  of its name, and a hypothesis a :class:`Given`, a fact the body cites by
  name, ``by(stored)``, or at a point, ``by(pde(i, a - 2, b))``. A name of the
  statement the function does not take as a parameter, one bound outside the
  theorem, is given its symbolic value in the namespace instead
  (:func:`body_arguments`).
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
- ``for n in claim.dom:`` gives one symbolic point, the conclusion's
  variables, with the conclusion's guard known (:class:`_Dom`). A body with
  ``yield`` is a generator, driven here: ``yield by(...)`` closes the point
  the loop is at, and a point that yields nothing is lanky's to finish from
  the steps asserted for it.
- ``claim[p]`` is the claim at an earlier point of the loop, and
  ``claim(...)`` the theorem at smaller values of its parameters: each a
  citation, refused here when it is at a point the loop has not filled in.
  Calling the theorem being proved by its own name is refused, with
  ``claim`` as the fix, and so is every form of lanky 0.5's proofs.

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
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
from typing import Any

from lanky.citations import Citation
from lanky.proofs.cases import decide, negated, offset_of, shape_of
from lanky.surface import By, RemovedForm, claiming, reason_text
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
    """A hypothesis of the theorem, as its proof cites it: a fact with a name.

    Written alone, ``by(stored)``, it is cited at the point lanky finds by
    matching it against the step it supports; called, ``pde(i, a - 2, b)``,
    it is cited at those values of its variables, outermost first. A
    hypothesis written ``p & q`` is cited as both parts.
    """

    def __init__(self, name: str, prop: Any, tracer: _Tracer | None) -> None:
        self.name = name
        self.prop = prop
        self._tracer = tracer

    @property
    def parts(self) -> tuple[Any, ...]:
        """The parts of a hypothesis written as a conjunction; the hypothesis itself otherwise."""
        return conjuncts(self.prop) or (self.prop,)

    def __call__(self, *values: Any, **named: Any) -> Citation:
        """The hypothesis at a point: a citation."""
        assert self._tracer is not None
        return self._tracer.cite(self, values, named, sys._getframe(1))

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
    """The claim a proof cites, ``claim``: the conclusion at a point, the theorem at values.

    Lean has it as a theorem of its own, ``Lanky.<name>.claim``, recursive,
    with the theorem's variables and the conclusion's as its parameters.

    Attributes:
        name: ``claim``.
        params: The parameters a citation of it gives values for: the
            theorem's parameters that some ``claim(...)`` changes, then the
            conclusion's variables.
        domains: The sort each parameter ranges over.
        generalized: The parameters that are the theorem's own.
        line: The line of the loop over ``claim.dom``, or of the first
            citation of the claim.
    """

    name: str
    params: tuple[str, ...]
    domains: tuple[Any, ...]
    generalized: tuple[str, ...]
    line: int

    def written(self, values: tuple[Any, ...], bracket: bool) -> str:
        """A citation of the claim, as written: ``claim[a - 2, b + 2]``, ``claim(n - 1)``."""
        if bracket:
            shown_values = [
                value
                for name, value in zip(self.params, values, strict=True)
                if name not in self.generalized
            ]
            return f"{self.name}[{', '.join(shown(value) for value in shown_values)}]"
        given = [
            value
            for name, value in zip(self.params, values, strict=True)
            if name in self.generalized or not self.generalized
        ]
        return f"{self.name}({', '.join(shown(value) for value in given)})"


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
            gives; ``None`` for a point or a case that gives none, which
            lanky finishes from the steps asserted for it.
        line: The line of that ``yield`` or ``return``.
        order: The questions and the steps (:class:`Asserted`) of the path,
            in the order the body reached them.
        hole: Whether its ``by(...)`` left it open.
        point: Whether it closes a point of ``claim.dom``.
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
        claim: The claim it cites, ``claim[p]`` or ``claim(...)``, or loops
            over, ``claim.dom``; ``None`` for a proof that does neither.
        root: The tree of cases.
        leaves: The paths, in the order they were traced.
        lines: The body's lines, first and last.
        path: The file it is written in.
    """

    theorem: Any
    claim: ClaimDef | None
    root: Node
    leaves: tuple[Leaf, ...]
    lines: tuple[int, int]
    path: str

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
    """What a citation of the claim cites while the body is traced, before the claim is defined."""

    __name__ = "claim"
    name = "claim"


@dataclass(frozen=True)
class _Handle:
    """A variable of the conclusion, ``claim.n``: ``line_taylor.claim.n`` in a message."""

    theorem: str
    name: str

    def __repr__(self) -> str:
        """``line_taylor.claim.n``."""
        return f"{self.theorem}.claim.{self.name}"


class _Dom:
    """``claim.dom`` in a trace: one symbolic point, the guard known (see the module)."""

    def __init__(self, tracer: _Tracer, line: int | None) -> None:
        self.tracer = tracer
        self.line = line
        self.started = False

    def __iter__(self) -> _Dom:
        """A loop over it takes it as its own iterator."""
        return self

    def __next__(self) -> Any:
        """The one point, the first time; then the loop is done."""
        tracer = self.tracer
        path = tracer.path
        assert path is not None
        if not self.started:
            self.started = True
            if path.loops:
                raise ProofError(
                    "claim",
                    "the body loops over claim.dom twice; a proof is one loop over the claim's "
                    "points, each closed with yield by(...)",
                    self.line,
                )
            tracer._close(path)
            path.loops += 1
            path.state = "at"
            if tracer.loop_line is None:
                tracer.loop_line = self.line
            path.facts.extend(tracer.point_facts())
            path.events.append(("point", ""))
            variables = [var for var, _ in tracer.binders]
            return variables[0] if len(variables) == 1 else tuple(variables)
        tracer._close(path)
        path.state = "after"
        raise StopIteration

    def __repr__(self) -> str:
        """``claim.dom``."""
        return f"<claim.dom of {self.tracer.theorem.__name__}>"


class _Traced:
    """What ``claim`` stands for while a body is traced (see :mod:`lanky.surface`)."""

    def __init__(self, tracer: _Tracer) -> None:
        self.tracer = tracer

    def dom(self, frame: Any) -> _Dom:
        """``claim.dom``: the loop's one symbolic point."""
        tracer = self.tracer
        line = tracer._line(frame)
        if not tracer.binders:
            name = tracer.theorem.__name__
            raise ProofError(
                "claim",
                f"claim.dom is the domain of the claim's variables, and {name}'s conclusion "
                "has none; a claim with no variables ends with return by(...)",
                line,
                fix="return by(...)",
            )
        return _Dom(tracer, line)

    def at(self, point: Any, frame: Any) -> Citation:
        """``claim[p]``: the conclusion at an earlier point of the loop."""
        return self.tracer.claim_at(point, frame)

    def call(self, values: tuple, named: Mapping[str, Any], frame: Any) -> Citation:
        """``claim(...)``: the theorem at smaller values of its parameters."""
        return self.tracer.claim_call(values, named, frame)

    def handle(self, name: str) -> _Handle:
        """``claim.n``: a variable of the conclusion, as a handle."""
        names = [var.name for var, _ in self.tracer.binders]
        if name not in names:
            raise AttributeError(
                f"claim has no variable {name}; its variables are {', '.join(names) or 'none'}"
            )
        return _Handle(self.tracer.theorem.__name__, name)

    def __repr__(self) -> str:
        """``<claim of line_taylor: ...>``."""
        return f"<claim of {self.tracer.theorem.__name__}: {render(self.tracer.goal)}>"


class _Tracer:
    """The trace of one theorem's body: its runs, one per path and per assert, and their record."""

    def __init__(self, theorem: Any) -> None:
        self.theorem = theorem
        self.fn = theorem.fn
        self.codes = _own_codes(self.fn.__code__)
        self.namespace = namespace(theorem)
        self.variables: dict[str, Any] = dict(theorem.variables)
        self.hypotheses: dict[str, Any] = dict(theorem.hypotheses)
        self.goal = theorem.goal
        self.binders: list[tuple[Var, Any]] = (
            list(self.goal.binders) if isinstance(self.goal, Forall) else []
        )
        self.path: _Path | None = None
        self.claim_ref = _ClaimRef()
        self.loop_line: int | None = None
        self.claim_line: int | None = None
        self.view = _Traced(self)

    # {{{ what the body sees

    def types(self) -> dict[str, Any]:
        """The sort of every name the proof's terms mention: the theorem's and the conclusion's."""
        types = dict(self.variables)
        for var, domain in self.binders:
            types.setdefault(var.name, domain)
        return types

    def _base_facts(self) -> list[Any]:
        """What holds on every path before any split: the theorem's hypotheses."""
        return [part for _name, prop in self.hypotheses.items() for part in conjuncts(prop)]

    def point_facts(self) -> list[Any]:
        """What holds at a point of ``claim.dom``: the conclusion's guard."""
        goal = self.goal
        return list(conjuncts(goal.guard)) if isinstance(goal, Forall) else []

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
                    "this step comes after the loop over claim.dom, and belongs to no point; "
                    "move it into the loop",
                    node.lineno if node is not None else frame.f_lineno,
                )
            if path.closed is not None:
                raise ProofError(
                    "assert",
                    f"the point was closed at line {path.closed} by its yield; a step after "
                    "it is for nothing: assert it before the yield",
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
        """A citation of ``source`` at ``values``, written at the body's line ``frame`` runs."""
        line = self._line(frame)
        names = self._binder_names(source)
        called = Citation(source).name
        if named:
            unknown = [name for name in named if name not in names]
            if unknown:
                raise ProofError(
                    "cite",
                    f"{called} has no variable {unknown[0]}: its variables "
                    f"are {', '.join(names) or 'none'}",
                    line,
                )
            if len(values) > len(names):
                raise ProofError(
                    "cite",
                    _takes(called, names, len(values) + len(named)),
                    line,
                    fix=f"{called}({', '.join(names)})" if names else None,
                )
            given = dict(zip(names, values, strict=False))
            twice = [name for name in named if name in given]
            if twice:
                # each value is written once, as Python itself asks of a call
                raise ProofError(
                    "cite",
                    f"{called} is given {twice[0]} twice, by its place and by its name",
                    line,
                )
            given.update(named)
            if len(given) != len(names):
                missing = [name for name in names if name not in given]
                raise ProofError("cite", f"{called} needs a value for {', '.join(missing)}", line)
            values = tuple(given[name] for name in names)
        elif len(values) != len(names):
            raise ProofError(
                "cite",
                _takes(called, names, len(values)),
                line,
                fix=f"{called}({', '.join(names)})" if names else None,
            )
        citation = Citation(source, tuple(family_value(value) for value in values), line)
        if self.path is not None:
            self.path.events.append(("cite", citation.text()))
        return citation

    def cite_theorem(
        self, theorem: Any, values: tuple, named: Mapping[str, Any], frame: Any
    ) -> Citation:
        """A theorem called inside the trace: a citation, or the self-reference refused."""
        line = self._line(frame)
        if theorem is self.theorem:
            raise self._self_reference(line, values, named)
        return self.cite(theorem, values, named, frame)

    def _self_reference(
        self, line: int | None, values: tuple = (), named: Mapping[str, Any] | None = None
    ) -> ProofError:
        """The refusal of a theorem that cites itself by name, with ``claim`` as the fix."""
        name = self.theorem.__name__
        where = f"{os.path.basename(self.theorem.path)}:{line}" if line else "its body"
        given = [shown(value) for value in values]
        given += [f"{key}={shown(value)}" for key, value in (named or {}).items()]
        binders = [var.name for var, _ in self.binders]
        inside = self.path is not None and self.path.state == "at"
        if given and len(values) == len(binders) and (inside or len(values) != len(self.variables)):
            fix = f"claim[{', '.join(given)}]"
            what = "the claim at an earlier point of the loop over claim.dom"
        else:
            parameters = list(self.variables)
            fix = f"claim({', '.join(given) or ', '.join(parameters)})"
            what = "the theorem at smaller values"
        return ProofError(
            "self-reference",
            f"{name} cites itself by name at {where}; in its own proof the theorem is "
            f"claim, and {what} is {fix}",
            line,
            fix=fix,
        )

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

    # {{{ the claim

    def _current_point(self) -> str:
        """The point the loop is at, as a message says it: ``n``, ``(i, a, b)``."""
        names = [var.name for var, _ in self.binders]
        return names[0] if len(names) == 1 else f"({', '.join(names)})"

    def claim_at(self, point: Any, frame: Any) -> Citation:
        """``claim[p]``, checked to be at a point the loop has filled in (see the module)."""
        path = self.path
        assert path is not None
        line = self._line(frame)
        name = self.theorem.__name__
        if not self.binders:
            raise ProofError(
                "claim",
                f"claim[...] is the claim at a point of its domain, and {name}'s conclusion "
                "has no variables; cite the theorem at smaller values as claim(...)",
                line,
            )
        values = point if isinstance(point, tuple) else (point,)
        names = [var.name for var, _ in self.binders]
        if len(values) != len(names):
            raise ProofError(
                "cite",
                f"claim[...] takes a value for each of the claim's variables, "
                f"{', '.join(names)}, and is given {len(values)}",
                line,
                fix=f"claim[{', '.join(names)}]",
            )
        written = f"claim[{', '.join(shown(value) for value in values)}]"
        if path.state != "at":
            raise ProofError(
                "claim",
                f"{written} is the claim at an earlier point of the loop over claim.dom, and "
                "it is cited outside that loop; cite it inside for "
                f"{', '.join(names)} in claim.dom:",
                line,
            )
        later = _not_earlier(names, values)
        if later == "later":
            raise ProofError(
                "later",
                f"{written} is not filled in yet when the loop is at {self._current_point()}",
                line,
                fix="cite the claim at a point the loop has filled in, as "
                + _earlier_example(names),
            )
        if later == "same":
            raise ProofError(
                "later",
                f"{written} is the point the loop is at, {self._current_point()}, which this "
                "step is filling in",
                line,
                fix="cite the claim at a point the loop has filled in, as "
                + _earlier_example(names),
            )
        if self.claim_line is None:
            self.claim_line = line
        citation = Citation(self.claim_ref, values, line, bracket=True)
        path.events.append(("cite", written))
        return citation

    def claim_call(self, values: tuple, named: Mapping[str, Any], frame: Any) -> Citation:
        """``claim(...)``, the theorem at other values of its parameters, checked to be smaller."""
        path = self.path
        assert path is not None
        line = self._line(frame)
        names = list(self.variables)
        if len(values) > len(names):
            raise ProofError(
                "cite",
                f"claim(...) takes the theorem's parameters, {', '.join(names) or 'none'}, and "
                f"is given {len(values)} values",
                line,
            )
        given = dict(zip(names, values, strict=False))
        for key, value in named.items():
            if key not in names:
                raise ProofError(
                    "cite",
                    f"claim(...) takes the theorem's parameters, and {key} is none of them: "
                    f"they are {', '.join(names) or 'none'}",
                    line,
                )
            if key in given:
                raise ProofError(
                    "cite", f"claim(...) is given {key} twice, by its place and by its name", line
                )
            given[key] = value
        full = tuple(family_value(given[name]) if name in given else Var(name) for name in names)
        given_text = [shown(value) for value in values]
        given_text += [f"{key}={shown(value)}" for key, value in named.items()]
        written = f"claim({', '.join(given_text)})"
        changed = [
            name
            for name, value in zip(names, full, strict=True)
            if not (isinstance(value, Var) and value.name == name)
        ]
        changes = [offset_of(full[names.index(name)], name) for name in changed]
        from lanky.proofs.cases import integer_sort

        if changed and not any(integer_sort(self.variables[name]) for name in changed):
            first = changed[0]
            value = full[names.index(first)]
            mentioned = [
                name
                for name in names
                if name != first
                and integer_sort(self.variables[name])
                and name in _names_in(value)
            ]
            fix = f"claim({mentioned[0]}={shown(value)})" if len(mentioned) == 1 else None
            raise ProofError(
                "claim",
                f"{written} gives {first} the value {shown(value)}: claim(...) takes the "
                f"theorem's parameters in order, {', '.join(names)}, as calling the theorem "
                "does, and the theorem at smaller values has one of its integer parameters "
                "smaller",
                line,
                fix=fix,
            )
        if not changes:
            raise ProofError(
                "later",
                f"{written} is the theorem at the values the proof is at, which is what it is "
                "proving",
                line,
                fix=f"cite it at smaller values, as {_smaller_example(names, self.variables)}",
            )
        if all(change is not None for change in changes) and not any(
            change < 0 for change in changes
        ):
            raise ProofError(
                "later",
                f"{written} is at larger values than the proof's {', '.join(changed)}: the "
                "theorem is cited at smaller values",
                line,
                fix=f"cite it at smaller values, as {_smaller_example(names, self.variables)}",
            )
        if self.claim_line is None:
            self.claim_line = line
        citation = Citation(self.claim_ref, full, line, bracket=False)
        path.events.append(("cite", written))
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
            with running(self), asking_proof_questions(self), claiming(self.view):
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
                if stop.value is not None:
                    raise ProofError(
                        "return",
                        "a proof that closes its points with yield ends with no return value; "
                        "each point's reason is its yield by(...)",
                        path.returns.get(self.fn.__code__),
                    ) from None
                return
            frame = generator.gi_frame
            self._yielded(value, path, frame.f_lineno if frame is not None else None)

    def _call(self, thunk: Any, path: _Path) -> Any:
        """Run part of the body, turning what it raises into a refusal at its line."""
        try:
            return thunk()
        except (ProofError, _Stopped, StopIteration):
            raise
        except AssertionError as exc:
            self._assertion(exc, path)
            raise AssertionError("unreachable") from None  # pragma: no cover
        except RemovedForm as exc:
            raise ProofError("removed", exc.message, self._raised_at(exc), exc.fix) from None
        except SymbolicBoolError as exc:
            raise ProofError("question", str(exc), self._raised_at(exc)) from None
        except RecursionError:
            raise ProofError(
                "raised",
                "the proof calls itself without end; the claim at an earlier point is "
                "claim[...], and the theorem at smaller values claim(...)",
                None,
            ) from None
        except NameError as exc:
            missing = getattr(exc, "name", None)
            if missing in ("by", "claim"):
                raise ProofError(
                    "raised",
                    f"{missing} is one of the words of a proof, and the file does not import it",
                    self._raised_at(exc),
                    fix="from lanky import by, claim",
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
        """What a body that does not yield returned: ``by(...)``, nothing, or a refused form."""
        code = self.fn.__code__
        line = path.returns.get(code)
        self._close(path)
        if result is None:
            if path.leaf_line is None:
                path.leaf_line = line
            return
        if path.loops:
            raise ProofError(
                "return",
                "return by(...) leaves the loop over claim.dom at its first point; close each "
                "point with yield by(...)",
                line,
                fix=f"yield {_by_text(result)}",
            )
        if isinstance(result, By):
            path.leaf_facts = tuple(self._fact(item, line) for item in result.facts)
            path.leaf_hole = result.hole
            path.leaf_line = line
            return
        raise self._refused_reason(result, line, "return")

    def _yielded(self, value: Any, path: _Path, line: int | None) -> None:
        """What a ``yield`` gives: ``by(...)`` for the point the loop is at, or nothing."""
        self._close(path)
        if path.state != "at":
            where = (
                "after the loop over claim.dom"
                if path.state == "after"
                else "outside a loop over claim.dom"
            )
            raise ProofError(
                "yield",
                f"yield by(...) closes the point the loop over claim.dom is at, and this one "
                f"is {where}; a claim with no variables ends with return by(...)",
                line,
                fix="for n in claim.dom: ... yield by(...)" if not path.loops else None,
            )
        if path.closed is not None:
            raise ProofError(
                "yield",
                f"the point was closed already at line {path.closed}; a point is closed once, "
                "by one yield: split the cases with if and else",
                line,
            )
        path.closed = line
        path.events.append(("yield", str(line)))
        path.leaf_line = line
        if value is None:
            return
        if isinstance(value, By):
            path.leaf_facts = tuple(self._fact(item, line) for item in value.facts)
            path.leaf_hole = value.hole
            return
        raise self._refused_reason(value, line, "yield")

    def _refused_reason(self, value: Any, line: int | None, word: str) -> ProofError:
        """A ``return`` or ``yield`` of what is no ``by(...)``: 0.5's forms, with the fix."""
        from lanky.surface import _Claim

        if isinstance(value, _Claim):
            return ProofError(
                "removed",
                "return claim is how lanky 0.5 ended a proof; in 0.6 the proof loops over the "
                "claim's points and closes each with yield by(...)",
                line,
                fix=f"for {', '.join(var.name for var, _ in self.binders) or 'n'} in claim.dom:",
            )
        items = value if isinstance(value, tuple | list) else (value,)
        from lanky.theory import Theorem

        if items and all(isinstance(item, Given | Citation | Theorem) for item in items):
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
            f"a proof's {word} gives by(...), the reasons for its claim, or nothing; this "
            f"{word} gives {_described(value)}",
            line,
            fix=f"{word} by(...)",
        )

    def _fact(self, item: Any, line: int | None) -> Citation:
        """A fact ``by(...)`` was given, as a citation; anything but a fact is refused."""
        from lanky.surface import _Claim
        from lanky.theory import Theorem

        if isinstance(item, Citation):
            return item
        if isinstance(item, Given):
            return Citation(item, None, line)
        if isinstance(item, Theorem):
            if item is self.theorem:
                raise self._self_reference(line)
            return Citation(item, None, line)
        if isinstance(item, _Claim):
            raise ProofError(
                "claim",
                "claim alone is the whole theorem, the one being proved; cite it at an earlier "
                "point, as claim[n - 1], or at smaller values, as claim(n - 1)",
                line,
            )
        raise ProofError(
            "return",
            f"by(...) takes facts: a hypothesis, a theorem or the claim at a point; it is "
            f"given {_described(item)}",
            line,
        )

    # }}}

    # {{{ the claim, once every path is traced

    def define_claim(self, leaves: list[Leaf]) -> tuple[ClaimDef | None, list[Leaf]]:
        """The claim the proof cites or loops over, and the leaves with its citations made final.

        A citation of the claim is recorded while the body runs with what it
        was given: a point of the conclusion, ``claim[p]``, or values of the
        theorem's parameters, ``claim(...)``. Once every path is traced the
        claim's parameters are known: the theorem's parameters some
        ``claim(...)`` changes, then the conclusion's variables. Each
        citation then gives a value for every parameter: its own, the
        parameter itself for one it leaves as it is, and ``None`` for a
        variable of the conclusion a ``claim(...)`` leaves for lanky to find.
        """
        citations = [
            citation
            for leaf in leaves
            for citation in leaf.citations
            if citation.source is self.claim_ref
        ]
        if self.loop_line is None and not citations:
            return None, leaves
        names = list(self.variables)
        calls = [citation for citation in citations if not citation.bracket]
        generalized = [
            name
            for index, name in enumerate(names)
            if any(
                not (isinstance(call.values[index], Var) and call.values[index].name == name)
                for call in calls
            )
        ]
        binders = [var.name for var, _ in self.binders]
        shadowing = [name for name in binders if name in self.variables or name in self.hypotheses]
        if shadowing:
            raise ProofError(
                "claim",
                f"the claim's variable {shadowing[0]} has the name of a parameter of "
                f"{self.theorem.__name__}, so the two cannot be told apart in the proof; "
                "rename the claim's",
                self.loop_line or self.claim_line,
            )
        params = (*generalized, *binders)
        domains = (
            *(self.variables[name] for name in generalized),
            *(domain for _var, domain in self.binders),
        )
        line = self.loop_line or self.claim_line or self.theorem.line
        claim = ClaimDef("claim", params, domains, tuple(generalized), line)
        made: dict[int, Citation] = {}
        for citation in citations:
            if citation.bracket:
                values = (*(Var(name) for name in generalized), *citation.values)
            else:
                given = dict(zip(names, citation.values, strict=True))
                values = (*(given[name] for name in generalized), *(None for _ in binders))
            made[id(citation)] = replace(citation, source=claim, values=tuple(values))

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

    # }}}


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


def _not_earlier(names: list[str], values: tuple[Any, ...]) -> str | None:
    """``later`` or ``same`` for a point the loop has not filled in; else ``None``.

    The loop fills the claim in order, so a point is filled in before the one
    the loop is at when one of its variables is smaller there: ``claim[n -
    1]``, ``claim[i, a - 2, b + 2]``. One with none smaller and one larger,
    ``claim[n + 1]``, is not filled in yet, and the point itself is the one
    being filled. A point that is smaller in one variable and larger in
    another, ``claim[a + 1, n - 1]``, is left to the measure Lean is given
    (:func:`lanky.proofs.compile.measure`), as is a value that is no
    variable plus a whole number.
    """
    changes = [offset_of(value, name) for name, value in zip(names, values, strict=True)]
    if any(change is None for change in changes):
        return None
    if all(change == 0 for change in changes):
        return "same"
    if all(change >= 0 for change in changes):
        return "later"
    return None


def _names_in(value: Any) -> frozenset[str]:
    """The names a value mentions; none for a number."""
    from lanky.terms import free_variables

    try:
        return frozenset(free_variables(value)) if hasattr(value, "mapper_method") else frozenset()
    except Exception:  # noqa: BLE001 - a value that cannot be read mentions nothing lanky can name
        return frozenset()


def _earlier_example(names: list[str]) -> str:
    """``claim[n - 1]``, or ``claim[a - 1, b]``: a point the loop has filled in."""
    first, *rest = names
    return f"claim[{', '.join([f'{first} - 1', *rest])}]"


def _smaller_example(names: list[str], variables: Mapping[str, Any]) -> str:
    """``claim(n - 1)``: the theorem at smaller values of its first integer parameter."""
    from lanky.proofs.cases import integer_sort

    integer = [name for name in names if integer_sort(variables[name])]
    if not integer:
        return "claim(...)"
    first = integer[0]
    shown_values = [f"{name} - 1" if name == first else name for name in names]
    while shown_values and shown_values[-1] in names and shown_values[-1] != first:
        shown_values.pop()
    return f"claim({', '.join(shown_values)})"


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
    goal = theorem.goal
    binders = [var.name for var, _ in goal.binders] if isinstance(goal, Forall) else []
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
                f"the claim's points, for {point} in claim.dom:, each closed with "
                "yield by(...), and claim[...] is the claim at an earlier point",
                constant.co_firstlineno,
                fix=f"for {point} in claim.dom:",
            )
        raise ProofError(
            "removed",
            f"{signature} is how lanky 0.5 wrote an induction on the theorem's parameters; "
            "in 0.6 the body itself is the proof, and claim(...) is the theorem at smaller "
            "values",
            constant.co_firstlineno,
            fix=f"the body itself, citing claim({', '.join(p + ' - 1' for p in params[:1])})",
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
    )
