"""Tracing a written proof: the body run on symbolic values, once per path.

The design idea. A theorem's body is ordinary Python, and running it on the
symbolic terms its annotations were read with records the proof: which facts
each ``return`` gives, at which points, and under which case. Nothing is read
from the body's syntax but whether there is a proof at all
(:func:`written_lines`). The body runs only under ``lanky check``, after
every native run and every draw of the check, never when the file is imported
or run, in a namespace built at check time (:func:`namespace`): the module's
live globals, the snapshot's copies of what the annotations read laid over
them, and lanky's ``all``, ``any``, ``sum`` and ``abs``.

While a body is traced:

- Its parameters are symbolic values: a variable is the :class:`~lanky.terms.Var`
  of its name, and a hypothesis a :class:`Given`, a fact the body cites by
  name, ``stored``, or at a point, ``pde(i, a - 2, b)``.
- An ``if`` in the body's own code is a case split. The truth value of its
  proposition is scheduled (:meth:`_Tracer.ask`): the body runs once per path,
  each branch with its condition as a fact, and a proposition asked twice on
  one path gets the same answer. A condition the path's facts already decide
  (a condition on the bounds of naturals, say) is answered so, and makes no
  split. Asked anywhere else, by pymbolic, by ``in``, by a sort, the
  question raises as it does outside a trace, so that no silent case split
  is made.
- ``def claim(a, b)``, returned, is the claim at a point: lanky calls it with
  the claim's variables, and a call of ``claim`` inside it is a citation of
  the claim at smaller values, recorded by a stub put in the closure cell
  that holds ``claim`` (:meth:`_Tracer._start_claim`), so that tracing never
  recurses.
- Calling a hypothesis, a theorem or the claim with symbolic values is a
  citation. Calling the theorem being proved is refused, with ``def claim``
  as the fix.

The result is a :class:`Proof`: the claim's definition, if there is one, and a
tree of cases whose leaves are the facts each ``return`` gives. What it means
in Lean is :mod:`lanky.proofs.compile`'s business.
"""

from __future__ import annotations

import ast
import dis
import functools
import inspect
import os
import sys
import textwrap
import types as pytypes
from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any

from lanky.proofs.match import decide, negated, shape_of
from lanky.terms import (
    BUILTIN_OVERRIDES,
    Forall,
    SymbolicBoolError,
    Var,
    asking_proof_questions,
    code_reads,
    conjuncts,
    render,
)

__all__ = [
    "MAX_PATHS",
    "MAX_QUESTIONS",
    "Citation",
    "ClaimDef",
    "Given",
    "Leaf",
    "Node",
    "Proof",
    "ProofError",
    "Question",
    "active",
    "namespace",
    "trace_proof",
    "written_lines",
]

#: How many paths a body may take, its cases, before it is refused.
MAX_PATHS = 64

#: How many truth values one run of a body may ask for, a guard against a
#: ``while`` over a symbolic condition, which asks the same question for ever.
MAX_QUESTIONS = 256


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
        kind: What went wrong, one word: ``self-reference``, ``no-point``,
            ``measure``, ``negative``, ``claim``, ``return``, ``question``,
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

    Written alone, ``return stored``, it is cited at the point lanky finds by
    matching it against the case's claim; called, ``pde(i, a - 2, b)``, it is
    cited at those values of its variables, outermost first. A hypothesis
    written ``p & q`` is cited as both parts.
    """

    def __init__(self, name: str, prop: Any, tracer: _Tracer) -> None:
        self.name = name
        self.prop = prop
        self._tracer = tracer

    @property
    def parts(self) -> tuple[Any, ...]:
        """The parts of a hypothesis written as a conjunction; the hypothesis itself otherwise."""
        return conjuncts(self.prop) or (self.prop,)

    def __call__(self, *values: Any, **named: Any) -> Citation:
        """The hypothesis at a point: a citation."""
        return self._tracer.cite(self, values, named, sys._getframe(1))

    def __bool__(self) -> bool:
        """Refused: a fact has no truth value to ask for."""
        raise SymbolicBoolError(
            f"{self.name} is a fact, and a fact has no truth value to ask for; cite it "
            f"in a return, as return {self.name}"
        )

    def __repr__(self) -> str:
        """The hypothesis's name."""
        return self.name


@dataclass(frozen=True, eq=False)
class ClaimDef:
    """The local function that is the claim at a point, ``def claim(a, b)``.

    Attributes:
        name: Its Python name, ``claim`` by convention.
        params: Its parameters, the claim's variables by name and in order,
            and any parameter of the theorem it generalizes.
        domains: The sort each parameter ranges over: a variable of the
            goal's, or the theorem's sort of a parameter it generalizes.
        generalized: The parameters that name parameters of the theorem.
        line: The line of its ``def``.
    """

    name: str
    params: tuple[str, ...]
    domains: tuple[Any, ...]
    generalized: tuple[str, ...]
    line: int


@dataclass(frozen=True, eq=False)
class Citation:
    """A fact the proof cites: a hypothesis, a theorem, or the claim, maybe at a point.

    Attributes:
        source: A :class:`Given`, a :class:`~lanky.theory.Theorem`, or the
            :class:`ClaimDef` for the claim at smaller values.
        values: The point, a value per variable of the fact, outermost first;
            ``None`` for a fact cited by its name alone.
        line: The line of the body it was written on.
    """

    source: Any
    values: tuple[Any, ...] | None
    line: int | None

    @property
    def name(self) -> str:
        """The name the fact is cited by."""
        return _source_name(self.source)

    @property
    def is_claim(self) -> bool:
        """Whether this is the claim at a point, which is the induction."""
        return isinstance(self.source, ClaimDef)

    def text(self, values: tuple[Any, ...] | None = None) -> str:
        """How the citation is written: ``pde(i, a - 2, b)``, or ``stored`` alone."""
        values = self.values if values is None else values
        if values is None:
            return self.name
        return f"{self.name}({', '.join(shown(value) for value in values)})"


def _source_name(source: Any) -> str:
    """The name a fact is cited by."""
    if isinstance(source, Given | ClaimDef):
        return source.name
    return getattr(source, "__name__", None) or getattr(source, "qualname", None) or repr(source)


def shown(value: Any) -> str:
    """A value as lanky writes it in a citation or a report."""
    return render(value) if hasattr(value, "mapper_method") else repr(value)


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
class Leaf:
    """One path of a proof, ending at a ``return``.

    Attributes:
        questions: The case splits on the way, in order, each with its answer.
        facts: The facts the ``return`` gives, ``None`` for a bare ``return``,
            which leaves the case to lanky.
        line: The line of the ``return``.
    """

    questions: tuple[Question, ...]
    facts: tuple[Citation, ...] | None
    line: int | None

    @property
    def conditions(self) -> list[tuple[Any, int]]:
        """What holds in this case, each with the line of its ``if``."""
        return [(question.condition, question.line) for question in self.questions]


@dataclass(eq=False)
class Node:
    """A node of the case tree: a split and its two branches, or a leaf."""

    question: Question | None = None
    then: Node | None = None
    otherwise: Node | None = None
    leaf: Leaf | None = None


@dataclass(eq=False)
class Proof:
    """A written proof, traced: what Lean is asked to check, and where each part was written.

    Attributes:
        theorem: The :class:`~lanky.theory.Theorem` it proves.
        claim: The ``claim`` function, when the body defines one.
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
        """Every citation of the claim at a point, in the order they were traced."""
        return [
            citation for leaf in self.leaves for citation in (leaf.facts or ()) if citation.is_claim
        ]

    @property
    def cited(self) -> list[Any]:
        """The theorems the proof cites, each once, in order."""
        out: list[Any] = []
        for leaf in self.leaves:
            for citation in leaf.facts or ():
                source = citation.source
                if not isinstance(source, Given | ClaimDef) and all(
                    source is not seen for seen in out
                ):
                    out.append(source)
        return out

    @property
    def where(self) -> str:
        """``file.py:41-48``: where the proof is written."""
        first, last = self.lines
        span = f"{first}-{last}" if last != first else f"{first}"
        return f"{os.path.basename(self.path)}:{span}"


# }}}


# {{{ the trace


#: The trace in progress, which a theorem called inside it cites rather than evaluates.
_ACTIVE: ContextVar[_Tracer | None] = ContextVar("lanky_proof_trace", default=None)


def active() -> _Tracer | None:
    """The trace of a written proof in progress, or ``None`` outside one.

    :meth:`lanky.theory.Theorem.__call__` asks: inside a trace, calling a
    theorem is citing it, whatever its arguments are, and outside one it
    evaluates the claim at concrete values, as it always has.
    """
    return _ACTIVE.get()


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


def _own_codes(code: Any) -> frozenset[Any]:
    """``code`` and every code object compiled inside it: the body, ``claim``, helpers."""
    found = {code}
    stack = [code]
    while stack:
        current = stack.pop()
        for constant in current.co_consts:
            if isinstance(constant, pytypes.CodeType) and constant not in found:
                found.add(constant)
                stack.append(constant)
    return frozenset(found)


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


class _ClaimStub:
    """What ``claim`` is inside itself while it is traced: a recorder of citations."""

    def __init__(self, tracer: _Tracer) -> None:
        self._tracer = tracer

    def __call__(self, *values: Any, **named: Any) -> Citation:
        """The claim at these values: a citation, which is the induction."""
        assert self._tracer.claim is not None
        return self._tracer.cite(self._tracer.claim, values, named, sys._getframe(1))

    def __bool__(self) -> bool:
        """Refused: the claim is a fact, cited at a point."""
        raise SymbolicBoolError("the claim is a fact, cited at a point, as claim(a - 2, b)")

    def __repr__(self) -> str:
        """The claim function's name."""
        return self._tracer.claim.name if self._tracer.claim else "claim"


@dataclass(eq=False)
class _Path:
    """One run of the body: the answers it was given, and what it asked and cited."""

    schedule: list[bool]
    facts: list[Any] = field(default_factory=list)
    memo: dict[str, bool] = field(default_factory=dict)
    questions: list[Question] = field(default_factory=list)
    branches: list[bool] = field(default_factory=list)
    branch_events: list[int] = field(default_factory=list)
    events: list[tuple[str, str]] = field(default_factory=list)
    returns: dict[Any, int] = field(default_factory=dict)
    asked: int = 0
    leaf: Leaf | None = None


class _Tracer:
    """The trace of one theorem's body: its runs, one per path, and what they recorded."""

    def __init__(self, theorem: Any) -> None:
        self.theorem = theorem
        self.fn = theorem.fn
        self.codes = _own_codes(self.fn.__code__)
        self.namespace = namespace(theorem)
        self.variables: dict[str, Any] = dict(theorem.variables)
        self.hypotheses: dict[str, Any] = dict(theorem.hypotheses)
        self.goal = theorem.goal
        self.claim: ClaimDef | None = None
        self.claim_code: Any = None
        self.path: _Path | None = None

    # {{{ what the body sees

    def types(self) -> dict[str, Any]:
        """The sort of every name the proof's terms mention: the theorem's and the claim's."""
        types = dict(self.variables)
        if self.claim is not None:
            types.update(zip(self.claim.params, self.claim.domains, strict=True))
        return types

    def _base_facts(self) -> list[Any]:
        """What holds on every path before any split: the theorem's hypotheses."""
        return [part for _name, prop in self.hypotheses.items() for part in conjuncts(prop)]

    def _claim_facts(self) -> list[Any]:
        """What holds inside ``claim``: the goal's guard at the claim's variables."""
        goal = self.goal
        return list(conjuncts(goal.guard)) if isinstance(goal, Forall) else []

    def ask(self, prop: Any, frame: Any) -> bool:
        """The truth value of a case split the body's own ``if`` asks for (see the module).

        Raises:
            SymbolicBoolError: If the question does not come from an ``if``
                in the body's own code.
            ProofError: If one run asks more than :data:`MAX_QUESTIONS`.
        """
        if frame is None or frame.f_code not in self.codes:
            raise SymbolicBoolError(
                f"the truth value of {render(prop)} was asked for outside the proof's own "
                "code, by a function it calls, by an `in` test or by sorting: in a proof only "
                "an if of the proof's own is a case split"
            )
        if not _branches_on(frame):
            raise SymbolicBoolError(
                f"the truth value of {render(prop)} was asked for by the proof, but not by "
                "an if: and, or and not used as values, and a comparison of tuples, would "
                "keep one side of the question; split the case with if"
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
        key = render(prop)
        if key in path.memo:
            return path.memo[key]
        decided = decide(prop, path.facts, self.types())
        if decided is None:
            index = len(path.branches)
            answer = path.schedule[index] if index < len(path.schedule) else True
            path.branches.append(answer)
            forced = False
        else:
            answer, forced = decided, True
        path.memo[key] = answer
        question = Question(prop, frame.f_lineno, answer, forced)
        path.questions.append(question)
        path.facts.append(question.condition)
        path.events.append(("ask", key))
        if not forced:
            path.branch_events.append(len(path.events))
        return answer

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
        if named:
            unknown = [name for name in named if name not in names]
            if unknown:
                raise ProofError(
                    "cite",
                    f"{_source_name(source)} has no variable {unknown[0]}: its variables "
                    f"are {', '.join(names) or 'none'}",
                    line,
                )
            given = dict(zip(names, values, strict=False))
            given.update(named)
            if len(given) != len(names):
                missing = [name for name in names if name not in given]
                raise ProofError(
                    "cite",
                    f"{_source_name(source)} needs a value for {', '.join(missing)}",
                    line,
                )
            values = tuple(given[name] for name in names)
        elif len(values) != len(names):
            raise ProofError(
                "cite",
                f"{_source_name(source)} takes {len(names)} values, its variables "
                f"{', '.join(names) or 'none'}, and is given {len(values)}",
                line,
                fix=f"{_source_name(source)}({', '.join(names)})" if names else None,
            )
        citation = Citation(source, tuple(values), line)
        if self.path is not None:
            self.path.events.append(("cite", citation.text()))
        return citation

    def cite_theorem(
        self, theorem: Any, values: tuple, named: Mapping[str, Any], frame: Any
    ) -> Citation:
        """A theorem called inside the trace: a citation, or the self-reference refused."""
        line = self._line(frame)
        if theorem is self.theorem:
            raise self._self_reference(line, values)
        return self.cite(theorem, values, named, frame)

    def _self_reference(self, line: int | None, values: tuple = ()) -> ProofError:
        """The refusal of a theorem that calls itself by name, with ``claim`` as the fix."""
        name = self.theorem.__name__
        goal = self.goal
        variables = [var.name for var, _ in goal.binders] if isinstance(goal, Forall) else []
        where = f"{os.path.basename(self.theorem.path)}:{line}" if line else "its body"
        at = ", ".join(shown(value) for value in values) if values else ", ".join(variables)
        return ProofError(
            "self-reference",
            f"{name} calls itself at {where}. To argue from smaller values, write def "
            f"claim({', '.join(variables)}) and call claim({at})",
            line,
            fix=f"def claim({', '.join(variables)}), and claim({at})",
        )

    def _binder_names(self, source: Any) -> list[str]:
        """The variables a fact takes values for, outermost first."""
        if isinstance(source, ClaimDef):
            return list(source.params)
        if isinstance(source, Given):
            parts = [shape_of(part) for part in source.parts]
            with_binders = [part for part in parts if part.binders]
            if not with_binders:
                return []
            first = [var.name for var, _ in with_binders[0].binders]
            return first
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

    # {{{ a run

    @contextmanager
    def _tracing(self, path: _Path) -> Iterator[None]:
        """Run with this tracer answering the body's questions and recording its returns."""
        self.path = path
        token = _ACTIVE.set(self)
        previous = sys.getprofile()

        def profile(frame: Any, event: str, arg: Any) -> None:
            if event == "return" and frame.f_code in self.codes:
                path.returns[frame.f_code] = frame.f_lineno
            if previous is not None:
                previous(frame, event, arg)

        sys.setprofile(profile)
        try:
            with asking_proof_questions(self):
                yield
        finally:
            sys.setprofile(previous)
            _ACTIVE.reset(token)

    def run(self, schedule: list[bool]) -> _Path:
        """Run the body once, with the first case splits answered by ``schedule``."""
        path = _Path(list(schedule))
        path.facts = self._base_facts()
        fn = self.fn
        body = pytypes.FunctionType(
            fn.__code__, self.namespace, fn.__name__, fn.__defaults__, fn.__closure__
        )
        body.__kwdefaults__ = fn.__kwdefaults__
        arguments: dict[str, Any] = {name: Var(name) for name in self.variables}
        arguments.update({name: Given(name, prop, self) for name, prop in self.hypotheses.items()})
        with self._tracing(path):
            result = self._call(body, (), arguments)
            code = fn.__code__
            if isinstance(result, pytypes.FunctionType) and result.__code__ in self.codes:
                self._start_claim(result)
                assert self.claim is not None
                path.facts.extend(self._claim_facts())
                code = result.__code__
                result = self._call(result, tuple(Var(name) for name in self.claim.params), {})
            elif self.claim is not None:
                raise ProofError(
                    "claim",
                    "the body returns claim on one path and something else on another; "
                    "return claim on every path",
                    path.returns.get(code),
                )
            path.leaf = self._leaf(result, path)
            path.leaf = Leaf(tuple(path.questions), path.leaf.facts, path.returns.get(code))
        return path

    def _call(self, function: Any, values: tuple, named: dict[str, Any]) -> Any:
        """Call the body or ``claim``, turning what it raises into a refusal at its line."""
        try:
            return function(*values, **named)
        except ProofError:
            raise
        except SymbolicBoolError as exc:
            raise ProofError("question", str(exc), self._raised_at(exc)) from None
        except RecursionError:
            raise ProofError(
                "raised",
                "the proof calls itself without end; the claim at smaller values is "
                "written claim(...) inside def claim, and the body returns claim",
                None,
            ) from None
        except Exception as exc:  # noqa: BLE001 - the body is the user's, so say what it raised
            raise ProofError(
                "raised", f"the proof raised {type(exc).__name__}: {exc}", self._raised_at(exc)
            ) from None

    def _raised_at(self, exc: BaseException) -> int | None:
        """The line of the body an exception was raised at, the innermost one."""
        line = None
        trace = exc.__traceback__
        while trace is not None:
            if trace.tb_frame.f_code in self.codes:
                line = trace.tb_lineno
            trace = trace.tb_next
        return line

    def _start_claim(self, function: Any) -> None:
        """Read ``claim``'s definition once, and put the stub in its closure cell on every run."""
        if self.claim is None:
            self.claim = self._claim_def(function)
            self.claim_code = function.__code__
        elif function.__code__ is not self.claim_code:
            raise ProofError(
                "claim",
                "the body returns a different function on another path; return claim on every path",
                function.__code__.co_firstlineno,
            )
        stub = _ClaimStub(self)
        for index, _name in enumerate(function.__code__.co_freevars):
            cell = function.__closure__[index]
            try:
                contents = cell.cell_contents
            except ValueError:  # an empty cell holds nothing to swap
                continue
            if contents is function:
                cell.cell_contents = stub

    def _claim_def(self, function: Any) -> ClaimDef:
        """``claim``'s parameters, checked against the claim's variables (see :class:`ClaimDef`)."""
        code = function.__code__
        line = code.co_firstlineno
        params: list[str] = []
        for parameter in inspect.signature(function).parameters.values():
            plain = parameter.kind in (
                inspect.Parameter.POSITIONAL_ONLY,
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
            )
            if not plain or parameter.default is not inspect.Parameter.empty:
                raise ProofError(
                    "claim",
                    f"{function.__name__}'s parameters are the claim's variables, each a "
                    f"plain name; {parameter} is not",
                    line,
                )
            params.append(parameter.name)
        goal = self.goal
        binders = list(goal.binders) if isinstance(goal, Forall) else []
        names = [var.name for var, _ in binders]
        shadowing = [name for name in names if name in self.variables or name in self.hypotheses]
        if shadowing:
            raise ProofError(
                "claim",
                f"the claim's variable {shadowing[0]} has the name of a parameter of "
                f"{self.theorem.__name__}, so the two cannot be told apart in the proof; "
                "rename the claim's",
                line,
            )
        own = [name for name in params if name in names]
        if own != names:
            missing = [name for name in names if name not in params]
            what = (
                f"leaves out {', '.join(missing)}"
                if missing
                else f"takes them in another order than the claim, {', '.join(names)}"
            )
            raise ProofError(
                "claim",
                f"{function.__name__}({', '.join(params)}) takes the claim's variables, by "
                f"name and in order, and {what}",
                line,
                fix=f"def {function.__name__}({', '.join(names)})",
            )
        domains: list[Any] = []
        generalized: list[str] = []
        by_name = {var.name: domain for var, domain in binders}
        for name in params:
            if name in by_name:
                domains.append(by_name[name])
            elif name in self.variables:
                domains.append(self.variables[name])
                generalized.append(name)
            else:
                raise ProofError(
                    "claim",
                    f"{function.__name__}'s parameter {name} is neither a variable of the "
                    f"claim ({', '.join(names) or 'it has none'}) nor a parameter of "
                    f"{self.theorem.__name__} to generalize",
                    line,
                )
        return ClaimDef(function.__name__, tuple(params), tuple(domains), tuple(generalized), line)

    def _leaf(self, result: Any, path: _Path) -> Leaf:
        """What a ``return`` gives: facts, or nothing for a bare one."""
        code = self.claim_code if self.claim is not None else self.fn.__code__
        line = path.returns.get(code)
        if result is None:
            return Leaf((), None, line)
        items = result if isinstance(result, tuple | list) else (result,)
        if not items:
            return Leaf((), None, line)
        return Leaf((), tuple(self._fact(item, line) for item in items), line)

    def _fact(self, item: Any, line: int | None) -> Citation:
        """One thing a ``return`` gives, as a citation; anything but a fact is refused."""
        from lanky.theory import Theorem

        if isinstance(item, Citation):
            return item
        if isinstance(item, Given):
            return Citation(item, None, line)
        if isinstance(item, Theorem):
            if item is self.theorem:
                raise self._self_reference(line)
            return Citation(item, None, line)
        if isinstance(item, _ClaimStub):
            params = ", ".join(self.claim.params) if self.claim else ""
            raise ProofError(
                "claim",
                "the claim is cited at the values it is about, closer to a base case, "
                "which is what makes it an induction",
                line,
                fix=f"{self.claim.name if self.claim else 'claim'}({params}), at smaller values",
            )
        what = type(item).__name__
        described = shown(item) if hasattr(item, "mapper_method") else f"a {what}"
        raise ProofError(
            "return",
            f"a proof returns the facts that give the case's claim, claim, or nothing; "
            f"this returns {described}",
            line,
        )

    # }}}


def _tree(leaves: list[Leaf]) -> Node:
    """The case tree of the paths' splits, each path's leaf at its end."""
    root = Node()
    for leaf in leaves:
        node = root
        for question in leaf.questions:
            if question.forced:
                continue
            if node.question is None:
                node.question = question
            elif render(node.question.prop) != render(question.prop):
                raise ProofError(
                    "paths",
                    "the body asks other questions on paths that agree so far; a proof has "
                    "to run the same way on every path up to each split",
                    question.line,
                )
            if question.answer:
                node.then = node.then or Node()
                node = node.then
            else:
                node.otherwise = node.otherwise or Node()
                node = node.otherwise
        node.leaf = leaf
    return root


def trace_proof(theorem: Any) -> Proof:
    """Trace a theorem's written proof (see the module).

    Raises:
        ValueError: If the theorem's body holds no proof (:func:`written_lines`).
        ProofError: For a proof lanky refuses before Lean is asked.
    """
    lines = written_lines(theorem.fn)
    if lines is None:
        raise ValueError(f"{theorem.__name__} has no written proof")
    tracer = _Tracer(theorem)
    leaves: list[Leaf] = []
    pending: list[tuple[list[bool], list[tuple[str, str]] | None]] = [([], None)]
    while pending:
        if len(leaves) >= MAX_PATHS:
            raise ProofError(
                "paths",
                f"the proof has more than {MAX_PATHS} cases; split the claim into lemmas",
                None,
            )
        schedule, expected = pending.pop()
        path = tracer.run(schedule)
        if expected is not None and path.events[: len(expected)] != expected:
            raise ProofError(
                "paths",
                "the body does not run the same way on every path: it cites or asks something "
                "else before a split than it did before, and a proof has to give the same "
                "steps each time",
                path.leaf.line if path.leaf else None,
            )
        assert path.leaf is not None
        leaves.append(path.leaf)
        for index in reversed(range(len(schedule), len(path.branches))):
            prefix = path.branches[:index] + [False]
            pending.append((prefix, path.events[: path.branch_events[index]]))
    root = _tree(leaves)
    return Proof(
        theorem=theorem,
        claim=tracer.claim,
        root=root,
        leaves=tuple(leaves),
        lines=lines,
        path=theorem.path,
    )
