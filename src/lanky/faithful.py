"""The faithfulness fact: a claim's term computes what its annotations compute (#91).

The design idea. lanky reads an annotation by running its Python on terms
(:func:`lanky.terms.evaluate_annotations`), and every oracle is handed the term
that reading leaves. Some of Python's operations answer from the object they
are handed rather than through its overloads: ``is``, an attribute load, a
hash, a text, the truth value of a number, a comparison of two lanky types. On
a term each of them gives one answer, whatever value the term takes, so the
term says something else than the claim, and an oracle proves the term. Rules
refuse the cases found so far (#61, #63, #64, #70, #73), and each fix found
more; a helper function or a library between the annotation and the term
escapes all of them (#79, #80, #88).

So the reading is checked by its results rather than by its spelling, as
loopty checks a kernel's trace against its body (its ``trace-faithful``
fact): each annotation of a claim is run again as Python at drawn concrete
values of the parameters, the term the reading left is evaluated at the same
values by lanky's own evaluator, and the two have to agree. Whatever answered
from the term rather than from its value shows up as a point where they do
not.

*The rerun.* An annotation is compiled from its source again and evaluated as
Python evaluates it, in a copy of the function's globals as they were when
lanky read it (:attr:`lanky.theory.Theorem.namespace`): a name that is not a
parameter is the module's or the builtins', and ``all``, ``any``, ``sum`` and
``abs`` are Python's. A parameter that is a variable is its drawn value, a
family a :class:`~lanky.testing.Table`, which is callable, and a parameter
that is a hypothesis is the variable lanky's reading makes of it. The
prelude's types iterate concretely while the rerun runs
(:func:`lanky.terms.concrete_sorts`): ``Fin[n]`` at a drawn ``n`` is
``range(n)`` already, and a sort with no end, ``Nat`` say, iterates a finite
sample of itself, drawn once per draw, which is the same list wherever and
however often the annotation iterates it. One operator is read as a lanky
statement means it: ``~`` of a truth value is ``not``, where Python's ``~`` of
a ``bool`` is the bitwise complement of an integer, ``~True == -2``. A term the
rerun builds anyway, from a module-level variable or a function that makes
terms on purpose (``lanky.cas.from_sympy``), is read at the draw by the
evaluator.

*The term.* The term is evaluated at the same values by lanky's evaluator
(:class:`lanky.terms.LankyEvaluationMapper`) in the Python reading, the one
:meth:`lanky.theory.Theorem.__call__` uses, so that Python's numbers and its
rounding are on both sides. A quantifier over a sort ranges over the same
sample the rerun iterated, read as the whole domain, so a universal and an
existential are answered over it both ways, as Python's ``all`` and ``any``
answer them. A variable's sort is compared too, by what it is at the draw: a
``Fin``'s bound, a refinement's truth values, a family's domain and values.

*The points.* The draws are the property tester's
(:func:`lanky.testing.sample_value`, with the definitional hypotheses
satisfied by construction, :func:`lanky.testing.satisfy_hypotheses`), from its
seed, after :data:`CORNERS` draws of small values and domain ends: every
natural the tester draws, a ``Fin``'s first and last points, zero, one and
minus one. A bounded quantifier enumerates every point of its domain anyway.

*Agreement.* The two readings agree at a draw when every annotation computes
the same there: the same truth value, or the same value. An exception on one
side and a value on the other is a disagreement: ``i.name`` raises at a
number, where its term has a value. Two answers count as no answer, as they
do for the tester (:data:`lanky.terms.Undecided`): a division by zero, an
elementary function outside its Python domain, a family applied outside its
domain, and an overflow, on either side, since lanky's reading settles such a
point three-valued where Python stops at the first. So does a point where both
sides raise. A disagreement at a point where the term computed a floating-point
number is not counted either, and is recorded as ``rounding``: Python rounds
the annotation's arithmetic in the order it is written and the term's in the
order pymbolic keeps it, which can differ in the last bit, while the claim is
read over the reals.

*The fact.* Its kind is ``faithful``, its id is the claim's with that kind
(``faithful:gauss.gauss@31``), and its owner is the claim's. It is

* ``refuted`` at the first draw at which an annotation and its term disagree,
  with the draw as ``counterexample``, the annotation as ``witness``, and both
  answers in the ``reason``;
* ``tested`` by ``python`` when some annotation was compared at some draw and
  none disagreed;
* ``assumed``, with the reason as ``declined``, when nothing could be
  compared: a statement with a free name, a variable of a sort the tester
  cannot draw, an annotation Python evaluated when the function was defined
  that holds a term, or draws at which no annotation had an answer on both
  sides.

The check is sampled: a disagreement only at a point no draw reaches escapes
it. :mod:`lanky.theory` gives each claim's fact this one's id, and
:func:`lanky.check.establish` rests every decision and proof of the claim on
it, and offers a claim whose reading is refuted to no oracle.
"""

from __future__ import annotations

import ast
import inspect
import random
import warnings
from collections.abc import Iterator, Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import numpy
import pymbolic.primitives as prim

from lanky.intervals import ComplexValue
from lanky.ledger import Fact, Status, fact_id
from lanky.prelude import FinType, FnType, LankyType, Refined, Sort, SumType
from lanky.terms import (
    LankyEvaluationMapper,
    Polarity,
    Undecided,
    Var,
    concrete_sorts,
    render,
)
from lanky.testing import (
    MAX_NAT,
    SAMPLED_SORTS,
    OpenStatement,
    SkipSample,
    Table,
    Unsampleable,
    sample_value,
    sampling_order,
    satisfy_hypotheses,
    statement_free_names,
)

__all__ = [
    "CORNERS",
    "DECIDED_BY",
    "KIND",
    "SAMPLES",
    "SEED",
    "SORT_POINTS",
    "STATEMENT",
    "faithful_fact",
]

#: The kind of the fact, as the ledger and its JSON name it.
KIND = "faithful"

#: What the statement of the fact says, for every claim.
STATEMENT = "the term computes what the annotations compute"

#: Who the fact names as its decider when the comparison was made.
DECIDED_BY = "python"

#: How many draws of small values and domain ends come first: enough that a
#: single natural takes every value the tester draws, ``0`` to ``MAX_NAT``.
CORNERS = MAX_NAT + 1

#: How many of the property tester's draws follow them.
SAMPLES = 32

#: How many times as many draws are attempted, for those that cannot be
#: completed (an empty ``Fin``, a definition outside its codomain).
ATTEMPTS = 4

#: The seed of the draws, the property tester's.
SEED = 0

#: How many drawn points a sort's sample holds besides its small values.
SORT_POINTS = 2

#: The small values each sort's sample starts with.
_SMALL: dict[str, tuple[Any, ...]] = {
    "Nat": (0, 1, 2),
    "Int": (0, -1, 1),
    "Real": (Fraction(0), Fraction(1), Fraction(-1, 2)),
    "Complex": (0j, 1 + 0j, 1j),
    "Bool": (False, True),
    "Prop": (False, True),
}

#: What a point raises where lanky's reading has no answer and Python's stops:
#: a quantifier the draws leave open, a family applied outside its domain, a
#: division by zero, an elementary function outside its domain, an overflow.
_OPEN = (Undecided, ArithmeticError)

#: The name the rerun calls ``~`` by (see :func:`_invert`).
_INVERT = "__lanky_invert__"


# {{{ the rerun


def _invert(value: Any) -> Any:
    """``~value`` as a lanky statement means it: ``not`` of a truth value.

    lanky's connectives are ``&``, ``|`` and ``~``. On two truth values
    Python's ``&`` and ``|`` are ``and`` and ``or`` already, and its ``~``
    is the bitwise complement of the integer a ``bool`` is, ``~True == -2``,
    which is truthy. Anything else is Python's ``~``: a numpy truth value's
    is its negation, and an integer's is its complement, which lanky reads
    otherwise, as the negation of a proposition.
    """
    if isinstance(value, bool):
        return not value
    return ~value


class _Invert(ast.NodeTransformer):
    """Call :func:`_invert` for every ``~`` in an annotation's source."""

    def visit_UnaryOp(self, node: ast.UnaryOp) -> Any:
        """``~operand`` as ``__lanky_invert__(operand)``; any other operator as it is."""
        self.generic_visit(node)
        if not isinstance(node.op, ast.Invert):
            return node
        call = ast.Call(ast.Name(_INVERT, ast.Load()), [node.operand], [])
        return ast.copy_location(call, node)


def _compiled(source: str) -> Any:
    """An annotation's source compiled for the rerun, with ``~`` read as :func:`_invert` reads it.

    ``eval`` strips the spaces and tabs a string starts with and ``compile``
    does not, so they are stripped here as :func:`lanky.terms.evaluate_annotations`
    strips them.
    """
    with warnings.catch_warnings():
        # Python warned about the source when lanky read it, ``is not`` with
        # a literal say, and saying it twice says nothing more.
        warnings.simplefilter("ignore", SyntaxWarning)
        tree = ast.parse(source.lstrip(" \t"), "<string>", "eval")
        tree = ast.fix_missing_locations(_Invert().visit(tree))
        return compile(tree, "<string>", "eval")


@dataclass(frozen=True)
class _Outcome:
    """What one reading of one annotation came to at one draw: a value, or what it raised."""

    value: Any = None
    error: Exception | None = None

    def text(self) -> str:
        """The outcome as a reason says it."""
        if self.error is not None:
            return f"raises {type(self.error).__name__}: {self.error}"
        return f"computes {_shown(self.value)}"


def _shown(value: Any) -> str:
    """A value as a reason shows it: a term rendered, a family as its values, short."""
    if isinstance(value, prim.ExpressionNode):
        text = render(value)
    elif isinstance(value, Table):
        text = repr(value.values)
    else:
        text = repr(value)
    return text if len(text) <= 120 else text[:117] + "..."


# }}}


# {{{ the term, at a draw


class _Reading(LankyEvaluationMapper):
    """lanky's evaluator in the Python reading, a sort read as the sample the rerun iterated.

    ``floating`` records whether a value it computed was a floating-point
    number, so that a disagreement rounding can explain is told from one it
    cannot (see the module docstring).
    """

    def __init__(self, context: dict[str, Any], samples: _Samples) -> None:
        super().__init__(context, samples, Polarity.POSITIVE)
        self.exact = False
        self.floating = False

    @staticmethod
    def is_exhaustive(domain: Any) -> bool:
        """Every domain is walked whole: a sort's sample is its domain here."""
        return True

    def rec(self, expr: Any, *args: Any, **kwargs: Any) -> Any:
        """Evaluate ``expr``, noting a floating-point value."""
        value = super().rec(expr, *args, **kwargs)
        if isinstance(value, float | complex | numpy.inexact):
            self.floating = True
        return value

    __call__ = rec


def _sort_at(sort: Any, reading: _Reading) -> Any:
    """``sort`` as it is at the draw ``reading`` holds: its bounds and refinements evaluated."""
    if isinstance(sort, FinType):
        return FinType(reading.rec(sort.bound))
    if isinstance(sort, FnType):
        return FnType(_sort_at(sort.domain, reading), _sort_at(sort.codomain, reading))
    if isinstance(sort, Refined):
        return Refined(
            _sort_at(sort.base, reading), tuple(reading.rec(prop) for prop in sort.props)
        )
    if isinstance(sort, SumType):
        return SumType(tuple(_sort_at(piece, reading) for piece in sort.pieces))
    if isinstance(sort, prim.ExpressionNode):
        return reading.rec(sort)
    return sort


def _value_at(value: Any, reading: _Reading) -> Any:
    """A term or a type read at the draw; anything else as it is."""
    if isinstance(value, LankyType):
        return _sort_at(value, reading)
    if isinstance(value, prim.ExpressionNode):
        return reading.rec(value)
    return value


def _holds_term(value: Any) -> bool:
    """Whether ``value`` is a term, or a type or container that holds one."""
    if isinstance(value, prim.ExpressionNode):
        return True
    if isinstance(value, FinType):
        return _holds_term(value.bound)
    if isinstance(value, FnType):
        return _holds_term(value.domain) or _holds_term(value.codomain)
    if isinstance(value, Refined):
        return _holds_term(value.base) or any(_holds_term(prop) for prop in value.props)
    if isinstance(value, SumType):
        return any(_holds_term(piece) for piece in value.pieces)
    if isinstance(value, tuple | list | set | frozenset):
        return any(_holds_term(item) for item in value)
    if isinstance(value, dict):
        return any(_holds_term(item) for item in (*value.keys(), *value.values()))
    return False


# }}}


# {{{ the draws


class _Samples:
    """The finite sample each sort iterates at one draw, the same for both readings.

    A sort's sample is its small values (:data:`_SMALL`) and
    :data:`SORT_POINTS` of the tester's draws of it, drawn the first time the
    sort is iterated at the draw and kept, so that the rerun and the term
    range over the same points wherever and however often they iterate it.
    """

    def __init__(self, rng: random.Random) -> None:
        self.rng = rng
        self.drawn: list[tuple[Any, list[Any]]] = []

    def __call__(self, sort: Any) -> list[Any]:
        """The sample of ``sort``, or of what it refines.

        Raises:
            Unsampleable: For a sort the tester has no sampler for.
        """
        while isinstance(sort, Refined):
            sort = sort.base
        for seen, points in self.drawn:
            if seen is sort or (isinstance(seen, Sort) and seen == sort):
                return points
        if not isinstance(sort, Sort) or sort.name not in SAMPLED_SORTS:
            raise Unsampleable(f"no sampler for {sort!r}")
        points = list(_SMALL[sort.name])
        if sort.name not in ("Bool", "Prop"):
            for _ in range(SORT_POINTS):
                point = _python(sample_value(sort, self.rng, {}))
                if not any(type(point) is type(seen) and point == seen for seen in points):
                    points.append(point)
        self.drawn.append((sort, points))
        return points

    def described(self) -> dict[str, list[Any]]:
        """The samples drawn, by sort, as a counterexample shows them."""
        return {str(sort): list(points) for sort, points in self.drawn}


class _Corners(random.Random):
    """A stand-in for the tester's random source that gives small values and domain ends.

    The tester draws every value through ``randrange`` and ``random``
    (:func:`lanky.testing.sample_value`). Here ``randrange`` answers the
    ``k``-th of the values in its range nearest zero and its ends, in the
    order ``0``, ``1``, ``-1``, the last, the first, and then outwards from
    zero, so the ``k``-th corner draw puts a natural at ``0``, ``1``, ``5``,
    ``2``, ``3``, ``4``, a point of ``Fin[n]`` at ``0``, ``1``, ``n - 1``,
    ..., and a rational at ``0``, ``1/4``, ``-1/2``, ``8/3``, ...; so the
    first draws, at which a disagreement is reported, are the smallest.
    ``random`` answers ``0`` and then ``0.75``, so a ``Bool`` is ``True`` and
    then ``False``.
    """

    def __init__(self, k: int) -> None:
        super().__init__(k)
        self.k = k

    def randrange(self, start: int, stop: int | None = None, step: int = 1) -> int:  # type: ignore[override]
        """The ``k``-th value of the range in the order the class docstring gives."""
        if stop is None:
            start, stop = 0, start
        order = [0, 1, -1, stop - 1, start]
        for magnitude in range(2, max(abs(start), abs(stop)) + 1):
            order += [magnitude, -magnitude]
        candidates = list(dict.fromkeys(v for v in order if start <= v < stop))
        candidates += [v for v in range(start, stop) if v not in candidates]
        return candidates[self.k % len(candidates)]

    def random(self) -> float:
        """``0`` at an even ``k`` and ``0.75`` at an odd one."""
        return 0.0 if self.k % 2 == 0 else 0.75


def _python(value: Any) -> Any:
    """A drawn value as Python computes with it.

    The tester draws a ``Complex`` as a :class:`~lanky.intervals.ComplexValue`
    of two fractions, for its exact reading; both readings here are Python's,
    and Python's ``exp`` and ``log`` take a ``complex``. A family's values are
    converted the same way.
    """
    if isinstance(value, ComplexValue):
        return complex(float(value.real), float(value.imag))
    if isinstance(value, Table):
        return Table([_python(item) for item in value.values], name=value.name)
    return value


@dataclass
class _Draw:
    """One draw: its label, the values of the variables, and the samples of the sorts."""

    label: str
    context: dict[str, Any]
    samples: _Samples


def _draws(variables: Sequence[tuple[str, Any]], hypotheses: Sequence[Any]) -> Iterator[Any]:
    """The draws to compare at, corner draws first; a string for a draw that could not be made.

    Each draw takes a value of every variable, a size before what it sizes
    (:func:`lanky.testing.sampling_order`), and then assigns the definitional
    hypotheses, as the tester does, so that a family that is a scan of
    another is one. A statement with no variables has one draw, the empty one.
    """
    ordered = sampling_order(variables)
    sorts = dict(ordered)
    rng = random.Random(SEED)
    sources: list[tuple[str, random.Random]] = [
        (f"corner {k}", _Corners(k)) for k in range(CORNERS if ordered else 1)
    ]
    made = 0
    attempt = 0
    while sources or (ordered and made < SAMPLES and attempt < SAMPLES * ATTEMPTS):
        if sources:
            label, source = sources.pop(0)
        else:
            label, source = f"draw {attempt}", rng
            attempt += 1
        samples = _Samples(random.Random(f"{SEED}:{label}"))
        context: dict[str, Any] = {}
        try:
            for name, sort in ordered:
                context[name] = _python(sample_value(sort, source, context, name))
            satisfy_hypotheses(hypotheses, context, sorts, samples)
        except SkipSample as exc:
            yield f"{label}: {exc}"
            continue
        if label.startswith("draw"):
            made += 1
        yield _Draw(label, context, samples)


# }}}


# {{{ comparing


@dataclass(frozen=True)
class _Annotation:
    """One annotation of a claim: what it says, its source, and the term lanky read off it."""

    name: str
    role: str
    term: Any
    code: Any = None
    given: Any = None

    @property
    def what(self) -> str:
        """The annotation as a reason names it."""
        if self.role == "goal":
            return "the goal"
        if self.role == "sort":
            return f"the sort of {self.name}"
        return f"the hypothesis {self.name}"


def _judge(python: _Outcome, term: _Outcome, floating: bool) -> str:
    """How the two readings of one annotation compare at one draw.

    ``agreed``, ``differed``, ``rounding`` (they differ where floating point
    was computed), ``open`` (one side has no answer, see :data:`_OPEN`),
    ``silent`` (both raised), or ``uncomparable`` (a value ``==`` cannot
    compare).
    """
    if isinstance(python.error, _OPEN) or isinstance(term.error, _OPEN):
        return "open"
    if python.error is not None and term.error is not None:
        return "silent"
    if python.error is not None or term.error is not None:
        return "differed"
    a, b = python.value, term.value
    if _holds_term(a) or _holds_term(b):
        return "uncomparable"
    truths = [isinstance(value, bool | numpy.bool_) for value in (a, b)]
    if any(truths):
        if not all(truths):
            # a truth value and a number: one reading is a proposition and
            # the other is not, which the tester and Lean read differently
            return "differed"
        same = bool(a) == bool(b)
    else:
        try:
            answer = a == b
        except Exception:  # noqa: BLE001 - values == cannot compare are not compared
            return "uncomparable"
        if not isinstance(answer, bool | numpy.bool_):
            return "uncomparable"
        same = bool(answer)
    if same:
        return "agreed"
    return "rounding" if floating else "differed"


def _compare(
    namespace: dict[str, Any],
    parameters: Sequence[str],
    annotations: Sequence[_Annotation],
    draw: _Draw,
) -> Iterator[tuple[_Annotation, str, _Outcome, _Outcome]]:
    """Each annotation, how its two readings compare at ``draw``, and the two outcomes.

    ``namespace`` is the function's globals as they were when lanky read the
    annotations (:attr:`lanky.theory.Theorem.namespace`).
    """
    scope = dict(namespace)
    for name in parameters:
        scope[name] = draw.context[name] if name in draw.context else Var(name)
    scope[_INVERT] = _invert
    for annotation in annotations:
        reading = _Reading(dict(draw.context), draw.samples)
        with concrete_sorts(draw.samples):
            try:
                if annotation.code is not None:
                    value = eval(annotation.code, scope, None)
                else:
                    value = annotation.given
                python = _Outcome(_value_at(value, reading))
            except Exception as exc:  # noqa: BLE001 - what the annotation raises is its answer
                python = _Outcome(error=exc)
        if isinstance(python.value, float | complex | numpy.inexact):
            reading.floating = True
        try:
            term = _Outcome(_value_at(annotation.term, reading))
        except Exception as exc:  # noqa: BLE001 - what the term raises is its answer
            term = _Outcome(error=exc)
        yield annotation, _judge(python, term, reading.floating), python, term


# }}}


def _annotations(theorem: Any) -> list[_Annotation] | str:
    """The claim's annotations, in the order lanky read them; or why they cannot be rerun."""
    fn = theorem.fn
    raw = inspect.get_annotations(fn, eval_str=False)
    terms: dict[str, tuple[str, Any]] = {name: ("sort", sort) for name, sort in theorem.variables}
    terms.update((name, ("hypothesis", prop)) for name, prop in theorem.hypotheses)
    terms["return"] = ("goal", theorem.goal)
    out: list[_Annotation] = []
    for name, annotation in raw.items():
        if name not in terms:
            continue
        role, term = terms[name]
        if isinstance(annotation, str):
            out.append(_Annotation(name, role, term, code=_compiled(annotation)))
            continue
        if _holds_term(annotation):
            what = "the goal" if role == "goal" else f"the annotation of {name}"
            return (
                f"{what} was evaluated by Python when the function was defined, "
                "without `from __future__ import annotations`, and it holds a term, "
                "so there is no source to run again at a point"
            )
        # Python computed it once, and the reading took that value as it is.
        out.append(_Annotation(name, role, term, given=annotation))
    return out


def faithful_fact(theorem: Any) -> Fact:
    """The ``faithful`` fact of one claim, established by rerunning its annotations.

    ``theorem`` is a :class:`lanky.theory.Theorem`, or an
    :class:`~lanky.theory.Axiom`. Nothing here raises: anything the rerun
    cannot do leaves the fact ``assumed``, with the reason as ``declined``.
    """
    identifier = fact_id(KIND, theorem.qualname, module=theorem.module, line=theorem.line)

    def fact(status: Status, **provenance: Any) -> Fact:
        return Fact(
            id=identifier,
            kind=KIND,
            statement=STATEMENT,
            term=None,
            status=status,
            decided_by=None if status is Status.ASSUMED else DECIDED_BY,
            provenance={"path": theorem.path, "line": theorem.line, **provenance},
            where=theorem.where,
            owner=theorem.qualname,
        )

    def declined(why: str) -> Fact:
        return fact(Status.ASSUMED, declined=f"{DECIDED_BY}: {why}")

    try:
        hypotheses = [prop for _, prop in theorem.hypotheses]
        free = statement_free_names(theorem.variables, hypotheses, theorem.goal)
        if free:
            names = OpenStatement(free).names
            listing = names[0] if len(names) == 1 else f"{', '.join(names[:-1])} and {names[-1]}"
            return declined(
                f"the statement mentions {listing}, which no parameter or binder of it "
                "binds, so no draw gives it a value and its annotations cannot be run "
                "again at one"
            )
        annotations = _annotations(theorem)
        if isinstance(annotations, str):
            return declined(annotations)
        parameters = list(inspect.signature(theorem.fn).parameters)
        counts = {"draws": 0, "compared": 0, "rounding": 0, "open": 0, "silent": 0}
        skipped: list[str] = []
        unanswered = ""
        for draw in _draws(theorem.variables, hypotheses):
            if isinstance(draw, str):
                skipped.append(draw)
                continue
            counts["draws"] += 1
            for annotation, verdict, python, term in _compare(
                theorem.namespace, parameters, annotations, draw
            ):
                if verdict == "agreed":
                    counts["compared"] += 1
                elif verdict == "differed":
                    return _refuted(fact, annotation, draw, python, term)
                elif verdict in counts:
                    counts[verdict] += 1
                    unanswered = unanswered or _unanswered(annotation, python, term)
                else:
                    unanswered = unanswered or (
                        f"{annotation.what} computes {_shown(python.value)} and its term "
                        f"{_shown(term.value)}, which == cannot compare"
                    )
    except Exception as exc:  # noqa: BLE001 - a fact, never a crash of the check
        return declined(f"the annotations could not be run again: {type(exc).__name__}: {exc}")
    if not counts["draws"]:
        why = skipped[0] if skipped else "no draw could be made"
        return declined(f"no draw could be made, so nothing was compared ({why})")
    if not counts["compared"]:
        return declined(
            f"no annotation had an answer on both sides at any of {counts['draws']} "
            f"draws, so nothing was compared ({unanswered})"
        )
    extra = {key: counts[key] for key in ("rounding", "open", "silent") if counts[key]}
    return fact(
        Status.TESTED,
        draws=counts["draws"],
        compared=counts["compared"],
        seed=SEED,
        **extra,
    )


def _unanswered(annotation: _Annotation, python: _Outcome, term: _Outcome) -> str:
    """Why an annotation was not compared at a draw, as the reason of an ``assumed`` fact."""
    return f"{annotation.what}: as Python it {python.text()}, and its term {term.text()}"


def _refuted(
    fact: Any, annotation: _Annotation, draw: _Draw, python: _Outcome, term: _Outcome
) -> Fact:
    """The refutation at ``draw``, where ``annotation`` and its term disagree."""
    counterexample = {
        name: list(value.values) if isinstance(value, Table) else value
        for name, value in draw.context.items()
    }
    sampled = draw.samples.described()
    witness = annotation.what
    if sampled:
        witness += f", with each sort iterating {sampled}"
    return fact(
        Status.REFUTED,
        counterexample=counterexample,
        witness=witness,
        python_answer=python.text(),
        term_answer=term.text(),
        draw=draw.label,
        reason=(
            f"at this draw {annotation.what}, run again as Python, {python.text()}, "
            f"and its term {term.text()}: the term says something else than what "
            "was written, so no oracle that decides or proves is asked about the claim"
        ),
    )
