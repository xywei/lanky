"""The native run of a written proof: the body run as plain Python, at drawn values.

The design idea. ``assert`` already means "check this here", so a proof's
steps are tests for free: lanky runs the body as plain Python at the values
the check draws (:func:`lanky.testing.valid_draws`), exact ``Fraction`` values and
exact complex numbers, never floats, before Lean is asked. There:

- ``name.conclusion.domain`` gives the domain's first points, in the loop's
  order (from the top down under ``reversed(...)``), up to the tester's
  draw bound (:data:`lanky.testing.MAX_NAT` for a natural), the
  conclusion's guard holding at each; a nested ``for`` is walked at the
  point of the loop around it;
- each ``assert`` is Python's own: a false step raises, and lanky reports it
  at its line, with the values there and the two sides of the comparison
  that failed;
- each point's conclusion is checked when the loop moves on, so a point no
  step of the proof can reach is caught too;
- ``by(...)`` is read only where a step fails, as Python reads it, and a
  citation in it is inert.

A failure is a counterexample, which needs no Lean (:func:`native_failure`).
The run only tests: it never proves a step, and a draw it cannot finish (a
comparison its enclosures cannot settle, a value with no exact form, a
float) says nothing either way. A user can run a proof the same way by hand,
at values of their own (:func:`run_by_hand`, :meth:`lanky.theory.Theorem.run_proof`),
in a REPL or under pdb.
"""

from __future__ import annotations

import ast
import builtins
import sys
import types as pytypes
from collections.abc import Iterator, Mapping
from contextlib import ExitStack
from fractions import Fraction
from typing import Any

from lanky.proofs.trace import (
    _assert_at_line,
    _own_codes,
    body_arguments,
    is_generator,
    namespace,
    running,
)

__all__ = [
    "NATIVE_DRAWS",
    "ExactInt",
    "PointFalse",
    "native_failure",
    "native_run",
    "run_by_hand",
]

#: How many of the check's draws the body is run at.
NATIVE_DRAWS = 50

#: How many points of a conclusion's domain one loop walks at most.
POINT_LIMIT = 200


class PointFalse(AssertionError):
    """The conclusion is false at a point of its domain a native run reached."""


class ExactInt(int):
    """An integer whose quotient is a ``Fraction``: ``(n - 1) / n`` stays exact.

    Python's ``/`` of two integers is a float, which a step's comparison
    would then read rounded. The values the native run gives, its points and
    its drawn integers, are these, and their sums, differences, products and
    powers stay these, so a quotient of them is exact as the step means it.
    """

    def _wrap(self, value: Any) -> Any:
        return ExactInt(value) if isinstance(value, int) and not isinstance(value, bool) else value

    def __truediv__(self, other: Any) -> Any:
        if isinstance(other, int) and not isinstance(other, bool):
            return Fraction(int(self), int(other))
        return NotImplemented if isinstance(other, float) else Fraction(int(self)) / other

    def __rtruediv__(self, other: Any) -> Any:
        if isinstance(other, int) and not isinstance(other, bool):
            return Fraction(int(other), int(self))
        return NotImplemented if isinstance(other, float) else other / Fraction(int(self))

    def __add__(self, other: Any) -> Any:
        return self._wrap(int.__add__(self, other))

    __radd__ = __add__

    def __sub__(self, other: Any) -> Any:
        return self._wrap(int.__sub__(self, other))

    def __rsub__(self, other: Any) -> Any:
        return self._wrap(int.__rsub__(self, other))

    def __mul__(self, other: Any) -> Any:
        return self._wrap(int.__mul__(self, other))

    __rmul__ = __mul__

    def __pow__(self, other: Any, modulo: Any = None) -> Any:
        if isinstance(other, int) and other < 0 and modulo is None:
            return Fraction(int(self)) ** int(other)
        return self._wrap(int.__pow__(self, other, modulo))

    def __neg__(self) -> Any:
        return ExactInt(-int(self))

    def __floordiv__(self, other: Any) -> Any:
        return self._wrap(int.__floordiv__(self, other))

    def __mod__(self, other: Any) -> Any:
        return self._wrap(int.__mod__(self, other))

    def __repr__(self) -> str:
        return repr(int(self))

    __str__ = __repr__


def exact(value: Any) -> Any:
    """A drawn value as the native run hands it to the body: an integer as an :class:`ExactInt`."""
    if isinstance(value, int) and not isinstance(value, bool | ExactInt):
        return ExactInt(value)
    return value


class _Fact:
    """A fact cited in a native run, inert: ``by(...)`` is read only where a step fails."""

    def __init__(self, text: str) -> None:
        self.text_ = text

    def text(self) -> str:
        """How the citation is written."""
        return self.text_

    def __getitem__(self, point: Any) -> _Fact:
        """The fact at a point of its domain, ``pde[i, a - 2, b]``, as inert as the fact."""
        values = point if isinstance(point, tuple) else (point,)
        return _Fact(f"{self.text_}[{', '.join(_number(value) for value in values)}]")

    def __call__(self, *values: Any, **named: Any) -> _Fact:
        """Refused: a point is given in brackets (lanky 0.5 gave it in parentheses)."""
        from lanky.surface import RemovedForm

        shown = [_number(value) for value in values]
        raise RemovedForm(
            f"{self.text_}({', '.join(shown)}) is how lanky 0.5 cited a condition at a point; "
            "brackets give a point of its domain",
            f"{self.text_}[{', '.join(shown)}]",
        )

    def __bool__(self) -> bool:
        """Refuse: a fact has no truth value."""
        raise TypeError(f"{self.text_} is a fact, and a fact has no truth value to ask for")

    def __repr__(self) -> str:
        return self.text_


class _Called(_Fact):
    """Another claim called for inputs in a native run, ``gauss(n - 1)``: inert, with its tree."""

    @property
    def conclusion(self) -> Any:
        """``other(x).conclusion``, inert: its points in brackets."""
        return _Fact(f"{self.text_}.conclusion")


class _Point:
    """Where a native run's loops are: the point, how many levels deep, the line that closed it."""

    def __init__(self) -> None:
        self.values: dict[str, Any] | None = None
        self.depth = 0
        self.line: int | None = None
        self.checked = True


class _Run:
    """One native run of a body at one draw: what the claim's tree and a call mean there."""

    def __init__(self, theorem: Any, context: Mapping[str, Any], bound: int) -> None:
        from lanky.surface import levels

        self.theorem = theorem
        self.context = dict(context)
        self.bound = bound
        self.levels = levels(theorem.goal)
        self.point = _Point()
        self.loop_line: int | None = None

    @property
    def name(self) -> str:
        """The claim's name, as its proof spells it."""
        return getattr(self.theorem, "qualname", None) or self.theorem.__name__

    def statement_at(self, depth: int) -> Any:
        """The conclusion at a point ``depth`` levels deep: the goal under those ``for`` levels."""
        node = self.theorem.goal
        for _ in range(depth):
            node = node.body
        return node

    # {{{ what the claim's tree and a call mean here

    def loop(self, conclusion: Any, reverse: bool, frame: Any) -> Iterator[Any]:
        """``name.conclusion.domain``: the conclusion's first points, in the loop's order."""
        level = len(conclusion.point)
        outer: dict[str, Any] = {}
        for index, values in enumerate(conclusion.point):
            names = [var.name for var, _ in self.levels[index][0]]
            outer.update(zip(names, values, strict=False))
        if self.loop_line is None:
            self.loop_line = getattr(frame, "f_lineno", None)
        return self._walk(level, outer, reverse)

    def _walk(self, level: int, outer: dict[str, Any], reverse: bool) -> Iterator[Any]:
        if level and self.point.depth == level:
            # the outer point is checked at each point of its own domain instead
            self.point.checked = True
        binders, guard = self.levels[level]
        names = [var.name for var, _ in binders]
        # reversed, the top of the domain first: each level walked from its top
        # down, so a large bounded domain is never walked in full to reach it
        points = _points(list(binders), guard, {**self.context, **outer}, self.bound, reverse)
        for count, values in enumerate(points):
            if count >= POINT_LIMIT:
                break
            self.check_point()
            self.point.values = {**outer, **dict(zip(names, values, strict=True))}
            self.point.depth = level + 1
            self.point.line = None
            self.point.checked = False
            yield values[0] if len(values) == 1 else tuple(values)
        self.check_point()

    def check_point(self) -> None:
        """Check the conclusion at the point the loop is leaving.

        Raises:
            PointFalse: Where it is false there.
        """
        point = self.point
        if point.checked or point.values is None:
            return
        point.checked = True
        from lanky.terms import evaluate

        try:
            holds = evaluate(self.statement_at(point.depth), {**self.context, **point.values})
        except Exception:  # noqa: BLE001 - a point with no answer is no counterexample
            return
        if holds is False:
            raise PointFalse(point)

    def check_goal(self, line: int | None) -> None:
        """Check the claim's goal where a proof with no loop over its domain ends.

        A proof that closes with ``return by(...)`` serves no point of a
        domain, so :meth:`check_point` has nothing to check; the goal is
        checked at the draw instead, as each point's is when its case closes.

        Raises:
            PointFalse: Where it is false at the draw.
        """
        if self.loop_line is not None or self.point.values is not None:
            return
        from lanky.terms import evaluate

        try:
            holds = evaluate(self.theorem.goal, dict(self.context))
        except Exception:  # noqa: BLE001 - a goal with no answer here is no counterexample
            return
        if holds is False:
            self.point.line = line
            raise PointFalse(self.point)

    def condition(self, claim: Any, name: str, frame: Any) -> _Fact:
        """``name.conditions.ode`` in the claim's own proof: the fact, inert."""
        if claim is not self.theorem:
            from lanky.surface import FormError

            raise FormError(f"{name} is a condition of {claim.__name__}, which its proof assumes")
        return _Fact(name)

    def cite_theorem(
        self, theorem: Any, values: tuple, named: Mapping[str, Any], frame: Any
    ) -> Any:
        """A claim called in a native run: inert, a citation for a ``by(...)``.

        Raises:
            lanky.surface.FormError: For the claim calling itself, which the
                trace refuses with the fix.
        """
        if theorem is self.theorem:
            from lanky.surface import FormError

            raise FormError(f"{self.name} calls itself in its own proof")
        shown = [_number(value) for value in values]
        shown += [f"{key}={_number(value)}" for key, value in named.items()]
        return _Called(f"{theorem.__name__}({', '.join(shown)})")

    def __repr__(self) -> str:
        return f"<the proof of {self.name}, run at drawn values>"

    # }}}


def _points(
    binders: list[tuple[Any, Any]],
    guard: Any,
    context: Mapping[str, Any],
    bound: int,
    reverse: bool = False,
) -> Iterator[tuple[Any, ...]]:
    """The points of the conclusion's domain, in the loop's order, its guard holding at each.

    Reversed, each binder's values are walked from the top down, which is the
    loop's order reversed: the points of a lexicographic order, reversed, are
    every level's values reversed.
    """
    from lanky.terms import evaluate

    def walk(index: int, scope: dict[str, Any]) -> Iterator[tuple[Any, ...]]:
        if index == len(binders):
            if guard is not None:
                try:
                    if evaluate(guard, scope) is not True:
                        return
                except Exception:  # noqa: BLE001 - a point whose guard has no answer is passed
                    return
            yield tuple(scope[var.name] for var, _ in binders)
            return
        var, domain = binders[index]
        for value in _domain_values(domain, var, scope, bound, reverse):
            yield from walk(index + 1, {**scope, var.name: value})

    yield from walk(0, dict(context))


def _domain_values(
    domain: Any, var: Any, scope: Mapping[str, Any], bound: int, reverse: bool = False
) -> Iterator[Any]:
    """The first values of a binder's domain: a ``Fin``'s points, the naturals to the bound.

    Reversed, its last values first, from the top down.
    """
    from lanky.prelude import FinType, Refined, Sort
    from lanky.terms import evaluate

    props: tuple[Any, ...] = ()
    while isinstance(domain, Refined):
        props += domain.props
        domain = domain.base
    if isinstance(domain, FinType):
        size = domain.bound
        if hasattr(size, "mapper_method"):
            size = evaluate(size, dict(scope))
        values: Any = range(int(size))
    elif isinstance(domain, Sort) and domain.name == "Nat":
        values = range(bound + 1)
    elif isinstance(domain, Sort) and domain.name == "Int":
        values = sorted(range(-bound, bound + 1), key=lambda value: (abs(value), value < 0))
    else:
        raise TypeError(f"the native run does not walk {domain}")
    if reverse:
        values = reversed(values)
    for value in values:
        exact_value = ExactInt(value)
        if props:
            point = {**scope, var.name: exact_value}
            try:
                if not all(evaluate(prop, point) is True for prop in props):
                    continue
            except Exception:  # noqa: BLE001 - a refinement with no answer passes the value over
                continue
        yield exact_value


def native_namespace(theorem: Any) -> dict[str, Any]:
    """A native run's globals: the trace's, with Python's ``all``, ``any``, ``sum``, ``abs``, ..."""
    out = namespace(theorem)
    for name in ("all", "any", "sum", "abs", "max", "min"):
        out[name] = getattr(builtins, name)
    return out


def _run(theorem: Any, values: Mapping[str, Any], run: _Run) -> None:
    """Run the body as plain Python at ``values``, ``run`` answering the claim's tree."""
    from lanky.terms import closed_truth, concrete_sorts, exact_reading

    fn = theorem.fn
    arguments: dict[str, Any] = {
        name: exact(values[name]) for name, _ in theorem.variables if name in values
    }
    for name, _prop in theorem.hypotheses:
        arguments[name] = _Fact(name)
    positional, named, outer = body_arguments(fn, arguments)
    globals_ = native_namespace(theorem)
    globals_.update(outer)
    body = pytypes.FunctionType(fn.__code__, globals_, fn.__name__, fn.__defaults__, fn.__closure__)
    body.__kwdefaults__ = fn.__kwdefaults__

    def points(sort: Any) -> list[Any]:
        from lanky.prelude import Sort

        if isinstance(sort, Sort) and sort.name == "Nat":
            return [ExactInt(value) for value in range(run.bound + 1)]
        if isinstance(sort, Sort) and sort.name == "Int":
            return [ExactInt(value) for value in range(-run.bound, run.bound + 1)]
        raise TypeError(f"the native run does not walk {sort}")

    with ExitStack() as stack:
        stack.enter_context(running(run))
        stack.enter_context(exact_reading())
        stack.enter_context(closed_truth())
        stack.enter_context(concrete_sorts(points))
        returned: list[int] = []
        if is_generator(fn):
            generator = body(*positional, **named)
            for value in generator:
                frame = generator.gi_frame
                if run.point.values is not None and run.point.line is None:
                    run.point.line = frame.f_lineno if frame is not None else None
                del value
        else:
            # the line the body returns at, which a false goal is reported at;
            # every event goes on to a profiler already installed, as the trace's do
            previous = sys.getprofile()

            def watch(frame: Any, event: str, arg: Any) -> None:
                if event == "return" and frame.f_code is fn.__code__:
                    returned.append(frame.f_lineno)
                if previous is not None:
                    previous(frame, event, arg)

            sys.setprofile(watch)
            try:
                body(*positional, **named)
            finally:
                sys.setprofile(previous)
        run.check_point()
        run.check_goal(returned[-1] if returned else None)


def native_failure(theorem: Any, samples: int = NATIVE_DRAWS, seed: int = 0) -> Any:
    """The first step or point of ``theorem``'s proof a native run finds false, as a report.

    ``None`` where none is found: a proof whose every step held at every
    draw, and one that could not be drawn or run at all. The report is a
    :class:`lanky.proofs.report.Failure` of kind ``false``, at the line of
    the step, with the values there.
    """
    return native_run(theorem, samples, seed)[0]


def native_run(theorem: Any, samples: int = NATIVE_DRAWS, seed: int = 0) -> tuple[Any, int]:
    """:func:`native_failure`, and how many draws the body ran to its end at, every step holding.

    A count of ``0`` with no failure is a proof the run could not draw or
    run at all, which it tested nothing of.
    """
    from lanky.proofs.filled import FILLED_DRAWS, filled_draws, over_the_naturals
    from lanky.terms import exact_reading
    from lanky.testing import MAX_NAT, valid_draws

    hypotheses = [prop for _name, prop in theorem.hypotheses]
    codes = _own_codes(theorem.fn.__code__)
    if any(over_the_naturals(sort) for _name, sort in theorem.variables):
        # no table of every natural is drawn: fill one in from the hypotheses
        draws = filled_draws(theorem, min(samples, FILLED_DRAWS), seed)
    else:
        try:
            with exact_reading():
                draws = list(valid_draws(theorem.variables, hypotheses, samples, seed))
        except Exception:  # noqa: BLE001 - a statement the tester cannot draw runs no proof
            return None, 0
    ran = 0
    for context in draws:
        run = _Run(theorem, context, MAX_NAT)
        try:
            _run(theorem, context, run)
        except PointFalse:
            return _point_failure(theorem, run), ran
        except AssertionError as exc:
            found = _step_failure(theorem, run, exc, codes)
            if found is not None:
                return found, ran
            continue
        except Exception:  # noqa: BLE001 - a draw the body cannot run at says nothing
            continue
        ran += 1
    return None, ran


def run_by_hand(theorem: Any, **values: Any) -> None:
    """Run ``theorem``'s proof as plain Python at ``values``, as a REPL or pdb would.

    A value for each variable, by name, as :meth:`lanky.theory.Theorem.__call__`
    takes them; a family as a sequence or a table. ``name.conclusion.domain``
    gives its first points, to the tester's draw bound, and a citation is inert. A
    false step raises Python's own ``AssertionError``, its message the
    step's ``by(...)``; a point where the claim is false raises
    :class:`PointFalse`. Floats compare exactly here, so a step can fail on
    rounding: give ``Fraction`` values.
    """
    from lanky.testing import MAX_NAT
    from lanky.theory import _as_family

    sorts = dict(theorem.variables)
    missing = [name for name in sorts if name not in values]
    if missing:
        raise TypeError(f"{theorem.__name__}'s proof needs values for {', '.join(missing)}")
    context = {name: _as_family(value, sorts.get(name), name) for name, value in values.items()}
    _run(theorem, context, _Run(theorem, context, MAX_NAT))


# {{{ the report


def _number(value: Any) -> str:
    """A value as a report writes it: ``3``, ``-1/24``, ``1 + 2j``."""
    from lanky.intervals import ComplexValue

    if isinstance(value, bool):
        return str(value)
    if isinstance(value, int):
        return str(int(value))
    if isinstance(value, Fraction):
        return str(value.numerator) if value.denominator == 1 else str(value)
    if isinstance(value, ComplexValue):
        real, imag = value.real, value.imag
        if isinstance(real, Fraction | int) and isinstance(imag, Fraction | int):
            if imag == 0:
                return _number(Fraction(real))
            magnitude = _number(Fraction(abs(imag)))
            imaginary = f"{'' if magnitude == '1' else magnitude}j"
            if real == 0:
                return f"-{imaginary}" if imag < 0 else imaginary
            return f"{_number(Fraction(real))} {'-' if imag < 0 else '+'} {imaginary}"
    if hasattr(value, "mapper_method"):
        from lanky.terms import render

        return render(value)
    return repr(value)


def _exact_number(value: Any) -> bool:
    """Whether a value is a number the native run reads exactly: no float, no enclosure."""
    from lanky.intervals import ComplexValue

    if isinstance(value, bool):
        return False
    if isinstance(value, int | Fraction):
        return True
    if isinstance(value, ComplexValue):
        return all(isinstance(part, int | Fraction) for part in (value.real, value.imag))
    return False


def _assignment(theorem: Any, run: _Run) -> str:
    """``n = 3, alpha = 2, beta = 1``: the point the loop is at, then the drawn numbers."""
    pairs: list[tuple[str, Any]] = list((run.point.values or {}).items())
    pairs += [
        (name, run.context[name])
        for name, _sort in theorem.variables
        if name in run.context and _exact_number(run.context[name])
    ]
    return ", ".join(f"{name} = {_number(value)}" for name, value in pairs if _exact_number(value))


def _step_failure(theorem: Any, run: _Run, exc: AssertionError, codes: Any) -> Any:
    """The report of an ``assert`` a native run found false, or ``None`` where it reads no number.

    The two sides of the comparison that failed are evaluated again in the
    failing frame, so that the report can give them; a side that is no
    exact number (a float, an enclosure) leaves the step unreported, since
    the run refutes only at exact values.
    """
    from lanky.proofs.report import Failure

    trace = exc.__traceback__
    frame = None
    line = None
    while trace is not None:
        if trace.tb_frame.f_code in codes:
            frame, line = trace.tb_frame, trace.tb_lineno
        trace = trace.tb_next
    if frame is None or line is None:
        return None
    node = _assert_at_line(frame.f_code, line)
    if node is not None:
        line = node.lineno
    sides = _sides(node, frame) if node is not None else None
    if sides is None:
        return None
    left, right, operator = sides
    at = _assignment(theorem, run)
    where = f"At {at}: " if at else ""
    relation = "" if operator == "==" else f" (it needs {operator})"
    return Failure(
        "false",
        line,
        "a step of its proof is false",
        (f"{where}the left side is {_number(left)}, the right side {_number(right)}{relation}.",),
        None,
    )


def _sides(node: ast.Assert, frame: Any) -> tuple[Any, Any, str] | None:
    """The two sides of the first comparison of an ``assert`` that fails, evaluated in ``frame``."""
    test = node.test
    if not isinstance(test, ast.Compare):
        return None
    scope = {**frame.f_globals, **frame.f_locals}
    path = frame.f_code.co_filename

    def value(expression: ast.expr) -> Any:
        from lanky.terms import evaluate, exact_reading, free_names

        code = compile(ast.Expression(expression), path, "eval")
        found = eval(code, scope)  # noqa: S307 - the user's own step, read again where it failed
        if hasattr(found, "mapper_method") and not free_names(found):
            # a term of numbers alone, as a helper hands one back: its value
            with exact_reading():
                found = evaluate(found, {})
        return found

    operators = {
        ast.Eq: ("==", lambda a, b: a == b),
        ast.NotEq: ("!=", lambda a, b: a != b),
        ast.Lt: ("<", lambda a, b: a < b),
        ast.LtE: ("<=", lambda a, b: a <= b),
        ast.Gt: (">", lambda a, b: a > b),
        ast.GtE: (">=", lambda a, b: a >= b),
    }
    try:
        left = value(test.left)
        for op, comparator in zip(test.ops, test.comparators, strict=True):
            right = value(comparator)
            said, compare = operators.get(type(op), (None, None))
            if compare is None:
                return None
            if compare(left, right) is not True:
                if not (_exact_number(left) and _exact_number(right)):
                    return None
                return left, right, said
            left = right
    except Exception:  # noqa: BLE001 - a side that cannot be read again leaves no report
        return None
    return None


def _point_failure(theorem: Any, run: _Run) -> Any:
    """The report of a point of the conclusion's domain where the conclusion is false."""
    from lanky.proofs.report import Failure
    from lanky.terms import render

    at = _assignment(theorem, run)
    line = run.point.line or run.loop_line
    said = render(run.statement_at(run.point.depth))
    if run.point.values is None:
        # a proof with no loop over its domain: the goal where it ends
        cells = [
            f"{name}[{', '.join(_number(index) for index in key)}] = {_number(value)}"
            for name, _sort in theorem.variables
            for key, value in sorted(getattr(run.context.get(name), "cells", {}).items())[:5]
            if 0 < len(getattr(run.context.get(name), "cells", {})) <= 4 and _exact_number(value)
        ]
        shown = ", ".join(part for part in (at, ", ".join(cells)) if part)
        where = f"At {shown}" if shown else "At a draw of its variables"
        return Failure(
            "false",
            line,
            "its conclusion is false where its proof ends",
            (f"{where}: the conclusion, {said}, is false.",),
            None,
        )
    return Failure(
        "false",
        line,
        "its conclusion is false at a point its proof reaches",
        (f"At {at}: the conclusion there, {said}, is false.",),
        None,
    )


# }}}
