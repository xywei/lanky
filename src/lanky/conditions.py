"""Named conditions: ``@condition``, and the theorems of a ``with`` block holding under one.

The design idea. Engineers give the conditions their results share a name:
the CFL condition, a segment that does not pass through zero, a conforming
mesh. lanky lets them write it once::

    @condition
    def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
        \"\"\"A source segment alpha + tau * beta that does not pass through zero.\"\"\"


    with segment as (alpha, beta, nonzero):

        @theorem
        def line_taylor(a: Fn[Nat, Complex], first_term: alpha * a[1] == beta, ...) -> ...:
            ...

A condition is written like a theorem with no conclusion and no body: typed
variables and named conditions, and a docstring. It has two uses, as one
object:

- *As a hypothesis.* Called on values it says whether the condition holds:
  ``segment(alpha=2, beta=1)`` is ``True``, and in an annotation, where the
  values are symbolic, the call is the proposition itself, so that
  ``stable: cfl(c, dt, h)`` is a hypothesis like any other.
- *As a setting.* ``with segment as (alpha, beta, nonzero):`` binds the
  condition's variables and named conditions, in its signature's order and
  under its names, and every theorem defined in the block holds under it: its
  statement is the condition's variables and conditions, then its own. A
  ``with`` block makes no new scope in Python, so the theorems keep their
  module-level names and are cited by them.

How it works. :meth:`Condition.__enter__` reads the names the ``with``
statement binds off its bytecode, refuses a count or a name other than the
signature's, and sets a context variable that :class:`lanky.theory.Theorem`
reads when it is decorated (:func:`in_force`); :meth:`Condition.__exit__`
clears it. The names are bound to what lanky reads them as, a variable's
:class:`~lanky.terms.Var` and a named condition's proposition, and each value
is remembered (:func:`bound_by`), so that a theorem defined after the block
that still uses one is refused, with the block to put it in.
"""

from __future__ import annotations

import dis
import inspect
import os
import sys
from collections.abc import Iterable, Mapping, Sequence
from contextvars import ContextVar, Token
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

from lanky.terms import LogicalAnd, Var, evaluate, evaluate_annotations, render, truth_value

__all__ = ["Condition", "Under", "bound_by", "condition", "in_force", "under_label"]


@dataclass(frozen=True)
class Under:
    """One condition in force: the condition, and what its ``with`` statement bound.

    Attributes:
        condition: The :class:`Condition`.
        values: ``(name, value)`` for each variable and named condition, in the
            signature's order: a variable's :class:`~lanky.terms.Var` and a
            condition's proposition, the values the ``with`` statement bound.
    """

    condition: Condition
    values: tuple[tuple[str, Any], ...]

    @property
    def names(self) -> tuple[str, ...]:
        """The names the ``with`` statement bound, in the signature's order."""
        return tuple(name for name, _ in self.values)


#: The conditions in force where a theorem is decorated, outermost first.
_IN_FORCE: ContextVar[tuple[Under, ...]] = ContextVar("lanky_conditions", default=())

#: Every value a ``with`` statement has bound, by its id: the value (kept
#: alive, so that the id stays its own), its condition and its name.
_BOUND: dict[int, tuple[Any, Condition, str]] = {}


def in_force() -> tuple[Under, ...]:
    """The conditions whose ``with`` blocks are running here, outermost first."""
    return _IN_FORCE.get()


def bound_by(value: Any) -> tuple[Condition, str] | None:
    """The condition and the name a ``with`` statement bound ``value`` to, or ``None``.

    Asked of a module-level name a theorem reads: after its block, ``alpha``
    still holds what ``with segment as (alpha, beta, nonzero)`` bound it to,
    and a theorem that uses it outside the block is refused.
    """
    entry = _BOUND.get(id(value))
    if entry is None or entry[0] is not value:
        return None
    return entry[1], entry[2]


def under_label(under: Sequence[Under]) -> str:
    """``segment (nonzero), cfl (stable)``: the conditions, each with its named conditions."""
    return ", ".join(entry.condition.label for entry in under)


class Condition:
    """A named condition, read off a typed Python function with no conclusion and no body.

    Attributes:
        variables: ``(name, sort)`` pairs, in signature order.
        hypotheses: ``(name, proposition)`` pairs: the named conditions.
        snapshot: What the annotations reach, copied when they were read, as
            a theorem's (:func:`lanky.faithful.capture`), which the
            faithfulness check of a theorem under the condition runs the
            condition's annotations again in.

    Raises:
        TypeError: If the function has a return annotation (a statement with
            a conclusion is a ``@theorem``), a body, a parameter that is not
            a plain name (``*args``, a default), a parameter annotated with a
            builtin of Python's, or no parameter at all; or if it is defined
            inside a ``with`` block of another condition.
    """

    def __init__(self, fn: Any) -> None:
        import functools

        from lanky.faithful import capture
        from lanky.theory import _refuse_a_builtin_annotation

        self.fn = fn
        functools.update_wrapper(self, fn)
        code = fn.__code__
        self.path = code.co_filename
        self.line = code.co_firstlineno
        self.where = f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        at = f"{self.qualname} at {self.where}"
        outer = in_force()
        if outer:
            raise TypeError(
                f"{at}: a condition is defined outside every with block, and this one is "
                f"inside with {outer[-1].condition.__name__}; to name the two together, "
                f"give {self.__name__} both sets of variables and conditions"
            )
        for parameter in inspect.signature(fn).parameters.values():
            plain = parameter.kind in (
                inspect.Parameter.POSITIONAL_ONLY,
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
                inspect.Parameter.KEYWORD_ONLY,
            )
            if not plain or parameter.default is not inspect.Parameter.empty:
                raise TypeError(
                    f"{at}: a condition's parameters are its variables and its named "
                    f"conditions, each a plain name with an annotation; {parameter} is not"
                )
        from lanky.proofs.trace import written_lines

        self.snapshot = capture(fn)
        annotations = evaluate_annotations(fn)
        if "return" in annotations:
            raise TypeError(
                f"{at}: a condition has no conclusion, only variables and named "
                f"conditions; a statement with a conclusion is a @theorem, or a theorem "
                f"under {self.__name__}, inside with {self.__name__} as (...):"
            )
        if written_lines(fn) is not None:
            raise TypeError(
                f"{at}: a condition has no body, since its signature says all of it; "
                "write its docstring alone under the signature"
            )
        missing = [
            name for name in inspect.signature(fn).parameters if name not in annotations
        ]
        if missing:
            raise TypeError(
                f"{at}: {missing[0]} has no annotation; a condition's parameter is a "
                "variable, annotated with its sort, or a named condition, annotated with "
                "the proposition"
            )
        variables: list[tuple[str, Any]] = []
        hypotheses: list[tuple[str, Any]] = []
        for name, annotation in annotations.items():
            _refuse_a_builtin_annotation(fn, name, annotation)
            if isinstance(annotation, prim.ExpressionNode | bool):
                hypotheses.append((name, annotation))
            else:
                variables.append((name, annotation))
        if not variables and not hypotheses:
            raise TypeError(
                f"{at}: a condition names variables and conditions on them; this one "
                "has no parameter"
            )
        self.variables = tuple(variables)
        self.hypotheses = tuple(hypotheses)
        self._tokens: list[Token] = []

    # {{{ what it says

    @property
    def names(self) -> tuple[str, ...]:
        """The variables and the named conditions, in the signature's order."""
        return tuple(inspect.signature(self.fn).parameters)

    @property
    def label(self) -> str:
        """``segment (nonzero)``: the name, and its named conditions after it."""
        conditions = ", ".join(name for name, _ in self.hypotheses)
        return f"{self.__name__} ({conditions})" if conditions else self.__name__

    @property
    def signature(self) -> str:
        """``segment(alpha: Complex, beta: Complex, nonzero: alpha != 0)``, as written."""
        try:
            raw = inspect.get_annotations(self.fn, eval_str=False)
        except Exception:  # noqa: BLE001 - the names alone, then
            raw = {}
        parts = []
        for name in self.names:
            annotation = raw.get(name)
            if annotation is None:
                parts.append(name)
            elif isinstance(annotation, str):
                parts.append(f"{name}: {' '.join(annotation.split())}")
            elif isinstance(annotation, prim.ExpressionNode):
                parts.append(f"{name}: {render(annotation)}")
            else:
                parts.append(f"{name}: {getattr(annotation, '__name__', annotation)}")
        return f"{self.__name__}({', '.join(parts)})"

    @property
    def term(self) -> Any:
        """The named conditions as one proposition, over the condition's variables."""
        return _conjunction([prop for _, prop in self.hypotheses])

    def __repr__(self) -> str:
        """``<condition segment(alpha: Complex, beta: Complex, nonzero: alpha != 0)>``."""
        return f"<condition {self.signature}>"

    # }}}

    # {{{ as a hypothesis

    def __call__(self, *values: Any, **named: Any) -> Any:
        """Whether the condition holds at these values; at symbolic ones, the proposition.

        The values are the variables', by position or by name, as
        ``cfl(c, dt, h)`` or ``cfl(c=1, dt=0.1, h=0.2)``. At concrete values
        the answer is a ``bool``: every named condition holds there. Where a
        value is symbolic, as in an annotation, ``stable: cfl(c, dt, h)``,
        the answer is the named conditions with the values put in for the
        variables, one proposition, which is how a theorem's hypothesis
        reads it. While the faithfulness check runs an annotation again at
        drawn values, the condition's own annotations are run again too, so
        that the check reaches what they say (:mod:`lanky.faithful`).

        Raises:
            TypeError: If a variable has no value, or two, or a value is given
                for a named condition, which is what the call answers.
        """
        arguments = self._arguments(values, named)
        if any(_holds_term(value) for value in arguments.values()):
            from lanky.induction import substitute

            return _conjunction([substitute(prop, arguments) for _, prop in self.hypotheses])
        from lanky.terms import rerunning

        if rerunning():
            from lanky.faithful import rerun_condition

            return rerun_condition(self, arguments)
        from lanky.theory import _as_family

        sorts = dict(self.variables)
        context = {
            name: _as_family(value, sorts.get(name), name) for name, value in arguments.items()
        }
        for _name, prop in self.hypotheses:
            if not truth_value(evaluate(prop, context), prop):
                return False
        return True

    def _arguments(self, values: tuple, named: Mapping[str, Any]) -> dict[str, Any]:
        """The value of each variable, from a call by position or by name."""
        names = [name for name, _ in self.variables]
        conditions = [name for name, _ in self.hypotheses]
        listing = ", ".join(names) or "none"
        if len(values) > len(names):
            raise TypeError(
                f"{self.__name__} takes the values of its variables, {listing}, and is "
                f"given {len(values) + len(named)}; it answers whether "
                f"{', '.join(conditions) or 'its conditions'} hold there"
            )
        given = dict(zip(names, values, strict=False))
        for name, value in named.items():
            if name in conditions:
                raise TypeError(
                    f"{name} is a condition of {self.__name__}, which the call answers; "
                    f"give {self.__name__} the values of its variables, {listing}"
                )
            if name not in names:
                raise TypeError(
                    f"{self.__name__} has no variable {name}: its variables are {listing}"
                )
            if name in given:
                raise TypeError(
                    f"{self.__name__} is given {name} twice, by its place and by its name"
                )
            given[name] = value
        missing = [name for name in names if name not in given]
        if missing:
            raise TypeError(f"{self.__name__} needs values for {', '.join(missing)}")
        return given

    # }}}

    # {{{ as a setting

    def __enter__(self) -> tuple[Any, ...]:
        """Put the condition in force, and bind its variables and named conditions.

        The names the ``with`` statement binds are read off its bytecode
        (:func:`_targets`), so that a count or a name other than the
        signature's is refused here, with the signature, rather than left
        to Python's unpacking, which would bind ``b`` to what ``beta`` means.

        Raises:
            TypeError: If the names are not the signature's, in its order; if
                the condition is in force here already; or if one of its names
                is another condition's in force, other than a variable both
                declare with one sort.
        """
        names = self.names
        line = f"with {self.__name__} as ({', '.join(names)}):"
        targets = _targets(sys._getframe(1))
        if targets is not None and targets != list(names):
            raise TypeError(self._wrong_targets(targets, line))
        outer = in_force()
        if any(entry.condition is self for entry in outer):
            raise TypeError(
                f"{line} is inside a with block of {self.__name__} already; a theorem "
                f"inside it holds under {self.__name__} once"
            )
        values: list[tuple[str, Any]] = []
        sorts = dict(self.variables)
        props = dict(self.hypotheses)
        for name in names:
            for entry in outer:
                if name not in entry.names:
                    continue
                other = entry.condition
                theirs = dict(other.variables).get(name)
                if name in sorts and theirs is not None and str(theirs) == str(sorts[name]):
                    continue  # one variable both conditions are about
                raise TypeError(
                    f"{line} binds {name}, which with {other.__name__} binds already, "
                    f"as {other.signature} names it; give one of the two another name"
                )
            value = Var(name) if name in sorts else props[name]
            _BOUND[id(value)] = (value, self, name)
            values.append((name, value))
        self._tokens.append(_IN_FORCE.set((*outer, Under(self, tuple(values)))))
        return tuple(value for _, value in values)

    def __exit__(self, *exc: object) -> bool:
        """Take the condition out of force; whatever the block raised goes on."""
        if self._tokens:
            _IN_FORCE.reset(self._tokens.pop())
        return False

    def _wrong_targets(self, targets: list[str] | str, line: str) -> str:
        """Why the names a ``with`` statement binds are refused, with the line to write."""
        names = self.names
        count = len(names)
        what = f"{count} variable{'s' if count != 1 else ''} and conditions"
        if isinstance(targets, str):
            written = (
                f"with {self.__name__}:" if targets == "" else f"with {self.__name__} as {targets}:"
            )
            return (
                f"{written} binds {'nothing' if targets == '' else 'one name'}, and "
                f"{self.__name__} has {what}, {self.signature}; write {line}"
            )
        written = f"with {self.__name__} as ({', '.join(targets)}):"
        if len(targets) != count:
            return (
                f"{written} binds {len(targets)} name{'s' if len(targets) != 1 else ''}, "
                f"and {self.__name__} has {what}, {self.signature}; write {line}"
            )
        renamed = [
            f"{target} for {name}"
            for target, name in zip(targets, names, strict=True)
            if target != name
        ]
        return (
            f"{written} names them otherwise than {self.signature} does "
            f"({', '.join(renamed)}): a theorem under {self.__name__} reads its variables "
            f"and conditions by their names; write {line}"
        )

    # }}}


def condition(fn: Any = None, /) -> Any:
    """Read a typed function with no conclusion and no body as a :class:`Condition`.

    Parameters annotated with sorts are the condition's variables, and
    parameters annotated with propositions are its named conditions::

        @condition
        def cfl(c: Real, dt: Real, h: Real, positive: h > 0, stable: c * dt <= h):
            \"\"\"The CFL condition of an explicit scheme for u_t + c u_x = 0.\"\"\"

    ``cfl(c=1, dt=0.1, h=0.2)`` is then ``True``, ``stable: cfl(c, dt, h)``
    is a hypothesis of any theorem, and the theorems written under ``with
    cfl as (c, dt, h, positive, stable):`` hold under it.

    Raises:
        TypeError: For anything :class:`Condition` refuses, and for an
            argument that is not a function: ``@condition`` takes none.
    """
    if fn is None:
        return condition
    if not callable(fn) or isinstance(fn, Condition) or not hasattr(fn, "__code__"):
        raise TypeError(f"@condition decorates a typed function, and {fn!r} is not one")
    return Condition(fn)


def _conjunction(props: Sequence[Any]) -> Any:
    """One proposition: ``True`` for none, the proposition for one, their conjunction else."""
    if not props:
        return True
    if len(props) == 1:
        return props[0]
    return LogicalAnd(tuple(props))


def _holds_term(value: Any) -> bool:
    """Whether ``value`` is a term, or a container that holds one."""
    if isinstance(value, prim.ExpressionNode):
        return True
    if isinstance(value, tuple | list):
        return any(_holds_term(item) for item in value)
    return False


#: The instructions that store the name a ``with`` statement binds.
_STORES = frozenset({"STORE_NAME", "STORE_GLOBAL", "STORE_FAST", "STORE_DEREF"})


def _targets(frame: Any) -> list[str] | str | None:
    """The names the ``with`` statement running in ``frame`` binds; ``None`` where unreadable.

    ``with segment as (alpha, beta, nonzero):`` is ``["alpha", "beta",
    "nonzero"]``; ``with segment as s:`` is ``"s"`` and ``with segment:``
    is ``""``. The frame is stopped at the instruction that calls
    ``__enter__`` (``BEFORE_WITH`` on Python 3.12 and 3.13, a ``CALL`` after
    them), and the instructions after it store what it returns: an
    ``UNPACK_SEQUENCE`` and a store per name, a single store, or a
    ``POP_TOP``. A target of another shape, ``(a, *rest)`` or ``obj.x``, is
    ``None`` and left to Python, which unpacks it as it says.
    """
    if frame is None:
        return None
    try:
        listing = [
            instruction
            for instruction in dis.get_instructions(frame.f_code)
            if instruction.opname not in ("CACHE", "EXTENDED_ARG")
        ]
    except Exception:  # noqa: BLE001 - no bytecode to read, and Python unpacks as it does
        return None
    position = next(
        (index for index, instruction in enumerate(listing) if instruction.offset == frame.f_lasti),
        None,
    )
    if position is None or position + 1 >= len(listing):
        return None
    following = listing[position + 1 :]
    first = following[0]
    if first.opname == "POP_TOP":
        return ""
    if first.opname in _STORES:
        return str(first.argval)
    if first.opname != "UNPACK_SEQUENCE":
        return None
    count = int(first.arg)
    names = _stored_names(following[1:], count)
    return names if names is not None and len(names) == count else None


def _stored_names(instructions: Iterable[Any], count: int) -> list[str] | None:
    """The names the next ``count`` stores store, superinstructions included; ``None`` else."""
    names: list[str] = []
    for instruction in instructions:
        if len(names) >= count:
            break
        opname = instruction.opname
        if opname in _STORES:
            names.append(str(instruction.argval))
        elif opname == "STORE_FAST_STORE_FAST":
            names.extend(str(name) for name in instruction.argval)
        elif opname == "STORE_FAST_LOAD_FAST":
            names.append(str(instruction.argval[0]))
        else:
            return None
    return names[:count] if len(names) >= count else None
