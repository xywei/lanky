"""Named conditions, and ``with``: the claims of a block hold under what it assumes.

The design idea. Engineers give the conditions their results share a name:
the CFL condition, an expansion point away from zero, a conforming mesh.
lanky lets them write it once::

    @condition
    def away_from_zero(alpha: Complex, beta: Complex, nonzero: alpha != 0):
        \"\"\"The expansion point alpha is not zero.\"\"\"


    with away_from_zero as (alpha, beta, nonzero):

        @claim
        def line_taylor(a: Fn[Nat, Complex], first_term: alpha * a[1] == beta, ...) -> ...:
            ...

A condition is written like a claim with no goal and no body: typed
variables and named conditions, and a docstring. It has two uses, as one
object:

- *As a hypothesis.* Called on values it says whether the condition holds:
  ``away_from_zero(alpha=2, beta=1)`` is ``True``, and in an annotation, where
  the values are symbolic, the call is the proposition itself, so that
  ``ok: cfl(c, dt, h)`` is a hypothesis like any other, which brings the
  variables' sorts with it and reads in the ledger as it is written.
- *As a setting.* ``with away_from_zero as (alpha, beta, nonzero):`` binds the
  condition's variables and named conditions, in its signature's order and
  under its names, and every claim defined in the block holds under it: its
  statement is the condition's variables and conditions, then its own. A
  ``with`` block makes no new scope in Python, so the claims keep their
  module-level names and are cited by them.

A ``with`` statement can assume two more things, written the same way
(:class:`Assuming`): another claim's conditions, ``with
line_taylor.conditions as (a, first_term, ode):``, and a whole claim, ``with
line_taylor as (a, first_term, ode):``, whose goal then holds in the block too,
cited by the claim's name. A claim built on a whole claim rests on it, so that
its row reads ``under line_taylor`` until line_taylor is proved, and nothing
built on an unproved claim passes for proved.

How it works. :meth:`Assuming.__enter__` reads the names the ``with``
statement binds off its bytecode, refuses a count or a name other than the
signature's, and sets a context variable that :class:`lanky.theory.Claim`
reads when it is decorated (:func:`in_force`); :meth:`Assuming.__exit__`
clears it. The names are bound to what lanky reads them as, a variable's
:class:`~lanky.terms.Var` and a named condition's proposition, and each
module-level binding is remembered (:func:`bound_by`), so that a claim
defined after the block that still uses one is refused, with the block to put
it in.

A condition is a fact of the ledger too (:meth:`Condition.fact`): its row is
the check that its conditions can hold at all, by draws, and is never
``proved``, since a condition is assumed and not claimed. A claim the draws
refute is tested against the file's conditions (:func:`suggested_conditions`),
and one that excludes every failing draw is named, with the ``with`` line to
write.
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

__all__ = [
    "Assuming",
    "Condition",
    "ConditionNotMet",
    "Conditions",
    "Under",
    "anything_bound",
    "bound_by",
    "condition",
    "in_force",
    "suggested_conditions",
    "under_label",
    "with_clause",
    "with_line",
]


class ConditionNotMet(ValueError):
    """A claim called at values where one of its conditions fails: the question does not apply.

    Attributes:
        claim: The name of the claim called.
        condition: The name of the condition that fails.
    """

    def __init__(self, message: str, claim: str, condition: str) -> None:
        super().__init__(message)
        self.claim = claim
        self.condition = condition


@dataclass(frozen=True)
class Under:
    """One thing in force: what a ``with`` statement assumed, and what it bound.

    Attributes:
        condition: What is assumed (:class:`Assuming`): a :class:`Condition`,
            a claim's :class:`Conditions`, or a whole claim.
        values: ``(name, value)`` for each name the ``with`` statement bound,
            in the signature's order: a variable's :class:`~lanky.terms.Var`
            and a condition's proposition.
    """

    condition: Any
    values: tuple[tuple[str, Any], ...]

    @property
    def names(self) -> tuple[str, ...]:
        """The names the ``with`` statement bound, in the signature's order."""
        return tuple(name for name, _ in self.values)

    @property
    def parts(self) -> tuple[str, ...]:
        """Every name it puts in the statement: the bound ones, and a whole claim's goal."""
        assumed = self.condition
        names = [name for name, _ in assumed.assumed_variables]
        names += [name for name, _ in assumed.assumed_hypotheses]
        return tuple(dict.fromkeys((*self.names, *names)))


#: What is in force where a claim is decorated, outermost first.
_IN_FORCE: ContextVar[tuple[Under, ...]] = ContextVar("lanky_conditions", default=())

#: Every name a ``with`` statement has bound at a module's top level, by the
#: module's namespace and the name: the namespace and the value (both kept,
#: so that their ids stay their own) and what it assumed. The binding, not the
#: value: a named condition can be a shared object (``True``, a proposition
#: another name holds too), and another name holding it is no name the block
#: bound.
_BOUND: dict[tuple[int, str], tuple[dict, Any, Any]] = {}


def in_force() -> tuple[Under, ...]:
    """What the ``with`` blocks running here assume, outermost first."""
    return _IN_FORCE.get()


def anything_bound() -> bool:
    """Whether any ``with`` statement of lanky's has bound a name in this process."""
    return bool(_BOUND)


def bound_by(namespace: Mapping[str, Any], name: str) -> tuple[Any, str] | None:
    """What a ``with`` statement assumed when it bound ``name`` in ``namespace``; or ``None``.

    Asked of a module-level name a claim reads: after its block, ``alpha``
    still holds what ``with away_from_zero as (alpha, beta, nonzero)`` bound
    it to, and a claim that uses it outside the block is refused. A name the
    module has bound to something else since is its own again.
    """
    entry = _BOUND.get((id(namespace), name))
    if entry is None or entry[0] is not namespace:
        return None
    if name not in namespace or namespace[name] is not entry[1]:
        return None
    return entry[2], name


def with_clause(assumed: Any) -> str:
    """``cfl as (nu, stable)``: what follows ``with``; the name alone where nothing is bound."""
    names = tuple(assumed.names)
    if not names:
        return assumed.__name__
    return f"{assumed.__name__} as ({', '.join(names)})"


def with_line(assumed: Any) -> str:
    """``with cfl as (nu, stable):``, the line that assumes ``assumed``."""
    return f"with {with_clause(assumed)}:"


def under_label(under: Sequence[Under]) -> str:
    """``away_from_zero (nonzero), cfl (stable)``: what is assumed, each with its conditions."""
    return ", ".join(entry.condition.label for entry in under)


def signature_text(fn: Any, names: Sequence[str], name: str) -> str:
    """``cfl(nu: Real, stable: (0 <= nu) & (nu <= 1))``: a signature as it is written."""
    try:
        raw = inspect.get_annotations(fn, eval_str=False)
    except Exception:  # noqa: BLE001 - the names alone, then
        raw = {}
    parts = []
    for parameter in names:
        annotation = raw.get(parameter)
        if annotation is None:
            parts.append(parameter)
        elif isinstance(annotation, str):
            parts.append(f"{parameter}: {' '.join(annotation.split())}")
        elif isinstance(annotation, prim.ExpressionNode):
            parts.append(f"{parameter}: {render(annotation)}")
        else:
            parts.append(f"{parameter}: {getattr(annotation, '__name__', annotation)}")
    return f"{name}({', '.join(parts)})"


# {{{ what a with statement assumes


class Assuming:
    """What a ``with`` statement can assume: a condition, a claim's conditions, a whole claim.

    Each gives its parts the same way, so that the three read alike in a
    claim's statement, in the ledger and in the refusals:

    - ``names``: what ``as`` binds, every name of its signature in order;
    - ``assumed_variables`` and ``assumed_hypotheses``: what it puts in the
      statement of each claim in the block, a whole claim's goal among the
      hypotheses, under the claim's name;
    - ``label``: how a statement names it after ``under``;
    - ``required``: what has to be in force already, the conditions a claim
      holds under itself;
    - ``rests_on``: the facts a claim in the block rests on for it, a whole
      claim's own;
    - ``source_fn``, ``snapshot``, ``annotation_keys`` and
      ``world_parameters``: what the faithfulness check runs again, and
      where (:mod:`lanky.faithful`).
    """

    #: What a refusal calls it: ``with cfl``, a condition, has ``variables and conditions``.
    what = "variables and conditions"

    @property
    def required(self) -> tuple[Any, ...]:
        """What has to be in force for a ``with`` statement of it: nothing, for a condition."""
        return ()

    @property
    def rests_on(self) -> tuple[str, ...]:
        """The fact ids a claim in its block rests on: none, but for a whole claim."""
        return ()

    @property
    def annotation_keys(self) -> dict[str, str]:
        """The annotation of the source each part is read from, by the part's name."""
        return {name: name for name in self.names}

    @property
    def world_parameters(self) -> tuple[str, ...]:
        """The names the faithfulness check binds at drawn values where its annotations run."""
        return tuple(self.names)

    def _token_stack(self) -> list[Token]:
        stack = self.__dict__.get("_with_tokens")
        if stack is None:
            stack = self.__dict__["_with_tokens"] = []
        return stack

    def __enter__(self) -> tuple[Any, ...]:
        """Put it in force, and bind its variables and named conditions.

        The names the ``with`` statement binds are read off its bytecode
        (:func:`_targets`), so that a count or a name other than the
        signature's is refused here, with the signature, rather than left
        to Python's unpacking, which would bind ``b`` to what ``beta`` means.

        Raises:
            TypeError: If the names are not the signature's, in its order; if
                it is in force here already; if what it requires is not (a
                claim's conditions, or a whole claim, under conditions of its
                own); or if one of its names is another's in force, other than
                a variable both declare with one sort.
        """
        names = self.names
        line = with_line(self)
        frame = sys._getframe(1)
        targets = _targets(frame)
        # ``as (n)`` is ``as n``, one store: the one name, given bare. With no
        # names, ``with item:`` binds nothing, as it should.
        bare = len(names) == 1 and targets == names[0]
        nothing = not names and targets == ""
        if targets is not None and not bare and not nothing and targets != list(names):
            raise TypeError(self._wrong_targets(targets, line))
        outer = in_force()
        if any(entry.condition is self for entry in outer):
            raise TypeError(
                f"{line} is inside a with block of {self.__name__} already; a claim "
                f"inside it holds under {self.__name__} once"
            )
        missing = [
            needed
            for needed in self.required
            if not any(entry.condition is needed for entry in outer)
        ]
        if missing:
            raise TypeError(self._not_in_force(missing, line))
        values: list[tuple[str, Any]] = []
        sorts = dict(self.assumed_variables)
        props = dict(self.assumed_hypotheses)
        for name in names:
            for entry in outer:
                if name not in entry.parts:
                    continue
                other = entry.condition
                theirs = dict(other.assumed_variables).get(name)
                if name in sorts and theirs is not None and str(theirs) == str(sorts[name]):
                    continue  # one variable both are about
                raise TypeError(
                    f"{line} binds {name}, which with {other.__name__} binds already, "
                    f"as {other.signature} names it; give one of the two another name"
                )
            value = Var(name) if name in sorts else props[name]
            values.append((name, value))
        if frame.f_locals is frame.f_globals:
            # a module's top level, where a claim after the block could read them
            for name, value in values:
                _BOUND[(id(frame.f_globals), name)] = (frame.f_globals, value, self)
        self._token_stack().append(_IN_FORCE.set((*outer, Under(self, tuple(values)))))
        if bare:
            return values[0][1]
        return tuple(value for _, value in values)

    def __exit__(self, *exc: object) -> bool:
        """Take it out of force; whatever the block raised goes on."""
        stack = self._token_stack()
        if stack:
            _IN_FORCE.reset(stack.pop())
        return False

    def _not_in_force(self, missing: Sequence[Any], line: str) -> str:
        """Why a claim's conditions, or a whole claim, are refused outside its own conditions."""
        owner = getattr(self, "claim", self)
        held = ", ".join(needed.__name__ for needed in missing)
        lines = [with_clause(needed) for needed in (*missing, self)]
        return (
            f"{line} assumes {owner.__name__}, which holds under {held}, and {held} is "
            f"not in force here; write with {', '.join(lines)}:"
        )

    def _wrong_targets(self, targets: list[str] | str, line: str) -> str:
        """Why the names a ``with`` statement binds are refused, with the line to write."""
        names = self.names
        count = len(names)
        what = f"{count} {self.what}"
        if isinstance(targets, str) and targets and count == 1:
            targets = [targets]  # one name for one: a name other than the signature's
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
            f"({', '.join(renamed)}): a claim under {self.__name__} reads its variables "
            f"and conditions by their names; write {line}"
        )


# }}}


# {{{ a condition


class Condition(Assuming):
    """A named condition, read off a typed Python function with no goal and no body.

    Attributes:
        variables: ``(name, sort)`` pairs, in signature order.
        hypotheses: ``(name, proposition)`` pairs: the named conditions.
        snapshot: What the annotations reach, copied when they were read, as
            a claim's (:func:`lanky.faithful.capture`), which the
            faithfulness check of a claim under the condition runs the
            condition's annotations again in.

    Raises:
        TypeError: If the function has a return annotation (a statement with
            a goal is a ``@claim``), a body, a parameter that is not a plain
            name (``*args``, a default), a parameter annotated with a builtin
            of Python's, or no parameter at all; or if it is defined inside a
            ``with`` block.
    """

    #: What the ledger calls its fact, and the first word of its id.
    noun = "condition"

    def __init__(self, fn: Any) -> None:
        import functools

        from lanky.faithful import capture
        from lanky.theory import _module_of, _refuse_a_builtin_annotation

        self.fn = fn
        functools.update_wrapper(self, fn)
        self._names = tuple(inspect.signature(fn).parameters)
        code = fn.__code__
        self.path = code.co_filename
        self.line = code.co_firstlineno
        self.where = f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        self.module = _module_of(fn)
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
                f"{at}: a condition has no goal, only variables and named conditions; a "
                f"statement with a goal is a @claim, or a claim under {self.__name__}, "
                f"inside with {self.__name__} as (...):"
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

    # {{{ what it says

    @property
    def names(self) -> tuple[str, ...]:
        """The variables and the named conditions, in the signature's order."""
        return tuple(inspect.signature(self.fn).parameters)

    @property
    def assumed_variables(self) -> tuple[tuple[str, Any], ...]:
        """What a ``with`` block of it puts in each claim's statement: its variables."""
        return self.variables

    @property
    def assumed_hypotheses(self) -> tuple[tuple[str, Any], ...]:
        """And its named conditions."""
        return self.hypotheses

    @property
    def source_fn(self) -> Any:
        """The function its annotations are read from."""
        return self.fn

    @property
    def label(self) -> str:
        """``away_from_zero (nonzero)``: the name, and its named conditions after it."""
        conditions = ", ".join(name for name, _ in self.hypotheses)
        return f"{self.__name__} ({conditions})" if conditions else self.__name__

    @property
    def signature(self) -> str:
        """``away_from_zero(alpha: Complex, beta: Complex, nonzero: alpha != 0)``, as written."""
        return signature_text(self.fn, self.names, self.__name__)

    @property
    def term(self) -> Any:
        """The named conditions as one proposition, over the condition's variables."""
        return _conjunction([prop for _, prop in self.hypotheses])

    def __repr__(self) -> str:
        """``<condition away_from_zero(alpha: Complex, beta: Complex, nonzero: alpha != 0)>``."""
        return f"<condition {self.signature}>"

    def __getattr__(self, name: str) -> Any:
        """Refuse ``cfl.nu``: a condition's names are bound by ``with``, not read off it."""
        if not name.startswith("_") and name in self.__dict__.get("_names", ()):
            raise AttributeError(_attribute_refusal(self, name))
        raise AttributeError(f"{type(self).__name__!r} object has no attribute {name!r}")

    # }}}

    # {{{ as a fact

    @property
    def fact_id(self) -> str:
        """``condition:upwind.cfl@31``: the id of its row, keyed as a claim's is."""
        from lanky.ledger import fact_id

        return fact_id(self.noun, self.qualname, module=self.module, line=self.line)

    def fact(self) -> Any:
        """The condition's row: whether its conditions can hold at all, never ``proved``.

        Its term is ``True`` under the condition's variables and conditions,
        and only the oracles that draw are asked about it
        (:func:`lanky.check.establish`): a pass says the draws found values
        where the conditions hold, and where none did, the stronger oracles
        are asked whether they are inconsistent, as for any claim's
        hypotheses, and a condition that can never hold is ``vacuous`` and
        fails the check. A condition is assumed, not claimed, so nothing
        proves it.
        """
        from lanky.ledger import Fact, Status
        from lanky.terms import Forall

        binders = tuple((Var(name), sort) for name, sort in self.variables)
        props = [prop for _, prop in self.hypotheses]
        guard = props[0] if len(props) == 1 else (LogicalAnd(tuple(props)) if props else None)
        variables = ", ".join(f"{name} : {sort}" for name, sort in self.variables)
        hypotheses = [[name, render(prop)] for name, prop in self.hypotheses]
        said = " | ".join(
            part
            for part in (variables, ", ".join(text for _, text in hypotheses))
            if part
        )
        return Fact(
            id=self.fact_id,
            kind=self.noun,
            statement=f"can hold: {said}",
            term=Forall(binders, True, guard),
            status=Status.ASSUMED,
            decided_by=None,
            provenance={
                "path": self.path,
                "line": self.line,
                "sequent": {
                    "head": "can hold",
                    "variables": variables,
                    "hypotheses": hypotheses,
                    "goal": "",
                },
                "hypothesis_names": [name for name, _ in self.hypotheses],
            },
            where=self.where,
            owner=self.qualname,
        )

    # }}}

    # {{{ as a hypothesis

    def __call__(self, *values: Any, **named: Any) -> Any:
        """Whether the condition holds at these values; at symbolic ones, the proposition.

        The values are the variables', by position or by name, as
        ``cfl(c, dt, h)`` or ``cfl(c=1, dt=0.1, h=0.2)``. At concrete values
        the answer is a ``bool``: every named condition holds there. Where a
        value is symbolic, as in an annotation, ``ok: cfl(c, dt, h)``, the
        answer is the named conditions with the values put in for the
        variables, one proposition, which is how a claim's hypothesis
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
        return _holds_everywhere(self.variables, self.hypotheses, arguments)

    def _arguments(self, values: tuple, named: Mapping[str, Any]) -> dict[str, Any]:
        """The value of each variable, from a call by position or by name."""
        return _call_arguments(self.__name__, self.variables, self.hypotheses, values, named)

    # }}}


def _attribute_refusal(assumed: Any, name: str) -> str:
    """Why ``cfl.nu`` names nothing, and where ``nu`` comes from instead."""
    line = with_line(assumed)
    return (
        f"{assumed.__name__}.{name} names nothing: {name} is bound by {line}, and a claim "
        f"outside the block ranges over {name} in its own for, or takes it as a parameter"
    )


def _call_arguments(
    called: str,
    variables: Sequence[tuple[str, Any]],
    hypotheses: Sequence[tuple[str, Any]],
    values: tuple,
    named: Mapping[str, Any],
    filled: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """The value of each variable, from a call by position or by name.

    ``filled`` holds the values a ``with`` block gives already, which the call
    leaves out: its positional values are the rest, in order.
    """
    filled = dict(filled or {})
    names = [name for name, _ in variables if name not in filled]
    conditions = [name for name, _ in hypotheses]
    listing = ", ".join(names) or "none"
    if len(values) > len(names):
        raise TypeError(
            f"{called} takes the values of its variables, {listing}, and is given "
            f"{len(values) + len(named)}; it answers whether "
            f"{', '.join(conditions) or 'its conditions'} hold there"
        )
    given = dict(zip(names, values, strict=False))
    for name, value in named.items():
        if name in conditions:
            raise TypeError(
                f"{name} is a condition of {called}, which the call answers; give "
                f"{called} the values of its variables, {listing}"
            )
        if name in filled:
            raise TypeError(
                f"{name} is the with block's here, and {called} takes it from there; give "
                f"{called} its own variables, {listing}"
            )
        if name not in names:
            raise TypeError(f"{called} has no variable {name}: its variables are {listing}")
        if name in given:
            raise TypeError(f"{called} is given {name} twice, by its place and by its name")
        given[name] = value
    missing = [name for name in names if name not in given]
    if missing:
        raise TypeError(f"{called} needs values for {', '.join(missing)}")
    return {**filled, **given}


def _holds_everywhere(
    variables: Sequence[tuple[str, Any]],
    hypotheses: Sequence[tuple[str, Any]],
    arguments: Mapping[str, Any],
) -> bool:
    """Whether every named condition holds at concrete ``arguments``."""
    from lanky.theory import _as_family

    sorts = dict(variables)
    context = {name: _as_family(value, sorts.get(name), name) for name, value in arguments.items()}
    for _name, prop in hypotheses:
        if not truth_value(evaluate(prop, context), prop):
            return False
    return True


def condition(fn: Any = None, /) -> Any:
    """Read a typed function with no goal and no body as a :class:`Condition`, and register it.

    Parameters annotated with sorts are the condition's variables, and
    parameters annotated with propositions are its named conditions::

        @condition
        def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
            \"\"\"The CFL condition: the Courant number is between 0 and 1.\"\"\"

    ``cfl(nu=0.5)`` is then ``True``, ``ok: cfl(nu)`` is a hypothesis of any
    claim, and the claims written under ``with cfl as (nu, stable):`` hold
    under it. ``lanky check`` gives it a row of its own, the check that its
    conditions can hold (:meth:`Condition.fact`).

    Raises:
        TypeError: For anything :class:`Condition` refuses, and for an
            argument that is not a function: ``@condition`` takes none.
    """
    if fn is None:
        return condition
    if not callable(fn) or isinstance(fn, Assuming) or not hasattr(fn, "__code__"):
        raise TypeError(f"@condition decorates a typed function, and {fn!r} is not one")
    from lanky.plugins import registry

    return registry.register_object(Condition(fn))


# }}}


# {{{ a claim's conditions


class Conditions(Assuming):
    """A claim's conditions, ``line_taylor.conditions``: its variables and named conditions.

    The half of a claim before its goal, as one object. ``with
    line_taylor.conditions as (a, first_term, ode):`` assumes them for the
    claims of the block, which then hold under line_taylor's conditions and
    not under its goal; ``line_taylor.conditions.ode`` is one of them, the
    proposition as line_taylor states it; and ``line_taylor.conditions(a=...)``
    says whether they hold at values, as a condition does.
    """

    def __init__(self, claim: Any) -> None:
        self.__dict__["claim"] = claim
        self.__dict__["__name__"] = f"{claim.__name__}.conditions"

    @property
    def names(self) -> tuple[str, ...]:
        """The claim's parameters, in its signature's order."""
        return tuple(inspect.signature(self.claim.fn).parameters)

    @property
    def assumed_variables(self) -> tuple[tuple[str, Any], ...]:
        """The claim's own variables."""
        return tuple(self.claim.own_variables)

    @property
    def assumed_hypotheses(self) -> tuple[tuple[str, Any], ...]:
        """The claim's own named conditions."""
        return tuple(self.claim.own_hypotheses)

    #: Read as a condition's are.
    variables = assumed_variables
    hypotheses = assumed_hypotheses

    @property
    def required(self) -> tuple[Any, ...]:
        """What the claim holds under itself, which has to be in force for its conditions."""
        return tuple(self.claim.held_under)

    @property
    def source_fn(self) -> Any:
        """The claim's function, whose annotations are read again."""
        return self.claim.fn

    @property
    def snapshot(self) -> Any:
        """The claim's snapshot."""
        return self.claim.snapshot

    @property
    def world_parameters(self) -> tuple[str, ...]:
        """The claim's parameters and what its own ``with`` blocks bound."""
        return (*self.names, *self.claim.bound)

    @property
    def label(self) -> str:
        """``line_taylor.conditions (first_term, ode)``."""
        conditions = ", ".join(name for name, _ in self.assumed_hypotheses)
        return f"{self.__name__} ({conditions})" if conditions else self.__name__

    @property
    def signature(self) -> str:
        """``line_taylor.conditions(a: Fn[Nat, Complex], first_term: ..., ode: ...)``."""
        return signature_text(self.claim.fn, self.names, self.__name__)

    @property
    def term(self) -> Any:
        """The named conditions as one proposition."""
        return _conjunction([prop for _, prop in self.assumed_hypotheses])

    def __getattr__(self, name: str) -> Any:
        """``line_taylor.conditions.ode``: one condition, the proposition as the claim states it.

        Only the claim's own: a condition of what the claim holds under is
        that one's, and is named as such. Inside a proof that ``lanky
        check`` runs, the run in progress answers: in the claim's own proof
        it is the fact ``ode`` names there, which ``by(...)`` cites, and in
        another claim's proof it is refused, since that claim's proof is
        what assumes it.
        """
        if name.startswith("_"):
            raise AttributeError(name)
        claim = self.claim
        own = dict(self.assumed_hypotheses)
        if name in own:
            from lanky.proofs.trace import active

            run = active()
            if run is not None:
                return run.condition(claim, name, sys._getframe(1))
            return own[name]
        listing = ", ".join(own) or "none"
        if name in dict(self.assumed_variables):
            raise AttributeError(
                f"{name} is a variable of {claim.__name__}, not one of its conditions, "
                f"which are {listing}"
            )
        held = next((entry.condition for entry in claim.under if name in entry.parts), None)
        if held is not None:
            raise AttributeError(
                f"{name} is a condition of {held.__name__}, which {claim.__name__} holds "
                f"under; the conditions of {claim.__name__} itself are {listing}"
            )
        raise AttributeError(
            f"{claim.__name__} has no condition {name}: its conditions are {listing}"
        )

    def __setattr__(self, name: str, value: Any) -> None:
        """Refuse: a claim's conditions are what its signature says."""
        if name.startswith("_"):
            self.__dict__[name] = value
            return
        raise AttributeError(f"{self.__name__} are read off the claim's signature")

    @property
    def fn(self) -> Any:
        """The claim's function, whose annotations state its conditions."""
        return self.claim.fn

    def __call__(self, *values: Any, **named: Any) -> Any:
        """Whether the claim's own conditions hold at these values; at symbolic ones, them.

        While the faithfulness check runs an annotation that calls them again
        at drawn values, the claim's own annotations of them are run again
        too, as a condition's are (:func:`lanky.faithful.rerun_condition`),
        so that the check reaches what they say; for a claim under a ``with``
        block, whose annotations read the block's names, they are answered
        from the term.
        """
        arguments = _call_arguments(
            self.__name__, self.assumed_variables, self.assumed_hypotheses, values, named
        )
        if any(_holds_term(value) for value in arguments.values()):
            from lanky.induction import substitute

            return _conjunction(
                [substitute(prop, arguments) for _, prop in self.assumed_hypotheses]
            )
        from lanky.terms import rerunning

        if rerunning() and not self.claim.bound:
            from lanky.faithful import rerun_condition

            return rerun_condition(self, arguments)
        return _holds_everywhere(self.assumed_variables, self.assumed_hypotheses, arguments)

    def __repr__(self) -> str:
        """``<line_taylor.conditions(a: ..., first_term: ..., ode: ...)>``."""
        return f"<{self.signature}>"


# }}}


# {{{ a condition for a refuted claim


def suggested_conditions(
    claim: Any, conditions: Iterable[Any], samples: int = 200, seed: int = 0
) -> list[str]:
    """The lines that name each condition of the file excluding every draw that refutes ``claim``.

    The claim's statement is drawn as the property tester draws it, with its
    goal's leading ``for`` variables drawn too, so that a condition on one of
    them is tested where the goal failed. A condition fits when its variables
    are among the drawn names, it is false at every failing draw, and it is
    true at a draw that passed, so that it leaves something to claim. Each
    fitting condition is named with the ``with`` line that puts the claim
    under it::

        The condition cfl in this file excludes every failing draw: put the claim
        under with cfl as (nu, stable).

    Nothing rests on it: the claim under the condition is checked again, as
    any claim is.
    """
    from lanky.terms import Forall, exact_reading
    from lanky.testing import valid_draws

    candidates = [found for found in conditions if isinstance(found, Condition)]
    already = {id(entry.condition) for entry in getattr(claim, "under", ())}
    candidates = [found for found in candidates if id(found) not in already]
    if not candidates:
        return []
    variables = list(claim.variables)
    hypotheses = [prop for _, prop in claim.hypotheses]
    body = claim.goal
    while isinstance(body, Forall):
        variables += [(var.name, domain) for var, domain in body.binders]
        if body.guard is not None:
            hypotheses.append(body.guard)
        body = body.body
    drawn = {name for name, _ in variables}
    candidates = [
        found
        for found in candidates
        if found.variables and all(name in drawn for name, _ in found.variables)
    ]
    if not candidates:
        return []
    failing: list[dict[str, Any]] = []
    passing: list[dict[str, Any]] = []
    try:
        with exact_reading():
            for context in valid_draws(variables, hypotheses, samples, seed):
                try:
                    holds = truth_value(evaluate(body, context), body)
                except Exception:  # noqa: BLE001 - a draw with no answer is neither
                    continue
                (passing if holds else failing).append(dict(context))
            if not failing:
                return []
            lines = []
            for found in candidates:
                at_failing = [_holds_at(found, draw) for draw in failing]
                at_passing = [_holds_at(found, draw) for draw in passing]
                if all(holds is False for holds in at_failing) and any(
                    holds is True for holds in at_passing
                ):
                    lines.append(
                        f"The condition {found.__name__} in this file excludes every failing "
                        f"draw: put the claim under with {with_clause(found)}."
                    )
    except Exception:  # noqa: BLE001 - a suggestion that cannot be made is not made
        return []
    return lines


def _holds_at(found: Condition, draw: Mapping[str, Any]) -> bool | None:
    """Whether ``found`` holds at a draw of a claim's names; ``None`` where it has no answer."""
    values = {name: draw[name] for name, _ in found.variables}
    try:
        return _holds_everywhere(found.variables, found.hypotheses, values)
    except Exception:  # noqa: BLE001 - a condition with no answer at a draw says nothing there
        return None


# }}}


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

    ``with away_from_zero as (alpha, beta, nonzero):`` is ``["alpha", "beta",
    "nonzero"]``; ``with away_from_zero as s:`` is ``"s"`` and ``with
    away_from_zero:`` is ``""``. The frame is stopped at the instruction that
    calls ``__enter__`` (``BEFORE_WITH`` on Python 3.12 and 3.13, a ``CALL``
    after them), and the instructions after it store what it returns: an
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
