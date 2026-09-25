"""Symbolic terms: pymbolic expressions that can also be propositions.

The design idea. lanky never parses Python. Annotations are Python expressions,
so lanky *evaluates* them in a scope whose unknown names become symbolic
variables (:class:`Scope`), and lets Python's own operator overloading build the
term. pymbolic is the shared expression language, so the terms lanky builds are
pymbolic expressions and a plugin such as loopty can lower them to loopy without
any translation step.

pymbolic on its own is not quite enough for propositions. ``a == b`` on a
pymbolic node is structural equality and answers a ``bool``, so an annotation
like ``off(0) == 0`` would collapse to ``False`` before lanky ever saw it. The
fix is small: every node lanky builds is an ordinary pymbolic node *subclass*
that overrides the comparison operators to build
:class:`pymbolic.primitives.Comparison` and the bitwise operators to build the
logical connectives. Mapper dispatch is inherited (a lanky :class:`Add` still
answers ``map_sum``), so every pymbolic mapper keeps working.

Four node types have no pymbolic counterpart and are added here:
:class:`Forall`, :class:`Exists`, :class:`Sum` (a reduction over a generator,
not addition) and :class:`Abs`.

Binders come from generators. ``all(p(r) for r in Fin[n])`` is an ordinary
generator expression; the builtin ``all`` is replaced by :func:`forall` while an
annotation is being evaluated, the index type's ``__iter__`` yields exactly one
fresh variable when its bound is symbolic, and the name of that variable is read
off the generator's code object so that the printed statement says ``r`` and not
``_i3``. A ``if`` clause in the generator records a guard: the truth value of a
symbolic proposition is undefined, so :meth:`PropositionMixin.__bool__` uses the
request as the signal that a guard was written, and raises outside binder
tracing.
"""

from __future__ import annotations

import builtins
import dataclasses
import dis
import functools
import inspect
import itertools
import sys
from collections.abc import Callable, Iterable, Iterator, Sequence
from contextlib import closing
from fractions import Fraction
from typing import Any, ClassVar

import pymbolic.primitives as prim
from pymbolic import expr_dataclass
from pymbolic.mapper.evaluator import EvaluationMapper as _PymbolicEvaluationMapper

__all__ = [
    "Abs",
    "Add",
    "BUILTIN_OVERRIDES",
    "Call",
    "Comparison",
    "Exists",
    "Forall",
    "LogicalAnd",
    "LogicalNot",
    "LogicalOr",
    "Scope",
    "Subscript",
    "Sum",
    "SymbolicBoolError",
    "Undecided",
    "Var",
    "binder_assignments",
    "binders",
    "conjuncts",
    "evaluate",
    "evaluate_annotations",
    "exists",
    "forall",
    "init_args",
    "free_variables",
    "render",
    "structurally_equal",
    "sum_",
    "truth_value",
]


class SymbolicBoolError(TypeError):
    """Raised when Python asks for the truth value of a symbolic proposition.

    A proposition is a term, not a ``bool``. It becomes a ``bool`` only when it
    is evaluated at concrete values (:func:`evaluate`). The one place where
    Python may ask is the ``if`` clause of a generator expression being traced
    for binders, where the question is answered by recording a guard.
    """


class Undecided(Exception):
    """Raised when evaluation cannot answer a term from the points it was given.

    The case that matters is an existential over a sampled domain. ``Fin[n]``
    is enumerated, so ``any(...)`` over it is decided either way; ``Nat`` is
    *sampled*, so a handful of draws that produce no witness say nothing at all
    about whether one exists. Answering ``False`` there would turn a true
    statement into a counterexample, so evaluation declines instead, and the
    property tester drops the draw rather than counting it as evidence.
    """


# {{{ operator-overloading mixins


def _make_binary(name: str) -> Callable[..., Any]:
    """Wrap one pymbolic arithmetic operator so that it answers a lanky node."""
    base = getattr(prim.ExpressionNode, f"__{name}__")

    def operation(self: Any, other: Any) -> Any:
        result = base(self, other)
        if result is NotImplemented:
            return NotImplemented
        return lift(result)

    operation.__name__ = f"__{name}__"
    operation.__qualname__ = f"SymbolicMixin.__{name}__"
    operation.__doc__ = f"Build the lanky counterpart of pymbolic's ``__{name}__``."
    return operation


def _make_unary(name: str) -> Callable[..., Any]:
    """Wrap one pymbolic unary operator so that it answers a lanky node."""
    base = getattr(prim.ExpressionNode, f"__{name}__")

    def operation(self: Any) -> Any:
        return lift(base(self))

    operation.__name__ = f"__{name}__"
    operation.__qualname__ = f"SymbolicMixin.__{name}__"
    operation.__doc__ = f"Build the lanky counterpart of pymbolic's ``__{name}__``."
    return operation


class SymbolicMixin:
    """Operator overloading shared by every lanky term.

    Arithmetic is pymbolic's, with the result re-tagged as the lanky subclass so
    that the next operator applied to it is lanky's again. Comparisons build
    :class:`Comparison` instead of answering ``bool``; ``&``, ``|`` and ``~``
    build the logical connectives rather than bitwise ones, because lanky terms
    are mathematics and not bit patterns.
    """

    def __hash__(self) -> int:
        """Hash as the underlying pymbolic node does."""
        return super().__hash__()  # type: ignore[misc]

    # {{{ comparisons build propositions

    def __eq__(self, other: Any) -> Comparison:  # type: ignore[override]
        """Build the proposition ``self == other``."""
        return Comparison(self, "==", other)

    def __ne__(self, other: Any) -> Comparison:  # type: ignore[override]
        """Build the proposition ``self != other``."""
        return Comparison(self, "!=", other)

    def __lt__(self, other: Any) -> Comparison:
        """Build the proposition ``self < other``."""
        return Comparison(self, "<", other)

    def __le__(self, other: Any) -> Comparison:
        """Build the proposition ``self <= other``."""
        return Comparison(self, "<=", other)

    def __gt__(self, other: Any) -> Comparison:
        """Build the proposition ``self > other``."""
        return Comparison(self, ">", other)

    def __ge__(self, other: Any) -> Comparison:
        """Build the proposition ``self >= other``."""
        return Comparison(self, ">=", other)

    # }}}

    # {{{ logical connectives

    def __and__(self, other: Any) -> LogicalAnd:
        """Build the conjunction ``self and other``."""
        return LogicalAnd((self, other))

    def __rand__(self, other: Any) -> LogicalAnd:
        """Build the conjunction ``other and self``."""
        return LogicalAnd((other, self))

    def __or__(self, other: Any) -> LogicalOr:
        """Build the disjunction ``self or other``."""
        return LogicalOr((self, other))

    def __ror__(self, other: Any) -> LogicalOr:
        """Build the disjunction ``other or self``."""
        return LogicalOr((other, self))

    def __invert__(self) -> LogicalNot:
        """Build the negation ``not self``."""
        return LogicalNot(self)

    # }}}

    def __call__(self, *args: Any) -> Call:
        """Build an application ``self(...)``, the way a family is indexed."""
        return Call(self, tuple(args))

    def __getitem__(self, index: Any) -> Subscript:
        """Build a subscript ``self[...]``."""
        return Subscript(self, index)


for _name in (
    "add", "radd", "sub", "rsub", "mul", "rmul",
    "truediv", "rtruediv", "floordiv", "rfloordiv",
    "mod", "rmod", "pow", "rpow",
):
    setattr(SymbolicMixin, f"__{_name}__", _make_binary(_name))

for _name in ("neg", "pos"):
    setattr(SymbolicMixin, f"__{_name}__", _make_unary(_name))

del _name


# {{{ where a truth value was asked for


#: What to say about each way of asking for the truth value of a proposition.
_MISUSE = {
    "boolop": (
        "the proposition {prop!r} was used as an operand of Python's ``and``, "
        "``or`` or ``not``, which short-circuits on a truth value and would "
        "silently drop part of what you wrote; build the connective instead: "
        "``&`` for and, ``|`` for or, ``~`` for not (mind the precedence: "
        "``(a < b) & (b < c)``)"
    ),
    "foreign": (
        "the truth value of {prop!r} was asked for outside the ``if`` clause of "
        "the generator being traced, most likely by an ``if`` or a ``while`` "
        "statement inside a function the annotation calls; a proposition becomes "
        "a bool only when it is evaluated at concrete values"
    ),
}


@functools.lru_cache(maxsize=64)
def _instructions(code: Any) -> tuple[tuple[Any, ...], dict[int, int]]:
    """The instructions of a code object, and an offset-to-index table."""
    listing = tuple(dis.get_instructions(code))
    return listing, {instruction.offset: index for index, instruction in enumerate(listing)}


def _asking_context(frame: Any, code: Any) -> str:
    """Classify the bytecode that asked for a truth value: guard, boolop, foreign.

    The one place Python may ask for the truth value of a proposition is the
    ``if`` clause of the generator expression being traced, and the answer is to
    record a guard. Two ways of getting there are mistakes, and both are worth
    catching because both are silent:

    ``and`` and ``or`` short-circuit. ``if a and b`` happens to survive, because
    CPython compiles a conjunction in a comprehension filter into two successive
    tests and both are recorded; ``if a or b`` does not, because answering the
    first test truthfully skips the second operand entirely and the disjunction
    is quietly narrowed to its left half. Used as a value rather than as a
    filter, as in a body ``a and b``, the left operand becomes a guard and only
    the right one is the body. The bytecode tells the cases apart: a boolean
    operator used as a value copies its operand before testing it (``COPY``),
    and the arms of a short-circuiting ``or`` jump to one shared target. Both
    shapes were read off CPython 3.12 and 3.13.

    An ``if`` or a ``while`` inside a function the annotation calls asks from
    another frame entirely, and whatever it records would be attached to the
    wrong generator.

    An unrecognized layout is read as a guard, which is what every earlier
    CPython did: the check may miss a mistake on an interpreter it does not
    know, but it never invents one.
    """
    if frame is None:
        return "guard"
    if code is not None and frame.f_code is not code:
        return "foreign"
    listing, index_of = _instructions(frame.f_code)
    position = index_of.get(frame.f_lasti)
    if position is None:
        return "guard"
    current = listing[position]
    previous = listing[position - 1] if position else None
    if current.opname.startswith("POP_JUMP_IF"):
        # 3.12: the jump itself converts the value it pops.
        jump_at = position
    else:
        # 3.13 and later: TO_BOOL, or a comparison the compiler told to answer
        # a bool, and the jump is the instruction after it.
        following = position + 1
        if following >= len(listing) or not listing[following].opname.startswith("POP_JUMP_IF"):
            return "guard"
        jump_at = following
    if previous is not None and previous.opname == "COPY":
        return "boolop"
    jump = listing[jump_at]
    for other_at in range(jump_at + 1, len(listing)):
        other = listing[other_at]
        if (
            other.opname == jump.opname
            and other.argval == jump.argval
            and _tests_a_value(listing, other_at)
        ):
            return "boolop"
    return "guard"


def _tests_a_value(listing: tuple[Any, ...], position: int) -> bool:
    """Whether the jump at ``position`` consumes a truth value of its own.

    Two jumps to one target are the arms of a short-circuiting ``or`` only when
    both of them are testing something; a jump the compiler emitted for control
    flow, such as the one that ends a loop body, is not.
    """
    if position == 0:
        return False
    return listing[position - 1].opname in (
        "TO_BOOL",
        "COMPARE_OP",
        "CONTAINS_OP",
        "IS_OP",
        "CALL",
        "LOAD_FAST",
        "LOAD_GLOBAL",
        "LOAD_DEREF",
    )


# }}}


class PropositionMixin(SymbolicMixin):
    """A term whose value is a truth value.

    Asking for ``bool`` of one is an error, except inside binder tracing, where
    the question can only come from the ``if`` clause of a generator expression
    and is answered by recording the proposition as a guard.
    """

    def __bool__(self) -> bool:
        """Record a guard while tracing binders; otherwise refuse."""
        trace = current_trace()
        if trace is None:
            raise SymbolicBoolError(
                f"the truth value of the symbolic proposition {render(self)!r} is "
                "undefined; evaluate it at concrete values (Theorem.__call__, "
                "Theorem.test) or keep it symbolic"
            )
        context = _asking_context(sys._getframe(1), trace.code)
        if context != "guard":
            raise SymbolicBoolError(_MISUSE[context].format(prop=render(self)))
        trace.add_guard(self)
        return True


# }}}


# {{{ node types


class Var(SymbolicMixin, prim.Variable):
    """A symbolic variable: a :class:`pymbolic.primitives.Variable` that compares."""


class Add(SymbolicMixin, prim.Sum):
    """Addition. Named ``Add`` because :class:`Sum` here is the reduction."""


class Product(SymbolicMixin, prim.Product):
    """Multiplication."""


class Quotient(SymbolicMixin, prim.Quotient):
    """True division."""


class FloorDiv(SymbolicMixin, prim.FloorDiv):
    """Floor division."""


class Remainder(SymbolicMixin, prim.Remainder):
    """Remainder."""


class Power(SymbolicMixin, prim.Power):
    """Exponentiation."""


class Call(SymbolicMixin, prim.Call):
    """Application of a family to arguments, as in ``off(r)``."""


class Subscript(SymbolicMixin, prim.Subscript):
    """Subscript of an array-like term, as in ``x[i]``."""


class Comparison(PropositionMixin, prim.Comparison):
    """A comparison proposition, as in ``off(0) == 0``."""


class LogicalAnd(PropositionMixin, prim.LogicalAnd):
    """Conjunction."""


class LogicalOr(PropositionMixin, prim.LogicalOr):
    """Disjunction."""


class LogicalNot(PropositionMixin, prim.LogicalNot):
    """Negation."""


@expr_dataclass(eq=False)
class Forall(PropositionMixin, prim.ExpressionNode):
    """Universal quantification over index-type binders.

    ``binders`` are ``(variable, domain)`` pairs, outermost first, exactly as
    written in the generator expression. ``guard`` is the generator's ``if``
    clause when there is one, and restricts the domain rather than weakening the
    body, which is what a decision procedure wants to see.
    """

    binders: tuple[tuple[Var, Any], ...]
    body: Any
    guard: Any = None



@expr_dataclass(eq=False)
class Exists(PropositionMixin, prim.ExpressionNode):
    """Existential quantification, with the same shape as :class:`Forall`."""

    binders: tuple[tuple[Var, Any], ...]
    body: Any
    guard: Any = None



@expr_dataclass(eq=False)
class Sum(SymbolicMixin, prim.ExpressionNode):
    """A reduction over binders: the value of ``lanky.sum(body for i in dom)``.

    This is not pymbolic's ``Sum`` (which is addition, and is :class:`Add`
    here). A plugin lowers this node through ``registry.term_lowerings``; that
    is how loopty turns it into a loopy reduction.
    """

    binders: tuple[tuple[Var, Any], ...]
    body: Any
    guard: Any = None

    mapper_method: ClassVar[str] = "map_lanky_sum"


@expr_dataclass(eq=False)
class Abs(SymbolicMixin, prim.ExpressionNode):
    """Absolute value."""

    operand: Any



#: Plain pymbolic node types and the lanky subclass that replaces them.
_COUNTERPART: dict[type, type] = {
    prim.Variable: Var,
    prim.Sum: Add,
    prim.Product: Product,
    prim.Quotient: Quotient,
    prim.FloorDiv: FloorDiv,
    prim.Remainder: Remainder,
    prim.Power: Power,
    prim.Call: Call,
    prim.Subscript: Subscript,
    prim.Comparison: Comparison,
    prim.LogicalAnd: LogicalAnd,
    prim.LogicalOr: LogicalOr,
    prim.LogicalNot: LogicalNot,
}


def init_args(expr: Any) -> tuple[Any, ...]:
    """The constructor arguments of a pymbolic node, in order.

    Every node is a dataclass, so its fields are its constructor arguments.
    """
    if dataclasses.is_dataclass(expr):
        return tuple(getattr(expr, field.name) for field in dataclasses.fields(expr))
    return tuple(expr.__getinitargs__())


def lift(expr: Any) -> Any:
    """Re-tag a plain pymbolic node as its lanky counterpart, shallowly.

    Children are left alone: they were built by lanky operators already, or they
    are constants.
    """
    counterpart = _COUNTERPART.get(type(expr))
    if counterpart is None:
        return expr
    return counterpart(*init_args(expr))


# }}}


# {{{ binder tracing


_FRESH = itertools.count()


class _Trace:
    """One binder-tracing context: the binders and guards of one generator."""

    def __init__(self, names: Sequence[str] = (), code: Any = None) -> None:
        self.names = list(names)
        #: The code object being traced, so that a truth value asked for from
        #: another frame can be told from the generator's own ``if`` clause.
        self.code = code
        self.binders: list[tuple[Var, Any]] = []
        self.guards: list[Any] = []

    def bind(self, domain: Any) -> Var:
        """Invent the bound variable for ``domain`` and record the binder."""
        if len(self.binders) < len(self.names):
            name = self.names[len(self.binders)]
        else:
            name = f"_i{next(_FRESH)}"
        var = Var(name)
        self.binders.append((var, domain))
        return var

    def add_guard(self, prop: Any) -> None:
        """Record a generator ``if`` clause."""
        self.guards.append(prop)

    def guard(self) -> Any:
        """Combine the recorded guards into one proposition, or ``None``."""
        if not self.guards:
            return None
        if len(self.guards) == 1:
            return self.guards[0]
        return LogicalAnd(tuple(self.guards))


_TRACE_STACK: list[_Trace] = []


def current_trace() -> _Trace | None:
    """The innermost binder trace, or ``None`` outside tracing.

    Index types call this from ``__iter__`` to decide whether to yield one
    generic point or to enumerate concretely.
    """
    return _TRACE_STACK[-1] if _TRACE_STACK else None


class _Driven:
    """The outcome of running a generator once under binder tracing."""

    def __init__(self, trace: _Trace, values: list[Any]) -> None:
        self.binders = tuple(trace.binders)
        self.guard = trace.guard()
        self.values = values

    @property
    def body(self) -> Any:
        """The single symbolic value the generator yielded."""
        if not self.values and self.guard is not None:
            # The generic point was filtered out, and the only way that can
            # happen is a guard whose sense was inverted after lanky answered
            # it: capturing a guard answers ``True``, so ``not`` turns the one
            # point into none. The connective, not Python's keyword, is the fix.
            raise SymbolicBoolError(
                "the guard of this generator was written with Python's ``not``, "
                "which inverts the answer lanky gives while capturing the guard "
                "and leaves the quantifier empty; write ``~(...)`` instead "
                f"(the guard captured was {render(self.guard)!r})"
            )
        if len(self.values) != 1:
            raise ValueError(
                "a generator over a symbolic index type must yield exactly one "
                f"generic point, got {len(self.values)}; mixing concrete and "
                "symbolic domains in one comprehension is not supported"
            )
        return self.values[0]


def _binder_names(gen: Any) -> Sequence[str]:
    """Read the loop-target names off a generator expression's code object.

    The names are what makes a printed statement readable: ``forall r in
    Fin(n)`` rather than ``forall _i7 in Fin(n)``. They are taken from the
    bytecode, in the order the targets are stored, because the obvious source
    is wrong in a case that matters: a target a nested comprehension closes
    over is a cell variable rather than a local, so ``co_varnames`` has only
    ``.0`` in it for the outer generator of ``all(all(p(i, j) for j in ...) for
    i in ...)``. Reading the stores keeps that ``i``, and keeps the order.

    An unrecognized shape (a tuple target, say) gives no name, and the binder
    falls back to a fresh one, which is correct and merely less readable.
    """
    code = getattr(gen, "gi_code", None)
    if code is None:
        return ()
    names: list[str] = []
    storing = False
    for instruction in dis.get_instructions(code):
        if instruction.opname == "FOR_ITER":
            storing = True
        elif storing:
            if instruction.opname.startswith(("STORE_FAST", "STORE_DEREF", "STORE_NAME")):
                # CPython fuses a store with the next load or store into one
                # superinstruction, whose argument is then a tuple; the target
                # of the loop is the first of them.
                argument = instruction.argval
                names.append(str(argument[0] if isinstance(argument, tuple) else argument))
            storing = False
    if names:
        return names
    return [n for n in code.co_varnames[1:] if not n.startswith(".")]


def _drive(gen: Iterable[Any]) -> _Driven:
    """Run ``gen`` to exhaustion once with binder tracing active."""
    trace = _Trace(_binder_names(gen), getattr(gen, "gi_code", None))
    _TRACE_STACK.append(trace)
    try:
        values = list(gen)
    finally:
        _TRACE_STACK.pop()
    return _Driven(trace, values)


def binders(gen: Iterable[Any]) -> tuple[tuple[Var, Any], ...]:
    """Return the ``(variable, index type)`` pairs bound by ``gen``.

    The generator is consumed. In symbolic mode each index type yields exactly
    one fresh variable, so one pair per ``for`` clause comes back.
    """
    return _drive(gen).binders


def forall(gen: Iterable[Any]) -> Any:
    """Universal quantification; the replacement for the builtin ``all``.

    Symbolic domains give a :class:`Forall` term, concrete ones the plain
    ``bool`` that ``all`` would have answered.
    """
    driven = _drive(gen)
    if not driven.binders:
        return builtins.all(driven.values)
    return Forall(driven.binders, driven.body, driven.guard)


def exists(gen: Iterable[Any]) -> Any:
    """Existential quantification; the replacement for the builtin ``any``."""
    driven = _drive(gen)
    if not driven.binders:
        return builtins.any(driven.values)
    return Exists(driven.binders, driven.body, driven.guard)


def sum_(gen: Iterable[Any]) -> Any:
    """Reduction; the replacement for the builtin ``sum``, exported as ``lanky.sum``.

    Over a symbolic domain this is a :class:`Sum` term whose reduced domain is
    known; over a concrete one it is the ordinary Python (or numpy) sum, so the
    same source runs under plain ``python``.
    """
    driven = _drive(gen)
    if not driven.binders:
        return builtins.sum(driven.values)
    return Sum(driven.binders, driven.body, driven.guard)


def abs_(value: Any) -> Any:
    """Absolute value; the replacement for the builtin ``abs``."""
    if isinstance(value, prim.ExpressionNode):
        return Abs(value)
    return builtins.abs(value)


#: The builtins that mean something else inside an annotation.
BUILTIN_OVERRIDES: dict[str, Any] = {
    "all": forall,
    "any": exists,
    "sum": sum_,
    "abs": abs_,
}


# }}}


# {{{ scope and annotation evaluation


class Scope(dict):
    """A mapping in which every unknown name is a symbolic variable.

    This is the whole of lanky's "parser": used as the globals of ``eval``, it
    lets Python itself read an annotation such as ``Fn[Fin[n], Nat]`` in which
    ``n`` has no value anywhere. Dunder names still raise :exc:`KeyError`, so
    the interpreter's own bookkeeping (``__builtins__``) is undisturbed.
    """

    def __missing__(self, name: str) -> Any:
        """Invent a variable for ``name``, remembering it for later lookups."""
        if name.startswith("__") and name.endswith("__"):
            raise KeyError(name)
        var = Var(name)
        self[name] = var
        return var


def evaluate_annotations(fn: Any, values: dict[str, Any] | None = None) -> dict[str, Any]:
    """Evaluate every annotation of ``fn`` as an expression.

    Annotations are strings under ``from __future__ import annotations`` and
    objects otherwise; both are handled, the strings by evaluating them here in
    a :class:`Scope` seeded with the function's globals, the parameters as
    variable proxies, and the builtins that quantify (``all``, ``any``, ``sum``,
    ``abs``). The result is keyed by parameter name, in signature order, with
    the return annotation last under the key ``"return"``.

    ``values`` overrides the proxies, which is how the same annotation is reused
    as a predicate over concrete values.
    """
    raw = inspect.get_annotations(fn, eval_str=False)
    scope = Scope(getattr(fn, "__globals__", {}))
    scope.update(BUILTIN_OVERRIDES)
    for name in inspect.signature(fn).parameters:
        scope[name] = Var(name)
    if values:
        scope.update(values)

    out: dict[str, Any] = {}
    for name, annotation in raw.items():
        out[name] = eval(annotation, scope, None) if isinstance(annotation, str) else annotation
    return out


# }}}


# {{{ evaluation at concrete values


def truth_value(value: Any, prop: Any) -> bool:
    """``value`` as the truth value of ``prop``, refusing what is not one.

    A statement is a proposition, so what it evaluates to at a draw has to be a
    truth value. ``bool()`` takes anything: ``def t(n: Nat) -> n + 1`` claims
    nothing, and Lean declines it because its goal has type ``Nat``, but
    Python's truthiness made every draw of it a pass and the malformed claim
    was reported ``TESTED``. A hypothesis was read the same way, and so was
    every operand of a connective and every body of a quantifier, so
    ``(n + 1) | (n > 5)`` passed as well. A numpy boolean, which a comparison
    of numpy values answers, is a truth value; a number, a table or ``None``
    is not.

    Raises:
        TypeError: If ``value`` is not a Boolean. The property-test oracle
            reports that as a test that could not run, so the fact stays
            ``ASSUMED`` with the reason in its provenance.
    """
    if isinstance(value, bool):
        return value
    # numpy is a dependency but nothing else here needs it, so it is imported
    # only on the way to refusing a value
    import numpy

    if isinstance(value, numpy.bool_):
        return bool(value)
    raise TypeError(
        f"{render(prop)} is not a proposition: it evaluates to {value!r}, which "
        f"is a {type(value).__name__} and not a truth value"
    )


class LankyEvaluationMapper(_PymbolicEvaluationMapper):
    """Evaluate a lanky term at concrete values.

    Quantifiers and reductions need their binder domains enumerated. An index
    type says how (``points(evaluate)``); anything else, a sort such as ``Nat``
    with no finite extent, is handed to ``sampler``, which is how the property
    tester tests a statement about all naturals.

    The two kinds of domain are not equally informative, and the difference is
    the whole reason :class:`Undecided` exists. An enumerated domain is the
    domain, so both quantifiers are decided over it. A sampled domain is a
    handful of points out of infinitely many, and only one of the two answers
    survives that: a ``forall`` that fails at a drawn point really is false
    there, but an ``exists`` that finds no witness among four draws has learned
    nothing, so it declines rather than answering ``False``.

    Wherever a proposition's truth is read, in a connective, a guard or the
    body of a quantifier, the value has to be a truth value
    (:func:`truth_value`). pymbolic's own connectives apply Python's
    truthiness, which reads a number as a proposition.
    """

    def __init__(
        self,
        context: dict[str, Any],
        sampler: Callable[[Any], Iterable[Any]] | None = None,
    ) -> None:
        super().__init__(context)
        self.context: dict[str, Any] = context
        self.sampler = sampler

    @staticmethod
    def is_exhaustive(domain: Any) -> bool:
        """Whether walking this domain visits every one of its points.

        An index type with a bound answers ``points``, so its extent is the
        whole domain; anything else is sampled.
        """
        return getattr(domain, "points", None) is not None

    def _points(self, domain: Any) -> Iterable[Any]:
        """The concrete points of one binder domain."""
        points = getattr(domain, "points", None)
        if points is not None:
            return points(self.rec)
        if self.sampler is not None:
            return self.sampler(domain)
        raise ValueError(f"cannot enumerate the binder domain {domain!r}")

    def assignments(self, binder_list: Sequence[tuple[Var, Any]]) -> Iterator[None]:
        """Bind every binder in turn, yielding once per assignment.

        The restoration is in a ``finally`` because every consumer here
        short-circuits: a ``forall`` stops at a counterexample and an
        ``exists`` at a witness, and a walk that ends at the first ``yield``
        never reaches code placed after the loop. A binder that shadows an
        outer one of the same name would then leave the inner point behind,
        and the rest of the enclosing statement would be evaluated at it: the
        inner ``i`` of ``all(any(i == 0 for i in Fin[1]) & (i < 2) for i in
        Fin[3])`` would answer the outer ``i < 2`` and turn a false statement
        into a pass.
        """
        if not binder_list:
            yield None
            return
        (var, domain), rest = binder_list[0], binder_list[1:]
        saved = self.context.get(var.name, _UNSET)
        try:
            for point in self._points(domain):
                self.context[var.name] = point
                yield from self.assignments(rest)
        finally:
            if saved is _UNSET:
                self.context.pop(var.name, None)
            else:
                self.context[var.name] = saved

    def _holds(self, expr: Any) -> bool:
        """Whether a guard holds under the current assignment."""
        return expr is None or self._truth(expr)

    def _truth(self, expr: Any) -> bool:
        """Evaluate a proposition, refusing a value that is not a truth value."""
        return truth_value(self.rec(expr), expr)

    def map_logical_and(self, expr: prim.LogicalAnd) -> bool:
        """Every operand, left to right, stopping at the first false one."""
        return all(self._truth(child) for child in expr.children)

    def map_logical_or(self, expr: prim.LogicalOr) -> bool:
        """Some operand, left to right, stopping at the first true one."""
        return any(self._truth(child) for child in expr.children)

    def map_logical_not(self, expr: prim.LogicalNot) -> bool:
        """The negation of the operand."""
        return not self._truth(expr.child)

    def map_forall(self, expr: Forall) -> Any:
        """True when the body holds at every point of the guarded domain.

        Over a sampled domain a ``True`` is evidence rather than proof, which is
        exactly what the ``TESTED`` status means; a ``False`` is a real
        counterexample either way, so nothing here has to be held back.

        The walk is closed explicitly on the way out. Leaving it to the
        collector would work in CPython and rest on refcounting for something
        that has to hold: until the walk is closed its ``finally`` has not run,
        and the binding this quantifier replaced is still the inner point.
        """
        with closing(self.assignments(expr.binders)) as walk:
            for _ in walk:
                if self._holds(expr.guard) and not self._truth(expr.body):
                    return False
        return True

    def map_exists(self, expr: Exists) -> Any:
        """True when the body holds somewhere in the guarded domain.

        Raises:
            Undecided: If no witness turned up and at least one binder domain
                was sampled rather than enumerated, so "no witness among these
                points" is not "no witness".
        """
        with closing(self.assignments(expr.binders)) as walk:
            for _ in walk:
                if self._holds(expr.guard) and self._truth(expr.body):
                    return True
        sampled = [
            domain for _var, domain in expr.binders if not self.is_exhaustive(domain)
        ]
        if sampled:
            names = ", ".join(str(domain) for domain in sampled)
            raise Undecided(
                f"no witness was drawn for {render(expr)}, and {names} is "
                "sampled rather than enumerated, so the statement is undecided "
                "here rather than false"
            )
        return False

    def map_lanky_sum(self, expr: Sum) -> Any:
        """Add the body over the guarded domain.

        A reduction visits every point, so nothing short-circuits here; the
        walk is still closed explicitly, because an exception raised in the
        body leaves the loop the same way a witness does.
        """
        total: Any = 0
        with closing(self.assignments(expr.binders)) as walk:
            for _ in walk:
                if self._holds(expr.guard):
                    total = total + self.rec(expr.body)
        return total

    def map_abs(self, expr: Abs) -> Any:
        """Absolute value of the operand."""
        return builtins.abs(self.rec(expr.operand))


class _Unset:
    """Sentinel for "this name had no value before the binder bound it"."""


_UNSET = _Unset()


def binder_assignments(
    binder_list: Sequence[tuple[Var, Any]],
    context: dict[str, Any],
    sampler: Callable[[Any], Iterable[Any]] | None = None,
) -> Iterator[None]:
    """Yield once per assignment of ``binder_list``, binding them in ``context``.

    The context is mutated in place and restored afterwards, including when the
    walk is abandoned part way: the restoration is in a ``finally``, so closing
    the iterator puts back the bindings it replaced. A caller that breaks out
    of the loop should close it (``contextlib.closing``) rather than leave that
    to the collector. This is what a sampler uses to walk a quantified
    hypothesis point by point.
    """
    yield from LankyEvaluationMapper(context, sampler).assignments(list(binder_list))


def evaluate(
    expr: Any,
    context: dict[str, Any] | None = None,
    sampler: Callable[[Any], Iterable[Any]] | None = None,
) -> Any:
    """Evaluate ``expr`` at the values in ``context``.

    A proposition evaluates to a ``bool``, which is what makes an annotation
    double as a property test.

    Raises:
        Undecided: If an existential over a domain ``sampler`` supplied found no
            witness. Sampled points are not the domain, so there is no ``False``
            to return, and the caller drops the draw instead.
        TypeError: If an operand of a connective, a guard or the body of a
            quantifier is not a truth value (:func:`truth_value`). What the
            whole of ``expr`` evaluates to is the caller's to judge.
    """
    if not isinstance(expr, prim.ExpressionNode):
        return expr
    return LankyEvaluationMapper(dict(context or {}), sampler)(expr)


# }}}


# {{{ structural comparison and printing


def structurally_equal(left: Any, right: Any) -> bool:
    """Compare two terms as syntax trees.

    ``==`` builds a proposition, so tests and caches need this instead.
    """
    if isinstance(left, prim.ExpressionNode) or isinstance(right, prim.ExpressionNode):
        if not (
            isinstance(left, prim.ExpressionNode) and isinstance(right, prim.ExpressionNode)
        ):
            return False
        if left.mapper_method != right.mapper_method:
            return False
        return structurally_equal(init_args(left), init_args(right))
    if isinstance(left, tuple) and isinstance(right, tuple):
        return len(left) == len(right) and all(
            structurally_equal(a, b) for a, b in zip(left, right, strict=True)
        )
    return bool(left == right)


def conjuncts(prop: Any) -> tuple[Any, ...]:
    """Split a proposition into its top-level conjuncts.

    A guard built from several hypotheses is one ``and``; a tester wants them
    back as a list, because each is a separate filter.
    """
    if prop is None:
        return ()
    if isinstance(prop, prim.LogicalAnd):
        out: tuple[Any, ...] = ()
        for child in prop.children:
            out += conjuncts(child)
        return out
    return (prop,)


def free_variables(expr: Any) -> frozenset[str]:
    """The names a term mentions that no binder of the term binds."""
    if isinstance(expr, Var):
        return frozenset({expr.name})
    if isinstance(expr, Forall | Exists | Sum):
        bound = {var.name for var, _ in expr.binders}
        inner = free_variables(expr.body) | free_variables(expr.guard)
        domains: frozenset[str] = frozenset()
        for _, domain in expr.binders:
            domains |= free_variables(getattr(domain, "bound", None))
        return (inner - bound) | domains
    if isinstance(expr, prim.ExpressionNode):
        out: frozenset[str] = frozenset()
        for arg in init_args(expr):
            out |= free_variables(arg)
        return out
    if isinstance(expr, tuple | list):
        out = frozenset()
        for item in expr:
            out |= free_variables(item)
        return out
    return frozenset()


_OR, _AND, _NOT, _CMP, _ADD, _MUL, _POW, _ATOM = range(8)


def _parens(text: str, inner: int, outer: int) -> str:
    """Parenthesize when an inner operator binds more loosely than its context."""
    return f"({text})" if inner < outer else text


def _binders_text(expr: Forall | Exists | Sum) -> str:
    """Render ``i in Fin(n), j in Fin(m)`` for a quantifier or reduction."""
    return ", ".join(f"{var.name} in {domain}" for var, domain in expr.binders)


def _signed(child: Any) -> tuple[bool, str]:
    """Split a summand into a sign and its text, so that ``a + (-1)*b`` prints as ``a - b``.

    Subtraction is not a pymbolic node: ``a - b`` is a sum with a negated
    summand, and printing it as written is what makes a statement readable.
    """
    if isinstance(child, prim.Product) and child.children:
        first = child.children[0]
        if isinstance(first, int) and first == -1:
            rest = child.children[1:]
            if len(rest) == 1:
                return True, _render(rest[0], _MUL)
            return True, _render(Product(rest), _MUL)
    if isinstance(child, int | float | Fraction) and child < 0:
        return True, _render(-child, _MUL)
    return False, _render(child, _ADD)


def _sum_text(children: Sequence[Any]) -> str:
    """Render the summands of a sum, with subtraction where a summand is negated."""
    parts = []
    for position, child in enumerate(children):
        negated, text = _signed(child)
        if position == 0:
            parts.append(f"-{text}" if negated else text)
        else:
            parts.append(f"{' - ' if negated else ' + '}{text}")
    return "".join(parts)


def _render(expr: Any, outer: int) -> str:
    """Render ``expr``, parenthesized for a context of precedence ``outer``."""
    if isinstance(expr, Var | prim.Variable):
        return expr.name
    if isinstance(expr, Forall | Exists):
        universal = isinstance(expr, Forall)
        if not expr.binders:
            # A closed statement with hypotheses and no variables. There is
            # nothing to quantify, so it reads as the sequent it is rather than
            # as "forall nothing".
            if expr.guard is None:
                return _render(expr.body, outer)
            joiner = " |- " if universal else " and "
            text = f"{_render(expr.guard, _OR + 1)}{joiner}{_render(expr.body, _OR + 1)}"
            return _parens(text, _OR, outer)
        word = "forall" if universal else "exists"
        guard = f" where {_render(expr.guard, _OR)}" if expr.guard is not None else ""
        text = f"{word} {_binders_text(expr)}{guard}. {_render(expr.body, _OR)}"
        return _parens(text, _OR, outer)
    if isinstance(expr, Sum):
        guard = f" if {_render(expr.guard, _OR)}" if expr.guard is not None else ""
        return f"sum({_render(expr.body, _OR)} for {_binders_text(expr)}{guard})"
    if isinstance(expr, Abs):
        return f"abs({_render(expr.operand, _OR)})"
    if isinstance(expr, prim.Comparison):
        text = (
            f"{_render(expr.left, _ADD)} {expr.operator} {_render(expr.right, _ADD)}"
        )
        return _parens(text, _CMP, outer)
    if isinstance(expr, prim.LogicalAnd | prim.LogicalOr):
        joiner, level = (
            (" and ", _AND) if isinstance(expr, prim.LogicalAnd) else (" or ", _OR)
        )
        text = joiner.join(_render(child, level + 1) for child in expr.children)
        return _parens(text, level, outer)
    if isinstance(expr, prim.LogicalNot):
        return _parens(f"not {_render(expr.child, _CMP + 1)}", _NOT, outer)
    if isinstance(expr, prim.Sum):
        return _parens(_sum_text(expr.children), _ADD, outer)
    if isinstance(expr, prim.Product):
        text = "*".join(_render(child, _MUL) for child in expr.children)
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.QuotientBase):
        if isinstance(expr, prim.FloorDiv):
            symbol = "//"
        elif isinstance(expr, prim.Remainder):
            symbol = "%"
        else:
            symbol = "/"
        text = f"{_render(expr.numerator, _MUL)} {symbol} {_render(expr.denominator, _POW)}"
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.Power):
        text = f"{_render(expr.base, _POW)}**{_render(expr.exponent, _POW)}"
        return _parens(text, _POW, outer)
    if isinstance(expr, prim.Call):
        args = ", ".join(_render(arg, _OR) for arg in expr.parameters)
        return f"{_render(expr.function, _ATOM)}({args})"
    if isinstance(expr, prim.Subscript):
        index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
        return (
            f"{_render(expr.aggregate, _ATOM)}"
            f"[{', '.join(_render(i, _OR) for i in index)}]"
        )
    return str(expr)


def render(expr: Any) -> str:
    """Render a term as readable Python-like source.

    This is what the ledger shows and what a Lean printer is measured against.
    """
    return _render(expr, _OR)


# }}}
