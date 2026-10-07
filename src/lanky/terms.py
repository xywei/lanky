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

Five node types have no pymbolic counterpart and are added here:
:class:`Forall`, :class:`Exists`, :class:`Sum` (a reduction over a generator,
not addition), :class:`Abs` and :class:`Elementary`, an elementary function
(``exp``, ``log`` or ``sqrt``) applied to one argument.

Binders come from generators. ``all(p(r) for r in Fin[n])`` is an ordinary
generator expression; the builtin ``all`` is replaced by :func:`forall` while an
annotation is being evaluated, the index type's ``__iter__`` yields exactly one
fresh variable when its bound is symbolic, and the name of that variable is read
off the generator's code object so that the printed statement says ``r`` and not
``_i3``. A ``if`` clause in the generator records a guard: the truth value of a
symbolic proposition is undefined, so :meth:`PropositionMixin.__bool__` uses the
request as the signal that a guard was written, and raises outside binder
tracing. A concrete domain (``Fin[3]``) binds no binder: it is walked, and
the builtin answers over what the generator yielded, so a symbolic guard there
has nowhere to go and is refused rather than dropped.
"""

from __future__ import annotations

import builtins
import cmath
import dataclasses
import dis
import enum
import functools
import inspect
import itertools
import math
import numbers
import operator
import sys
from collections.abc import Callable, Iterable, Iterator, Sequence
from contextlib import closing, contextmanager
from contextvars import ContextVar
from fractions import Fraction
from typing import Any, ClassVar

import pymbolic.primitives as prim
from pymbolic import expr_dataclass
from pymbolic.mapper.evaluator import EvaluationMapper as _PymbolicEvaluationMapper

__all__ = [
    "Abs",
    "Add",
    "BUILTIN_OVERRIDES",
    "BuiltinName",
    "Call",
    "Comparison",
    "ELEMENTARY_FUNCTIONS",
    "EVALUATED_BUILTINS",
    "Elementary",
    "Exists",
    "Forall",
    "LogicalAnd",
    "LogicalNot",
    "LogicalOr",
    "OpenPoint",
    "Polarity",
    "Scope",
    "Subscript",
    "Sum",
    "SymbolicBoolError",
    "Undecided",
    "UndefinedValue",
    "Var",
    "binder_assignments",
    "binders",
    "conjoin",
    "conjuncts",
    "disjoin",
    "elementary_value",
    "evaluate",
    "evaluate_annotations",
    "exact_reading",
    "exists",
    "exp",
    "forall",
    "init_args",
    "free_variables",
    "log",
    "render",
    "sqrt",
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

    A universal over a sampled domain is the mirror image. A draw that breaks
    it is a real counterexample, but a pass over a handful of draws is only
    evidence that it holds. That is what ``TESTED`` means where the statement
    asserts the universal, and nothing anywhere else: under a negation, in a
    hypothesis or the guard of a universal, or inside a sum, a ``True`` would
    be used as a certainty, so evaluation declines there (see
    :class:`Polarity`), and it declines as well when no draw reached the
    universal's guarded domain at all. A sum over a sampled domain declines
    wherever it stands, because the draws are not the domain.
    """


class UndefinedValue(ArithmeticError):
    """Raised when an elementary function is evaluated where Python gives it no value.

    ``math.log(0)`` and ``math.sqrt(-1)`` raise ``ValueError``, and
    ``math.exp(1000)`` overflows a float. Mathlib's ``Real.log``,
    ``Real.sqrt`` and ``Real.exp`` are total (``Real.log 0`` is ``0`` and the
    square root of a negative number is ``0``), so this is the same kind of gap
    as a division by zero: the sampled reading has no answer at the draw where
    the Lean reading has one. The property tester drops such a draw rather
    than count it as a counterexample, and :mod:`lanky.semantics` notes the
    gap on the fact. The tester's exact reading (:func:`exact_reading`) raises
    it for a logarithm or a square root outside its domain; its exponential
    never overflows.
    """


class Polarity(enum.Enum):
    """Where a proposition stands in the statement being evaluated.

    What a sampled answer is worth depends on where it is read. A universal
    over a sampled domain that breaks at a draw is false, wherever it stands;
    one that holds at every draw has only been seen to hold, and that is
    evidence, which is what ``TESTED`` means, only where the statement asserts
    it.

    ``POSITIVE`` is where the statement asserts the proposition: the goal, an
    operand of a conjunction or a disjunction that stands there, the body of a
    quantifier that does, and the guard and the refinements of an existential
    that does, which are conjuncts of what it claims. ``NEGATIVE`` is where
    the statement assumes or denies it: a hypothesis, the operand of a
    negation, and the guard and the refinements of a universal, which are the
    antecedent of what it claims. A ``True`` there counts against the
    statement, or lets a draw into the test, so it has to be certain.
    ``MIXED`` is both at once: a proposition whose truth value is used as a
    value, as an operand of a comparison (``p == q`` between propositions
    reads both ways), an arithmetic operation, a call or a sum.
    """

    POSITIVE = 1
    NEGATIVE = -1
    MIXED = 0

    def flipped(self) -> Polarity:
        """Where the operand of a negation that stands here stands."""
        return Polarity(-self.value)


#: What an operand with no answer at the values in hand raises: a quantifier the
#: draws leave open (:class:`Undecided`), a division by zero, which Python
#: raises where Lean's integer division is total, and an elementary function
#: outside its Python domain (:class:`UndefinedValue`), where Mathlib's is
#: total. None of them is a truth value, and none is an error in the statement.
_OPEN = (Undecided, ZeroDivisionError, UndefinedValue)


#: Whether evaluation reads numbers exactly, as the property tester does (see
#: :func:`exact_reading`).
_EXACT: ContextVar[bool] = ContextVar("lanky_exact_reading", default=False)


@contextmanager
def exact_reading() -> Iterator[None]:
    """Evaluate with exact numbers while the block runs: the property tester's reading.

    Python computes a real number in floating point, and a statement read that
    way is refuted by rounding: ``(x + 0.1) - 0.1 == x`` is false at most
    floats ``x``, and Lean proves it (#33). Inside this block every evaluation
    reads the reals exactly (see :mod:`lanky.intervals`): a float literal is
    the rational number it holds, a complex literal is a
    :class:`~lanky.intervals.ComplexValue` of its parts, ``n / 2`` and ``2 **
    -1`` of integers are fractions, ``exp``, ``log`` and ``sqrt`` are exact
    where the value is rational and enclosed where it is not, and a comparison
    the enclosures cannot settle is :class:`Undecided`, unless it is an
    equality the statement asserts and the enclosures agree to
    (:meth:`LankyEvaluationMapper.map_comparison`). The values the evaluation
    is given are whatever they are: the tester draws fractions for ``Real``.

    Outside it evaluation is Python's, which is what running the file computes,
    and what :meth:`lanky.theory.Theorem.__call__` reports.
    """
    token = _EXACT.set(True)
    try:
        yield
    finally:
        _EXACT.reset(token)


@functools.cache
def _intervals() -> Any:
    """:mod:`lanky.intervals`, imported when first asked for, since it imports this module."""
    from lanky import intervals

    return intervals


def conjoin(operands: Iterable[Callable[[], bool]]) -> bool:
    """The conjunction of ``operands``, read three-valued, as Kleene's strong ``and``.

    Each operand is a thunk that answers a truth value, and they are asked in
    order. The first ``False`` answers the conjunction, whatever an operand
    before it could not answer: a conjunction with a false conjunct is false
    however the others come out. An operand with no answer here (see
    :data:`_OPEN`) is passed over and the walk goes on, and when nothing
    settles the conjunction the first such answer is raised again at the end.
    So ``p & q`` and ``q & p`` agree, where a walk that stopped at its first
    undecided operand gave up on a conjunction a later operand refutes.

    That is sound wherever the conjunction stands. One operand's certain
    ``False`` settles it, whatever the undecided operand would have been, and
    a ``True`` counts for as much as it did before.

    The walk still stops at the first ``False``, so an operand after it is
    never asked: ``(k > 0) & (10 // k > 1)`` does not divide by zero at
    ``k = 0``. An operand after an undecided one is asked now, and anything it
    raises that is not an open answer (a ``TypeError`` for a value that is not
    a truth value, say) is raised; the undecided operand used to keep it from
    being asked at all.

    Raises:
        Undecided: If no operand is ``False`` and one of them was undecided,
            or the ``ZeroDivisionError`` or :class:`UndefinedValue` that one
            raised.
    """
    pending: Exception | None = None
    for operand in operands:
        try:
            if not operand():
                return False
        except _OPEN as exc:
            if pending is None:
                pending = exc
    if pending is not None:
        raise pending
    return True


def disjoin(operands: Iterable[Callable[[], bool]]) -> bool:
    """The disjunction of ``operands``, read three-valued; the mirror of :func:`conjoin`.

    The first ``True`` answers the disjunction, whatever an operand before it
    could not answer, and when no operand is ``True`` the first open answer is
    raised again.

    Raises:
        Undecided: If no operand is ``True`` and one of them was undecided,
            or the ``ZeroDivisionError`` or :class:`UndefinedValue` that one
            raised.
    """
    pending: Exception | None = None
    for operand in operands:
        try:
            if operand():
                return True
        except _OPEN as exc:
            if pending is None:
                pending = exc
    if pending is not None:
        raise pending
    return False


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
    "call": (
        "the truth value of {prop!r} was asked for by a function the generator "
        "being traced calls, or by an ``in`` test, and not by its ``if`` clause: "
        "Python's ``min``, ``max`` and ``sorted`` compare their arguments, and "
        "``x in range(3)`` compares ``x`` with each number in turn, so reading "
        "the answer as a guard would keep one comparison of many and say "
        "something else; a proposition becomes a bool only when it is evaluated "
        "at concrete values"
    ),
}

#: The instructions that run code of the interpreter's own, which can ask a
#: value for its truth without a frame of its own: a call of a builtin, an
#: ``in`` test, which compares its operand with each member, and the step of
#: a loop over an iterator a builtin made, such as ``filter``'s.
_CALLING = ("CALL", "CALL_KW", "CALL_FUNCTION_EX", "CONTAINS_OP", "FOR_ITER")


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
    wrong generator. A builtin the generator calls asks from no frame of its
    own, so the frame is the generator's, stopped at the call: ``min(i, j)``
    in a body asks for ``j < i``, and recording that as a guard turned
    ``all(min(i, j) <= i for ...)`` into a statement about the points where
    ``j < i`` (#63). So does an ``in`` test, ``if i in range(3)``, which asks
    for ``i == 0`` and stops. Either is a call (:data:`_CALLING`).

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
    if current.opname in _CALLING:
        return "call"
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


#: The elementary functions a statement can apply, by the name it spells them.
ELEMENTARY_FUNCTIONS = ("exp", "log", "sqrt")


@expr_dataclass(eq=False)
class Elementary(SymbolicMixin, prim.ExpressionNode):
    """An elementary function applied to one argument: ``exp(x)``, ``log(x)``, ``sqrt(x)``.

    A node of its own rather than a :class:`Call` of a variable named ``exp``,
    because a call is how a family is applied, and a family is a parameter the
    statement binds: a statement that binds a family called ``exp`` means that
    family, and one that writes ``lanky.exp`` means the function every reader
    knows. At concrete values it is ``math``'s function for a real argument and
    ``cmath``'s for a complex one (:func:`elementary_value`); the Lean printer
    writes it as ``Real.exp`` or ``Complex.exp``, which is Mathlib. Its mapper
    method is ``map_elementary``.
    """

    function: str
    argument: Any



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


#: Where a condition that does not mention the loop variable can go instead,
#: per builtin. A sum has no such place: its value would depend on the condition.
_OUTSIDE = {
    "all": "~(condition) | all(body for ...)",
    "any": "(condition) & any(body for ...)",
}


def _refuse_a_dropped_guard(driven: _Driven, word: str) -> None:
    """Raise if a generator over a concrete domain captured a symbolic guard.

    A concrete domain (``Fin[3]``) is walked point by point, so the generator
    binds no binder and the quantifier is answered by the builtin, over the
    values it yielded. A guard that mentions a variable of the statement
    (``if n > 100``) has no truth value at a point. Asking for one while the
    generator is traced records it and answers ``True``, so every point was
    yielded and the guard was dropped: ``sum(1 for i in Fin[3] if n > 100)``
    became ``3`` before any sampling happened, and the statement around it a
    constant, refuted at draws where it is true. ``all`` and ``any`` dropped
    the guard the same way whenever the body was a concrete value.

    Keeping the guard point by point would need it recorded against each value
    rather than pooled in the trace, so it is refused instead, naming the ways
    to write the condition that do keep it: outside the quantifier, for a
    condition that does not mention the loop variable, or over a domain with a
    symbolic bound, where the quantifier is a term that carries its guard. The
    body is no place for it: a symbolic body over a concrete domain is refused
    already, when the builtin asks it for a truth value.

    Raises:
        SymbolicBoolError: If the trace bound no binder and recorded a guard.
    """
    if driven.binders or driven.guard is None:
        return
    # The trace pools what every point recorded, so a guard that does not
    # mention the loop variable comes back once per point; it is named once.
    captured = " and ".join(dict.fromkeys(render(g) for g in conjuncts(driven.guard)))
    # No point got through. Python's `not` does that, since it inverts the
    # answer lanky gives while capturing the guard, but so does a concrete
    # condition joined with `and` that holds at no point, so the hint is
    # conditional.
    inverted = (
        ""
        if driven.values
        else " (no point got through it: if it was written with Python's `not`, "
        "which inverts the answer lanky gives while capturing it, write `~(...)`)"
    )
    outside = _OUTSIDE.get(word)
    moved = (
        f"a condition that does not mention the loop variable can stand outside "
        f"the quantifier, as in {outside}; otherwise "
        if outside
        else ""
    )
    raise SymbolicBoolError(
        f"this {word}(...) walks a concrete domain point by point, and its guard "
        f"{captured!r} is symbolic, with no truth value at a point, so lanky "
        f"would have to drop it, which changes the statement{inverted}; {moved}"
        "give the domain a symbolic bound (a variable m with the hypothesis "
        "m == 3, say), so that the quantifier is a term that keeps its guard"
    )


def forall(gen: Iterable[Any]) -> Any:
    """Universal quantification; the replacement for the builtin ``all``.

    Symbolic domains give a :class:`Forall` term, concrete ones the plain
    ``bool`` that ``all`` would have answered.

    Raises:
        SymbolicBoolError: If the domain is concrete and the guard symbolic,
            which the builtin would drop (see :func:`_refuse_a_dropped_guard`).
    """
    driven = _drive(gen)
    if not driven.binders:
        _refuse_a_dropped_guard(driven, "all")
        return builtins.all(driven.values)
    return Forall(driven.binders, driven.body, driven.guard)


def exists(gen: Iterable[Any]) -> Any:
    """Existential quantification; the replacement for the builtin ``any``.

    Raises:
        SymbolicBoolError: If the domain is concrete and the guard symbolic,
            as for :func:`forall`.
    """
    driven = _drive(gen)
    if not driven.binders:
        _refuse_a_dropped_guard(driven, "any")
        return builtins.any(driven.values)
    return Exists(driven.binders, driven.body, driven.guard)


def sum_(gen: Iterable[Any]) -> Any:
    """Reduction; the replacement for the builtin ``sum``, exported as ``lanky.sum``.

    Over a symbolic domain this is a :class:`Sum` term whose reduced domain is
    known; over a concrete one it is the ordinary Python (or numpy) sum, so the
    same source runs under plain ``python``.

    Raises:
        SymbolicBoolError: If the domain is concrete and the guard symbolic,
            as for :func:`forall`. A sum of symbolic values over a concrete
            domain is added up without asking any value for its truth, so
            nothing else would have noticed the guard go.
    """
    driven = _drive(gen)
    if not driven.binders:
        _refuse_a_dropped_guard(driven, "sum")
        return builtins.sum(driven.values)
    return Sum(driven.binders, driven.body, driven.guard)


def abs_(value: Any) -> Any:
    """Absolute value; the replacement for the builtin ``abs``."""
    if isinstance(value, prim.ExpressionNode):
        return Abs(value)
    return builtins.abs(value)


def elementary_value(function: str, value: Any) -> Any:
    """The value of an elementary function at a number, as Python computes it.

    A real argument (an ``int``, a ``float``, a ``Fraction`` or a numpy scalar)
    goes to :mod:`math` and a complex one to :mod:`cmath`, so ``exp(x)`` for a
    real ``x`` is a ``float``, as it is in the file run as a program. A point
    where Python has no value is refused with :exc:`UndefinedValue`, which is a
    gap between the readings and not a counterexample. The property tester
    does not use it: in its exact reading (:func:`exact_reading`) the value is
    :func:`lanky.intervals.elementary`'s.

    Raises:
        UndefinedValue: If Python's function raises at ``value``: the logarithm
            of a number that is not positive, the square root of a negative
            one, or an exponential that overflows a float.
        TypeError: If ``value`` is not a number, a ``bool`` included.
    """
    if function not in ELEMENTARY_FUNCTIONS:
        raise ValueError(f"unknown elementary function {function!r}")
    if isinstance(value, bool) or not isinstance(value, numbers.Complex):
        raise TypeError(f"{function} takes a number, not {value!r}")
    module = math if isinstance(value, numbers.Real) else cmath
    try:
        return getattr(module, function)(value)
    except (ValueError, OverflowError) as exc:
        raise UndefinedValue(
            f"{function}({value!r}) has no value in Python ({exc}), while "
            "Mathlib's function is total"
        ) from exc


def _elementary(function: str) -> Callable[[Any], Any]:
    """The function a statement calls to apply one elementary function."""

    def apply(value: Any) -> Any:
        if isinstance(value, prim.ExpressionNode):
            return Elementary(function, value)
        return elementary_value(function, value)

    apply.__name__ = apply.__qualname__ = function
    apply.__doc__ = (
        f"``{function}`` of a term, as an :class:`Elementary` node, or of a number, "
        "as Python computes it (see :func:`elementary_value`)."
    )
    return apply


#: The exponential, ``Real.exp`` or ``Complex.exp`` in Lean.
exp = _elementary("exp")
#: The natural logarithm, ``Real.log`` in Lean, and ``Complex.log`` for a complex
#: argument, which Lean has to keep off the branch cut (see :mod:`lanky.lean`).
log = _elementary("log")
#: The square root, ``Real.sqrt`` in Lean, and ``Complex.sqrt`` for a complex
#: argument, which Lean has to keep off the branch cut (see :mod:`lanky.lean`).
sqrt = _elementary("sqrt")


#: The builtins that mean something else inside an annotation.
BUILTIN_OVERRIDES: dict[str, Any] = {
    "all": forall,
    "any": exists,
    "sum": sum_,
    "abs": abs_,
}


# }}}


# {{{ scope and annotation evaluation


#: The builtins an annotation may call, at concrete arguments, and get what
#: Python computes: functions of their arguments alone, which neither read nor
#: change anything else. The rest (``print``, ``open``, ``eval``, ``input``
#: and so on) are no part of a statement, and calling one is refused rather
#: than run while lanky reads the annotation.
EVALUATED_BUILTINS = frozenset(
    """
    bin bool chr complex dict divmod enumerate float frozenset hex int len list
    max min oct ord pow range reversed round set slice sorted str tuple zip
    """.split()
)


def _holds_symbolic(value: Any) -> bool:
    """Whether ``value`` is a term, or a container that holds one.

    A lanky type answers for itself: ``len(Fin[n])`` and iterating ``Nat`` are
    refused by the type, and ``len(Fin[3])`` is ``3``.
    """
    if isinstance(value, prim.ExpressionNode):
        return True
    if isinstance(value, tuple | list | set | frozenset):
        return any(_holds_symbolic(item) for item in value)
    if isinstance(value, dict):
        return any(_holds_symbolic(item) for item in (*value.keys(), *value.values()))
    return False


@contextmanager
def _untraced() -> Iterator[None]:
    """Suspend binder tracing while the block runs, whatever generator is being traced.

    A builtin called from a generator's body runs while that generator is
    traced, so a symbolic domain it iterates would bind a binder of the
    quantifier around it, and a proposition it asks for a truth value would
    be recorded as that quantifier's guard. With the stack empty both are
    refused, as they are outside any annotation.
    """
    saved = list(_TRACE_STACK)
    _TRACE_STACK.clear()
    try:
        yield
    finally:
        _TRACE_STACK[:] = saved


class BuiltinName(Var):
    """A builtin of Python's that an annotation names and nothing in it binds.

    A :class:`Scope` invents a variable for every name it does not have, and
    Python looks a name up in the globals before the builtins, so ``min``,
    ``round`` and ``complex`` in an annotation were variables like ``n``:
    ``min(x, y)`` the application of a free name, as a family is applied, and
    ``round(0.5) == 1`` a statement about whatever Lean reads ``round`` as
    (#63, #64). A builtin's name is this instead. Called at concrete
    arguments it is the builtin, if it is one of :data:`EVALUATED_BUILTINS`:
    ``round(0.5)`` is ``0`` and ``complex(-1, -0.0)`` the complex number, as
    in the file run as a program. Called with a term or a lanky type among its
    arguments it is refused, naming the builtin: lanky has no term for the
    builtin, and Python would compute it on the term, comparing two
    propositions where ``min`` compares two numbers. The builtins that mean
    something else in an annotation (:data:`BUILTIN_OVERRIDES`) are never
    looked up here.

    Named and not called, it is the variable it always was, a free name, as
    ``x: int`` is: a theorem refuses a parameter whose annotation is one
    (:class:`lanky.theory.Theorem`), a plugin can refuse it as loopty refuses
    a sort that is a free name, and the Lean printer declines a statement
    that mentions it (:func:`lanky.lean.statement_of`).
    """

    def __call__(self, *args: Any, **kwargs: Any) -> Any:  # type: ignore[override]
        """The builtin at concrete arguments; refused at symbolic ones.

        Raises:
            TypeError: If an argument is a term or a lanky type, or holds one,
                or if the builtin is not one an annotation may call.
            SymbolicBoolError: If the builtin asks a proposition for its truth
                value, as ``max`` does of a generator over a concrete domain
                whose body is symbolic.
        """
        shown = ", ".join(
            [_shown(arg) for arg in args]
            + [f"{key}={_shown(value)}" for key, value in kwargs.items()]
        )
        if self.name not in EVALUATED_BUILTINS:
            raise TypeError(
                f"{self.name}({shown}) calls Python's {self.name}, which is no "
                "part of a statement: lanky evaluates an annotation, and calls "
                "only the builtins that compute a value from their arguments "
                "alone, there and then (EVALUATED_BUILTINS); bind the name as a "
                "parameter if a variable of that name is meant"
            )
        if _holds_symbolic(args) or _holds_symbolic(kwargs):
            raise TypeError(
                f"{self.name}({shown}) applies Python's {self.name} to a "
                "symbolic value, which lanky has no term for: in an annotation "
                "the builtins all, any, sum and abs build terms, and the others "
                "are Python's at concrete values only. Write what is meant with "
                "terms (lanky.exp, lanky.log and lanky.sqrt among them), or bind "
                f"{self.name} as a parameter if a variable of that name is meant"
            )
        function = getattr(builtins, self.name)
        try:
            with _untraced():
                return function(*args, **kwargs)
        except SymbolicBoolError as exc:
            raise SymbolicBoolError(
                f"{self.name}({shown}) asks a symbolic proposition for its truth "
                f"value, which Python's {self.name} computes with and lanky has "
                f"no term for: {exc}"
            ) from exc
        except TypeError as exc:
            # a symbolic domain the builtin iterated, which binds nothing here,
            # or arguments Python's builtin does not take
            raise TypeError(f"Python's {self.name} raised at {self.name}({shown}): {exc}") from exc


def _shown(value: Any) -> str:
    """An argument of a builtin, as a message names it: a term rendered, a generator elided."""
    if inspect.isgenerator(value):
        return "(... for ...)"
    return render(value) if isinstance(value, prim.ExpressionNode) else repr(value)


class Scope(dict):
    """A mapping in which every unknown name is a symbolic variable.

    This is the whole of lanky's "parser": used as the globals of ``eval``, it
    lets Python itself read an annotation such as ``Fn[Fin[n], Nat]`` in which
    ``n`` has no value anywhere. Dunder names still raise :exc:`KeyError`, so
    the interpreter's own bookkeeping (``__builtins__``) is undisturbed. The
    name of one of Python's builtins is a :class:`BuiltinName`, a variable
    that is the builtin when it is called at concrete values.
    """

    def __missing__(self, name: str) -> Any:
        """Invent a variable for ``name``, remembering it for later lookups."""
        if name.startswith("__") and name.endswith("__"):
            raise KeyError(name)
        var = BuiltinName(name) if _is_builtin(name) else Var(name)
        self[name] = var
        return var


def _is_builtin(name: str) -> bool:
    """Whether ``name`` names one of Python's builtins, which no annotation defines."""
    return not name.startswith("_") and hasattr(builtins, name)


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


@functools.cache
def _refined_type() -> type:
    """:class:`lanky.prelude.Refined`, imported when first asked for.

    The prelude imports this module, so the class cannot be imported at the
    top of it.
    """
    from lanky.prelude import Refined

    return Refined


def _base_domain(domain: Any) -> Any:
    """The domain a refinement refines, through any number of refinements."""
    refined = _refined_type()
    while isinstance(domain, refined):
        domain = domain.base
    return domain


class _Walk:
    """What one walk over a quantifier's binders met.

    ``sampled`` lists the domains the walk drew points from rather than
    enumerating them, each once, in the order they were met. ``visited``
    counts the assignments the refinements admitted, and ``reached`` the ones
    the guard admitted as well. ``unsure`` counts the points the walk could
    place neither in the guarded domain nor out of it (:class:`OpenPoint`).

    Whether a domain was drawn from is recorded as the walk goes rather than
    read off the binders, because a walk can end before it gets to a sampled
    binder: over ``i in Fin[n], k in Nat`` at ``n = 0`` the first binder has
    no point, ``Nat`` is never drawn from, and the domain is empty rather than
    unexplored, so the quantifier is decided over it.
    """

    def __init__(self) -> None:
        self.sampled: list[Any] = []
        self.visited = 0
        self.reached = 0
        self.unsure = 0

    def drew(self, domain: Any) -> None:
        """Record that points were drawn from ``domain``."""
        if not any(seen is domain for seen in self.sampled):
            self.sampled.append(domain)

    def names(self) -> str:
        """The sampled domains, as a reason names them."""
        return ", ".join(str(domain) for domain in self.sampled)


@dataclasses.dataclass(frozen=True, eq=False)
class OpenPoint:
    """A point of a quantifier's walk that the values in hand put neither in its domain nor out.

    :meth:`LankyEvaluationMapper.guarded_assignments` yields one, in place of
    ``None``, where the guard or a refinement has no answer at the point (see
    :data:`_OPEN`: an undecided quantifier in it, a division by zero), and
    where a binder's domain cannot be enumerated at all, because its bound has
    no answer (``Fin[10 // i]`` at ``i = 0``). A quantifier reads its points
    as one conjunction or one disjunction, three-valued, so such a point does
    not end the walk: a body that settles it there settles it, and otherwise
    the point is open (see :meth:`LankyEvaluationMapper.map_forall`).

    Attributes:
        reason: The open answer, which is raised again when no point settles
            the quantifier.
        bound: Whether the binders are bound at the point, so that the body
            can be read there. They are where a guard or a refinement is
            open; a domain that could not be enumerated has no points to bind,
            and stands for all of them at once.
    """

    reason: Exception
    bound: bool = True


#: The nodes that say where their operands stand (see :class:`Polarity`). Every
#: other node uses the values below it as values.
_POLAR = (prim.LogicalAnd, prim.LogicalOr, prim.LogicalNot, Forall, Exists)

#: A comparison's operator, as the function Python applies for it.
_COMPARISONS = {
    "==": operator.eq,
    "!=": operator.ne,
    "<": operator.lt,
    "<=": operator.le,
    ">": operator.gt,
    ">=": operator.ge,
}


def _where(polarity: Polarity) -> str:
    """Where a proposition that does not stand ``POSITIVE`` stands, for a reason."""
    if polarity is Polarity.NEGATIVE:
        return (
            "the statement assumes or denies it (a hypothesis, a guard or a "
            "refinement, or under a negation)"
        )
    return (
        "its truth value is used as a value (inside a sum, a comparison or "
        "an arithmetic operation)"
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

    The other answer of a ``forall``, ``True`` because every draw held, is
    evidence and not proof, and what evidence is worth depends on where it is
    read. The mapper carries the :class:`Polarity` of the node it evaluates:
    the connectives and the quantifiers say where their operands stand, and
    any other node uses the values below it as values, so a proposition under
    it stands both ways. A sampled ``forall`` answers ``True`` only where it
    stands ``POSITIVE``, where the statement asserts it and a pass is what
    ``TESTED`` means; anywhere else the ``True`` would be used as a certainty,
    and it declines. It declines as well when no draw reached its guarded
    domain, because a ``forall`` that held at no point was not seen to hold.
    A sum over a sampled domain declines wherever it stands: draws are not the
    domain, and their sum is not the sum.

    A refined domain ``T & p`` (:class:`lanky.prelude.Refined`) has the points
    of ``T`` at which ``p`` holds. ``p`` talks about the binder (``k > 0`` for
    the binder ``k``), so it can only be read with the binder bound, and that
    is done here, point by point, as a guard is read: ``T`` is walked or
    sampled, each point is bound, and the points the refinement rejects are
    skipped. Whether the domain is enumerated is whether ``T`` is, so
    ``Fin[n] & p`` still decides both quantifiers. This is the reading the Lean
    printer gives the same binder (``T`` plus the guard ``p``), so the two
    readings of the statement agree.

    A connective reads its operands three-valued (:func:`conjoin`,
    :func:`disjoin`). An operand the values in hand cannot answer does not
    stop it, and a later operand that settles it, a ``False`` in a
    conjunction or a ``True`` in a disjunction, answers it all the same, so
    the order the operands are written in does not change the answer. A
    quantifier reads its points the same way, a universal as the conjunction
    of its points and an existential as their disjunction (:meth:`map_forall`,
    :meth:`map_exists`), so ``all(p(i) for i in Fin[2])`` and ``p(0) & p(1)``
    agree; a point whose guard or refinement has no answer is settled by a
    body that settles it whatever the guard, and is open otherwise.

    Wherever a proposition's truth is read, in a connective, a guard, a
    refinement or the body of a quantifier, the value has to be a truth value
    (:func:`truth_value`). pymbolic's own connectives apply Python's
    truthiness, which reads a number as a proposition.

    A mapper made inside :func:`exact_reading` reads numbers exactly, as the
    property tester does: its constants, true divisions, powers, elementary
    functions and comparisons are :mod:`lanky.intervals`'s (``exact``). One
    made outside it reads them as Python does.
    """

    def __init__(
        self,
        context: dict[str, Any],
        sampler: Callable[[Any], Iterable[Any]] | None = None,
        polarity: Polarity = Polarity.POSITIVE,
    ) -> None:
        super().__init__(context)
        self.context: dict[str, Any] = context
        self.sampler = sampler
        #: Where the node being evaluated stands in the statement.
        self.polarity = polarity
        #: Whether numbers are read exactly (see :func:`exact_reading`).
        self.exact = _EXACT.get()

    def rec(self, expr: Any, *args: Any, **kwargs: Any) -> Any:
        """Evaluate ``expr``, where the node that asked for it puts it.

        A connective or a quantifier keeps the polarity it is given and says
        where its own operands stand. So does a comparison, because what an
        equality of two enclosures is worth depends on where it stands
        (:meth:`map_comparison`); its two sides are values, and stand
        ``MIXED``. Any other node, an arithmetic operation, a call or a sum,
        uses the values below it as they are, so what is below it is evaluated
        standing ``MIXED``.
        """
        if (
            self.polarity is Polarity.MIXED
            or isinstance(expr, _POLAR)
            or isinstance(expr, prim.Comparison)
            or not isinstance(expr, prim.ExpressionNode)
        ):
            return super().rec(expr, *args, **kwargs)
        return self._at(Polarity.MIXED, expr)

    __call__ = rec

    def _at(self, polarity: Polarity, expr: Any) -> Any:
        """Evaluate ``expr`` standing at ``polarity``."""
        saved, self.polarity = self.polarity, polarity
        try:
            return self.rec(expr)
        finally:
            self.polarity = saved

    @staticmethod
    def is_exhaustive(domain: Any) -> bool:
        """Whether walking this domain visits every one of its points.

        An index type with a bound answers ``points``, so its extent is the
        whole domain; anything else is sampled. A refinement is walked by
        walking what it refines, so it is exhaustive when that is: every point
        of ``Fin[n]`` is visited and each is kept or skipped.
        """
        return getattr(_base_domain(domain), "points", None) is not None

    def _points(self, domain: Any) -> Iterable[Any]:
        """The concrete points of one binder domain, before any refinement.

        A refined domain yields the points of the domain it refines, and
        :meth:`assignments` keeps the ones the refinement admits, because the
        refinement can only be read with the binder bound. The sampler is
        handed the base too: a draw of ``Nat & p`` made without the binder's
        name could not judge ``p``, and used to come back unfiltered.
        """
        base = _base_domain(domain)
        points = getattr(base, "points", None)
        if points is not None:
            return points(self.rec)
        if self.sampler is not None:
            return self.sampler(base)
        raise ValueError(f"cannot enumerate the binder domain {domain!r}")

    def _admits(self, domain: Any, polarity: Polarity) -> bool:
        """Whether the point just bound is a point of ``domain``.

        Only a refinement can say no. Its propositions are read under the
        current assignment, the binder included, the innermost refinement
        first, so ``Nat & (k > 0) & (10 // k > 1)`` never divides by zero, and
        standing at ``polarity``. A proposition that cannot be answered
        raises, as a guard does, unless a later one rejects the point, and
        the caller decides what that means (the property tester drops the
        draw).
        """
        if not isinstance(domain, _refined_type()):
            return True
        # One conjunction, read three-valued (conjoin): a proposition that
        # rejects the point settles it, whatever an earlier one could not answer.
        return conjoin(
            [
                lambda: self._admits(domain.base, polarity),
                *(lambda p=p: self._truth_at(polarity, p) for p in domain.props),
            ]
        )

    def assignments(
        self,
        binder_list: Sequence[tuple[Var, Any]],
        refinements: Polarity | None = None,
    ) -> Iterator[None]:
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

        A point a refined domain does not admit (:meth:`_admits`) is bound,
        judged and skipped, so no assignment yielded here is outside the
        domain its binder declares. The refinements stand at ``refinements``,
        by default where a universal standing here puts them, opposite to it.
        """
        if refinements is None:
            refinements = self.polarity.flipped()
        return self._walk(list(binder_list), refinements, _Walk())

    def _walk(
        self,
        binder_list: Sequence[tuple[Var, Any]],
        refinements: Polarity,
        walk: _Walk,
        keep_open: bool = False,
        unsure: Exception | None = None,
    ) -> Iterator[OpenPoint | None]:
        """The walk :meth:`assignments` describes, recording what it drew in ``walk``.

        Without ``keep_open`` a refinement or a domain bound with no answer at
        a point raises, and the walk ends there. With it the walk goes on, as
        a quantifier reads its points (see :meth:`guarded_assignments`): a
        point a refinement cannot answer is bound and yielded as an
        :class:`OpenPoint`, and every point under it inherits the open answer,
        ``unsure``, unless a refinement below rejects it; a binder whose
        domain cannot be enumerated is yielded once, as an :class:`OpenPoint`
        with nothing bound, in place of the points it would have had.
        """
        if not binder_list:
            yield None if unsure is None else OpenPoint(unsure)
            return
        (var, domain), rest = binder_list[0], binder_list[1:]
        saved = self.context.get(var.name, _UNSET)
        try:
            try:
                points = self._points(domain)
            except _OPEN as exc:
                if not keep_open:
                    raise
                yield OpenPoint(unsure or exc, bound=False)
                return
            if not self.is_exhaustive(domain):
                walk.drew(domain)
            for point in points:
                self.context[var.name] = point
                here = unsure
                try:
                    if not self._admits(domain, refinements):
                        continue
                except _OPEN as exc:
                    if not keep_open:
                        raise
                    here = here or exc
                yield from self._walk(rest, refinements, walk, keep_open, here)
        finally:
            if saved is _UNSET:
                self.context.pop(var.name, None)
            else:
                self.context[var.name] = saved

    def guarded_assignments(self, expr: Forall | Exists) -> Iterator[OpenPoint | None]:
        """Bind a quantifier's binders at each point of its guarded domain.

        The points are the assignments :meth:`assignments` yields at which the
        guard holds too, and each is yielded as ``None``. A universal's
        refinements and guard are the antecedent of what it claims, and stand
        opposite to it; an existential's are conjuncts of it, and stand where
        it does. The caller evaluates the body at each point and stops at the
        answer it is looking for, a counterexample to a universal or a witness
        to an existential, which closes the walk.

        A point the guard or a refinement has no answer at is not the end of
        the walk (#29). It is bound and yielded as an :class:`OpenPoint`
        carrying the open answer, and so is a binder domain that cannot be
        enumerated, with nothing bound, since a quantifier is a conjunction or
        a disjunction of its points and reads them three-valued, as
        :func:`conjoin` reads operands. A guard or a refinement that rejects
        the point still settles it, whatever another could not answer. Only a
        point yielded as ``None`` counts as one the walk reached.

        A walk that runs to its end is where sampling can leave the answer
        open, and that is settled here, after the last point. When the walk
        drew from no sampled domain it was exhaustive, and the caller's answer
        stands: no counterexample, or no witness, anywhere in the domain.

        Raises:
            Undecided: If the walk drew from a sampled domain and the answer
                the caller would give is not one: an existential that found
                no witness among draws; a universal that reached no point of
                its guarded domain, because the guard or a refinement rejected
                every draw; and a universal that held at every point it
                reached but does not stand ``POSITIVE``, so that its ``True``
                would be used as a certainty (see :class:`Polarity`).
        """
        universal = isinstance(expr, Forall)
        antecedent = self.polarity.flipped() if universal else self.polarity
        walk = _Walk()
        with closing(
            self._walk(list(expr.binders), antecedent, walk, keep_open=True)
        ) as points:
            for unsure in points:
                if unsure is not None and not unsure.bound:
                    walk.unsure += 1
                    yield unsure
                    continue
                if unsure is None:
                    walk.visited += 1
                try:
                    if not self._holds(expr.guard, antecedent):
                        continue
                except _OPEN as exc:
                    unsure = unsure or OpenPoint(exc)
                if unsure is None:
                    walk.reached += 1
                else:
                    walk.unsure += 1
                yield unsure
        if not walk.sampled:
            return
        if universal:
            _decline_sampled_pass(expr, walk, self.polarity)
            return
        raise Undecided(
            f"no witness was drawn for {render(expr)}, and {walk.names()} is "
            "sampled rather than enumerated, so the statement is undecided "
            "here rather than false"
        )

    def _holds(self, expr: Any, polarity: Polarity) -> bool:
        """Whether a guard holds under the current assignment, standing at ``polarity``."""
        return expr is None or self._truth_at(polarity, expr)

    def _truth(self, expr: Any) -> bool:
        """Evaluate a proposition, refusing a value that is not a truth value."""
        return truth_value(self.rec(expr), expr)

    def _truth_at(self, polarity: Polarity, expr: Any) -> bool:
        """Evaluate a proposition standing at ``polarity``, as :meth:`_truth` does."""
        return truth_value(self._at(polarity, expr), expr)

    def map_logical_and(self, expr: prim.LogicalAnd) -> bool:
        """Every operand, left to right, stopping at the first false one.

        An operand the values in hand cannot answer does not stop the walk: a
        later false one still settles the conjunction (:func:`conjoin`).
        """
        return conjoin(lambda child=child: self._truth(child) for child in expr.children)

    def map_logical_or(self, expr: prim.LogicalOr) -> bool:
        """Some operand, left to right, stopping at the first true one.

        An operand the values in hand cannot answer does not stop the walk: a
        later true one still settles the disjunction (:func:`disjoin`).
        """
        return disjoin(lambda child=child: self._truth(child) for child in expr.children)

    def map_logical_not(self, expr: prim.LogicalNot) -> bool:
        """The negation of the operand, which stands opposite to it."""
        return not self._truth_at(self.polarity.flipped(), expr.child)

    def map_forall(self, expr: Forall) -> Any:
        """True when the body holds at every point of the guarded domain.

        A ``False`` is a real counterexample over any domain. Over a sampled
        domain a ``True`` is evidence rather than proof, which is exactly what
        the ``TESTED`` status means where the statement asserts the ``forall``
        and nothing anywhere else (:meth:`guarded_assignments` declines it
        there).

        The points are read three-valued, as the operands of a conjunction
        are (:func:`conjoin`), so the order of the domain does not change the
        answer (#29): a point whose body has no answer is passed over, and a
        later point where the body fails is a counterexample all the same;
        when none is, the first open answer is raised again. A point whose
        guard or refinement has no answer (an :class:`OpenPoint`) is settled
        when the body holds there, since an implication with a true
        consequent holds whatever its antecedent, and is open otherwise.

        The walk is closed explicitly on the way out. Leaving it to the
        collector would work in CPython and rest on refcounting for something
        that has to hold: until the walk is closed its ``finally`` has not run,
        and the binding this quantifier replaced is still the inner point.

        Raises:
            Undecided: If no point is a counterexample and one has no answer,
                or the ``ZeroDivisionError`` or :class:`UndefinedValue` that
                one raised; or if a sampled walk met no counterexample and
                that is not an answer here (:meth:`guarded_assignments`).
        """
        return self._quantify(expr)

    def map_exists(self, expr: Exists) -> Any:
        """True when the body holds somewhere in the guarded domain.

        The points are read three-valued, as the operands of a disjunction
        are (:func:`disjoin`): a witness after a point that has no answer is
        a witness all the same. A point whose guard or refinement has no
        answer is settled when the body fails there, since it is then no
        witness whatever its guard, and is open otherwise.

        Raises:
            Undecided: If no point is a witness and one has no answer, or
                the ``ZeroDivisionError`` or :class:`UndefinedValue` that one
                raised; or if no witness turned up and a binder domain was
                sampled rather than enumerated, so "no witness among these
                points" is not "no witness" (:meth:`guarded_assignments`).
        """
        return self._quantify(expr)

    def _quantify(self, expr: Forall | Exists) -> bool:
        """Read a quantifier's points as one conjunction or one disjunction, three-valued.

        A universal is settled by a point where the body fails, and an
        existential by one where it holds; such a point settles it only when
        the point is certainly in the guarded domain. When nothing settles it,
        the first open answer is raised again, whatever the end of a sampled
        walk would have said: that a sampled universal held at every draw, or
        that no witness was drawn, is not what happened at a draw that had no
        answer.
        """
        settles = isinstance(expr, Exists)
        pending: Exception | None = None
        try:
            with closing(self.guarded_assignments(expr)) as points:
                for unsure in points:
                    if unsure is not None and not unsure.bound:
                        pending = pending or unsure.reason
                        continue
                    try:
                        body = self._truth(expr.body)
                    except _OPEN as exc:
                        pending = pending or exc
                        continue
                    if body != settles:
                        continue
                    if unsure is None:
                        return settles
                    pending = pending or unsure.reason
        except Undecided:
            if pending is None:
                raise
        if pending is not None:
            raise pending
        return not settles

    def map_lanky_sum(self, expr: Sum) -> Any:
        """Add the body over the guarded domain.

        A reduction visits every point, so nothing short-circuits here; the
        walk is still closed explicitly, because an exception raised in the
        body leaves the loop the same way a witness does. Everything in a sum
        is used as a value and stands ``MIXED``.

        Raises:
            Undecided: If the walk draws from a sampled domain. The sum of a
                handful of draws is not the sum over the domain, and it is
                declined before the body is evaluated at a draw.
        """
        total: Any = 0
        walk = _Walk()
        with closing(self._walk(list(expr.binders), self.polarity, walk)) as points:
            for _ in points:
                _decline_sampled_sum(expr, walk)
                if self._holds(expr.guard, self.polarity):
                    total = total + self.rec(expr.body)
        _decline_sampled_sum(expr, walk)
        return total

    def map_abs(self, expr: Abs) -> Any:
        """Absolute value of the operand."""
        return builtins.abs(self.rec(expr.operand))

    def map_elementary(self, expr: Elementary) -> Any:
        """The function at the value of its argument, as :func:`elementary_value` has it.

        In the exact reading it is :func:`lanky.intervals.elementary`'s: exact
        where the value is rational, and enclosed where it is not.
        """
        value = self.rec(expr.argument)
        if self.exact:
            return _intervals().elementary(expr.function, value)
        return elementary_value(expr.function, value)

    def map_constant(self, expr: Any) -> Any:
        """A number is its own value; in the exact reading a float is the rational it holds.

        So is a complex number's pair of parts (:func:`lanky.intervals.exact`),
        which is how the Lean printer reads both literals.
        """
        if self.exact:
            return _intervals().exact(expr)
        return expr

    def map_quotient(self, expr: prim.Quotient) -> Any:
        """True division; in the exact reading, two integers divide to a fraction."""
        numerator, denominator = self.rec(expr.numerator), self.rec(expr.denominator)
        if self.exact:
            return _intervals().quotient(numerator, denominator)
        return numerator / denominator

    def map_power(self, expr: prim.Power) -> Any:
        """A power; in the exact reading, as :func:`lanky.intervals.power` takes it."""
        base, exponent = self.rec(expr.base), self.rec(expr.exponent)
        if self.exact:
            return _intervals().power(base, exponent)
        return base**exponent

    def map_comparison(self, expr: prim.Comparison) -> Any:
        """Compare the two sides, which are values and stand ``MIXED``.

        In the exact reading a side can be an enclosure (see
        :mod:`lanky.intervals`), and a comparison with one is answered by
        :func:`lanky.intervals.compare`: true where the enclosures prove it,
        false where they exclude it, and a false answer is as definite as a
        proof. Where they straddle it, it is undecided, with one exception. An
        equality between two transcendental numbers is never proved by
        enclosures, so an equality the statement asserts, one standing
        ``POSITIVE``, holds where the enclosures agree to within
        :data:`lanky.intervals.AGREEMENT` bits (:func:`lanky.intervals.agree`).
        That is evidence and not proof, which is what ``TESTED`` means, and it
        is the reading a sampled universal that held at every draw gets: under
        a negation, in a hypothesis or a guard, or used as a value, the
        ``True`` would be used as a certainty, and the comparison is undecided
        there. So is an order whose enclosures overlap, wherever it stands.

        Raises:
            Undecided: Where the enclosures straddle the comparison, but for
                an asserted equality they agree to.
        """
        left = self._at(Polarity.MIXED, expr.left)
        right = self._at(Polarity.MIXED, expr.right)
        if self.exact:
            intervals = _intervals()
            if isinstance(left, intervals.NUMBER_TYPES) or isinstance(
                right, intervals.NUMBER_TYPES
            ):
                answer = intervals.compare(expr.operator, left, right)
                if answer is not NotImplemented:
                    return self._settle(expr, answer, left, right)
        return _COMPARISONS[expr.operator](left, right)

    def _settle(self, expr: prim.Comparison, answer: bool | None, left: Any, right: Any) -> bool:
        """What a comparison of enclosures answers, given what the enclosures said.

        Raises:
            Undecided: Where they straddle it (see :meth:`map_comparison`).
        """
        if answer is not None:
            return answer
        intervals = _intervals()
        sides = f"{intervals.describe(left)} and {intervals.describe(right)}"
        if expr.operator != "==":
            raise Undecided(
                f"the two sides of {render(expr)} are enclosed at this draw in {sides}, "
                "which overlap, so the enclosures neither prove it nor refute it, and "
                "the statement is undecided here"
            )
        if self.polarity is not Polarity.POSITIVE:
            raise Undecided(
                f"the two sides of {render(expr)} agree to within their enclosures at "
                f"this draw, {sides}, which is evidence that they are equal and not "
                f"proof, and the equality stands where {_where(self.polarity)}, which "
                "needs a certain answer, so the statement is undecided here"
            )
        if not intervals.agree(left, right):
            raise Undecided(
                f"the two sides of {render(expr)} are enclosed at this draw in {sides}, "
                f"which overlap but are wider than {intervals.AGREEMENT} bits of their "
                "size, too wide for the agreement to be evidence, so the statement is "
                "undecided here"
            )
        return True

    def map_foreign(self, expr: Any, *args: Any, **kwargs: Any) -> Any:
        """A constant pymbolic has no class for, a ``Fraction``, is its own value.

        pymbolic's operators refuse a ``Fraction`` operand, so a term with one
        in it is built node by node, by a plugin, and it is a literal like any
        other: the Lean printer reads an integral one as the integer it equals,
        and the evaluator refused it as an invalid foreign object, which left
        the property tester unable to run the statement at all.
        """
        if isinstance(expr, Fraction):
            return expr
        return super().map_foreign(expr, *args, **kwargs)


class _Unset:
    """Sentinel for "this name had no value before the binder bound it"."""


_UNSET = _Unset()


def _decline_sampled_pass(expr: Forall, walk: _Walk, polarity: Polarity) -> None:
    """Decline a universal that met no counterexample among draws, where that is no answer.

    ``walk`` drew from a sampled domain, so the pass is a handful of draws
    that held. Two things make that worth nothing, and either one declines.

    No draw reached the guarded domain. A guard or a refinement that rejects
    every draw (``k > 100``, or ``Nat & (k == 1000)``, over naturals drawn up
    to five) leaves a ``forall`` that held at every point it looked at because
    it looked at none. Over an enumerated domain that is the vacuous truth it
    looks like; over draws it says nothing about whether the guarded domain is
    empty, and the guard and the refinement spellings of one statement are
    declined alike.

    The universal does not stand ``POSITIVE``. Held at every draw is evidence
    that it holds, which the statement may use where it asserts the universal
    and nowhere else: under a negation, in a hypothesis or the guard of a
    universal, the ``True`` would count against the statement or let a draw
    into the test, and inside a sum or a comparison it would be used as a
    value.

    Raises:
        Undecided: In either case.
    """
    names = walk.names()
    if not walk.reached:
        if walk.visited:
            missed = f"passed the guard {render(expr.guard)}"
        elif any(isinstance(domain, _refined_type()) for domain in walk.sampled):
            missed = "satisfied its refinement"
        else:
            missed = "reached a point of its domain"
        if walk.unsure:
            # the body was read at a draw the guard or a refinement had no
            # answer at, which is no point of the guarded domain for certain
            missed, looked = f"{missed} for certain", "held at no point known to be in its domain"
        else:
            looked = "was evaluated at no point"
        raise Undecided(
            f"no draw of {names} {missed}, so {render(expr)} {looked}, which is "
            "not evidence that it holds"
        )
    if polarity is Polarity.POSITIVE:
        return
    raise Undecided(
        f"{render(expr)} held at every draw of {names}, which is evidence that "
        f"it holds and not proof, and it stands where {_where(polarity)}, which "
        "needs a certain answer, so the statement is undecided here"
    )


def _decline_sampled_sum(expr: Sum, walk: _Walk) -> None:
    """Decline a sum whose walk drew from a sampled domain.

    Raises:
        Undecided: If ``walk`` drew from one.
    """
    if walk.sampled:
        raise Undecided(
            f"{render(expr)} adds up over {walk.names()}, which is sampled "
            "rather than enumerated, and a sum over draws is not the sum over "
            "the domain, so the statement is undecided here"
        )


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
    hypothesis point by point. A refined domain yields only the points its
    refinement admits (see :class:`LankyEvaluationMapper`), read as the
    antecedent of a universal the statement asserts, so standing ``NEGATIVE``.
    """
    yield from LankyEvaluationMapper(context, sampler).assignments(list(binder_list))


def evaluate(
    expr: Any,
    context: dict[str, Any] | None = None,
    sampler: Callable[[Any], Iterable[Any]] | None = None,
    polarity: Polarity = Polarity.POSITIVE,
) -> Any:
    """Evaluate ``expr`` at the values in ``context``.

    A proposition evaluates to a ``bool``, which is what makes an annotation
    double as a property test. ``polarity`` is where ``expr`` stands in the
    statement (:class:`Polarity`): a goal stands ``POSITIVE``, and a
    hypothesis ``NEGATIVE``. It matters only for what ``sampler`` draws.

    Raises:
        Undecided: If a quantifier or a sum over a domain ``sampler`` supplied
            has no answer from the draws (see
            :meth:`LankyEvaluationMapper.guarded_assignments`): an existential
            that found no witness, a universal that reached no point of its
            guarded domain or that held at every draw where it does not stand
            ``POSITIVE``, or a sum. Sampled points are not the domain, so there
            is no answer to return, and the caller drops the draw instead.
        TypeError: If an operand of a connective, a guard or the body of a
            quantifier is not a truth value (:func:`truth_value`). What the
            whole of ``expr`` evaluates to is the caller's to judge.
    """
    if not isinstance(expr, prim.ExpressionNode):
        # A constant is read as the mapper reads one, so that a float a
        # definition assigns is the rational it holds in the exact reading.
        return _intervals().exact(expr) if _EXACT.get() else expr
    return LankyEvaluationMapper(dict(context or {}), sampler, polarity)(expr)


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


def _domain_names(var: Var, domain: Any) -> frozenset[str]:
    """The names a binder's domain mentions, apart from the binder itself.

    A ``Fin`` bound is read as it always was. A refinement adds the names its
    propositions mention, less its own binder, which is what they are about:
    ``Fin[n] & (k < m)`` for the binder ``k`` mentions ``n`` and ``m``. It used
    to be read through ``bound``, which a refinement does not have, so both
    were missed.
    """
    if isinstance(domain, _refined_type()):
        return _domain_names(var, domain.base) | (free_variables(domain.props) - {var.name})
    return free_variables(getattr(domain, "bound", None))


def free_variables(expr: Any) -> frozenset[str]:
    """The names a term mentions that no binder of the term binds.

    A binder's domain is read with the binders before it bound, and not its
    own: ``all(j < n for i in Fin[n] for j in Fin[i])`` evaluates ``Fin[i]``
    after the outer ``i`` is bound, so that ``i`` is the binder and the term
    mentions ``n`` alone, while in ``all(i > 0 for i in Fin[i])`` the domain is
    evaluated before its binder exists, and its ``i`` is free. A refinement is
    about its own binder, which :func:`_domain_names` leaves out.
    """
    if isinstance(expr, Var):
        return frozenset({expr.name})
    if isinstance(expr, Forall | Exists | Sum):
        bound: set[str] = set()
        domains: frozenset[str] = frozenset()
        for var, domain in expr.binders:
            domains |= _domain_names(var, domain) - bound
            bound.add(var.name)
        inner = free_variables(expr.body) | free_variables(expr.guard)
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
    if isinstance(expr, Elementary):
        return f"{expr.function}({_render(expr.argument, _OR)})"
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
