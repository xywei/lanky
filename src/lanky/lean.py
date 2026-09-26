"""Printing lanky terms as Lean 4 source, over core Lean only.

The design idea. Lean is the platform lanky is hosted on, so a lanky statement
has to arrive there as something Lean can elaborate on its own, with no Mathlib
and no ``lake exe cache get``. That constraint decides almost everything in this
module: what can be printed is exactly what core Lean's ``Int``, ``Nat`` and
``Bool``, its arithmetic, and its logical connectives can say. A reduction
(:class:`lanky.terms.Sum`) needs ``Finset.sum`` and an absolute value needs the
``abs`` of an ordered ring; both are Mathlib, so both raise
:exc:`UnsupportedTerm` rather than emit source Lean would reject with a puzzling
elaboration error. ``Real`` is out for the same reason.

*One reading of arithmetic, the integer one.* A statement means what it
computes when the file runs: the property tester draws a ``Nat`` as a Python
integer, so ``n - 1`` is ``-1`` at ``n = 0``, and isl reads index arithmetic
the same way. The printer states that same statement to Lean. A ``Nat`` or
``Fin`` variable is an ``Int`` whose bounds are hypotheses, ``0 ≤ n`` and, for
``Fin[m]``, ``n < m`` as well; every operation is ``Int``'s; and ``//`` and
``%`` are ``Int.fdiv`` and ``Int.fmod``, which round toward negative infinity
as Python's do. Lean's truncated ``Nat`` subtraction never appears, so
``n - 1 ≥ 0`` is as false in Lean as it is under the tester, and what Lean
proves is what the tester tests. Truncation could not have been matched on the
Python side anyway: pymbolic has no subtraction node, so ``a - b + c`` is one
flattened sum and has lost the association truncation depends on, while
integer arithmetic does not depend on it.

Two choices keep ``omega``, the workhorse tactic here, effective without
changing what anything means. A divisor that is a positive literal prints as
``/`` and ``%``, which on ``Int`` are Euclidean division and its remainder: for
a positive divisor those are floor division and its remainder exactly, and
``omega`` reasons about them where it knows nothing of ``Int.fdiv``. And a
family's natural values stay ``Nat`` (see below) and are cast to ``Int`` where
they are used as numbers, so that ``omega`` knows they are not negative without
being told. The one place the readings still part is division by zero:
``Int.fdiv x 0`` is ``0`` and Python raises, which :mod:`lanky.semantics`
records as a note.

*A bounded quantifier is an ``Int`` quantifier with guards.* ``Fin[n]`` prints
as ``∀ i : Int, 0 ≤ i → i < n → ...`` and not as ``∀ i : Fin n, ...``. The
``Fin`` form would be closer to the lanky type, but every arithmetic step then
carries a coercion ``(↑i : Nat)`` and a wraparound: ``i + 1`` in ``Fin n`` is not
``i + 1`` in the statement lanky means, and ``omega`` reasons about linear
arithmetic over ``Nat`` and ``Int`` rather than about coercions out of ``Fin``.
The guarded form says the same thing with nothing to unfold, so the goals the
tactic ladder sees are the goals it is good at.

*A family is a total function.* ``Fn[Fin[n], Nat]`` prints as ``Int → Nat``,
not as ``Fin n → Nat``, and an application of it used as a number is cast,
``(f i : Int)``. The bound lives in the guards of the quantifiers that apply
the family, so the printed statement constrains the family exactly where the
lanky statement does and leaves it unconstrained outside. That is sound exactly
as far as its premise goes: a statement that never mentions a point cannot
depend on its value. A statement that *does* mention one is a different matter,
and :func:`check_applications` is the premise made into a check. ``f(n)`` for an
``f : Fn[Fin[n], Nat]`` erases to an unrestricted ``f n``, which Lean is happy
to reason about and the lanky statement has no value for, so the printer
declines the whole statement (:exc:`UnsupportedTerm`) rather than proving
something about a point outside the domain. What "in bounds" means here is
"lanky can show it from the binders": an argument is checked as an affine form
against the bounds the ``Fin`` binders and the ``Nat`` sorts give, so
``off(r + 1)`` against ``Fn[Fin[n + 1], Nat]`` with ``r`` in ``Fin[n]`` goes
through and anything the affine reading cannot settle is declined rather than
assumed. Declining costs a proof at worst; assuming costs soundness. A family
over ``Nat`` erases to a function from ``Int`` as well, so its arguments have
to be shown non-negative in the same way, or be the natural value of another
family.

Three things follow from taking that seriously. An application chain is checked
level by level: ``f(i)(j)`` for a family of families erases to ``f i j``, so
``j`` has a domain to leave just as ``i`` does. Every expression a domain
carries is walked too, under the binders it sits in, because a ``Fin`` bound, a
nested family type and a refinement predicate are all elaborated by Lean the way
a body is, and an impossible hypothesis about a point the statement has no value
for proves anything. And a family whose *domain* is refined is declined where it
is applied: the erasure keeps nothing of the refinement, and affine arithmetic
over the binders cannot establish one.

A name has to mean in the printed source what it meant in Python, too. A
generator's first domain is evaluated before its binder exists, so the bound in
``all(i > 0 for i in Fin[i])`` is an outer ``i``; printed as a guard after the
binder it would be the binder itself, and the statement vacuous, so a binder
that captures a name its own domain mentions is declined.

An exponent is the one operand ``Int`` does not take: Lean's ``^`` on ``Int``
wants a ``Nat``. A literal is printed as it is, a ``Nat`` or ``Fin`` variable as
``e.toNat`` (which is ``e``, given ``0 ≤ e``), and a family's natural value
without its cast; anything else could be negative, where Python's ``**`` gives a
float, and is declined. A literal base is ascribed, ``(2 : Int) ^ m.toNat``:
with its variable only in the ``Nat`` exponent, nothing else would tell Lean
that ``1 - 2 ** m`` is integer arithmetic, and it would read a numeral with no
typed neighbour as a ``Nat``.

The printer is a recursive descent with Lean's own operator precedences, so the
emitted source is the source a Lean user would have written, and it is worth
reading on its own and not only as oracle input. It carries a scope, the lanky
type of every name bound around the subterm it prints, which is how it knows
that ``f i`` is a natural to cast and ``n`` a natural whose exponent form is
``n.toNat``.

*Mathlib mode.* Everything above is the default, and it is what every function
here prints unless asked for Mathlib (``mathlib=True``), which the Lean oracle
asks for when it runs in a Lake project with Mathlib (see
:mod:`lanky.mathlib`). The Mathlib dialect prints the core fragment exactly as
above, apart from one ascription described below, and declines less:

- ``Real`` and ``Complex`` are ``ℝ`` and ``ℂ``. A ``float`` literal is the
  exact rational number Python holds, ``(1 / 2 : ℝ)`` for ``0.5``, and a
  non-integral ``Fraction`` the same; a ``complex`` literal is
  ``(a + b * Complex.I : ℂ)``. A float is ascribed ``ℝ`` even when it is
  integral: ``2.0 ** n`` is float arithmetic in Python, and an unascribed
  ``2`` would make it natural arithmetic in Lean.
- True division is division in a field: ``x / y`` prints as ``(x : ℝ) / y``,
  or with ``ℂ`` when either side is complex, because Python's ``/`` on two
  integers is not integer division either. Lean's field division is total, so
  a divisor that may be zero is noted (:mod:`lanky.semantics`).
- An absolute value is ``|x|``, and ``‖z‖`` for a complex ``z``, which is the
  modulus Python's ``abs`` computes.
- ``exp``, ``log`` and ``sqrt`` (:class:`lanky.terms.Elementary`) are
  ``Real.exp``, ``Real.log`` and ``Real.sqrt``, and ``Complex.exp`` for a
  complex argument. A complex logarithm or square root is declined: ``cmath``
  reads the sign of a zero imaginary part to pick a side of the branch cut,
  so ``log(x * complex(-1, -0.0))`` is ``-πi`` at ``x = 1``, and Lean's
  complex numbers have no signed zero.
- A reduction over ``Fin`` binders is ``∑ i ∈ Finset.Ico (0 : ℤ) n, body``,
  with a guard or a refinement as ``with``. Its binder is an ``Int``, as a
  bounded quantifier's is, so the body is the same integer arithmetic. A sum
  over a domain with no bound, ``Nat``, is infinite and is declined.

What makes this more than a longer table is *coercion*. Lean elaborates a tree
of ``+``, ``-``, ``*`` and ``/`` by finding the largest type among its leaves
and casting every leaf to it, so ``x + n / 2`` with a real ``x`` would divide
the cast ``n`` in ``ℝ``. Every integer operation that is not a ring operation
is therefore kept out of such a tree: a floor division by a positive literal is
ascribed, ``(n / 2 : ℤ)``, which makes it a leaf the tree casts whole, and
``Int.fdiv`` and ``Int.fmod`` are applications, which are leaves already. The
ring operations commute with the cast, so an integer sum or product inside a
real one means the same thing either way. What each subterm is, an integer, a
real or a complex number, is read off the scope (:func:`_kind`), and a floor
division, a remainder or an order comparison over something that is not an
integer, or not real, is declined rather than printed with a meaning Python
does not give it. So is a ``Fin`` whose bound is not an integer, which the
tester walks as ``range(int(x))``.

The other half of coercion is a numeral with nothing around it to type it,
which Lean reads as a ``Nat``, as the core dialect's power base already shows.
A reduction is where the Mathlib dialect meets it: ``Finset.Ico 0 3`` would be
a set of naturals, and ``sum(i - 1 for i in Fin[3])`` a sum of truncated
differences, ``1`` where Python computes ``0``; and ``sum(1 for i in Fin[n])``
would be a natural, so that ``... - 3 >= 0`` holds in Lean at ``n = 0``. So the
lower bound is ascribed, ``(0 : ℤ)``, and so is a body that is an integer
numeral.
"""

from __future__ import annotations

from collections.abc import Iterator, Mapping
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Abs,
    Elementary,
    Exists,
    Forall,
    Sum,
    Var,
    conjuncts,
    free_variables,
    init_args,
    render,
)

__all__ = [
    "LeanStatement",
    "UnsupportedTerm",
    "check_applications",
    "dialect",
    "domain_guards",
    "is_natural",
    "lean_type",
    "print_lean",
    "statement_of",
]


#: Whether the printer is writing for a Lean session that has imported Mathlib.
#: The public functions take ``mathlib=`` and set it for the call; the private
#: ones read it, so that every helper a statement goes through prints in one
#: dialect without the flag being threaded through each of them.
_MATHLIB: ContextVar[bool] = ContextVar("lanky_lean_mathlib", default=False)


@contextmanager
def dialect(mathlib: bool | None) -> Iterator[None]:
    """Print in the Mathlib dialect, or in core Lean's, for the duration.

    ``None`` keeps whichever dialect is in effect, which is what a public
    function called from inside another one wants.
    """
    if mathlib is None:
        yield
        return
    token = _MATHLIB.set(bool(mathlib))
    try:
        yield
    finally:
        _MATHLIB.reset(token)


def _in_mathlib() -> bool:
    """Whether the dialect in effect is Mathlib's."""
    return _MATHLIB.get()


class UnsupportedTerm(NotImplementedError):
    """Raised for a term core Lean cannot express without Mathlib.

    Declining is the point. An oracle that emits source Lean rejects wastes a
    session and reports an elaboration error where the honest answer is "this
    statement is outside the fragment", so :meth:`LeanOracle.can_establish` asks
    the printer first and leaves such a fact to a weaker oracle.
    """


# {{{ precedences, as Lean has them

#: ``∀`` and ``∃`` extend as far to the right as they can.
_QUANT = 10
#: ``→``, right associative.
_ARROW = 20
_OR = 30
_AND = 35
_NOT = 40
#: ``=``, ``<``, ``≤`` and friends.
_CMP = 50
_ADD = 65
_MUL = 70
_POW = 75
#: Function application binds tighter than any operator.
_APP = 1024
_ATOM = 2048


def _parens(text: str, inner: int, outer: int) -> str:
    """Parenthesize when the printed operator binds more loosely than its context."""
    return f"({text})" if inner < outer else text


# }}}


# {{{ sorts and types

#: The scalar sorts core Lean has, and the Lean type a variable of each gets. A
#: natural is an ``Int`` whose non-negativity is a hypothesis (see
#: :func:`domain_guards`), so that its arithmetic is integer arithmetic.
_SORT_NAMES = {"Nat": "Int", "Int": "Int", "Bool": "Bool", "Prop": "Prop"}

#: The sorts Mathlib adds, as the Mathlib dialect prints them.
_MATHLIB_SORT_NAMES = {"Real": "ℝ", "Complex": "ℂ"}

#: The kinds of number a subterm can be (:func:`_kind`), smallest first: an
#: operation on two of them is carried out in the larger.
_NUMBER_KINDS = ("Int", "Real", "Complex")

#: The field each kind of number divides in, as the Mathlib dialect prints it.
_FIELDS = {"Int": "ℝ", "Real": "ℝ", "Complex": "ℂ"}

#: What the printer knows about the names bound around a subterm: the lanky
#: type of each, read off the binder that bound it.
_Types = Mapping[str, Any]


def lean_type(obj: Any, mathlib: bool | None = None) -> str:
    """The Lean type of a variable of a lanky type.

    A natural is an ``Int`` here, and so is a point of ``Fin[n]``: their bounds
    are hypotheses (:func:`domain_guards`), and their arithmetic is integer
    arithmetic (see the module docstring). ``Real`` and ``Complex`` are ``ℝ``
    and ``ℂ`` in the Mathlib dialect (``mathlib=True``), and are declined in
    core Lean's.

    A family is a function from ``Int``, and its values keep their own type:
    ``Fn[Fin[n], Nat]`` is ``Int → Nat``, and an application of it that is used
    as a number is cast to ``Int`` where it stands (see :func:`_render`). A
    family whose domain is itself a family needs brackets around the domain,
    because ``→`` is right associative: ``Fn[Fn[Fin[n], Nat], Nat]`` is
    ``(Int → Nat) → Nat``, and without the brackets it would read as the
    two-argument ``Int → Int → Nat``, which is a different type and the one a
    family of families already prints as.
    """
    with dialect(mathlib):
        return _lean_type(obj)


def _lean_type(obj: Any) -> str:
    """:func:`lean_type`, in the dialect in effect."""
    if isinstance(obj, Sort):
        name = _SORT_NAMES.get(obj.name)
        if name is None and _in_mathlib():
            name = _MATHLIB_SORT_NAMES.get(obj.name)
        if name is None:
            raise UnsupportedTerm(
                f"the sort {obj.name} has no core-Lean counterpart "
                "(Real needs Mathlib)"
            )
        return name
    if isinstance(obj, FinType):
        return "Int"
    if isinstance(obj, FnType):
        domain = _lean_type(obj.domain)
        if isinstance(_unrefined(obj.domain), FnType):
            domain = f"({domain})"
        return f"{domain} → {_value_type(obj.codomain)}"
    if isinstance(obj, Refined):
        return _lean_type(obj.base)
    raise UnsupportedTerm(f"cannot print the type {obj!r} in Lean")


def is_natural(obj: Any) -> bool:
    """Whether the inhabitants of a lanky type are naturals.

    ``Nat``, ``Fin[n]`` and a refinement of either. A variable of such a type
    prints as an ``Int`` with ``0 ≤ x`` among its hypotheses, which is what a
    tactic script has to trade back for a ``Nat`` before it can induce on it.
    """
    base = _unrefined(obj)
    return isinstance(base, FinType) or (isinstance(base, Sort) and base.name == "Nat")


def _value_type(obj: Any) -> str:
    """The Lean type of a family's values; a natural value stays a ``Nat``.

    A value is never bound by a binder, so there is nowhere to state its
    non-negativity as a hypothesis, and ``Nat`` says it for free: ``omega``
    knows that ``(f i : Int)`` is not negative when ``f i`` is a ``Nat``.
    Every application used as a number is cast to ``Int``, so the arithmetic is
    integer arithmetic all the same.
    """
    if is_natural(obj):
        return "Nat"
    return _lean_type(obj)


def _unrefined(obj: Any) -> Any:
    """The type a refinement refines, or ``obj`` itself; a refinement prints as its base."""
    while isinstance(obj, Refined):
        obj = obj.base
    return obj


def _scalar_bounds(domain: Any) -> tuple[Any, Any]:
    """What a binder's domain says about the value of its variable.

    ``(lower, upper)`` as terms, with ``None`` where there is no bound. A
    refinement is read through to its base: its propositions may well pin the
    variable down further, but only the base is a bound this module can use
    without a solver.
    """
    if isinstance(domain, Refined):
        return _scalar_bounds(domain.base)
    if isinstance(domain, FinType):
        return 0, domain.bound - 1
    if isinstance(domain, Sort) and domain.name == "Nat":
        return 0, None
    return None, None


def domain_guards(
    var: Var, domain: Any, types: _Types | None = None, mathlib: bool | None = None
) -> list[str]:
    """The propositions a binder's domain imposes on its variable.

    ``Nat`` gives ``0 ≤ n`` and ``Fin[n]`` gives ``0 ≤ i`` and ``i < n``,
    because both print as ``Int`` (:func:`lean_type`); a refinement gives its
    base's guards and then its own propositions; any other sort gives nothing,
    because the Lean type already says it.

    ``types`` gives the lanky type of every name bound around the binder (see
    :func:`_render`). A ``Fin`` bound is read with those names, and a
    refinement's propositions with the variable itself added, since they are
    about that variable. ``mathlib`` picks the dialect they are printed in.
    """
    with dialect(mathlib):
        return _domain_guards(var, domain, types or {})


def _domain_guards(var: Var, domain: Any, types: _Types) -> list[str]:
    """:func:`domain_guards`, in the dialect in effect."""
    name = _render(var, _CMP + 1, types)
    if isinstance(domain, Sort) and domain.name == "Nat":
        return [f"0 ≤ {name}"]
    if isinstance(domain, FinType):
        if _in_mathlib():
            _require_integer_bound(domain, types)
        return [f"0 ≤ {name}", f"{name} < {_render(domain.bound, _CMP + 1, types)}"]
    if isinstance(domain, Refined):
        inner = {**types, var.name: domain}
        return _domain_guards(var, domain.base, types) + [
            _render_prop(p, _ARROW + 1, inner) for p in domain.props
        ]
    return []


# }}}


# {{{ expressions

#: lanky comparison operators and the Lean relations that mean the same.
_RELATIONS = {
    "==": "=",
    "!=": "≠",
    "<": "<",
    "<=": "≤",
    ">": ">",
    ">=": "≥",
}


def _integral(value: Any) -> Any:
    """An integral ``Fraction`` as the ``int`` it equals; anything else as it is.

    ``Fraction(2, 1)`` prints as the numeral ``2``, so every rule that treats
    an integer literal specially has to see it as one: the ``Int`` ascription
    of a power's base, a literal exponent, a positive literal divisor, and a
    negative summand read back as a subtraction. The base is the one that
    matters: without its ascription ``1 - Fraction(2, 1) ** n >= 0`` printed
    over ``Nat``, where Lean proves it with truncated subtraction and Python
    refutes it at ``n = 1``. pymbolic's operators refuse a ``Fraction``
    operand, so such a literal comes only from a term built node by node, by
    hand or by a plugin.
    """
    if isinstance(value, Fraction) and value.denominator == 1:
        return int(value)
    return value


def _render_number(value: Any) -> str:
    """Print a numeric literal, refusing the ones that need a field."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    if _in_mathlib() and isinstance(value, Fraction | float | complex):
        return _field_literal(value)
    if isinstance(value, Fraction):
        if value.denominator == 1:
            return str(value.numerator)
        raise UnsupportedTerm(
            f"the rational literal {value} needs a field, which is Mathlib"
        )
    if isinstance(value, float):
        raise UnsupportedTerm(
            f"the floating-point literal {value} has no core-Lean sort "
            "(Real needs Mathlib)"
        )
    raise UnsupportedTerm(f"cannot print the literal {value!r} in Lean")


def _rational_text(value: Fraction) -> str:
    """``p / q``, or ``p`` when the rational is an integer, with no ascription."""
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator} / {value.denominator}"


def _exact(value: float) -> Fraction:
    """The rational number a finite ``float`` is, refusing an infinity or a NaN."""
    if value != value or value in (float("inf"), float("-inf")):
        raise UnsupportedTerm(f"the floating-point value {value} is not a real number")
    return Fraction(value)


def _field_literal(value: Fraction | float | complex) -> str:
    """Print a rational, float or complex literal in the Mathlib dialect.

    A float is the dyadic rational Python holds, not the decimal it was
    written as: ``0.1`` is ``3602879701896397 / 36028797018963968``, which is
    what the file computes with. It is ascribed ``ℝ`` whatever its value, since
    a bare integral numeral would take the type of its neighbours, ``Nat`` among
    them (see the module docstring). A complex literal is its two parts around
    ``Complex.I``.
    """
    if isinstance(value, complex):
        real, imaginary = _exact(value.real), _exact(value.imag)
        sign = "-" if imaginary < 0 else "+"
        return (
            f"({_rational_text(real)} {sign} {_rational_text(abs(imaginary))} "
            "* Complex.I : ℂ)"
        )
    if isinstance(value, float):
        value = _exact(value)
    return f"({_rational_text(value)} : ℝ)"


def _negated(child: Any) -> tuple[bool, Any] | None:
    """Recognize ``(-1) * x`` so that a sum of it prints as a subtraction."""
    child = _integral(child)
    if isinstance(child, prim.Product) and child.children:
        first = _integral(child.children[0])
        if isinstance(first, int) and first == -1:
            rest = child.children[1:]
            if len(rest) == 1:
                return True, rest[0]
            return True, prim.Product(rest)
    if isinstance(child, int) and not isinstance(child, bool) and child < 0:
        return True, -child
    return None


def _render_sum(expr: prim.Sum, types: _Types) -> str:
    """Print an addition, reading a negated summand back as a subtraction.

    Subtraction is not a node: pymbolic builds ``a - b`` as a sum with ``(-1) *
    b`` in it, and it prints as the ``-`` it was written as. Every operand is an
    ``Int`` (see the module docstring), so this is integer subtraction, which is
    what the property tester computes too; association does not matter to it,
    which is why the flattened sum can be printed as it stands.
    """
    parts = []
    for position, child in enumerate(expr.children):
        negation = _negated(child)
        if negation is None:
            text = _render(child, _ADD, types)
            parts.append(text if position == 0 else f" + {text}")
        else:
            text = _render(negation[1], _MUL, types)
            parts.append(f"-{text}" if position == 0 else f" - {text}")
    return "".join(parts)


def _is_positive_literal(expr: Any) -> bool:
    """Whether a divisor is an integer literal that is plainly above zero."""
    expr = _integral(expr)
    return isinstance(expr, int) and not isinstance(expr, bool) and expr > 0


def _render_division(expr: prim.FloorDiv | prim.Remainder, outer: int, types: _Types) -> str:
    """Print ``//`` or ``%`` with Python's rounding, which is floor rounding.

    ``Int.fdiv`` and ``Int.fmod`` round toward negative infinity as Python's
    ``//`` and ``%`` do, so they are what a divisor gets whose sign Lean cannot
    see. A positive literal divisor prints as ``/`` and ``%`` instead. Lean's
    ``Int`` division is Euclidean (``Int.ediv`` and ``Int.emod``), which for a
    positive divisor is floor division and its remainder exactly, and ``omega``
    reasons about it where it knows nothing of ``Int.fdiv``. A zero divisor
    prints as ``Int.fdiv x 0``, which Lean evaluates to ``0`` where Python
    raises; :mod:`lanky.semantics` records that gap.

    In the Mathlib dialect both operands have to be integers, and the literal
    form is ascribed, ``(n / 2 : ℤ)``: next to a real it would otherwise be
    real division of the cast ``n`` (see the module docstring).
    """
    floor = isinstance(expr, prim.FloorDiv)
    if _in_mathlib():
        _require_integers(expr, types)
    if _is_positive_literal(expr.denominator):
        symbol = "/" if floor else "%"
        text = (
            f"{_render(expr.numerator, _MUL, types)} {symbol} "
            f"{_render(expr.denominator, _MUL + 1, types)}"
        )
        if _in_mathlib():
            # a leaf of type ℤ, which a real tree around it casts whole
            return f"({text} : ℤ)"
        return _parens(text, _MUL, outer)
    function = "Int.fdiv" if floor else "Int.fmod"
    text = (
        f"{function} {_render(expr.numerator, _ATOM, types)} "
        f"{_render(expr.denominator, _ATOM, types)}"
    )
    return _parens(text, _APP, outer)


def _application_type(expr: Any, types: _Types) -> Any:
    """The lanky type of an application's value, when its family is in scope.

    ``f(i)(j)`` for an ``f : Fn[Fin[n], Fn[Fin[m], Nat]]`` is a ``Nat``, and
    ``f(i)`` alone is a family. ``None`` when the head is not a family the
    statement binds, as in an open term, or when the chain applies it more
    often than its type allows, which :func:`check_applications` refuses.
    """
    found = _spine(expr)
    if found is None:
        return None
    name, arguments = found
    current = types.get(name)
    for _ in arguments:
        base = _unrefined(current)
        if not isinstance(base, FnType):
            return None
        current = base.codomain
    return current


def _application_text(expr: prim.Call | prim.Subscript, types: _Types) -> str:
    """Print an application as Lean writes one, ``f a b``, with no cast."""
    if isinstance(expr, prim.Call):
        head, arguments = expr.function, tuple(expr.parameters)
    else:
        head = expr.aggregate
        arguments = expr.index if isinstance(expr.index, tuple) else (expr.index,)
    args = " ".join(_render(arg, _ATOM, types) for arg in arguments)
    return f"{_render(head, _APP, types)} {args}"


def _render_exponent(expr: Any, types: _Types) -> str:
    """Print an exponent, which Lean's ``^`` on ``Int`` takes as a ``Nat``.

    A non-negative literal elaborates as a ``Nat`` as it stands. A natural
    variable is an ``Int`` in the printed statement, and ``n.toNat`` is ``n``
    given the ``0 ≤ n`` among its hypotheses. A family's natural value is a
    ``Nat`` already and is printed without its cast. Anything else could be
    negative, where Python's ``**`` answers a float and Lean has no ``^`` at
    all, so it is declined.

    Raises:
        UnsupportedTerm: For an exponent that is not one of the three.
    """
    expr = _integral(expr)
    if isinstance(expr, int) and not isinstance(expr, bool) and expr >= 0:
        return str(expr)
    if isinstance(expr, Var | prim.Variable) and is_natural(types.get(expr.name)):
        return f"{expr.name}.toNat"
    if isinstance(expr, prim.Call | prim.Subscript) and is_natural(
        _application_type(expr, types)
    ):
        return _application_text(expr, types)
    raise UnsupportedTerm(
        f"the exponent {render(expr)} is not a literal, a natural variable or a "
        "natural value: Lean's ^ on Int takes a Nat, and a negative exponent is "
        "a float in Python"
    )


def _render_base(expr: Any, types: _Types) -> str:
    """Print the base of a power, ascribing ``Int`` to a literal one.

    Lean gives a numeral the type its neighbours have, and ``Nat`` when none
    of them has one. A variable that appears only in an exponent is printed as
    ``n.toNat``, a ``Nat``, which gives the base no type at all, so ``1 - 2 **
    m >= 0`` would elaborate as a statement about ``Nat``, where the
    subtraction truncates and the claim is true, while Python computes ``-1``
    at ``m = 1``. Ascribing the literal base, ``(2 : Int) ^ m.toNat``, gives
    every numeral around it the type ``Int``. Any other base is typed already:
    it has a variable, a cast or a call in it that is an ``Int``, or it is a
    power whose own base this rule has typed. An integral ``Fraction`` is the
    ``int`` it equals (:func:`_integral`), and is ascribed the same way.
    """
    expr = _integral(expr)
    if isinstance(expr, int) and not isinstance(expr, bool):
        return f"({expr} : Int)"
    return _render(expr, _POW + 1, types)


# {{{ the Mathlib dialect: kinds of number, and what only it prints


def _sort_kind(obj: Any) -> str:
    """What a variable of a lanky type is as a number: ``Int``, ``Real`` or ``Complex``.

    A natural, an integer and a point of ``Fin`` are all integers (see the
    module docstring). ``Prop`` for a truth value, and ``Int`` for anything
    this cannot read, such as a family used without being applied, which is
    not a number in any case and meets no operation that would care.
    """
    base = _unrefined(obj)
    if isinstance(base, Sort):
        if base.name in ("Real", "Complex"):
            return base.name
        if base.name in ("Bool", "Prop"):
            return "Prop"
    return "Int"


def _widest(kinds: Any) -> str:
    """The largest kind of number among ``kinds``, which an operation on them is in."""
    found = [kind for kind in kinds if kind in _NUMBER_KINDS]
    return max(found, key=_NUMBER_KINDS.index) if found else "Int"


def _kind(expr: Any, types: _Types) -> str:
    """What ``expr`` is as a number: ``Int``, ``Real`` or ``Complex``, or ``Prop``.

    The printer needs to know where the coercions Lean would insert could
    change a meaning (see the module docstring), and this is how it knows: a
    variable is what its binder says, a literal what Python made it, an
    arithmetic operation the widest of its operands, a true division at least
    real, and an application what its family's codomain is. A name nothing in
    scope binds, a free variable of an open term, counts as an integer, which
    is how core Lean's printer has always read it.
    """
    if isinstance(expr, bool):
        return "Prop"
    if isinstance(expr, Var | prim.Variable):
        return _sort_kind(types.get(expr.name))
    expr = _integral(expr)
    if isinstance(expr, int):
        return "Int"
    if isinstance(expr, Fraction | float):
        return "Real"
    if isinstance(expr, complex):
        return "Complex"
    if isinstance(expr, prim.Comparison | prim.LogicalAnd | prim.LogicalOr | prim.LogicalNot):
        return "Prop"
    if isinstance(expr, Forall | Exists):
        return "Prop"
    if isinstance(expr, prim.Sum | prim.Product):
        return _widest(_kind(child, types) for child in expr.children)
    if isinstance(expr, prim.Power):
        return _widest([_kind(expr.base, types)])
    if isinstance(expr, prim.FloorDiv | prim.Remainder):
        return "Int"
    if isinstance(expr, prim.Quotient):
        return _widest(["Real", _kind(expr.numerator, types), _kind(expr.denominator, types)])
    if isinstance(expr, Abs):
        return "Int" if _kind(expr.operand, types) == "Int" else "Real"
    if isinstance(expr, Elementary):
        argument = _kind(expr.argument, types)
        return "Complex" if argument == "Complex" and expr.function == "exp" else "Real"
    if isinstance(expr, Sum):
        inner = dict(types)
        for var, domain in expr.binders:
            inner[var.name] = domain
        return _kind(expr.body, inner)
    if isinstance(expr, prim.Call | prim.Subscript):
        return _sort_kind(_application_type(expr, types))
    return "Int"


def _require_integers(expr: prim.FloorDiv | prim.Remainder, types: _Types) -> None:
    """Refuse a floor division or a remainder whose operands are not both integers.

    Python's ``//`` and ``%`` take floats as well, where ``x // 1`` is the floor
    of ``x`` as a float; Lean's ``Int.fdiv`` and ``Int.fmod`` do not, and
    printing them over a cast ``x`` would be a different operation.
    """
    for operand in (expr.numerator, expr.denominator):
        kind = _kind(operand, types)
        if kind != "Int":
            raise UnsupportedTerm(
                f"{render(expr)} is floor division or a remainder of a {kind} "
                f"operand ({render(operand)}), which Python computes in floating "
                "point and Lean's Int.fdiv and Int.fmod do not take"
            )


def _require_integer_bound(domain: FinType, types: _Types) -> None:
    """Refuse a ``Fin`` whose bound is not an integer.

    The tester walks ``Fin[x]`` as ``range(int(x))``, which truncates a real
    ``x``, while the guard ``i < x`` over a cast ``i`` does not: ``Fin[2.5]``
    has two points in Python and three in Lean. Core Lean cannot print a real
    bound at all; the Mathlib dialect could, and must not.
    """
    kind = _kind(domain.bound, types)
    if kind != "Int":
        raise UnsupportedTerm(
            f"{domain} has a {kind} bound, which Python truncates to an integer "
            "and Lean would compare the index with as it stands"
        )


def _render_quotient(expr: prim.Quotient, outer: int, types: _Types) -> str:
    """Print true division as division in ``ℝ``, or in ``ℂ`` when a side is complex.

    Python's ``/`` never divides integers as integers: ``7 / 2`` is ``3.5``.
    Ascribing the numerator to the field makes Lean divide there too, since
    the division is then in the widest type among its leaves.
    """
    kind = _widest([_kind(expr.numerator, types), _kind(expr.denominator, types)])
    text = (
        f"({_render(expr.numerator, _QUANT, types)} : {_FIELDS[kind]}) / "
        f"{_render(expr.denominator, _MUL + 1, types)}"
    )
    return _parens(text, _MUL, outer)


def _render_abs(expr: Abs, types: _Types) -> str:
    """Print ``|x|``, or ``‖z‖`` for a complex ``z``, the modulus Python's ``abs`` gives."""
    inner = _render(expr.operand, _QUANT, types)
    if _kind(expr.operand, types) == "Complex":
        return f"‖{inner}‖"
    if "|" in inner:
        # bars nest ambiguously, so an inner absolute value gets brackets
        inner = f"({inner})"
    return f"|{inner}|"


#: What each elementary function is called in Mathlib, for a real argument and
#: for a complex one; ``None`` where lanky does not print it.
_ELEMENTARY = {
    "exp": ("Real.exp", "Complex.exp"),
    "log": ("Real.log", None),
    "sqrt": ("Real.sqrt", None),
}


def _render_elementary(expr: Elementary, outer: int, types: _Types) -> str:
    """Print ``exp``, ``log`` or ``sqrt`` as Mathlib's function of the argument's kind.

    An integer argument is cast to ``ℝ`` by Lean where it is applied, which is
    what Python's ``math.exp(n)`` does too. The complex logarithm and square
    root are declined: ``cmath.log`` and ``cmath.sqrt`` read the sign of a
    zero imaginary part to choose a side of their branch cut, so that
    ``cmath.log(complex(-1, -0.0))`` is ``-πi`` and ``cmath.log(complex(-1,
    0.0))`` is ``πi``, while Lean's complex numbers have no signed zero and
    ``Complex.log (-1)`` is ``π * I`` from either side. The complex
    exponential is entire, and has no cut to disagree about.
    """
    real, complex_ = _ELEMENTARY[expr.function]
    name = complex_ if _kind(expr.argument, types) == "Complex" else real
    if name is None:
        kind = "logarithm" if expr.function == "log" else "square root"
        raise UnsupportedTerm(
            f"{render(expr)} is a complex {kind}, whose branch cut Python and Lean "
            "do not draw the same way: cmath picks a side of it by the sign of a "
            "zero imaginary part, and Lean's complex numbers have no signed zero"
        )
    return _parens(f"{name} {_render(expr.argument, _ATOM, types)}", _APP, outer)


def _render_reduction(expr: Sum, outer: int, types: _Types) -> str:
    """Print a reduction as Mathlib's ``∑``, one ``Finset.Ico`` per binder.

    ``Fin[n]`` is ``Finset.Ico (0 : ℤ) n``, so the binder is an integer as a
    quantifier's is, and ``n`` below ``0`` gives the empty sum Python's
    ``range`` gives. The ascription is what makes the binder an integer when
    the bound is a literal, and a body that is an integer numeral is ascribed
    too, which makes the sum an integer: without them Lean reads both as
    naturals, whose subtraction truncates (see the module docstring). A
    refinement of the domain, and the generator's guard on the last binder,
    filter it with ``with``. The body extends as far right as it can, so a sum
    that is an operand is bracketed.

    Raises:
        UnsupportedTerm: For a binder over anything but ``Fin`` or a
            refinement of it: a sum over ``Nat`` has no finite extent.
    """
    layers = [dict(types)]
    for var, domain in expr.binders:
        if not isinstance(_unrefined(domain), FinType):
            raise UnsupportedTerm(
                f"{render(expr)} sums over {domain}, which is not a Fin: Mathlib's "
                "∑ is over a finite set, and the sum has no finite extent"
            )
        layers.append({**layers[-1], var.name: domain})
    inner = layers[-1]
    body = _integral(expr.body)
    if isinstance(body, int) and not isinstance(body, bool):
        text = f"({body} : ℤ)"
    else:
        text = _render(expr.body, _ADD + 1, inner)
    guards = list(conjuncts(expr.guard))
    for position in reversed(range(len(expr.binders))):
        var, domain = expr.binders[position]
        _require_integer_bound(_unrefined(domain), layers[position])
        bound = _render(_unrefined(domain).bound, _ATOM, layers[position])
        conditions = []
        refined = domain
        while isinstance(refined, Refined):
            conditions = [
                _render_prop(p, _AND + 1, layers[position + 1]) for p in refined.props
            ] + conditions
            refined = refined.base
        if position == len(expr.binders) - 1:
            conditions += [_render_prop(guard, _AND + 1, inner) for guard in guards]
        condition = f" with {' ∧ '.join(conditions)}" if conditions else ""
        text = f"∑ {var.name} ∈ Finset.Ico (0 : ℤ) {bound}{condition}, {text}"
    return _parens(text, _QUANT, outer)


# }}}


def _render_quantifier(expr: Forall | Exists, outer: int, types: _Types) -> str:
    """Print ``∀`` or ``∃`` one binder at a time, each guard next to its binder.

    Nesting the binders rather than grouping them keeps every guard beside the
    variable it constrains, which is how a Lean user writes it and how the
    oracle's ``intro`` list lines up with the statement. Each binder's guards
    are printed with the binders before it in scope, and the body and the
    generator's guard with all of them.
    """
    universal = isinstance(expr, Forall)
    word = "∀" if universal else "∃"
    guards = list(conjuncts(expr.guard))
    layers = [dict(types)]
    for var, domain in expr.binders:
        layers.append({**layers[-1], var.name: domain})
    inner = layers[-1]
    if not expr.binders:
        # A closed statement whose hypotheses are its only parameters: there is
        # no variable to quantify, but the guard is still the antecedent and
        # dropping it would print a strictly stronger claim than was written.
        text = _render_prop(expr.body, _ARROW if universal else _AND + 1, inner)
        for guard in reversed(guards):
            joiner = "→" if universal else "∧"
            text = f"{_render_prop(guard, _ARROW + 1, inner)} {joiner} {text}"
        if not guards:
            return _render_prop(expr.body, outer, inner)
        return _parens(text, _ARROW if universal else _AND, outer)
    # A universal's body is the rightmost thing in the formula, and an arrow is
    # right associative, so it never needs brackets; an existential's body sits
    # to the right of a conjunction, where a quantifier would swallow the rest.
    text = _render_prop(expr.body, _QUANT if universal else _AND + 1, inner)
    for position in reversed(range(len(expr.binders))):
        var, domain = expr.binders[position]
        conditions = _domain_guards(var, domain, layers[position])
        if position == len(expr.binders) - 1:
            conditions += [_render_prop(guard, _ARROW + 1, inner) for guard in guards]
        if universal:
            for condition in reversed(conditions):
                text = f"{condition} → {text}"
        else:
            for condition in reversed(conditions):
                text = f"{condition} ∧ {text}"
        text = f"{word} {var.name} : {_lean_type(domain)}, {text}"
    return _parens(text, _QUANT, outer)


def _render_prop(expr: Any, outer: int, types: _Types) -> str:
    """Print a term that stands where Lean expects a proposition.

    The one term that reads differently in the two positions is a Boolean
    constant. ``-> 1 == 2`` is answered by Python while the annotation is
    evaluated, so the statement lanky holds is the ``bool`` ``False``, and the
    proposition that says so in Lean is ``False`` and not the ``Bool`` literal
    ``false``: the literal elaborates as a proposition only through the
    ``Bool``-to-``Prop`` coercion, which is a second reading of the statement
    where lanky means exactly one. In a value position, as an operand of a
    comparison, ``false`` is still what is printed.
    """
    if isinstance(expr, bool):
        return "True" if expr else "False"
    return _render(expr, outer, types)


def _render(expr: Any, outer: int, types: _Types) -> str:
    """Print ``expr`` as Lean source, parenthesized for a context of ``outer``.

    ``types`` maps the names bound around ``expr`` to their lanky types. It is
    what tells an application of a family with natural values, which is cast
    to ``Int`` where it is used as a number, from anything else; a name it does
    not know, a free variable of an open term, is printed as it stands.
    """
    if isinstance(expr, Var | prim.Variable):
        return expr.name
    expr = _integral(expr)
    if isinstance(expr, int | float | Fraction | bool | complex):
        text = _render_number(expr)
        # an ascribed literal is bracketed already, whatever its sign
        atomic = text.startswith("(") or not _is_negative(expr)
        return _parens(text, _ATOM if atomic else _ADD, outer)
    if expr is None:
        raise UnsupportedTerm("cannot print an empty term in Lean")
    if isinstance(expr, Forall | Exists):
        return _render_quantifier(expr, outer, types)
    if isinstance(expr, Sum):
        if _in_mathlib():
            return _render_reduction(expr, outer, types)
        raise UnsupportedTerm(
            "a reduction needs Finset.sum, which is Mathlib; core Lean cannot "
            "state it"
        )
    if isinstance(expr, Abs):
        if _in_mathlib():
            return _render_abs(expr, types)
        raise UnsupportedTerm(
            "an absolute value needs the abs of an ordered ring, which is Mathlib"
        )
    if isinstance(expr, Elementary):
        if _in_mathlib():
            return _render_elementary(expr, outer, types)
        raise UnsupportedTerm(
            f"{expr.function} needs Real.{expr.function}, which is Mathlib"
        )
    if isinstance(expr, prim.Comparison):
        relation = _RELATIONS.get(expr.operator)
        if relation is None:
            raise UnsupportedTerm(f"unknown comparison operator {expr.operator!r}")
        if (
            _in_mathlib()
            and expr.operator not in ("==", "!=")
            and "Complex" in (_kind(expr.left, types), _kind(expr.right, types))
        ):
            raise UnsupportedTerm(
                f"{render(expr)} orders complex numbers, which Python refuses "
                "and Mathlib orders only under a scoped instance"
            )
        text = (
            f"{_render(expr.left, _CMP + 1, types)} {relation} "
            f"{_render(expr.right, _CMP + 1, types)}"
        )
        return _parens(text, _CMP, outer)
    if isinstance(expr, prim.LogicalAnd):
        text = " ∧ ".join(_render_prop(child, _AND + 1, types) for child in expr.children)
        return _parens(text, _AND, outer)
    if isinstance(expr, prim.LogicalOr):
        text = " ∨ ".join(_render_prop(child, _OR + 1, types) for child in expr.children)
        return _parens(text, _OR, outer)
    if isinstance(expr, prim.LogicalNot):
        return _parens(f"¬{_render_prop(expr.child, _APP, types)}", _NOT, outer)
    if isinstance(expr, prim.Sum):
        return _parens(_render_sum(expr, types), _ADD, outer)
    if isinstance(expr, prim.Product):
        text = " * ".join(_render(child, _MUL + 1, types) for child in expr.children)
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.FloorDiv | prim.Remainder):
        return _render_division(expr, outer, types)
    if isinstance(expr, prim.Quotient):
        if _in_mathlib():
            return _render_quotient(expr, outer, types)
        raise UnsupportedTerm(
            "true division needs a field, which is Mathlib; use // for the "
            "floor division Nat and Int have"
        )
    if isinstance(expr, prim.Power):
        text = f"{_render_base(expr.base, types)} ^ {_render_exponent(expr.exponent, types)}"
        return _parens(text, _POW, outer)
    if isinstance(expr, prim.Call | prim.Subscript):
        text = _application_text(expr, types)
        if is_natural(_application_type(expr, types)):
            # A natural value is a Nat in Lean (see _value_type); used as a
            # number it is cast, so that its arithmetic is integer arithmetic.
            return f"({text} : Int)"
        return _parens(text, _APP, outer)
    raise UnsupportedTerm(f"cannot print {type(expr).__name__} in Lean: {expr!r}")


def _is_negative(value: Any) -> bool:
    """Whether a literal needs parentheses where an operand is expected."""
    return isinstance(value, int | float | Fraction) and not isinstance(value, bool) and value < 0


def print_lean(expr: Any, mathlib: bool | None = None) -> str:
    """Render a lanky term as one Lean 4 proposition.

    ``mathlib=True`` prints in the Mathlib dialect (see the module docstring),
    for a session that has imported Mathlib.

    Raises:
        UnsupportedTerm: If the term leaves the fragment of the dialect, or
            applies a family outside the domain it declares
            (:func:`check_applications`).
    """
    with dialect(mathlib):
        check_applications(expr)
        return _render_prop(expr, _QUANT, {})


# }}}


# {{{ applications of a family, and the domain it declares

#: The key an affine form keeps its constant term under; no variable is named "".
_CONSTANT = ""

#: How many bounds one argument may be resolved through before giving up.
_SUBSTITUTIONS = 16


def _affine(expr: Any) -> dict[str, int] | None:
    """``expr`` as ``{variable: coefficient}`` plus a constant, or ``None``.

    Affine is as far as this goes, and far enough: an index expression is
    ``r + 1`` or ``2 * i`` or ``n - 1``, and anything else (a division, a
    family application, a product of two variables) is not something the check
    can reason about, so it answers ``None`` and the caller declines. An
    integral ``Fraction`` is the integer it equals (:func:`_integral`), as it
    is where it is printed.
    """
    if isinstance(expr, bool):
        return None
    expr = _integral(expr)
    if isinstance(expr, int):
        return {_CONSTANT: expr}
    if isinstance(expr, Var | prim.Variable):
        return {_CONSTANT: 0, expr.name: 1}
    if isinstance(expr, prim.Sum):
        total: dict[str, int] = {_CONSTANT: 0}
        for child in expr.children:
            part = _affine(child)
            if part is None:
                return None
            total = _add(total, part)
        return total
    if isinstance(expr, prim.Product):
        total = {_CONSTANT: 1}
        for child in expr.children:
            part = _affine(child)
            if part is None or not (_is_constant(total) or _is_constant(part)):
                return None
            total = (
                _scale(part, total[_CONSTANT])
                if _is_constant(total)
                else _scale(total, part[_CONSTANT])
            )
        return total
    return None


def _add(left: dict[str, int], right: dict[str, int]) -> dict[str, int]:
    """Sum two affine forms."""
    total = dict(left)
    for name, coefficient in right.items():
        total[name] = total.get(name, 0) + coefficient
    return total


def _scale(form: dict[str, int], factor: int) -> dict[str, int]:
    """Multiply an affine form by an integer."""
    return {name: coefficient * factor for name, coefficient in form.items()}


def _is_constant(form: dict[str, int]) -> bool:
    """Whether the form has no variable left with a nonzero coefficient."""
    return all(value == 0 for name, value in form.items() if name != _CONSTANT)


@dataclass
class _Scope:
    """What is in scope while a statement's applications are checked.

    ``lower`` and ``upper`` are affine forms, so the upper bound of an ``i`` in
    ``Fin[n + 1]`` is ``n``, itself in terms of a variable with bounds of its
    own. ``families`` is the parameters whose sort is a family over an index
    type: those, and only those, have a domain to leave.
    """

    lower: dict[str, dict[str, int]] = field(default_factory=dict)
    upper: dict[str, dict[str, int]] = field(default_factory=dict)
    families: dict[str, FnType] = field(default_factory=dict)

    def extended(self, binders: Any) -> _Scope:
        """This scope with the binders of one quantifier added."""
        out = _Scope(dict(self.lower), dict(self.upper), dict(self.families))
        for var, domain in binders:
            out.bind(var.name, domain)
        return out

    def bind(self, name: str, domain: Any) -> None:
        """Record what one binder's domain says about its variable.

        Whatever an outer binder of the same name said is dropped first: an
        inner binder shadows it, and carrying the old bounds over would be
        reasoning about the wrong variable.
        """
        base = domain.base if isinstance(domain, Refined) else domain
        self.lower.pop(name, None)
        self.upper.pop(name, None)
        self.families.pop(name, None)
        if isinstance(base, FnType):
            self.families[name] = base
            return
        low, high = _scalar_bounds(domain)
        for bound, table in ((low, self.lower), (high, self.upper)):
            form = None if bound is None else _affine(bound)
            if form is not None:
                table[name] = form


def _resolve(form: dict[str, int], scope: _Scope, maximize: bool) -> int | None:
    """The largest (or smallest) value an affine form can take, as an integer.

    Each variable is replaced by the bound that pushes the form the way this
    call wants it: an upper bound for a positive coefficient when maximizing, a
    lower bound for a negative one, and the other way round when minimizing.
    The bounds are affine too, so the substitution can introduce a variable of
    its own (the ``n`` in ``i <= n + 1 - 1``), which is why this is a loop; a
    variable with no bound in the direction that is needed means the form is
    unbounded as far as lanky can tell, and ``None`` says so.
    """
    form = dict(form)
    for _ in range(_SUBSTITUTIONS):
        name = next(
            (
                key
                for key, value in form.items()
                if key != _CONSTANT and value != 0
            ),
            None,
        )
        if name is None:
            return form[_CONSTANT]
        coefficient = form[name]
        wants_upper = (coefficient > 0) == maximize
        bound = (scope.upper if wants_upper else scope.lower).get(name)
        if bound is None:
            return None
        form[name] = 0
        form = _add(form, _scale(bound, coefficient))
    return None


def _fits(argument: Any, domain: FinType, scope: _Scope) -> bool:
    """Whether ``argument`` is a point of ``domain`` for every value in scope.

    Two obligations, both discharged by affine arithmetic rather than by a
    solver: ``argument <= bound - 1`` and ``argument >= 0``. The second one is
    not redundant, because an ``Int`` index can be negative and ``Fin`` starts
    at zero.
    """
    arg = _affine(argument)
    limit = _affine(domain.bound)
    if arg is None or limit is None:
        return False
    highest = _resolve(_add(_add(arg, _scale(limit, -1)), {_CONSTANT: 1}), scope, True)
    if highest is None or highest > 0:
        return False
    return _nonnegative(argument, scope)


def _nonnegative(argument: Any, scope: _Scope) -> bool:
    """Whether ``argument`` is at least zero for every value in scope.

    This is the whole obligation for a family over ``Nat``, which prints as a
    function from ``Int`` like every family: ``f(n - 1)`` for an
    ``f : Fn[Nat, Nat]`` names the point ``-1`` at ``n = 0``, which the family
    does not have.
    """
    arg = _affine(argument)
    if arg is None:
        return False
    lowest = _resolve(arg, scope, False)
    return lowest is not None and lowest >= 0


def _natural_value(argument: Any, scope: _Scope) -> bool:
    """Whether ``argument`` applies a family in scope whose values are naturals.

    ``g(f(i))`` for an ``f : Fn[Fin[n], Nat]`` and a ``g : Fn[Nat, Nat]`` is
    not affine, so :func:`_nonnegative` cannot read it, but its value is a
    ``Nat`` in the printed source as in the lanky statement, which is all a
    point of ``Nat`` has to be. The inner application is checked against its
    own domain where the walk reaches it.
    """
    found = _spine(argument)
    if found is None:
        return False
    name, arguments = found
    current: Any = scope.families.get(name)
    if current is None:
        return False
    for _ in arguments:
        base = _unrefined(current)
        if not isinstance(base, FnType):
            return False
        current = base.codomain
    return is_natural(current)


def _spine(expr: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family name, arguments in order)`` for a chain of applications.

    ``f(i)`` is one application and ``f(i)(j)`` is two, because a family whose
    codomain is itself a family is applied again. The outer call's function is
    then the inner call rather than a variable, so reading only the innermost
    one would leave ``j`` unchecked while Lean, which sees the erased total
    ``Int → Int → Nat``, is free to reason about it. A subscript is the same
    application written differently, and a multi-argument call or a multi-index
    subscript is the same chain again: both print as successive applications.
    """
    arguments: tuple[Any, ...] = ()
    while True:
        if isinstance(expr, prim.Call):
            arguments = (*expr.parameters, *arguments)
            expr = expr.function
        elif isinstance(expr, prim.Subscript):
            index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
            arguments = (*index, *arguments)
            expr = expr.aggregate
        elif isinstance(expr, Var | prim.Variable):
            return (expr.name, arguments) if arguments else None
        else:
            return None


def _check_chain(
    expr: Any,
    name: str,
    arguments: tuple[Any, ...],
    family: FnType,
    scope: _Scope,
) -> None:
    """Check every level of one application chain against its own domain.

    The declared type is walked alongside the arguments, so ``f(i)(j)`` for an
    ``f : Fn[Fin[n], Fn[Fin[m], Nat]]`` discharges ``i`` against ``Fin[n]`` and
    ``j`` against ``Fin[m]``; a level whose domain is refined is declined
    outright, because the erasure drops the refinement and affine arithmetic
    over the binders cannot put it back.

    Raises:
        UnsupportedTerm: If a level cannot be shown to stay in bounds, if a
            level's domain is refined, or if the chain applies the family more
            times than its type has arguments.
    """
    current: Any = family
    for argument in arguments:
        base = current.base if isinstance(current, Refined) else current
        if not isinstance(base, FnType):
            raise UnsupportedTerm(
                f"{render(expr)} applies {name} more times than its type "
                f"({family}) has arguments, so the erased Lean function would "
                "be given an argument it does not take"
            )
        domain = base.domain
        if isinstance(domain, Refined):
            raise UnsupportedTerm(
                f"{render(expr)} applies {name} over the refined domain "
                f"({domain}): a family prints as a total function and its "
                "bounds live in the guards, which carry nothing about a "
                "refinement, and lanky discharges an argument by affine "
                "arithmetic over the binders rather than by a solver, so it "
                "cannot show that the argument is a point of the domain"
            )
        natural_domain = isinstance(domain, Sort) and domain.name == "Nat"
        if (isinstance(domain, FinType) and not _fits(argument, domain, scope)) or (
            natural_domain
            and not (_nonnegative(argument, scope) or _natural_value(argument, scope))
        ):
            raise UnsupportedTerm(
                f"{render(expr)} applies {name} outside the domain it declares "
                f"({domain}): lanky cannot show that {render(argument)} is a point "
                f"of {domain}, and a family prints as a total function from Int, "
                "so Lean would be reasoning about a value the statement does not "
                "have"
            )
        current = base.codomain


def _check_domain(domain: Any, scope: _Scope, refined: _Scope) -> None:
    """Check the applications in the expressions one binder domain carries.

    A domain is not a pymbolic node, so the walk has to know how to open one,
    and it has to: Lean elaborates a ``Fin`` bound, a family's domain and
    codomain and a refinement's predicates exactly as it elaborates a body, so
    an application in any of them is erased exactly as one in a body is. A
    binder ``i : Nat & (f(n) != f(n))`` over an ``f : Fn[Fin[n], Nat]``
    otherwise hands Lean an impossible hypothesis about a point the family does
    not have, and anything follows from it.

    The predicates are checked under ``refined``, which has the binder itself:
    a refinement talks about its own variable, and the base's guard (``i < n``
    for a ``Fin[n] & p``) is printed before the predicate and so stands as its
    antecedent. Everything else is checked under ``scope``, the binders that
    precede this one.
    """
    if isinstance(domain, Refined):
        _check_domain(domain.base, scope, refined)
        for prop in domain.props:
            _check(prop, refined)
        return
    if isinstance(domain, FinType):
        _check(domain.bound, scope)
        return
    if isinstance(domain, FnType):
        # A refinement inside a family type refines the family's own index,
        # which has no binder here, so there is no scope to add.
        _check_domain(domain.domain, scope, scope)
        _check_domain(domain.codomain, scope, scope)


def _names_in_domain(domain: Any) -> frozenset[str]:
    """The variables a binder's domain mentions, apart from its own refinement.

    A refinement's predicates are about the variable being bound (``k : Nat &
    (k > 0)``) and are printed after it on purpose, so they are not counted.
    Everything else in the domain, a ``Fin`` bound above all, was evaluated by
    Python before the binder existed and talks about whatever the name meant
    there.
    """
    if isinstance(domain, Refined):
        return _names_in_domain(domain.base)
    if isinstance(domain, FinType):
        return free_variables(domain.bound)
    if isinstance(domain, FnType):
        return _names_in_domain(domain.domain) | _names_in_domain(domain.codomain)
    return frozenset()


def _check_capture(var: Var, domain: Any) -> None:
    """Refuse a binder whose own domain mentions a variable of the same name.

    ``def bad(i: Nat) -> all(i > 0 for i in Fin[i])`` is a sound Python
    statement: the ``Fin[i]`` is evaluated before the generator binds its
    ``i``, so it means the parameter, and the statement is false at ``i = 1``.
    The printed guard sits after the binder, where Lean reads it as the inner
    ``i``: ``∀ i : Int, 0 ≤ i → i < i → i > 0`` is vacuous, ``omega`` proves it, and the
    ledger would say ``proved``. Declining leaves the fact to the tester, which
    reads it the way Python does; renaming the binder in the printed source
    would keep the proof, and is the natural next step if a real statement is
    ever declined here.

    Raises:
        UnsupportedTerm: If the binder captures a name its domain mentions.
    """
    if var.name in _names_in_domain(domain):
        raise UnsupportedTerm(
            f"the binder {var.name} in {domain} captures the {var.name} its own "
            f"domain mentions: Python reads {domain} before {var.name} is bound, "
            "and Lean would read the printed guard as the bound variable itself"
        )


def _check(expr: Any, scope: _Scope) -> None:
    """Check every application below ``expr``, under the binders it sits in.

    Every binder is also checked for capturing a name its own domain mentions
    (:func:`_check_capture`), which the printed source would otherwise read
    as a different statement.
    """
    if isinstance(expr, Forall | Exists | Sum):
        inner = scope
        for var, domain in expr.binders:
            _check_capture(var, domain)
            preceding = inner
            inner = inner.extended(((var, domain),))
            _check_domain(domain, preceding, inner)
        _check(expr.body, inner)
        if expr.guard is not None:
            _check(expr.guard, inner)
        return
    if not isinstance(expr, prim.ExpressionNode):
        return
    found = _spine(expr)
    if found is not None:
        name, arguments = found
        family = scope.families.get(name)
        if family is not None:
            _check_chain(expr, name, arguments, family, scope)
    for child in init_args(expr):
        if isinstance(child, tuple):
            for item in child:
                _check(item, scope)
        else:
            _check(child, scope)


def check_applications(term: Any) -> None:
    """Refuse a statement that applies a family outside the domain it declares.

    This is what makes the erasure of ``Fn[Fin[n], B]`` to ``Int → B`` sound
    rather than merely usual (see the module docstring). Only a family the
    statement's own binders declare is checked: a bare ``f(a)`` with no binder
    for ``f`` is an open term, and an open term is somebody else's statement.

    Everywhere an application can hide is visited: the body, the guard, and the
    expressions the binder domains carry, which are the ``Fin`` bounds, the
    nested family types and the refinement predicates. Every level of a chained
    application is checked against its own domain.

    The same walk refuses a binder that captures a name its own domain
    mentions (:func:`_check_capture`), which is a different way for the
    printed statement to stop being the one lanky holds.

    Raises:
        UnsupportedTerm: If an application cannot be shown to stay in bounds,
            if the domain of the family it applies is refined, if it applies
            a family more times than its type has arguments, or if a binder
            captures a name its own domain mentions.
    """
    _check(term, _Scope())


# }}}


# {{{ a term as a Lean theorem


@dataclass(eq=False)
class LeanStatement:
    """One lanky statement, arranged the way a Lean theorem is written.

    A closed lanky statement is a :class:`~lanky.terms.Forall` whose binders are
    the variables and whose guard is the hypotheses. Lean writes those as the
    theorem's parameters rather than as a nest of ``∀`` and ``→``, which is not
    only more readable: it gives every hypothesis a name, and a tactic script
    cannot do induction without naming the hypothesis it induces on.

    A binder's own guards (``0 ≤ n``, and ``i < n`` for a point of ``Fin[n]``)
    follow it in the parameter list, and the statement's hypotheses follow
    the last binder, which is where :func:`print_lean` puts them too.

    Attributes:
        name: The theorem's Lean name (see :attr:`declared_name`).
        binders: ``(name, Lean type)`` pairs, in order.
        hypotheses: ``(name, Lean proposition)`` pairs; the names are invented
            here, since a lanky guard is a conjunction and carries none.
        goal: The conclusion, as Lean source.
        goal_term: The conclusion as a lanky term, which is what a tactic
            strategy inspects to decide what to induce on.
        hypothesis_terms: The hypotheses as lanky terms, in the order of
            ``hypotheses``; ``None`` for a guard a binder's domain gave.
        anchors: For each hypothesis, how many binders precede it in the
            parameter list. Empty means every hypothesis follows every binder.
        types: The lanky type of each binder, which the printer needs to
            render a hypothesis again (it decides where a family's value is
            cast to ``Int``).
        mathlib: Whether the statement was printed in the Mathlib dialect,
            and so has to be elaborated where Mathlib is imported.
    """

    name: str
    binders: tuple[tuple[str, str], ...]
    hypotheses: tuple[tuple[str, str], ...]
    goal: str
    goal_term: Any = None
    hypothesis_terms: tuple[Any, ...] = field(default_factory=tuple)
    anchors: tuple[int, ...] = field(default_factory=tuple)
    types: dict[str, Any] = field(default_factory=dict)
    mathlib: bool = False

    def _parameters(self) -> list[tuple[bool, int]]:
        """The parameters in order, as ``(is_hypothesis, index)`` pairs."""
        anchors = self.anchors or (len(self.binders),) * len(self.hypotheses)
        order: list[tuple[bool, int]] = []
        for position in range(len(self.binders) + 1):
            order += [(True, index) for index, at in enumerate(anchors) if at == position]
            if position < len(self.binders):
                order.append((False, position))
        return order

    @property
    def parameters(self) -> str:
        """The binders and hypotheses as Lean binder syntax."""
        return " ".join(
            "({} : {})".format(*(self.hypotheses if hypothesis else self.binders)[index])
            for hypothesis, index in self._parameters()
        )

    @property
    def proposition(self) -> str:
        """The statement as one closed proposition, binders and all.

        A hypothesis that is itself quantified needs parentheses here, where it
        stands to the left of an arrow, and none in the binder syntax above, so
        the term is rendered again rather than the text reused.
        """
        text = self.goal
        for hypothesis, index in reversed(self._parameters()):
            if not hypothesis:
                name, sort = self.binders[index]
                text = f"∀ {name} : {sort}, {text}"
                continue
            prop = self.hypotheses[index][1]
            term = self.hypothesis_terms[index] if self.hypothesis_terms else None
            if term is not None:
                with dialect(self.mathlib):
                    prop = _render_prop(term, _ARROW + 1, self.types)
            text = f"{prop} → {text}"
        return text

    @property
    def declared_name(self) -> str:
        """The name the theorem is declared under: :attr:`name`, or ``Lanky.name``.

        A Mathlib statement is declared in the ``Lanky`` namespace. Mathlib
        declares thousands of lemmas at the root, ``mul_comm``, ``sq_nonneg`` and
        ``two_mul`` among them, and a claim named after one would be refused as
        already declared at every attempt, whatever its tactic. Nothing in
        Mathlib lives under ``Lanky``, and the prefix changes nothing else: the
        statement's own names are its binders and fully qualified constants.
        """
        return f"Lanky.{self.name}" if self.mathlib else self.name

    def source(self, tactic: str) -> str:
        """The full Lean declaration proved by ``tactic``.

        The tactic block is indented as a block, so a multi-line script can be
        passed in as written. The theorem is declared under
        :attr:`declared_name`.
        """
        head = f"theorem {self.declared_name}"
        if self.parameters:
            head = f"{head} {self.parameters}"
        body = "\n".join("  " + line if line.strip() else line for line in tactic.splitlines())
        return f"{head} : {self.goal} := by\n{body}\n"


def _lean_name(name: str) -> str:
    """Turn a Python qualified name into a usable Lean identifier."""
    cleaned = "".join(character if character.isalnum() else "_" for character in name)
    cleaned = cleaned.strip("_") or "lanky_claim"
    if cleaned[0].isdigit():
        cleaned = f"lanky_{cleaned}"
    return cleaned


def statement_of(
    term: Any, name: str = "lanky_claim", mathlib: bool | None = None
) -> LeanStatement:
    """Arrange a closed lanky term as a Lean theorem.

    The top-level quantifier becomes the theorem's parameters and its guard
    becomes the named hypotheses; everything below stays a proposition. A
    natural variable is an ``Int`` parameter followed by ``0 ≤ n``, as
    :func:`lean_type` and :func:`domain_guards` have it. ``mathlib=True``
    prints it in the Mathlib dialect (see the module docstring).

    Raises:
        UnsupportedTerm: If any part of the statement leaves the fragment, or
            applies a family outside the domain it declares
            (:func:`check_applications`).
    """
    with dialect(mathlib):
        return _statement_of(term, name)


def _statement_of(term: Any, name: str) -> LeanStatement:
    """:func:`statement_of`, in the dialect in effect."""
    lean_name = _lean_name(name)
    mathlib = _in_mathlib()
    check_applications(term)
    if not isinstance(term, Forall):
        return LeanStatement(lean_name, (), (), print_lean(term), term, mathlib=mathlib)

    binders: list[tuple[str, str]] = []
    hypotheses: list[tuple[str, str]] = []
    hypothesis_terms: list[Any] = []
    anchors: list[int] = []
    types: dict[str, Any] = {}
    for var, domain in term.binders:
        guards = _domain_guards(var, domain, types)
        types = {**types, var.name: domain}
        binders.append((var.name, _lean_type(domain)))
        for guard in guards:
            hypotheses.append((f"h{len(hypotheses)}", guard))
            hypothesis_terms.append(None)
            anchors.append(len(binders))
    for guard in conjuncts(term.guard):
        hypotheses.append((f"h{len(hypotheses)}", _render_prop(guard, _QUANT, types)))
        hypothesis_terms.append(guard)
        anchors.append(len(binders))
    return LeanStatement(
        name=lean_name,
        binders=tuple(binders),
        hypotheses=tuple(hypotheses),
        goal=_render_prop(term.body, _QUANT, types),
        goal_term=term.body,
        hypothesis_terms=tuple(hypothesis_terms),
        anchors=tuple(anchors),
        types=types,
        mathlib=mathlib,
    )


# }}}
