"""The bridge to a computer algebra system: lanky terms as sympy expressions, and back.

The design idea. A simplifier is the third kind of evidence lanky's ledger has
room for, between a sample and a decision procedure: an identity sympy takes to
zero is worth more than one that held at two hundred draws, and less than one a
decision procedure answered, since a simplifier can fail to see that a true
identity holds, and its answers are not guaranteed. The oracle that asks it is
:class:`lanky.oracles.cas.CasOracle`. This module is the translation it relies
on, and that a plugin building claims from sympy's output relies on too.

The translation is strict, in both directions, because a term read with a
meaning it does not have is a proof of the wrong statement. Only what both
sides read alike crosses:

- numbers, read exactly: an ``int`` is an integer, a ``Fraction`` a rational,
  and a float the rational it holds, as the property tester and the Lean
  printer read one; ``1j`` is sympy's ``I``;
- variables, which have to be bound by a quantifier of the statement whose
  sort names a set of numbers: ``Real`` is a real symbol, ``Complex`` a
  complex one, ``Int`` an integer, and ``Nat`` and a point of ``Fin[n]`` an
  integer that is not negative, so sympy applies no identity the sort does not
  grant (``sqrt(x**2)`` of a real ``x`` is ``Abs(x)``, not ``x``);
- addition, multiplication, true division and powers, ``abs``, and
  ``lanky.exp``, ``lanky.log`` and ``lanky.sqrt``, which are sympy's ``exp``,
  ``log`` and ``sqrt``: Python's principal branches, where Python gives them a
  value. A logarithm or a square root of a real argument crosses only where
  sympy can show that the argument is not negative. Below zero sympy's
  functions are complex, Python's ``math`` raises and Mathlib's are real, so a
  statement read there would be decided in a reading of its own:
  ``x * sqrt(-1) == x * 1j`` holds to sympy, has no value in Python at any
  ``x``, and is false in Lean.

Everything else is :class:`Untranslatable`, with the reason: a family applied to
an argument, a subscript, a reduction, a floor division or a remainder, a
variable whose sort is not a set of numbers (an operator does not commute, and a
boundary is not a number), a free variable nobody gave a sort to, a truth value
used as a number, and a real logarithm or square root of what may be negative.
A float sympy holds to a precision of its own, ``pi``, and an infinity have no
counterpart on the way back.

Where Python gives a statement no value, the readings are not compared. sympy
simplifies a rational function as the function it is wherever its denominator
is not zero, so ``x / x`` is ``1`` to it, and an identity it finds holds at
every point where Python gives both sides a value. Where a denominator is zero,
or a logarithm's argument is, Python raises and the property tester leaves the
draw undecided. Lean's division and logarithm are total and give those points
values of their own; that gap is :mod:`lanky.semantics`'s, which notes it on
the fact in Mathlib mode, the one reading in which Lean states such a
statement, whichever oracle settles it.

sympy is an optional dependency, the ``cas`` extra, and is imported when a
translation is asked for, not when this module is: ``import lanky`` does not
import it.
"""

from __future__ import annotations

import math
import numbers
from collections.abc import Iterator, Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, Refined, Sort
from lanky.terms import (
    Abs,
    Add,
    Comparison,
    Elementary,
    Exists,
    Extremum,
    Forall,
    Power,
    Product,
    Quotient,
    Sum,
    Var,
    render,
)

__all__ = [
    "Equation",
    "Untranslatable",
    "check_shape",
    "equations",
    "from_sympy",
    "symbol_for",
    "sympy_module",
    "to_sympy",
]


class Untranslatable(ValueError):
    """Raised for a term, or a sympy expression, the other side has no counterpart for.

    Declining is the point, as it is for the Lean printer's
    :class:`lanky.lean.UnsupportedTerm`: a statement translated with a meaning
    it does not have would be simplified into a verdict about another
    statement, so :meth:`lanky.oracles.cas.CasOracle.can_establish` asks for
    the translation first and leaves a fact it raises for to a weaker oracle.
    """


def sympy_module() -> Any:
    """sympy, imported now; ``ImportError`` saying how to install it when it is missing."""
    try:
        import sympy
    except ImportError as exc:
        raise ImportError(
            'sympy is not installed; the CAS bridge needs it (pip install "lanky[cas]")'
        ) from exc
    return sympy


# {{{ lanky to sympy

#: The sympy assumptions a variable of each sort is made with.
_ASSUMPTIONS: dict[str, dict[str, bool]] = {
    "Real": {"real": True},
    "Complex": {},
    "Int": {"integer": True},
    "Nat": {"integer": True, "nonnegative": True},
}


def symbol_for(name: str, domain: Any) -> Any:
    """The sympy symbol a variable of this domain is, with what its sort grants.

    ``Real`` is ``real=True``, ``Complex`` has no assumption, ``Int`` is
    ``integer=True``, and ``Nat`` and every ``Fin[n]`` are integers that are
    not negative. A refinement is read as its base sort: the propositions
    refining it narrow the variable further, and an identity that holds over
    the base holds over any part of it, so leaving them out costs a decision
    and never makes a wrong one.

    Raises:
        Untranslatable: For any other domain, ``Bool`` and ``Prop``, a
            family, or a sort a plugin made, whose values need not be numbers.
    """
    assumptions = _assumptions(name, domain)
    return sympy_module().Symbol(name, **assumptions)


def _assumptions(name: str, domain: Any) -> dict[str, bool]:
    """The sympy assumptions a variable of ``domain`` is made with; read without sympy.

    Raises:
        Untranslatable: For a domain that is not a set of numbers (see
            :func:`symbol_for`).
    """
    base = domain
    while isinstance(base, Refined):
        base = base.base
    if isinstance(base, FinType):
        return {"integer": True, "nonnegative": True}
    if isinstance(base, Sort) and base.name in _ASSUMPTIONS:
        return dict(_ASSUMPTIONS[base.name])
    raise Untranslatable(
        f"{name} ranges over {domain}, which is not a set of numbers a simplifier "
        "may treat as commuting scalars"
    )


def _number(value: Any, sympy: Any = None) -> Any:
    """A Python number as the sympy number it is, exactly; with no ``sympy``, only checked.

    Raises:
        Untranslatable: For a truth value, an infinity or a NaN, and anything
            that is not a number.
    """
    if isinstance(value, bool):
        raise Untranslatable(f"{value} is a truth value, not a number")
    if isinstance(value, numbers.Integral):
        return None if sympy is None else sympy.Integer(int(value))
    if isinstance(value, numbers.Rational):
        if sympy is None:
            return None
        return sympy.Rational(int(value.numerator), int(value.denominator))
    if isinstance(value, numbers.Real):
        if not math.isfinite(float(value)):
            raise Untranslatable(f"{value} is not a finite number")
        if sympy is None:
            return None
        exact = Fraction(float(value))
        return sympy.Rational(exact.numerator, exact.denominator)
    if isinstance(value, numbers.Complex):
        real, imag = _number(value.real, sympy), _number(value.imag, sympy)
        return None if sympy is None else real + sympy.I * imag
    raise Untranslatable(f"{value!r} is not a number")


_ELEMENTARY_NAMES = {
    "exp": "exp",
    "log": "log",
    "sqrt": "sqrt",
    "real": "re",
    "imag": "im",
    "conj": "conjugate",
}

#: The functions whose real argument has to be seen not to be negative, by
#: what a message calls their value.
_REAL_DOMAIN = {"log": "logarithm", "sqrt": "square root"}


def to_sympy(expr: Any, symbols: Mapping[str, Any]) -> Any:
    """The sympy expression a lanky arithmetic term is.

    ``symbols`` maps the name of each variable the term may mention to its
    sympy symbol (see :func:`symbol_for`); :func:`equations` builds it from
    the quantifiers of a statement.

    Raises:
        Untranslatable: For anything outside the fragment the module's
            docstring lists, with the reason.
    """
    return _translate(expr, symbols, sympy_module())


def _translate(expr: Any, symbols: Mapping[str, Any], sympy: Any) -> Any:
    """:func:`to_sympy` of ``expr``; with no ``sympy``, only its shape checked.

    Without sympy nothing is built, and what is checked is everything that
    refuses a term but sympy's own reading of it: the node types, the
    numbers, and that each variable is bound (it is a key of ``symbols``).
    That a real logarithm's or square root's argument may be negative is
    sympy's to say, and is checked only where the term is translated.

    Raises:
        Untranslatable: As :func:`to_sympy` does.
    """
    if isinstance(expr, prim.Variable):
        if expr.name not in symbols:
            raise Untranslatable(
                f"{expr.name} is not bound by a quantifier of the statement, so its "
                "sort is not known"
            )
        return symbols[expr.name]
    if not isinstance(expr, prim.ExpressionNode):
        return _number(expr, sympy)
    if isinstance(expr, prim.Sum | prim.Product):
        children = [_translate(child, symbols, sympy) for child in expr.children]
        if sympy is None:
            return None
        return (sympy.Add if isinstance(expr, prim.Sum) else sympy.Mul)(*children)
    if isinstance(expr, prim.FloorDiv | prim.Remainder):
        kind = "floor division" if isinstance(expr, prim.FloorDiv) else "remainder"
        raise Untranslatable(f"{render(expr)} is a {kind}, which the bridge does not take")
    if isinstance(expr, prim.Quotient):
        numerator = _translate(expr.numerator, symbols, sympy)
        denominator = _translate(expr.denominator, symbols, sympy)
        return None if sympy is None else numerator / denominator
    if isinstance(expr, prim.Power):
        base = _translate(expr.base, symbols, sympy)
        exponent = _translate(expr.exponent, symbols, sympy)
        return None if sympy is None else sympy.Pow(base, exponent)
    if isinstance(expr, Elementary):
        argument = _translate(expr.argument, symbols, sympy)
        if sympy is None:
            return None
        if (
            expr.function in _REAL_DOMAIN
            and argument.is_extended_real
            and not argument.is_nonnegative
        ):
            raise Untranslatable(
                f"{render(expr)} is the {_REAL_DOMAIN[expr.function]} of a real number "
                "sympy cannot show is not negative, where sympy's value is complex, "
                "Python's math raises and Mathlib's value is real"
            )
        function = getattr(sympy, _ELEMENTARY_NAMES[expr.function])
        return function(argument)
    if isinstance(expr, Abs):
        operand = _translate(expr.operand, symbols, sympy)
        return None if sympy is None else sympy.Abs(operand)
    if isinstance(expr, Extremum):
        arguments = [_translate(argument, symbols, sympy) for argument in expr.arguments]
        if sympy is None:
            return None
        return (sympy.Max if expr.function == "max" else sympy.Min)(*arguments)
    if isinstance(expr, prim.Call):
        what = "a family applied to an argument"
    elif isinstance(expr, prim.Subscript):
        what = "a subscript"
    elif isinstance(expr, Sum):
        what = "a reduction"
    elif isinstance(
        expr, Forall | Exists | prim.Comparison | prim.LogicalAnd | prim.LogicalOr | prim.LogicalNot
    ):
        what = "a proposition used as a number"
    else:
        what = f"a {type(expr).__name__}"
    raise Untranslatable(f"{render(expr)} is {what}, which the bridge does not take")


@dataclass(frozen=True, eq=False)
class Equation:
    """One equation of a statement, as written and as sympy reads its sides.

    Attributes:
        term: The comparison as the statement has it, for messages.
        left: Its left side, as a sympy expression.
        right: Its right side.
    """

    term: Any
    left: Any
    right: Any


def equations(term: Any) -> tuple[Equation, ...]:
    """The equations a statement asserts, each with its sides translated.

    The statement is an equation, a conjunction of statements, or a universal
    over statements (a theorem's term is the last), and nothing else. The
    quantifiers' binders become the symbols the sides are read with, nested
    ones inside the ones around them; their guards, which are a theorem's
    hypotheses, are not read. An identity that holds for every value of its
    variables holds where the hypotheses do as well, so leaving them out costs
    an identity that holds only under them, which is declined, and never makes
    a wrong one.

    The shape is read first, without sympy (:func:`check_shape`), so a
    statement of another shape is refused before sympy is imported: a file of
    orders and sums costs a check nothing for the oracle's being installed.
    sympy's constructors evaluate as they build, so the translation itself
    can take time on a large statement, which is why the CAS oracle asks for
    it inside its deadline and asks only for the shape before it.

    Raises:
        Untranslatable: For a statement of any other shape (an order, a
            disequality, a disjunction, an existential), for one that
            asserts no equation, and for a side outside the fragment.
    """
    found = check_shape(term)
    symbols: dict[tuple[str, int], Any] = {}
    out = []
    for comparison, binders in found:
        scope: dict[str, Any] = {}
        for var, domain in binders:
            key = (var.name, id(domain))
            if key not in symbols:
                symbols[key] = symbol_for(var.name, domain)
            scope[var.name] = symbols[key]
        out.append(
            Equation(
                comparison,
                to_sympy(comparison.left, scope),
                to_sympy(comparison.right, scope),
            )
        )
    return tuple(out)


def check_shape(term: Any) -> tuple[tuple[Any, tuple], ...]:
    """The equations a statement asserts, with the binders around each, checked without sympy.

    Everything :func:`equations` refuses a statement for is checked here but
    what only sympy can say: the statement's shape, that each binder ranges
    over a set of numbers, and that each side is built of the nodes and
    numbers the bridge takes, over variables a quantifier binds. Whether a
    real logarithm's or square root's argument may be negative is sympy's
    reading, and is left to the translation. Nothing is built and sympy is
    not imported, so this is cheap whatever the size of the statement, which
    is what :meth:`lanky.oracles.cas.CasOracle.can_establish` asks (#77).

    Raises:
        Untranslatable: As :func:`equations` does, for all but the domain of
            a real logarithm or square root.
    """
    found = tuple(_comparisons(term, ()))
    if not found:
        raise Untranslatable(f"{render(term)} asserts no equation")
    for comparison, binders in found:
        scope: dict[str, None] = {}
        for var, domain in binders:
            _assumptions(var.name, domain)
            scope[var.name] = None
        _translate(comparison.left, scope, None)
        _translate(comparison.right, scope, None)
    return found


def _comparisons(term: Any, binders: tuple) -> Iterator[tuple[Any, tuple]]:
    """Each equation of ``term``, with the binders in scope around it, outermost first."""
    if isinstance(term, Forall):
        yield from _comparisons(term.body, (*binders, *term.binders))
        return
    if isinstance(term, prim.LogicalAnd):
        for child in term.children:
            yield from _comparisons(child, binders)
        return
    if isinstance(term, prim.Comparison) and term.operator == "==":
        yield term, binders
        return
    if isinstance(term, bool):
        raise Untranslatable(f"the statement is the constant {term}")
    raise Untranslatable(
        f"{render(term)} is not an equation, a conjunction of equations or a "
        "universal over them"
    )


# }}}


# {{{ sympy to lanky


def from_sympy(expr: Any, variables: Mapping[str, Any] | None = None) -> Any:
    """The lanky term a sympy expression is, built from lanky's own nodes.

    A symbol becomes the variable of its name, or ``variables[name]`` when the
    mapping has it. An integer becomes an ``int`` and a rational a
    ``Fraction``. A product with factors to a negative power becomes a
    quotient, ``x**(1/2)`` becomes ``lanky.sqrt(x)``, and ``exp``, ``log`` and
    ``Abs`` become lanky's, so the term reads as sympy prints it and the
    property tester and the Lean printer take it as they take one written by
    hand. An equation or an order between two expressions becomes the
    comparison.

    Raises:
        Untranslatable: For a float, whose value sympy holds to a precision of
            its own, ``pi`` and other constants with no lanky counterpart, an
            infinity, and any function but ``exp``, ``log`` and ``Abs``.
    """
    sympy = sympy_module()
    return _from_sympy(sympy, sympy.sympify(expr), variables or {})


def _product(factors: list[Any]) -> Any:
    """The product of ``factors``: the one factor itself, or ``1`` for none."""
    if not factors:
        return 1
    if len(factors) == 1:
        return factors[0]
    return Product(tuple(factors))


#: sympy's relational classes, by the operator a lanky comparison writes.
_RELATIONS = {
    "Equality": "==",
    "Unequality": "!=",
    "StrictLessThan": "<",
    "LessThan": "<=",
    "StrictGreaterThan": ">",
    "GreaterThan": ">=",
}


def _from_sympy(sympy: Any, expr: Any, variables: Mapping[str, Any]) -> Any:
    """:func:`from_sympy` of one node."""
    if isinstance(expr, sympy.Symbol):
        given = variables.get(expr.name)
        return given if given is not None else Var(expr.name)
    if isinstance(expr, sympy.Integer):
        return int(expr)
    if isinstance(expr, sympy.Rational):
        return Fraction(int(expr.p), int(expr.q))
    if expr is sympy.I:
        return 1j
    if expr is sympy.E:
        return Elementary("exp", 1)
    if isinstance(expr, sympy.Float):
        raise Untranslatable(
            f"{expr} is a float sympy holds to a precision of its own; write it as a Rational"
        )
    if isinstance(expr, sympy.Add):
        return Add(tuple(_summand(sympy, arg, variables) for arg in expr.args))
    if isinstance(expr, sympy.Mul):
        return _from_mul(sympy, expr, variables)
    if isinstance(expr, sympy.Pow):
        return _from_pow(sympy, expr, variables)
    if isinstance(expr, sympy.exp):
        return Elementary("exp", _from_sympy(sympy, expr.args[0], variables))
    if isinstance(expr, sympy.log) and len(expr.args) == 1:
        return Elementary("log", _from_sympy(sympy, expr.args[0], variables))
    for function, name in (("real", "re"), ("imag", "im"), ("conj", "conjugate")):
        if isinstance(expr, getattr(sympy, name)):
            return Elementary(function, _from_sympy(sympy, expr.args[0], variables))
    if isinstance(expr, sympy.Abs):
        return Abs(_from_sympy(sympy, expr.args[0], variables))
    relation = _RELATIONS.get(type(expr).__name__)
    if relation is not None:
        left, right = (_from_sympy(sympy, arg, variables) for arg in expr.args)
        return Comparison(left, relation, right)
    raise Untranslatable(f"{expr} ({type(expr).__name__}) has no lanky counterpart")


def _summand(sympy: Any, expr: Any, variables: Mapping[str, Any]) -> Any:
    """A term of a sum, as a negation when sympy gives it a negative coefficient.

    ``x - 2*y`` is ``x + (-2)*y`` to sympy, and lanky's renderer prints a
    summand ``-1*t`` as a subtraction, so ``-2*y`` is built as ``-1*(2*y)``
    here, and the sum reads ``x - 2*y`` rather than ``x + -2*y``.
    """
    if isinstance(expr, sympy.Mul):
        coefficient, _rest = expr.as_coeff_Mul()
        if coefficient.is_Rational and coefficient < 0:
            return Product((-1, _from_sympy(sympy, -expr, variables)))
    return _from_sympy(sympy, expr, variables)


def _from_mul(sympy: Any, expr: Any, variables: Mapping[str, Any]) -> Any:
    """A product, as a quotient when some factor is to a negative power."""
    numerator: list[Any] = []
    denominator: list[Any] = []
    for factor in expr.args:
        base, exponent = factor.as_base_exp()
        if isinstance(exponent, sympy.Rational) and exponent < 0 and not factor.is_Number:
            denominator.append(_from_sympy(sympy, sympy.Pow(base, -exponent), variables))
        else:
            numerator.append(_from_sympy(sympy, factor, variables))
    top = _product(numerator)
    return Quotient(top, _product(denominator)) if denominator else top


def _from_pow(sympy: Any, expr: Any, variables: Mapping[str, Any]) -> Any:
    """A power, as a square root, a quotient, or a power."""
    base, exponent = expr.args
    if isinstance(exponent, sympy.Rational) and exponent < 0:
        return Quotient(1, _from_sympy(sympy, sympy.Pow(base, -exponent), variables))
    lanky_base = _from_sympy(sympy, base, variables)
    if exponent == sympy.Rational(1, 2):
        return Elementary("sqrt", lanky_base)
    if isinstance(exponent, sympy.Rational) and exponent.q == 2:
        return Power(Elementary("sqrt", lanky_base), int(exponent.p))
    return Power(lanky_base, _from_sympy(sympy, exponent, variables))


# }}}
