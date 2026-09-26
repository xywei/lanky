"""A small algebra of layer potentials, and the rule engine that decides claims in it.

This is the rule engine behind ``pytential_skie.py``, kept apart so that the
demonstration reads as the claims it makes. It is example code and not part of
lanky. lanky provides the shape of the claims (:mod:`lanky.rewrites`), the
axioms they rest on (``@axiom``) and the ledger; everything about layer
potentials is here, as it would be in a plugin.

The algebra. ``S`` and ``D`` are the single- and double-layer potentials of one
kernel, Laplace or Helmholtz. ``trace(u, side)`` and ``normal_derivative(u,
side)`` are the limits of a representation ``u`` on the boundary from one
side: ``INTERIOR`` is -1 and ``EXTERIOR`` is +1, the side the normal points
to. ``I``, ``S``, ``D``, ``Sp`` and ``Dp`` are the boundary operators: the
identity, and the direct values of the four layer operators, printed ``S'``
and ``D'``. The same letter stands for a potential inside a trace and for its
direct value outside one, as in Kress and in pytential. A coefficient is a
polynomial in named parameters, such as ``eta``, over the Gaussian rationals:
``1j * eta / 2`` is one. A float is read as the binary number it is, so
``0.5`` is one half and ``0.1`` is not a tenth.

The rules are the axioms. A :class:`RuleSet` is built from ``@axiom`` objects
and reads its rules off their statements: ``trace(D, s) == D + s / 2 * I``
is the rule for the Dirichlet trace of ``D`` from either side,
``compact(S)`` says that ``S`` is compact, and ``~scalar_plus_compact(Dp)``
that ``D'`` is not a multiple of the identity plus a compact operator. The
engine applies nothing else about layer potentials, so a verdict rests on
exactly the axioms it names, and an axiom copied down wrong changes the
verdicts that use it. Two facts about operators in general it uses without an
axiom: compact operators form a linear space, so a combination of them is
compact, and the identity is not compact, the functions on a boundary being
infinitely many dimensions, so the identity coefficient of ``c*I`` plus a
compact operator is one number, and a compact operator is not of the second
kind.

The claims. A :class:`BoundaryEquation` is a lanky rewrite, from the trace of a
representation to the boundary operator it is claimed to be, under the
obligation ``"jump relations"``, together with a verdict about that operator:
second kind (``c*I`` plus a compact operator, ``c`` not zero), first kind (a
compact operator: no identity term), or not second kind because a named
operator is not a multiple of the identity plus a compact one. It claims
three facts: the rewrite; for a second-kind claim, that the identity
coefficient is not zero, stated as integer arithmetic core Lean can prove;
and the verdict, which rests on the other two.

What the engine decides, and why it is a decision procedure. It accepts
one-sided traces of finite linear combinations of ``S`` and ``D`` of one kernel
on a closed boundary of class C², boundary operators that are finite linear
combinations of ``I``, ``S``, ``D``, ``S'``, ``D'`` and such traces, and
polynomial coefficients. Within that fragment:

- a rewrite is decided by resolving every trace with its jump rule and
  comparing the two sides term by term, which is exact polynomial arithmetic;
- a verdict is decided by collecting the operator's terms. A nonzero constant
  coefficient on the one operator that is not a multiple of the identity plus
  a compact operator makes the whole operator not second kind; without one it
  is ``c*I`` plus a compact operator, and a constant ``c`` is zero or it is not.

Every claim in the fragment gets an answer, and whatever is outside it is
declined with the reason: a verdict that depends on a parameter's value
(``eta*I + D``), two operators that are not a multiple of the identity plus a
compact one (the Helmholtz ``D'`` minus the Laplace one is compact, which these
rules cannot see), two kernels, a trace no axiom gives. Membership is decided
by looking. That makes the engine a decision procedure for the fragment,
relative to the axioms, and its trust class is ``decision-procedure``, as
isl's is for Presburger arithmetic. The axioms themselves are ``assumed``, and
the ledger shows what each verdict is decided under.

What it does not see. A rewrite is a claim about the derivation: that the jump
relations take the trace to the target. On a particular boundary two different
expressions can be one operator (on a circle the Laplace ``D`` and ``S'`` are
the same multiple of the mean value), and an identity that holds only there is
not one these rules derive.

The adapter. :func:`from_pytential` translates a pytential ``sym`` expression
built from ``sym.S``, ``sym.D``, ``sym.Sp`` and ``sym.Dp`` of one Laplace or
Helmholtz kernel on one boundary, applied to one density, with scalar
coefficients, into this algebra, reading ``qbx_forced_limit`` as the side:
``None`` off the boundary, ``+1`` or ``-1`` a one-sided limit, ``"avg"`` the
direct value. It imports nothing from pytential. It recognizes the nodes by
their structure, and it refuses what it does not recognize.
"""

from __future__ import annotations

import dataclasses
import numbers
import re
from collections.abc import Callable, Iterable
from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.ledger import Fact, Status, fact_id
from lanky.plugins import registry
from lanky.rewrites import Rewrite, RewriteTerm
from lanky.terms import Comparison, LogicalOr

__all__ = [
    "EXTERIOR",
    "FIRST_KIND",
    "INTERIOR",
    "OBLIGATION",
    "SECOND_KIND",
    "BoundaryEquation",
    "C2Boundary",
    "D",
    "Decision",
    "Dp",
    "I",
    "JumpRewrite",
    "LayerRules",
    "Operator",
    "OutsideFragment",
    "Poly",
    "RuleSet",
    "S",
    "Side",
    "Sp",
    "Verdict",
    "VerdictQuestion",
    "classify",
    "compact",
    "from_pytential",
    "normal_derivative",
    "resolve",
    "same",
    "scalar",
    "scalar_plus_compact",
    "trace",
]

#: The side a limit is taken from. The normal points to the exterior.
INTERIOR = -1
EXTERIOR = +1

#: What a boundary equation's rewrite claims of its trace and its target.
OBLIGATION = "jump relations"


class OutsideFragment(ValueError):
    """Something these rules do not accept; the message says which part and why."""


# {{{ scalars: Gaussian rationals, and polynomials over them


@dataclass(frozen=True)
class Gauss:
    """A Gaussian rational ``re + im*i``, exactly."""

    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __add__(self, other: Gauss) -> Gauss:
        return Gauss(self.re + other.re, self.im + other.im)

    def __neg__(self) -> Gauss:
        return Gauss(-self.re, -self.im)

    def __mul__(self, other: Gauss) -> Gauss:
        return Gauss(
            self.re * other.re - self.im * other.im,
            self.re * other.im + self.im * other.re,
        )

    def inverse(self) -> Gauss:
        """``1 / self``; ``ZeroDivisionError`` for zero."""
        norm = self.re * self.re + self.im * self.im
        if not norm:
            raise ZeroDivisionError("division by zero")
        return Gauss(self.re / norm, -self.im / norm)

    def __bool__(self) -> bool:
        return bool(self.re) or bool(self.im)

    def __str__(self) -> str:
        """Python's notation, with fractions: ``-1/2``, ``1j``, ``1j/2``, ``(1 - 3j/2)``."""
        if not self.im:
            return _fraction_text(self.re)
        imaginary = _imaginary_text(self.im)
        if not self.re:
            return imaginary
        sign, magnitude = ("-", _imaginary_text(-self.im)) if self.im < 0 else ("+", imaginary)
        return f"({_fraction_text(self.re)} {sign} {magnitude})"


def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _imaginary_text(value: Fraction) -> str:
    if value.denominator == 1:
        return f"{value.numerator}j"
    return f"{value.numerator}j/{value.denominator}"


#: A monomial: ``(name, power)`` pairs, sorted by name, powers positive.
Monomial = tuple[tuple[str, int], ...]

_ONE_GAUSS = Gauss(Fraction(1))


@dataclass(frozen=True)
class Poly:
    """A polynomial in named parameters with Gaussian-rational coefficients.

    Kept canonical, with no zero coefficient and the terms sorted, so that two
    polynomials are equal exactly when they are equal as polynomials, and
    ``==`` says so.
    """

    terms: tuple[tuple[Monomial, Gauss], ...] = ()

    @staticmethod
    def of(items: Iterable[tuple[Monomial, Gauss]]) -> Poly:
        """The canonical polynomial of some terms, like ones added up."""
        total: dict[Monomial, Gauss] = {}
        for monomial, coefficient in items:
            total[monomial] = total.get(monomial, Gauss()) + coefficient
        return Poly(tuple(sorted(((m, c) for m, c in total.items() if c), key=lambda t: t[0])))

    @staticmethod
    def constant(value: Gauss) -> Poly:
        return Poly.of([((), value)])

    @staticmethod
    def variable(name: str) -> Poly:
        return Poly.of([(((name, 1),), _ONE_GAUSS)])

    def __add__(self, other: Poly) -> Poly:
        return Poly.of([*self.terms, *other.terms])

    def __neg__(self) -> Poly:
        return Poly(tuple((m, -c) for m, c in self.terms))

    def __sub__(self, other: Poly) -> Poly:
        return self + (-other)

    def __mul__(self, other: Poly) -> Poly:
        return Poly.of(
            (_times(left, right), a * b)
            for left, a in self.terms
            for right, b in other.terms
        )

    def __bool__(self) -> bool:
        return bool(self.terms)

    def value(self) -> Gauss | None:
        """The constant this polynomial is, or ``None`` when it mentions a parameter."""
        if not self.terms:
            return Gauss()
        if len(self.terms) == 1 and self.terms[0][0] == ():
            return self.terms[0][1]
        return None

    def names(self) -> frozenset[str]:
        """The parameters this polynomial mentions."""
        return frozenset(name for monomial, _ in self.terms for name, _power in monomial)

    def substitute(self, name: str, value: Gauss) -> Poly:
        """This polynomial with ``value`` for the parameter ``name``."""
        items = []
        for monomial, coefficient in self.terms:
            rest = tuple((n, p) for n, p in monomial if n != name)
            power = sum(p for n, p in monomial if n == name)
            factor = _ONE_GAUSS
            for _ in range(power):
                factor = factor * value
            items.append((rest, coefficient * factor))
        return Poly.of(items)

    def __str__(self) -> str:
        """Python's notation, ``0`` for zero; see :func:`_term_text`."""
        if not self.terms:
            return "0"
        return _joined([_term_text(c, m) for m, c in self.terms])


def _times(left: Monomial, right: Monomial) -> Monomial:
    powers: dict[str, int] = {}
    for name, power in (*left, *right):
        powers[name] = powers.get(name, 0) + power
    return tuple(sorted(powers.items()))


def _monomial_text(monomial: Monomial) -> str:
    return "*".join(name if power == 1 else f"{name}**{power}" for name, power in monomial)


def _term_text(coefficient: Gauss, monomial: Monomial) -> str:
    if not monomial:
        return str(coefficient)
    if coefficient == _ONE_GAUSS:
        return _monomial_text(monomial)
    if coefficient == -_ONE_GAUSS:
        return f"-{_monomial_text(monomial)}"
    return f"{coefficient}*{_monomial_text(monomial)}"


def _joined(parts: list[str]) -> str:
    """Summands joined with ``+``, or ``-`` for one that starts with a minus sign."""
    out = parts[0]
    for part in parts[1:]:
        out += f" - {part[1:]}" if part.startswith("-") else f" + {part}"
    return out


ZERO = Poly()
ONE = Poly.constant(_ONE_GAUSS)


def scalar(value: Any, leaf: Callable[[Any], Poly | None] | None = None) -> Poly:
    """A Python number or a pymbolic expression as a :class:`Poly`.

    A pymbolic variable, a lanky ``Var`` among them, is a parameter. Sums,
    products, powers with a literal natural exponent, and quotients by a
    nonzero constant are what a polynomial is made of; anything else, a
    function call or a division by a parameter, is outside the fragment.
    ``leaf`` is asked first about every node and may answer for it, which is
    how the pytential adapter reads a normal vector's components.

    Raises:
        OutsideFragment: For anything that is not such a polynomial.
    """
    if leaf is not None:
        answer = leaf(value)
        if answer is not None:
            return answer
    if isinstance(value, Poly):
        return value
    if isinstance(value, bool):
        raise OutsideFragment(f"{value!r} is a truth value, not a coefficient")
    if isinstance(value, numbers.Integral):
        return Poly.constant(Gauss(Fraction(int(value))))
    if isinstance(value, Fraction):
        return Poly.constant(Gauss(value))
    if isinstance(value, numbers.Real):
        return Poly.constant(Gauss(_exact(float(value))))
    if isinstance(value, numbers.Complex):
        number = complex(value)
        return Poly.constant(Gauss(_exact(number.real), _exact(number.imag)))
    if isinstance(value, prim.Variable):
        return Poly.variable(value.name)
    if isinstance(value, prim.CommonSubexpression):
        return scalar(value.child, leaf)
    if isinstance(value, prim.Sum):
        total = ZERO
        for child in value.children:
            total = total + scalar(child, leaf)
        return total
    if isinstance(value, prim.Product):
        total = ONE
        for child in value.children:
            total = total * scalar(child, leaf)
        return total
    if isinstance(value, prim.Quotient):
        denominator = scalar(value.denominator, leaf).value()
        if denominator is None or not denominator:
            raise OutsideFragment(
                f"{value} divides by {value.denominator}, which is not a nonzero constant"
            )
        return scalar(value.numerator, leaf) * Poly.constant(denominator.inverse())
    if isinstance(value, prim.Power):
        exponent = value.exponent
        if not isinstance(exponent, numbers.Integral) or isinstance(exponent, bool) or exponent < 0:
            raise OutsideFragment(f"{value} has an exponent that is not a literal natural")
        base, total = scalar(value.base, leaf), ONE
        for _ in range(int(exponent)):
            total = total * base
        return total
    raise OutsideFragment(f"{value!r} is not a polynomial in the parameters")


def _exact(number: float) -> Fraction:
    if number != number or number in (float("inf"), float("-inf")):
        raise OutsideFragment(f"{number} is not a finite number")
    return Fraction(number)


# }}}


# {{{ operators


@dataclass(frozen=True, order=True)
class Symbol:
    """One boundary operator: ``I``, or the direct value of ``S``, ``D``, ``S'`` or ``D'``."""

    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class OneSided:
    """The limit of one layer potential on the boundary, from one side.

    ``kind`` is ``"trace"`` or ``"normal_derivative"``, ``potential`` is
    ``"S"`` or ``"D"``, and ``side`` is ``INTERIOR`` or ``EXTERIOR``, or the name
    of a variable standing for either, which is what a jump relation is stated
    with.
    """

    kind: str
    potential: str
    side: int | str

    def __str__(self) -> str:
        return f"{self.kind}({self.potential}, {_side_text(self.side)})"


#: The order terms print in, which is the order they are usually written in.
_ORDER = {"I": 0, "D": 1, "S": 2, "D'": 3, "S'": 4}


def _sort_key(atom: Symbol | OneSided) -> tuple:
    if isinstance(atom, Symbol):
        return (0, _ORDER.get(atom.name, 9), atom.name)
    return (1, atom.kind, atom.potential, str(atom.side))


def _side_text(side: int | str) -> str:
    if side == INTERIOR:
        return "INTERIOR"
    if side == EXTERIOR:
        return "EXTERIOR"
    return str(side)


class Operator:
    """A finite linear combination of boundary operators and one-sided limits.

    Arithmetic builds new operators: a sum, a difference, a negation, and a
    multiple by a scalar (a number, or a pymbolic expression that is a
    polynomial in parameters, see :func:`scalar`). A composition of two
    operators is outside the algebra and refused. ``==`` builds an
    :class:`Equation`, as a lanky term's builds a proposition, so that an
    axiom can state a jump relation; :func:`same` is the comparison.

    ``kernel`` names the kernel, for an operator the pytential adapter
    translated, and is ``None`` for the operators of this module, which stand
    for the problem's kernel. Two named kernels in one operator are refused.
    """

    __slots__ = ("kernel", "shown", "terms", "traced")

    def __init__(
        self,
        terms: dict[Symbol | OneSided, Poly],
        *,
        kernel: str | None = None,
        shown: str | None = None,
        traced: tuple[str, Operator, int | str] | None = None,
    ) -> None:
        ordered = sorted(terms.items(), key=lambda item: _sort_key(item[0]))
        self.terms = {atom: coefficient for atom, coefficient in ordered if coefficient}
        self.kernel = kernel
        #: How the operator was written, when that reads better than its terms.
        self.shown = shown
        #: For a limit taken with trace() or normal_derivative(): what of, and from where.
        self.traced = traced

    # {{{ arithmetic

    def _combine(self, other: Operator, sign: int) -> Operator:
        kernel = _one_kernel(self.kernel, other.kernel)
        terms = dict(self.terms)
        for atom, coefficient in other.terms.items():
            terms[atom] = terms.get(atom, ZERO) + (coefficient if sign > 0 else -coefficient)
        return Operator(terms, kernel=kernel)

    def __add__(self, other: Any) -> Operator:
        if isinstance(other, Operator):
            return self._combine(other, +1)
        if _is_zero(other):
            return self
        return NotImplemented

    def __radd__(self, other: Any) -> Operator:
        return self.__add__(other)

    def __sub__(self, other: Any) -> Operator:
        if isinstance(other, Operator):
            return self._combine(other, -1)
        if _is_zero(other):
            return self
        return NotImplemented

    def __rsub__(self, other: Any) -> Operator:
        if _is_zero(other):
            return -self
        return NotImplemented

    def __neg__(self) -> Operator:
        return self.scaled(-ONE)

    def scaled(self, factor: Poly) -> Operator:
        """This operator times a polynomial."""
        return Operator(
            {atom: factor * c for atom, c in self.terms.items()}, kernel=self.kernel
        )

    def __mul__(self, other: Any) -> Operator:
        if isinstance(other, Operator):
            raise OutsideFragment(
                f"({self}) composed with ({other}) is a product of operators, which is "
                "outside this algebra"
            )
        try:
            factor = scalar(other)
        except OutsideFragment:
            if isinstance(other, prim.ExpressionNode):
                raise
            return NotImplemented
        return self.scaled(factor)

    def __rmul__(self, other: Any) -> Operator:
        return self.__mul__(other)

    def __truediv__(self, other: Any) -> Operator:
        divisor = scalar(other).value()
        if divisor is None or not divisor:
            raise OutsideFragment(f"({self}) / {other}: the divisor is not a nonzero constant")
        return self.scaled(Poly.constant(divisor.inverse()))

    # }}}

    def __eq__(self, other: Any) -> Equation:  # type: ignore[override]
        """Build the proposition ``self == other``; :func:`same` compares."""
        return Equation(self, _operator(other))

    __hash__ = object.__hash__

    def __str__(self) -> str:
        if self.shown is not None:
            return self.shown
        if not self.terms:
            return "0"
        return _joined([_summand_text(atom, c) for atom, c in self.terms.items()])

    def __repr__(self) -> str:
        return f"<operator {self}>"


def _summand_text(atom: Symbol | OneSided, coefficient: Poly) -> str:
    name = str(atom)
    if coefficient == ONE:
        return name
    if coefficient == -ONE:
        return f"-{name}"
    text = str(coefficient)
    if len(coefficient.terms) > 1:
        text = f"({text})"
    return f"{text}*{name}"


def _is_zero(value: Any) -> bool:
    return isinstance(value, numbers.Number) and not isinstance(value, bool) and value == 0


def _operator(value: Any) -> Operator:
    if isinstance(value, Operator):
        return value
    if _is_zero(value):
        return Operator({})
    raise OutsideFragment(f"{value!r} is not an operator of this algebra")


def _one_kernel(left: str | None, right: str | None) -> str | None:
    if left is not None and right is not None and left != right:
        raise OutsideFragment(
            f"two kernels in one operator, {left} and {right}; these rules speak of one"
        )
    return left if left is not None else right


def same(left: Operator, right: Operator) -> bool:
    """Whether two operators have the same terms with the same coefficients."""
    return left.terms == right.terms


I = Operator({Symbol("I"): ONE})  # noqa: E741 - the identity is I in every reference
S = Operator({Symbol("S"): ONE})
D = Operator({Symbol("D"): ONE})
Sp = Operator({Symbol("S'"): ONE})
Dp = Operator({Symbol("D'"): ONE})

#: The operators a trace can be taken of: the layer potentials.
_POTENTIALS = ("S", "D")


def trace(u: Operator, side: Any) -> Operator:
    """The limit of the representation ``u`` on the boundary from ``side``: its Dirichlet trace."""
    return _one_sided("trace", u, side)


def normal_derivative(u: Operator, side: Any) -> Operator:
    """The limit of ``u``'s normal derivative on the boundary from ``side``: its Neumann trace."""
    return _one_sided("normal_derivative", u, side)


def _one_sided(kind: str, u: Operator, side: Any) -> Operator:
    if isinstance(side, prim.Variable):
        side_key: int | str = side.name
    elif (
        isinstance(side, numbers.Integral)
        and not isinstance(side, bool)
        and side in (INTERIOR, EXTERIOR)
    ):
        side_key = int(side)
    else:
        raise ValueError(f"a side is INTERIOR (-1) or EXTERIOR (+1), not {side!r}")
    terms: dict[Symbol | OneSided, Poly] = {}
    for atom, coefficient in u.terms.items():
        if not isinstance(atom, Symbol) or atom.name not in _POTENTIALS:
            raise OutsideFragment(
                f"{kind}({u}, ...) takes the limit of {atom}, and only a layer "
                "potential, S or D, has one here"
            )
        terms[OneSided(kind, atom.name, side_key)] = coefficient
    return Operator(
        terms,
        kernel=u.kernel,
        shown=f"{kind}({u}, {_side_text(side_key)})",
        traced=(kind, u, side_key),
    )


# }}}


# {{{ propositions, and the sorts axioms quantify over


class Proposition:
    """A claim about operators, which Python has no truth value for."""

    def __invert__(self) -> Not:
        return Not(self)

    def __bool__(self) -> bool:
        raise TypeError(f"{self} is a claim about operators; lanky check decides it")


@dataclass(frozen=True, eq=False)
class Equation(Proposition):
    """``left == right``, as written in a jump relation."""

    left: Operator
    right: Operator

    def __str__(self) -> str:
        return f"{self.left} == {self.right}"


@dataclass(frozen=True, eq=False)
class Compact(Proposition):
    """The operator is compact."""

    operator: Operator

    def __str__(self) -> str:
        return f"compact({self.operator})"


@dataclass(frozen=True, eq=False)
class ScalarPlusCompact(Proposition):
    """The operator is ``c*I`` plus a compact operator, for some number ``c``."""

    operator: Operator

    def __str__(self) -> str:
        return f"scalar_plus_compact({self.operator})"


@dataclass(frozen=True, eq=False)
class Not(Proposition):
    """The claim does not hold."""

    claim: Proposition

    def __str__(self) -> str:
        return f"~{self.claim}"


def compact(operator: Operator) -> Compact:
    """The claim that ``operator`` is compact."""
    return Compact(operator)


def scalar_plus_compact(operator: Operator) -> ScalarPlusCompact:
    """The claim that ``operator`` is a multiple of the identity plus a compact operator."""
    return ScalarPlusCompact(operator)


class _Sort:
    """A sort an axiom quantifies over, which lanky's tester has no sampler for."""

    def __init__(self, text: str) -> None:
        self.text = text

    def __repr__(self) -> str:
        return self.text


#: The boundaries the axioms speak of: closed, and of class C².
C2Boundary = _Sort("C2Boundary")

#: The two sides of a boundary: INTERIOR, -1, and EXTERIOR, +1.
Side = _Sort("Side")


# }}}


# {{{ rules, read off axioms


@dataclass(frozen=True)
class JumpRule:
    """What an axiom says a one-sided limit of one potential is."""

    kind: str
    potential: str
    side: str
    right: Operator
    axiom: Any

    def at(self, side: int) -> Operator:
        """The limit from ``side``: the axiom's right-hand side with ``side`` put in."""
        value = Gauss(Fraction(side))
        return Operator(
            {atom: c.substitute(self.side, value) for atom, c in self.right.terms.items()}
        )


class RuleSet:
    """The rules the engine may apply, each read off an ``@axiom``.

    Three statements are rules:

    - ``trace(P, s) == rhs`` and ``normal_derivative(P, s) == rhs``, for a
      potential ``P`` and a variable ``s`` of sort :data:`Side`: the limit of
      ``P`` from either side, with ``rhs`` a combination of boundary operators
      whose coefficients mention ``s`` alone;
    - ``compact(A)``, for one boundary operator ``A`` other than ``I``;
    - ``~scalar_plus_compact(A)``, for one boundary operator ``A``.

    Building a rule set also installs the oracle that reads it,
    :class:`LayerRules`, in lanky's registry; installing it twice is
    installing it once.

    Raises:
        TypeError: If an axiom's statement is none of the three.
        ValueError: If two axioms give a rule for the same thing.
    """

    def __init__(self, *axioms: Any) -> None:
        registry.register_oracle(ORACLE)
        self.axioms = axioms
        self.jumps: dict[tuple[str, str], JumpRule] = {}
        self.classes: dict[str, tuple[str, Any]] = {}
        for axiom in axioms:
            self._read(axiom)

    def _read(self, axiom: Any) -> None:
        name = getattr(axiom, "__name__", repr(axiom))
        goal = getattr(axiom, "goal", None)
        if getattr(axiom, "noun", None) != "axiom":
            raise TypeError(f"{name}: a rule is read off an @axiom, and this is not one")
        if isinstance(goal, Equation):
            self._read_jump(axiom, name, goal)
        elif isinstance(goal, Compact):
            self._classify(axiom, name, goal.operator, "compact")
        elif isinstance(goal, Not) and isinstance(goal.claim, ScalarPlusCompact):
            self._classify(axiom, name, goal.claim.operator, "not scalar plus compact")
        else:
            raise TypeError(
                f"{name}: {goal} is not a rule these operators have; a rule is a jump "
                "relation, compact(A), or ~scalar_plus_compact(A)"
            )

    def _read_jump(self, axiom: Any, name: str, goal: Equation) -> None:
        left = goal.left
        atoms = list(left.terms.items())
        if len(atoms) != 1 or not isinstance(atoms[0][0], OneSided) or atoms[0][1] != ONE:
            raise TypeError(f"{name}: a jump relation has one limit of one potential on the left")
        limit = atoms[0][0]
        sides = [var for var, sort in axiom.variables if sort is Side]
        if not isinstance(limit.side, str) or limit.side not in sides:
            raise TypeError(
                f"{name}: a jump relation is stated for a side variable of sort Side, "
                f"and {_side_text(limit.side)} is not one of its variables"
            )
        for atom, coefficient in goal.right.terms.items():
            if not isinstance(atom, Symbol) or coefficient.names() - {limit.side}:
                raise TypeError(
                    f"{name}: the right-hand side of a jump relation is a combination of "
                    f"boundary operators whose coefficients mention {limit.side} alone"
                )
        key = (limit.kind, limit.potential)
        if key in self.jumps:
            raise ValueError(
                f"{name} and {self.jumps[key].axiom.__name__} both give the "
                f"{limit.kind} of {limit.potential}"
            )
        self.jumps[key] = JumpRule(limit.kind, limit.potential, limit.side, goal.right, axiom)

    def _classify(self, axiom: Any, name: str, operator: Operator, kind: str) -> None:
        atoms = list(operator.terms.items())
        if len(atoms) != 1 or not isinstance(atoms[0][0], Symbol) or atoms[0][1] != ONE:
            raise TypeError(f"{name}: {kind} is said of one boundary operator")
        symbol = atoms[0][0].name
        if symbol == "I":
            raise TypeError(
                f"{name}: I is the identity, which these rules know already and which "
                "is neither compact nor anything else an axiom need say"
            )
        if symbol in self.classes:
            raise ValueError(
                f"{name} and {self.classes[symbol][1].__name__} both say what kind of "
                f"operator {symbol} is"
            )
        self.classes[symbol] = (kind, axiom)

    # {{{ the claims

    def second_kind(self, fn: Any) -> BoundaryEquation:
        """Decorate a function returning ``(trace, operator)``: the operator is second kind."""
        return registry.register_object(BoundaryEquation(fn, rules=self, verdict=SECOND_KIND))

    def first_kind(self, fn: Any) -> BoundaryEquation:
        """Decorate a function returning ``(trace, operator)``: the operator is compact."""
        return registry.register_object(BoundaryEquation(fn, rules=self, verdict=FIRST_KIND))

    def not_second_kind(self, *operators: Operator) -> Callable[[Any], BoundaryEquation]:
        """A decorator: the operator is not second kind, because of the operators named.

        Raises:
            TypeError: If no operator is named, one is named twice, or one is
                not a boundary operator.
        """
        names: list[str] = []
        for operator in operators:
            atoms = list(operator.terms)
            if len(atoms) != 1 or not isinstance(atoms[0], Symbol):
                raise TypeError(
                    f"not_second_kind names boundary operators, and {operator} is not one"
                )
            if atoms[0].name in names:
                raise TypeError(f"not_second_kind names {atoms[0].name} twice")
            names.append(atoms[0].name)
        if not names:
            raise TypeError("not_second_kind names the operator that makes it so, as in (Dp)")
        verdict = Verdict("not second kind", tuple(sorted(names, key=lambda n: _ORDER.get(n, 9))))

        def decorate(fn: Any) -> BoundaryEquation:
            return registry.register_object(BoundaryEquation(fn, rules=self, verdict=verdict))

        return decorate

    # }}}


# }}}


# {{{ the engine


@dataclass(frozen=True)
class Resolved:
    """An operator with every one-sided limit replaced by its jump rule's value."""

    operator: Operator
    applied: tuple[Any, ...]
    steps: tuple[str, ...]


def resolve(operator: Operator, rules: RuleSet) -> Resolved:
    """Replace every one-sided limit in ``operator`` by what its jump relation gives.

    Raises:
        OutsideFragment: For a limit taken from a side that is a variable, or
            one no axiom of ``rules`` gives.
    """
    total = Operator({}, kernel=operator.kernel)
    applied: list[Any] = []
    steps: list[str] = []
    for atom, coefficient in operator.terms.items():
        if isinstance(atom, Symbol):
            total = total + Operator({atom: coefficient})
            continue
        if not isinstance(atom.side, int):
            raise OutsideFragment(f"{atom} is taken from a side that is a variable")
        rule = rules.jumps.get((atom.kind, atom.potential))
        if rule is None:
            raise OutsideFragment(f"no axiom gives the {atom.kind} of {atom.potential}")
        value = rule.at(atom.side)
        steps.append(f"{atom} = {value} by {rule.axiom.__name__}")
        total = total + value.scaled(coefficient)
        if not any(rule.axiom is seen for seen in applied):
            applied.append(rule.axiom)
    return Resolved(total, tuple(applied), tuple(steps))


@dataclass(frozen=True)
class Classification:
    """What kind of operator a boundary operator is, and what says so."""

    kind: str
    identity: Poly
    offending: tuple[str, ...]
    applied: tuple[Any, ...]
    reason: str


def classify(operator: Operator, rules: RuleSet) -> Classification:
    """Second kind, first kind, or not second kind, with the axioms that say so.

    One-sided limits in ``operator`` are resolved first (:func:`resolve`).

    Raises:
        OutsideFragment: When the verdict would depend on a parameter's value,
            when two operators are not a multiple of the identity plus a
            compact one, and when no axiom says what kind an operator is.
    """
    resolved = resolve(operator, rules)
    applied = list(resolved.applied)
    identity = ZERO
    compact_part: list[tuple[str, Any]] = []
    offending: list[tuple[str, Poly, Any]] = []
    for atom, coefficient in resolved.operator.terms.items():
        assert isinstance(atom, Symbol)
        if atom.name == "I":
            identity = coefficient
            continue
        entry = rules.classes.get(atom.name)
        if entry is None:
            raise OutsideFragment(f"no axiom says whether {atom.name} is compact")
        kind, axiom = entry
        if kind == "compact":
            compact_part.append((atom.name, axiom))
        else:
            offending.append((atom.name, coefficient, axiom))
    applied += [axiom for _, axiom in compact_part]
    compact_text = (
        "the rest is compact ("
        + ", ".join(f"{name} by {axiom.__name__}" for name, axiom in compact_part)
        + ")"
        if compact_part
        else "nothing else is left"
    )
    if len(offending) > 1:
        raise OutsideFragment(
            f"{' and '.join(name for name, _, _ in offending)} are both not a multiple of "
            "the identity plus a compact operator, and a combination of two such can be "
            "one, which these rules cannot tell"
        )
    if offending:
        name, coefficient, axiom = offending[0]
        value = coefficient.value()
        if value is None:
            raise OutsideFragment(
                f"the coefficient {coefficient} of {name} mentions "
                f"{', '.join(sorted(coefficient.names()))}, so the verdict depends on its value"
            )
        applied.append(axiom)
        return Classification(
            "not second kind",
            identity,
            (name,),
            tuple(applied),
            f"{name} is not c*I + compact ({axiom.__name__}) and its coefficient is {value}, "
            f"not 0, while {compact_text}: the operator is not c*I + compact either",
        )
    value = identity.value()
    if value is None:
        raise OutsideFragment(
            f"the identity coefficient {identity} mentions "
            f"{', '.join(sorted(identity.names()))}, so the verdict depends on its value"
        )
    if value:
        return Classification(
            "second kind",
            identity,
            (),
            tuple(applied),
            f"the identity coefficient is {value}, not 0, and {compact_text}",
        )
    return Classification(
        "first kind",
        identity,
        (),
        tuple(applied),
        f"the identity coefficient is 0 and {compact_text}: the operator is compact",
    )


@dataclass(frozen=True)
class Verdict:
    """What kind of equation a boundary operator is claimed to give."""

    kind: str
    offending: tuple[str, ...] = ()

    @property
    def text(self) -> str:
        """The claim in words, as the ledger's statement ends."""
        if self.kind == "first kind":
            return "first kind: no identity term"
        if self.kind == "not second kind":
            return f"not second kind: {', '.join(self.offending)} is not c*I + compact"
        return self.kind


SECOND_KIND = Verdict("second kind")
FIRST_KIND = Verdict("first kind")


@dataclass(frozen=True, eq=False)
class JumpRewrite(RewriteTerm):
    """A boundary equation's rewrite, with the rules that may decide it."""

    rules: Any = None


@dataclass(frozen=True, eq=False)
class VerdictQuestion:
    """Whether a boundary operator is the kind of operator the verdict says.

    ``identity`` is the identity coefficient the claim's coefficient fact
    states, when it has one, which the answer has to agree with.
    """

    operator: Operator
    verdict: Verdict
    rules: Any
    identity: Gauss | None = None

    def __str__(self) -> str:
        return f"{self.operator} is {self.verdict.text}"


@dataclass(frozen=True)
class Decision:
    """The engine's answer to one claim: whether it holds, why, and on what."""

    holds: bool
    reason: str
    applied: tuple[Any, ...]
    steps: tuple[str, ...] = ()


def decide(term: JumpRewrite | VerdictQuestion) -> Decision:
    """Decide a rewrite or a verdict.

    Raises:
        OutsideFragment: For a claim outside what the rules decide.
    """
    if isinstance(term, JumpRewrite):
        return _decide_rewrite(term)
    return _decide_verdict(term)


def _decide_rewrite(term: JumpRewrite) -> Decision:
    rules = term.rules
    source, target = resolve(term.source, rules), resolve(term.target, rules)
    applied = _unique(source.applied + target.applied)
    steps = source.steps + target.steps
    kernels = (term.source.kernel, term.target.kernel)
    if None not in kernels and kernels[0] != kernels[1]:
        return Decision(
            False, f"the trace is of the {kernels[0]} kernel and the target of the {kernels[1]}",
            applied, steps,
        )
    if same(source.operator, target.operator):
        return Decision(
            True,
            f"{term.source} = {source.operator} by {_names(applied)}",
            applied,
            steps,
        )
    return Decision(
        False,
        f"the jump relations give {term.source} = {source.operator} "
        f"({_names(applied) or 'no axiom'}), and the target is {target.operator}: "
        f"they differ by {source.operator - target.operator}",
        applied,
        steps,
    )


def _decide_verdict(term: VerdictQuestion) -> Decision:
    found = classify(term.operator, term.rules)
    claimed = term.verdict
    if term.identity is not None and found.identity != Poly.constant(term.identity):
        return Decision(
            False,
            f"the coefficient fact states an identity coefficient of {term.identity}, and "
            f"the rules give {found.identity}",
            found.applied,
        )
    if found.kind != claimed.kind:
        return Decision(False, f"{term.operator} is {found.kind}: {found.reason}", found.applied)
    if found.offending != claimed.offending:
        return Decision(
            False,
            f"the operator that is not c*I + compact is {', '.join(found.offending)}, "
            f"not {', '.join(claimed.offending)}",
            found.applied,
        )
    return Decision(True, found.reason, found.applied)


def _unique(axioms: Iterable[Any]) -> tuple[Any, ...]:
    out: list[Any] = []
    for axiom in axioms:
        if not any(axiom is seen for seen in out):
            out.append(axiom)
    return tuple(out)


def _names(axioms: Iterable[Any]) -> str:
    return ", ".join(axiom.__name__ for axiom in axioms)


class LayerRules:
    """The oracle: the engine above, answering the facts a boundary equation claims.

    Its trust class is ``decision-procedure``: see the module's docstring for
    the fragment it is complete for. A fact it decides rests, in addition to
    what it rested on already, on the axioms the decision applied, so the
    ledger says what the verdict is decided under. A claim outside the
    fragment is declined, and the reason is kept in the provenance as
    ``declined``.
    """

    name = "layer-rules"

    def trust_class(self) -> str:
        """Complete for its fragment, relative to the axioms it reads."""
        return "decision-procedure"

    def can_establish(self, fact: Fact, /) -> bool:
        """Willing to try a boundary equation's rewrite or verdict."""
        return isinstance(fact.term, JumpRewrite | VerdictQuestion)

    def establish(self, fact: Fact, /) -> Fact | None:
        """``DECIDED`` or ``REFUTED``, resting on the axioms applied; or declined."""
        try:
            decision = decide(fact.term)
        except OutsideFragment as exc:
            return fact.with_status(fact.status, declined=f"{self.name}: {exc}")
        applied = [axiom.fact_id for axiom in decision.applied]
        fact = replace(
            fact,
            rests_on=(*fact.rests_on, *(id_ for id_ in applied if id_ not in fact.rests_on)),
        )
        if decision.holds:
            return fact.with_status(
                Status.DECIDED, self.name, detail=decision.reason, derivation=list(decision.steps)
            )
        return fact.with_status(
            Status.REFUTED, self.name, reason=decision.reason, derivation=list(decision.steps)
        )


#: The one oracle every rule set installs.
ORACLE = LayerRules()


# }}}


# {{{ the claims


class BoundaryEquation(Rewrite):
    """A representation's trace, the boundary operator it is claimed to be, and a verdict.

    Decorated through a :class:`RuleSet` (``@rules.second_kind``,
    ``@rules.first_kind``, ``@rules.not_second_kind(Dp)``) on a function of no
    arguments that returns ``(trace(u, side), operator)`` or the same with
    ``normal_derivative``. The docstring's first line names the problem.

    Raises:
        TypeError: If the function does not return two operators, the first
            of them a limit taken with :func:`trace` or
            :func:`normal_derivative`.
    """

    def __init__(self, fn: Any, *, rules: RuleSet, verdict: Verdict) -> None:
        self.rules = rules
        self.verdict = verdict
        super().__init__(fn, obligation=OBLIGATION)
        if not isinstance(self.source, Operator) or self.source.traced is None:
            raise TypeError(
                f"{self.qualname} at {self.where}: a boundary equation starts from "
                "trace(u, side) or normal_derivative(u, side)"
            )
        if not isinstance(self.target, Operator):
            raise TypeError(
                f"{self.qualname} at {self.where}: the boundary operator is an operator "
                f"of this algebra, not {self.target!r}"
            )

    # {{{ what it says

    @property
    def problem(self) -> str:
        """The first line of the docstring, without its full stop."""
        lines = (self.__doc__ or self.qualname).strip().splitlines()
        return lines[0].rstrip(".")

    @property
    def representation(self) -> Operator:
        """``u``, the representation whose limit the source is."""
        assert self.source.traced is not None
        return self.source.traced[1]

    @property
    def data(self) -> str:
        """``"f"`` for Dirichlet data, ``"g"`` for Neumann data."""
        assert self.source.traced is not None
        return "f" if self.source.traced[0] == "trace" else "g"

    @property
    def term(self) -> JumpRewrite:
        return JumpRewrite(self.source, self.target, self.obligation, self.rules)

    def identity(self) -> Gauss | None:
        """The identity coefficient of the target, once its limits are resolved.

        ``None`` when that coefficient mentions a parameter or the target is
        outside the fragment: then there is no arithmetic to state, and the
        verdict is declined anyway.
        """
        try:
            resolved = resolve(self.target, self.rules).operator
        except OutsideFragment:
            return None
        return resolved.terms.get(Symbol("I"), ZERO).value()

    # }}}

    # {{{ its facts

    def coefficient_fact(self) -> Fact | None:
        """For a second-kind claim, the identity coefficient's being nonzero, as integer arithmetic.

        Core Lean has no rationals, so the fact compares the numerators: a
        Gaussian rational ``p/q + (r/s)*i`` is not zero exactly when ``p`` or
        ``r`` is not. The term is built node by node, so that Python does not
        answer it, and it is lanky's, so that Lean and the property tester
        take it like any other.
        """
        if self.verdict.kind != "second kind":
            return None
        value = self.identity()
        if value is None:
            return None
        real = Comparison(value.re.numerator, "!=", 0)
        imaginary = Comparison(value.im.numerator, "!=", 0)
        if value.re and value.im:
            term: Any = LogicalOr((real, imaginary))
        else:
            # a zero coefficient states 0 != 0, which is false, and is refuted
            term = imaginary if value.im else real
        return Fact(
            id=fact_id("coefficient", self.qualname, module=self.module, line=self.line),
            kind="coefficient",
            statement=f"coefficient of I: {value} != 0",
            term=term,
            status=Status.ASSUMED,
            provenance={"path": self.path, "line": self.line, "coefficient": str(value)},
            where=self.where,
            owner=self.qualname,
        )

    def facts(self) -> tuple[Fact, ...]:
        """The rewrite, the coefficient when there is one, and the verdict resting on both."""
        rewrite = self.fact()
        coefficient = self.coefficient_fact()
        rests_on = [rewrite.id] + ([coefficient.id] if coefficient is not None else [])
        question = VerdictQuestion(
            self.target,
            self.verdict,
            self.rules,
            self.identity() if coefficient is not None else None,
        )
        verdict = Fact(
            id=fact_id("verdict", self.qualname, module=self.module, line=self.line),
            kind="verdict",
            statement=str(question),
            term=question,
            status=Status.ASSUMED,
            provenance={"path": self.path, "line": self.line},
            where=self.where,
            owner=self.qualname,
            rests_on=tuple(rests_on),
        )
        return (rewrite, *([coefficient] if coefficient is not None else []), verdict)

    # }}}

    # {{{ deciding it without the ledger

    def decide_rewrite(self) -> Decision:
        """The engine's answer about the rewrite (see :func:`decide`)."""
        return decide(self.term)

    def decide_verdict(self) -> Decision:
        """The engine's answer about the verdict (see :func:`decide`)."""
        return decide(VerdictQuestion(self.target, self.verdict, self.rules))

    # }}}


# }}}


# {{{ the pytential adapter

_NORMAL = re.compile(r"normal_e(\d+)")


@dataclass(frozen=True)
class _Layer:
    potential: str
    limit: Any

    def __str__(self) -> str:
        return f"{self.potential} (qbx_forced_limit={self.limit!r})"


@dataclass(frozen=True)
class _Gradient:
    potential: str
    limit: Any
    axis: int


def from_pytential(expr: Any, density: str = "sigma") -> Operator:
    """The operator a pytential ``sym`` expression applies to the density ``density``.

    ``expr`` is built from ``sym.S``, ``sym.D``, ``sym.Sp`` and ``sym.Dp`` of
    one Laplace or Helmholtz kernel applied to ``sym.var(density)``, the
    density itself (which is the identity), and scalar coefficients that are
    polynomials in parameters (see :func:`scalar`). ``qbx_forced_limit`` is
    read as the side: ``None`` is a potential off the boundary, which is what
    a representation holds, ``+1`` and ``-1`` a limit from the exterior or the
    interior, and ``"avg"`` the direct value.

    pytential builds ``sym.Sp`` and ``sym.Dp`` as a normal vector dotted with
    the gradient in the target, one target derivative per axis, and ``sym.D``
    with the normal as its source direction. Both are recognized by reading
    the normal's components, the common subexpressions pytential names
    ``normal_e0``, ``normal_e1``, ..., as unknowns: the coefficient of the
    derivative along axis ``i`` has to be the ``i``-th of them, times the same
    scalar for every axis. pytential gives every boundary's normal those
    names, so each component is read with the geometry the descriptors
    inside it name, and it has to be the normal of the boundary the operator
    is on.

    The rules speak of one boundary, so every ``IntG`` has to have its
    density on one geometry and its targets on one, and a limit on the
    boundary has to be taken on the density's own; pytential's default
    descriptors are read as the one boundary. A factor on the density inside
    an operator has to be a constant. A parameter there could be a function
    on the boundary, which does not come out of the operator, and every
    coefficient here is a number that does.

    Raises:
        OutsideFragment: For anything else: another kernel, two kernels, a
            density other than ``density``, a target derivative that is not
            a normal derivative, a potential mixed with boundary operators,
            two geometries, or a factor inside an operator that is not a
            constant.
    """
    kernel: list[Any] = []
    terms = _walk(expr, density, kernel)
    gradients: dict[tuple[str, Any], dict[int, Poly]] = {}
    out: dict[Symbol | OneSided, Poly] = {}
    limits = set()
    for atom, coefficient in terms.items():
        if isinstance(atom, _Gradient):
            gradients.setdefault((atom.potential, atom.limit), {})[atom.axis] = coefficient
            continue
        if _normal_names(coefficient):
            raise OutsideFragment(
                f"{atom} is multiplied by {coefficient}, a normal component, outside a "
                "normal derivative"
            )
        if isinstance(atom, _Layer):
            limits.add(atom.limit is None)
            key = _boundary_atom(atom.potential, atom.limit, normal=False)
        else:
            limits.add(False)
            key = atom
        out[key] = out.get(key, ZERO) + coefficient
    dim = kernel[0][1] if kernel else 0
    # the normal a normal derivative is along is the one of the boundary it is taken on
    on = kernel[0][2][1] if kernel else None
    for (potential, limit), by_axis in gradients.items():
        if sorted(by_axis) != list(range(dim)):
            raise OutsideFragment(
                f"target derivatives of {potential} along axes {sorted(by_axis)} are not a "
                f"gradient in {dim} dimensions"
            )
        common = None
        for axis, coefficient in by_axis.items():
            reduced = _divide_by_normal(coefficient, axis, on)
            if reduced is None or (common is not None and reduced != common):
                raise OutsideFragment(
                    f"the target derivatives of {potential} are not weighted by the normal "
                    "of the boundary they are taken on"
                )
            common = reduced
        if limit is None:
            raise OutsideFragment(
                f"the normal derivative of {potential} off the boundary has no normal to take"
            )
        limits.add(False)
        key = _boundary_atom(potential, limit, normal=True)
        out[key] = out.get(key, ZERO) + (common or ZERO)
    if len(limits) > 1:
        raise OutsideFragment(
            "the expression mixes potentials off the boundary with boundary operators"
        )
    return Operator(out, kernel=kernel[0][0] if kernel else None)


def _boundary_atom(potential: str, limit: Any, normal: bool) -> Symbol | OneSided:
    if limit is None:
        return Symbol(potential)
    if limit == "avg":
        return Symbol(f"{potential}'" if normal else potential)
    if limit in (INTERIOR, EXTERIOR):
        return OneSided("normal_derivative" if normal else "trace", potential, int(limit))
    raise OutsideFragment(f"qbx_forced_limit={limit!r} is not a side these rules read")


def _normal_leaf(value: Any) -> Poly | None:
    """A component of a boundary's normal as an unknown, named for its axis and its boundary."""
    if isinstance(value, prim.CommonSubexpression):
        match = _NORMAL.fullmatch(str(value.prefix or ""))
        if match:
            return Poly.variable(_normal_name(int(match.group(1)), _normal_geometry(value.child)))
    return None


def _normal_name(axis: int, geometry: Any) -> str:
    """``normal[0]@'circle'``: the unknown for one component of one boundary's normal."""
    return f"normal[{axis}]@{geometry!r}"


class _Unknown:
    """The boundary of a normal whose nodes name none, or several: no boundary is it."""

    def __repr__(self) -> str:
        return "<no one boundary>"


_NO_ONE_BOUNDARY = _Unknown()


def _normal_geometry(expr: Any) -> Any:
    """The geometry a normal's component is computed on, read off the descriptors in it.

    pytential names the components of every boundary's normal alike,
    ``normal_e0``, ``normal_e1``, ..., and what tells one boundary's from
    another's is the DOF descriptors of the nodes inside, which name the
    geometry. One geometry, the default one read as ``None`` (see
    :func:`_geometry`), is the answer; for none or several the answer is a
    boundary no operator is on, so the component matches no normal.
    """
    found: list[Any] = []
    pending = [expr]
    while pending:
        node = pending.pop()
        if hasattr(node, "geometry") and hasattr(node, "granularity"):
            geometry = _geometry(node)
            if not any(geometry == seen for seen in found):
                found.append(geometry)
        elif isinstance(node, tuple | list):
            pending.extend(node)
        elif dataclasses.is_dataclass(node) and not isinstance(node, type):
            pending.extend(getattr(node, field.name) for field in dataclasses.fields(node))
        elif isinstance(node, prim.ExpressionNode):
            pending.extend(node.__getinitargs__())
    return found[0] if len(found) == 1 else _NO_ONE_BOUNDARY


def _normal_names(poly: Poly) -> set[str]:
    return {name for name in poly.names() if name.startswith("normal[")}


def _divide_by_normal(poly: Poly, axis: int, geometry: Any) -> Poly | None:
    """``poly`` over the ``axis``-th component of ``geometry``'s normal.

    ``None`` unless every term has that component once and no other.
    """
    wanted = _normal_name(axis, geometry)
    items = []
    for monomial, coefficient in poly.terms:
        normals = [(n, p) for n, p in monomial if n.startswith("normal[")]
        if normals != [(wanted, 1)]:
            return None
        items.append((tuple((n, p) for n, p in monomial if n != wanted), coefficient))
    return Poly.of(items)


def _is_density(value: Any, density: str) -> bool:
    while isinstance(value, prim.CommonSubexpression):
        value = value.child
    return isinstance(value, prim.Variable) and value.name == density


def _mentions_operator(value: Any, density: str) -> bool:
    """Whether the density, or an operator applied to it, is anywhere in ``value``.

    Every node :func:`scalar` reads a polynomial from is looked into, so that
    no density reaches it to be read as a parameter: ``sigma**1 * S(sigma)``
    is no multiple of ``S``.
    """
    if _is_density(value, density) or type(value).__name__ == "IntG":
        return True
    if isinstance(value, prim.CommonSubexpression):
        return _mentions_operator(value.child, density)
    if isinstance(value, prim.Sum | prim.Product):
        return any(_mentions_operator(child, density) for child in value.children)
    if isinstance(value, prim.Quotient):
        return _mentions_operator(value.numerator, density) or _mentions_operator(
            value.denominator, density
        )
    if isinstance(value, prim.Power):
        return _mentions_operator(value.base, density) or _mentions_operator(
            value.exponent, density
        )
    return False


def _walk(value: Any, density: str, kernel: list[Any]) -> dict[Any, Poly]:
    """The terms of an operator expression, before normal derivatives are put together."""
    if _is_density(value, density):
        return {Symbol("I"): ONE}
    if type(value).__name__ == "IntG":
        return dict([_intg(value, density, kernel)])
    if isinstance(value, prim.CommonSubexpression):
        return _walk(value.child, density, kernel)
    if isinstance(value, prim.Sum):
        total: dict[Any, Poly] = {}
        for child in value.children:
            for atom, coefficient in _walk(child, density, kernel).items():
                total[atom] = total.get(atom, ZERO) + coefficient
        return total
    if isinstance(value, prim.Product):
        bearing = [child for child in value.children if _mentions_operator(child, density)]
        if len(bearing) > 1:
            raise OutsideFragment(f"{value} multiplies operators together")
        factor = ONE
        for child in value.children:
            if not bearing or child is not bearing[0]:
                factor = factor * scalar(child, _normal_leaf)
        if not bearing:
            return _constant_term(factor, value)
        return {atom: factor * c for atom, c in _walk(bearing[0], density, kernel).items()}
    if isinstance(value, prim.Quotient) and not _mentions_operator(value.denominator, density):
        divisor = scalar(value.denominator, _normal_leaf).value()
        if divisor is None or not divisor:
            raise OutsideFragment(f"{value} divides by something that is not a nonzero constant")
        inverse = Poly.constant(divisor.inverse())
        return {atom: inverse * c for atom, c in _walk(value.numerator, density, kernel).items()}
    if _mentions_operator(value, density):
        raise OutsideFragment(f"{value!r} applies the density in a way this adapter does not read")
    return _constant_term(scalar(value, _normal_leaf), value)


def _density_factor(value: Any, density: str) -> Poly | None:
    """``c`` when ``value`` is a scalar ``c`` times the density, and ``None`` otherwise.

    An operator applied to ``c`` times the density is ``c`` times the operator
    applied to it. pytential's ``DirichletOperator`` divides the density by
    its weight, which is 1 without L2 weighting, so what it applies its
    operators to is ``sigma / 1``.
    """
    while isinstance(value, prim.CommonSubexpression):
        value = value.child
    if isinstance(value, prim.Variable) and value.name == density:
        return ONE
    if isinstance(value, prim.Quotient) and not _mentions_operator(value.denominator, density):
        inner = _density_factor(value.numerator, density)
        divisor = scalar(value.denominator, _normal_leaf).value()
        if inner is None or divisor is None or not divisor:
            return None
        return inner * Poly.constant(divisor.inverse())
    if isinstance(value, prim.Product):
        bearing = [child for child in value.children if _mentions_operator(child, density)]
        if len(bearing) != 1:
            return None
        inner = _density_factor(bearing[0], density)
        if inner is None:
            return None
        for child in value.children:
            if child is not bearing[0]:
                inner = inner * scalar(child, _normal_leaf)
        return inner
    return None


def _geometry(descriptor: Any) -> Any:
    """The geometry a pytential DOF descriptor names, and ``None`` for the default one."""
    geometry = getattr(descriptor, "geometry", descriptor)
    if isinstance(geometry, type) and geometry.__name__ in ("DEFAULT_SOURCE", "DEFAULT_TARGET"):
        return None
    return geometry


def _places_text(places: tuple[Any, Any]) -> str:
    source, target = ("the default" if place is None else repr(place) for place in places)
    return f"the density on {source} and the targets on {target}"


def _constant_term(factor: Poly, value: Any) -> dict[Any, Poly]:
    if factor:
        raise OutsideFragment(f"{value} is a term with no density in it")
    return {}


def _intg(node: Any, density: str, kernel: list[Any]) -> tuple[_Layer | _Gradient, Poly]:
    """One ``IntG`` as a layer potential, or one axis of the gradient of one, and its factor.

    The factor is the scalar the density is multiplied by (see
    :func:`_density_factor`), which is 1 but for a weight.
    """
    if len(node.source_kernels) != 1 or len(node.densities) != 1:
        raise OutsideFragment("an IntG with several source kernels is not one layer potential")
    factor = _density_factor(node.densities[0], density)
    if factor is None:
        raise OutsideFragment(f"an IntG applied to {node.densities[0]}, not to {density}")
    if factor.value() is None:
        raise OutsideFragment(
            f"an IntG applied to {density} times {factor}: only a constant comes out of an "
            "operator, and a parameter inside one could be a function on the boundary"
        )
    limit = node.qbx_forced_limit
    if isinstance(limit, bool) or limit not in (None, INTERIOR, EXTERIOR, "avg"):
        raise OutsideFragment(f"qbx_forced_limit={limit!r} is not a side these rules read")
    places = (_geometry(getattr(node, "source", None)), _geometry(getattr(node, "target", None)))
    if limit is not None and places[0] != places[1]:
        raise OutsideFragment(
            f"a limit taken with {_places_text(places)}: the jump relations are about the "
            "boundary the density is on"
        )
    target = node.target_kernel
    axis = None
    if type(target).__name__ == "AxisTargetDerivative":
        axis, target = int(target.axis), target.inner_kernel
    source = node.source_kernels[0]
    potential = "S"
    direction = None
    if type(source).__name__ == "DirectionalSourceDerivative":
        direction = source.dir_vec_name
        vector = node.kernel_arguments[direction]
        for index, component in enumerate(vector):
            if scalar(component, _normal_leaf) != Poly.variable(_normal_name(index, places[0])):
                raise OutsideFragment(
                    "a source derivative along something that is not the normal of the "
                    "boundary the density is on"
                )
        potential, source = "D", source.inner_kernel
    if source != target:
        raise OutsideFragment(f"source kernel {source} and target kernel {target} differ")
    family = type(target).__name__
    if family not in ("LaplaceKernel", "HelmholtzKernel") or type(source).__name__ != family:
        raise OutsideFragment(
            f"{target} is not a Laplace or Helmholtz kernel, which the axioms speak of"
        )
    arguments = ", ".join(
        f"{name}={value}"
        for name, value in sorted(node.kernel_arguments.items())
        if name != direction
    )
    name = f"{family.removesuffix('Kernel')}({target.dim}{', ' + arguments if arguments else ''})"
    if kernel and kernel[0][0] != name:
        raise OutsideFragment(f"two kernels in one expression, {kernel[0][0]} and {name}")
    if kernel and kernel[0][2] != places:
        raise OutsideFragment(
            f"two geometries in one expression, {_places_text(kernel[0][2])} and "
            f"{_places_text(places)}; these rules speak of one boundary"
        )
    if not kernel:
        kernel.append((name, int(target.dim), places))
    if axis is None:
        return _Layer(potential, limit), factor
    return _Gradient(potential, limit, axis), factor


# }}}
