"""Exact reals for the property tester: rationals, and enclosures where they stop.

The design idea. Lean reads a statement over ``Real`` in ``ℝ``, and the property
tester used to read it in floating point, so an identity that holds only up to
rounding was refuted by the one and proved by the other: ``exp(x + y) ==
exp(x) * exp(y)`` and ``(x + 0.1) - 0.1 == x`` were both refuted (#33). A
refutation is meant to be as definite as a proof, and a rounding error is no
counterexample, so the tester reads real numbers exactly.

A draw of ``Real`` is a :class:`~fractions.Fraction`, whatever its exactness
class, and a draw of ``Complex`` is a :class:`ComplexValue` with two fractions
for parts. Ring arithmetic and true division are exact on them, which is all
that ``(x + 0.1) - 0.1 == x`` and ``x / y * y == x`` need. A float literal is the
rational number Python holds, as the Lean printer reads it, and a complex
literal is its two parts read the same way (:func:`exact`); ``n / 2`` of an
integer is the fraction (:func:`quotient`).

Where the rationals stop, at ``exp``, ``log`` and ``sqrt`` and the complex
``exp`` (:func:`elementary`), a value is *enclosed*: an :class:`Interval` is a
closed interval with rational endpoints that contains the real number it stands
for, and arithmetic on one gives an interval that contains the result. The
endpoints are rounded outward to :data:`PRECISION` significant bits, which
keeps the arithmetic cheap and the enclosure rigorous. A value that is rational
after all is given exactly: ``exp(0)`` is ``1``, ``log(1)`` is ``0`` and
``sqrt(9/4)`` is ``3/2``.

A comparison with an enclosure in it has three answers (:func:`compare`). When
the enclosures prove it, it is true; when they exclude it, it is false, and
that is a counterexample as definite as a proof; when they straddle it, they
say neither, and the draw decides nothing. An equality needs one more rule.
Two enclosures can never show two transcendental numbers equal, so
``exp(x + y) == exp(x) * exp(y)`` would be undecided at every draw. Where the
statement asserts an equality, standing ``POSITIVE``
(:class:`lanky.terms.Polarity`), agreement to within narrow enclosures
(:func:`agree`) counts as holding: that is evidence, which is what ``TESTED``
means, as a sampled universal that held at every draw is. Anywhere else, under
a negation, in a hypothesis or a guard, or used as a value, the ``True`` would
be used as a certainty, and the draw is undecided. An order that the
enclosures straddle is undecided wherever it stands.

One enclosure is one real number. The exponential of an argument is computed
once and cached, so ``exp(x) == exp(y)`` at a draw where ``x`` and ``y`` are
the same fraction compares one enclosure with itself, and that is equal for
certain, which Python's containers take for granted as well. So is an
operation on enclosures: ``2 * exp(x)`` computed twice at one draw is one
object, which is what lets a table the tester fills from the definition
``f(i) == 2 * exp(x)`` satisfy that definition when it is read back as a
hypothesis. An enclosure less itself is ``0``, and over itself ``1``, and
``exp(x) - exp(x)``, which pymbolic evaluates as ``exp(x) + (-1) * exp(x)``,
is ``0`` as well.

An infinity or a NaN is a float and no real number. An enclosure is below
``inf`` for certain, and a NaN equals nothing, as Python compares them, but
arithmetic with either, or a function of either, leaves the draw undecided.

What is not enclosed is left undecided, never guessed: a complex logarithm or
square root (the printer declines both, see :mod:`lanky.lean`), an exponential,
a cosine or a sine of an argument beyond :data:`EXP_LIMIT`, and a negative
number to a power that is not an integer, which Python answers with a complex
number. A logarithm or a square root outside its Python domain raises
:class:`~lanky.terms.UndefinedValue`, as Python's functions do, which is the gap
to Mathlib's total functions that :mod:`lanky.semantics` notes; an argument
whose enclosure reaches the edge of the domain is undecided, since which side
it is on is not known.

Nothing here changes what a file computes when it runs: ``lanky.exp(0.5)`` at a
number is Python's float, and so is :func:`lanky.terms.evaluate` at floats. The
exact reading is the property tester's, and :func:`lanky.terms.exact_reading`
turns it on.
"""

from __future__ import annotations

import functools
import math
import numbers
from collections import OrderedDict
from collections.abc import Callable
from fractions import Fraction
from typing import Any

from lanky.terms import Undecided, UndefinedValue

__all__ = [
    "AGREEMENT",
    "EXP_LIMIT",
    "NUMBER_TYPES",
    "PRECISION",
    "ComplexValue",
    "Interval",
    "agree",
    "compare",
    "describe",
    "elementary",
    "exact",
    "exp_value",
    "log_value",
    "power",
    "quotient",
    "sqrt_value",
]

#: The significant bits an enclosure's endpoints are rounded to. Far more than a
#: comparison of the values the tester draws needs, and few enough to be cheap.
PRECISION = 128

#: The bits two enclosures have to agree to for an equality between them to be
#: evidence (:func:`agree`).
AGREEMENT = 64

#: The largest magnitude of an argument that ``exp``, and the cosine and sine
#: of a complex exponential, are enclosed at. ``exp(16384)`` has some twenty
#: thousand bits; past this, an argument is undecided rather than enclosed.
EXP_LIMIT = 2**14

#: The bits a series is summed with beyond :data:`PRECISION`, which absorb its
#: rounding before the result is rounded outward.
_GUARD = 32

#: ``log 2`` to about sixteen digits, used only to pick the multiple of it to
#: take out of an exponent: any multiple is sound, and this one leaves a small
#: remainder.
_LN2_NEAR = Fraction(0.6931471805599453)


# {{{ rounding


def _floor_scaled(q: Fraction, shift: int) -> int:
    """``floor(q * 2**shift)``."""
    if shift >= 0:
        return (q.numerator << shift) // q.denominator
    return q.numerator // (q.denominator << -shift)


def _dyadic(mantissa: int, shift: int) -> Fraction:
    """``mantissa / 2**shift``."""
    if shift >= 0:
        return Fraction(mantissa, 1 << shift)
    return Fraction(mantissa << -shift)


def _round(q: Fraction, up: bool, bits: int = PRECISION) -> Fraction:
    """``q`` rounded outward to ``bits`` significant bits: up when ``up``, down otherwise.

    A rational that is short already is kept as it is, so that an endpoint such
    as ``1/3`` stays exact; only a long one is rounded, and always in the
    direction that keeps the number inside the interval.
    """
    if q.numerator.bit_length() + q.denominator.bit_length() <= 2 * bits:
        return q
    shift = bits - (q.numerator.bit_length() - q.denominator.bit_length())
    if up:
        return _dyadic(-_floor_scaled(-q, shift), shift)
    return _dyadic(_floor_scaled(q, shift), shift)


def describe(q: Any, spec: str = "") -> str:
    """A number for a reason or a repr.

    A short rational is written as one, ``3/2``; a long one as the float
    nearest it, formatted by ``spec`` when one is given, or as a power of two
    when it is too large or too small for a float. An enclosure is its repr.
    """
    if isinstance(q, Interval | ComplexValue):
        return repr(q)
    if isinstance(q, numbers.Rational):
        q = Fraction(int(q.numerator), int(q.denominator))
        if not spec and q.numerator.bit_length() <= 64 and q.denominator.bit_length() <= 64:
            return str(q)
    elif not isinstance(q, numbers.Real):
        return repr(q)
    try:
        number = float(q)
    except OverflowError:
        number = math.inf
    if isinstance(q, Fraction) and q and (number == 0 or math.isinf(number)):
        exponent = q.numerator.bit_length() - q.denominator.bit_length()
        return f"{'-' if q < 0 else ''}2**{exponent} (about)"
    return format(number, spec) if spec else repr(number)


def _text(q: Any) -> str:
    """A part of a complex number as its repr shows it: a fraction as ``1/2``."""
    return repr(q) if isinstance(q, Interval) else str(q)


# }}}


# {{{ reading numbers exactly


def _rational(value: Any) -> Fraction | None:
    """A real number that is not an enclosure, as the rational it is; ``None`` otherwise.

    A float is the rational number it holds, as the Lean printer reads one. An
    infinity and a NaN are not real numbers, and neither is anything that is
    not a number.
    """
    if isinstance(value, Fraction):
        return value
    if isinstance(value, numbers.Rational):
        return Fraction(int(value.numerator), int(value.denominator))
    if isinstance(value, numbers.Real):
        number = float(value)
        return Fraction(number) if math.isfinite(number) else None
    return None


def _bounds(value: Any) -> tuple[Fraction, Fraction] | None:
    """A real number as the endpoints of an enclosure of it, or ``None`` for anything else."""
    if isinstance(value, Interval):
        return value.lo, value.hi
    q = _rational(value)
    return None if q is None else (q, q)


def _nonfinite(value: Any) -> bool:
    """Whether ``value`` is a float infinity or NaN, which is a number and not a real one."""
    return (
        isinstance(value, numbers.Real)
        and not isinstance(value, numbers.Rational | Interval)
        and not math.isfinite(float(value))
    )


def _no_infinity(value: Any) -> Undecided:
    """What an infinity or a NaN in the exact reading's arithmetic raises."""
    return Undecided(
        f"{value!r} is a float and no real number, and the exact reading does not "
        "compute with it, so this draw decides nothing"
    )


def _operand(value: Any) -> tuple[Fraction, Fraction] | None:
    """The other operand of an enclosure's arithmetic as its bounds, ``None`` if no number.

    Raises:
        Undecided: For an infinity or a NaN (:func:`_nonfinite`), which Python
            would compute with and the exact reading does not.
    """
    bounds = _bounds(value)
    if bounds is None and _nonfinite(value):
        raise _no_infinity(value)
    return bounds


def _real(value: Any) -> Fraction | Interval:
    """A real number as a rational or an enclosure.

    Raises:
        Undecided: If ``value`` is an infinity or a NaN (:func:`_nonfinite`).
        TypeError: If ``value`` is not a real number.
    """
    if isinstance(value, Interval):
        return value
    q = _rational(value)
    if q is None:
        if _nonfinite(value):
            raise _no_infinity(value)
        raise TypeError(f"{value!r} is not a finite real number")
    return q


def _parts(value: Any) -> tuple[Any, Any] | None:
    """A number as its real and imaginary parts, each a rational or an enclosure."""
    if isinstance(value, ComplexValue):
        return value.real, value.imag
    if isinstance(value, Interval):
        return value, Fraction(0)
    if isinstance(value, complex):
        real, imag = _rational(value.real), _rational(value.imag)
        return None if real is None or imag is None else (real, imag)
    q = _rational(value)
    return None if q is None else (q, Fraction(0))


def _integer(value: Any) -> int | None:
    """An exponent as the integer it is, or ``None`` when it is not one."""
    if isinstance(value, numbers.Integral):
        return int(value)
    if isinstance(value, Fraction) and value.denominator == 1:
        return int(value)
    return None


def _is_zero(value: Any) -> bool:
    """Whether ``value`` is exactly zero, which an enclosure never is."""
    return not isinstance(value, Interval) and value == 0


def exact(value: Any) -> Any:
    """A constant of a term as the exact reading takes it.

    An integer is itself. A finite float is the rational number it holds, and a
    complex number with finite parts a :class:`ComplexValue` of them, which is
    how the Lean printer reads both. Anything else is left as it is.
    """
    if isinstance(value, numbers.Rational):
        return value
    if isinstance(value, complex):
        parts = _parts(value)
        return value if parts is None else ComplexValue(*parts)
    if isinstance(value, numbers.Real):
        q = _rational(value)
        return value if q is None else q
    return value


# }}}


# {{{ enclosures


def _enclosure(lo: Fraction, hi: Fraction, bits: int = PRECISION) -> Fraction | Interval:
    """The number ``[lo, hi]`` encloses, rounded outward: the rational itself when they meet."""
    if lo == hi:
        return lo
    return Interval(_round(lo, False, bits), _round(hi, True, bits))


#: The results of the arithmetic and the functions of enclosures, by operation
#: and operands, so that one operation on the same numbers gives one object
#: (see the module docstring). The operands are kept with the result, so that
#: no ``id`` in a key is taken by another object while the key is here.
_RESULTS: OrderedDict[tuple[Any, ...], tuple[Any, tuple[Any, ...]]] = OrderedDict()

#: How many results :data:`_RESULTS` keeps, the least recently used going first.
#: A result it has let go is computed again as another object, which only
#: decides less: two objects compare by their endpoints.
_RESULTS_KEPT = 1 << 14

#: The operations whose operands can be taken in either order.
_COMMUTATIVE = frozenset(("+", "*"))

#: The bounds of ``0``, ``1`` and ``-1``: adding the first or multiplying by the
#: second gives an enclosure's own object back, and multiplying by the third its
#: negation's.
_ZERO = (Fraction(0), Fraction(0))
_ONE = (Fraction(1), Fraction(1))
_MINUS_ONE = (Fraction(-1), Fraction(-1))


def _identity(value: Any) -> tuple[str, Any]:
    """An operand as part of a key: an enclosure by the object, a rational by its value."""
    if isinstance(value, Interval):
        return ("enclosure", id(value))
    return ("rational", _rational(value))


def _once(operation: str, operands: tuple[Any, ...], compute: Callable[[], Any]) -> Any:
    """``compute()``, as the one object an operation on these operands gives.

    An enclosure is one number, and an operation on the same numbers is one
    number too, so it is given as one object. Without that, a table the tester
    fills from a definition such as ``f(i) == 2 * exp(x)`` holds one enclosure
    and the definition, read again as a hypothesis, computes another with the
    same endpoints, which is no certain equality, and every draw that sets
    ``f`` from ``exp`` is left undecided.
    """
    keys = tuple(_identity(operand) for operand in operands)
    if operation in _COMMUTATIVE:
        keys = tuple(sorted(keys))
    key = (operation, *keys)
    found = _RESULTS.get(key)
    if found is not None:
        _RESULTS.move_to_end(key)
        return found[0]
    result = compute()
    _RESULTS[key] = (result, operands)
    while len(_RESULTS) > _RESULTS_KEPT:
        _RESULTS.popitem(last=False)
    return result


def _negation(value: Interval) -> Interval:
    """``-value``, recorded both ways, so that ``-(-value)`` is ``value`` (:func:`_negates`)."""
    negated = Interval(-value.hi, -value.lo)
    _RESULTS[("neg", _identity(negated))] = (value, (negated,))
    return negated


def _negates(a: Interval, b: Interval) -> bool:
    """Whether ``b`` is the object ``-a`` gave, or ``a`` the one ``-b`` gave."""
    found = _RESULTS.get(("neg", _identity(a)))
    return found is not None and found[0] is b


def _product(
    a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    """The endpoints of the product of two enclosures."""
    corners = (a[0] * b[0], a[0] * b[1], a[1] * b[0], a[1] * b[1])
    return min(corners), max(corners)


def _quotient(
    a: tuple[Fraction, Fraction], b: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction]:
    """The endpoints of the quotient of two enclosures.

    Raises:
        ZeroDivisionError: If the divisor is exactly zero, as Python raises.
        Undecided: If the divisor's enclosure contains zero, so that whether
            this divides by zero is not known.
    """
    lo, hi = b
    if lo <= 0 <= hi:
        if lo == hi:
            raise ZeroDivisionError("division by zero")
        raise Undecided(
            f"the divisor is enclosed in [{describe(lo)}, {describe(hi)}], which contains "
            "zero, so whether this divides by zero is not known at this draw"
        )
    return _product(a, (1 / hi, 1 / lo))


def _power_bound(q: Fraction, k: int, up: bool) -> Fraction:
    """A bound on ``q ** k`` for ``k >= 1``: from above when ``up``, from below otherwise.

    The power is taken by repeated squaring, rounding outward at every step, so
    that a high power of a long endpoint does not grow its digits unrounded.
    """
    if q < 0 and k % 2:
        return -_power_bound(-q, k, not up)
    base, result = abs(q), Fraction(1)
    while True:
        if k & 1:
            result = _round(result * base, up)
        k >>= 1
        if not k:
            return result
        base = _round(base * base, up)


def _integer_power(bounds: tuple[Fraction, Fraction], k: int) -> Fraction | Interval:
    """An enclosure to an integer power, as Python's ``**`` of the number it encloses."""
    lo, hi = bounds
    if k == 0:
        return Fraction(1)
    if k < 0:
        inverse = _bounds(_integer_power(bounds, -k))
        return _enclosure(*_quotient((Fraction(1), Fraction(1)), inverse))
    if k % 2 or lo >= 0:
        return _enclosure(_power_bound(lo, k, False), _power_bound(hi, k, True))
    if hi <= 0:
        return _enclosure(_power_bound(hi, k, False), _power_bound(lo, k, True))
    return _enclosure(Fraction(0), _power_bound(max(-lo, hi), k, True))


def _floor(value: Any) -> int:
    """The floor of a number, which an enclosure has only when it lies between two integers.

    Raises:
        Undecided: If the enclosure contains an integer inside it.
    """
    lo, hi = _bounds(value)
    if math.floor(lo) != math.floor(hi):
        raise Undecided(
            f"{describe(value)} lies across an integer, so its floor is not known at this draw"
        )
    return math.floor(lo)


class Interval:
    """An enclosure of one real number: the closed interval ``[lo, hi]``, with ``lo < hi``.

    Its arithmetic is interval arithmetic, with integers, fractions, floats (as
    the rationals they hold) and other intervals, and every result contains the
    number the operation gives. A result whose endpoints meet is that rational
    number, not an interval. Its comparisons are the three-valued ones of
    :func:`compare`, and a comparison the endpoints do not settle raises
    :class:`~lanky.terms.Undecided`. It is not a truth value, and it has no
    float: an enclosure is converted to nothing that would quietly round it.
    Equality and hashing go by identity otherwise, since one interval object is
    one number and two with the same endpoints need not be.
    """

    __slots__ = ("hi", "lo")

    def __init__(self, lo: Fraction, hi: Fraction) -> None:
        if not lo < hi:
            raise ValueError(f"an enclosure needs lo < hi, not [{lo}, {hi}]")
        self.lo = lo
        self.hi = hi

    # {{{ arithmetic

    # Each operation is computed once for the same operands (:func:`_once`). An
    # infinity or a NaN as the other operand is undecided (:func:`_operand`).
    # The identities an operation with 0, 1 or -1 has keep the object, since
    # pymbolic evaluates a sum from 0 and a product from 1, and a difference as
    # a sum with -1 times the subtrahend: exp(x) - exp(x) is exp(x) + (-1) *
    # exp(x), which is exp(x) plus its own negation, 0.

    def __add__(self, other: Any) -> Any:
        """Enclose ``self + other``: ``self`` plus ``0`` is itself, and plus ``-self`` is ``0``."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        if b == _ZERO:
            return self
        if isinstance(other, Interval) and _negates(self, other):
            return Fraction(0)
        return _once("+", (self, other), lambda: _enclosure(self.lo + b[0], self.hi + b[1]))

    __radd__ = __add__

    def __sub__(self, other: Any) -> Any:
        """Enclose ``self - other``; an enclosure less itself is ``0``, as one number is."""
        if other is self:
            return Fraction(0)
        b = _operand(other)
        if b is None:
            return NotImplemented
        if b == _ZERO:
            return self
        return _once("-", (self, other), lambda: _enclosure(self.lo - b[1], self.hi - b[0]))

    def __rsub__(self, other: Any) -> Any:
        """Enclose ``other - self``."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        if b == _ZERO:
            return -self
        return _once("r-", (self, other), lambda: _enclosure(b[0] - self.hi, b[1] - self.lo))

    def __mul__(self, other: Any) -> Any:
        """Enclose ``self * other``: ``self`` times ``1`` is itself, times ``-1`` is ``-self``."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        if b == _ONE:
            return self
        if b == _MINUS_ONE:
            return -self
        return _once("*", (self, other), lambda: _enclosure(*_product((self.lo, self.hi), b)))

    __rmul__ = __mul__

    def __truediv__(self, other: Any) -> Any:
        """Enclose ``self / other`` (see :func:`_quotient` for a divisor near zero).

        An enclosure over itself is ``1`` where the enclosure excludes zero.
        """
        if other is self and not self.lo <= 0 <= self.hi:
            return Fraction(1)
        b = _operand(other)
        if b is None:
            return NotImplemented
        if b == _ONE:
            return self
        if b == _MINUS_ONE:
            return -self
        return _once("/", (self, other), lambda: _enclosure(*_quotient((self.lo, self.hi), b)))

    def __rtruediv__(self, other: Any) -> Any:
        """Enclose ``other / self``."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        return _once("r/", (self, other), lambda: _enclosure(*_quotient(b, (self.lo, self.hi))))

    def __floordiv__(self, other: Any) -> Any:
        """``floor(self / other)``, where the enclosure settles it."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        return _floor(_enclosure(*_quotient((self.lo, self.hi), b)))

    def __rfloordiv__(self, other: Any) -> Any:
        """``floor(other / self)``, where the enclosure settles it."""
        b = _operand(other)
        if b is None:
            return NotImplemented
        return _floor(_enclosure(*_quotient(b, (self.lo, self.hi))))

    def __mod__(self, other: Any) -> Any:
        """``self - other * floor(self / other)``, Python's remainder."""
        if _operand(other) is None:
            return NotImplemented
        return self - other * (self // other)

    def __rmod__(self, other: Any) -> Any:
        """``other - self * floor(other / self)``."""
        if _operand(other) is None:
            return NotImplemented
        return other - self * (other // self)

    def __pow__(self, exponent: Any) -> Any:
        """Enclose ``self ** k`` for an integer ``k``; :func:`power` takes the rest."""
        k = _integer(exponent)
        if k is None:
            return NotImplemented
        if k == 1:
            return self
        return _once("**", (self, k), lambda: _integer_power((self.lo, self.hi), k))

    def __neg__(self) -> Interval:
        """Enclose ``-self``; the negation of the negation is ``self``, the same object."""
        return _once("neg", (self,), lambda: _negation(self))

    def __pos__(self) -> Interval:
        """``self``."""
        return self

    def __abs__(self) -> Interval:
        """Enclose ``abs(self)``."""
        if self.lo >= 0:
            return self
        if self.hi <= 0:
            return -self
        return _once("abs", (self,), lambda: Interval(Fraction(0), max(-self.lo, self.hi)))

    # }}}

    # {{{ comparisons

    def __eq__(self, other: Any) -> Any:  # type: ignore[override]
        """``self == other``, where the enclosures settle it."""
        return _settled("==", self, other)

    def __ne__(self, other: Any) -> Any:  # type: ignore[override]
        """``self != other``, where the enclosures settle it."""
        return _settled("!=", self, other)

    def __lt__(self, other: Any) -> Any:
        """``self < other``, where the enclosures settle it."""
        return _settled("<", self, other)

    def __le__(self, other: Any) -> Any:
        """``self <= other``, where the enclosures settle it."""
        return _settled("<=", self, other)

    def __gt__(self, other: Any) -> Any:
        """``self > other``, where the enclosures settle it."""
        return _settled(">", self, other)

    def __ge__(self, other: Any) -> Any:
        """``self >= other``, where the enclosures settle it."""
        return _settled(">=", self, other)

    __hash__ = object.__hash__

    # }}}

    def __bool__(self) -> bool:
        """Refuse: an enclosure is not a truth value."""
        raise TypeError(f"{self!r} is an enclosure of a number, not a truth value")

    def __repr__(self) -> str:
        """The midpoint and the radius, as floats."""
        middle, radius = (self.lo + self.hi) / 2, (self.hi - self.lo) / 2
        return f"Interval({describe(middle)} ± {describe(radius, '.1e')})"

    __str__ = __repr__


class ComplexValue:
    """A complex number with exact parts, or an enclosure of one.

    Python's ``complex`` holds two floats, so it cannot be the exact complex
    number a draw of ``Complex`` is. This holds two parts, ``real`` and
    ``imag``, each a rational or an :class:`Interval`, and its arithmetic is the
    field's, part by part: exact where the parts are, and enclosing where they
    are not. ``abs`` is the modulus, as Python's is. Like Python's complex
    numbers it has no order, and like an enclosure it is not a truth value.
    """

    __slots__ = ("imag", "real")

    def __init__(self, real: Any, imag: Any) -> None:
        self.real = real
        self.imag = imag

    def __add__(self, other: Any) -> Any:
        """``self + other``."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return ComplexValue(self.real + b[0], self.imag + b[1])

    __radd__ = __add__

    def __sub__(self, other: Any) -> Any:
        """``self - other``."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return ComplexValue(self.real - b[0], self.imag - b[1])

    def __rsub__(self, other: Any) -> Any:
        """``other - self``."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return ComplexValue(b[0] - self.real, b[1] - self.imag)

    def __mul__(self, other: Any) -> Any:
        """``self * other``."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return _complex_product((self.real, self.imag), b)

    __rmul__ = __mul__

    def __truediv__(self, other: Any) -> Any:
        """``self / other``, raising ``ZeroDivisionError`` at zero, as Python does."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return _complex_quotient((self.real, self.imag), b)

    def __rtruediv__(self, other: Any) -> Any:
        """``other / self``."""
        b = _parts(other)
        if b is None:
            return NotImplemented
        return _complex_quotient(b, (self.real, self.imag))

    def __pow__(self, exponent: Any) -> Any:
        """``self ** k`` for an integer ``k``; a complex power of another kind is not taken."""
        k = _integer(exponent)
        if k is None:
            return NotImplemented
        return _complex_power((self.real, self.imag), k)

    def __neg__(self) -> ComplexValue:
        """``-self``."""
        return ComplexValue(-self.real, -self.imag)

    def __pos__(self) -> ComplexValue:
        """``self``."""
        return self

    def __abs__(self) -> Any:
        """The modulus, exact when it is rational and enclosed otherwise."""
        return sqrt_value(self.real**2 + self.imag**2)

    def __eq__(self, other: Any) -> Any:  # type: ignore[override]
        """``self == other``, where the parts settle it."""
        return _settled("==", self, other)

    def __ne__(self, other: Any) -> Any:  # type: ignore[override]
        """``self != other``, where the parts settle it."""
        return _settled("!=", self, other)

    __hash__ = object.__hash__

    def __bool__(self) -> bool:
        """Refuse: a number is not a truth value."""
        raise TypeError(f"{self!r} is a complex number, not a truth value")

    def __repr__(self) -> str:
        """The two parts, a fraction written ``1/2``."""
        return f"ComplexValue({_text(self.real)}, {_text(self.imag)})"

    __str__ = __repr__


def _complex_product(a: tuple[Any, Any], b: tuple[Any, Any]) -> ComplexValue:
    """``(a0 + a1 i) * (b0 + b1 i)``."""
    return ComplexValue(a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0])


def _complex_quotient(a: tuple[Any, Any], b: tuple[Any, Any]) -> ComplexValue:
    """``(a0 + a1 i) / (b0 + b1 i)``, over the squared modulus of the divisor."""
    modulus = b[0] ** 2 + b[1] ** 2
    return ComplexValue(
        (a[0] * b[0] + a[1] * b[1]) / modulus, (a[1] * b[0] - a[0] * b[1]) / modulus
    )


def _complex_power(parts: tuple[Any, Any], k: int) -> ComplexValue:
    """A complex number to an integer power, by repeated squaring."""
    if k < 0:
        return _complex_quotient((Fraction(1), Fraction(0)), _parts(_complex_power(parts, -k)))
    result, base = (Fraction(1), Fraction(0)), parts
    while k:
        if k & 1:
            result = _parts(_complex_product(result, base))
        k >>= 1
        if k:
            base = _parts(_complex_product(base, base))
    return ComplexValue(*result)


#: The number types of the exact reading that Python does not have. A comparison
#: with one of them is answered by :func:`compare`.
NUMBER_TYPES = (Interval, ComplexValue)


# }}}


# {{{ comparisons


def _comparable(value: Any) -> tuple[Any, Any] | None:
    """A number as the bounds a comparison reads: an infinity is its own, as Python has it."""
    bounds = _bounds(value)
    if bounds is None and _nonfinite(value) and not math.isnan(float(value)):
        return float(value), float(value)
    return bounds


def _order(op: str, left: Any, right: Any) -> bool | None:
    """``left <op> right`` for two real numbers, or ``None`` where their enclosures overlap.

    An enclosure is of a real number, so it is below ``inf`` and above
    ``-inf`` for certain, and a NaN is equal to nothing and in no order, as
    Python compares one.
    """
    if any(_nonfinite(side) and math.isnan(float(side)) for side in (left, right)):
        return op == "!="
    if left is right:
        return op in ("==", "<=", ">=")
    a, b = _comparable(left), _comparable(right)
    if a is None or b is None:
        return NotImplemented  # type: ignore[return-value]
    (alo, ahi), (blo, bhi) = a, b
    if op == "<":
        return True if ahi < blo else False if alo >= bhi else None
    if op == "<=":
        return True if ahi <= blo else False if alo > bhi else None
    if op == ">":
        return True if alo > bhi else False if ahi <= blo else None
    if op == ">=":
        return True if alo >= bhi else False if ahi < blo else None
    if alo == ahi == blo == bhi:
        equal: bool | None = True
    elif ahi < blo or bhi < alo:
        equal = False
    else:
        equal = None
    if op == "==":
        return equal
    return None if equal is None else not equal


def compare(op: str, left: Any, right: Any) -> bool | None:
    """What the enclosures say about ``left <op> right``: ``True``, ``False``, or ``None``.

    ``True`` when the enclosures prove the comparison and ``False`` when they
    exclude it; either is certain. ``None`` when they straddle it, which is
    what the caller decides about (see :meth:`lanky.terms.LankyEvaluationMapper.map_comparison`).
    One object compared with itself is equal to itself. A complex number is
    compared part by part, and only for equality.

    Returns ``NotImplemented`` when an operand is not a number at all, so that
    the comparison is Python's.

    Raises:
        TypeError: For an order between complex numbers, which Python refuses too.
    """
    if isinstance(left, ComplexValue | complex) or isinstance(right, ComplexValue | complex):
        if op not in ("==", "!="):
            raise TypeError(f"'{op}' is not defined between complex numbers, which have no order")
        if left is right:
            return op == "=="
        a, b = _parts(left), _parts(right)
        if a is None or b is None:
            return NotImplemented  # type: ignore[return-value]
        real, imag = _order("==", a[0], b[0]), _order("==", a[1], b[1])
        if real is False or imag is False:
            equal: bool | None = False
        elif real and imag:
            equal = True
        else:
            equal = None
        if op == "==":
            return equal
        return None if equal is None else not equal
    return _order(op, left, right)


def _settled(op: str, left: Any, right: Any) -> Any:
    """``left <op> right`` as a truth value, for a comparison outside the evaluator.

    Raises:
        Undecided: If the enclosures straddle it.
    """
    answer = compare(op, left, right)
    if answer is None:
        raise Undecided(
            f"{describe(left)} {op} {describe(right)} is not settled by the enclosures, "
            "which overlap"
        )
    return answer


def _narrow(left: Any, right: Any) -> bool:
    """Whether two real numbers are enclosed to :data:`AGREEMENT` bits of their size.

    The size is at least ``1``, so below one the bits are absolute: the
    difference of two sides that cancel, ``exp(x) * exp(-x) - 1``, is enclosed
    around zero to the width the product had, and agrees with ``0``.
    """
    a, b = _bounds(left), _bounds(right)
    if a is None or b is None:
        return False
    size = max(Fraction(1), abs(a[0]), abs(a[1]), abs(b[0]), abs(b[1]))
    tolerance = size / (1 << AGREEMENT)
    return a[1] - a[0] <= tolerance and b[1] - b[0] <= tolerance


def agree(left: Any, right: Any) -> bool:
    """Whether two numbers the enclosures cannot tell apart are enclosed narrowly.

    Two enclosures that overlap agree to their width, and that is what an
    equality between them is worth as evidence. Enclosures a long computation
    has widened past :data:`AGREEMENT` bits of the size of the numbers say too
    little, and an equality between them is left undecided. A complex number
    agrees when both of its parts do.
    """
    a, b = _parts(left), _parts(right)
    if a is None or b is None:
        return False
    return _narrow(a[0], b[0]) and _narrow(a[1], b[1])


# }}}


# {{{ division and powers


def quotient(numerator: Any, denominator: Any) -> Any:
    """True division in the exact reading: ``n / 2`` of two integers is the fraction.

    Raises:
        ZeroDivisionError: At a zero divisor, as Python raises.
    """
    if isinstance(numerator, numbers.Integral) and isinstance(denominator, numbers.Integral):
        return Fraction(int(numerator), int(denominator))
    return numerator / denominator


def power(base: Any, exponent: Any) -> Any:
    """``base ** exponent`` in the exact reading.

    An integer exponent is exact on a rational base, a negative one on an
    integer base included (Python's ``2 ** -1`` is a float, and here it is
    ``1/2``), and encloses on an enclosed base. A power that is not an integer
    is ``exp(exponent * log(base))`` for a positive base, and a square root,
    exact where it is rational, when the exponent's denominator is two. A zero
    base to a positive power is zero, and to a power that is not positive
    raises ``ZeroDivisionError``, as Python's ``0 ** -0.5`` does.

    Raises:
        Undecided: For a negative base to a power that is not an integer, which
            Python answers with a complex number, a complex power that is not
            an integer power, and a base or an exponent whose enclosure leaves
            its sign unknown.
    """
    k = _integer(exponent)
    if k is not None:
        if isinstance(base, numbers.Integral) and k < 0:
            return Fraction(int(base)) ** k
        return base**k
    if isinstance(base, ComplexValue | complex) or isinstance(exponent, ComplexValue | complex):
        raise Undecided(
            f"{describe(base)} ** {describe(exponent)} is a complex power that is not an "
            "integer power, which the tester does not enclose, so this draw decides nothing"
        )
    base, exponent = _real(base), _real(exponent)
    positive = _order(">", base, 0)
    if positive is None:
        raise Undecided(
            f"the base {describe(base)} of a power that is not an integer power may be "
            "zero or negative at this draw, so the power is not known"
        )
    if not positive:
        if not _is_zero(base):
            raise Undecided(
                f"{describe(base)} ** {describe(exponent)} is a negative number to a power "
                "that is not an integer, which Python answers with a complex number "
                "and the tester does not read, so this draw decides nothing"
            )
        above = _order(">", exponent, 0)
        if above is None:
            raise Undecided(
                f"0 ** {describe(exponent)} is 0 or a division by zero, and the "
                "exponent's enclosure does not say which"
            )
        if above:
            return Fraction(0)
        raise ZeroDivisionError("0 cannot be raised to a negative power")
    if isinstance(exponent, Fraction) and exponent.denominator == 2:
        return sqrt_value(power(base, exponent.numerator))
    return exp_value(exponent * log_value(base))


# }}}


# {{{ the elementary functions


def elementary(function: str, value: Any) -> Any:
    """``exp``, ``log`` or ``sqrt`` of a number, in the exact reading.

    A real argument (an integer, a fraction, a float as the rational it holds,
    or an enclosure) gives :func:`exp_value`, :func:`log_value` or
    :func:`sqrt_value`, and a complex one gives the complex exponential. A
    complex logarithm or square root is not enclosed: the printer declines
    both, since Python picks a side of the branch cut by the sign of a zero,
    and the draw decides nothing.

    Raises:
        UndefinedValue: If Python's function has no value there: the logarithm
            of a number that is not positive, or the square root of a negative
            one.
        Undecided: Where the exact reading has no enclosure (see the module
            docstring).
        TypeError: If ``value`` is not a number, a ``bool`` included.
        ValueError: If ``function`` is not one of the three.
    """
    if function not in ("exp", "log", "sqrt"):
        raise ValueError(f"unknown elementary function {function!r}")
    if isinstance(value, bool) or not isinstance(value, numbers.Complex | Interval | ComplexValue):
        raise TypeError(f"{function} takes a number, not {value!r}")
    if isinstance(value, ComplexValue | complex):
        parts = _parts(value)
        if parts is None:
            raise TypeError(f"{value!r} is not a finite complex number")
        if function == "exp":
            return _complex_exp(*parts)
        raise Undecided(
            f"{function}({describe(value)}) is a complex {function}, which the tester "
            "does not enclose: Python picks a side of its branch cut by the sign of a "
            "zero, which an exact number does not have, so this draw decides nothing"
        )
    x = _real(value)
    if function == "exp":
        return exp_value(x)
    if function == "log":
        return log_value(x)
    return sqrt_value(x)


def _undefined(function: str, value: Any, why: str) -> UndefinedValue:
    """The gap a function outside its Python domain is, worded as Python's own is."""
    return UndefinedValue(
        f"{function}({describe(value)}) has no value in Python ({why}), while "
        "Mathlib's function is total"
    )


def exp_value(x: Fraction | Interval) -> Fraction | Interval:
    """``exp(x)``: ``1`` at zero, and an enclosure anywhere else.

    Raises:
        Undecided: For an argument beyond :data:`EXP_LIMIT`.
    """
    if isinstance(x, Interval):
        return _once("exp", (x,), lambda: _enclosure(_exp_bounds(x.lo)[0], _exp_bounds(x.hi)[1]))
    if x == 0:
        return Fraction(1)
    return _exp_enclosure(Fraction(x))


def log_value(x: Fraction | Interval) -> Fraction | Interval:
    """``log(x)``: ``0`` at one, and an enclosure at any other positive number.

    Raises:
        UndefinedValue: If ``x`` is not positive, where Python raises.
        Undecided: If ``x`` is an enclosure that reaches zero.
    """
    if isinstance(x, Interval):
        if x.hi <= 0:
            raise _undefined("log", x, "its argument is not positive")
        if x.lo <= 0:
            raise Undecided(
                f"log({x!r}) is of an enclosure that reaches zero, so whether it has a "
                "value in Python is not known at this draw"
            )
        return _once("log", (x,), lambda: _enclosure(_log_bounds(x.lo)[0], _log_bounds(x.hi)[1]))
    if x <= 0:
        raise _undefined("log", x, "its argument is not positive")
    if x == 1:
        return Fraction(0)
    return _log_enclosure(Fraction(x))


def sqrt_value(x: Fraction | Interval) -> Fraction | Interval:
    """``sqrt(x)``: exact where it is rational, and an enclosure where it is not.

    Raises:
        UndefinedValue: If ``x`` is negative, where Python raises.
        Undecided: If ``x`` is an enclosure that reaches below zero.
    """
    if isinstance(x, Interval):
        if x.hi < 0:
            raise _undefined("sqrt", x, "its argument is negative")
        if x.lo < 0:
            raise Undecided(
                f"sqrt({x!r}) is of an enclosure that reaches below zero, so whether "
                "it has a value in Python is not known at this draw"
            )
        return _once("sqrt", (x,), lambda: _enclosure(_sqrt_bounds(x.lo)[0], _sqrt_bounds(x.hi)[1]))
    if x < 0:
        raise _undefined("sqrt", x, "its argument is negative")
    return _sqrt_exact(Fraction(x))


@functools.lru_cache(maxsize=4096)
def _exp_enclosure(q: Fraction) -> Interval:
    """The enclosure of ``exp(q)``, one object per argument (see the module docstring)."""
    return Interval(*_exp_bounds(q))


@functools.lru_cache(maxsize=4096)
def _log_enclosure(q: Fraction) -> Interval:
    """The enclosure of ``log(q)``, one object per argument."""
    return Interval(*_log_bounds(q))


@functools.lru_cache(maxsize=4096)
def _sqrt_exact(q: Fraction) -> Fraction | Interval:
    """``sqrt(q)``, the rational when it is one, and one enclosure per argument otherwise."""
    lo, hi = _sqrt_bounds(q)
    return lo if lo == hi else Interval(lo, hi)


@functools.cache
def _ln2(bits: int) -> tuple[Fraction, Fraction]:
    """Bounds on ``log 2``, summing ``2 atanh(1/3)`` in fixed point with ``bits`` bits.

    Each term ``1 / ((2k + 1) 3**(2k + 1))`` is floored to a unit of
    ``2**-bits``, by less than one unit, and the series stops at the first term
    that floors to zero, after which the rest is below two units.
    """
    one = 1 << bits
    total, count, power_of_three = 0, 0, 3
    while term := one // (power_of_three * (2 * count + 1)):
        total += term
        count += 1
        power_of_three *= 9
    return Fraction(2 * total, one), Fraction(2 * (total + count + 2), one)


def _exp_series(r: Fraction, bits: int) -> tuple[Fraction, Fraction]:
    """Bounds on ``e**r`` for ``|r| <= 1/2``, from the Taylor series in fixed point.

    The ``n``-th term is the one before times ``r / n``, floored to a unit of
    ``2**-bits``; the error it carries is at most half the one before plus one
    unit, so below two units. The sum stops after the first term of at most
    one unit, and what it leaves out is then below three units.
    """
    if abs(r) > Fraction(1, 2):
        raise ValueError(f"the series is summed for |r| <= 1/2, not at {r}")
    one = 1 << bits
    numerator, denominator = r.numerator, r.denominator
    term = total = one
    n = 0
    while abs(term) > 1:
        n += 1
        term = term * numerator // (denominator * n)
        total += term
    margin = 2 * n + 8
    return Fraction(total - margin, one), Fraction(total + margin, one)


def _exp_bounds(q: Fraction) -> tuple[Fraction, Fraction]:
    """Bounds on ``exp(q)``: ``2**k * exp(r)`` with ``q = k log 2 + r``, and ``r`` small.

    Raises:
        Undecided: For an argument beyond :data:`EXP_LIMIT`.
    """
    if q == 0:
        return Fraction(1), Fraction(1)
    if abs(q) > EXP_LIMIT:
        raise Undecided(
            f"exp({describe(q)}) is beyond the arguments the tester encloses "
            f"(|x| <= {EXP_LIMIT}), so this draw decides nothing"
        )
    bits = PRECISION + _GUARD
    k = round(q / _LN2_NEAR)
    ln2_lo, ln2_hi = _ln2(bits + abs(k).bit_length() + 2)
    if k >= 0:
        r_lo, r_hi = q - k * ln2_hi, q - k * ln2_lo
    else:
        r_lo, r_hi = q - k * ln2_lo, q - k * ln2_hi
    scale = Fraction(2) ** k
    lower = _exp_series(r_lo, bits)[0] * scale
    upper = _exp_series(r_hi, bits)[1] * scale
    return _round(lower, False), _round(upper, True)


def _atanh_series(z: Fraction, bits: int) -> tuple[Fraction, Fraction]:
    """Bounds on ``atanh(z)`` for ``0 <= z < 1/3``, from its series in fixed point.

    Each power ``z**(2k + 1)`` is the one before times ``z**2``, floored, so it
    is off by less than ``9/8`` of a unit, and a term divides it, floored again,
    so that the ``k`` terms are off by less than three units each. The sum
    stops at the first power that floors to zero, after which the rest is below
    two units.
    """
    one = 1 << bits
    numerator, denominator = z.numerator, z.denominator
    square_numerator, square_denominator = numerator * numerator, denominator * denominator
    power_of_z = one * numerator // denominator
    total, count = 0, 0
    while power_of_z:
        total += power_of_z // (2 * count + 1)
        count += 1
        power_of_z = power_of_z * square_numerator // square_denominator
    margin = 3 * count + 4
    return Fraction(total - margin, one), Fraction(total + margin, one)


def _log_bounds(q: Fraction) -> tuple[Fraction, Fraction]:
    """Bounds on ``log(q)`` for ``q > 0``.

    With ``q = 2**e m`` and ``1 <= m < 2``, ``log(q)`` is ``e log 2 + 2
    atanh((m - 1) / (m + 1))``, and the atanh's argument is below ``1/3``.
    """
    bits = PRECISION + _GUARD
    e = q.numerator.bit_length() - q.denominator.bit_length()
    m = q / Fraction(2) ** e
    if m < 1:
        e, m = e - 1, m * 2
    elif m >= 2:
        e, m = e + 1, m / 2
    lo, hi = _atanh_series((m - 1) / (m + 1), bits)
    ln2_lo, ln2_hi = _ln2(bits + abs(e).bit_length() + 2)
    if e >= 0:
        base_lo, base_hi = e * ln2_lo, e * ln2_hi
    else:
        base_lo, base_hi = e * ln2_hi, e * ln2_lo
    return _round(base_lo + 2 * lo, False), _round(base_hi + 2 * hi, True)


def _sqrt_bounds(q: Fraction) -> tuple[Fraction, Fraction]:
    """Bounds on ``sqrt(q)`` for ``q >= 0``, which meet where the root is rational.

    ``sqrt(n / d)`` is ``sqrt(n d) / d``, and the integer square root of
    ``n d`` scaled by a power of four brackets it between two neighbours.
    """
    product = q.numerator * q.denominator
    root = math.isqrt(product)
    if root * root == product:
        exact_root = Fraction(root, q.denominator)
        return exact_root, exact_root
    shift = max(0, PRECISION + _GUARD - product.bit_length() // 2)
    root = math.isqrt(product << (2 * shift))
    scale = q.denominator << shift
    return _round(Fraction(root, scale), False), _round(Fraction(root + 1, scale), True)


def _cos_sin(x: Fraction | Interval) -> tuple[Any, Any]:
    """``cos(x)`` and ``sin(x)``, exact at zero and enclosed anywhere else.

    An enclosed argument is read at its midpoint and widened by its radius,
    which the cosine and the sine cannot move by more than, since neither has a
    slope steeper than one.
    """
    if isinstance(x, Interval):
        middle, radius = (x.lo + x.hi) / 2, (x.hi - x.lo) / 2
        return _once(
            "cos sin", (x,), lambda: tuple(_widen(value, radius) for value in _cos_sin(middle))
        )
    if x == 0:
        return Fraction(1), Fraction(0)
    return _cos_sin_enclosure(Fraction(x))


def _widen(value: Any, radius: Fraction) -> Fraction | Interval:
    """An enclosure of ``value`` widened by ``radius`` on both sides."""
    lo, hi = _bounds(value)
    return _enclosure(lo - radius, hi + radius)


def _square_bounds(a: tuple[Fraction, Fraction], bits: int) -> tuple[Fraction, Fraction]:
    """The endpoints of the square of an enclosure, rounded outward at ``bits``."""
    lo, hi = a
    if lo >= 0:
        low, high = lo * lo, hi * hi
    elif hi <= 0:
        low, high = hi * hi, lo * lo
    else:
        low, high = Fraction(0), max(lo * lo, hi * hi)
    return _round(low, False, bits), _round(high, True, bits)


@functools.lru_cache(maxsize=4096)
def _cos_sin_enclosure(q: Fraction) -> tuple[Interval, Interval]:
    """Enclosures of ``cos(q)`` and ``sin(q)``, halving ``q`` below ``1/2`` and doubling back.

    The series at ``y = q / 2**h`` is summed in fixed point as the exponential's
    is, and the angle is doubled ``h`` times with ``cos 2y = 2 cos**2 y - 1``
    and ``sin 2y = 2 sin y cos y`` in interval arithmetic. Each doubling can
    widen the enclosures fourfold, so they are summed with ``2 h`` more bits.

    Raises:
        Undecided: For an argument beyond :data:`EXP_LIMIT`.
    """
    if abs(q) > EXP_LIMIT:
        raise Undecided(
            f"the cosine and sine of {describe(q)} are beyond the arguments the tester "
            f"encloses (|x| <= {EXP_LIMIT}), so this draw decides nothing"
        )
    halvings, y = 0, q
    while abs(y) > Fraction(1, 2):
        halvings, y = halvings + 1, y / 2
    bits = PRECISION + _GUARD + 2 * halvings
    one = 1 << bits
    numerator, denominator = y.numerator, y.denominator
    term, cos_sum, sin_sum, n = one, one, 0, 0
    while abs(term) > 1:
        n += 1
        term = term * numerator // (denominator * n)
        if n % 4 == 1:
            sin_sum += term
        elif n % 4 == 2:
            cos_sum -= term
        elif n % 4 == 3:
            sin_sum -= term
        else:
            cos_sum += term
    margin = 2 * n + 8
    cos_b = (Fraction(cos_sum - margin, one), Fraction(cos_sum + margin, one))
    sin_b = (Fraction(sin_sum - margin, one), Fraction(sin_sum + margin, one))
    for _ in range(halvings):
        square = _square_bounds(cos_b, bits)
        both = _product(sin_b, cos_b)
        cos_b = (2 * square[0] - 1, 2 * square[1] - 1)
        sin_b = (_round(2 * both[0], False, bits), _round(2 * both[1], True, bits))
    return (
        Interval(_round(cos_b[0], False), _round(cos_b[1], True)),
        Interval(_round(sin_b[0], False), _round(sin_b[1], True)),
    )


def _complex_exp(real: Any, imag: Any) -> ComplexValue:
    """``exp(real + imag i)``, which is ``exp(real) (cos imag + i sin imag)``.

    At exact parts it is computed once per argument, as the real exponential
    is, so that one exponential of one complex number is one value.
    """
    real, imag = _real(real), _real(imag)
    if isinstance(real, Interval) or isinstance(imag, Interval):
        return _complex_exp_of(real, imag)
    return _complex_exp_exact(real, imag)


@functools.lru_cache(maxsize=4096)
def _complex_exp_exact(real: Fraction, imag: Fraction) -> ComplexValue:
    """``exp(real + imag i)`` at exact parts, one object per argument."""
    return _complex_exp_of(real, imag)


def _complex_exp_of(real: Fraction | Interval, imag: Fraction | Interval) -> ComplexValue:
    """``exp(real) (cos imag + i sin imag)``."""
    magnitude = exp_value(real)
    if _is_zero(imag):
        return ComplexValue(magnitude, Fraction(0))
    cos_value, sin_value = _cos_sin(imag)
    return ComplexValue(magnitude * cos_value, magnitude * sin_value)


# }}}
