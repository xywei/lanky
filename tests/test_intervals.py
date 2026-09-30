"""The exact reading of the reals: rationals, enclosures, and comparisons of them (#33).

The enclosures are checked against :mod:`decimal`, whose ``exp``, ``ln`` and
``sqrt`` are correctly rounded at any precision, so a reference with sixty
digits pins down each enclosure's number far more finely than the enclosure
itself does. The cosine and the sine are checked against digits of ``cos 1``
and ``sin 1`` and against each other.
"""

from __future__ import annotations

import decimal
import math
import random
from fractions import Fraction

import pytest

from lanky import exp, log, sqrt
from lanky.intervals import (
    AGREEMENT,
    EXP_LIMIT,
    ComplexValue,
    Interval,
    agree,
    compare,
    elementary,
    exact,
    exp_value,
    log_value,
    power,
    quotient,
    sqrt_value,
)
from lanky.prelude import Fin, Fn, Nat, Real
from lanky.terms import Forall, Undecided, UndefinedValue, Var, evaluate, exact_reading
from lanky.testing import check

x = Var("x")
n = Var("n")
z = Var("z")
f = Var("f")
i = Var("i")

#: Digits of the reference values, far more than an enclosure resolves.
_DIGITS = 60


def _decimal(q: Fraction) -> decimal.Decimal:
    return decimal.Decimal(q.numerator) / decimal.Decimal(q.denominator)


def _reference(function: str, q: Fraction) -> Fraction:
    """``function(q)`` to sixty digits, from :mod:`decimal`."""
    with decimal.localcontext() as context:
        context.prec = _DIGITS
        value = getattr(_decimal(q), function)()
        return Fraction(value)


def _encloses(value: object, reference: Fraction, relative: Fraction) -> bool:
    """Whether an enclosure meets the reference, give or take the reference's own error."""
    slack = abs(reference) * relative
    lo, hi = (value.lo, value.hi) if isinstance(value, Interval) else (value, value)
    return lo <= reference + slack and hi >= reference - slack


def _width(value: Interval) -> Fraction:
    return value.hi - value.lo


_POINTS = [
    Fraction(1),
    Fraction(-1),
    Fraction(1, 3),
    Fraction(-7, 4),
    Fraction(8),
    Fraction(-8),
    Fraction(1, 1000),
    Fraction(100),
    Fraction(-700),
    Fraction(3, 2**70),
]


@pytest.mark.parametrize("q", _POINTS, ids=str)
def test_exp_encloses_its_value_narrowly(q: Fraction) -> None:
    value = exp_value(q)
    assert isinstance(value, Interval)
    reference = _reference("exp", q)
    assert _encloses(value, reference, Fraction(1, 10**50))
    assert _width(value) <= reference / 2**120


_POSITIVE = sorted({abs(p) for p in _POINTS} | {Fraction(2), Fraction(10), Fraction(9, 4)})


@pytest.mark.parametrize("q", _POSITIVE, ids=str)
def test_log_and_sqrt_enclose_their_values_narrowly(q: Fraction) -> None:
    if q != 1:
        value = log_value(q)
        assert isinstance(value, Interval)
        reference = _reference("ln", q)
        assert _encloses(value, reference, Fraction(1, 10**50))
        assert _width(value) <= max(1, abs(reference)) / 2**118
    root = sqrt_value(q)
    reference = _reference("sqrt", q)
    assert _encloses(root, reference, Fraction(1, 10**50))
    if isinstance(root, Interval):
        assert _width(root) <= reference / 2**120


def test_the_cosine_and_the_sine_of_a_complex_exponential() -> None:
    """``exp(i)`` is ``cos 1 + i sin 1``, whose digits are known."""
    cos_1 = Fraction("0.5403023058681397174009366074429766037323")
    sin_1 = Fraction("0.8414709848078965066525023216302989996226")
    value = elementary("exp", ComplexValue(Fraction(0), Fraction(1)))
    assert _encloses(value.real, cos_1, Fraction(1, 10**38))
    assert _encloses(value.imag, sin_1, Fraction(1, 10**38))
    # large arguments are halved and doubled back, and stay on the unit circle
    for angle in (Fraction(8), Fraction(-100, 3), Fraction(1000)):
        value = elementary("exp", ComplexValue(Fraction(0), angle))
        assert compare("==", abs(value), 1) is None
        assert agree(abs(value), 1)
        assert float(value.real.lo) == pytest.approx(math.cos(angle), abs=1e-12)
        assert float(value.imag.lo) == pytest.approx(math.sin(angle), abs=1e-12)


def test_a_rational_value_is_given_exactly() -> None:
    assert exp_value(Fraction(0)) == 1 and type(exp_value(Fraction(0))) is Fraction
    assert log_value(Fraction(1)) == 0 and type(log_value(Fraction(1))) is Fraction
    assert sqrt_value(Fraction(9, 4)) == Fraction(3, 2)
    assert sqrt_value(Fraction(0)) == 0
    assert isinstance(sqrt_value(Fraction(2)), Interval)
    assert abs(ComplexValue(Fraction(3, 5), Fraction(4, 5))) == 1
    assert elementary("exp", ComplexValue(Fraction(0), Fraction(0))) == 1
    assert elementary("sqrt", 4) == 2


def test_identities_hold_to_within_the_enclosures() -> None:
    """True identities are never excluded, and they agree to far more bits than a float has."""
    rng = random.Random(0)
    for _ in range(50):
        a = Fraction(rng.randrange(-40, 41), rng.randrange(1, 9))
        b = Fraction(rng.randrange(-40, 41), rng.randrange(1, 9))
        p = Fraction(rng.randrange(1, 60), rng.randrange(1, 9))
        for left, right in (
            (exp_value(a + b), exp_value(a) * exp_value(b)),
            (log_value(exp_value(a)), a),
            (exp_value(log_value(p)), p),
            (sqrt_value(p) ** 2, p),
            (log_value(p * p), 2 * log_value(p)),
        ):
            assert compare("==", left, right) in (None, True)
            assert agree(left, right)


def test_a_comparison_has_three_answers() -> None:
    root = sqrt_value(Fraction(2))
    assert compare("<", root, Fraction(3, 2)) is True
    assert compare(">", root, Fraction(7, 5)) is True
    assert compare("==", root, Fraction(7, 5)) is False
    assert compare("!=", root, Fraction(7, 5)) is True
    # an enclosure of the square of the root contains two, and says nothing either way
    square = root * root
    for op in ("==", "!=", "<", "<=", ">", ">="):
        assert compare(op, square, 2) is None
    with pytest.raises(Undecided, match="not settled"):
        bool(square == 2)
    # one enclosure is one number, and equal to itself for certain
    assert compare("==", root, root) is True
    assert compare("<", root, root) is False
    assert exp_value(Fraction(1, 2)) is exp_value(Fraction(2, 4))
    assert compare("==", exp_value(Fraction(1, 2)), exp_value(Fraction(1, 2))) is True


def test_complex_numbers_are_exact_and_have_no_order() -> None:
    a = ComplexValue(Fraction(1, 2), Fraction(-3, 4))
    b = ComplexValue(Fraction(2), Fraction(1, 3))
    assert compare("==", a * b / b, a) is True
    assert compare("==", (a + b) * (a - b), a * a - b * b) is True
    assert compare("==", a, ComplexValue(Fraction(1, 2), Fraction(3, 4))) is False
    assert compare("==", a**-2 * a**2, 1) is True
    with pytest.raises(ZeroDivisionError):
        a / ComplexValue(Fraction(0), Fraction(0))
    with pytest.raises(TypeError, match="no order"):
        compare("<", a, b)
    with pytest.raises(Undecided, match="complex log"):
        elementary("log", a)
    with pytest.raises(Undecided, match="complex sqrt"):
        elementary("sqrt", a)
    assert repr(a) == "ComplexValue(1/2, -3/4)"


def test_what_python_leaves_undefined_raises_as_python_does() -> None:
    for function, value in (("log", 0), ("log", Fraction(-1, 2)), ("sqrt", -1)):
        with pytest.raises(UndefinedValue, match="has no value in Python"):
            elementary(function, value)
    # an enclosure wholly below zero is outside the domain for certain
    with pytest.raises(UndefinedValue, match="has no value in Python"):
        log_value(sqrt_value(Fraction(2)) - 2)
    with pytest.raises(ZeroDivisionError):
        quotient(1, 0)
    with pytest.raises(ZeroDivisionError):
        sqrt_value(Fraction(2)) / 0


def test_an_enclosure_that_reaches_an_edge_decides_nothing() -> None:
    around_zero = sqrt_value(Fraction(2)) * sqrt_value(Fraction(2)) - 2
    assert isinstance(around_zero, Interval) and around_zero.lo < 0 < around_zero.hi
    with pytest.raises(Undecided, match="reaches zero"):
        log_value(around_zero)
    with pytest.raises(Undecided, match="reaches below zero"):
        sqrt_value(around_zero)
    with pytest.raises(Undecided, match="contains zero"):
        Fraction(1) / around_zero
    with pytest.raises(Undecided, match="lies across an integer"):
        sqrt_value(Fraction(2)) ** 2 // 1
    assert sqrt_value(Fraction(2)) // 1 == 1


def test_exp_is_total_below_its_limit_and_undecided_beyond() -> None:
    """``math.exp(-1000)`` underflows to ``0.0``; the enclosure is above zero."""
    assert math.exp(-1000) == 0.0
    assert compare(">", exp_value(Fraction(-1000)), 0) is True
    assert compare(">", exp_value(Fraction(1000)), 10**434) is True
    with pytest.raises(Undecided, match="beyond the arguments"):
        exp_value(Fraction(EXP_LIMIT + 1))


def test_powers_in_the_exact_reading() -> None:
    assert power(2, -1) == Fraction(1, 2)
    assert power(Fraction(2, 3), 3) == Fraction(8, 27)
    assert power(Fraction(9, 4), Fraction(1, 2)) == Fraction(3, 2)
    assert power(Fraction(9, 4), Fraction(-3, 2)) == Fraction(8, 27)
    assert power(0, Fraction(1, 2)) == 0
    cube_root = power(Fraction(2), Fraction(1, 3))
    assert compare("==", cube_root**3, 2) is None and agree(cube_root**3, 2)
    with pytest.raises(ZeroDivisionError):
        power(0, Fraction(-1, 2))
    with pytest.raises(Undecided, match="negative number to a power"):
        power(Fraction(-8), Fraction(1, 3))
    # an even power of an enclosure that straddles zero starts at zero
    root = sqrt_value(Fraction(2))
    square = (root * root - 2) ** 2
    assert isinstance(square, Interval) and square.lo == 0
    assert compare(">=", square, 0) is True
    assert compare("<", (root - 2) ** 3, 0) is True
    assert compare("==", root**-2, Fraction(1, 2)) is None and agree(root**-2, Fraction(1, 2))


def test_an_enclosure_is_no_truth_value_and_no_float() -> None:
    root = sqrt_value(Fraction(2))
    with pytest.raises(TypeError, match="not a truth value"):
        bool(root)
    with pytest.raises(TypeError):
        float(root)
    with pytest.raises(TypeError, match="not a truth value"):
        bool(ComplexValue(Fraction(1), Fraction(0)))


def test_agreement_asks_for_narrow_enclosures() -> None:
    wide = Interval(Fraction(1) - Fraction(1, 2**40), Fraction(1) + Fraction(1, 2**40))
    narrow = Interval(Fraction(1) - Fraction(1, 2**100), Fraction(1) + Fraction(1, 2**100))
    assert AGREEMENT < 100
    assert agree(narrow, 1)
    assert not agree(wide, 1)
    assert not agree(narrow, wide)


def test_the_exact_reading_of_a_term() -> None:
    """A float literal is the rational it holds, and ``n / 2`` is a fraction, as Lean reads both."""
    with exact_reading():
        assert evaluate(x + 0.1, {"x": Fraction(0)}) == Fraction(0.1)
        assert evaluate(x + 0.1, {"x": Fraction(0)}) != Fraction(1, 10)
        assert evaluate(n / 2, {"n": 3}) == Fraction(3, 2)
        assert evaluate(n**-1, {"n": 4}) == Fraction(1, 4)
        assert evaluate(x**0.5, {"x": Fraction(9, 4)}) == Fraction(3, 2)
        literal = evaluate(z * complex(1.5, -2), {"z": ComplexValue(Fraction(1), Fraction(0))})
        assert isinstance(literal, ComplexValue)
        assert (literal.real, literal.imag) == (Fraction(3, 2), Fraction(-2))
        assert exact(0.5) == Fraction(1, 2) and exact(3) == 3
        assert isinstance(evaluate(exp(x), {"x": Fraction(1, 2)}), Interval)
        assert evaluate(log(x) == 0, {"x": 1}) is True
        assert evaluate(sqrt(x) == Fraction(3, 2), {"x": Fraction(9, 4)}) is True
    # outside it evaluation is Python's, as the file computes when it runs
    assert evaluate(x + 0.1, {"x": 0}) == 0.1
    assert evaluate(n / 2, {"n": 3}) == 1.5
    assert isinstance(evaluate(exp(x), {"x": Fraction(1, 2)}), float)


def test_an_equality_of_enclosures_counts_only_where_it_is_asserted() -> None:
    """Agreement is evidence standing ``POSITIVE``, and undecided anywhere else.

    An order that straddles is undecided wherever it stands, since it is the
    enclosures, not the numbers, that fail to settle it.
    """
    y = Var("y")
    at = {"x": Fraction(1, 2), "y": Fraction(1, 3)}
    identity = exp(x + y) == exp(x) * exp(y)
    with exact_reading():
        assert evaluate(identity, at) is True
        assert evaluate(identity & (x > 0), at) is True
        with pytest.raises(Undecided, match="stands where the statement assumes or denies it"):
            evaluate(~identity, at)
        with pytest.raises(Undecided, match="used as a value"):
            evaluate(identity == True, at)  # noqa: E712 - a comparison of truth values
        with pytest.raises(Undecided, match="neither prove it nor refute it"):
            evaluate(exp(x) * exp(-x) <= 1, at)
        # an exclusion is a definite answer wherever it stands
        assert evaluate(~(exp(x + y) == exp(x) + exp(y)), at) is True
        assert evaluate(exp(x) * exp(-x) <= Fraction(1, 2), at) is False


def test_one_operation_on_the_same_numbers_is_one_number() -> None:
    """An enclosure is one number, and so is an operation on the same ones.

    ``2 * exp(x)`` computed twice is one object, and equal to itself for
    certain, where two objects with the same endpoints would decide nothing.
    """
    e, h = exp_value(Fraction(1, 3)), exp_value(Fraction(1, 2))
    assert 2 * e is e * 2
    assert e * h is h * e
    assert e + h is h + e
    assert e - h is e - h and 1 - e is 1 - e and e / h is e / h and 1 / e is 1 / e
    assert -e is -e and e**3 is e**3 and abs(e - 2) is abs(e - 2)
    assert exp_value(e) is exp_value(e) and log_value(e) is log_value(e)
    assert sqrt_value(e) is sqrt_value(e)
    assert compare("==", 2 * e, 2 * e) is True
    # an enclosure less itself is 0, and over itself 1, where it excludes zero
    assert e - e == 0 and type(e - e) is Fraction
    assert e / e == 1 and type(e / e) is Fraction
    # 0, 1 and -1 keep the object: pymbolic sums from 0, multiplies from 1, and
    # reads e - e as e + (-1) * e, which is e plus its own negation
    assert 0 + e is e and e - 0 is e and 1 * e is e and e / 1 is e and e**1 is e
    negated = -e
    assert -1 * e is negated and e / -1 is negated and 0 - e is negated and -negated is e
    assert e + (-e) == 0 and type(-e + e) is Fraction
    around_zero = sqrt_value(Fraction(2)) * sqrt_value(Fraction(2)) - 2
    with pytest.raises(Undecided, match="contains zero"):
        around_zero / around_zero
    # the same endpoints computed apart are two objects, and say nothing
    apart = Interval(e.lo, e.hi)
    assert compare("==", apart, e) is None
    with exact_reading():
        at = {"x": Fraction(1, 3)}
        assert evaluate(exp(x) - exp(x) >= 0, at) is True
        assert evaluate(2 * exp(x) == 2 * exp(x), at) is True


def test_a_table_defined_from_an_enclosure_satisfies_its_definition() -> None:
    """A definition read back as a hypothesis holds for certain at the table it filled.

    The tester fills ``f`` from ``f(i) == 2 * exp(x)`` and then reads the
    definition as a hypothesis, standing where a ``True`` has to be certain.
    Two enclosures of ``2 * exp(x)`` computed apart decide nothing, and every
    draw with ``n > 0`` and ``x != 0`` was undecided; one object for one
    number is equal to itself.
    """
    table = [("x", Real), ("n", Nat), ("f", Fn[Fin[n], Real])]
    for definition, goal in (
        (f(i) == 2 * exp(x), f(i) > 0),
        (f(i) == exp(x) * i, f(i) >= 0),
        (f(i) == sqrt(exp(x) + i), f(i) * f(i) == exp(x) + i),
    ):
        report = check(table, [Forall(((i, Fin[n]),), definition)], Forall(((i, Fin[n]),), goal))
        assert report.ok and report.valid == 200 and report.undecided == 0, definition
    # a recurrence reads the entries it set
    geometric = [("x", Real), ("n", Nat), ("f", Fn[Fin[n + 1], Real])]
    hypotheses = [f(0) == 1, Forall(((i, Fin[n]),), f(i + 1) == f(i) * exp(x))]
    report = check(geometric, hypotheses, Forall(((i, Fin[n + 1]),), f(i) > 0))
    assert report.ok and report.valid == 200 and report.undecided == 0
    # and a false claim about such a table is refuted, at a draw that fills it
    report = check(
        table,
        [Forall(((i, Fin[n]),), f(i) == 2 * exp(x))],
        Forall(((i, Fin[n]),), f(i) > 2 * exp(x)),
    )
    assert not report.ok and len(report.counterexample["f"]) > 0


def test_an_infinity_is_compared_as_python_does_and_computed_with_not_at_all() -> None:
    """``exp(x) < math.inf`` holds, and ``exp(x) + math.inf`` decides nothing.

    An infinity and a NaN are floats and no real numbers. A comparison with
    one is Python's, which is certain for every real number; arithmetic or a
    function of one has no exact reading, and is undecided rather than a
    ``TypeError`` that stops the test.
    """
    e = exp_value(Fraction(1))
    assert compare("<", e, math.inf) is True
    assert compare(">", e, -math.inf) is True
    assert compare("==", e, math.inf) is False
    assert compare("==", e, math.nan) is False
    assert compare("!=", e, math.nan) is True
    assert compare("<", e, math.nan) is False
    for operation in (
        lambda: e + math.inf,
        lambda: math.inf - e,
        lambda: e * math.nan,
        lambda: elementary("exp", math.inf),
        lambda: power(math.inf, Fraction(1, 2)),
    ):
        with pytest.raises(Undecided, match="no real number"):
            operation()
    report = check([("x", Real)], [], exp(x) < math.inf)
    assert report.ok and report.valid == 200
    # a rational plus an infinity is Python's, and exp(0) is the rational 1
    report = check([("x", Real)], [], exp(x) + math.inf > 0)
    assert report.ok and report.undecided > 0
    assert any("no real number" in reason for reason in report.skipped)
