"""pytential's QBX on the surface: sumpy's line-Taylor coefficients of the 2-D Laplace kernel.

Run it as ``gauss.py`` and ``sumpy_recurrence.py`` are run, where sumpy imports.

``python examples/line_taylor.py``
    Builds sumpy's ``LineTaylorLocalExpansion`` of the 2-D Laplace kernel
    through order ``ORDER``, the expansion pytential's direct QBX evaluates a
    layer potential on its own surface with, and prints each coefficient
    beside the closed form, with what sympy simplifies their difference to.

``uv run lanky check examples/line_taylor.py``
    The ledger. ``line_ode``, the differential equation the kernel solves
    along the line, is ``assumed`` on its citation. ``line_taylor``, the
    closed form of the coefficients for every order, is ``proved under
    line_ode`` by Lean where Mathlib is installed (see :mod:`lanky.mathlib`);
    without it, it reads ``assumed``, since the property tester draws no
    family over ``Nat`` (#98). And sumpy's own coefficients through
    ``ORDER`` are ``decided (heuristic)`` against the closed form by the CAS
    oracle (the ``cas`` extra), or ``tested`` by the property tester, which
    evaluates the same equations exactly, without it.

The mathematics. QBX evaluates a layer potential at a target ``t`` on the
surface through an expansion about a center ``c`` off it. For the 2-D Laplace
kernel ``G(x) = log |x|`` (its factor ``-1/(2 pi)`` is left out) and a source
``s``, the kernel at ``t - s`` is ``G(alpha + tau * beta)`` at ``tau = 1``,
with ``alpha = c - s`` and ``beta = t - c``, and sumpy's line-Taylor expansion
expands it in ``tau``, along the line from the center through the target,
rather than in ``x`` and ``y``: its ``k``-th coefficient is the ``k``-th
derivative in ``tau`` at ``0``, and the expansion divides it by ``k!``.
Read ``alpha`` and ``beta`` as complex numbers, and ``|alpha + tau * beta|``
is the modulus of ``alpha + tau * beta`` at every real ``tau``, so the kernel
along the line is the real part of ``log(alpha + tau * beta)``.

Its coefficients in ``tau`` are ``log(alpha)`` and, for ``n >= 1``, ``c(n) ==
-(-beta / alpha) ** n / n``. The function ``f(tau) = log(alpha + tau * beta)``
solves ``(alpha + tau * beta) * f'(tau) == beta`` (``line_ode``). Write ``f``
as the sum of ``c(n) * tau ** n`` and compare the powers of ``tau`` on the two
sides: ``alpha * c(1) == beta`` at ``tau ** 0``, and ``(n + 1) * alpha * c(n +
1) + n * beta * c(n) == 0`` at ``tau ** n`` for ``n >= 1``. ``line_taylor``
takes these two as hypotheses about any table ``c`` of complex numbers, and
concludes the closed form for every ``n``: an induction, two orders at a
time, whose step is a linear combination of the recurrence and the induction
hypothesis that Python finds and Lean checks (see :mod:`lanky.induction`).
Comparing the coefficients of the series is the step taken on the citation,
as differentiating the PDE is in ``sumpy_recurrence.py``, and it is what the
proof rests on ``line_ode`` for.

The third row ties the theorem to sumpy's code. sumpy's ``k``-th
coefficient, divided by ``k!``, is the real part of ``c(k)``, which is ``(c(k)
+ conj(c(k))) / 2``, written out with the conjugates of ``alpha`` and
``beta``. The CAS oracle simplifies the difference of the two sides of each
of the ``ORDER + 1`` equations to zero.

sumpy, and sympy through it, are imported inside the functions that use them;
neither is a dependency of lanky.
"""

from __future__ import annotations

import functools
import math
import os
from typing import Any

from lanky import axiom, log, theorem
from lanky.cas import from_sympy
from lanky.check import module_name
from lanky.ledger import Fact, fact_id
from lanky.oracles.lean import decline
from lanky.plugins import registry
from lanky.prelude import Complex, Fn, Nat, Real
from lanky.terms import Comparison, Forall, LogicalAnd, Var

#: The order through which sumpy's coefficients are checked.
ORDER = 6

#: Where the differential equation is taken from: the principal logarithm's
#: derivative, and the power series of a function analytic at a point, whose
#: coefficients a linear differential equation relates.
AHLFORS = "L. V. Ahlfors, Complex Analysis, 3rd ed., McGraw-Hill, 1979, chs. 2 and 5"


def log_line(alpha: Any, beta: Any, tau: Any, functions: Any) -> Any:
    """The kernel along the line from the center through the target, as a complex logarithm.

    ``functions`` is the module whose ``log`` is meant, sympy's here.
    """
    return functions.log(alpha + tau * beta)


def tau_derivative(kernel: Any, alpha: Any, beta: Any, tau: Any) -> Any:
    """``d/dtau`` of ``kernel(alpha, beta, tau)``, as sympy differentiates it, as a lanky term."""
    import sympy

    a, b = sympy.symbols("alpha beta")
    t = sympy.Symbol("tau", real=True)
    derivative = sympy.diff(kernel(a, b, t, sympy), t)
    return from_sympy(derivative, {"alpha": alpha, "beta": beta, "tau": tau})


@axiom(cite=AHLFORS)
def line_ode(
    alpha: Complex, beta: Complex, tau: Real, off: alpha + tau * beta != 0
) -> (alpha + tau * beta) * tau_derivative(log_line, alpha, beta, tau) == beta:
    """``f(tau) = log(alpha + tau * beta)`` solves ``(alpha + tau * beta) * f'(tau) == beta``.

    Wherever ``alpha + tau * beta`` is not zero, and off the logarithm's
    branch cut, where it is analytic. Its series in ``tau`` about ``0``,
    for ``alpha`` not zero, has coefficients that the equation relates by
    comparing powers of ``tau``: that is what :func:`line_taylor` takes as
    its hypotheses.
    """


@theorem(uses=[line_ode])
def line_taylor(
    alpha: Complex,
    beta: Complex,
    c: Fn[Nat, Complex],
    away: alpha != 0,
    first: alpha * c(1) == beta,
    ode: all((n + 1) * alpha * c(n + 1) + n * beta * c(n) == 0 for n in Nat if n >= 1),
) -> all(c(n) == -((-beta / alpha) ** n) / n for n in Nat if n >= 1):
    """The line-Taylor coefficients of ``log(alpha + tau * beta)``, for every order.

    ``first`` and ``ode`` are ``line_ode`` read on the coefficients, at
    ``tau ** 0`` and at ``tau ** n``.
    """


# {{{ sumpy's coefficients, through ORDER


class LineTaylor:
    """sumpy's claim that its line-Taylor coefficients of the 2-D Laplace kernel are the log series.

    Built by :func:`expands` from a function that returns the expansion. The
    function runs once, where it is decorated, and the coefficients are read
    off what it returns, in sympy, over the parts ``a0``, ``a1`` of ``alpha``
    and ``b0``, ``b1`` of ``beta``.

    Attributes:
        order: The order through which the coefficients are checked.
        coefficients: sumpy's coefficient of each order, a sympy expression.
    """

    noun = "line-taylor"

    def __init__(self, fn: Any, *, order: int) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        self.order = order
        code = fn.__code__
        self.path, self.line = code.co_filename, code.co_firstlineno
        self.where = f"{os.path.basename(self.path)}:{self.line}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        self.module = module_name(self.path) or fn.__module__
        try:
            expansion = fn()
        except ImportError as exc:
            raise ImportError(
                f"{self.qualname} at {self.where} checks sumpy's own expansion, and sumpy "
                f"is not importable here ({exc}); pip install sumpy"
            ) from exc
        self.coefficients = _read_coefficients(expansion)[: order + 1]

    def statement(self) -> str:
        """``coefficient(k) / k! == re(c(k))`` through the order, in words a reader knows."""
        return (
            f"a0, a1, b0, b1 : Real | a0**2 + a1**2 > 0 |- with alpha = a0 + a1*1j and "
            f"beta = b0 + b1*1j, sumpy's coefficient(0) == log(abs(alpha)) and "
            f"coefficient(k) / k! == re(-(-beta / alpha)**k / k) for 1 <= k <= {self.order}"
        )

    def term(self) -> Forall:
        """The claim as one statement over the parts of ``alpha`` and ``beta``, an equation each."""
        a0, a1, b0, b1 = (Var(name) for name in ("a0", "a1", "b0", "b1"))
        names = {"a0": a0, "a1": a1, "b0": b0, "b1": b1}
        alpha, beta = a0 + a1 * 1j, b0 + b1 * 1j
        # the conjugates, written out, so that a real part is (z + conj(z)) / 2
        alpha_bar, beta_bar = a0 - a1 * 1j, b0 - b1 * 1j
        equations = [Comparison(from_sympy(self.coefficients[0], names), "==", log(abs(alpha)))]
        for k in range(1, len(self.coefficients)):
            sumpy = from_sympy(self.coefficients[k] / math.factorial(k), names)
            series = -((-beta / alpha) ** k + (-beta_bar / alpha_bar) ** k) / (2 * k)
            equations.append(Comparison(sumpy, "==", series))
        return Forall(
            ((a0, Real), (a1, Real), (b0, Real), (b1, Real)),
            LogicalAnd(tuple(equations)),
            a0**2 + a1**2 > 0,
        )

    def fact_id(self) -> str:
        """The id of the claim's one fact."""
        return fact_id(self.noun, self.qualname, module=self.module, line=self.line)

    def facts(self) -> tuple[Fact, ...]:
        """The claim through the order, for the CAS oracle."""
        return (
            Fact(
                id=self.fact_id(),
                kind=self.noun,
                statement=self.statement(),
                term=self.term(),
                provenance={"path": self.path, "line": self.line},
                where=self.where,
                owner=self.qualname,
            ),
        )

    def __call__(self) -> Any:
        """The expansion, built again."""
        return self.fn()

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<{self.noun} {self.__name__}: {self.statement()}>"


def _read_coefficients(expansion: Any) -> list[Any]:
    """sumpy's coefficient of each order, as sympy expressions in ``a0``, ``a1``, ``b0``, ``b1``.

    The expansion is handed sumpy's own symbolic vectors for ``alpha``, the
    center less the source, and ``beta``, the target less the center, as
    pytential hands it the geometry, and ``rscale`` ``1``, which the
    line-Taylor expansion ignores.
    """
    import sympy
    from sumpy.symbolic import make_sym_vector

    avec, bvec = make_sym_vector("a", 2), make_sym_vector("b", 2)
    rows = expansion.coefficients_from_source(expansion.kernel, avec, bvec, rscale=1)
    return [sympy.sympify(row) for row in rows]


class LineTaylorTheory:
    """The facts a :class:`LineTaylor` claims; what a plugin's theory would be."""

    name = "line-taylor"

    def facts(self, obj: Any, /) -> tuple:
        """The claim's facts, or nothing for an object it does not own."""
        return obj.facts() if isinstance(obj, LineTaylor) else ()


# Each import of this file defines the class anew, and a check imports the file
# under a name of its own, so the theory of the latest import replaces that of
# an earlier one, which would not recognize this import's claims.
registry.register_theory(LineTaylorTheory(), replace=True)

#: Why Lean is not asked about the claim through ``ORDER``.
FOR_THE_CAS = (
    "the claim through the order checked is the CAS oracle's, one equation per "
    "coefficient; Lean's is the claim for every order, line_taylor"
)


def expands(*, order: int) -> Any:
    """Claim that the expansion the decorated function returns has the log series as coefficients.

    The function takes no arguments and returns sumpy's line-Taylor
    expansion of the 2-D Laplace kernel. It runs once, where it is
    decorated, and the claim is read off what it returns, through ``order``.
    """

    def decorate(fn: Any) -> LineTaylor:
        claim = LineTaylor(fn, order=order)
        try:
            decline(claim.fact_id(), FOR_THE_CAS)
        except LookupError:  # no Lean oracle registered, so none to keep away
            pass
        return registry.register_object(claim)

    return decorate


@expands(order=ORDER)
def qbx_expansion():
    """sumpy's line-Taylor expansion of the 2-D Laplace kernel, as pytential's QBX takes it."""
    from sumpy.expansion.local import LineTaylorLocalExpansion
    from sumpy.kernel import LaplaceKernel

    return LineTaylorLocalExpansion(LaplaceKernel(2), ORDER)


# }}}


# {{{ running it


def main() -> int:
    """Print each coefficient beside the closed form; exit 1 unless every one agrees."""
    import sympy

    a0, a1, b0, b1 = sympy.symbols("a0 a1 b0 b1", real=True)
    swap = dict(zip(sympy.symbols("a0 a1 b0 b1"), (a0, a1, b0, b1), strict=True))
    alpha, beta = a0 + sympy.I * a1, b0 + sympy.I * b1
    point = {a0: sympy.Rational(3, 2), a1: sympy.Rational(-1, 2), b0: sympy.Rational(1, 4), b1: 1}
    rows = [("k", "closed form", "sympy: sumpy's / k! - closed form", "sumpy's / k! at a point")]
    agree = True
    for k, coefficient in enumerate(qbx_expansion.coefficients):
        coefficient = coefficient.xreplace(swap) / math.factorial(k)
        if k == 0:
            closed, shown = sympy.log(sympy.Abs(alpha)), "log|alpha|"
        else:
            closed = sympy.re(sympy.expand_complex(-((-beta / alpha) ** k) / k))
            shown = f"re(-(-beta/alpha)**{k} / {k})"
        difference = sympy.simplify(coefficient - closed)
        agree = agree and difference == 0
        value = float(coefficient.xreplace(point))
        rows.append((str(k), shown, str(difference), f"{value:.6g}"))
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    for index, row in enumerate(rows):
        cells = zip(row, widths, strict=True)
        print("  ".join(cell.ljust(width) for cell, width in cells).rstrip())
        if index == 0:
            print("  ".join("-" * width for width in widths))
    print()
    print(
        "With alpha = a0 + a1*1j the center less the source and beta = b0 + b1*1j the target\n"
        "less the center, sumpy's line-Taylor coefficients of log|x| are the real parts of\n"
        f"the series of log(alpha + tau*beta) through order {qbx_expansion.order}; the point is\n"
        "alpha = 3/2 - 1/2*1j, beta = 1/4 + 1j."
        if agree
        else "Some coefficient is NOT the closed form: see the table."
    )
    print()
    print(
        "`lanky check examples/line_taylor.py` puts it in the ledger: decided through the\n"
        "order by the CAS oracle, and the closed form proved for every order by Lean where\n"
        "Mathlib is installed, under the differential equation the kernel solves."
    )
    return 0 if agree else 1


if __name__ == "__main__":
    raise SystemExit(main())

# }}}
