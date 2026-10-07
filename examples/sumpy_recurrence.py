"""sumpy's compressed Taylor coefficients of the 2-D Laplace kernel, checked two ways.

Run it as ``gauss.py`` and ``pytential_skie.py`` are run, where sumpy imports.

``python examples/sumpy_recurrence.py``
    Builds sumpy's compressed Taylor wrangler for the 2-D Laplace kernel,
    reconstructs every derivative through order ``ORDER`` from the ones it
    stores, and prints each beside the direct derivative of ``log r``, with
    what sympy simplifies their difference to and how far apart mpmath finds
    them.

``uv run lanky check examples/sumpy_recurrence.py``
    The ledger: one claim, that every coefficient the wrangler reconstructs
    is the kernel's derivative, at three statuses. ``tested`` by mpmath, which
    takes the derivatives numerically at random points; ``decided
    (heuristic)`` by the CAS oracle, which simplifies the difference of the
    two sides of each equation to zero with sympy (the ``cas`` extra); and,
    for every order and not only through ``ORDER``, ``proved under harmonic``
    by Lean, where Mathlib is installed (see :mod:`lanky.mathlib`). Without
    the CAS oracle the second row reads ``tested`` by the property tester,
    which evaluates the same equations exactly, in rational arithmetic, and
    without Mathlib the third reads ``assumed``. Above them is the kernel's
    harmonicity, ``assumed`` on its citation.

The mathematics. A Taylor expansion of a kernel ``G`` needs every derivative
``d^(a+b) G / dx^a dy^b`` with ``a + b`` up to the order. When ``G`` satisfies a
PDE, most of them are determined by the others: the 2-D Laplace kernel is
harmonic, ``G_xx = -G_yy``, so a derivative with ``a >= 2`` is minus the one
with two fewer ``x``'s and two more ``y``'s. sumpy's
``LinearPDEBasedExpansionTermsWrangler`` stores the derivatives with ``a <= 1``,
``2p + 1`` of the ``(p + 1)(p + 2)/2`` through order ``p``, and reconstructs the
rest by that recurrence. The claim is that the reconstruction is right: for
every ``a + b <= p``, the wrangler's combination of the stored derivatives
equals the derivative it stands for. The constant factor ``-1/(2 pi)`` of the
kernel is left out, since the reconstruction is linear.

The harmonicity is an axiom here, ``harmonic``, taken on its citation and
sampled for a counterexample. The first two rows do not rest on it: each
checks the reconstruction against the derivatives themselves, one order at a
time. The third does. For every order, the claim is an induction on ``a``:
the coefficient ``(a + 2, b)`` is minus the one at ``(a, b + 2)``, which by
the induction hypothesis is the derivative ``D(a, b + 2)``, and the PDE,
differentiated ``a`` times in ``x`` and ``b`` in ``y``, says that ``D(a + 2, b)
+ D(a, b + 2) == 0``. That step is algebra, which Lean checks with
``linear_combination`` once Python has found which hypotheses to combine, at
which points, with which multipliers (see :mod:`lanky.induction`). What is not
algebra is that the derivatives of the kernel satisfy the PDE at every order:
that is the harmonicity, differentiated, which the kernel's smoothness away
from the origin allows, and it is the hypothesis the proof takes and the axiom
the row rests on. So the third row's term is a statement about any table
``D`` of numbers indexed by ``(a, b)`` that satisfies the PDE at every order,
and any table ``R`` that agrees with it where the wrangler stores and follows
the recurrence elsewhere: ``R`` is ``D``. The derivatives of ``log r`` at a
point are such a ``D``, by ``harmonic``, and the wrangler's reconstruction is
such an ``R``, by the recurrence, which is read off the PDE sumpy declares for
the kernel, as the wrangler reads it, and checked against the wrangler's
weights through ``ORDER``; a wrangler whose weights do not follow it makes no
claim for every order.

The CAS's row is the claim through ``ORDER``, 28 equations, and Lean is not
asked about it (:func:`lanky.oracles.lean.decline`): Lean's row is the one for
every order, and the ladder would spend minutes on a conjunction it has no
strategy for before the CAS oracle decides it in a second.

The recurrence is read off the wrangler, not written here: it is handed
symbols for the stored derivatives and returns, for each coefficient, the
combination of them it computes, whose rational weights are what the claim is
about. The derivatives are sympy's (``diff``) for the symbolic row, and
mpmath's (``mpmath.diff``, by finite differences at high precision) for the
sampled one, so the two rows rest on no common computation but the weights.

sumpy, and sympy and mpmath through it, are imported inside the functions that
use them. None of them is a dependency of lanky: the oracle that asks sympy is
lanky's, behind the ``cas`` extra, and the one that asks mpmath is here, where
a plugin's would be. So is the search for the induction's multipliers, which
is sympy's, and so lanky's ``cas`` extra too.
"""

from __future__ import annotations

import functools
import os
import random
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

from lanky import axiom
from lanky.cas import from_sympy
from lanky.check import module_name
from lanky.ledger import Fact, Status, fact_id
from lanky.oracles.lean import decline
from lanky.plugins import registry
from lanky.prelude import Fn, Nat, Real
from lanky.terms import Add, Comparison, Forall, LogicalAnd, LogicalOr, Product, Var
from lanky.theory import fact_ids

#: The order through which every coefficient is checked.
ORDER = 6

#: How many points mpmath takes the derivatives at, and to how many digits.
POINTS, DIGITS = 20, 30

#: Where the kernel's harmonicity is taken from: the fundamental solution of
#: Laplace's equation, of which ``log r`` is a multiple, is harmonic away from
#: its source.
KRESS = "R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6"


def log_r(x: Any, y: Any, functions: Any) -> Any:
    """The 2-D Laplace kernel without its constant factor: ``log r``.

    ``functions`` is the module whose ``log`` and ``sqrt`` are meant, sympy's
    for the derivatives as formulas and mpmath's for them as numbers.
    """
    return functions.log(functions.sqrt(x**2 + y**2))


def laplacian(kernel: Any, x: Var, y: Var) -> Any:
    """``G_xx + G_yy`` of ``kernel``, as sympy differentiates it, over lanky's ``x`` and ``y``."""
    import sympy

    sx, sy = sympy.symbols("x y", real=True)
    kernel_term = kernel(sx, sy, sympy)
    return from_sympy(kernel_term.diff(sx, 2) + kernel_term.diff(sy, 2), {"x": x, "y": y})


@axiom(cite=KRESS)
def harmonic(x: Real, y: Real, away: x**2 + y**2 > 0) -> laplacian(log_r, x, y) == 0:
    """The 2-D Laplace kernel is harmonic away from the origin: ``G_xx + G_yy == 0``.

    The PDE the wrangler reconstructs by, and what the proof of the claim for
    every order rests on: the kernel is smooth away from the origin, so its
    derivatives commute with the Laplacian, and every one of them is harmonic
    too, which is the hypothesis that proof takes.
    """


# {{{ the claim


@dataclass(frozen=True, eq=False)
class Sampled:
    """The claim at points, as the term the ``mpmath`` oracle evaluates."""

    claim: Reconstruction

    def __str__(self) -> str:
        """The statement the sampled fact makes."""
        return self.claim.statement(f"at {self.claim.points} points: ")


class Reconstruction:
    """A wrangler's claim that every coefficient it reconstructs is the kernel's derivative.

    Built by :func:`reconstructs` from a function that returns the wrangler.
    The function runs once, where it is decorated, and the claim is read off
    what it returns.

    Attributes:
        kernel: The kernel, as :func:`log_r` is written.
        order: The order through which the coefficients are checked.
        identifiers: The multi-index ``(a, b)`` of every coefficient, in the
            wrangler's order.
        stored: The multi-indices of the coefficients the wrangler stores.
        weights: For each coefficient, the rational weight of each stored one
            in the combination the wrangler reconstructs it by, by the stored
            one's place in ``stored``.
        pde: The PDE sumpy declares for the kernel, as the rational
            coefficient of each derivative in it, ``{(2, 0): 1, (0, 2): 1}``
            for Laplace's; ``None`` when there is no claim for every order
            (see :func:`_read_pde`).
        leading: The derivative of the PDE the wrangler solves it for, the
            first one it does not store: ``(2, 0)``.
        uses: The facts the claim for every order rests on, ``harmonic``'s.
    """

    noun = "reconstruction"

    def __init__(
        self,
        fn: Any,
        *,
        kernel: Any,
        order: int,
        points: int,
        digits: int,
        seed: int = 0,
        uses: Any = (),
    ) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        self.kernel, self.order = kernel, order
        self.points, self.digits, self.seed = points, digits, seed
        self.uses = fact_ids(uses)
        code = fn.__code__
        self.path, self.line = code.co_filename, code.co_firstlineno
        self.where = f"{os.path.basename(self.path)}:{self.line}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        self.module = module_name(self.path) or fn.__module__
        try:
            wrangler = fn()
        except ImportError as exc:
            raise ImportError(
                f"{self.qualname} at {self.where} checks sumpy's own wrangler, and sumpy "
                f"is not importable here ({exc}); pip install sumpy"
            ) from exc
        self.identifiers, self.stored, self.weights = _read_recurrence(wrangler)
        self.derivatives = _derivatives(kernel, self.identifiers)
        found = _read_pde(wrangler, self.identifiers, self.stored, self.weights)
        self.pde, self.leading = found if found is not None else (None, None)

    def statement(self, prefix: str = "", scope: str | None = None) -> str:
        """``reconstructed(a, b) == diff(G, x, a, y, b) for a + b <= p``, after ``prefix``."""
        return (
            f"{prefix}reconstructed(a, b) == diff({self.kernel_text}, x, a, y, b) "
            f"{scope or f'for a + b <= {self.order}'}"
        )

    def recurrence_text(self) -> str:
        """The recurrence, ``reconstructed(a + 2, b) == -reconstructed(a, b + 2)`` for Laplace."""
        assert self.pde is not None and self.leading is not None
        left = _shifted("reconstructed", self.leading)
        parts = []
        for mi, coefficient in self.pde.items():
            if mi == self.leading:
                continue
            weight = -coefficient / self.pde[self.leading]
            size = "" if abs(weight) == 1 else f"{abs(weight)}*"
            parts.append(f"{'-' if weight < 0 else '+'} {size}{_shifted('reconstructed', mi)}")
        right = " ".join(parts)
        right = right[2:] if right.startswith("+ ") else "-" + right[2:]
        return f"{left} == {right}"

    def pde_text(self) -> str:
        """The PDE as the derivatives of ``G`` it combines: ``G_xx + G_yy == 0`` for Laplace."""
        assert self.pde is not None
        parts = []
        for mi, coefficient in self.pde.items():
            size = "" if abs(coefficient) == 1 else f"{abs(coefficient)}*"
            parts.append(f"{'-' if coefficient < 0 else '+'} {size}{_derivative_name(mi)}")
        text = " ".join(parts)
        text = text[2:] if text.startswith("+ ") else "-" + text[2:]
        return f"{text} == 0"

    @property
    def kernel_text(self) -> str:
        """The kernel, as sympy prints it."""
        import sympy

        x, y = sympy.symbols("x y", real=True)
        return str(self.kernel(x, y, sympy))

    def combination(self, index: int, values: Any, number: Any = None) -> Any:
        """Coefficient ``index`` as the wrangler reconstructs it from ``values`` of the stored.

        ``number`` turns a weight into the kind of number ``values`` are, when
        they do not take a ``Fraction`` as it is.
        """
        return sum(
            (
                (weight if number is None else number(weight)) * values[place]
                for place, weight in self.weights[index].items()
            ),
            start=0,
        )

    # {{{ facts

    def fact_id(self, detail: str) -> str:
        """The id of one of the claim's facts: ``sampled``, ``symbolic`` or ``every-order``."""
        return fact_id(self.noun, self.qualname, module=self.module, line=self.line, detail=detail)

    def _fact(self, detail: str, statement: str, term: Any, rests_on: tuple = ()) -> Fact:
        return Fact(
            id=self.fact_id(detail),
            kind=self.noun,
            statement=statement,
            term=term,
            provenance={"path": self.path, "line": self.line},
            where=self.where,
            owner=self.qualname,
            rests_on=rests_on,
        )

    def term(self) -> Forall:
        """The claim as one statement over ``x`` and ``y``, an equation per coefficient."""
        x, y = Var("x"), Var("y")
        names = {"x": x, "y": y}
        direct = [from_sympy(derivative, names) for derivative in self.derivatives]
        stored = [direct[self.identifiers.index(mi)] for mi in self.stored]
        equations = []
        for index in range(len(self.identifiers)):
            parts = [
                derivative if weight == 1 else Product((weight, derivative))
                for place, weight in self.weights[index].items()
                for derivative in (stored[place],)
            ]
            reconstructed = parts[0] if len(parts) == 1 else Add(tuple(parts))
            equations.append(Comparison(reconstructed, "==", direct[index]))
        return Forall(((x, Real), (y, Real)), LogicalAnd(tuple(equations)), x**2 + y**2 > 0)

    def every_order_term(self) -> Forall:
        """The claim for every order: a table that follows the recurrence is the derivatives'.

        Over two tables of reals indexed by ``(a, b)``, the derivatives ``D``
        and the reconstruction ``R``: if ``D`` satisfies the PDE at every
        order, ``R`` agrees with ``D`` where the wrangler stores, and ``R``
        follows the recurrence everywhere else, then ``R`` is ``D``. For
        Laplace's PDE, with ``R(a + 2)(b) == -R(a)(b + 2)``.
        """
        assert self.pde is not None and self.leading is not None
        a, b = Var("a"), Var("b")
        derivatives, reconstructed = Var("D"), Var("R")
        table = Fn[Nat, Fn[Nat, Real]]
        orders = ((a, Nat), (b, Nat))

        def at(family: Var, shift: tuple[int, int]) -> Any:
            return family(a + shift[0] if shift[0] else a)(b + shift[1] if shift[1] else b)

        def weighted(weight: Fraction, term: Any) -> Any:
            return term if weight == 1 else Product((_number(weight), term))

        def total(parts: list[Any]) -> Any:
            return parts[0] if len(parts) == 1 else Add(tuple(parts))

        pde = Forall(
            orders,
            Comparison(
                total([weighted(c, at(derivatives, mi)) for mi, c in self.pde.items()]), "==", 0
            ),
        )
        below = [
            Comparison(v, "<", bound)
            for v, bound in zip((a, b), self.leading, strict=True)
            if bound
        ]
        stored = Forall(
            orders,
            Comparison(at(reconstructed, (0, 0)), "==", at(derivatives, (0, 0))),
            below[0] if len(below) == 1 else LogicalOr(tuple(below)),
        )
        lead = self.pde[self.leading]
        recurrence = Forall(
            orders,
            Comparison(
                at(reconstructed, self.leading),
                "==",
                total(
                    [
                        weighted(-c / lead, at(reconstructed, mi))
                        for mi, c in self.pde.items()
                        if mi != self.leading
                    ]
                ),
            ),
        )
        goal = Forall(orders, Comparison(at(reconstructed, (0, 0)), "==", at(derivatives, (0, 0))))
        return Forall(
            ((derivatives, table), (reconstructed, table)),
            goal,
            LogicalAnd((pde, stored, recurrence)),
        )

    def facts(self) -> tuple[Fact, ...]:
        """The claim at points, for mpmath; as formulas, for the CAS; for every order, for Lean.

        The last only where the wrangler's weights follow the recurrence the
        PDE gives (see :func:`_read_pde`).
        """
        facts = [
            self._fact("sampled", str(Sampled(self)), Sampled(self)),
            self._fact(
                "symbolic",
                self.statement("x : Real, y : Real | x**2 + y**2 > 0 |- "),
                self.term(),
            ),
        ]
        if self.pde is not None:
            facts.append(
                self._fact(
                    "every-order",
                    self.statement("every order: ", f"for every a, b, by {self.recurrence_text()}"),
                    self.every_order_term(),
                    rests_on=self.uses,
                )
            )
        return tuple(facts)

    # }}}

    # {{{ the two checks, as the file run as a program prints them

    def simplified(self) -> list[Any]:
        """What sympy simplifies the difference of the two sides of each equation to."""
        import sympy

        stored = [self.derivatives[self.identifiers.index(mi)] for mi in self.stored]
        return [
            sympy.simplify(self.combination(index, stored) - self.derivatives[index])
            for index in range(len(self.identifiers))
        ]

    def draws(self) -> list[tuple[Fraction, Fraction]]:
        """The points mpmath takes the derivatives at: rational, and away from the origin."""
        rng = random.Random(self.seed)
        found: list[tuple[Fraction, Fraction]] = []
        while len(found) < self.points:
            x, y = (Fraction(rng.randrange(-200, 201), 100) for _ in range(2))
            if x * x + y * y >= Fraction(1, 4):
                found.append((x, y))
        return found

    @property
    def tolerance(self) -> Fraction:
        """How far apart, relative to the derivative, mpmath may find the two sides."""
        return Fraction(1, 10 ** (self.digits - 10))

    def sampled(self) -> tuple[list[Any], dict[str, Any] | None]:
        """The largest relative difference mpmath finds for each coefficient, and a counterexample.

        The counterexample is the first point and coefficient at which the two
        sides differ by more than ``10**-(digits - 10)`` relative to the
        derivative, or ``None`` when there is none.
        """
        import mpmath

        largest = [mpmath.mpf(0)] * len(self.identifiers)
        found = None
        with mpmath.workdps(self.digits):
            tolerance = _mpf(self.tolerance)
            for x, y in self.draws():
                point = (_mpf(x), _mpf(y))
                values = [
                    mpmath.diff(lambda u, v: self.kernel(u, v, mpmath), point, mi)
                    for mi in self.identifiers
                ]
                stored = [values[self.identifiers.index(mi)] for mi in self.stored]
                for index, mi in enumerate(self.identifiers):
                    reconstructed = self.combination(index, stored, _mpf)
                    gap = abs(reconstructed - values[index]) / max(1, abs(values[index]))
                    largest[index] = max(largest[index], gap)
                    if found is None and gap > tolerance:
                        found = {
                            "x": x,
                            "y": y,
                            "a": mi[0],
                            "b": mi[1],
                            "reconstructed": mpmath.nstr(reconstructed, 12),
                            "derivative": mpmath.nstr(values[index], 12),
                            "difference": mpmath.nstr(gap, 3),
                        }
        return largest, found

    # }}}

    def __call__(self) -> Any:
        """The wrangler, built again."""
        return self.fn()

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<{self.noun} {self.__name__}: {self.statement()}>"


def _mpf(value: int | Fraction) -> Any:
    """A weight as an mpmath number, exactly as far as the working precision goes."""
    import mpmath

    value = Fraction(value)
    return mpmath.mpf(value.numerator) / value.denominator


def _read_recurrence(wrangler: Any) -> tuple[list[tuple[int, int]], list[tuple[int, int]], list]:
    """The coefficients, the stored ones, and the weights the wrangler reconstructs each by.

    The wrangler is handed a symbol for each stored derivative, and returns
    each coefficient as a combination of them, in sympy or SymEngine,
    whichever sumpy uses. That combination has to be linear, with rational
    weights and nothing else in it, which is checked rather than assumed.
    """
    import sumpy.symbolic as backend
    import sympy

    identifiers = [tuple(mi) for mi in wrangler.get_full_coefficient_identifiers()]
    stored = [tuple(mi) for mi in wrangler.get_coefficient_identifiers()]
    names = [f"stored_{place}" for place in range(len(stored))]
    rows = wrangler.get_full_kernel_derivatives_from_stored(
        [backend.Symbol(name) for name in names], 1
    )
    symbols = [sympy.Symbol(name) for name in names]
    weights = []
    for mi, row in zip(identifiers, rows, strict=True):
        polynomial = sympy.Poly(sympy.sympify(row), *symbols)
        if polynomial.total_degree() > 1 or polynomial.coeff_monomial(1) != 0:
            raise ValueError(f"the wrangler reconstructs {mi} by {row}, which is not linear")
        weight = {}
        for place, symbol in enumerate(symbols):
            coefficient = polynomial.coeff_monomial(symbol)
            if coefficient == 0:
                continue
            if not isinstance(coefficient, sympy.Rational):
                raise ValueError(f"the wrangler weighs {symbol} by {coefficient} in {mi}")
            weight[place] = (
                int(coefficient)
                if coefficient.q == 1
                else Fraction(int(coefficient.p), int(coefficient.q))
            )
        weights.append(weight)
    return identifiers, stored, weights


def _read_pde(
    wrangler: Any, identifiers: list[tuple[int, int]], stored: list[tuple[int, int]], weights: list
) -> tuple[dict[tuple[int, int], Fraction], tuple[int, int]] | None:
    """The PDE the wrangler reconstructs by, and the derivative it is solved for; or ``None``.

    The PDE is the one sumpy declares for the wrangler's kernel
    (``get_pde_as_diff_op``), a rational coefficient for each derivative in
    it. The wrangler stores every derivative that is not a derivative of one
    of them, the leading one, and reconstructs the others from it: a
    derivative ``m`` beyond ``L`` is minus the PDE's other terms, shifted by
    ``m - L`` and divided by ``L``'s coefficient. The leading derivative is
    the one whose shifts are exactly what the wrangler does not store.

    That is the recurrence the claim for every order is about, so the
    wrangler's weights through its order are checked against it, exactly:
    a stored coefficient is itself, and every other is the recurrence's
    combination of the weights it names. ``None``, and no claim for every
    order, for a wrangler with no kernel to read a PDE off, a PDE with a
    coefficient that is not a rational number (Helmholtz's ``k``), a stored
    set no derivative of the PDE gives, a recurrence that reaches past the
    order for some coefficient, where the wrangler cannot follow it, or
    weights that do not follow the recurrence: the rows at points and as
    formulas still check such a wrangler, and refute one that is wrong.
    """
    import sympy

    kernel = getattr(wrangler, "knl", None)
    get_pde = getattr(kernel, "get_pde_as_diff_op", None)
    if get_pde is None:
        return None
    try:
        operator = get_pde()
    except NotImplementedError:
        return None
    if len(operator.eqs) != 1:
        return None
    pde: dict[tuple[int, int], Fraction] = {}
    for derivative, coefficient in operator.eqs[0].items():
        value = sympy.sympify(coefficient)
        if getattr(derivative, "vec_idx", 0) != 0 or not value.is_Rational:
            return None
        pde[tuple(derivative.mi)] = Fraction(int(value.p), int(value.q))
    # in a fixed order, x's before y's, whatever order sumpy keeps them in
    pde = dict(sorted(pde.items(), reverse=True))
    kept = set(stored)
    for leading in pde:
        shifts = {mi for mi in identifiers if all(m >= n for m, n in zip(mi, leading, strict=True))}
        if set(identifiers) - shifts == kept:
            break
    else:
        return None
    place = {mi: index for index, mi in enumerate(identifiers)}
    for index, mi in enumerate(identifiers):
        if mi in kept:
            expected = {stored.index(mi): Fraction(1)}
        else:
            expected = {}
            for other, coefficient in pde.items():
                if other == leading:
                    continue
                source = tuple(m - n + o for m, n, o in zip(mi, leading, other, strict=True))
                if source not in place:
                    # the recurrence reaches past the order, where the wrangler
                    # has nothing, so it cannot follow it here
                    return None
                for stored_place, weight in weights[place[source]].items():
                    share = -coefficient / pde[leading] * weight
                    expected[stored_place] = expected.get(stored_place, 0) + share
        actual = {key: Fraction(value) for key, value in weights[index].items() if value != 0}
        if {key: value for key, value in expected.items() if value != 0} != actual:
            return None
    return pde, leading


def _derivative_name(mi: tuple[int, int]) -> str:
    """``G_xx`` for ``(2, 0)``, and ``G`` for ``(0, 0)``."""
    return "G" + ("_" + "x" * mi[0] + "y" * mi[1] if any(mi) else "")


def _shifted(name: str, mi: tuple[int, int]) -> str:
    """``name(a + 2, b)`` for the shift ``(2, 0)``."""
    shifted = [f"{v} + {m}" if m else v for v, m in zip("ab", mi, strict=True)]
    return f"{name}({', '.join(shifted)})"


def _number(value: Fraction) -> int | Fraction:
    """A weight as the plain number it is: an integer where it is one."""
    return int(value) if value.denominator == 1 else value


def _derivatives(kernel: Any, identifiers: list[tuple[int, int]]) -> list[Any]:
    """sympy's derivative of the kernel for each multi-index, over real ``x`` and ``y``."""
    import sympy

    x, y = sympy.symbols("x y", real=True)
    out = []
    for a, b in identifiers:
        derivative = kernel(x, y, sympy)
        if a:
            derivative = derivative.diff(x, a)
        if b:
            derivative = derivative.diff(y, b)
        out.append(derivative)
    return out


class ReconstructionTheory:
    """The facts a :class:`Reconstruction` claims; what a plugin's theory would be."""

    name = "reconstruction"

    def facts(self, obj: Any, /) -> tuple:
        """The claim's facts, or nothing for an object it does not own."""
        return obj.facts() if isinstance(obj, Reconstruction) else ()


class Mpmath:
    """The oracle that evaluates a sampled claim: its trust class is ``test``."""

    name = "mpmath"

    def trust_class(self) -> str:
        """Evidence from evaluation at points."""
        return "test"

    def can_establish(self, fact: Fact, /) -> bool:
        """Willing to try a reconstruction's claim at points."""
        return isinstance(fact.term, Sampled)

    def establish(self, fact: Fact, /) -> Fact:
        """``TESTED`` when every coefficient agrees at every point; ``REFUTED`` with the point."""
        claim = fact.term.claim
        largest, found = claim.sampled()
        common = {"samples": claim.points, "digits": claim.digits}
        if found is not None:
            return fact.with_status(
                Status.REFUTED,
                self.name,
                counterexample=found,
                reason=(
                    f"the reconstructed coefficient ({found['a']}, {found['b']}) is "
                    f"{found['reconstructed']} and the derivative {found['derivative']}, "
                    f"{found['difference']} apart relative to it"
                ),
                **common,
            )
        return fact.with_status(
            Status.TESTED,
            self.name,
            valid=claim.points,
            largest_difference=float(max(largest)),
            **common,
        )


# Each import of this file defines its classes anew, and a check imports the
# file it checks under a name of its own, so the theory and the oracle of the
# latest import replace those of an earlier one, which would not recognize
# this import's claims.
registry.register_theory(ReconstructionTheory(), replace=True)
registry.register_oracle(Mpmath(), replace=True)


#: Why Lean is not asked about the claim through ``ORDER`` (see the module docstring).
FOR_THE_CAS = (
    "the claim through the order checked is the CAS oracle's, one equation per "
    "coefficient; Lean's is the claim for every order"
)


def reconstructs(
    kernel: Any, *, order: int, uses: Any = (), points: int = POINTS, digits: int = DIGITS
) -> Any:
    """Claim that the wrangler the decorated function returns reconstructs ``kernel``'s derivatives.

    The function takes no arguments and returns the wrangler. It runs once,
    where it is decorated, and the claim is read off what it returns: the
    coefficients through ``order``, the ones the wrangler stores, and the
    combination of those it reconstructs each of the others by. ``uses``
    names what the claim for every order rests on, as ``@theorem(uses=...)``
    does: the kernel's harmonicity.
    """

    def decorate(fn: Any) -> Reconstruction:
        claim = Reconstruction(
            fn, kernel=kernel, order=order, points=points, digits=digits, uses=uses
        )
        try:
            decline(claim.fact_id("symbolic"), FOR_THE_CAS)
        except LookupError:  # no Lean oracle registered, so none to keep away
            pass
        return registry.register_object(claim)

    return decorate


# }}}


@reconstructs(log_r, order=ORDER, uses=harmonic)
def compressed_taylor():
    """sumpy's compressed Taylor wrangler for the 2-D Laplace kernel."""
    from sumpy.expansion import LinearPDEBasedExpansionTermsWrangler
    from sumpy.kernel import LaplaceKernel

    return LinearPDEBasedExpansionTermsWrangler(
        order=ORDER, dim=2, max_mi=None, knl=LaplaceKernel(2)
    )


# {{{ running it


def _table(rows: list[tuple[str, ...]]) -> list[str]:
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    lines = [
        "  ".join(cell.ljust(width) for cell, width in zip(row, widths, strict=True)).rstrip()
        for row in rows
    ]
    lines.insert(1, "  ".join("-" * width for width in widths))
    return lines


def _combination_text(claim: Reconstruction, index: int) -> str:
    """How the wrangler reconstructs a coefficient: ``stored``, or ``-(0, 4)``."""
    weights, mi = claim.weights[index], claim.identifiers[index]
    if mi in claim.stored and list(weights.items()) == [(claim.stored.index(mi), 1)]:
        return "stored"
    parts = []
    for place, weight in weights.items():
        sign = "-" if weight < 0 else "+"
        size = "" if abs(weight) == 1 else f"{abs(weight)}*"
        parts.append(f"{sign} {size}{claim.stored[place]}")
    text = " ".join(parts)
    return text[2:] if text.startswith("+ ") else "-" + text[2:]


def main() -> int:
    """Print each coefficient beside its derivative; exit 1 unless every one agrees."""
    import sympy

    claim = compressed_taylor
    simplified = claim.simplified()
    largest, found = claim.sampled()
    rows = [
        (
            "(a, b)",
            "reconstructed",
            "direct derivative of G",
            "difference (sympy)",
            "difference (mpmath)",
        )
    ]
    for index, mi in enumerate(claim.identifiers):
        rows.append(
            (
                str(mi),
                _combination_text(claim, index),
                str(sympy.factor(claim.derivatives[index])),
                str(simplified[index]),
                (
                    f"within {float(claim.tolerance):.0e}"
                    if float(largest[index]) <= float(claim.tolerance)
                    else f"{float(largest[index]):.1e}"
                ),
            )
        )
    print(
        f"sumpy's compressed Taylor wrangler for G = {claim.kernel_text}, the 2-D Laplace\n"
        f"kernel, stores {len(claim.stored)} of the {len(claim.identifiers)} derivatives "
        f"through order {claim.order} and reconstructs the rest:"
    )
    print()
    print("\n".join(_table(rows)))
    print()
    agree = all(difference == 0 for difference in simplified) and found is None
    if agree:
        print(
            "Every reconstructed coefficient is the direct derivative. sympy simplifies each\n"
            f"difference to 0, and mpmath's derivatives, at {claim.digits} digits, agree to "
            f"within {float(claim.tolerance):.0e}\n"
            f"of each other, relative, at {claim.points} points."
        )
    else:
        print("Some reconstructed coefficient is NOT the direct derivative: see the table.")
        if found is not None:
            print(f"mpmath: {found}")
    print()
    if claim.pde is not None:
        print(
            f"Through order {claim.order} the wrangler follows the recurrence\n"
            f"{claim.recurrence_text()}, which is the PDE sumpy\n"
            f"declares for the kernel, {claim.pde_text()}, solved for "
            f"{_derivative_name(claim.leading)}."
        )
    else:
        print("The wrangler's weights do not follow the recurrence its kernel's PDE gives.")
    print()
    print(
        "`lanky check examples/sumpy_recurrence.py` puts the claim in the ledger: tested by\n"
        "mpmath, decided by the CAS oracle where sympy is installed, and proved for every\n"
        "order by Lean where Mathlib is, under the kernel's harmonicity."
    )
    return 0 if agree else 1


if __name__ == "__main__":
    raise SystemExit(main())

# }}}
