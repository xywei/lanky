"""Induction over families of expressions: Python searches for the step, Lean checks it.

The design idea. A claim about every order of something, every derivative of a
kernel or every term of a series, quantifies the order, a natural number, and
applies families to it: ``all(R(a)(b) == D(a)(b) for a in Nat for b in Nat)``.
Its hypotheses say how a family at one order is made from the family at lower
ones, a recurrence, and what holds at the lowest. Its proof is an induction on
the order, and the step of that induction is an identity: the goal at ``a +
2`` is a combination of the recurrence at ``a``, the induction hypothesis at
``a`` and whatever else the hypotheses give, with coefficients that are
numbers, or rational functions of the statement's other variables. Lean's
``linear_combination`` checks such a combination, by moving everything to one
side and normalizing with ``ring``, or with ``field_simp`` and then ``ring``
where the coefficients have denominators. What it does not do is find the
combination. Finding it is a search, and checking it is a computation, so the
two are split: Python searches, Lean checks.

This module is the Python half. A :class:`Case` is one case of the proof, the
goal there and the hypotheses it may use, each a :class:`Lemma`; a finder takes
a case and returns a certificate, the uses (:class:`Use`) of the lemmas, each at
the values it is applied at and with its multiplier, whose combination is the
goal. :func:`find_certificate` is lanky's finder, and a plugin can hand the Lean
oracle its own (:func:`lanky.oracles.lean.use_certificate`), which is the
certificate hook: a plugin that knows where its multipliers come from, the
coefficients of a PDE, say, need not have them searched for. Whatever a finder
returns, Lean checks it; a wrong certificate costs one failed attempt and
never a wrong proof. The Lean half, which reads the cases off a statement and
writes the script that has Lean check the certificates, is
:func:`lanky.oracles.lean.family_induction_scripts`.

The search is plain. The applications of a family in the goal are the atoms,
and a lemma whose equation applies the same family is instantiated by solving
the affine equations that make one of its applications the atom: ``R(a + 2)(b)``
against ``R(k + 2)(b)`` gives ``a = k``. The applications that instance brings
in are atoms in turn, for a few rounds. Each instance has to satisfy its
lemma's guards, which are read as affine inequalities over the bounds the case
gives its variables (a natural is at least ``0``, the induction hypothesis is
for an order below the one in the goal), and an instance whose guards cannot be
shown that way is not proposed. Then the goal, and every instance, is a linear
form in the atoms, with coefficients and a constant term that are expressions
in the other variables, and the multipliers solve a linear system over the
rational functions of those variables. That is sympy's (the ``cas`` extra), and
without it lanky's finder finds nothing and the oracle's ladder goes on without
the certificate.
"""

from __future__ import annotations

import itertools
import numbers
from collections.abc import Callable, Mapping
from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Abs,
    Comparison,
    Elementary,
    Exists,
    Forall,
    Sum,
    Var,
    conjuncts,
    init_args,
)

__all__ = [
    "Case",
    "Finder",
    "Lemma",
    "Use",
    "domain_conditions",
    "find_certificate",
    "lemma_of",
    "substitute",
    "substitute_domain",
]

#: How many times the search widens its set of atoms before it gives up.
ROUNDS = 4

#: How many instances of the lemmas the search proposes at most.
MAX_INSTANCES = 48


# {{{ what a case is


@dataclass(frozen=True, eq=False)
class Lemma:
    """A hypothesis a case may use: an equation under binders, and how Lean applies it.

    Attributes:
        name: The name Lean knows it by: a theorem's hypothesis, ``h0`` and
            on, or the induction hypothesis.
        binders: ``(variable, domain)`` pairs, in the order Lean takes them,
            for which a use gives values.
        premises: What Lean applies the hypothesis to, in order: ``("value",
            name)`` for a binder, which a use gives, and ``("proof", guard)``
            for a guard, which the script discharges.
        equation: The equation it gives, over the binders and the names of
            the case.
        conditions: What a use has to satisfy that is not a premise: that
            the order the induction hypothesis is applied at is a natural,
            which its type says and no premise does.
    """

    name: str
    binders: tuple[tuple[Var, Any], ...]
    premises: tuple[tuple[str, Any], ...]
    equation: Any
    conditions: tuple[Any, ...] = ()

    @property
    def guards(self) -> tuple[Any, ...]:
        """Every proposition a use has to make true, premises and conditions both."""
        return (*(term for kind, term in self.premises if kind == "proof"), *self.conditions)


@dataclass(frozen=True, eq=False)
class Case:
    """One case of an induction's proof: the goal there, and what may be used for it.

    Attributes:
        name: Which case it is, for messages: ``"base"``, ``"step"``, or the
            value of the order in a base case taken one value at a time.
        goal: The equation to prove, as a comparison over ``variables``.
        lemmas: What the case may use: the statement's hypotheses that are
            equations, and, in the step and in a base case taken at a value,
            the induction hypothesis.
        variables: The lanky type of every name in scope: the statement's
            own binders, the goal's other variables and the case's own.
        bounds: For each integer name in scope, what is known of its value,
            as ``(lower, upper)``, each a term or ``None``: a natural is at
            least ``0``, a point of ``Fin[n]`` at most ``n - 1``, and the order
            in a base case below the step.
        families: The names in scope that are families; an application of one
            is an atom of the linear forms.
    """

    name: str
    goal: Any
    lemmas: tuple[Lemma, ...]
    variables: Mapping[str, Any]
    bounds: Mapping[str, tuple[Any, Any]]
    families: frozenset[str]


@dataclass(frozen=True, eq=False)
class Use:
    """One use of a lemma in a certificate: the lemma, where it is applied, and its multiplier.

    Attributes:
        lemma: The lemma's name (:attr:`Lemma.name`).
        arguments: A value for each of the lemma's binders, in order, as
            lanky terms over the case's names.
        multiplier: What the lemma's equation is multiplied by in the
            combination, a lanky term over the case's names; ``1`` by default.
    """

    lemma: str
    arguments: tuple[Any, ...] = ()
    multiplier: Any = 1


#: What a certificate hook is: a case in, the uses whose combination is its
#: goal out, or ``None`` when it has none.
Finder = Callable[[Case], "tuple[Use, ...] | None"]


def domain_conditions(var: Var, domain: Any) -> list[Any]:
    """The guards a binder's domain gives its variable, as terms, in the order Lean takes them.

    The terms :func:`lanky.lean.domain_guards` prints: ``0 <= n`` for a
    natural, ``0 <= i`` and ``i < n`` for a point of ``Fin[n]``, the base's
    and then the refinement's own for a refinement, and nothing for any other
    sort. Each is a premise of a hypothesis that quantifies the variable.
    """
    if isinstance(domain, Sort) and domain.name == "Nat":
        return [Comparison(0, "<=", var)]
    if isinstance(domain, FinType):
        return [Comparison(0, "<=", var), Comparison(var, "<", domain.bound)]
    if isinstance(domain, Refined):
        return [*domain_conditions(var, domain.base), *domain.props]
    return []


def lemma_of(name: str, term: Any) -> Lemma | None:
    """The lemma a hypothesis is, or ``None`` when it is not an equation under universals.

    Nested universals are taken apart level by level, as Lean prints them:
    each binder with its domain's guards after it, and a level's own guard
    after its last binder, one premise per conjunct.
    """
    binders: list[tuple[Var, Any]] = []
    premises: list[tuple[str, Any]] = []
    node = term
    while isinstance(node, Forall):
        for var, domain in node.binders:
            binders.append((var, domain))
            premises.append(("value", var.name))
            premises += [("proof", guard) for guard in domain_conditions(var, domain)]
        premises += [("proof", guard) for guard in conjuncts(node.guard)]
        node = node.body
    if not (isinstance(node, prim.Comparison) and node.operator == "=="):
        return None
    names = [var.name for var, _ in binders]
    if len(set(names)) != len(names):
        # a level that rebinds a name of an outer one: the values could not be told apart
        return None
    return Lemma(name, tuple(binders), tuple(premises), node)


def substitute(expr: Any, values: Mapping[str, Any]) -> Any:
    """``expr`` with each variable ``values`` names replaced by its value.

    A binder of a quantifier or a reduction hides the outer name it shares
    inside its body, guard and later domains, as it does in Python.
    """
    if not values:
        return expr
    if isinstance(expr, prim.Variable):
        return values.get(expr.name, expr)
    if isinstance(expr, tuple):
        return tuple(substitute(item, values) for item in expr)
    if isinstance(expr, Forall | Exists | Sum):
        inner = dict(values)
        binders = []
        for var, domain in expr.binders:
            binders.append((var, substitute_domain(domain, inner)))
            inner.pop(var.name, None)
        guard = None if expr.guard is None else substitute(expr.guard, inner)
        return type(expr)(tuple(binders), substitute(expr.body, inner), guard)
    if isinstance(expr, prim.ExpressionNode):
        return type(expr)(*(substitute(arg, values) for arg in init_args(expr)))
    return expr


def substitute_domain(domain: Any, values: Mapping[str, Any]) -> Any:
    """A binder's domain with ``values`` put in its bound and its refinement, and a family's."""
    if isinstance(domain, FinType):
        return FinType(substitute(domain.bound, values))
    if isinstance(domain, Refined):
        return Refined(
            substitute_domain(domain.base, values),
            tuple(substitute(prop, values) for prop in domain.props),
        )
    if isinstance(domain, FnType):
        return FnType(
            substitute_domain(domain.domain, values), substitute_domain(domain.codomain, values)
        )
    return domain


# }}}


# {{{ the algebra, in sympy


class _Unsupported(Exception):
    """A term the search cannot read as an expression in sympy."""


def _sympy() -> Any | None:
    """sympy, or ``None`` where it is not installed."""
    try:
        import sympy
    except ImportError:
        return None
    return sympy


class _Algebra:
    """Terms of a case as sympy expressions, a family application as an applied function.

    A family ``R`` applied as ``R(a + 2)(b)`` is ``R(a + 2, b)``, an undefined
    function of sympy's, so that putting values for the variables in its
    arguments is sympy's ``subs`` and finding the atoms is ``atoms``. An
    integer variable is an integer symbol, so that an argument of a family
    reads as the integer expression it is.
    """

    def __init__(self, sympy: Any, case: Case) -> None:
        self.sympy = sympy
        self.case = case
        self.symbols: dict[str, Any] = {}
        self.functions: dict[str, Any] = {}
        self.names: dict[Any, str] = {}
        self._fresh = itertools.count()

    def symbol(self, name: str, sort: Any = None) -> Any:
        """The sympy symbol of a variable of the case, made the first time it is asked for."""
        found = self.symbols.get(name)
        if found is None:
            found = self.symbols[name] = self._make(name, sort or self.case.variables.get(name))
            self.names[found] = name
        return found

    def bound_symbol(self, var: Var, sort: Any) -> Any:
        """A fresh symbol for a lemma's binder, which no name of the case can be confused with."""
        symbol = self._make(f"{var.name}__{next(self._fresh)}", sort)
        self.names[symbol] = var.name
        return symbol

    def _make(self, name: str, sort: Any) -> Any:
        base = sort
        while isinstance(base, Refined):
            base = base.base
        if isinstance(base, FinType) or (
            isinstance(base, Sort) and base.name in ("Nat", "Int")
        ):
            return self.sympy.Symbol(name, integer=True)
        if isinstance(base, Sort) and base.name == "Real":
            return self.sympy.Symbol(name, real=True)
        return self.sympy.Symbol(name)

    def is_integer(self, symbol: Any) -> bool:
        """Whether a symbol stands for an integer: the variables bounds are kept for."""
        return bool(symbol.is_integer)

    def convert(self, expr: Any, scope: Mapping[str, Any]) -> Any:
        """A lanky term as a sympy expression; ``scope`` maps a name to its symbol first.

        Raises:
            _Unsupported: For anything but arithmetic, ``exp``, ``log``,
                ``sqrt``, an absolute value and a family's application.
        """
        sympy = self.sympy
        if isinstance(expr, bool):
            raise _Unsupported(f"{expr} is a truth value")
        if isinstance(expr, prim.Variable):
            if expr.name in scope:
                return scope[expr.name]
            if expr.name in self.case.families:
                raise _Unsupported(f"the family {expr.name} is used without being applied")
            return self.symbol(expr.name)
        if isinstance(expr, numbers.Number):
            return _number(sympy, expr)
        if isinstance(expr, prim.Call | prim.Subscript):
            spine = _spine(expr)
            if spine is None or spine[0] not in self.case.families:
                raise _Unsupported("an application of something that is not a family")
            name, arguments = spine
            function = self.functions.get(name)
            if function is None:
                function = self.functions[name] = sympy.Function(name)
            return function(*(self.convert(argument, scope) for argument in arguments))
        if isinstance(expr, prim.Sum):
            return sympy.Add(*(self.convert(child, scope) for child in expr.children))
        if isinstance(expr, prim.Product):
            return sympy.Mul(*(self.convert(child, scope) for child in expr.children))
        if isinstance(expr, prim.Quotient):
            return self.convert(expr.numerator, scope) / self.convert(expr.denominator, scope)
        if isinstance(expr, prim.Power):
            return sympy.Pow(self.convert(expr.base, scope), self.convert(expr.exponent, scope))
        if isinstance(expr, Elementary):
            function = {"exp": sympy.exp, "log": sympy.log, "sqrt": sympy.sqrt}[expr.function]
            return function(self.convert(expr.argument, scope))
        if isinstance(expr, Abs):
            return sympy.Abs(self.convert(expr.operand, scope))
        raise _Unsupported(f"a {type(expr).__name__}")

    def side(self, equation: Any, scope: Mapping[str, Any]) -> Any:
        """An equation as one expression, its left side less its right."""
        return self.convert(equation.left, scope) - self.convert(equation.right, scope)

    def applications(self, expr: Any) -> set[Any]:
        """The applications of a family in ``expr``: its atoms."""
        return {atom for atom in expr.atoms(self.sympy.core.function.AppliedUndef)}

    def back(self, expr: Any) -> Any:
        """A sympy expression over the case's names as the lanky term it is.

        A sum is written with its constant last, ``b + 2`` where sympy keeps
        ``2 + b``, which is how a hypothesis is usually written, so that the
        application a use brings in reads as the one it is to cancel. The
        script normalizes what does not (see
        :data:`lanky.oracles.lean.COMBINATION_NORM`).
        """
        from lanky.cas import from_sympy

        term = from_sympy(expr, {name: Var(name) for name in self.case.variables})
        if isinstance(term, prim.Sum):
            numbers_last = sorted(
                term.children, key=lambda child: isinstance(child, numbers.Number)
            )
            term = type(term)(tuple(numbers_last))
        return term


def _number(sympy: Any, value: Any) -> Any:
    """A Python number as the sympy number it is, exactly."""
    if isinstance(value, bool):
        raise _Unsupported(f"{value} is a truth value")
    if isinstance(value, numbers.Integral):
        return sympy.Integer(int(value))
    if isinstance(value, numbers.Rational):
        return sympy.Rational(int(value.numerator), int(value.denominator))
    if isinstance(value, float):
        exact = Fraction(value)
        return sympy.Rational(exact.numerator, exact.denominator)
    if isinstance(value, complex):
        return _number(sympy, value.real) + sympy.I * _number(sympy, value.imag)
    raise _Unsupported(f"{value!r} is not a number")


def _spine(expr: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family, arguments)`` of a chain of applications, ``f(i)(j)`` as ``f`` at ``(i, j)``."""
    arguments: tuple[Any, ...] = ()
    while True:
        if isinstance(expr, prim.Call):
            arguments = (*expr.parameters, *arguments)
            expr = expr.function
        elif isinstance(expr, prim.Subscript):
            index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
            arguments = (*index, *arguments)
            expr = expr.aggregate
        elif isinstance(expr, prim.Variable):
            return (expr.name, arguments) if arguments else None
        else:
            return None


# }}}


# {{{ guards, read as affine inequalities


def _extreme(sympy: Any, expr: Any, bounds: Mapping[Any, tuple[Any, Any]], largest: bool) -> Any:
    """The largest (or smallest) value an affine expression takes within ``bounds``, or ``None``.

    Each symbol is replaced by the bound that pushes the expression the way
    the call wants it, and a bound may itself mention a symbol with bounds of
    its own, so this is a loop. A symbol with no bound that way, a
    coefficient that is not a number, and an expression that is not affine
    leave it unbounded, as far as this can tell: ``None``.
    """
    expr = sympy.expand(expr)
    for _ in range(16):
        free = sorted(expr.free_symbols, key=str)
        if not free:
            return expr
        try:
            polynomial = sympy.Poly(expr, *free)
        except sympy.PolynomialError:
            return None
        if polynomial.total_degree() > 1:
            return None
        symbol = free[0]
        coefficient = polynomial.coeff_monomial(symbol)
        if not coefficient.is_number:
            return None
        if coefficient == 0:
            expr = expr.subs(symbol, 0)
            continue
        lower, upper = bounds.get(symbol, (None, None))
        bound = upper if (coefficient > 0) == largest else lower
        if bound is None:
            return None
        expr = sympy.expand(expr.subs(symbol, bound))
    return None


def _implied(algebra: _Algebra, guard: Any, scope: Mapping[str, Any], bounds: Any) -> bool:
    """Whether the case's bounds show ``guard`` at the values ``scope`` gives.

    A comparison of integers is read as an affine inequality, an equation as
    an identity, and a conjunction and a disjunction as their parts. Anything
    else, a guard over the reals among them, is not shown, so the instance
    that needs it is not proposed.
    """
    sympy = algebra.sympy
    if guard is True:
        return True
    if isinstance(guard, prim.LogicalAnd):
        return all(_implied(algebra, child, scope, bounds) for child in guard.children)
    if isinstance(guard, prim.LogicalOr):
        return any(_implied(algebra, child, scope, bounds) for child in guard.children)
    if not isinstance(guard, prim.Comparison):
        return False
    try:
        difference = algebra.convert(guard.left, scope) - algebra.convert(guard.right, scope)
    except _Unsupported:
        return False
    if difference.atoms(sympy.core.function.AppliedUndef):
        return False
    if guard.operator == "==":
        return sympy.expand(difference) == 0
    # between integers a strict inequality is one by at least 1
    gap = 1 if difference.is_integer else 0
    if guard.operator in ("<", "<="):
        highest = _extreme(sympy, difference, bounds, largest=True)
        if highest is None or not highest.is_number:
            return False
        return bool(highest <= -gap) if guard.operator == "<" else bool(highest <= 0)
    if guard.operator in (">", ">="):
        lowest = _extreme(sympy, difference, bounds, largest=False)
        if lowest is None or not lowest.is_number:
            return False
        return bool(lowest >= gap) if guard.operator == ">" else bool(lowest >= 0)
    if guard.operator == "!=":
        highest = _extreme(sympy, difference, bounds, largest=True)
        lowest = _extreme(sympy, difference, bounds, largest=False)
        return bool(
            (highest is not None and highest.is_number and highest < 0)
            or (lowest is not None and lowest.is_number and lowest > 0)
        )
    return False


# }}}


# {{{ the search


@dataclass(eq=False)
class _Instance:
    """A lemma at values: what is applied, and the equation it gives."""

    lemma: Lemma
    values: tuple[Any, ...]
    side: Any
    atoms: set[Any] = field(default_factory=set)


def _bounds(algebra: _Algebra, case: Case) -> dict[Any, tuple[Any, Any]]:
    """The case's bounds, by symbol."""
    out: dict[Any, tuple[Any, Any]] = {}
    for name, (lower, upper) in case.bounds.items():
        symbol = algebra.symbol(name)
        out[symbol] = tuple(
            None if bound is None else algebra.convert(bound, {}) for bound in (lower, upper)
        )
    return out


def _patterns(algebra: _Algebra, lemma: Lemma) -> tuple[dict[str, Any], Any, set[Any]] | None:
    """A lemma's binders as fresh symbols, its equation over them, and its applications."""
    scope = {var.name: algebra.bound_symbol(var, domain) for var, domain in lemma.binders}
    try:
        side = algebra.side(lemma.equation, scope)
    except _Unsupported:
        return None
    return scope, side, algebra.applications(side)


def _unify(sympy: Any, pattern: Any, atom: Any, unknowns: list[Any]) -> dict[Any, Any] | None:
    """The values of ``unknowns`` that make the application ``pattern`` the application ``atom``.

    Both have to apply the same family to as many arguments, and the
    equations between their arguments have to fix every unknown, with an
    integer expression: an argument is an integer, and a value with a
    fraction in it, ``k / 2``, is no point of the family's domain in general.
    """
    if pattern.func != atom.func or len(pattern.args) != len(atom.args):
        return None
    equations = [
        sympy.expand(left - right) for left, right in zip(pattern.args, atom.args, strict=True)
    ]
    equations = [equation for equation in equations if equation != 0]
    present = [unknown for unknown in unknowns if any(e.has(unknown) for e in equations)]
    if not present:
        return {} if not equations else None
    try:
        solutions = sympy.linsolve(equations, present)
    except (ValueError, TypeError, NotImplementedError, sympy.PolynomialError):
        return None
    if not isinstance(solutions, sympy.FiniteSet) or len(solutions) != 1:
        return None
    (solution,) = solutions
    values = dict(zip(present, solution, strict=True))
    for value in values.values():
        # sympy reads an integer combination of integer symbols as an integer
        if value.free_symbols & set(present) or value.is_integer is not True:
            return None
    return values


def _linear(sympy: Any, side: Any, atoms: list[Any]) -> tuple[list[Any], Any] | None:
    """``side`` as its coefficient on each atom and its constant term, or ``None`` if not linear."""
    marks = [sympy.Dummy(f"atom{index}") for index in range(len(atoms))]
    replaced = side.xreplace(dict(zip(atoms, marks, strict=True)))
    if replaced.atoms(sympy.core.function.AppliedUndef):
        return None
    coefficients = []
    for mark in marks:
        coefficient = sympy.diff(replaced, mark)
        if any(sympy.simplify(sympy.diff(coefficient, other)) != 0 for other in marks):
            return None
        coefficients.append(sympy.simplify(coefficient))
    constant = sympy.simplify(replaced.subs({mark: 0 for mark in marks}))
    return coefficients, constant


def _solve(sympy: Any, goal: Any, instances: list[_Instance]) -> list[Any] | None:
    """Multipliers whose combination of the instances is the goal, or ``None``.

    The goal and each instance are linear forms in the atoms; the multipliers
    make every coefficient and the constant term agree. Where the system has
    many solutions, the free multipliers are ``0``.
    """
    found = set(goal.atoms(sympy.core.function.AppliedUndef))
    for instance in instances:
        found |= instance.atoms
    atoms = sorted(found, key=str)
    target = _linear(sympy, goal, atoms)
    if target is None:
        return None
    forms = []
    for instance in instances:
        form = _linear(sympy, instance.side, atoms)
        if form is None:
            return None
        forms.append(form)
    unknowns = [sympy.Dummy(f"mu{index}") for index in range(len(instances))]
    pairs = list(zip(unknowns, forms, strict=True))
    zero = sympy.Integer(0)
    equations = [
        target[0][position] - sum((mu * form[0][position] for mu, form in pairs), zero)
        for position in range(len(atoms))
    ]
    equations.append(target[1] - sum((mu * form[1] for mu, form in pairs), zero))
    equations = [equation for equation in equations if sympy.simplify(equation) != 0]
    if not equations:
        return [sympy.Integer(0)] * len(instances)
    try:
        solutions = sympy.linsolve(equations, unknowns)
    except (ValueError, TypeError, NotImplementedError):
        return None
    if not isinstance(solutions, sympy.FiniteSet) or len(solutions) == 0:
        return None
    solution = next(iter(solutions))
    free = {unknown: 0 for unknown in unknowns}
    multipliers = [sympy.factor(sympy.simplify(value.subs(free))) for value in solution]
    combined = zip(multipliers, instances, strict=True)
    residual = goal - sum((multiplier * instance.side for multiplier, instance in combined), zero)
    if sympy.simplify(residual) != 0:
        return None
    return multipliers


def find_certificate(case: Case) -> tuple[Use, ...] | None:
    """lanky's certificate hook: the uses whose combination is the case's goal, or ``None``.

    The search the module docstring describes: instances of the lemmas, at
    the atoms of the goal and then at the atoms they bring in, for
    :data:`ROUNDS` rounds and :data:`MAX_INSTANCES` instances at most, and the
    multipliers that make their combination the goal. ``None`` where sympy is
    not installed, where the goal or a lemma is not an equation the search can
    read, and where no combination of what it found is the goal.
    """
    sympy = _sympy()
    if sympy is None:
        return None
    algebra = _Algebra(sympy, case)
    try:
        goal = algebra.side(case.goal, {})
        bounds = _bounds(algebra, case)
    except _Unsupported:
        return None
    patterns = []
    for lemma in case.lemmas:
        found = _patterns(algebra, lemma)
        if found is not None:
            patterns.append((lemma, *found))
    frontier = list(algebra.applications(goal))
    known = set(frontier)
    instances: list[_Instance] = []
    seen: set[tuple[str, tuple[Any, ...]]] = set()
    for _ in range(ROUNDS):
        fresh: list[Any] = []
        for atom in frontier:
            for lemma, scope, side, applications in patterns:
                unknowns = [scope[var.name] for var, _ in lemma.binders]
                for pattern in applications:
                    values = _unify(sympy, pattern, atom, unknowns)
                    if values is None or len(values) != len(unknowns):
                        continue
                    ordered = tuple(sympy.expand(values[unknown]) for unknown in unknowns)
                    key = (lemma.name, ordered)
                    if key in seen:
                        continue
                    seen.add(key)
                    at = dict(zip((var.name for var, _ in lemma.binders), ordered, strict=True))
                    if not all(_implied(algebra, guard, at, bounds) for guard in lemma.guards):
                        continue
                    instance_side = side.xreplace(values)
                    instance = _Instance(
                        lemma, ordered, instance_side, algebra.applications(instance_side)
                    )
                    instances.append(instance)
                    for application in instance.atoms - known:
                        known.add(application)
                        fresh.append(application)
            if len(instances) > MAX_INSTANCES:
                break
        if instances:
            multipliers = _solve(sympy, goal, instances)
            if multipliers is not None:
                return tuple(
                    Use(
                        instance.lemma.name,
                        tuple(algebra.back(value) for value in instance.values),
                        algebra.back(multiplier),
                    )
                    for instance, multiplier in zip(instances, multipliers, strict=True)
                    if multiplier != 0
                )
        if not fresh or len(instances) > MAX_INSTANCES:
            return None
        frontier = fresh
    return None


# }}}
