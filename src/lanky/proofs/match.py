"""The algebra a written proof needs before Lean is asked: points, cases and pins.

Three questions are answered here, in Python, and each answer only produces
text that Lean checks. Where is a fact cited without a point (``return
stored``) applied? Which cases of a proof are impossible, or certain, given
the conditions of the path to them? And which variables does a case's
condition fix (``a + b == 0`` among naturals fixes ``a`` and ``b`` at ``0``)?

A point is found by matching. A fact's applications of a family, ``D[i, a',
b']``, are matched against the applications in the case's claim, ``D[i, a,
b]``: each argument is an affine form in the fact's binders, and the
equations between the arguments are solved one unknown at a time, so ``R[x +
2, y]`` against ``R[a, b]`` gives ``x = a - 2`` and ``y = b``. Only integer
solutions with a coefficient of one are taken, which is what an offset is; a
point that needs a division is left for the user to write.

The cases are read with lanky's induction search (:mod:`lanky.induction`),
which reads a guard as an affine inequality over the bounds of its variables
and the facts of the case. It needs sympy (the ``cas`` extra); without it a
condition is known only when the path has asked it, or its negation, before.
"""

from __future__ import annotations

import numbers
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import domain_conditions, substitute
from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import Comparison, Forall, LogicalNot, Var, conjuncts, render

__all__ = [
    "Shape",
    "affine",
    "applications",
    "decide",
    "from_affine",
    "integer_sort",
    "negated",
    "pins",
    "shape_of",
    "spine",
    "unify",
]


# {{{ affine forms


def affine(term: Any) -> dict[str | None, Fraction] | None:
    """``term`` as a sum of rational multiples of its variables and a constant, or ``None``.

    The constant is kept under ``None``. A family's application, a power, a
    division by something that is not a number, or a product of two
    variables is no affine form.
    """
    if isinstance(term, bool):
        return None
    if isinstance(term, numbers.Integral):
        return {None: Fraction(int(term))} if term else {}
    if isinstance(term, Fraction):
        return {None: term} if term else {}
    if isinstance(term, prim.Variable):
        return {term.name: Fraction(1)}
    if isinstance(term, prim.Sum):
        total: dict[str | None, Fraction] = {}
        for child in term.children:
            form = affine(child)
            if form is None:
                return None
            _accumulate(total, form, Fraction(1))
        return total
    if isinstance(term, prim.Product):
        factor = Fraction(1)
        variable: dict[str | None, Fraction] | None = None
        for child in term.children:
            form = affine(child)
            if form is None:
                return None
            if set(form) <= {None}:
                factor *= form.get(None, Fraction(0))
                continue
            if variable is not None:
                return None
            variable = form
        if variable is None:
            return {None: factor} if factor else {}
        out: dict[str | None, Fraction] = {}
        _accumulate(out, variable, factor)
        return out
    if isinstance(term, prim.Quotient):
        numerator, denominator = affine(term.numerator), affine(term.denominator)
        if numerator is None or denominator is None or not set(denominator) <= {None}:
            return None
        divisor = denominator.get(None, Fraction(0))
        if not divisor:
            return None
        out = {}
        _accumulate(out, numerator, 1 / divisor)
        return out
    return None


def _accumulate(
    total: dict[str | None, Fraction], form: Mapping[str | None, Fraction], factor: Fraction
) -> None:
    """Add ``factor`` times ``form`` into ``total``, dropping what cancels."""
    for key, value in form.items():
        combined = total.get(key, Fraction(0)) + factor * value
        if combined:
            total[key] = combined
        else:
            total.pop(key, None)


def _number(value: Fraction) -> int | Fraction:
    """A rational as an ``int`` where it is one, as a term holds it."""
    return int(value) if value.denominator == 1 else value


def from_affine(form: Mapping[str | None, Fraction], order: Sequence[str] = ()) -> Any:
    """The term an affine form is, written as a reader would: ``a - 2``, ``b + 2``, ``-a``.

    The variables come in ``order`` first and then by name, and the constant
    last.
    """
    names = [name for name in order if name in form]
    names += sorted(name for name in form if name is not None and name not in names)
    term: Any = None
    for name in names:
        coefficient = form[name]
        piece: Any = Var(name) if coefficient == 1 else _number(coefficient) * Var(name)
        if term is None:
            term = -Var(name) if coefficient == -1 else piece
        elif coefficient < 0:
            term = term - (Var(name) if coefficient == -1 else _number(-coefficient) * Var(name))
        else:
            term = term + piece
    constant = form.get(None, Fraction(0))
    if term is None:
        return _number(constant)
    if constant > 0:
        return term + _number(constant)
    if constant < 0:
        return term - _number(-constant)
    return term


def simplified(term: Any, order: Sequence[str] = ()) -> Any:
    """``term``, written as its affine form where it has one: ``a - 2 + 2`` is ``a``."""
    form = affine(term)
    return term if form is None else from_affine(form, order)


# }}}


# {{{ applications of families


def spine(term: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family, arguments)`` of an application, ``R[i, a, b]`` or ``R(a)(b)``; else ``None``."""
    arguments: tuple[Any, ...] = ()
    while True:
        if isinstance(term, prim.Call):
            arguments = (*term.parameters, *arguments)
            term = term.function
        elif isinstance(term, prim.Subscript):
            index = term.index if isinstance(term.index, tuple) else (term.index,)
            arguments = (*index, *arguments)
            term = term.aggregate
        elif isinstance(term, prim.Variable):
            return (term.name, arguments) if arguments else None
        else:
            return None


def applications(term: Any) -> list[Any]:
    """Every application of a family in ``term``, outermost first, each once by its text."""
    from lanky.terms import Exists, Sum, init_args

    found: list[Any] = []
    seen: set[str] = set()
    stack = [term]
    while stack:
        node = stack.pop(0)
        if isinstance(node, prim.Call | prim.Subscript) and spine(node) is not None:
            key = render(node)
            if key not in seen:
                seen.add(key)
                found.append(node)
            stack.extend(spine(node)[1])
            continue
        if isinstance(node, Forall | Exists | Sum):
            stack.extend(part for part in (node.body, node.guard) if part is not None)
        elif isinstance(node, prim.ExpressionNode):
            for child in init_args(node):
                stack.extend(child if isinstance(child, tuple) else (child,))
    return found


def _split(term: Any, unknowns: Iterable[str]) -> tuple[dict[str, Fraction], Any] | None:
    """``term`` as ``sum(c * u) + rest``, with no unknown in ``rest``; ``None`` if it is not.

    A term that is no affine form is ``rest`` itself when it mentions no
    unknown.
    """
    from lanky.terms import free_variables

    unknown = set(unknowns)
    form = affine(term)
    if form is None:
        if free_variables(term) & unknown:
            return None
        return {}, term
    coefficients = {name: value for name, value in form.items() if name in unknown}
    rest = {name: value for name, value in form.items() if name not in unknown}
    return coefficients, from_affine(rest)


def same(left: Any, right: Any) -> bool:
    """Whether two terms are equal as integers by their affine forms, or as written."""
    from lanky.terms import structurally_equal

    first, second = affine(left), affine(right)
    if first is not None and second is not None:
        return first == second
    return structurally_equal(left, right) or render(left) == render(right)


def unify(
    pattern: Any, atom: Any, unknowns: Sequence[str], order: Sequence[str] = ()
) -> dict[str, Any] | None:
    """The values of ``unknowns`` that make the application ``pattern`` the application ``atom``.

    Both have to apply the same family to as many arguments. Each equation
    between two arguments is affine in the unknowns; one with a single
    unknown left, at a coefficient of one or minus one, gives its value, and
    an equation with none left has to hold as it stands. ``None`` when the
    applications do not match; the unknowns the arguments do not mention are
    left out of the answer. ``order`` is the order the values' variables are
    written in.
    """
    first, second = spine(pattern), spine(atom)
    if first is None or second is None:
        return None
    if first[0] != second[0] or len(first[1]) != len(second[1]):
        return None
    pending = list(zip(first[1], second[1], strict=True))
    solved: dict[str, Any] = {}
    while pending:
        progress = False
        left_over = []
        for left, right in pending:
            here = substitute(left, solved)
            split = _split(here, [name for name in unknowns if name not in solved])
            if split is None:
                return None
            coefficients, rest = split
            if not coefficients:
                if not same(rest, right):
                    return None
                progress = True
                continue
            if len(coefficients) == 1:
                ((name, coefficient),) = coefficients.items()
                if coefficient in (1, -1):
                    value = _solve_for(right, rest, coefficient, order)
                    if value is None:
                        return None
                    solved[name] = value
                    progress = True
                    continue
            left_over.append((left, right))
        if not progress:
            return None
        pending = left_over
    return solved


def _solve_for(right: Any, rest: Any, coefficient: Fraction, order: Sequence[str]) -> Any:
    """The unknown ``u`` with ``coefficient * u + rest == right``, simplified where it can be."""
    first, second = affine(right), affine(rest)
    if first is not None and second is not None:
        form: dict[str | None, Fraction] = {}
        _accumulate(form, first, coefficient)
        _accumulate(form, second, -coefficient)
        return from_affine(form, order)
    value = right - rest if not _is_zero(rest) else right
    return value if coefficient == 1 else -value


def _is_zero(term: Any) -> bool:
    """Whether ``term`` is the number zero."""
    return isinstance(term, numbers.Number) and not isinstance(term, bool) and term == 0


# }}}


# {{{ the shape of a fact


@dataclass(frozen=True, eq=False)
class Shape:
    """A fact as Lean applies it: its binders, what each application takes, and its body.

    Attributes:
        binders: ``(variable, domain)`` pairs, in the order Lean takes them.
        premises: What Lean applies the fact to, in order: ``("value",
            name)`` for a binder, and ``("proof", proposition)`` for a guard,
            which the proof discharges.
        body: What the fact says at its point.
    """

    binders: tuple[tuple[Var, Any], ...]
    premises: tuple[tuple[str, Any], ...]
    body: Any

    def at(self, values: Mapping[str, Any]) -> tuple[Any, list[Any]]:
        """The body and the guards at a point, ``values`` keyed by binder name."""
        guards = [substitute(term, values) for kind, term in self.premises if kind == "proof"]
        return substitute(self.body, values), guards


def shape_of(prop: Any) -> Shape:
    """A proposition's shape (:class:`Shape`): nested universals taken apart as Lean prints them.

    Each binder with its domain's guards after it, and a level's own guard
    after its last binder, one premise per conjunct, which is how
    :func:`lanky.lean.print_lean` writes a universal and
    :func:`lanky.induction.lemma_of` reads one.
    """
    binders: list[tuple[Var, Any]] = []
    premises: list[tuple[str, Any]] = []
    node = prop
    while isinstance(node, Forall):
        for var, domain in node.binders:
            binders.append((var, domain))
            premises.append(("value", var.name))
            premises += [("proof", guard) for guard in domain_conditions(var, domain)]
        premises += [("proof", guard) for guard in conjuncts(node.guard)]
        node = node.body
    return Shape(tuple(binders), tuple(premises), node)


# }}}


# {{{ cases: what a path's conditions decide


#: Each comparison and the one its negation is.
_NEGATION = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}


def negated(prop: Any) -> Any:
    """The negation of a proposition, a comparison flipped: ``a >= 2`` for ``a < 2``."""
    if isinstance(prop, prim.Comparison) and prop.operator in _NEGATION:
        return Comparison(prop.left, _NEGATION[prop.operator], prop.right)
    if isinstance(prop, prim.LogicalNot):
        return prop.child
    return LogicalNot(prop)


def integer_sort(sort: Any) -> bool:
    """Whether a variable of this sort is an integer: ``Nat``, ``Int`` or a point of ``Fin``."""
    while isinstance(sort, Refined):
        sort = sort.base
    return isinstance(sort, FinType) or (isinstance(sort, Sort) and sort.name in ("Nat", "Int"))


def _natural(sort: Any) -> bool:
    """Whether a variable of this sort is at least ``0``: ``Nat`` or a point of ``Fin``."""
    while isinstance(sort, Refined):
        sort = sort.base
    return isinstance(sort, FinType) or (isinstance(sort, Sort) and sort.name == "Nat")


def _families(types: Mapping[str, Any]) -> frozenset[str]:
    """The names among ``types`` that are families."""
    out = set()
    for name, sort in types.items():
        while isinstance(sort, Refined):
            sort = sort.base
        if isinstance(sort, FnType):
            out.add(name)
    return frozenset(out)


def decide(prop: Any, facts: Sequence[Any], types: Mapping[str, Any]) -> bool | None:
    """Whether ``facts`` and the variables' bounds decide ``prop``: ``True``, ``False``, ``None``.

    A proposition is decided by the facts as they are written, its negation
    among them deciding it ``False``, and else by lanky's induction search,
    which reads a guard as an affine inequality over the variables' bounds
    (a natural is at least ``0``, a point of ``Fin[n]`` at most ``n - 1``)
    and the facts (:func:`lanky.induction._implied`), where sympy imports.
    ``None`` when neither shows it either way.
    """
    key = render(prop)
    shown = {render(fact) for fact in facts}
    if key in shown:
        return True
    if render(negated(prop)) in shown:
        return False
    try:
        import sympy  # noqa: F401 - only to know whether the search can run
    except ImportError:
        return None
    from lanky.induction import Case, _Algebra, _bounds, _implied, _known, _sympy

    bounds: dict[str, tuple[Any, Any]] = {}
    for name, sort in types.items():
        base = sort
        while isinstance(base, Refined):
            base = base.base
        if isinstance(base, FinType):
            bounds[name] = (0, base.bound - 1)
        elif _natural(base):
            bounds[name] = (0, None)
    variables = {name: sort for name, sort in types.items()}
    case = Case(
        name="case",
        goal=prop,
        lemmas=(),
        variables=variables,
        bounds=bounds,
        families=_families(types),
        facts=tuple(facts),
    )
    algebra = _Algebra(_sympy(), case)
    try:
        symbol_bounds = _bounds(algebra, case)
        known = _known(algebra, _sharpened(facts, types))
        if _implied(algebra, prop, {}, symbol_bounds, known):
            return True
        if _implied(algebra, negated(prop), {}, symbol_bounds, known):
            return False
    except Exception:  # noqa: BLE001 - a condition the search cannot read is not decided
        return None
    return None


def _sharpened(facts: Sequence[Any], types: Mapping[str, Any]) -> list[Any]:
    """The facts, with ``x != 0`` of a sum of naturals read as ``x >= 1``, which the search reads.

    The search reads an inequality and an equation as affine facts, and not a
    disequation; ``a + b != 0`` among naturals is ``a + b >= 1``, which it does.
    """
    out = []
    for fact in facts:
        out.append(fact)
        if not (isinstance(fact, prim.Comparison) and fact.operator == "!="):
            continue
        left, right = affine(fact.left), affine(fact.right)
        if left is None or right is None:
            continue
        form: dict[str | None, Fraction] = {}
        _accumulate(form, left, Fraction(1))
        _accumulate(form, right, Fraction(-1))
        if form.get(None) or not form:
            continue
        signs = {value > 0 for value in form.values()}
        if len(signs) == 1 and all(
            name is not None and name in types and _natural(types[name]) for name in form
        ):
            positive = signs.pop()
            total = from_affine(form)
            out.append(Comparison(total, ">=", 1) if positive else Comparison(total, "<=", -1))
    return out


def pins(
    prop: Any, types: Mapping[str, Any], local: Sequence[str] = ()
) -> list[tuple[str, Any]]:
    """The integer variables an equation fixes, with the value each is fixed at.

    ``n == 1`` fixes ``n`` at ``1``, ``2 - k == 0`` fixes ``k`` at ``2``,
    and ``a + b == 0`` among naturals fixes both at ``0``, since naturals
    that sum to nothing are each nothing. Anything else fixes nothing. Only
    an integer variable is fixed, since the proof substitutes it. And ``k ==
    p`` fixes ``k`` at ``p`` when ``k`` is among ``local``, the claim's own
    variables, which are the ones a case may fix at another's value.
    """
    if not (isinstance(prop, prim.Comparison) and prop.operator == "=="):
        return []
    left, right = affine(prop.left), affine(prop.right)
    if left is None or right is None:
        return []
    form: dict[str | None, Fraction] = {}
    _accumulate(form, left, Fraction(1))
    _accumulate(form, right, Fraction(-1))
    names = [name for name in form if name is not None]
    if not names or any(name not in types or not integer_sort(types[name]) for name in names):
        return []
    if len(names) == 1:
        (name,) = names
        coefficient = form[name]
        if coefficient not in (1, -1):
            return []
        value = -form.get(None, Fraction(0)) / coefficient
        if value.denominator != 1:
            return []
        return [(name, int(value))]
    constant = form.get(None, Fraction(0))
    signs = {form[name] > 0 for name in names}
    if constant == 0 and len(signs) == 1 and all(_natural(types[name]) for name in names):
        return [(name, 0) for name in names]
    for name in local:
        if name in form and form[name] in (1, -1):
            rest: dict[str | None, Fraction] = {}
            _accumulate(rest, {key: value for key, value in form.items() if key != name},
                        -1 / form[name])
            if all(value.denominator == 1 for value in rest.values()):
                return [(name, from_affine(rest))]
    return []


# }}}
