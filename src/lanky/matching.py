"""Matching: the point at which a fact left uncalled supports a step.

The design idea. A proof writes a point only where it carries the argument,
``claim(a - 2, b + 2)``, and leaves it out where the step already shows it:
``.equals(-R[a - 2, b + 2], by=recurrence)``. lanky finds the point the same
way a reader does, by lining the fact up with the step. ``recurrence`` says
``R[x + 2, y] == -R[x, y + 2]``; the step is about ``R[a, b]`` and ``R[a - 2,
b + 2]``; solving ``x + 2 = a`` and ``y = b`` gives the point ``(a - 2, b)``,
and the fact there is about exactly the step's two cells.

Three rules line a fact up with a term, and they are the same rules for every
fact, a hypothesis, a theorem or a library fact.

*First order.* A value of the fact binds a subterm of the step of its type:
``log_of_a_power``'s ``log(x ** n)`` against ``log(abs(alpha) ** 2)`` binds
``x`` to ``abs(alpha)`` and ``n`` to ``2``. An integer value (``Nat``,
``Int``, a point of ``Fin``) binds only an integer, a real one a real or an
integer, a complex one any number (:func:`kind_fits`).

*Offsets.* An index of a family is solved, not bound: ``R[x + 2, y]`` against
``R[a, b]`` gives ``x = a - 2``, as an affine equation over the integers,
with an integer solution (:func:`solve_index`).

*Higher order.* A family among the fact's own values, applied to distinct
variables that a sum or a quantifier of the fact binds, binds to a function
of them (:class:`FamilyValue`): ``one_more_term``'s ``sum(f[k] for k in Fin[n
+ 1])`` against ``sum(r ** k for k in Fin[n])`` binds ``f`` to ``k ↦ r ** k``
and ``n`` to ``n - 1``. This is the rule for facts with family parameters,
and loopty's matcher uses it too, for a rewrite whose theorem's family stands
for a product (:func:`higher_order_value`).

Which point. A fact is lined up with every subterm of the step at every
place it could fit: the subterms of its own that apply a family, and each of
its two sides. That gives candidate points (:func:`candidate_points`). A
candidate whose integer conditions do not follow from what the case knows is
dropped (``x >= 0`` where ``x = a - 4`` and the case knows only ``a >= 2``;
:func:`implied`), and of the rest the point is the one at which the fact is
about the step and nothing else: every application of a family in the fact,
at that point, is one the step has, or one side of the fact is a subterm of
the step (:func:`fits`). Two sums are the same up to the names of their
binders (:func:`same`): ``one_more_term``'s ``sum(f[k] for k in Fin[n])`` at
``f = i ↦ i ** 3`` is the step's ``sum(i ** 3 for i in Fin[n])``. Where
several points fit, the ones at which both sides of the fact are the step's
are preferred, so that the link from ``sum(i ** 3 for i in Fin[n + 1])`` to
``sum(i ** 3 for i in Fin[n]) + n ** 3`` takes ``one_more_term`` at ``n``,
not at ``n - 1``, where only its left side is. Exactly one such point is the
answer (:func:`single_point`); none, or more than one, asks the proof to
write the point, naming them.

Nothing here is trusted. A point is printed into the Lean the step compiles
to, and Lean checks the fact there, its conditions and all; a wrong point
costs a failed step and never a wrong proof.
"""

from __future__ import annotations

import itertools
from collections.abc import Iterator, Mapping, Sequence
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import Lemma, substitute, substitute_domain
from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Comparison,
    Exists,
    Forall,
    Sum,
    Var,
    init_args,
    lift,
    render,
    structurally_equal,
)

__all__ = [
    "FamilyValue",
    "NoSinglePoint",
    "candidate_points",
    "family_scope",
    "fits",
    "higher_order_value",
    "implied",
    "instantiate",
    "kind_fits",
    "match",
    "same",
    "same_function",
    "single_point",
    "solve_index",
]

#: The key an affine form keeps its constant under; no variable is named "".
_CONSTANT = ""

#: How many orders of the operands of a sum or a product are tried, at most.
_ORDERS = 24


class NoSinglePoint(LookupError):
    """No point of a fact fits a step, or several do; the message says which and the fix.

    Attributes:
        candidates: The points that fit, or that were tried; each a tuple of
            values, one per binder of the fact.
    """

    def __init__(self, message: str, candidates: Sequence[tuple[Any, ...]] = ()) -> None:
        super().__init__(message)
        self.candidates = tuple(candidates)


# {{{ a family's value, bound by the higher-order rule


@dataclass(frozen=True, eq=False)
class FamilyValue:
    """A family bound to a function of its arguments: ``k ↦ r ** k``.

    What the higher-order rule binds a family of a fact to. Applying it puts
    the arguments for its parameters in its body, which is how a fact at this
    value reads: ``f[n]`` at ``f = k ↦ r ** k`` is ``r ** n``.

    Attributes:
        parameters: The variables of the function, in the order of the
            family's arguments.
        body: The term they give.
    """

    parameters: tuple[Var, ...]
    body: Any

    def apply(self, arguments: Sequence[Any]) -> Any:
        """The body with ``arguments`` for the parameters.

        Raises:
            TypeError: If the number of arguments is not the number of parameters.
        """
        if len(arguments) != len(self.parameters):
            raise TypeError(
                f"{self.shown()} takes {len(self.parameters)} arguments, not {len(arguments)}"
            )
        values = {
            var.name: argument for var, argument in zip(self.parameters, arguments, strict=True)
        }
        return substitute(self.body, values)

    def __getitem__(self, index: Any) -> Any:
        """``f[i]`` and ``f[i, j]``: the body at the index."""
        return self.apply(index if isinstance(index, tuple) else (index,))

    def __call__(self, *arguments: Any) -> Any:
        """``f(i)`` and ``f(i, j)``: the body at the arguments."""
        return self.apply(arguments)

    def shown(self) -> str:
        """``lambda k: r**k``, as a message shows the value."""
        names = ", ".join(var.name for var in self.parameters)
        return f"lambda {names}: {render(self.body)}"

    def __repr__(self) -> str:
        """The value as Python would write it."""
        return f"<family {self.shown()}>"


def higher_order_value(
    arguments: Sequence[Any], target: Any, bound: Mapping[str, str]
) -> FamilyValue | None:
    """The function a family applied to ``arguments`` binds to, at ``target``; or ``None``.

    The higher-order rule: the arguments have to be distinct variables that
    a binder of the pattern binds (``bound`` maps each such pattern variable
    to the target's variable it was lined up with), and the value is the
    target as a function of the target's variables they stand for. A target
    that mentions another of the target's bound variables, one that is no
    argument, would let it escape its binder, and is refused. This is the
    rule loopty's matcher shares (``loopty.hypotheses._Matcher``).
    """
    names: list[str] = []
    for argument in arguments:
        if not isinstance(argument, prim.Variable) or argument.name not in bound:
            return None
        names.append(bound[argument.name])
    if len(set(names)) != len(names):
        return None
    escaping = (set(bound.values()) - set(names)) & _names(target)
    if escaping:
        return None
    return FamilyValue(tuple(Var(name) for name in names), target)


# }}}


# {{{ affine forms over the integers


def _affine(expr: Any) -> dict[str, Fraction] | None:
    """``expr`` as ``{variable: coefficient}`` plus a constant; ``None`` where it is not affine."""
    if isinstance(expr, bool):
        return None
    if isinstance(expr, int | Fraction):
        return {_CONSTANT: Fraction(expr)}
    if isinstance(expr, prim.Variable):
        return {_CONSTANT: Fraction(0), expr.name: Fraction(1)}
    if isinstance(expr, prim.Sum):
        total: dict[str, Fraction] = {_CONSTANT: Fraction(0)}
        for child in expr.children:
            part = _affine(child)
            if part is None:
                return None
            for name, value in part.items():
                total[name] = total.get(name, Fraction(0)) + value
        return total
    if isinstance(expr, prim.Product):
        total = {_CONSTANT: Fraction(1)}
        for child in expr.children:
            part = _affine(child)
            if part is None:
                return None
            if _constant_only(total):
                total = {name: value * total[_CONSTANT] for name, value in part.items()}
            elif _constant_only(part):
                total = {name: value * part[_CONSTANT] for name, value in total.items()}
            else:
                return None
        return total
    return None


def _constant_only(form: Mapping[str, Fraction]) -> bool:
    """Whether every variable of the form has the coefficient ``0``."""
    return all(value == 0 for name, value in form.items() if name != _CONSTANT)


def _clean(form: Mapping[str, Fraction]) -> dict[str, Fraction]:
    """The form without its zero coefficients, the constant kept."""
    out = {name: value for name, value in form.items() if value != 0 and name != _CONSTANT}
    out[_CONSTANT] = form.get(_CONSTANT, Fraction(0))
    return out


def _term(form: Mapping[str, Fraction]) -> Any:
    """An affine form as the lanky term a reader writes: ``a - 2``, ``2*i + 1``, ``b``.

    The variables in sorted order, the constant last, so ``x = a - 2`` reads
    as the subtraction it is.
    """
    parts: list[Any] = []
    for name in sorted(name for name in form if name != _CONSTANT):
        coefficient = form[name]
        if coefficient == 0:
            continue
        number = int(coefficient) if coefficient.denominator == 1 else coefficient
        parts.append(Var(name) if number == 1 else number * Var(name))
    constant = form.get(_CONSTANT, Fraction(0))
    if constant != 0 or not parts:
        parts.append(int(constant) if constant.denominator == 1 else constant)
    term = parts[0]
    for part in parts[1:]:
        term = term + part
    return term


def solve_index(
    pattern: Any, target: Any, unknowns: Mapping[str, Any], sigma: Mapping[str, Any]
) -> dict[str, Any] | None:
    """The values of ``unknowns`` that make the index ``pattern`` the index ``target``.

    ``sigma`` holds values found already. The pattern is affine in the
    unknowns, with integer coefficients; after the known ones are put in, one
    unknown is left at most, with the coefficient ``1`` or ``-1``, and its
    value is the target less the rest, an integer term. With none left the
    two have to be equal, as affine forms (``a - 2 + 2`` is ``a``) or as
    terms. ``None`` where the pattern is not affine, two unknowns are left,
    or the two cannot be equal.
    """
    known = {name: value for name, value in sigma.items() if name in unknowns}
    pattern = substitute(pattern, known)
    form = _affine(pattern)
    if form is None:
        return dict(sigma) if same(pattern, target) else None
    left = [name for name in form if name != _CONSTANT and name in unknowns and form[name] != 0]
    if not left:
        return dict(sigma) if same(pattern, target) else None
    if len(left) > 1:
        return None
    (name,) = left
    coefficient = form[name]
    if coefficient not in (1, -1):
        return None
    rest = {key: value for key, value in form.items() if key != name}
    target_form = _affine(target)
    if target_form is None:
        # x + c = T for a T that is no affine form: x = T - c, as a term
        if coefficient != 1:
            return None
        value = target - _term(rest) if not _zero(rest) else target
        return {**sigma, name: lift(value) if isinstance(value, prim.ExpressionNode) else value}
    difference = dict(target_form)
    for key, value in rest.items():
        difference[key] = difference.get(key, Fraction(0)) - value
    if coefficient == -1:
        difference = {key: -value for key, value in difference.items()}
    if any(value.denominator != 1 for value in difference.values()):
        return None
    return {**sigma, name: _term(_clean(difference))}


def _zero(form: Mapping[str, Fraction]) -> bool:
    """Whether a form is ``0``."""
    return all(value == 0 for value in form.values())


def same(left: Any, right: Any) -> bool:
    """Whether two terms are the same: as trees, or as affine forms, or applied at such indices.

    ``R[a - 2 + 2, b]`` is ``R[a, b]``, and ``a - 2 + 2`` is ``a``: an index
    the instance of a fact computes is compared as the integer it is.
    """
    if structurally_equal(left, right):
        return True
    first, second = _affine(left), _affine(right)
    if first is not None and second is not None:
        return _clean(first) == _clean(second)
    spine_left, spine_right = _spine(left), _spine(right)
    if spine_left is not None and spine_right is not None:
        (head, arguments), (other, values) = spine_left, spine_right
        return (
            head == other
            and len(arguments) == len(values)
            and all(same(a, b) for a, b in zip(arguments, values, strict=True))
        )
    if isinstance(left, Forall | Exists | Sum) or isinstance(right, Forall | Exists | Sum):
        return type(left) is type(right) and _same_binding(left, right)
    if isinstance(left, prim.ExpressionNode) and isinstance(right, prim.ExpressionNode):
        if left.mapper_method != right.mapper_method:
            return False
        first_args, second_args = init_args(left), init_args(right)
        return _same_parts(first_args, second_args)
    return False


def _same_binding(left: Forall | Exists | Sum, right: Forall | Exists | Sum) -> bool:
    """Whether two sums, or two quantifiers, are the same up to the names of their binders.

    ``sum(k**3 for k in Fin(n + 1))`` is ``sum(i**3 for i in Fin(n + 1))``: a
    binder's name is the reader's choice, and a fact stated with ``k`` is
    about the step's sum written with ``i``. Binder by binder, the domains
    have to be the same, a ``Fin``'s bound as the integer it is; then the
    bodies and the guards, each binder of the two read as one fresh name
    that neither term mentions, so that no name is captured.
    """
    if len(left.binders) != len(right.binders):
        return False
    if (left.guard is None) != (right.guard is None):
        return False
    taken = _names(left) | _names(right)
    mine: dict[str, Any] = {}
    theirs: dict[str, Any] = {}
    for (var, domain), (other, other_domain) in zip(left.binders, right.binders, strict=True):
        if not _same_domain(
            substitute_domain(domain, mine), substitute_domain(other_domain, theirs)
        ):
            return False
        fresh = _fresh(var.name, taken)
        taken.add(fresh)
        mine[var.name] = Var(fresh)
        theirs[other.name] = Var(fresh)
    if not same(substitute(left.body, mine), substitute(right.body, theirs)):
        return False
    if left.guard is None:
        return True
    return same(substitute(left.guard, mine), substitute(right.guard, theirs))


def _same_domain(left: Any, right: Any) -> bool:
    """Whether two binders' domains are the same: a ``Fin``'s bound as the integer it is."""
    if isinstance(left, FinType) or isinstance(right, FinType):
        return (
            isinstance(left, FinType)
            and isinstance(right, FinType)
            and same(left.bound, right.bound)
        )
    if isinstance(left, Refined) or isinstance(right, Refined):
        return (
            isinstance(left, Refined)
            and isinstance(right, Refined)
            and _same_domain(left.base, right.base)
            and len(left.props) == len(right.props)
            and all(same(a, b) for a, b in zip(left.props, right.props, strict=True))
        )
    return str(left) == str(right)


def _fresh(stem: str, taken: set[str]) -> str:
    """A name like ``stem`` that is not in ``taken``."""
    index = 0
    while True:
        name = f"_{stem}_{index}"
        if name not in taken:
            return name
        index += 1


def same_function(left: FamilyValue, right: FamilyValue) -> bool:
    """Whether two values of a family are the same function: ``k ↦ k**3`` is ``i ↦ i**3``.

    Their parameters are names the matcher took from the terms it lined up,
    so two matches of one fact can name them differently; each is applied
    to the same fresh variables, and the bodies compared.
    """
    if len(left.parameters) != len(right.parameters):
        return False
    taken = _names(left.body) | _names(right.body)
    taken |= {var.name for var in (*left.parameters, *right.parameters)}
    arguments = []
    for var in left.parameters:
        fresh = _fresh(var.name, taken)
        taken.add(fresh)
        arguments.append(Var(fresh))
    return same(left.apply(arguments), right.apply(arguments))


def _same_parts(left: Any, right: Any) -> bool:
    """:func:`same`, for the constructor arguments of two nodes of one kind."""
    if isinstance(left, tuple) and isinstance(right, tuple):
        return len(left) == len(right) and all(
            _same_parts(a, b) for a, b in zip(left, right, strict=True)
        )
    if isinstance(left, prim.ExpressionNode) or isinstance(right, prim.ExpressionNode):
        return same(left, right)
    return structurally_equal(left, right)


# }}}


# {{{ the rules


def _spine(expr: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family, arguments)`` of an application, ``R(a)(b)`` and ``R[a, b]`` alike."""
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


def _names(expr: Any) -> set[str]:
    """Every variable name a term mentions, bound ones included."""
    found: set[str] = set()
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Variable):
            found.add(node.name)
        elif isinstance(node, Forall | Exists | Sum):
            for var, domain in node.binders:
                found.add(var.name)
                stack.append(getattr(domain, "bound", None))
            stack.extend((node.body, node.guard))
        elif isinstance(node, prim.ExpressionNode):
            stack.extend(init_args(node))
        elif isinstance(node, tuple | list):
            stack.extend(node)
    return found


def _base_sort(sort: Any) -> Any:
    """A sort with its refinements taken off."""
    while isinstance(sort, Refined):
        sort = sort.base
    return sort


def _integer_sort(sort: Any) -> bool:
    """Whether a value of the sort is an integer: ``Nat``, ``Int`` or a point of ``Fin``."""
    base = _base_sort(sort)
    return isinstance(base, FinType) or (isinstance(base, Sort) and base.name in ("Nat", "Int"))


def kind_fits(sort: Any, term: Any, types: Mapping[str, Any]) -> bool:
    """Whether ``term`` may be the value of a fact's variable of ``sort``.

    An integer variable takes an integer, a real one a real number or an
    integer, a complex one any number. A family takes a family of the scope,
    by its name, or a function the higher-order rule bound, whose values
    have to fit the family's as a number does: a family of reals takes
    ``i ↦ i**3`` over the integers, which Lean reads through the cast into
    the reals, and not ``k ↦ z**k`` over the complex numbers. A sort this
    cannot read takes anything, and Lean judges.
    """
    from lanky.lean import number_type

    base = _base_sort(sort)
    if isinstance(base, FnType):
        if isinstance(term, FamilyValue):
            inner, codomain = family_scope(base, term, types)
            return kind_fits(codomain, term.body, inner)
        return isinstance(term, prim.Variable)
    if isinstance(term, FamilyValue) or isinstance(term, bool):
        return False
    try:
        kind = number_type(term, types, mathlib=True)
    except Exception:  # noqa: BLE001 - a term the printer cannot read is Lean's to judge
        return True
    if _integer_sort(sort):
        return kind not in ("ℝ", "ℂ")
    if isinstance(base, Sort) and base.name == "Real":
        return kind != "ℂ"
    return True


def family_scope(
    sort: Any, value: FamilyValue, types: Mapping[str, Any]
) -> tuple[dict[str, Any], Any]:
    """The scope a family's value is read in, and the sort of what it gives.

    Each parameter of the value has the type of the family's argument in its
    place, so that ``i ↦ i**3`` for an ``f: Fn[Nat, Real]`` reads ``i`` as a
    natural; the second is the family's codomain, ``Real`` there.
    """
    inner = dict(types)
    current = _base_sort(sort)
    for var in value.parameters:
        if not isinstance(current, FnType):
            break
        inner[var.name] = current.domain
        current = _base_sort(current.codomain)
    return inner, current


def match(
    pattern: Any,
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str] | None = None,
    local: frozenset[str] = frozenset(),
) -> Iterator[dict[str, Any]]:
    """Every way ``pattern`` is ``target`` with values for ``unknowns``, extending ``sigma``.

    ``unknowns`` maps each variable of the fact to its sort, ``types`` the
    names of the scope to theirs. ``bound`` maps a variable a binder of the
    pattern binds to the target's variable lined up with it, and ``local``
    holds the target's variables bound around ``target``: a value never
    mentions one of those, which would take it out of its binder.

    A sum or a product is matched operand by operand, in each order of its
    operands up to :data:`_ORDERS`; an equation either way round.
    """
    bound = bound or {}
    if isinstance(pattern, prim.Variable) and pattern.name in bound:
        if isinstance(target, prim.Variable) and target.name == bound[pattern.name]:
            yield dict(sigma)
        return
    if isinstance(pattern, prim.Variable) and pattern.name in unknowns:
        yield from _bind(pattern.name, target, unknowns, sigma, types, local)
        return
    spine = _spine(pattern)
    if spine is not None:
        yield from _match_application(spine, target, unknowns, sigma, types, bound, local)
        return
    if isinstance(pattern, prim.Comparison):
        if not isinstance(target, prim.Comparison):
            return
        if pattern.operator == target.operator:
            for found in match(pattern.left, target.left, unknowns, sigma, types, bound, local):
                yield from match(pattern.right, target.right, unknowns, found, types, bound, local)
        mirrored = _MIRRORED.get(pattern.operator)
        if mirrored == target.operator:
            for found in match(pattern.left, target.right, unknowns, sigma, types, bound, local):
                yield from match(pattern.right, target.left, unknowns, found, types, bound, local)
        return
    if isinstance(pattern, Forall | Exists | Sum):
        yield from _match_binding(pattern, target, unknowns, sigma, types, bound, local)
        return
    if isinstance(pattern, prim.Sum | prim.Product):
        yield from _match_operands(pattern, target, unknowns, sigma, types, bound, local)
        return
    if isinstance(pattern, prim.ExpressionNode):
        if not isinstance(target, prim.ExpressionNode) or pattern.mapper_method != (
            target.mapper_method
        ):
            return
        yield from _match_sequence(
            init_args(pattern), init_args(target), unknowns, sigma, types, bound, local
        )
        return
    if isinstance(pattern, tuple):
        if isinstance(target, tuple) and len(target) == len(pattern):
            yield from _match_sequence(pattern, target, unknowns, sigma, types, bound, local)
        return
    if _free_of(pattern, unknowns) and same(substitute(pattern, {}), target):
        yield dict(sigma)


#: The comparison an operator reads as with its sides swapped.
_MIRRORED = {"==": "==", "!=": "!=", "<": ">", "<=": ">=", ">": "<", ">=": "<="}


def _free_of(pattern: Any, unknowns: Mapping[str, Any]) -> bool:
    """Whether the pattern mentions none of the unknowns."""
    return not (_names(pattern) & set(unknowns))


def _bind(
    name: str,
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """The unknown ``name`` bound to ``target``, or checked against its value."""
    if name in sigma:
        value = sigma[name]
        if isinstance(value, FamilyValue):
            return
        if same(value, target):
            yield dict(sigma)
        return
    if _names(target) & local:
        return
    if not kind_fits(unknowns[name], target, types):
        return
    yield {**sigma, name: target}


def _match_application(
    spine: tuple[str, tuple[Any, ...]],
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """A family applied, against a target: by its value, by name, or by the higher-order rule.

    A family of the fact bound already is applied, and has to give the
    target. One still unbound is bound to a family of the scope where the
    target applies one at matching indices, and to a function of the
    arguments by the higher-order rule only where it does not: ``f[k]``
    against ``x[k]`` binds ``f`` to ``x``, not to ``k ↦ x[k]``.
    """
    head, arguments = spine
    renaming = {key: Var(item) for key, item in bound.items()}
    if head in unknowns:
        value = sigma.get(head)
        if isinstance(value, FamilyValue):
            plain = {key: item for key, item in sigma.items() if not isinstance(item, FamilyValue)}
            values = [substitute(substitute(argument, renaming), plain) for argument in arguments]
            if same(value.apply(values), target):
                yield dict(sigma)
            return
        matched = False
        target_spine = _spine(target)
        if target_spine is not None:
            name, values = target_spine
            fits_value = value is None or (isinstance(value, prim.Variable) and value.name == name)
            if fits_value and len(values) == len(arguments) and name not in local:
                extended = {**sigma, head: Var(name)}
                for found in _match_indices(
                    arguments, values, unknowns, extended, types, bound, local
                ):
                    matched = True
                    yield found
        if not matched and value is None:
            function = higher_order_value(arguments, target, bound)
            if function is not None:
                yield {**sigma, head: function}
        return
    target_spine = _spine(target)
    if target_spine is None or target_spine[0] != head or len(target_spine[1]) != len(arguments):
        return
    yield from _match_indices(arguments, target_spine[1], unknowns, sigma, types, bound, local)


def _match_indices(
    arguments: Sequence[Any],
    values: Sequence[Any],
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """The indices of a family, each solved as an offset where it is affine.

    An index that is a bare unknown or a variable a pattern binder binds is
    matched as a term; any other is solved (:func:`solve_index`), the
    pattern's bound variables read as the target's. An index the solve
    leaves with two unknowns is tried again once the others are known.
    """
    states: list[dict[str, Any]] = [dict(sigma)]
    pending = list(zip(arguments, values, strict=True))
    for _ in range(len(pending) + 1):
        if not pending:
            break
        later: list[tuple[Any, Any]] = []
        next_states: list[dict[str, Any]] = []
        for state in states:
            current = [state]
            deferred: list[tuple[Any, Any]] = []
            for argument, value in pending:
                argument = substitute(argument, {key: Var(item) for key, item in bound.items()})
                widened: list[dict[str, Any]] = []
                for each in current:
                    if isinstance(argument, prim.Variable) and argument.name in unknowns:
                        widened.extend(_bind(argument.name, value, unknowns, each, types, local))
                        continue
                    solved = solve_index(argument, value, unknowns, each)
                    if solved is None:
                        if _unknowns_left(argument, unknowns, each) > 1:
                            widened.append(each)
                            deferred.append((argument, value))
                        continue
                    if any(_names(solved[key]) & local for key in solved if key not in each):
                        continue
                    widened.append(solved)
                current = widened
            next_states.extend(current)
            later = deferred
        states = next_states
        pending = later
    if pending:
        return
    seen: list[dict[str, Any]] = []
    for state in states:
        if not any(_same_sigma(state, other) for other in seen):
            seen.append(state)
            yield state


def _unknowns_left(argument: Any, unknowns: Mapping[str, Any], sigma: Mapping[str, Any]) -> int:
    """How many unknowns an index has that ``sigma`` gives no value."""
    return len((_names(argument) & set(unknowns)) - set(sigma))


def _same_sigma(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
    """Whether two assignments give the same values."""
    if set(left) != set(right):
        return False
    for key, value in left.items():
        other = right[key]
        if isinstance(value, FamilyValue) or isinstance(other, FamilyValue):
            # a value's parameters are lanky variables, whose == builds a
            # proposition: two functions are compared as functions
            if not (
                isinstance(value, FamilyValue)
                and isinstance(other, FamilyValue)
                and same_function(value, other)
            ):
                return False
        elif not same(value, other):
            return False
    return True


def _match_sequence(
    patterns: Sequence[Any],
    targets: Sequence[Any],
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """Each pattern against the target in its place, in order."""
    if not patterns:
        yield dict(sigma)
        return
    for found in match(patterns[0], targets[0], unknowns, sigma, types, bound, local):
        yield from _match_sequence(patterns[1:], targets[1:], unknowns, found, types, bound, local)


def _match_operands(
    pattern: Any,
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """A sum or a product against one of the same kind and length, in each order of its operands."""
    kind = prim.Sum if isinstance(pattern, prim.Sum) else prim.Product
    if not isinstance(target, kind) or len(target.children) != len(pattern.children):
        return
    for count, order in enumerate(itertools.permutations(target.children)):
        if count >= _ORDERS:
            return
        yield from _match_sequence(pattern.children, order, unknowns, sigma, types, bound, local)


def _match_binding(
    pattern: Forall | Exists | Sum,
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """A quantifier or a sum against one of the same kind, binder by binder.

    Each binder's domain is matched first, a ``Fin``'s bound solved as an
    index, and then the body and the guard, with the pattern's binder read
    as the target's and the target's binder local, so no value takes it out
    of its binder.
    """
    if type(pattern) is not type(target) or len(pattern.binders) != len(target.binders):
        return
    states: list[dict[str, Any]] = [dict(sigma)]
    inner = dict(bound)
    inner_local = set(local)
    for (pattern_var, pattern_domain), (target_var, target_domain) in zip(
        pattern.binders, target.binders, strict=True
    ):
        widened: list[dict[str, Any]] = []
        for state in states:
            widened.extend(
                _match_domain(
                    pattern_domain,
                    target_domain,
                    unknowns,
                    state,
                    types,
                    inner,
                    frozenset(inner_local),
                )
            )
        states = widened
        inner[pattern_var.name] = target_var.name
        inner_local.add(target_var.name)
    inner_types = dict(types)
    for var, domain in target.binders:
        inner_types[var.name] = domain
    if (pattern.guard is None) != (target.guard is None):
        return
    for state in states:
        for found in match(
            pattern.body, target.body, unknowns, state, inner_types, inner, frozenset(inner_local)
        ):
            if pattern.guard is None:
                yield found
                continue
            yield from match(
                pattern.guard,
                target.guard,
                unknowns,
                found,
                inner_types,
                inner,
                frozenset(inner_local),
            )


def _match_domain(
    pattern: Any,
    target: Any,
    unknowns: Mapping[str, Any],
    sigma: Mapping[str, Any],
    types: Mapping[str, Any],
    bound: Mapping[str, str],
    local: frozenset[str],
) -> Iterator[dict[str, Any]]:
    """A binder's domain against the target's: a ``Fin``'s bound solved as an index."""
    if isinstance(pattern, FinType):
        if not isinstance(target, FinType):
            return
        argument = substitute(pattern.bound, {key: Var(item) for key, item in bound.items()})
        if isinstance(argument, prim.Variable) and argument.name in unknowns:
            yield from _bind(argument.name, target.bound, unknowns, sigma, types, local)
            return
        solved = solve_index(argument, target.bound, unknowns, sigma)
        if solved is not None:
            yield solved
        return
    if isinstance(pattern, Refined):
        if not isinstance(target, Refined) or len(pattern.props) != len(target.props):
            return
        for state in _match_domain(pattern.base, target.base, unknowns, sigma, types, bound, local):
            yield from _match_sequence(
                pattern.props, target.props, unknowns, state, types, bound, local
            )
        return
    if str(pattern) == str(target):
        yield dict(sigma)


# }}}


# {{{ a fact at a point


def instantiate(term: Any, values: Mapping[str, Any]) -> Any:
    """``term`` with each variable ``values`` names put in, a family's value applied.

    As :func:`lanky.induction.substitute`, but a family bound to a function
    (:class:`FamilyValue`) is applied where the term applies it: ``f[n]`` at
    ``f = k ↦ r ** k`` is ``r ** n``.
    """
    families = {name: value for name, value in values.items() if isinstance(value, FamilyValue)}
    plain = {name: value for name, value in values.items() if name not in families}
    if not families:
        return substitute(term, plain)
    return _apply_families(substitute(term, plain), families)


def _apply_families(term: Any, families: Mapping[str, FamilyValue]) -> Any:
    """``term`` with every application of a family in ``families`` replaced by its value there."""
    spine = _spine(term)
    if spine is not None and spine[0] in families:
        arguments = tuple(_apply_families(argument, families) for argument in spine[1])
        return families[spine[0]].apply(arguments)
    if isinstance(term, Forall | Exists | Sum):
        inner = {name: value for name, value in families.items()}
        for var, _ in term.binders:
            inner.pop(var.name, None)
        binders = tuple((var, substitute_domain(domain, {})) for var, domain in term.binders)
        guard = None if term.guard is None else _apply_families(term.guard, inner)
        return type(term)(binders, _apply_families(term.body, inner), guard)
    if isinstance(term, prim.ExpressionNode):
        return type(term)(*(_apply_families(argument, families) for argument in init_args(term)))
    if isinstance(term, tuple):
        return tuple(_apply_families(item, families) for item in term)
    return term


def _applications(term: Any, families: Mapping[str, Any]) -> list[Any]:
    """The applications in ``term`` of the families ``families`` names, outermost first."""
    found: list[Any] = []
    stack = [term]
    while stack:
        node = stack.pop()
        spine = _spine(node)
        if spine is not None and spine[0] in families:
            found.append(node)
            stack.extend(spine[1])
            continue
        if isinstance(node, Forall | Exists | Sum):
            stack.extend((node.body, node.guard))
        elif isinstance(node, prim.ExpressionNode):
            stack.extend(init_args(node))
        elif isinstance(node, tuple):
            stack.extend(node)
    return found


def _subterms(
    term: Any, local: frozenset[str] = frozenset()
) -> Iterator[tuple[Any, frozenset[str]]]:
    """Every subterm of ``term``, with the variables bound around it."""
    yield term, local
    if isinstance(term, Forall | Exists | Sum):
        inner = local | {var.name for var, _ in term.binders}
        for part in (term.body, term.guard):
            if part is not None:
                yield from _subterms(part, frozenset(inner))
        return
    if isinstance(term, prim.ExpressionNode):
        for argument in init_args(term):
            if isinstance(argument, tuple):
                for item in argument:
                    yield from _subterms(item, local)
            elif isinstance(argument, prim.ExpressionNode):
                yield from _subterms(argument, local)


def _families(types: Mapping[str, Any]) -> dict[str, Any]:
    """The names of ``types`` that are families."""
    return {name: sort for name, sort in types.items() if isinstance(_base_sort(sort), FnType)}


def _patterns(lemma: Lemma, types: Mapping[str, Any]) -> list[Any]:
    """What of a fact is lined up with a step: its family applications, then its sides."""
    unknowns = {var.name for var, _ in lemma.binders}
    families = {**_families(types), **_families(dict((v.name, d) for v, d in lemma.binders))}
    out: list[Any] = []
    for application in _applications(lemma.equation, families):
        if _names(application) & unknowns:
            out.append(application)
    for side in (lemma.equation.left, lemma.equation.right):
        if isinstance(side, prim.ExpressionNode) and _names(side) & unknowns:
            if not isinstance(side, prim.Variable):
                out.append(side)
    return out


def candidate_points(
    lemma: Lemma, terms: Sequence[Any], types: Mapping[str, Any]
) -> list[tuple[Any, ...]]:
    """The points of ``lemma`` at which some part of it is a subterm of ``terms``.

    Each part a fact is lined up by (:func:`_patterns`) is matched against
    each subterm of each term; the values it fixes are joined with those
    another part fixes where one part leaves some open. A point gives every
    binder of the lemma a value, in the lemma's order. Sorted, so the same
    step gives the same points every time.
    """
    unknowns = {var.name: domain for var, domain in lemma.binders}
    if not unknowns:
        return [()]
    partial: list[dict[str, Any]] = []
    for pattern in _patterns(lemma, types):
        for subterm, local in _subterms_of(terms):
            for found in match(pattern, subterm, unknowns, {}, types, None, local):
                if found and not any(_same_sigma(found, other) for other in partial):
                    partial.append(found)
    complete: list[dict[str, Any]] = []
    for found in partial:
        _complete(found, partial, unknowns, complete)
    points = [tuple(found[var.name] for var, _ in lemma.binders) for found in complete]
    return sorted(points, key=lambda point: tuple(_key(value) for value in point))


def _subterms_of(terms: Sequence[Any]) -> Iterator[tuple[Any, frozenset[str]]]:
    """Every subterm of every term, with the variables bound around it."""
    for term in terms:
        yield from _subterms(term)


def _complete(
    found: dict[str, Any],
    partial: list[dict[str, Any]],
    unknowns: Mapping[str, Any],
    out: list[dict[str, Any]],
    depth: int = 0,
) -> None:
    """Join ``found`` with the other partial assignments until every unknown has a value."""
    if set(found) >= set(unknowns):
        if not any(_same_sigma(found, other) for other in out):
            out.append(found)
        return
    if depth > len(unknowns):
        return
    for other in partial:
        if set(other) <= set(found):
            continue
        if all(
            _same_sigma({key: found[key]}, {key: other[key]}) for key in set(found) & set(other)
        ):
            _complete({**found, **other}, partial, unknowns, out, depth + 1)


def _key(value: Any) -> str:
    """A value as text, to sort points by."""
    if isinstance(value, FamilyValue):
        return value.shown()
    if isinstance(value, prim.ExpressionNode):
        return render(value)
    return repr(value)


def fits(
    lemma: Lemma, point: tuple[Any, ...], terms: Sequence[Any], types: Mapping[str, Any]
) -> bool:
    """Whether the fact at ``point`` is about the step's terms and nothing else.

    Every application of a family of the scope in the fact, at the point, is
    one of the step's (``R[a - 2 + 2, b]`` is ``R[a, b]``); for a fact that
    applies none, one of its sides at the point is a subterm of the step.
    """
    values = dict(zip((var.name for var, _ in lemma.binders), point, strict=True))
    instance = instantiate(lemma.equation, values)
    families = _families(types)
    present = [subterm for subterm, _ in _subterms_of(terms)]
    applications = _applications(instance, families)
    if applications:
        return all(any(same(found, other) for other in present) for found in applications)
    return any(
        any(same(side, other) for other in present)
        for side in (instance.left, instance.right)
        if isinstance(side, prim.ExpressionNode)
    )


def _both_sides(
    lemma: Lemma, point: tuple[Any, ...], terms: Sequence[Any]
) -> bool:
    """Whether both sides of the fact at ``point`` are terms of the step.

    A side that is a number, the ``0`` of ``D[a + 2, b] + D[a, b + 2] == 0``,
    is no term of the step to look for, and counts as one.
    """
    values = dict(zip((var.name for var, _ in lemma.binders), point, strict=True))
    instance = instantiate(lemma.equation, values)
    if not isinstance(instance, prim.Comparison):
        return False
    present = [subterm for subterm, _ in _subterms_of(terms)]
    return all(
        not isinstance(side, prim.ExpressionNode) or any(same(side, other) for other in present)
        for side in (instance.left, instance.right)
    )


def single_point(
    lemma: Lemma,
    terms: Sequence[Any],
    types: Mapping[str, Any],
    facts: Sequence[Any] = (),
    name: str = "the fact",
) -> tuple[Any, ...]:
    """The one point at which a fact left uncalled supports a step (see the module docstring).

    ``facts`` are what the case knows, propositions over the scope's names,
    which with the bounds the types give are what a candidate's integer
    conditions have to follow from (:func:`implied`).

    Raises:
        NoSinglePoint: If no candidate fits, or several do, naming the fix:
            write the point, as ``by=pde(a - 2, b)``.
    """
    candidates = candidate_points(lemma, terms, types)
    fitting = [point for point in candidates if fits(lemma, point, terms, types)]
    if len(fitting) > 1:
        # several fit: the ones whose conditions do not follow from the case go
        shown_ones = [
            point for point in fitting if _conditions(lemma, point, facts, types) is not False
        ]
        fitting = shown_ones or fitting
    if len(fitting) > 1:
        # still several: the step is the fact itself at the point where both
        # of its sides are the step's, as one_more_term at n is for the link
        # from sum(i**3 for i in Fin(n + 1)) to sum(i**3 for i in Fin(n)) + n**3,
        # where at n - 1 only its left side is
        whole = [point for point in fitting if _both_sides(lemma, point, terms)]
        fitting = whole or fitting
    if len(fitting) == 1:
        return fitting[0]
    shown = [f"({', '.join(_key(value) for value in point)})" for point in fitting or candidates]
    arguments = ", ".join(var.name for var, _ in lemma.binders)
    if not fitting:
        tried = f"; the points tried were {', '.join(shown[:4])}" if shown else ""
        raise NoSinglePoint(
            f"no single point of {name} fits this step{tried}; write it, as "
            f"by={name}({arguments}) with the values meant",
            candidates,
        )
    raise NoSinglePoint(
        f"{name} fits this step at {len(fitting)} points, {', '.join(shown)}; write the "
        f"one meant, as by={name}{shown[0]}",
        fitting,
    )


def _conditions(
    lemma: Lemma, point: tuple[Any, ...], facts: Sequence[Any], types: Mapping[str, Any]
) -> bool | None:
    """Whether the fact's conditions at ``point`` follow from the case: ``None`` if unread."""
    values = dict(zip((var.name for var, _ in lemma.binders), point, strict=True))
    answers = [implied(instantiate(guard, values), facts, types) for guard in lemma.guards]
    if any(answer is False for answer in answers):
        return False
    return True if all(answers) else None


# }}}


# {{{ what the case knows, read as integer arithmetic


def _bounds(types: Mapping[str, Any]) -> list[dict[str, Fraction]]:
    """The bounds the types give, each an affine form that is at least ``0``."""
    out: list[dict[str, Fraction]] = []
    for name, sort in types.items():
        base = _base_sort(sort)
        if isinstance(base, Sort) and base.name == "Nat":
            out.append({_CONSTANT: Fraction(0), name: Fraction(1)})
        elif isinstance(base, FinType):
            out.append({_CONSTANT: Fraction(0), name: Fraction(1)})
            bound = _affine(base.bound)
            if bound is not None:
                upper = {key: value for key, value in bound.items()}
                upper[name] = upper.get(name, Fraction(0)) - 1
                upper[_CONSTANT] = upper.get(_CONSTANT, Fraction(0)) - 1
                out.append(upper)
        if isinstance(sort, Refined):
            for prop in sort.props:
                out.extend(_nonnegative(prop, name))
    return out


def _nonnegative(prop: Any, name: str | None = None) -> list[dict[str, Fraction]]:
    """A proposition as affine forms that are at least ``0`` where it holds, if it is one.

    ``a >= 2`` is ``a - 2``; ``a < 2`` between integers is ``1 - a``; an
    equation gives two; a negated comparison is the comparison the other
    way. Anything else gives none.
    """
    del name
    if isinstance(prop, prim.LogicalNot) and isinstance(prop.child, prim.Comparison):
        flipped = _NEGATED.get(prop.child.operator)
        if flipped is None:
            return []
        prop = Comparison(prop.child.left, flipped, prop.child.right)
    if isinstance(prop, prim.LogicalAnd):
        return [form for child in prop.children for form in _nonnegative(child)]
    if not isinstance(prop, prim.Comparison):
        return []
    left, right = _affine(prop.left), _affine(prop.right)
    if left is None or right is None:
        return []
    difference = dict(left)
    for key, value in right.items():
        difference[key] = difference.get(key, Fraction(0)) - value
    negative = {key: -value for key, value in difference.items()}
    one = {_CONSTANT: Fraction(1)}
    if prop.operator == ">=":
        return [difference]
    if prop.operator == "<=":
        return [negative]
    if prop.operator == ">":
        return [_minus(difference, one)]
    if prop.operator == "<":
        return [_minus(negative, one)]
    if prop.operator == "==":
        return [difference, negative]
    return []


#: The comparison that holds where one does not, between integers.
_NEGATED = {"<": ">=", "<=": ">", ">": "<=", ">=": "<", "==": "!=", "!=": "=="}


def _minus(form: Mapping[str, Fraction], other: Mapping[str, Fraction]) -> dict[str, Fraction]:
    """``form - other``."""
    out = dict(form)
    for key, value in other.items():
        out[key] = out.get(key, Fraction(0)) - value
    return out


def _shown_by(form: Mapping[str, Fraction], known: Sequence[Mapping[str, Fraction]]) -> bool:
    """Whether ``form >= 0`` follows from the known forms, each at least ``0``.

    ``form`` less a sum of up to three known forms has to leave a number
    that is not negative, with no variable left: a nonnegative combination
    of what is known with unit weights, which is as far as an index argument
    needs to go (``a - 2 >= 0`` from ``a >= 2``; ``n - 2 >= 0`` from ``n >= 1``
    and ``n != 1`` is beyond it, and is left to Lean).
    """
    for count in range(min(3, len(known)) + 1):
        for chosen in itertools.combinations(known, count):
            rest = dict(form)
            for each in chosen:
                rest = _minus(rest, each)
            if _constant_only(rest) and rest.get(_CONSTANT, Fraction(0)) >= 0:
                return True
    return False


def implied(guard: Any, facts: Sequence[Any], types: Mapping[str, Any]) -> bool | None:
    """Whether ``guard`` follows from the case's facts and the bounds of its types.

    ``True`` where it follows as integer arithmetic (:func:`_shown_by`) or is
    one of the facts as it stands; ``False`` where it is integer arithmetic
    and does not follow that way; ``None`` for a guard this cannot read, a
    condition over the reals, say, which Lean's closers are left to show.
    """
    if guard is True:
        return True
    for fact in facts:
        if structurally_equal(fact, guard):
            return True
    if isinstance(guard, prim.LogicalAnd):
        answers = [implied(child, facts, types) for child in guard.children]
        if any(answer is False for answer in answers):
            return False
        return True if all(answers) else None
    if not isinstance(guard, prim.Comparison):
        return None
    left, right = _affine(guard.left), _affine(guard.right)
    if left is None or right is None:
        return None
    if not all(_integer_name(name, types) for name in (*left, *right) if name != _CONSTANT):
        return None
    known = _known(facts, types)
    if guard.operator == "!=":
        difference = _minus(left, right)
        one = {_CONSTANT: Fraction(1)}
        negative = {key: -value for key, value in difference.items()}
        if _shown_by(_minus(difference, one), known) or _shown_by(_minus(negative, one), known):
            return True
        for fact in facts:
            found = _disequality(fact)
            if found is not None and _clean(found) in (_clean(difference), _clean(negative)):
                return True
        return False
    forms = _nonnegative(guard)
    if not forms:
        return None
    return all(_shown_by(form, known) for form in forms)


def _known(facts: Sequence[Any], types: Mapping[str, Any]) -> list[dict[str, Fraction]]:
    """What the case knows as forms that are at least ``0``: the bounds, the facts, and their edges.

    An integer that is at least ``c`` and is not ``c`` is at least ``c + 1``:
    ``n >= 1`` and ``n != 1``, which is the case ``if n == 1:`` leaves, give
    ``n >= 2``. So each disequality among the facts moves the bound it sits
    on by one, where the bound follows.
    """
    known = _bounds(types)
    for fact in facts:
        known.extend(_nonnegative(fact))
    for fact in facts:
        difference = _disequality(fact)
        if difference is None:
            continue
        one = {_CONSTANT: Fraction(1)}
        negative = {key: -value for key, value in difference.items()}
        if _shown_by(difference, known):
            known.append(_minus(difference, one))
        elif _shown_by(negative, known):
            known.append(_minus(negative, one))
    return known


def _disequality(fact: Any) -> dict[str, Fraction] | None:
    """``left - right`` of a fact that says two integers differ, ``a != b`` or ``not (a == b)``."""
    if isinstance(fact, prim.LogicalNot) and isinstance(fact.child, prim.Comparison):
        if fact.child.operator != "==":
            return None
        fact = fact.child
    elif not (isinstance(fact, prim.Comparison) and fact.operator == "!="):
        return None
    left, right = _affine(fact.left), _affine(fact.right)
    if left is None or right is None:
        return None
    return _minus(left, right)


def _integer_name(name: str, types: Mapping[str, Any]) -> bool:
    """Whether a name of the scope is an integer, by its type."""
    sort = types.get(name)
    return sort is not None and _integer_sort(sort)


# }}}
