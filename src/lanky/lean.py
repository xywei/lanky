"""Printing lanky terms as Lean 4 source, over core Lean only.

The design idea. Lean is the platform lanky is hosted on, so a lanky statement
has to arrive there as something Lean can elaborate on its own, with no Mathlib
and no ``lake exe cache get``. That constraint decides almost everything in this
module: what can be printed is exactly what core Lean's ``Nat``, ``Int`` and
``Bool``, its arithmetic, and its logical connectives can say. A reduction
(:class:`lanky.terms.Sum`) needs ``Finset.sum`` and an absolute value needs the
``abs`` of an ordered ring; both are Mathlib, so both raise
:exc:`UnsupportedTerm` rather than emit source Lean would reject with a puzzling
elaboration error. ``Real`` is out for the same reason.

Two representation choices are worth stating, because a reader of the emitted
source will notice them and because they are what makes ``omega`` effective.

*A bounded quantifier is a ``Nat`` quantifier with a guard.* ``Fin[n]`` prints as
``∀ i : Nat, i < n → ...`` and not as ``∀ i : Fin n, ...``. The ``Fin`` form
would be closer to the lanky type, but every arithmetic step then carries a
coercion ``(↑i : Nat)`` and a wraparound: ``i + 1`` in ``Fin n`` is not ``i + 1``
in the statement lanky means, and ``omega``, which is the workhorse tactic here,
reasons about linear arithmetic over ``Nat`` and ``Int`` rather than about
coercions out of ``Fin``. The guarded form says the same thing with nothing to
unfold, so the goals the tactic ladder sees are the goals it is good at.

*A family is a total function.* ``Fn[Fin[n], Nat]`` prints as ``Nat → Nat``, not
as ``Fin n → Nat``. The bound lives in the guards of the quantifiers that apply
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
assumed. Declining costs a proof at worst; assuming costs soundness.

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

Two places where Lean's arithmetic is not Python's are worth knowing, because a
statement that uses them means in Lean what Lean's operators mean and not what a
sampled Python run would compute. Subtraction on ``Nat`` is truncated, so
``n - 1`` is ``0`` at ``n = 0`` in the emitted source while lanky's property
tester, which samples naturals as Python integers, lets it go negative. Division
and remainder on ``Int`` round the way Lean rounds them and not the way Python's
``//`` floors. Statements over ``Nat`` with no subtraction, which is what index
arithmetic is, are unaffected; the rest is recorded as a known gap.

The printer is a recursive descent with Lean's own operator precedences, so the
emitted source is the source a Lean user would have written, and it is worth
reading on its own and not only as oracle input.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Abs,
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
    "domain_guards",
    "lean_type",
    "print_lean",
    "statement_of",
]


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

#: The scalar sorts core Lean has, and their Lean names.
_SORT_NAMES = {"Nat": "Nat", "Int": "Int", "Bool": "Bool", "Prop": "Prop"}


def lean_type(obj: Any) -> str:
    """The Lean type of a lanky type.

    ``Fin[n]`` has no type of its own here: its points are naturals and its
    bound is a guard (see the module docstring), so it prints as ``Nat``.

    A family whose domain is itself a family needs brackets around the domain,
    because ``→`` is right associative: ``Fn[Fn[Fin[n], Nat], Nat]`` is
    ``(Nat → Nat) → Nat``, and without the brackets it would read as the
    two-argument ``Nat → Nat → Nat``, which is a different type and the one a
    family of families already prints as.
    """
    if isinstance(obj, Sort):
        name = _SORT_NAMES.get(obj.name)
        if name is None:
            raise UnsupportedTerm(
                f"the sort {obj.name} has no core-Lean counterpart "
                "(Real needs Mathlib)"
            )
        return name
    if isinstance(obj, FinType):
        return "Nat"
    if isinstance(obj, FnType):
        domain = lean_type(obj.domain)
        if isinstance(_unrefined(obj.domain), FnType):
            domain = f"({domain})"
        return f"{domain} → {lean_type(obj.codomain)}"
    if isinstance(obj, Refined):
        return lean_type(obj.base)
    raise UnsupportedTerm(f"cannot print the type {obj!r} in Lean")


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


def domain_guards(var: Var, domain: Any) -> list[str]:
    """The propositions a binder's domain imposes on its variable.

    ``Fin[n]`` gives ``i < n``; a refinement gives its own propositions; a plain
    sort gives nothing, because the Lean type already says it.
    """
    if isinstance(domain, FinType):
        return [f"{_render(var, _CMP + 1)} < {_render(domain.bound, _CMP + 1)}"]
    if isinstance(domain, Refined):
        return domain_guards(var, domain.base) + [
            _render_prop(p, _ARROW + 1) for p in domain.props
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


def _render_number(value: Any) -> str:
    """Print a numeric literal, refusing the ones that need a field."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
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


def _negated(child: Any) -> tuple[bool, Any] | None:
    """Recognize ``(-1) * x`` so that a sum of it prints as a subtraction."""
    if isinstance(child, prim.Product) and child.children:
        first = child.children[0]
        if isinstance(first, int) and first == -1:
            rest = child.children[1:]
            if len(rest) == 1:
                return True, rest[0]
            return True, prim.Product(rest)
    if isinstance(child, int) and not isinstance(child, bool) and child < 0:
        return True, -child
    return None


def _render_sum(expr: prim.Sum) -> str:
    """Print an addition, reading a negated summand back as a subtraction.

    Subtraction is not a node: pymbolic builds ``a - b`` as a sum with ``(-1) *
    b`` in it, and ``-1`` is not a ``Nat``, so printing the sum literally would
    not even elaborate. Over ``Nat`` the ``-`` this emits is Lean's truncated
    subtraction, which is what ``omega`` models.
    """
    parts = []
    for position, child in enumerate(expr.children):
        negation = _negated(child)
        if negation is None:
            text = _render(child, _ADD)
            parts.append(text if position == 0 else f" + {text}")
        else:
            text = _render(negation[1], _MUL)
            parts.append(f"-{text}" if position == 0 else f" - {text}")
    return "".join(parts)


def _render_quantifier(expr: Forall | Exists, outer: int) -> str:
    """Print ``∀`` or ``∃`` one binder at a time, each guard next to its binder.

    Nesting the binders rather than grouping them keeps every guard beside the
    variable it constrains, which is how a Lean user writes it and how the
    oracle's ``intro`` list lines up with the statement.
    """
    universal = isinstance(expr, Forall)
    word = "∀" if universal else "∃"
    guards = list(conjuncts(expr.guard))
    if not expr.binders:
        # A closed statement whose hypotheses are its only parameters: there is
        # no variable to quantify, but the guard is still the antecedent and
        # dropping it would print a strictly stronger claim than was written.
        text = _render_prop(expr.body, _ARROW if universal else _AND + 1)
        for guard in reversed(guards):
            joiner = "→" if universal else "∧"
            text = f"{_render_prop(guard, _ARROW + 1)} {joiner} {text}"
        if not guards:
            return _render_prop(expr.body, outer)
        return _parens(text, _ARROW if universal else _AND, outer)
    # A universal's body is the rightmost thing in the formula, and an arrow is
    # right associative, so it never needs brackets; an existential's body sits
    # to the right of a conjunction, where a quantifier would swallow the rest.
    text = _render_prop(expr.body, _QUANT if universal else _AND + 1)
    for position in reversed(range(len(expr.binders))):
        var, domain = expr.binders[position]
        conditions = domain_guards(var, domain)
        if position == len(expr.binders) - 1:
            conditions += [_render_prop(guard, _ARROW + 1) for guard in guards]
        if universal:
            for condition in reversed(conditions):
                text = f"{condition} → {text}"
        else:
            for condition in reversed(conditions):
                text = f"{condition} ∧ {text}"
        text = f"{word} {var.name} : {lean_type(domain)}, {text}"
    return _parens(text, _QUANT, outer)


def _render_prop(expr: Any, outer: int) -> str:
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
    return _render(expr, outer)


def _render(expr: Any, outer: int) -> str:
    """Print ``expr`` as Lean source, parenthesized for a context of ``outer``."""
    if isinstance(expr, Var | prim.Variable):
        return expr.name
    if isinstance(expr, int | float | Fraction | bool):
        return _parens(_render_number(expr), _ADD if _is_negative(expr) else _ATOM, outer)
    if expr is None:
        raise UnsupportedTerm("cannot print an empty term in Lean")
    if isinstance(expr, Forall | Exists):
        return _render_quantifier(expr, outer)
    if isinstance(expr, Sum):
        raise UnsupportedTerm(
            "a reduction needs Finset.sum, which is Mathlib; core Lean cannot "
            "state it"
        )
    if isinstance(expr, Abs):
        raise UnsupportedTerm(
            "an absolute value needs the abs of an ordered ring, which is Mathlib"
        )
    if isinstance(expr, prim.Comparison):
        relation = _RELATIONS.get(expr.operator)
        if relation is None:
            raise UnsupportedTerm(f"unknown comparison operator {expr.operator!r}")
        text = f"{_render(expr.left, _CMP + 1)} {relation} {_render(expr.right, _CMP + 1)}"
        return _parens(text, _CMP, outer)
    if isinstance(expr, prim.LogicalAnd):
        text = " ∧ ".join(_render_prop(child, _AND + 1) for child in expr.children)
        return _parens(text, _AND, outer)
    if isinstance(expr, prim.LogicalOr):
        text = " ∨ ".join(_render_prop(child, _OR + 1) for child in expr.children)
        return _parens(text, _OR, outer)
    if isinstance(expr, prim.LogicalNot):
        return _parens(f"¬{_render_prop(expr.child, _APP)}", _NOT, outer)
    if isinstance(expr, prim.Sum):
        return _parens(_render_sum(expr), _ADD, outer)
    if isinstance(expr, prim.Product):
        text = " * ".join(_render(child, _MUL + 1) for child in expr.children)
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.FloorDiv):
        text = f"{_render(expr.numerator, _MUL)} / {_render(expr.denominator, _MUL + 1)}"
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.Remainder):
        text = f"{_render(expr.numerator, _MUL)} % {_render(expr.denominator, _MUL + 1)}"
        return _parens(text, _MUL, outer)
    if isinstance(expr, prim.Quotient):
        raise UnsupportedTerm(
            "true division needs a field, which is Mathlib; use // for the "
            "floor division Nat and Int have"
        )
    if isinstance(expr, prim.Power):
        text = f"{_render(expr.base, _POW + 1)} ^ {_render(expr.exponent, _POW)}"
        return _parens(text, _POW, outer)
    if isinstance(expr, prim.Call):
        args = " ".join(_render(arg, _ATOM) for arg in expr.parameters)
        text = f"{_render(expr.function, _APP)} {args}"
        return _parens(text, _APP, outer)
    if isinstance(expr, prim.Subscript):
        index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
        args = " ".join(_render(i, _ATOM) for i in index)
        text = f"{_render(expr.aggregate, _APP)} {args}"
        return _parens(text, _APP, outer)
    raise UnsupportedTerm(f"cannot print {type(expr).__name__} in Lean: {expr!r}")


def _is_negative(value: Any) -> bool:
    """Whether a literal needs parentheses where an operand is expected."""
    return isinstance(value, int | float | Fraction) and not isinstance(value, bool) and value < 0


def print_lean(expr: Any) -> str:
    """Render a lanky term as one Lean 4 proposition.

    Raises:
        UnsupportedTerm: If the term leaves the core-Lean fragment, or applies
            a family outside the domain it declares (:func:`check_applications`).
    """
    check_applications(expr)
    return _render_prop(expr, _QUANT)


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
    can reason about, so it answers ``None`` and the caller declines.
    """
    if isinstance(expr, bool):
        return None
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
    lowest = _resolve(arg, scope, False)
    return lowest is not None and lowest >= 0


def _spine(expr: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family name, arguments in order)`` for a chain of applications.

    ``f(i)`` is one application and ``f(i)(j)`` is two, because a family whose
    codomain is itself a family is applied again. The outer call's function is
    then the inner call rather than a variable, so reading only the innermost
    one would leave ``j`` unchecked while Lean, which sees the erased total
    ``Nat → Nat → Nat``, is free to reason about it. A subscript is the same
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
                f"({domain}): a family prints as a total Nat function and its "
                "bounds live in the guards, which carry nothing about a "
                "refinement, and lanky discharges an argument by affine "
                "arithmetic over the binders rather than by a solver, so it "
                "cannot show that the argument is a point of the domain"
            )
        if isinstance(domain, FinType) and not _fits(argument, domain, scope):
            raise UnsupportedTerm(
                f"{render(expr)} applies {name} outside the domain it declares "
                f"({domain}): lanky cannot show that {render(argument)} is a point "
                f"of {domain}, and a family prints as a total Nat function, so Lean "
                "would be reasoning about a value the statement does not have"
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
    ``i``: ``∀ i : Nat, i < i → i > 0`` is vacuous, ``omega`` proves it, and the
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

    This is what makes the erasure of ``Fn[Fin[n], B]`` to ``Nat → B`` sound
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

    Attributes:
        name: The theorem's Lean name.
        binders: ``(name, Lean type)`` pairs, in order.
        hypotheses: ``(name, Lean proposition)`` pairs; the names are invented
            here, since a lanky guard is a conjunction and carries none.
        goal: The conclusion, as Lean source.
        goal_term: The conclusion as a lanky term, which is what a tactic
            strategy inspects to decide what to induce on.
        hypothesis_terms: The hypotheses as lanky terms, in the order of
            ``hypotheses``.
    """

    name: str
    binders: tuple[tuple[str, str], ...]
    hypotheses: tuple[tuple[str, str], ...]
    goal: str
    goal_term: Any = None
    hypothesis_terms: tuple[Any, ...] = field(default_factory=tuple)

    @property
    def parameters(self) -> str:
        """The binders and hypotheses as Lean binder syntax."""
        return " ".join(
            f"({name} : {text})" for name, text in (*self.binders, *self.hypotheses)
        )

    @property
    def proposition(self) -> str:
        """The statement as one closed proposition, binders and all.

        A hypothesis that is itself quantified needs parentheses here, where it
        stands to the left of an arrow, and none in the binder syntax above, so
        the term is rendered again rather than the text reused.
        """
        text = self.goal
        for position in reversed(range(len(self.hypotheses))):
            prop = self.hypotheses[position][1]
            term = self.hypothesis_terms[position] if self.hypothesis_terms else None
            if term is not None:
                prop = _render_prop(term, _ARROW + 1)
            text = f"{prop} → {text}"
        for name, sort in reversed(self.binders):
            text = f"∀ {name} : {sort}, {text}"
        return text

    def source(self, tactic: str) -> str:
        """The full Lean declaration proved by ``tactic``.

        The tactic block is indented as a block, so a multi-line script can be
        passed in as written.
        """
        head = f"theorem {self.name}"
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


def statement_of(term: Any, name: str = "lanky_claim") -> LeanStatement:
    """Arrange a closed lanky term as a Lean theorem.

    The top-level quantifier becomes the theorem's parameters and its guard
    becomes the named hypotheses; everything below stays a proposition.

    Raises:
        UnsupportedTerm: If any part of the statement leaves the fragment, or
            applies a family outside the domain it declares
            (:func:`check_applications`).
    """
    lean_name = _lean_name(name)
    check_applications(term)
    if not isinstance(term, Forall):
        return LeanStatement(lean_name, (), (), print_lean(term), term)

    binders: list[tuple[str, str]] = []
    hypotheses: list[tuple[str, str]] = []
    hypothesis_terms: list[Any] = []
    for var, domain in term.binders:
        binders.append((var.name, lean_type(domain)))
        for guard in domain_guards(var, domain):
            hypotheses.append((f"h{len(hypotheses)}", guard))
            hypothesis_terms.append(None)
    for guard in conjuncts(term.guard):
        hypotheses.append((f"h{len(hypotheses)}", _render_prop(guard, _QUANT)))
        hypothesis_terms.append(guard)
    return LeanStatement(
        name=lean_name,
        binders=tuple(binders),
        hypotheses=tuple(hypotheses),
        goal=_render_prop(term.body, _QUANT),
        goal_term=term.body,
        hypothesis_terms=tuple(hypothesis_terms),
    )


# }}}
