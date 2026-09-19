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
lanky statement does and leaves it unconstrained outside, which is sound: a
statement that never mentions a point cannot depend on its value.

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
from lanky.terms import Abs, Exists, Forall, Sum, Var, conjuncts

__all__ = [
    "LeanStatement",
    "UnsupportedTerm",
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
        return f"{lean_type(obj.domain)} → {lean_type(obj.codomain)}"
    if isinstance(obj, Refined):
        return lean_type(obj.base)
    raise UnsupportedTerm(f"cannot print the type {obj!r} in Lean")


def domain_guards(var: Var, domain: Any) -> list[str]:
    """The propositions a binder's domain imposes on its variable.

    ``Fin[n]`` gives ``i < n``; a refinement gives its own propositions; a plain
    sort gives nothing, because the Lean type already says it.
    """
    if isinstance(domain, FinType):
        return [f"{print_lean(var)} < {_render(domain.bound, _CMP + 1)}"]
    if isinstance(domain, Refined):
        return domain_guards(var, domain.base) + [_render(p, _ARROW + 1) for p in domain.props]
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
    # A universal's body is the rightmost thing in the formula, and an arrow is
    # right associative, so it never needs brackets; an existential's body sits
    # to the right of a conjunction, where a quantifier would swallow the rest.
    text = _render(expr.body, _QUANT if universal else _AND + 1)
    for position in reversed(range(len(expr.binders))):
        var, domain = expr.binders[position]
        conditions = domain_guards(var, domain)
        if position == len(expr.binders) - 1:
            conditions += [_render(guard, _ARROW + 1) for guard in guards]
        if universal:
            for condition in reversed(conditions):
                text = f"{condition} → {text}"
        else:
            for condition in reversed(conditions):
                text = f"{condition} ∧ {text}"
        text = f"{word} {var.name} : {lean_type(domain)}, {text}"
    return _parens(text, _QUANT, outer)


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
        text = " ∧ ".join(_render(child, _AND + 1) for child in expr.children)
        return _parens(text, _AND, outer)
    if isinstance(expr, prim.LogicalOr):
        text = " ∨ ".join(_render(child, _OR + 1) for child in expr.children)
        return _parens(text, _OR, outer)
    if isinstance(expr, prim.LogicalNot):
        return _parens(f"¬{_render(expr.child, _APP)}", _NOT, outer)
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
        UnsupportedTerm: If the term leaves the core-Lean fragment.
    """
    return _render(expr, _QUANT)


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
                prop = _render(term, _ARROW + 1)
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
        UnsupportedTerm: If any part of the statement leaves the fragment.
    """
    lean_name = _lean_name(name)
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
        hypotheses.append((f"h{len(hypotheses)}", _render(guard, _QUANT)))
        hypothesis_terms.append(guard)
    return LeanStatement(
        name=lean_name,
        binders=tuple(binders),
        hypotheses=tuple(hypotheses),
        goal=_render(term.body, _QUANT),
        goal_term=term.body,
        hypothesis_terms=tuple(hypothesis_terms),
    )


# }}}
