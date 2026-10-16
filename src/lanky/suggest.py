"""Which facts of :mod:`lanky.known` fit a claim, by shape.

The design idea. When Lean cannot prove a claim alone, the most useful thing
lanky can say is which known fact would take a step of it: "modulus_squared
rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha". That
is a suggestion, read off the shapes of the claim's terms, and nothing rests
on it: a proof that cites the fact is checked by Lean like any other.

A fact fits where one side of its statement matches a term of the claim: the
fact's variables bind terms of their own type (a ``Complex`` variable binds a
complex term, a ``Real`` one a real or an integer term), the same variable
binds the same term wherever it occurs, and the rest of the side is the
claim's term as written. Sums are matched binder by binder. A family the
fact sums over binds whatever the claim sums, as a function of the claim's
own binders, so ``one_more_term``'s ``f[k]`` binds ``r**k``. Sums and products
are matched up to the order of their operands, and a bare variable of the
fact may take up the operands the others leave, so ``distribute``'s
``c * sum(...)`` fits ``2 * x * sum(...)`` with ``c = 2*x``.

A side with no function in it, no ``log``, ``abs``, ``sum`` and the like,
fits too much to say anything: ``abs_of_positive``'s right side ``x`` fits
every term. Such a side is never suggested.

The matcher is about shape, and generous where that costs nothing: it does
not ask whether the fact's hypotheses hold where it fits, which is the
proof's business, and an integer bound ``n + 1`` fits a literal ``6`` at ``n =
5``. It is the step report's too: a step of a written proof that no cited
fact gets to is reported with the facts of its shape (:func:`suggestions`).
"""

from __future__ import annotations

import itertools
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import (
    Abs,
    Elementary,
    Exists,
    Forall,
    Sum,
    Var,
    conjuncts,
    free_variables,
    init_args,
    render,
    structurally_equal,
)

__all__ = ["Suggestion", "known_entries", "suggestions"]

#: How many suggestions are made for one claim, at most.
LIMIT = 5

#: How many operands of a sum or a product are matched in every order, at most.
_PERMUTED = 5


@dataclass(frozen=True)
class Suggestion:
    """A known fact that fits a term of a claim.

    Attributes:
        name: The fact's Python name, as ``from lanky.known import ...`` imports it.
        side: The side of the fact that fits, as the fact writes it.
        found: The term of the claim it fits.
        at: What each of the fact's variables binds there, by name, as text.
        reverse: Whether the side that fits is the fact's right side.
        relation: The fact's relation: ``==``, ``<=`` or ``<``, as written.
    """

    name: str
    side: str
    found: str
    at: tuple[tuple[str, str], ...]
    reverse: bool
    relation: str

    @property
    def text(self) -> str:
        """The suggestion in a line: what the fact does, and where and how it fits.

        ``modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)),
        at z = alpha``. A fact that states an equation rewrites the side that
        fits (``right to left`` when that is its right side); one that states
        an inequality bounds it, from above when it is the smaller side.
        A variable that binds a term of its own name is not repeated.
        """
        if self.relation == "==":
            how = ", right to left," if self.reverse else ""
            head = f"{self.name}{how} rewrites {self.side}"
        else:
            # a <= b bounds a from above and b from below
            direction = "below" if self.reverse else "above"
            head = f"{self.name} bounds {self.side} from {direction}"
        values = ", ".join(f"{name} = {value}" for name, value in self.at if name != value)
        if self.found == self.side and not values:
            return head
        return f"{head}; here {self.found}" + (f", at {values}" if values else "")


def known_entries() -> list[Any]:
    """The theorems of :mod:`lanky.known`, in the order its ``__all__`` names them.

    Imported here, when a suggestion is asked for, and not before: importing
    lanky never builds them.
    """
    import lanky.known as known

    return [getattr(known, name) for name in known.__all__]


def suggestions(
    term: Any,
    types: dict[str, Any] | None = None,
    *,
    entries: Sequence[Any] | None = None,
    exclude: Iterable[str] = (),
    limit: int = LIMIT,
) -> list[Suggestion]:
    """The facts of :mod:`lanky.known` that fit a term of ``term``, outermost first.

    ``term`` is a claim's term, a :class:`~lanky.terms.Forall` whose binders
    give the types of its variables, or any term with ``types`` naming them:
    the step a written proof takes, say. ``entries`` are the facts to try,
    by default :func:`known_entries`; ``exclude`` names facts not to
    suggest, such as the claim itself when it is one of them. One
    suggestion is made per fact and side, at the first term that fits.
    """
    entries = known_entries() if entries is None else list(entries)
    excluded = set(exclude)
    patterns = [
        pattern
        for entry in entries
        if getattr(entry, "__name__", None) not in excluded
        for pattern in _patterns(entry)
    ]
    found: list[Suggestion] = []
    seen: set[tuple[str, bool]] = set()
    for subterm, scope in _subterms(term, dict(types or {})):
        for pattern in patterns:
            key = (pattern.name, pattern.reverse)
            if key in seen:
                continue
            binding = _Match(pattern, scope).run(pattern.side, subterm)
            if binding is None:
                continue
            seen.add(key)
            found.append(
                Suggestion(
                    name=pattern.name,
                    side=render(pattern.side),
                    found=render(subterm),
                    at=tuple(
                        (name, binding.shown(name))
                        for name, _ in pattern.variables
                        if name in binding.values
                    ),
                    reverse=pattern.reverse,
                    relation=pattern.relation,
                )
            )
            if len(found) >= limit:
                return found
    return found


# {{{ the sides of a fact


@dataclass(frozen=True)
class _Pattern:
    """One side of a known fact, with the fact's variables and their types."""

    name: str
    side: Any
    variables: tuple[tuple[str, Any], ...]
    reverse: bool
    relation: str

    @property
    def sorts(self) -> dict[str, Any]:
        """The fact's variables, by name."""
        return dict(self.variables)


#: The relations a fact may state, as a comparison's operator.
_RELATIONS = ("==", "<=", "<", ">=", ">")


def _patterns(entry: Any) -> list[_Pattern]:
    """The sides of a fact worth matching: each with a function in it."""
    goal = getattr(entry, "goal", None)
    if not isinstance(goal, prim.Comparison) or goal.operator not in _RELATIONS:
        return []
    variables = tuple(getattr(entry, "variables", ()))
    left, right, relation = goal.left, goal.right, goal.operator
    if relation in (">=", ">"):
        left, right = right, left
        relation = "<=" if relation == ">=" else "<"
    sorts = dict(variables)
    sides = [(left, False), (right, True)]
    return [
        _Pattern(entry.__name__, side, variables, reverse, relation)
        for side, reverse in sides
        if _has_function(side) and not _any_sum(side, sorts)
    ]


def _any_sum(side: Any, sorts: dict[str, Any]) -> bool:
    """Whether ``side`` is a sum of anything: one family, at its one binder, below a variable.

    ``fiber_exchange``'s right side, ``sum(y[i] for i in Fin[n])``, is every
    sum there is, and says nothing about the claim it fits.
    """
    if not isinstance(side, Sum) or side.guard is not None or len(side.binders) != 1:
        return False
    (var, domain), body = side.binders[0], side.body
    if not (isinstance(domain, FinType) and isinstance(domain.bound, prim.Variable)):
        return False
    if domain.bound.name not in sorts:
        return False
    family, arguments = _spine(body)
    return (
        family in sorts
        and len(arguments) == 1
        and isinstance(arguments[0], prim.Variable)
        and arguments[0].name == var.name
    )


def _has_function(term: Any) -> bool:
    """Whether ``term`` applies a function: an elementary one, ``abs`` or a sum."""
    if isinstance(term, Elementary | Abs | Sum):
        return True
    if isinstance(term, prim.ExpressionNode):
        return any(_has_function(arg) for arg in init_args(term))
    if isinstance(term, tuple):
        return any(_has_function(item) for item in term)
    return False


# }}}


# {{{ the terms of a claim


def _subterms(term: Any, scope: dict[str, Any]) -> Iterator[tuple[Any, dict[str, Any]]]:
    """Every term of ``term`` that is a number, outermost first, each with its scope."""
    if isinstance(term, Forall | Exists):
        inner = dict(scope)
        for var, domain in term.binders:
            inner[var.name] = domain
        for part in (*conjuncts(term.guard), term.body):
            yield from _subterms(part, inner)
        return
    if isinstance(term, prim.Comparison):
        yield from _subterms(term.left, scope)
        yield from _subterms(term.right, scope)
        return
    if isinstance(term, prim.LogicalAnd | prim.LogicalOr):
        for child in term.children:
            yield from _subterms(child, scope)
        return
    if isinstance(term, prim.LogicalNot):
        yield from _subterms(term.child, scope)
        return
    if not isinstance(term, prim.ExpressionNode) or isinstance(term, prim.Variable):
        return
    yield term, scope
    if isinstance(term, Sum):
        inner = dict(scope)
        for var, domain in term.binders:
            inner[var.name] = domain
        yield from _subterms(term.body, inner)
        return
    if isinstance(term, prim.Call | prim.Subscript):
        # the arguments of a family are indices, not the numbers a fact is about
        return
    for arg in init_args(term):
        for item in arg if isinstance(arg, tuple) else (arg,):
            yield from _subterms(item, scope)


# }}}


# {{{ matching


class _Binding:
    """What a match has bound so far: a value per variable, a function per family."""

    def __init__(self) -> None:
        self.values: dict[str, Any] = {}
        #: For a family, the claim's binder names it was applied at and the body.
        self.functions: dict[str, tuple[tuple[str, ...], Any]] = {}

    def copy(self) -> _Binding:
        """A binding a failed branch can change without changing this one."""
        other = _Binding()
        other.values = dict(self.values)
        other.functions = dict(self.functions)
        return other

    def shown(self, name: str) -> str:
        """What ``name`` binds, as text: a term, or a function of the claim's binders."""
        if name in self.functions:
            names, body = self.functions[name]
            family, arguments = _spine(body)
            if family is not None and [getattr(a, "name", None) for a in arguments] == list(names):
                # f[k] -> y[k] is the claim's own family, y
                return family
            return f"{', '.join(names)} -> {render(body)}"
        return render(self.values[name])


class _Match:
    """One attempt to match a fact's side against a term of a claim."""

    def __init__(self, pattern: _Pattern, scope: dict[str, Any]) -> None:
        self.pattern = pattern
        self.sorts = pattern.sorts
        self.scope = scope

    def run(self, side: Any, term: Any) -> _Binding | None:
        """The binding under which ``side`` is ``term``, or ``None``."""
        for binding in self._match(side, term, _Binding(), {}, dict(self.scope)):
            return binding
        return None

    def _match(
        self,
        pattern: Any,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """Every binding that extends ``binding`` and makes ``pattern`` the term.

        ``bound`` names, for each binder of a sum of the fact the match is
        inside, the binder of the claim's sum it stands for; ``scope`` gives
        the type of every name of the claim in scope there.
        """
        if isinstance(pattern, Var | prim.Variable):
            name = pattern.name
            if name in bound:
                if isinstance(term, prim.Variable) and term.name == bound[name]:
                    yield binding
                return
            if name in self.sorts and not isinstance(_unrefined(self.sorts[name]), FnType):
                yield from self._bind(name, term, binding, bound, scope)
                return
            if isinstance(term, prim.Variable) and term.name == name:
                yield binding
            return
        if _is_number(pattern):
            yield from self._number(pattern, term, binding, bound, scope)
            return
        if isinstance(pattern, prim.Call | prim.Subscript):
            yield from self._application(pattern, term, binding, bound, scope)
            return
        if isinstance(pattern, Sum):
            yield from self._sum(pattern, term, binding, bound, scope)
            return
        if isinstance(pattern, prim.Sum | prim.Product):
            yield from self._operands(pattern, term, binding, bound, scope)
            return
        if not isinstance(pattern, prim.ExpressionNode) or not isinstance(
            term, prim.ExpressionNode
        ):
            return
        if pattern.mapper_method != term.mapper_method:
            return
        if isinstance(pattern, Elementary) and pattern.function != term.function:
            return
        if isinstance(pattern, prim.Comparison) and pattern.operator != term.operator:
            return
        yield from self._all(
            [
                (part, other)
                for part, other in zip(init_args(pattern), init_args(term), strict=True)
                if not isinstance(part, str)
            ],
            binding,
            bound,
            scope,
        )

    def _all(
        self,
        pairs: Sequence[tuple[Any, Any]],
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """Every binding under which each pattern of ``pairs`` is its term."""
        if not pairs:
            yield binding
            return
        (pattern, term), rest = pairs[0], pairs[1:]
        if isinstance(pattern, tuple):
            if not isinstance(term, tuple) or len(term) != len(pattern):
                return
            yield from self._all([*zip(pattern, term, strict=True), *rest], binding, bound, scope)
            return
        for extended in self._match(pattern, term, binding.copy(), bound, scope):
            yield from self._all(rest, extended, bound, scope)

    def _bind(
        self,
        name: str,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """Bind a variable of the fact to ``term``, if its type and the binding allow."""
        local = set(bound.values())
        if free_variables(term) & local:
            # a term of the claim's own binders is no value the fact's variable takes
            return
        if not _of_sort(term, self.sorts[name], scope):
            return
        if name in binding.values:
            if structurally_equal(binding.values[name], term):
                yield binding
            return
        binding.values[name] = term
        yield binding

    def _number(
        self,
        pattern: Any,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """A literal of the fact: the same number in the claim."""
        if _is_number(term) and term == pattern:
            yield binding

    def _application(
        self,
        pattern: Any,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """A family of the fact applied: at its own binders, a function; else as written."""
        family, arguments = _spine(pattern)
        if family is None or family not in self.sorts:
            if isinstance(term, prim.ExpressionNode) and term.mapper_method == (
                pattern.mapper_method
            ):
                yield from self._all(
                    list(zip(init_args(pattern), init_args(term), strict=True)),
                    binding,
                    bound,
                    scope,
                )
            return
        names = [
            bound.get(argument.name) if isinstance(argument, prim.Variable) else None
            for argument in arguments
        ]
        if all(names) and len(set(names)) == len(names):
            # f[k] at the fact's own binders: a function of the claim's binders
            yield from self._function(family, tuple(names), term, binding, scope)
            return
        if family in binding.functions:
            # f[n] once f is known: the function at these arguments
            from lanky.induction import substitute

            names_at, body = binding.functions[family]
            if len(names_at) != len(arguments):
                return
            values = []
            for argument in arguments:
                instances = list(self._instance(argument, binding, bound))
                if not instances:
                    return
                values.append(instances[0])
            expected = substitute(body, dict(zip(names_at, values, strict=True)))
            if _same(expected, term):
                yield binding
            return
        # f[n] with f not yet known: the claim's family, applied as written
        other, others = _spine(term)
        if other is None or len(others) != len(arguments):
            return
        names_at = tuple(f"_{position}" for position in range(len(others)))
        extended = binding.copy()
        extended.values[family] = Var(other)
        extended.functions[family] = (
            names_at,
            _applied(other, tuple(Var(name) for name in names_at)),
        )
        yield from self._all(list(zip(arguments, others, strict=True)), extended, bound, scope)

    def _instance(self, argument: Any, binding: _Binding, bound: dict[str, str]) -> Iterator[Any]:
        """A term of the fact, with what the binding gives its variables put in."""
        from lanky.induction import substitute

        values: dict[str, Any] = {name: Var(other) for name, other in bound.items()}
        values.update(binding.values)
        yield substitute(argument, values)

    def _function(
        self,
        family: str,
        names: tuple[str, ...],
        term: Any,
        binding: _Binding,
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """Bind a family of the fact to ``term`` as a function of the claim's binders."""
        sort = _unrefined(self.sorts[family])
        if not _of_sort(term, _codomain(sort), scope):
            return
        if family in binding.functions:
            from lanky.induction import substitute

            names_at, body = binding.functions[family]
            if len(names_at) != len(names):
                return
            renamed = substitute(
                body, {old: Var(new) for old, new in zip(names_at, names, strict=True)}
            )
            if _same(renamed, term):
                yield binding
            return
        binding.functions[family] = (names, term)
        binding.values[family] = term
        yield binding

    def _sum(
        self,
        pattern: Sum,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """A sum of the fact: a sum of the claim, binder by binder."""
        if not isinstance(term, Sum) or len(term.binders) != len(pattern.binders):
            return
        if (pattern.guard is None) != (term.guard is None):
            return
        inner_bound = dict(bound)
        inner_scope = dict(scope)
        pairs: list[tuple[Any, Any]] = []
        for (var, domain), (other, other_domain) in zip(pattern.binders, term.binders, strict=True):
            if not (isinstance(domain, FinType) and isinstance(other_domain, FinType)):
                return
            pairs.append((domain.bound, other_domain.bound))
            inner_bound[var.name] = other.name
            inner_scope[other.name] = other_domain
        # each bound is read with the binders before it bound, as Python does
        candidates = [binding]
        for position, (bound_pattern, bound_term) in enumerate(pairs):
            outer = {
                var.name: other.name
                for (var, _), (other, _) in zip(
                    pattern.binders[:position], term.binders[:position], strict=True
                )
            }
            step_bound = {**bound, **outer}
            candidates = [
                extended
                for candidate in candidates
                for extended in self._bound(
                    bound_pattern, bound_term, candidate, step_bound, inner_scope
                )
            ]
            if not candidates:
                return
        parts = [(pattern.body, term.body)]
        if pattern.guard is not None:
            parts.append((pattern.guard, term.guard))
        for candidate in candidates:
            yield from self._all(parts, candidate, inner_bound, inner_scope)

    def _bound(
        self,
        pattern: Any,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """A sum's bound: as written, or ``n + c`` against a literal at ``n = literal - c``."""
        matched = False
        for extended in self._match(pattern, term, binding.copy(), bound, scope):
            matched = True
            yield extended
        if matched or not isinstance(term, int) or isinstance(term, bool):
            return
        if isinstance(pattern, prim.Sum) and len(pattern.children) == 2:
            variable, offset = pattern.children
            if isinstance(variable, int):
                variable, offset = offset, variable
            if isinstance(offset, int) and isinstance(variable, prim.Variable):
                yield from self._match(variable, term - offset, binding.copy(), bound, scope)

    def _operands(
        self,
        pattern: prim.Sum | prim.Product,
        term: Any,
        binding: _Binding,
        bound: dict[str, str],
        scope: dict[str, Any],
    ) -> Iterator[_Binding]:
        """A sum or a product of the fact: the claim's, its operands in any order.

        A variable of the fact among the operands may take up several of the
        claim's, as their sum or product: ``c * sum(...)`` fits ``2 * x *
        sum(...)``.
        """
        if not isinstance(term, prim.ExpressionNode) or term.mapper_method != (
            pattern.mapper_method
        ):
            return
        mine, theirs = list(pattern.children), list(term.children)
        if len(theirs) > _PERMUTED + 2:
            return
        if len(mine) == len(theirs):
            orders = itertools.permutations(theirs) if len(theirs) <= _PERMUTED else [theirs]
            for order in orders:
                yield from self._all(list(zip(mine, order, strict=True)), binding, bound, scope)
            return
        if len(mine) > len(theirs):
            return
        # one variable of the fact takes up what the others leave
        for position, absorber in enumerate(mine):
            if not (
                isinstance(absorber, prim.Variable)
                and absorber.name in self.sorts
                and absorber.name not in bound
            ):
                continue
            others = mine[:position] + mine[position + 1 :]
            for chosen in itertools.permutations(range(len(theirs)), len(others)):
                rest = [child for index, child in enumerate(theirs) if index not in chosen]
                remainder = rest[0] if len(rest) == 1 else _rebuilt(term, rest)
                pairs = [
                    *zip(others, [theirs[index] for index in chosen], strict=True),
                    (absorber, remainder),
                ]
                yield from self._all(pairs, binding, bound, scope)


def _spine(term: Any) -> tuple[str | None, tuple[Any, ...]]:
    """The family a term applies and its arguments: ``f[i, j]`` and ``f(i)(j)`` alike."""
    arguments: list[Any] = []
    while isinstance(term, prim.Call | prim.Subscript):
        if isinstance(term, prim.Subscript):
            index = term.index
            arguments[:0] = list(index) if isinstance(index, tuple) else [index]
            term = term.aggregate
        else:
            arguments[:0] = list(term.parameters)
            term = term.function
    if isinstance(term, prim.Variable) and arguments:
        return term.name, tuple(arguments)
    return None, ()


def _applied(family: str, arguments: tuple[Any, ...]) -> Any:
    """``family[arguments]``, as the claim writes an application."""
    from lanky.terms import Subscript

    index = arguments[0] if len(arguments) == 1 else arguments
    return Subscript(Var(family), index)


def _same(expected: Any, term: Any) -> bool:
    """Whether two terms are the same, an application read either way, ``f[i]`` or ``f(i)``."""
    family, arguments = _spine(expected)
    other, others = _spine(term)
    if family is not None and other is not None:
        return family == other and structurally_equal(arguments, others)
    return structurally_equal(expected, term)


def _rebuilt(term: Any, children: list[Any]) -> Any:
    """A sum or a product of the claim's kind, of ``children``."""
    from lanky.terms import lift

    return lift(type(term)(tuple(children)))


def _unrefined(sort: Any) -> Any:
    """A type with its refinements taken off."""
    while isinstance(sort, Refined):
        sort = sort.base
    return sort


def _codomain(sort: Any) -> Any:
    """What a family's values are: the codomain under every index."""
    while isinstance(sort, FnType):
        sort = _unrefined(sort.codomain)
    return sort


def _is_number(value: Any) -> bool:
    """Whether ``value`` is a number Python holds, not a term and not a truth value."""
    return isinstance(value, int | float | complex) and not isinstance(value, bool)


#: The kinds of number a variable of each sort binds, by the sort's name.
_ACCEPTS = {
    "Nat": {"Int"},
    "Int": {"Int"},
    "Real": {"Int", "Real"},
    "Complex": {"Complex"},
}


def _of_sort(term: Any, sort: Any, scope: dict[str, Any]) -> bool:
    """Whether ``term`` is a value a variable of ``sort`` binds, as far as its type says."""
    sort = _unrefined(sort)
    if isinstance(sort, FinType):
        sort_name = "Nat"
    elif isinstance(sort, Sort):
        sort_name = sort.name
    else:
        return True
    accepted = _ACCEPTS.get(sort_name)
    if accepted is None:
        return True
    from lanky.lean import number_type

    try:
        kind = number_type(term, scope, mathlib=True)
    except Exception:  # noqa: BLE001 - a term the printer cannot place is not ruled out
        return True
    named = {"ℝ": "Real", "ℂ": "Complex"}.get(kind, "Int")
    if sort_name == "Nat" and named == "Int" and _is_number(term):
        return term >= 0
    return named in accepted


# }}}
