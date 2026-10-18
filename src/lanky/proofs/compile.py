"""Compiling a traced proof to one Lean command, each line traced back to the Python.

The design idea. The body writes only proof text. The claim is printed from
the annotations by lanky's printer, as it always is, with each hypothesis
under its Python name, so that a bug here can make a proof fail and never
prove another claim. One command holds the whole proof:

- The conclusion the proof loops over, ``for a, b in
  name.conclusion.domain:``, and cites at earlier points,
  ``name.conclusion[a - 2, b + 2]``, is a theorem of its own,
  ``Lanky.<name>.claim``, with the theorem's variables and the conclusion's
  as parameters (the variables of each nested ``for`` the proof loops over,
  in order), the goal's guards among its hypotheses, and the goal's body as
  its statement. A citation of the conclusion inside it is a recursive
  call, which ``termination_by`` with the measure lanky finds
  (:func:`measure`) has Lean check is closer to a base case. The theorem
  itself is ``Lanky.<name>``, proved by applying the claim.
- ``if c:`` is ``by_cases``. A branch whose condition fixes integers, ``n ==
  1`` or ``a + b == 0`` among naturals, substitutes them.
- A fact at a point is the hypothesis applied to the values, each condition
  closed by ``omega``, or, over the reals, by the first of a few rules. A fact
  cited by its name alone is applied at the point found by matching it
  against the step it supports, a link or the case's claim, and the terms
  of the step's other facts (:func:`lanky.matching.single_point`).
- ``assert x == y == z, by(f, g)`` is a ``have`` of ``x = z``, proved by a
  ``calc``, a link to a step, each link closed from the facts of the
  ``assert`` that fit it; it is known for the rest of its case, and every
  later step of the case may use it. ``by(...)`` is ``sorry``.
- ``yield by(f, g)`` and ``return by(f, g)`` are one step: ``exact``, or
  ``linear_combination`` with multipliers Python finds (:mod:`lanky.induction`),
  or ``linarith`` and ``nlinarith`` with the facts, in Mathlib; ``exact``,
  ``omega`` after the indices are normalized, or ``grind``, in core Lean.
  Where a step the case asserted starts at the claim's left side, the step
  is the rest of the way, from where that one ended. A case closed with
  ``by()`` is lanky's whole-goal closers on it, after the steps it
  asserted.
- The compiler adds what a reader never writes: that an integer denominator
  the case shows is not zero is not zero in the field (:func:`nonzero_lines`),
  and the shift ``n.toNat = (n - 1).toNat + 1`` where a fact has the power one
  order down (:func:`shift_lines`).
- A cited theorem is restated as a hypothesis of the command, from the text
  its own command proved where there is one (:func:`cited_text`), and the
  proof rests on it in the ledger.
- The command ends with ``#print axioms``, whose answer is read positively
  (:func:`lanky.proofs.report.audit`).

Every emitted line, and every condition's ``by`` inside one, records the
Python line it came from (:class:`Origin`), so a message Lean gives at a
position is reported at the line the user wrote, in lanky's notation.
"""

from __future__ import annotations

from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field, replace
from typing import Any

import pymbolic.primitives as prim

from lanky.audit import audit_lines
from lanky.citations import Citation, Premise
from lanky.induction import substitute
from lanky.lean import (
    ELABORATION_OPTIONS,
    ROOT_NAMES,
    LeanStatement,
    UnsupportedTerm,
    codomain_bound,
    lean_identifier,
    number_type,
    proof_exponents,
    render_prop,
    render_term,
    statement_of,
)
from lanky.matching import FamilyValue, _affine, implied, instantiate, same
from lanky.prelude import FinType, FnType, Refined
from lanky.proofs.cases import (
    Shape,
    integer_sort,
    negated,
    offset_of,
    pins,
    shape_of,
)
from lanky.proofs.trace import (
    Asserted,
    ClaimDef,
    Given,
    Leaf,
    LinkStep,
    Node,
    Proof,
    ProofError,
    Question,
    TracedChain,
)
from lanky.terms import (
    Add,
    Comparison,
    Elementary,
    Forall,
    LogicalAnd,
    Var,
    conjuncts,
    init_args,
    render,
)

__all__ = [
    "Command",
    "Instance",
    "Measure",
    "Origin",
    "Step",
    "cited_text",
    "compile_proof",
    "measure",
    "nonzero_lines",
    "shift_lines",
]

#: The heartbeats one step may take, so that a stray ``nlinarith`` cannot spend
#: the command's whole time.
STEP_HEARTBEATS = 400000

#: What a link's relation is in Lean.
_LEAN_RELATION = {"==": "=", "<=": "≤", "<": "<", ">=": "≥", ">": ">", "!=": "≠"}


def _shown(value: Any) -> str:
    """A value as an outline writes it: a family's value as the ``lambda`` that would give it."""
    from lanky.proofs.trace import shown

    return shown(value)


# {{{ what an emitted line came from


@dataclass(frozen=True, eq=False)
class Origin:
    """Where an emitted piece of Lean came from, for a message Lean gives there.

    Attributes:
        kind: What it is: ``split``, ``pin``, ``cite``, ``condition``,
            ``step``, ``routine``, ``measure``, ``main``, ``statement``.
        line: The Python line it came from, when there is one.
        detail: What the report needs to say about it, in lanky's terms.
    """

    kind: str
    line: int | None
    detail: Mapping[str, Any] = field(default_factory=dict)


@dataclass(eq=False)
class _Line:
    """One emitted line, where it came from, and the columns of the conditions in it."""

    text: str
    origin: Origin | None = None
    spans: tuple[tuple[int, int, Origin], ...] = ()


def _indented(lines: list[_Line], first: str, rest: str) -> list[_Line]:
    """``lines`` with ``first`` before the first and ``rest`` before the others."""
    out = []
    for index, line in enumerate(lines):
        prefix = first if index == 0 else rest
        shift = len(prefix)
        out.append(
            _Line(
                prefix + line.text,
                line.origin,
                tuple((start + shift, end + shift, origin) for start, end, origin in line.spans),
            )
        )
    return out


@dataclass(frozen=True, eq=False)
class Instance:
    """A fact as one step uses it: the citation, the part, the point, and what it says there."""

    citation: Citation
    part: int
    values: tuple[Any, ...]
    body: Any
    lean_name: str


@dataclass(frozen=True, eq=False)
class Step:
    """A step as the report needs it: where it is, its claim, and the facts at their points.

    Attributes:
        leaf: The case it closes, for a ``yield`` or a ``return``; ``None``
            for a step an ``assert`` states.
        claim: What it shows.
        instances: The facts at their points: those its ``by(...)`` gives,
            then the steps the case asserted before it, in Lean's context
            already (each with an :class:`~lanky.proofs.trace.Asserted` for
            its citation's source).
        conditions: The case's conditions, each with the line of its ``if``.
        types: The sort of every name in scope.
        multipliers: What Python found to combine the instances into the
            claim, where it found anything.
        line: The line of a link of an ``assert``.
        owner: The :class:`~lanky.proofs.trace.Leaf` or the
            :class:`~lanky.proofs.trace.Asserted` it belongs to.
    """

    leaf: Leaf | None
    claim: Any
    instances: tuple[Instance, ...]
    conditions: tuple[tuple[Any, int], ...]
    types: Mapping[str, Any]
    multipliers: tuple[Any, ...] | None = None
    line: int | None = None
    owner: Any = None

    @property
    def where(self) -> int | None:
        """The Python line of the step: a link's own, the ``assert``'s, or the ``yield``'s."""
        if self.line is not None:
            return self.line
        owner = self.owner if self.owner is not None else self.leaf
        return getattr(owner, "line", None)

    @property
    def asserted(self) -> Asserted | None:
        """The ``assert`` the step belongs to, if it is one's."""
        return self.owner if isinstance(self.owner, Asserted) else None


@dataclass(frozen=True, eq=False)
class Measure:
    """What gets smaller at each call of the claim: the ``termination_by`` and how it reads.

    Attributes:
        kind: ``down`` for an argument that gets smaller, ``up`` for one that
            climbs toward a bound, ``lex`` for a pair, the first smaller or
            the same with the second smaller.
        names: The parameters it is on.
        bound: The bound an ``up`` measure climbs toward, as a term.
        said: How the ledger says it: ``induction on a``.
    """

    kind: str
    names: tuple[str, ...]
    bound: Any = None
    said: str = ""


@dataclass(eq=False)
class Command:
    """The Lean command a written proof compiles to, and how to read Lean's answer to it.

    Attributes:
        source: The command.
        lines: Each line of it, with where it came from.
        declared: The theorem's Lean name, ``Lanky.<name>``.
        mathlib: Whether it is written for Lean with Mathlib.
        measure: What the claim's recursion is on, when it recurses.
        summary: How the ledger says the proof: ``induction on a, 3 cases, 3 steps``.
        steps: Each ``return`` with facts, and each link of a chain, as the
            report reads it.
        cited: The theorems the proof cites, restated as hypotheses, and the
            theorems their own proofs cited (:func:`cited_text`).
        restated: Each of those as ``(name, fact id, text, term)``: the text
            the command restates it as, which has to be the text its own
            command proved where one was kept for its term ``term``
            (:meth:`lanky.citations.ProvedTexts.mismatch`).
        as_cited: The text a proof that cites this theorem restates, which the
            command proves as ``Lanky.<name>.as_cited``; ``None`` for none.
        audited: The theorems the command's axiom audit asks about.
        holes: The Python lines of the steps left open, ``by(...)``.
        outline: The proof's steps as ``lanky check --steps`` prints them:
            ``(line, case, left, relation, term, reason)``.
    """

    source: str
    lines: list[_Line]
    declared: str
    mathlib: bool
    measure: Measure | None
    summary: str
    steps: list[Step]
    cited: list[Any]
    restated: tuple[tuple[str, str, str, Any], ...] = ()
    as_cited: str | None = None
    audited: tuple[str, ...] = ()
    holes: tuple[int, ...] = ()
    outline: list[tuple[int | None, str, str, str, str, str]] = field(default_factory=list)

    @property
    def rests_on(self) -> list[str]:
        """The ledger ids of the theorems the command restates, premises included, each once."""
        found = (getattr(theorem, "fact_id", None) for theorem in self.cited)
        return list(dict.fromkeys(identifier for identifier in found if identifier))

    @property
    def hole_lines(self) -> tuple[int, ...]:
        """The lines of the command its holes' ``sorry`` are on, counted from 1."""
        return tuple(
            index + 1
            for index, line in enumerate(self.lines)
            if line.origin is not None and line.origin.kind == "hole"
        )

    def origin_at(self, line: int | None, column: int | None) -> Origin | None:
        """Where the Lean at ``line`` (from 1) and ``column`` (from 0) came from.

        A condition's span holds the column when one does; else the line's
        own origin; else the nearest line above with one, since Lean gives
        some messages at the start of the tactic block they are about.
        """
        if line is None or not 1 <= line <= len(self.lines):
            return None
        emitted = self.lines[line - 1]
        if column is not None:
            inside = [
                (end - start, origin)
                for start, end, origin in emitted.spans
                if start <= column < end
            ]
            if inside:
                return min(inside, key=lambda pair: pair[0])[1]
        if emitted.origin is not None:
            return emitted.origin
        for above in range(line - 2, -1, -1):
            if self.lines[above].origin is not None:
                return self.lines[above].origin
        return None


# }}}


# {{{ names


class _Names:
    """Names drawn fresh from those a command already uses."""

    def __init__(self, taken: set[str]) -> None:
        self.used = set(taken)

    def fresh(self, stem: str) -> str:
        """``stem``, or ``stem_1`` and on, whichever no name in use is."""
        name = stem
        index = 1
        while name in self.used:
            name = f"{stem}_{index}"
            index += 1
        self.used.add(name)
        return name

    def numbered(self, stem: str) -> str:
        """``stem_1``, or ``stem_2`` and on, whichever no name in use is."""
        index = 1
        while f"{stem}_{index}" in self.used:
            index += 1
        name = f"{stem}_{index}"
        self.used.add(name)
        return name

    def copy(self) -> _Names:
        """Another set of names, drawn from those in use here and apart from them afterwards."""
        return _Names(set(self.used))


def _mentioned(term: Any) -> set[str]:
    """Every name a term mentions, bound or free."""
    from lanky.lean import _mentioned as mentioned

    return set(mentioned(term))


def _given_names(theorem: Any, names: _Names) -> dict[str, list[str]]:
    """The Lean name of each hypothesis, a name per part of one written ``p & q``.

    A hypothesis keeps its Python name, ``pde``; the parts of ``stored: p &
    q`` are ``stored_1`` and ``stored_2``. A name that would mean something
    else in Lean, a root name such as ``Real`` or the namespace ``Lanky``, or
    one a variable has, is drawn afresh; a Lean keyword is quoted where it is
    printed (:func:`lanky.lean.lean_identifier`).
    """
    out: dict[str, list[str]] = {}
    for name, prop in theorem.hypotheses:
        parts = conjuncts(prop) or (prop,)
        stem = f"{name}_" if name in ROOT_NAMES or name == "Lanky" else name
        if len(parts) == 1:
            out[name] = [names.fresh(stem)]
        else:
            out[name] = [names.fresh(f"{stem}_{index}") for index in range(1, len(parts) + 1)]
    return out


# }}}


# {{{ statements with the Python names


@dataclass(frozen=True, eq=False)
class _Param:
    """One parameter of a printed theorem, with what it is.

    ``kind`` is ``binder``; ``given`` for a hypothesis of the theorem (``name``
    is then the hypothesis's Python name in ``given``); ``guard`` for a
    conjunct of the goal's guard; ``domain`` for a guard a binder's domain
    gives; ``bound`` for a family's codomain bound; ``cited`` for a restated
    theorem.
    """

    binder: bool
    lean: str
    kind: str
    var: str | None = None
    term: Any = None
    given: str | None = None
    cited: Any = None


def _classified(
    statement: LeanStatement, roles: Sequence[tuple[str, str | None, str | None]], names: _Names
) -> tuple[LeanStatement, list[_Param]]:
    """``statement`` with its hypotheses named by ``roles``, and its parameters classified.

    ``roles`` holds one ``(kind, python name, lean name)`` per conjunct of the
    term's guard, in order: ``("given", "pde", "pde")`` or ``("guard", None,
    None)``. A guard's and a domain guard's names are drawn fresh.
    """
    bounds = {hypothesis: family for family, hypothesis in statement.codomain_bounds}
    terms = statement.hypothesis_terms or (None,) * len(statement.hypotheses)
    anchors = statement.anchors or (len(statement.binders),) * len(statement.hypotheses)
    renamed: list[tuple[str, str]] = []
    kinds: list[_Param] = []
    guard_index = 0
    counted: dict[int, int] = {}
    from lanky.induction import domain_conditions

    for index, ((name, text), term) in enumerate(zip(statement.hypotheses, terms, strict=True)):
        if term is not None:
            kind, given, lean = roles[guard_index]
            guard_index += 1
            if kind == "given":
                assert lean is not None
                new = lean
            else:
                new = names.fresh("hguard")
            renamed.append((lean_identifier(new), text))
            kinds.append(_Param(False, lean_identifier(new), kind, term=term, given=given))
            continue
        if name in bounds:
            family = bounds[name]
            new = names.fresh(f"h{family}_bound")
            renamed.append((lean_identifier(new), text))
            sort = statement.types.get(family)
            kinds.append(
                _Param(
                    False,
                    lean_identifier(new),
                    "bound",
                    var=family,
                    term=codomain_bound(Var(family), sort) if sort is not None else None,
                )
            )
            continue
        anchor = anchors[index]
        var = statement.variables[anchor - 1]
        position = counted.get(anchor, 0)
        counted[anchor] = position + 1
        guards = domain_conditions(Var(var), statement.types[var])
        new = names.fresh(f"h{var}" if position == 0 else f"h{var}_{position}")
        renamed.append((lean_identifier(new), text))
        kinds.append(
            _Param(
                False,
                lean_identifier(new),
                "domain",
                var=var,
                term=guards[position] if position < len(guards) else None,
            )
        )
    named = replace(
        statement,
        hypotheses=tuple(renamed),
        codomain_bounds=tuple(
            (family, renamed[index][0])
            for index, (hypothesis, _) in enumerate(statement.hypotheses)
            for family in [bounds.get(hypothesis)]
            if family is not None
        ),
    )
    params: list[_Param] = []
    for hypothesis, index in named._parameters():
        if hypothesis:
            params.append(kinds[index])
        else:
            var = named.variables[index]
            params.append(_Param(True, named.binders[index][0], "binder", var=var))
    return named, params


def _with_cited(
    statement: LeanStatement, params: list[_Param], cited: list[tuple[str, str, Any]]
) -> tuple[LeanStatement, list[_Param]]:
    """``statement`` with each cited theorem restated as a hypothesis after the others."""
    if not cited:
        return statement, params
    anchors = statement.anchors or (len(statement.binders),) * len(statement.hypotheses)
    terms = statement.hypothesis_terms or (None,) * len(statement.hypotheses)
    added = tuple((lean_identifier(lean), text) for lean, text, _ in cited)
    named = replace(
        statement,
        hypotheses=(*statement.hypotheses, *added),
        hypothesis_terms=(*terms, *(None,) * len(added)),
        anchors=(*anchors, *(len(statement.binders),) * len(added)),
    )
    more = [
        _Param(False, lean_identifier(lean), "cited", cited=theorem) for lean, _, theorem in cited
    ]
    return named, [*params, *more]


def cited_text(theorem: Any, mathlib: bool) -> str:
    """The statement a cited theorem is restated as, a hypothesis of the citing command.

    The text the theorem's own command proved, ``Lanky.<name>.as_cited``,
    byte for byte, where the check recorded one (:func:`lanky.citations.proved_texts`,
    which :func:`lanky.proofs.check_written_proofs` sets from the Lean
    oracle's texts): a citation restates only what Lean proved of the
    theorem it names, and only while the theorem's term is the one that
    text was proved for. Where none was recorded (a theorem only tested, an
    axiom, one whose Lean attempt failed, one changed since), the statement
    printed from its term, trusting the printer, as every citation did
    before; the ledger bounds the citing proof by what it cites. The two are the same
    proposition, printed by one function (:attr:`lanky.lean.LeanStatement.as_cited`).

    Raises:
        UnsupportedTerm: If the printer cannot state the cited theorem.
    """
    from lanky.citations import proved_text

    found = proved_text(getattr(theorem, "fact_id", None), getattr(theorem, "term", None))
    if found is not None:
        return found.text
    return statement_of(theorem.term, theorem.__name__, mathlib=mathlib).proposition


def _cited_premises(theorem: Any, mathlib: bool, names: _Names) -> Shape:
    """A cited theorem's shape as its restated text is applied: its parameters, then its goal's."""
    statement = statement_of(theorem.term, theorem.__name__, mathlib=mathlib)
    goal_term = statement.goal_term
    roles = [("guard", None, None)] * sum(
        1 for term in (statement.hypothesis_terms or ()) if term is not None
    )
    _named, params = _classified(statement, roles, _Names(set(names.used)))
    binders: list[tuple[Var, Any]] = []
    premises: list[tuple[str, Any]] = []
    for param in params:
        if param.binder:
            binders.append((Var(param.var), statement.types[param.var]))
            premises.append(("value", param.var))
        else:
            premises.append(("proof", param.term))
    inner = shape_of(goal_term)
    return Shape(tuple(binders) + inner.binders, tuple(premises) + inner.premises, inner.body)


# }}}


# {{{ the measure


#: How far a value is above a variable: ``-2`` for ``a - 2`` (:func:`.cases.offset_of`).
_change = offset_of


def _upper_bound(name: str, domain: Any, conditions: Sequence[Any]) -> Any:
    """What a parameter is below or at, as a term, read off its domain and the claim's conditions.

    For a measure that climbs: ``k < p`` or ``k <= p`` among the conditions,
    or ``Fin[p]``, gives ``p``, and ``(p - k).toNat`` gets smaller as ``k``
    climbs.
    """
    from lanky.terms import free_variables

    for condition in conditions:
        if not isinstance(condition, prim.Comparison):
            continue
        left, operator, right = condition.left, condition.operator, condition.right
        if isinstance(right, prim.Variable) and right.name == name:
            left, right = right, left
            operator = {"<": ">", "<=": ">=", ">": "<", ">=": "<="}.get(operator, operator)
        if not (isinstance(left, prim.Variable) and left.name == name):
            continue
        if name in free_variables(right):
            continue
        if operator == "<=":
            return right
        if operator == "<":
            return right - 1
    base = domain
    while isinstance(base, Refined):
        base = base.base
    if isinstance(base, FinType):
        return base.bound - 1
    return None


def measure(claim: ClaimDef, calls: Sequence[Citation], conditions: Sequence[Any]) -> Measure:
    """What gets smaller at every call of the claim (see :class:`Measure`).

    Tried in order: one argument that gets smaller at every call, ``a.toNat``;
    one that climbs at every call toward a bound the claim's conditions give
    it, ``(p - k).toNat``; and a pair, the first smaller or the same with the
    second smaller, ``(a.toNat, b.toNat)``. Only integer parameters count.

    Raises:
        ProofError: If no measure fits, at the first call no argument of
            which is smaller.
    """
    params = list(claim.params)
    integer = [
        name for name, domain in zip(params, claim.domains, strict=True) if integer_sort(domain)
    ]
    changes = [
        {name: _change(call.values[params.index(name)], name) for name in integer} for call in calls
    ]
    for name in integer:
        if all(change[name] is not None and change[name] <= -1 for change in changes):
            return Measure("down", (name,), said=f"induction on {name}")
    for name in integer:
        if all(change[name] is not None and change[name] >= 1 for change in changes):
            domain = claim.domains[params.index(name)]
            bound = _upper_bound(name, domain, conditions)
            if bound is not None:
                return Measure(
                    "up", (name,), bound=bound, said=f"induction on {name}, up to {render(bound)}"
                )
    for first in integer:
        for second in integer:
            if first == second:
                continue
            if all(
                (change[first] is not None and change[first] <= -1)
                or (change[first] == 0 and change[second] is not None and change[second] <= -1)
                for change in changes
            ):
                return Measure("lex", (first, second), said=f"induction on ({first}, {second})")
    offending = next(
        (
            (call, change)
            for call, change in zip(calls, changes, strict=True)
            if not any(value is not None and value <= -1 for value in change.values())
        ),
        (calls[0], changes[0]),
    )
    call = offending[0]
    if len(integer) == 1:
        which = f"{integer[0]} is not smaller than at ({', '.join(params)})"
    elif len(integer) == 2:
        which = f"neither {integer[0]} nor {integer[1]} is smaller than at ({', '.join(params)})"
    elif integer:
        which = f"none of {', '.join(integer)} is smaller than at ({', '.join(params)})"
    else:
        which = "the claim has no integer variable to be smaller"
    return_line = call.line
    raise ProofError(
        "measure",
        f"{call.text()} is not at smaller values: {which}",
        return_line,
        fix=(
            "cite the conclusion where one value is smaller, as a - 2, and stays a natural "
            "number, or loop over a bounded domain with reversed(...) for one that climbs"
        ),
    )


# }}}


# {{{ what the compiler adds, which the proof never writes


@dataclass
class _Scope:
    """What is in scope where a step is compiled, as what the compiler adds reads it.

    Attributes:
        types: The lanky type of every name in scope: the theorem's
            variables and the claim's, as the statement printer reads them.
        facts: What the case knows, as propositions over those names: the
            claim's conditions and each branch's (``a >= 2``, ``not (n == 1)``).
        mathlib: Whether the command is for a Lean with Mathlib.
        shadowed: The root names a variable is named like
            (:attr:`lanky.lean.LeanStatement.shadowed`).
        taken: Every name the declaration uses so far, which a fresh name
            avoids; the compiler adds the names it introduces.
    """

    types: Mapping[str, Any]
    facts: tuple[Any, ...] = ()
    mathlib: bool = True
    shadowed: frozenset[str] = frozenset()
    taken: set[str] = field(default_factory=set)

    def fresh(self, stem: str) -> str:
        """A name like ``stem`` that nothing in the declaration uses yet, then taken."""
        name, index = stem, 1
        while name in self.taken or name in self.types:
            name = f"{stem}_{index}"
            index += 1
        self.taken.add(name)
        return name

    def render(
        self,
        term: Any,
        atomic: bool = False,
        types: Mapping[str, Any] | None = None,
        sort: Any = None,
    ) -> str:
        """A term as Lean source, in the scope's dialect, its natural exponents as ``.toNat``.

        A family's value the higher-order rule bound (:class:`FamilyValue`) is
        a ``fun``, its parameters typed by ``sort``, the family's own type, so
        that ``k ↦ r ** k`` for an ``f: Fn[Nat, Real]`` is ``(fun k => r ^
        k.toNat)``.
        """
        scope = dict(self.types if types is None else types)
        if isinstance(term, FamilyValue):
            inner = dict(scope)
            current = _unrefined(sort)
            for var in term.parameters:
                if not isinstance(current, FnType):
                    break
                inner[var.name] = current.domain
                current = _unrefined(current.codomain)
            with proof_exponents(lambda exponent: self.natural(exponent)):
                text = render_term(term.body, inner, self.mathlib, self.shadowed)
            names = " ".join(var.name for var in term.parameters)
            return f"(fun {names} => {text})"
        with proof_exponents(lambda exponent: self.natural(exponent)):
            return render_term(term, scope, self.mathlib, self.shadowed, atomic=atomic)

    def natural(self, term: Any) -> bool:
        """Whether the case shows ``term`` is an integer at least ``0``."""
        return implied(Comparison(term, ">=", 0), self.facts, self.types) is True

    def ring(self, *terms: Any) -> str:
        """The Lean type the terms are numbers of: ``Int``, ``ℝ`` or ``ℂ``, the widest."""
        kinds = []
        for term in terms:
            try:
                kinds.append(number_type(term, self.types, mathlib=self.mathlib))
            except Exception:  # noqa: BLE001 - a term the printer cannot read is an integer to it
                kinds.append("Int")
        for wide in ("ℂ", "ℝ"):
            if wide in kinds:
                return wide
        return kinds[0] if kinds else "Int"


def _denominators(term: Any) -> list[Any]:
    """The denominators of the true divisions in ``term``, outermost first."""
    found: list[Any] = []
    stack = [term]
    while stack:
        node = stack.pop()
        if isinstance(node, FamilyValue):
            stack.append(node.body)
            continue
        if isinstance(node, prim.Quotient):
            found.append(node.denominator)
        if isinstance(node, prim.ExpressionNode):
            stack.extend(init_args(node))
        elif isinstance(node, tuple):
            stack.extend(node)
    return found


def nonzero_lines(terms: Iterable[Any], scope: _Scope) -> list[str]:
    """The facts that the denominators of ``terms`` are not zero, which ``field_simp`` needs.

    An integer denominator the case shows is not zero, ``n`` where ``n >= 1``
    or ``n - 1`` where ``n >= 2``, is stated in the field the step is in, by
    ``exact_mod_cast`` and ``omega``, and pushed through the cast, so that the
    context has ``(n : ℂ) - 1 ≠ 0`` in the form ``ring_nf`` writes it. A
    modulus squared, ``real(alpha * conj(alpha))``, is not zero by the normSq
    rule, where a hypothesis says ``alpha`` is not. A real or complex
    denominator is left to the hypotheses, which ``field_simp`` reads. Every
    line is tried, so one that does not hold costs nothing.
    """
    if not scope.mathlib:
        return []
    terms = list(terms)
    sides = [side for term in terms for side in _sides(term)]
    ring = scope.ring(*sides) if sides else "ℝ"
    if ring not in ("ℝ", "ℂ"):
        ring = "ℝ"
    lines: list[str] = []
    seen: list[Any] = []
    for term in terms:
        for denominator in _denominators(term):
            if isinstance(denominator, int | float) or any(
                same(denominator, other) for other in seen
            ):
                continue
            seen.append(denominator)
            if _is_modulus_squared(denominator):
                inner = scope.render(denominator.argument.children[0], atomic=True)
                name = scope.fresh("nz")
                lines.append(
                    f"try have {name} : Complex.re ({inner} * (starRingEnd ℂ) {inner}) ≠ 0 := by "
                    f"rw [Complex.mul_conj, Complex.ofReal_re]; "
                    f"exact (Complex.normSq_pos.mpr (by assumption)).ne'"
                )
                continue
            try:
                kind = number_type(denominator, scope.types, mathlib=True)
            except Exception:  # noqa: BLE001 - a denominator the printer cannot read gets nothing
                continue
            if (
                kind != "Int"
                or implied(Comparison(denominator, "!=", 0), scope.facts, scope.types) is not True
            ):
                continue
            text = scope.render(denominator)
            name = scope.fresh("nz")
            lines.append(
                f"try have {name} : (({text} : Int) : {ring}) ≠ 0 := by "
                f"exact_mod_cast (show ({text} : Int) ≠ 0 by omega)"
            )
            lines.append(f"try push_cast at {name}")
    return lines


def _sides(term: Any) -> tuple[Any, ...]:
    """The two sides of a comparison, or the term itself: what has a number type."""
    if isinstance(term, prim.Comparison):
        return (term.left, term.right)
    return (term,)


def _is_modulus_squared(term: Any) -> bool:
    """Whether a term is ``real(z * conj(z))``."""
    if not (isinstance(term, Elementary) and term.function == "real"):
        return False
    inner = term.argument
    if not (isinstance(inner, prim.Product) and len(inner.children) == 2):
        return False
    first, second = inner.children
    return (
        isinstance(second, Elementary)
        and second.function == "conj"
        and same(first, second.argument)
    )


def _powers(term: Any) -> list[prim.Power]:
    """Every power in a term."""
    found: list[prim.Power] = []
    stack = [term]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Power):
            found.append(node)
        if isinstance(node, prim.ExpressionNode):
            stack.extend(init_args(node))
        elif isinstance(node, tuple):
            stack.extend(node)
    return found


def shift_lines(goal: Any, facts: Sequence[Any], scope: _Scope) -> list[str]:
    """The rewrites that put the goal's powers in the exponents its facts have.

    Where the goal has ``x ** n`` for a natural ``n`` (``x ^ n.toNat`` in Lean)
    and a fact has the same base at ``n - s``, ``s`` a positive number the
    case shows ``n - s >= 0`` for, the goal is rewritten with ``n.toNat = (n -
    s).toNat + s`` and ``pow_succ`` (``pow_add`` for ``s > 1``), so that ``x ^
    (n - s).toNat`` is an atom of both. One rewrite per exponent, the
    smallest shift first.
    """
    if not scope.mathlib:
        return []
    shifts: dict[str, int] = {}
    fact_powers = [power for fact in facts for power in _powers(fact)]
    for power in _powers(goal):
        exponent = power.exponent
        if not isinstance(exponent, prim.Variable) or exponent.name not in scope.types:
            continue
        for other in fact_powers:
            if not same(other.base, power.base):
                continue
            offset = _offset(other.exponent, exponent.name)
            if offset is None or offset <= 0:
                continue
            if not scope.natural(exponent - offset):
                continue
            current = shifts.get(exponent.name)
            if current is None or offset < current:
                shifts[exponent.name] = offset
    lines = []
    for name, offset in sorted(shifts.items()):
        lemma = "pow_succ" if offset == 1 else "pow_add"
        variable = scope.render(Var(name), atomic=True)
        lines.append(
            f"rw [show {variable}.toNat = ({variable} - {offset}).toNat + {offset} by omega, "
            f"{lemma}]"
        )
    return lines


def _offset(exponent: Any, name: str) -> int | None:
    """``s`` where ``exponent`` is ``name - s``; ``None`` for anything else."""
    form = _affine(exponent)
    if form is None:
        return None
    variables = {key: value for key, value in form.items() if key and value != 0}
    if variables != {name: 1}:
        return None
    constant = form.get("", 0)
    if constant.denominator != 1:
        return None
    return int(-constant)


def _unrefined(sort: Any) -> Any:
    """A sort with its refinements taken off."""
    while isinstance(sort, Refined):
        sort = sort.base
    return sort


# }}}


# {{{ emitting the proof


@dataclass(eq=False)
class _Context:
    """What the emitter knows at a point of the tree.

    ``guards`` are the claim's own conditions, the goal's guard at its
    variables; ``conditions`` the case splits on the path, each with the line
    of its ``if``; ``facts`` everything that holds, for deciding;
    ``questions`` the splits on the path, for the outline's case labels;
    ``asserted`` the steps the case asserted so far, each a fact in Lean's
    context under its name, which every later step of the case may use.
    """

    pins: dict[str, Any]
    conditions: list[tuple[Any, int]]
    facts: list[Any]
    guards: tuple[Any, ...] = ()
    questions: list[Question] = field(default_factory=list)
    asserted: list[Instance] = field(default_factory=list)

    def branch(self, question: Question, holds: Any) -> _Context:
        """The context of one branch of a split, its condition known."""
        return _Context(
            dict(self.pins),
            [*self.conditions, (holds, question.line)],
            [*self.facts, holds],
            self.guards,
            [*self.questions, replace(question, answer=holds is question.prop)],
            list(self.asserted),
        )


class _Compiler:
    """The compile of one traced proof (see :func:`compile_proof`)."""

    def __init__(self, proof: Proof, mathlib: bool, as_cited: str | None = None) -> None:
        self.proof = proof
        self.as_cited = as_cited
        self.theorem = proof.theorem
        self.mathlib = mathlib
        theorem = proof.theorem
        # the conclusion as the proof closes it: nested for levels it loops over taken as one
        self.goal = proof.conclusion
        taken = _mentioned(theorem.term) | {name for name, _ in theorem.variables}
        if proof.claim is not None:
            taken |= set(proof.claim.params)
        self.names = _Names(taken | {"Lanky"})
        self.given = _given_names(theorem, self.names)
        self.cited: list[tuple[str, str, Any]] = []
        for cited in proof.cited:
            lean = self.names.fresh(cited.__name__)
            try:
                text = cited_text(cited, mathlib)
            except UnsupportedTerm as exc:
                raise ProofError(
                    "unsupported",
                    f"the proof cites {cited.__name__}, which Lean cannot state: {exc}",
                    None,
                ) from None
            self.cited.append((lean, text, cited))
        self._premises(list(proof.cited))
        self.steps: list[Step] = []
        self.lines: list[_Line] = []
        self.outline: list[tuple[int | None, str, str, str, str, str]] = []
        # the case the next row of the outline is in; whether a step makes a row of its own
        self._case = ""
        self._outlining = True
        # the cases lanky was left to close
        self.routine = 0

    def _premises(self, theorems: list[Any]) -> None:
        """Restate the theorems the cited theorems' own proofs cited, after them (:class:`Premise`).

        Raises:
            ProofError: If a premise has no proved text, or the premises come
                round in a circle, naming them.
        """
        from lanky.citations import premises_of

        seen = {getattr(theorem, "fact_id", None) for theorem in theorems}
        stack: list[Premise] = []
        for theorem in theorems:
            identifier = getattr(theorem, "fact_id", None)
            if not identifier:
                continue
            try:
                stack.extend(premises_of(identifier, term=getattr(theorem, "term", None)))
            except ValueError as exc:
                raise ProofError(
                    "unsupported", f"the proof cites {theorem.__name__}: {exc}"
                ) from None
        while stack:
            premise = stack.pop(0)
            if premise.fact_id in seen:
                continue
            seen.add(premise.fact_id)
            lean = self.names.fresh(premise.__name__)
            self.cited.append((lean, premise.text, premise))
            stack.extend(premise.premises)

    # {{{ statements

    def _roles(self, goal_guards: Sequence[Any]) -> list[tuple[str, str | None, str | None]]:
        """One role per conjunct of a term's guard: the hypotheses', then the goal's guard's."""
        roles: list[tuple[str, str | None, str | None]] = []
        for name, prop in self.theorem.hypotheses:
            parts = conjuncts(prop) or (prop,)
            for index, _part in enumerate(parts):
                roles.append(("given", name, self.given[name][index]))
        roles += [("guard", None, None)] * len(goal_guards)
        return roles

    def main_statement(self) -> tuple[LeanStatement, list[_Param]]:
        """The theorem as the ladder prints it, its hypotheses under their Python names."""
        theorem = self.theorem
        statement = statement_of(theorem.term, theorem.__name__, mathlib=self.mathlib)
        # its own parameters' names are its own: the claim's tactic block never sees them
        names = self.names.copy() if self.proof.claim is not None else self.names
        named, params = _classified(statement, self._roles(()), names)
        return _with_cited(named, params, self.cited)

    def claim_statement(self) -> tuple[LeanStatement, list[_Param], Any]:
        """``Lanky.<name>.claim``: the goal's variables and guard made parameters."""
        theorem = self.theorem
        goal = self.goal
        binders = [(Var(name), sort) for name, sort in theorem.variables]
        goal_guards: list[Any] = []
        body = goal
        if isinstance(goal, Forall):
            binders += list(goal.binders)
            goal_guards = list(conjuncts(goal.guard))
            body = goal.body
        props = [
            part for _name, prop in theorem.hypotheses for part in (conjuncts(prop) or (prop,))
        ]
        guard_terms = props + goal_guards
        guard: Any = None
        if len(guard_terms) == 1:
            guard = guard_terms[0]
        elif guard_terms:
            guard = LogicalAnd(tuple(guard_terms))
        term = Forall(tuple(binders), body, guard)
        statement = statement_of(term, theorem.__name__, mathlib=self.mathlib)
        statement = replace(statement, name=f"{statement.name}.claim")
        named, params = _classified(statement, self._roles(goal_guards), self.names)
        named, params = _with_cited(named, params, self.cited)
        return named, params, body

    # }}}

    def compile(self) -> Command:
        """The command: the claim's theorem and the theorem's, or the theorem's alone."""
        proof = self.proof
        theorem = self.theorem
        main, main_params = self.main_statement()
        self.declared = main.declared_name
        lines: list[_Line] = []
        measured: Measure | None = None
        if proof.claim is not None:
            claim_statement, claim_params, body = self.claim_statement()
            self.claim_declared = claim_statement.declared_name
            self.claim_params = claim_params
            self.types = dict(claim_statement.types)
            self.shadowed = claim_statement.shadowed
            conditions = [
                param.term
                for param in claim_params
                if param.kind in ("guard", "given") and param.term is not None
            ]
            calls = proof.calls
            if calls:
                measured = measure(proof.claim, calls, conditions)
            base = [part for _name, prop in theorem.hypotheses for part in conjuncts(prop)]
            goal_guards = list(conjuncts(self.goal.guard)) if isinstance(self.goal, Forall) else []
            context = _Context({}, [], [*base, *goal_guards], tuple(goal_guards))
            tactic = self._node(proof.root, context, body)
            lines.append(_Line(ELABORATION_OPTIONS))
            lines += self._head(claim_statement, Origin("statement", proof.claim.line))
            lines += _indented(tactic, "  ", "  ")
            if measured is not None:
                lines += self._termination(measured, Origin("measure", proof.claim.line))
            lines.append(_Line(""))
            lines.append(_Line(ELABORATION_OPTIONS))
            lines += self._head(main, Origin("main", proof.claim.line))
            lines += _indented(self._apply_claim(main, claim_params), "  ", "  ")
        else:
            self.types = dict(main.types)
            self.shadowed = main.shadowed
            intro, body = self._intro(main)
            if isinstance(self.goal, Forall):
                for var, domain in self.goal.binders:
                    self.types[var.name] = domain
            base = [part for _name, prop in theorem.hypotheses for part in conjuncts(prop)]
            goal_guards = list(conjuncts(self.goal.guard)) if isinstance(self.goal, Forall) else []
            context = _Context({}, [], [*base, *goal_guards], tuple(goal_guards))
            tactic = intro + self._node(proof.root, context, body)
            lines.append(_Line(ELABORATION_OPTIONS))
            lines += self._head(main, Origin("statement", proof.lines[0]))
            lines += _indented(tactic, "  ", "  ")
        audited: tuple[str, ...] = (self.declared,)
        if self.as_cited is not None:
            lines.append(_Line(""))
            lines += self._as_cited(main_params)
            audited = (self.declared, f"{self.declared}.as_cited")
        lines.append(_Line(""))
        for line in audit_lines(audited).splitlines():
            lines.append(_Line(line, Origin("audit", proof.lines[0])))
        source = "\n".join(line.text for line in lines) + "\n"
        return Command(
            source=source,
            lines=lines,
            declared=self.declared,
            mathlib=self.mathlib,
            measure=measured,
            summary=self._summary(measured),
            steps=self.steps,
            cited=[theorem for _lean, _text, theorem in self.cited],
            restated=tuple(
                (
                    theorem.__name__,
                    getattr(theorem, "fact_id", None) or "",
                    text,
                    getattr(theorem, "term", None),
                )
                for _lean, text, theorem in self.cited
            ),
            as_cited=self.as_cited,
            audited=audited,
            holes=tuple(self.proof.holes),
            outline=self.outline,
        )

    def _as_cited(self, main_params: list[_Param]) -> list[_Line]:
        """``theorem Lanky.<name>.as_cited``: the text a citing proof restates, from the theorem.

        The text is the claim's, as the ladder's command states it
        (:attr:`lanky.lean.LeanStatement.as_cited`), so a theorem proved by
        its written proof is cited exactly as one lanky proved alone. The
        theorems the proof cites are its hypotheses, by their own texts, so
        that a citation of this one restates those too (:class:`Premise`).
        """
        origin = Origin("as_cited", self.proof.lines[0])
        head = f"theorem {self.declared}.as_cited"
        cited = [(lean_identifier(lean), text) for lean, text, _ in self.cited]
        if cited:
            head += " " + " ".join(f"({lean} : {text})" for lean, text in cited)
        own = [param for param in main_params if param.kind != "cited"]
        lines = [_Line(ELABORATION_OPTIONS), _Line(f"{head} :", origin)]
        if not own and not cited:
            lines.append(_Line(f"    {self.as_cited} :=", origin))
            lines.append(_Line(f"  {self.declared}", origin))
            return lines
        names = [self.names.fresh(f"x_{index}") for index in range(1, len(own) + 1)]
        lines.append(_Line(f"    {self.as_cited} := by", origin))
        if names:
            lines.append(_Line(f"  intro {' '.join(names)}", origin))
        arguments = " ".join([*names, *(lean for lean, _ in cited)])
        lines.append(_Line(f"  exact {self.declared} {arguments}", origin))
        return lines

    def _summary(self, measured: Measure | None) -> str:
        """``induction on a, 3 cases, 3 steps``: the proof, as the ledger says it."""
        leaves = self.proof.leaves
        cases = len(leaves)
        steps = len(self.steps)
        routine = self.routine
        holes = len(self.proof.holes)
        parts = []
        if measured is not None:
            parts.append(measured.said)
        if cases > 1:
            parts.append(f"{cases} cases")
        if steps or not routine:
            parts.append("1 step" if steps == 1 else f"{steps} steps")
        if routine:
            parts.append("1 routine" if routine == 1 else f"{routine} routine")
        if holes:
            parts.append("1 step left open" if holes == 1 else f"{holes} steps left open")
        text = ", ".join(parts)
        used = [theorem for _lean, _text, theorem in self.cited if not isinstance(theorem, Premise)]
        if used:
            here = getattr(self.theorem, "module", None)
            listing = _listing([theorem.__name__ for theorem in used])
            modules = {getattr(theorem, "module", None) for theorem in used}
            if len(modules) == 1 and next(iter(modules)) not in (None, here):
                listing += f" from {next(iter(modules))}"
            text += f", using {listing}"
        return text

    def _head(self, statement: LeanStatement, origin: Origin) -> list[_Line]:
        """``theorem Lanky.<name> <parameters> : <goal> := by``, as one line."""
        head = f"theorem {statement.declared_name}"
        if statement.parameters:
            head = f"{head} {statement.parameters}"
        return [_Line(f"{head} : {statement.goal} := by", origin)]

    def _termination(self, measured: Measure, origin: Origin) -> list[_Line]:
        """``termination_by`` with the measure, and ``decreasing_by`` where it needs one."""
        names = [lean_identifier(name) for name in measured.names]
        if measured.kind == "down":
            return [
                _Line(f"termination_by {names[0]}.toNat", origin),
                _Line("decreasing_by omega", origin),
            ]
        if measured.kind == "up":
            bound = render_term(measured.bound, self.types, self.mathlib, self.shadowed)
            return [
                _Line(f"termination_by ({bound} - {names[0]}).toNat", origin),
                _Line("decreasing_by omega", origin),
            ]
        return [_Line(f"termination_by ({names[0]}.toNat, {names[1]}.toNat)", origin)]

    def _intro(self, statement: LeanStatement) -> tuple[list[_Line], Any]:
        """``intro`` of the goal's variables and guard, and the goal's body under the names."""
        from lanky.lean import dialect
        from lanky.oracles.lean import _goal_intro

        goal = self.goal
        if not isinstance(goal, Forall):
            return [], goal
        with dialect(self.mathlib):
            names, variables, _guards, _naturals, introduced = _goal_intro(statement)
        renaming = {
            var.name: Var(introduced[var.name])
            for var in variables
            if introduced[var.name] != lean_identifier(var.name)
        }
        self.renaming = renaming
        origin = Origin("statement", self.proof.lines[0])
        return [_Line(f"intro {' '.join(names)}", origin)], substitute(goal.body, renaming)

    def _apply_claim(self, main: LeanStatement, claim_params: list[_Param]) -> list[_Line]:
        """The theorem's proof: introduce the goal's variables, and apply the claim to them."""
        from lanky.lean import dialect
        from lanky.oracles.lean import _goal_intro

        origin = Origin("main", self.proof.claim.line if self.proof.claim else None)
        lines: list[_Line] = []
        introduced: dict[str, str] = {}
        if isinstance(self.goal, Forall):
            with dialect(self.mathlib):
                names, _variables, _guards, _naturals, introduced = _goal_intro(main)
            lines.append(_Line(f"intro {' '.join(names)}", origin))
            taken = {
                *names,
                *(name for name, _ in main.binders),
                *(name for name, _ in main.hypotheses),
            }
            more = self._inner_intro(introduced, taken)
            if more:
                lines.append(_Line(f"intro {' '.join(more)}", origin))
        arguments = []
        for param in claim_params:
            if param.binder:
                arguments.append(introduced.get(param.var, lean_identifier(param.var)))
            elif param.kind in ("given", "cited"):
                arguments.append(param.lean)
            else:
                arguments.append("(by assumption)")
        lines.append(_Line(f"exact {self.claim_declared} {' '.join(arguments)}".rstrip(), origin))
        return lines

    def _inner_intro(self, introduced: dict[str, str], taken: set[str]) -> list[str]:
        """The names ``intro`` gives the nested ``for`` levels the proof loops over, past the first.

        The theorem's goal states them nested, ``∀ i, ... → ∀ a b, ... →``,
        and the claim takes them flat, so each level's variables are
        introduced with their domain's guards and the level's own guard
        after them, as the printer writes them; the claim is applied to the
        variables, and its guards are found by ``assumption``.
        """
        from lanky.lean import domain_guards
        from lanky.surface import levels

        claim = self.proof.claim
        depth = len(claim.levels) if claim is not None and claim.levels else 1
        found = levels(self.theorem.goal)[:depth]
        names: list[str] = []
        scope = dict(self.types)
        used = set(taken)

        def fresh(stem: str) -> str:
            name, index = stem, 1
            while name in used:
                name = f"{stem}_{index}"
                index += 1
            used.add(name)
            return name

        for binders, guard in found[1:]:
            for var, domain in binders:
                lean = fresh(lean_identifier(var.name))
                introduced[var.name] = lean
                names.append(lean)
                for _ in domain_guards(var, domain, scope, mathlib=self.mathlib):
                    names.append(fresh("hd"))
                scope[var.name] = domain
            for _ in conjuncts(guard):
                names.append(fresh("hg"))
        return names

    # {{{ the tree

    def _render(self, term: Any, context: _Context, atomic: bool = False) -> str:
        """A term, with the case's pins put in, as Lean source."""
        here = substitute(term, {**getattr(self, "renaming", {}), **context.pins})
        return render_term(here, self.types, self.mathlib, self.shadowed, atomic=atomic)

    def _prop(self, prop: Any, context: _Context) -> str:
        """A proposition, with the case's pins put in, as Lean source."""
        here = substitute(prop, {**getattr(self, "renaming", {}), **context.pins})
        return render_prop(here, self.types, self.mathlib, self.shadowed)

    def _node(self, node: Node, context: _Context, claim: Any) -> list[_Line]:
        """The tactic block of a node of the case tree: its steps, then its split or its end."""
        lines = self._items(node.items, context)
        if node.leaf is not None and node.question is None:
            return lines + self._leaf(node.leaf, context, claim)
        question = node.question
        assert question is not None
        name = self.names.numbered("case")
        origin = Origin("split", question.line, {"condition": question.prop})
        try:
            condition = self._prop(question.prop, context)
        except UnsupportedTerm as exc:
            raise ProofError(
                "unsupported",
                f"Lean cannot state the case split {render(question.prop)}: {exc}",
                question.line,
            ) from None
        lines.append(_Line(f"by_cases {lean_identifier(name)} : {condition}", origin))
        for answer, branch in ((True, node.then), (False, node.otherwise)):
            prop = question.prop
            holds = prop if answer else negated(prop)
            inner = context.branch(question, holds)
            body: list[_Line] = self._pins(holds, inner, question.line)
            if branch is None:
                # a path no run took: its condition contradicts the path to it
                body.append(_Line("exfalso", origin))
                body.append(_Line("omega", origin))
            else:
                self._case = _label_of(inner.questions)
                body += self._node(branch, inner, claim)
            lines += _indented(body, "· ", "  ")
        return lines

    def _pins(self, prop: Any, context: _Context, line: int) -> list[_Line]:
        """``have`` and ``subst`` for each integer the branch's equation fixes (:func:`pins`)."""
        here = substitute(prop, context.pins)
        local = list(self.proof.claim.params) if self.proof.claim is not None else []
        found = pins(here, self.types, [name for name in local if name not in context.pins])
        out: list[_Line] = []
        origin = Origin("pin", line, {"condition": prop})
        for name, value in found:
            pin = self.names.numbered("pin")
            text = render_term(value, self.types, self.mathlib, self.shadowed)
            out.append(
                _Line(
                    f"have {lean_identifier(pin)} : {lean_identifier(name)} = {text} := by omega",
                    origin,
                )
            )
            out.append(_Line(f"subst {lean_identifier(name)}", origin))
            context.pins[name] = value
            context.pins = {
                key: substitute(term, {name: value}) for key, term in context.pins.items()
            }
            context.asserted = [
                replace(instance, body=substitute(instance.body, {name: value}))
                for instance in context.asserted
            ]
        return out

    def _items(self, items: Sequence[Any], context: _Context) -> list[_Line]:
        """What a node holds before its split or its end: the steps asserted, the questions decided.

        A condition the path's facts decided made no split, and an equation
        among them that fixes integers fixes them here.
        """
        lines: list[_Line] = []
        for item in items:
            if isinstance(item, Question):
                lines += self._pins(item.condition, context, item.line)
                context.facts.append(item.condition)
            elif isinstance(item, Asserted):
                lines += self._asserted(item, context)
        return lines

    # }}}

    # {{{ a step asserted

    def _asserted(self, step: Asserted, context: _Context) -> list[_Line]:
        """``assert x == y == z, by(f, g)``: a ``have`` of each thing it states, known from then on.

        A chain of one link is that link's step; a longer one is a ``calc``,
        each link closed from the facts of the ``assert`` that fit it, a fact
        cited by name alone at the point that fits the link (and left out of
        a link it fits nowhere). Each is in Lean's context under its name for
        the rest of the case, as an :class:`Instance` every later step adds
        to its own facts.
        """
        lines: list[_Line] = []
        first_row = True
        for part in step.parts:
            name = self.names.numbered("step")
            origin = Origin("asserted", step.line, {"step": step})
            if isinstance(part, TracedChain):
                try:
                    statement = (
                        f"{self._step_term(part.start, context)} "
                        f"{_LEAN_RELATION[part.relation]} {self._step_term(part.end, context)}"
                    )
                except UnsupportedTerm as exc:
                    raise ProofError(
                        "unsupported", f"Lean cannot state the step: {exc}", step.line
                    ) from None
                lines.append(_Line(f"have {lean_identifier(name)} : {statement} := by", origin))
                before = len(self.steps)
                self._outlining = False
                try:
                    if len(part.links) == 1:
                        left, link = next(part.steps())
                        body = self._link(left, link, step, context)
                    else:
                        body = self._calc(part, step, context)
                finally:
                    self._outlining = True
                self._check_every_fact_fits(step, self.steps[before:])
                lines += _indented(body, "  ", "  ")
                self._outline_assert(step, part, self.steps[before:], first_row)
                prop = part.claim
            else:
                try:
                    statement = self._prop(part, context)
                except UnsupportedTerm as exc:
                    raise ProofError(
                        "unsupported", f"Lean cannot state the step: {exc}", step.line
                    ) from None
                lines.append(_Line(f"have {lean_identifier(name)} : {statement} := by", origin))
                goal = substitute(part, context.pins)
                if step.hole:
                    body = [_Line("sorry", Origin("hole", step.line, {"claim": goal}))]
                    self._outline_row(step.line, render(goal), "", "", "left open (by(...))")
                else:
                    self._outlining = False
                    try:
                        body, made = self._step(goal, step.facts, step, context, step.line)
                    finally:
                        self._outlining = True
                    self._outline_row(
                        step.line, render(goal), "", "", self._reason_text(made.instances)
                    )
                lines += _indented(body, "  ", "  ")
                prop = part
            first_row = False
            citation = Citation(step, None, step.line)
            context.asserted.append(Instance(citation, 0, (), substitute(prop, context.pins), name))
            context.facts.append(substitute(prop, context.pins))
        return lines

    def _check_every_fact_fits(self, step: Asserted, made: Sequence[Step]) -> None:
        """Refuse a fact of an ``assert`` cited by name alone that fits none of its links."""
        used = {id(instance.citation) for each in made for instance in each.instances}
        for citation in step.facts:
            if citation.values is not None or citation.is_claim or id(citation) in used:
                continue
            if isinstance(citation.source, Given):
                shapes = [shape_of(part) for part in citation.source.parts]
            else:
                shapes = [_cited_premises(citation.source, self.mathlib, self.names)]
            if not any(shape.binders for shape in shapes):
                continue
            unknowns = ", ".join(var.name for var, _ in shapes[0].binders)
            raise ProofError(
                "no-point",
                f"{citation.name}: no single point of {citation.name} fits a link of this "
                f"step; write its point, as {citation.name}({unknowns}) with the values meant",
                step.line,
                fix=f"{citation.name}({unknowns})",
            )

    def _outline_assert(
        self, step: Asserted, chain: TracedChain, made: Sequence[Step], first: bool
    ) -> None:
        """The outline's rows of an asserted chain: the first with reasons, then the rest."""
        reason = (
            "left open (by(...))"
            if step.hole
            else self._reason_text([instance for each in made for instance in each.instances])
        )
        for index, (left, link) in enumerate(chain.steps()):
            if index == 0:
                self._outline_row(
                    step.line if first else None,
                    render(left),
                    link.relation,
                    render(link.term),
                    reason,
                )
            else:
                self.outline.append((None, "", render(left), link.relation, render(link.term), ""))

    def _outline_row(
        self, line: int | None, left: str, relation: str, right: str, reason: str
    ) -> None:
        """A row of the outline, in the case the next row is in."""
        self.outline.append((line, self._case, left, relation, right, reason))
        self._case = ""

    # }}}

    # {{{ a leaf

    def _leaf(self, leaf: Leaf, context: _Context, claim: Any) -> list[_Line]:
        """The block that closes one case: its ``yield`` or ``return``, or lanky's closers.

        Where a step the case asserted states the claim, that is the case's
        proof. Where one starts or ends at a side of the claim, the case's
        ``by(...)`` is asked only for the rest of the way (:meth:`_gap`).
        """
        here = substitute(claim, context.pins)
        word = "yield" if leaf.point else "return"
        if leaf.hole:
            self._outline_row(leaf.line, *_sides_of(here), f"left open ({word} by(...))")
            return [_Line("sorry", Origin("hole", leaf.line, {"claim": here}))]
        whole = self._asserted_claim(here, context)
        if whole is not None:
            return whole
        if leaf.facts is None:
            return self._finished(leaf, context, here)
        gap = self._gap(here, context)
        if gap is None:
            produced, step = self._step(here, leaf.facts, leaf, context, None)
            self._outline_leaf(leaf, here, step)
            return produced
        goal, finish = gap
        name = self.names.numbered("rest")
        origin = Origin("step", leaf.line, {"claim": here})
        try:
            statement = self._prop(goal, context)
        except UnsupportedTerm as exc:
            raise ProofError(
                "unsupported", f"Lean cannot state the step: {exc}", leaf.line
            ) from None
        produced, step = self._step(goal, leaf.facts, leaf, context, None)
        self._outline_leaf(leaf, here, step)
        lines = [_Line(f"have {lean_identifier(name)} : {statement} := by", origin)]
        lines += _indented(produced, "  ", "  ")
        lines.append(_Line(finish.format(rest=lean_identifier(name)), origin))
        return lines

    def _outline_leaf(self, leaf: Leaf, claim: Any, step: Step) -> None:
        """The outline's row of a ``yield`` or ``return``: the case's claim, and its reasons."""
        left, relation, right = _sides_of(claim)
        reasons = [
            instance
            for instance in step.instances
            if not isinstance(instance.citation.source, Asserted)
        ]
        self._outline_row(leaf.line, left, relation, right, self._reason_text(reasons))

    def _asserted_claim(self, claim: Any, context: _Context) -> list[_Line] | None:
        """``exact h``, where a step the case asserted states the claim, its sides either way."""
        for instance in reversed(context.asserted):
            body = instance.body
            if not (isinstance(body, Comparison) and isinstance(claim, Comparison)):
                continue
            name = lean_identifier(instance.lean_name)
            origin = Origin("asserted-end", instance.citation.line, {"claim": claim})
            if (
                body.operator == claim.operator
                and self._prints_as(body.left, claim.left, context)
                and self._prints_as(body.right, claim.right, context)
            ):
                return [_Line(f"exact {name}", origin)]
            if (
                body.operator == claim.operator == "=="
                and self._prints_as(body.left, claim.right, context)
                and self._prints_as(body.right, claim.left, context)
            ):
                return [_Line(f"exact {name}.symm", origin)]
        return None

    def _gap(self, claim: Any, context: _Context) -> tuple[Any, str] | None:
        """The rest of the way to an equation, from an asserted step that starts or ends at a side.

        ``(goal, finish)``: what the case's facts are asked for, and the Lean
        that finishes the claim from that and the asserted step, with
        ``{rest}`` for the name of the first. ``None`` where no asserted
        equation has a side of the claim's.
        """
        if not (isinstance(claim, Comparison) and claim.operator == "=="):
            return None
        for instance in reversed(context.asserted):
            body = instance.body
            if not (isinstance(body, Comparison) and body.operator == "=="):
                continue
            name = lean_identifier(instance.lean_name)
            if self._prints_as(body.left, claim.left, context):
                return Comparison(body.right, "==", claim.right), f"exact {name}.trans {{rest}}"
            if self._prints_as(body.right, claim.left, context):
                return (
                    Comparison(body.left, "==", claim.right),
                    f"exact {name}.symm.trans {{rest}}",
                )
            if self._prints_as(body.right, claim.right, context):
                return Comparison(claim.left, "==", body.left), f"exact {{rest}}.trans {name}"
            if self._prints_as(body.left, claim.right, context):
                return (
                    Comparison(claim.left, "==", body.right),
                    f"exact {{rest}}.trans {name}.symm",
                )
        return None

    def _prints_as(self, first: Any, second: Any, context: _Context) -> bool:
        """Whether two terms print as the same Lean, in this case."""
        try:
            return self._step_term(first, context) == self._step_term(second, context)
        except UnsupportedTerm:
            return False

    def _step(
        self,
        goal: Any,
        facts: Sequence[Citation],
        owner: Any,
        context: _Context,
        line: int | None,
        lenient: bool = False,
    ) -> tuple[list[_Line], Step]:
        """One step: the facts at their points, then what closes ``goal`` from them and the case's.

        The facts written at a point come first, so that the terms they
        bring are there for the facts cited by name alone to be matched
        against too. The steps the case asserted before it are facts of the
        step as well, in Lean's context already. ``lenient`` leaves out a
        fact cited by name alone that fits no single point of this step, for
        a link of a chain, whose ``assert`` lists the facts of every link.
        """
        lines: list[_Line] = []
        made: list[tuple[int, list[Instance]]] = []
        extra: list[Any] = []
        written = [
            (index, citation)
            for index, citation in enumerate(facts)
            if citation.values is not None or not _needs_a_point(citation)
        ]
        alone = [
            (index, citation)
            for index, citation in enumerate(facts)
            if citation.values is None and _needs_a_point(citation)
        ]
        for index, citation in [*written, *alone]:
            try:
                produced, instances = self._citation(
                    citation, context, goal, link=line is not None, extra=extra
                )
            except ProofError as exc:
                if lenient and exc.kind == "no-point" and citation.values is None:
                    continue
                raise
            lines += produced
            made.append((index, instances))
            for instance in instances:
                extra.extend(_sides(instance.body))
        instances_in_order = [
            instance
            for _index, group in sorted(made, key=lambda pair: pair[0])
            for instance in group
        ]
        step = Step(
            leaf=owner if isinstance(owner, Leaf) else None,
            claim=goal,
            instances=(*instances_in_order, *context.asserted),
            conditions=tuple(context.conditions),
            types=dict(self.types),
            line=line,
            owner=owner,
        )
        step = replace(step, multipliers=self._multipliers(goal, step.instances))
        self.steps.append(step)
        origin = Origin("step", step.where, {"step": step})
        lines += self._closer(step, origin, context)
        if self._outlining and line is not None:
            self._outline_row(line, *_sides_of(goal), self._reason_text(instances_in_order))
        return lines, step

    def _reason_text(self, instances: Sequence[Instance]) -> str:
        """``by recurrence, at (a - 2, b) and the claim at (a - 2, b + 2)``: a row's reasons."""
        reasons = []
        for instance in instances:
            citation = instance.citation
            if isinstance(citation.source, Asserted):
                continue
            at = f"({', '.join(_shown(value) for value in instance.values)})"
            if citation.is_claim:
                reasons.append(("the claim", f" at {at}"))
            elif instance.values:
                reasons.append((citation.name, f" at {at}"))
            else:
                reasons.append((citation.name, ""))
        reasons = list(dict.fromkeys(reasons))
        if not reasons:
            return "by algebra"
        if len(reasons) == 1:
            name, at = reasons[0]
            return f"by {name}{',' if at and name != 'the claim' else ''}{at}"
        said = [f"{name}{at}" for name, at in reasons]
        return f"by {', '.join(said[:-1])} and {said[-1]}"

    def _link(
        self,
        left: Any,
        link: LinkStep,
        step: Asserted,
        context: _Context,
        lenient: bool = False,
    ) -> list[_Line]:
        """The block that proves one link of a chain: a step, or ``sorry`` for one left open."""
        goal = Comparison(
            substitute(left, context.pins), link.relation, substitute(link.term, context.pins)
        )
        if link.hole:
            return [_Line("sorry", Origin("hole", step.line, {"claim": goal}))]
        lines, _made = self._step(goal, link.facts, step, context, link.line, lenient)
        return lines

    def _calc(self, chain: TracedChain, step: Asserted, context: _Context) -> list[_Line]:
        """The chain as a ``calc``, a link to a step, each block under its link."""
        origin = Origin("chain", chain.line, {"chain": chain})
        try:
            lines = [_Line(f"calc {self._step_term(chain.start, context)}", origin)]
            heads = []
            for index, (_left, link) in enumerate(chain.steps()):
                relation = _LEAN_RELATION[link.relation]
                term = self._step_term(link.term, context)
                heads.append(
                    f"    {relation} {term} := by" if index == 0 else f"  _ {relation} {term} := by"
                )
        except UnsupportedTerm as exc:
            raise ProofError(
                "unsupported", f"Lean cannot state a term of the chain: {exc}", chain.line
            ) from None
        for head, (left, link) in zip(heads, chain.steps(), strict=True):
            lines.append(_Line(head, Origin("link", link.line, {"chain": chain})))
            body = self._link(left, link, step, context, lenient=True)
            lines += _indented(body, "      ", "      ")
        return lines

    def _ring(self, claim: Any) -> str:
        """The Lean type the claim's sides are numbers of."""
        try:
            return number_type(Add((claim.left, claim.right)), self.types, mathlib=True)
        except Exception:  # noqa: BLE001 - what cannot be typed is a real number to the closers
            return "ℝ"

    def _scope(self, context: _Context) -> _Scope:
        """The scope a step is compiled in, as what the compiler adds reads it."""
        return _Scope(
            types=self.types,
            facts=tuple(context.facts),
            mathlib=self.mathlib,
            shadowed=self.shadowed,
            taken=self.names.used,
        )

    def _step_term(self, term: Any, context: _Context) -> str:
        """A term of a step as Lean source, its natural exponents as ``.toNat``."""
        scope = self._scope(context)
        here = substitute(term, {**getattr(self, "renaming", {}), **context.pins})
        with proof_exponents(scope.natural):
            return render_term(here, self.types, self.mathlib, self.shadowed)

    def _finished(self, leaf: Leaf, context: _Context, claim: Any) -> list[_Line]:
        """A point or a case with no reason given: lanky's whole-goal closers, after its steps.

        The steps the case asserted are in Lean's context, which the closers
        read; each is tried as the claim, and in a linear combination with
        the multipliers Python finds, before the closers.
        """
        origin = Origin(
            "routine",
            leaf.line,
            {"claim": claim, "conditions": context.conditions, "point": leaf.point},
        )
        self.routine += 1
        arms: list[str] = []
        known = list(context.asserted)
        relation = claim.operator if isinstance(claim, Comparison) else None
        if known and self.mathlib and relation == "==":
            multipliers = self._multipliers(claim, tuple(known))
            if multipliers is not None:
                probe = Step(
                    leaf=leaf,
                    claim=claim,
                    instances=tuple(known),
                    conditions=tuple(context.conditions),
                    types=dict(self.types),
                    multipliers=multipliers,
                )
                scope = self._scope(context)
                with proof_exponents(scope.natural):
                    combination = self._combination(probe)
                if combination is not None:
                    arms.append(combination)
        arms += ["omega", "(simp_all; done)", "(simp_all <;> omega)", "decide"]
        if self.mathlib:
            arms += [
                "norm_num",
                "(simp; done)",
                "positivity",
                "ring",
                "(field_simp; done)",
                "(field_simp; ring1)",
                "linarith",
                "nlinarith",
                "(push_cast; ring)",
            ]
        return [_Line("first", origin), *(_Line(f"  | {arm}", origin) for arm in arms)]

    def _citation(
        self,
        citation: Citation,
        context: _Context,
        claim: Any,
        link: bool = False,
        extra: Sequence[Any] = (),
    ) -> tuple[list[_Line], list[Instance]]:
        """The ``have`` lines that state a cited fact at its point, one per part.

        ``claim`` is what the step shows, a link's or the case's; ``extra``
        the terms the step's facts written at a point bring, which a fact
        cited by name alone is matched against too.
        """
        source = citation.source
        if isinstance(source, ClaimDef):
            return self._claim_call(citation, context, claim, link, extra)
        if isinstance(source, Given):
            shapes = [shape_of(part) for part in source.parts]
            leans = self.given[source.name]
        else:
            shapes = [_cited_premises(source, self.mathlib, self.names)]
            leans = [next(lean for lean, _text, theorem in self.cited if theorem is source)]
        lines: list[_Line] = []
        instances: list[Instance] = []
        for index, (shape, lean) in enumerate(zip(shapes, leans, strict=True)):
            if shape.binders:
                if citation.values is None:
                    values = self._point(citation, shape, context, claim, link, extra)
                elif any(value is None for value in citation.values):
                    values = self._rest_of_point(citation, shape, context, claim, link, extra)
                else:
                    values = citation.values
            else:
                values = ()
            made, instance_lines = self._apply(
                citation, index, shape, lean_identifier(lean), values, context
            )
            lines += instance_lines
            instances += made
        return lines, instances

    def _apply(
        self,
        citation: Citation,
        part: int,
        shape: Shape,
        lean: str,
        values: tuple[Any, ...],
        context: _Context,
    ) -> tuple[list[Instance], list[_Line]]:
        """``have f := h v₁ (by omega) ...``: one fact at its point, each condition discharged.

        A family of the fact bound to a function (:class:`~lanky.matching.FamilyValue`)
        is a ``fun``. Where that function's values are integers and the
        family's are reals, as ``one_more_term`` cited at ``sum(i**3 for i
        in Fin[n + 1])`` is, the fact at the point is about the reals, and
        the step about the integers: it is restated in the integers, the
        ring of its own terms, and shown from the fact through the cast,
        which is injective (:meth:`_through_the_cast`).
        """
        at = {var.name: value for (var, _), value in zip(shape.binders, values, strict=True)}
        sorts = {var.name: sort for var, sort in shape.binders}
        pieces: list[tuple[str, Origin | None]] = [(lean, None)]
        casts: list[tuple[str, str]] = []
        for kind, item in shape.premises:
            if kind == "value":
                try:
                    text, cast = self._value(at[item], sorts.get(item), context)
                except UnsupportedTerm as exc:
                    raise ProofError(
                        "unsupported",
                        f"Lean cannot state {citation.text()}'s point: {exc}",
                        citation.line,
                    ) from None
                pieces.append((text, None))
                if cast is not None:
                    casts.append(cast)
                continue
            condition = instantiate(item, at) if item is not None else None
            origin = Origin(
                "condition",
                citation.line,
                {
                    "citation": citation,
                    "values": values,
                    "condition": condition,
                    "conditions": tuple(context.conditions),
                    "guards": tuple(substitute(guard, context.pins) for guard in context.guards),
                    "facts": tuple(context.facts),
                },
            )
            pieces.append((self._discharge(condition, context), origin))
        body = instantiate(shape.body, at)
        parts = conjuncts(body) if isinstance(body, prim.LogicalAnd) else (body,)
        names = [self.names.numbered("f") for _ in parts]
        instances = [
            Instance(citation, part, values, substitute(piece, context.pins), name)
            for piece, name in zip(parts, names, strict=True)
        ]
        origin = Origin("cite", citation.line, {"citation": citation, "values": values})
        if casts and len(instances) == 1 and self.mathlib:
            restated = self._through_the_cast(instances[0], pieces, casts, origin, context)
            if restated is not None:
                return instances, restated
        if len(names) == 1:
            prefix = f"have {lean_identifier(names[0])} := "
        else:
            prefix = f"obtain ⟨{', '.join(lean_identifier(name) for name in names)}⟩ := "
        return instances, [_applied(prefix, pieces, origin)]

    def _value(
        self, value: Any, sort: Any, context: _Context
    ) -> tuple[str, tuple[str, str] | None]:
        """A value of a fact's point as Lean source, and the cast it needs, if any.

        A term is printed as a step prints one. A family's value is a
        ``fun``, its parameters read as the family's arguments: ``k ↦ r **
        k`` for an ``f: Fn[Nat, Real]`` is ``(fun k => r ^ k.toNat)``. Where
        its values are in a narrower ring than the family's, integers for a
        family of reals, the body is ascribed the family's ring, ``(fun i =>
        (i ^ 3 : ℝ))``, which Lean reads with the cast on each integer in it,
        and the second answer is the two rings, ``("Int", "ℝ")``.
        """
        from lanky.matching import FamilyValue, family_scope

        if not isinstance(value, FamilyValue):
            return self._render(value, context, atomic=True), None
        inner, codomain = family_scope(sort, value, self.types)
        hidden = {var.name for var in value.parameters}
        values = {
            key: item
            for key, item in {**getattr(self, "renaming", {}), **context.pins}.items()
            if key not in hidden
        }
        body = substitute(value.body, values)
        facts = tuple(context.facts)

        def natural(exponent: Any) -> bool:
            from lanky.matching import implied

            return implied(Comparison(exponent, ">=", 0), facts, inner) is True

        with proof_exponents(natural):
            text = render_term(body, inner, self.mathlib, self.shadowed)
        names = " ".join(lean_identifier(var.name) for var in value.parameters)
        ring = _ring_of_sort(codomain)
        cast = None
        if ring is not None and self.mathlib:
            try:
                own = number_type(body, inner, mathlib=True)
            except Exception:  # noqa: BLE001 - a body that cannot be typed is Lean's to judge
                own = ring
            if _RINGS.get(own, 0) < _RINGS.get(ring, 0):
                text = f"({text} : {ring})"
                cast = (own, ring)
        return f"(fun {names} => {text})", cast

    def _through_the_cast(
        self,
        instance: Instance,
        pieces: Sequence[tuple[str, Origin | None]],
        casts: Sequence[tuple[str, str]],
        origin: Origin,
        context: _Context,
    ) -> list[_Line] | None:
        """The fact at its point restated in the ring of its own terms, shown through the cast.

        ``one_more_term`` at ``i ↦ i**3`` says, in the reals, that the sum
        of the casts of the cubes to ``n + 1`` is the sum to ``n`` plus the
        cast of ``n**3``. The step is about the integers, so the fact is
        stated as the step reads it, ``∑ k ∈ Finset.Ico 0 (n + 1), k ^ 3 =
        ...`` over ``ℤ``, and proved from the fact in the reals: the cast is
        injective, so the equation in the integers follows from its cast,
        whose casts ``push_cast`` takes down to the integers in it, the
        sums' terms included, as it does in the fact, which is then what
        the cast says. ``None`` where
        the instance is no equation in a ring narrower than the fact's, and
        the fact is stated as it is.
        """
        body = instance.body
        if not isinstance(body, Comparison) or body.operator not in _LEAN_RELATION:
            return None
        own = self._ring(body)
        wide = max((ring for _, ring in casts), key=lambda ring: _RINGS.get(ring, 0))
        if _RINGS.get(own, 0) >= _RINGS.get(wide, 0):
            return None
        try:
            statement = (
                f"{self._step_term(body.left, context)} {_LEAN_RELATION[body.operator]} "
                f"{self._step_term(body.right, context)}"
            )
        except UnsupportedTerm:
            return None
        cast = lean_identifier(self.names.fresh("cast"))
        name = lean_identifier(instance.lean_name)
        arms = [f"exact_mod_cast {cast}"]
        if body.operator == "==":
            injective = (
                self._qualified("Complex.ofReal_injective")
                if own == "ℝ"
                else f"({self._qualified('Int.cast_injective')} (α := {wide}))"
            )
            arms.append(f"(apply {injective}; push_cast at {cast} ⊢; exact {cast})")
        lines = [_Line(f"have {name} : {statement} := by", origin)]
        inner = [_applied(f"have {cast} := ", pieces, origin), _Line("first", origin)]
        inner += [_Line(f"  | {arm}", origin) for arm in arms]
        return lines + _indented(inner, "  ", "  ")

    def _discharge(self, condition: Any, context: _Context) -> str:
        """How a condition is shown: ``(by omega)`` over the integers, else a rule."""
        if condition is not None and self._integer(condition):
            return "(by omega)"
        if not self.mathlib:
            return "(by first | assumption | omega)"
        mul_conj = self._qualified("Complex.mul_conj")
        normsq = self._qualified("Complex.normSq_pos")
        return (
            "(by first | assumption | omega | linarith | positivity "
            f"| (simp only [{mul_conj}, {self._qualified('Complex.ofReal_re')}]; "
            f"exact ({normsq}.mpr ‹_›).ne'))"
        )

    def _qualified(self, name: str) -> str:
        """A root declaration as this command names it."""
        from lanky.lean import global_name

        return global_name(name, self.shadowed)

    def _integer(self, condition: Any) -> bool:
        """Whether a condition is integer arithmetic, which ``omega`` decides."""
        if isinstance(condition, prim.LogicalAnd | prim.LogicalOr):
            return all(self._integer(child) for child in condition.children)
        if isinstance(condition, prim.LogicalNot):
            return self._integer(condition.child)
        if not isinstance(condition, prim.Comparison):
            return False
        try:
            kind = number_type(Add((condition.left, condition.right)), self.types, self.mathlib)
        except Exception:  # noqa: BLE001 - what cannot be typed is no integer
            return False
        return kind.endswith("Int")

    def _rest_of_point(
        self,
        citation: Citation,
        shape: Shape,
        context: _Context,
        claim: Any,
        link: bool,
        extra: Sequence[Any] = (),
    ) -> tuple:
        """The point of a fact cited with some of its values: ``gauss(m)``, ``other.conclusion[p]``.

        The values given are put in, and the rest found by matching the fact
        there against the step, as a fact cited by its name alone is matched.
        """
        assert citation.values is not None
        given = list(citation.values)
        known = {
            var.name: value
            for (var, _), value in zip(shape.binders, given, strict=True)
            if value is not None
        }
        missing = [
            (var, domain)
            for (var, domain), value in zip(shape.binders, given, strict=True)
            if value is None
        ]
        reduced = Shape(
            tuple(missing),
            tuple(("value", var.name) for var, _ in missing),
            instantiate(shape.body, known),
        )
        found = iter(self._point(citation, reduced, context, claim, link, extra))
        return tuple(next(found) if value is None else value for value in given)

    def _point(
        self,
        citation: Citation,
        shape: Shape,
        context: _Context,
        claim: Any,
        link: bool,
        extra: Sequence[Any] = (),
    ) -> tuple:
        """The point of a fact cited by name alone, by matching it against the step it supports.

        The step is a link of a chain, or a case's claim for a ``yield`` or a
        ``return``; its terms are that step's sides, and ``extra``, the sides
        of the facts the step cites at a point. The point is the one at which
        the fact is about the step's terms and nothing else, or where there is
        none, the one at which it gives one of them
        (:func:`lanky.matching.single_point`), solving offsets such as ``x +
        2 = a``, binding values by type, and a family of the fact to a
        function by the higher-order rule.

        Raises:
            ProofError: When no single point fits, with the fix: write it.
        """
        from lanky.induction import Lemma
        from lanky.matching import NoSinglePoint, single_point

        name = citation.name
        unknowns = [var.name for var, _ in shape.binders]
        what = "this step" if link else "this case's claim"
        if not isinstance(shape.body, Comparison):
            raise ProofError(
                "no-point",
                f"{name} says {render(shape.body)}, which lines up with no step; write its "
                f"point, as {_spelled_point(citation, unknowns)} with the values meant",
                citation.line,
                fix=_spelled_point(citation, unknowns),
            )
        lemma = Lemma(name, shape.binders, shape.premises, shape.body)
        terms = [claim.left, claim.right] if isinstance(claim, Comparison) else [claim]
        terms += [term for term in extra if all(term is not seen for seen in terms)]
        try:
            return tuple(single_point(lemma, terms, self.types, context.facts, name))
        except NoSinglePoint as exc:
            failed: NoSinglePoint = exc
        except Exception:  # noqa: BLE001 - a fact the matcher cannot read fits no point it finds
            failed = NoSinglePoint("", ())
        if not failed.several and _binds_a_family(failed.candidates):
            # the matcher's points bind a family to a function: the fix is one
            # of them, written with a lambda
            fix = _spelled_point(citation, None, failed.candidates[0])
            raise ProofError("no-point", f"{name}: {failed}", citation.line, fix=fix)
        if not failed.several:
            raise ProofError(
                "no-point",
                f"{name}: no point of {name} fits a term of {what}, {render(claim)}; write "
                f"its point, as {_spelled_point(citation, unknowns)} with the values meant",
                citation.line,
                fix=_spelled_point(citation, unknowns),
            )
        fix = _spelled_point(citation, None, failed.candidates[0])
        raise ProofError(
            "no-point",
            f"{name}: no single point of {name} fits {what}, {render(claim)}, since "
            f"{len(failed.candidates)} do; write it, as {fix}",
            citation.line,
            fix=fix,
        )

    def _claim_call(
        self,
        citation: Citation,
        context: _Context,
        goal: Any = None,
        link: bool = False,
        extra: Sequence[Any] = (),
    ) -> tuple[list[_Line], list[Instance]]:
        """``have f := Lanky.<name>.claim ...``: the claim at an earlier point, the recursive call.

        A ``claim(...)`` gives the theorem's parameters and leaves the
        conclusion's variables to lanky, which finds them by matching the
        claim against the step, as a fact cited by name alone is matched.
        """
        claim = self.proof.claim
        assert claim is not None and citation.values is not None
        values = dict(zip(claim.params, citation.values, strict=True))
        missing = [name for name, value in values.items() if value is None]
        if missing:
            known = {name: value for name, value in values.items() if value is not None}
            sorts = dict(zip(claim.params, claim.domains, strict=True))
            shape = Shape(
                tuple((Var(name), sorts[name]) for name in missing),
                tuple(("value", name) for name in missing),
                self._claim_body(known),
            )
            found = self._point(citation, shape, context, goal, link, extra)
            values.update(zip(missing, found, strict=True))
            citation = replace(citation, values=tuple(values[name] for name in claim.params))
        changed = {name for name, value in values.items() if not _same_variable(value, name)}
        pieces: list[tuple[str, Origin | None]] = [(self.claim_declared, None)]
        for param in self.claim_params:
            if param.binder:
                value = values.get(param.var, Var(param.var))
                pieces.append((self._render(value, context, atomic=True), None))
                continue
            if param.kind == "cited":
                pieces.append((param.lean, None))
                continue
            if param.term is None:
                pieces.append(("(by assumption)", None))
                continue
            if not _mentions(param.term, changed):
                # what the call does not change is in scope under its own name
                pieces.append((param.lean, None))
                continue
            condition = substitute(param.term, values)
            negative = None
            term = param.term
            if (
                param.kind == "domain"
                and isinstance(term, prim.Comparison)
                and term.operator == "<="
                and _is_zero(term.left)
                and isinstance(term.right, prim.Variable)
            ):
                negative = term.right.name
            origin = Origin(
                "condition",
                citation.line,
                {
                    "citation": citation,
                    "values": citation.values,
                    "condition": condition,
                    "conditions": tuple(context.conditions),
                    "guards": tuple(substitute(guard, context.pins) for guard in context.guards),
                    "facts": tuple(context.facts),
                    "negative": negative,
                    "claim": True,
                },
            )
            pieces.append((self._discharge(condition, context), origin))
        name = self.names.numbered("f")
        body = self._claim_body(values)
        instance = Instance(citation, 0, citation.values, substitute(body, context.pins), name)
        text, spans = f"have {lean_identifier(name)} := ", []
        for index, (piece, piece_origin) in enumerate(pieces):
            if index:
                text += " "
            start = len(text)
            text += piece
            if piece_origin is not None:
                spans.append((start, len(text), piece_origin))
        origin = Origin("call", citation.line, {"citation": citation})
        return [_Line(text, origin, tuple(spans))], [instance]

    def _claim_body(self, values: Mapping[str, Any]) -> Any:
        """What the claim says at a point: the goal's body there."""
        goal = self.goal
        body = goal.body if isinstance(goal, Forall) else goal
        return substitute(body, dict(values))

    # }}}

    # {{{ the step

    def _multipliers(self, claim: Any, instances: Sequence[Instance]) -> tuple[Any, ...] | None:
        """Multipliers that make the instances' combination the claim, as Python finds them.

        Kept by the step in the hint cache (:mod:`lanky.proofs.hints`), so
        that a check of an unchanged proof runs no sympy and writes the same
        Lean source. Lean checks whatever they are. Only the equations among
        the instances are combined, the others taking ``0``; and where the
        search finds nothing with all of them, which a fact the step does
        not need can cause (a link of an ``assert`` has the facts of all its
        links), it is asked again with one of them, then two.
        """
        if not (isinstance(claim, prim.Comparison) and claim.operator == "=="):
            return None
        equations = [
            index
            for index, instance in enumerate(instances)
            if isinstance(instance.body, prim.Comparison) and instance.body.operator == "=="
        ]
        if not equations:
            return None
        from lanky.proofs import hints
        from lanky.proofs.report import combination

        bodies = [instances[index].body for index in equations]
        cache = hints.HintCache(hints.default_hint_dir())
        key = hints.hint_key(claim, [instance.body for instance in instances], self.types)
        kept = cache.get(key)
        if kept is not hints.MISSING:
            return kept
        found = combination(claim, bodies, self.types)
        chosen: Sequence[int] = range(len(bodies))
        if found is None and len(bodies) > 1:
            from itertools import combinations

            for size in range(1, min(len(bodies), 3)):
                for subset in combinations(range(len(bodies)), size):
                    found = combination(claim, [bodies[index] for index in subset], self.types)
                    if found is not None:
                        chosen = subset
                        break
                if found is not None:
                    break
        multipliers: tuple[Any, ...] | None = None
        if found is not None:
            full: list[Any] = [0] * len(instances)
            for position, multiplier in zip(chosen, found, strict=True):
                full[equations[position]] = multiplier
            multipliers = tuple(full)
        from lanky.induction import _sympy

        if multipliers is not None or _sympy() is not None:
            # no multipliers is an answer only where the search could run
            cache.put(key, multipliers)
        return multipliers

    def _closer(self, step: Step, origin: Origin, context: _Context) -> list[_Line]:
        """The step's closing tactic: what turns the facts into the step's claim.

        With Mathlib, the compiler first puts in what the proof never writes:
        each fact with its casts pushed in, the facts that the integer
        denominators the case shows nonzero are not zero in the field
        (:func:`nonzero_lines`), and the rewrite that puts the goal's powers
        in the exponents its facts have (:func:`shift_lines`).
        """
        names = [lean_identifier(instance.lean_name) for instance in step.instances]
        claim = step.claim
        relation = claim.operator if isinstance(claim, Comparison) else None
        lines: list[_Line] = []
        scope = self._scope(context)
        if self.mathlib:
            for name in dict.fromkeys(names):
                lines.append(_Line(f"try push_cast at {name}", origin))
            bodies = [instance.body for instance in step.instances]
            with proof_exponents(scope.natural):
                added = nonzero_lines([claim, *bodies, *(step.multipliers or ())], scope)
                added += shift_lines(claim, bodies, scope)
            lines += [_Line(text, origin) for text in added]
        arms: list[str] = []
        for name in list(dict.fromkeys(names))[:4]:
            arms.append(f"exact {name}")
            if relation == "==":
                arms.append(f"exact {name}.symm")
        if names and relation == "==":
            # a fact that rewrites a part of the step, under a function the
            # step applies to it, as the modulus squared does under log
            joined = ", ".join(dict.fromkeys(names))
            arms.append(f"(rw [{joined}]; done)")
            for name in list(dict.fromkeys(names))[:4]:
                if len(names) > 1:
                    arms.append(f"(rw [{name}]; done)")
                arms.append(f"(rw [← {name}]; done)")
            arms.append(f"(simp only [{joined}]; done)")
        if self.mathlib:
            complex_ = self._ring(claim) == "ℂ" if relation else False
            if step.multipliers is not None:
                with proof_exponents(scope.natural):
                    combination = self._combination(step)
                if combination is not None:
                    arms.append(combination)
            if relation == "==":
                # algebra alone, for a link of an assert whose facts serve its other links
                arms.append(f"linear_combination (norm := {self._norm()})")
            if not complex_:
                if names:
                    arms.append(f"linarith [{', '.join(names)}]")
                    arms.append(f"nlinarith [{', '.join(names)}]")
                else:
                    arms += ["linarith", "nlinarith"]
            if relation in ("<=", "<", ">=", ">", "!="):
                arms.append("positivity")
            if relation == "==":
                arms += ["ring1", "(field_simp; ring1)"]
        else:
            arms += [
                "omega",
                f"(simp only [{self._qualified('Int.sub_add_cancel')}] at *; omega)",
                "grind",
            ]
        lines += [
            _Line(f"set_option maxHeartbeats {STEP_HEARTBEATS} in", origin),
            _Line("first", origin),
        ]
        lines += [_Line(f"  | {arm}", origin) for arm in arms]
        return lines

    def _norm(self) -> str:
        """lanky's normalization for ``linear_combination``, as this command names its roots."""
        from lanky.oracles.lean import combination_norm

        return combination_norm(
            LeanStatement(
                name="", binders=(), hypotheses=(), goal="", mathlib=True, shadowed=self.shadowed
            )
        )

    def _combination(self, step: Step) -> str | None:
        """``linear_combination (norm := ...) f₁ - f₂ + (m : ℝ) * f₃``, Python's multipliers."""
        from lanky.oracles.lean import _is_number, combination_norm

        claim = step.claim
        try:
            ring = number_type(Add((claim.left, claim.right)), self.types, mathlib=True)
        except Exception:  # noqa: BLE001 - a claim that cannot be typed has no combination
            return None
        parts: list[str] = []
        pairs = list(zip(step.multipliers or (), step.instances, strict=True))
        pairs.sort(key=lambda pair: not _is_number(pair[0], 1))
        for multiplier, instance in pairs:
            name = lean_identifier(instance.lean_name)
            if _is_number(multiplier, 0):
                continue
            if _is_number(multiplier, 1):
                term = name
            elif _is_number(multiplier, -1) and parts:
                parts.append(f"- {name}")
                continue
            else:
                try:
                    factor = render_term(multiplier, self.types, True, self.shadowed)
                except UnsupportedTerm:
                    return None
                term = f"({factor} : {ring}) * {name}"
            parts.append(f"+ {term}" if parts else term)
        if not parts:
            return None
        statement = LeanStatement(
            name="", binders=(), hypotheses=(), goal="", mathlib=True, shadowed=self.shadowed
        )
        return f"linear_combination (norm := {combination_norm(statement)}) {' '.join(parts)}"

    # }}}


#: The rings a number can be in, narrowest first, by the name a statement gives each.
_RINGS = {"Int": 1, "_root_.Int": 1, "ℝ": 2, "ℂ": 3}


def _ring_of_sort(sort: Any) -> str | None:
    """The Lean ring a value of a lanky sort is in: ``Int``, ``ℝ`` or ``ℂ``; ``None`` if unknown."""
    from lanky.prelude import Sort

    while isinstance(sort, Refined):
        sort = sort.base
    if isinstance(sort, FinType):
        return "Int"
    if isinstance(sort, Sort):
        return {"Nat": "Int", "Int": "Int", "Real": "ℝ", "Complex": "ℂ"}.get(sort.name)
    return None


def _spelled_point(
    citation: Citation, unknowns: Sequence[str] | None, found: Sequence[Any] = ()
) -> str:
    """A fact at a point as a proof writes it: ``pde[a - 2, b]``, ``gauss(m)``, ``f.conclusion[k]``.

    ``unknowns`` names the values left to write, each by its variable's
    name; or ``found`` gives them, the values the matcher found.
    """
    values = list(found) if unknowns is None else [Var(name) for name in unknowns]
    filled = iter(values)
    if citation.values is None:
        point = tuple(values)
    else:
        point = tuple(next(filled, None) if value is None else value for value in citation.values)
    try:
        return replace(citation, values=point).text()
    except Exception:  # noqa: BLE001 - a fact that cannot say itself is written by name
        return f"{citation.name}[{', '.join(_shown(value) for value in values)}]"


def _binds_a_family(points: Sequence[tuple[Any, ...]]) -> bool:
    """Whether some point gives a family of the fact a function as its value."""
    from lanky.matching import FamilyValue

    return any(isinstance(value, FamilyValue) for point in points for value in point)


def _applied(
    prefix: str, pieces: Sequence[tuple[str, Origin | None]], origin: Origin
) -> _Line:
    """``prefix`` and a fact applied to its pieces, each condition's columns kept for a message."""
    text, spans = prefix, []
    for index, (piece, piece_origin) in enumerate(pieces):
        if index:
            text += " "
        start = len(text)
        text += piece
        if piece_origin is not None:
            spans.append((start, len(text), piece_origin))
    return _Line(text, origin, tuple(spans))


def _needs_a_point(citation: Citation) -> bool:
    """Whether a citation is a fact cited by name alone, whose point the step gives."""
    return citation.values is None and not citation.is_claim


def _sides_of(claim: Any) -> tuple[str, str, str]:
    """``(left, relation, right)`` of a claim as the outline prints it; else the claim alone."""
    if isinstance(claim, Comparison):
        return render(claim.left), claim.operator, render(claim.right)
    return render(claim), "", ""


def _label_of(questions: Sequence[Question]) -> str:
    """The case of a path as a person reading the proof aloud says it: ``if a < 2:``.

    The outline lists the cases in the order the body has them, as the
    ``if``s read, so a case says only what the ones before it did not: the
    splits it went past on the way, their conditions false, are what "if"
    after them already means. So ``every_box``'s three cases read ``if a + b
    == 0:``, ``if a < 2:`` and ``otherwise:``, and not ``when a + b != 0 and
    a < 2:``. Under a split that held, a split that did not says its
    condition the other way round: ``if a < 2 and b >= 2:``. A case past
    every split, all false, is ``otherwise:``.
    """
    split = [question for question in questions if not question.forced]
    if not split:
        return ""
    first = next((index for index, question in enumerate(split) if question.answer), None)
    if first is None:
        return "otherwise:"
    said = " and ".join(render(question.condition) for question in split[first:])
    return f"if {said}:"


def _listing(names: Sequence[str]) -> str:
    """``a``, ``a and b``, ``a, b and c``."""
    if len(names) == 1:
        return names[0]
    return f"{', '.join(names[:-1])} and {names[-1]}"


def _same_variable(value: Any, name: str) -> bool:
    """Whether ``value`` is the variable ``name`` itself."""
    return isinstance(value, prim.Variable) and value.name == name


def _mentions(term: Any, names: set[str]) -> bool:
    """Whether ``term`` mentions any of ``names``."""
    from lanky.terms import free_variables

    return bool(free_variables(term) & names)


def compile_proof(proof: Proof, mathlib: bool, as_cited: str | None = None) -> Command:
    """The Lean command a traced proof compiles to (see the module).

    ``as_cited`` is the text a proof that cites the theorem restates, as the
    ladder's command states it (:func:`lanky.oracles.lean.claim_statement`):
    the command proves it as ``Lanky.<name>.as_cited`` after the theorem.

    Raises:
        UnsupportedTerm: If the printer cannot state the theorem in this dialect.
        ProofError: For what the compile finds wrong before Lean is asked: no
            measure for the claim's calls, no single point for a fact cited by
            its name, a case split or a point Lean cannot state.
    """
    return _Compiler(proof, mathlib, as_cited).compile()


def _is_zero(term: Any) -> bool:
    """Whether ``term`` is the number zero."""
    return isinstance(term, int) and not isinstance(term, bool) and term == 0
