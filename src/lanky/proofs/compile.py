"""Compiling a traced proof to one Lean command, each line traced back to the Python.

The design idea. The body writes only proof text. The claim is printed from
the annotations by lanky's printer, as it always is, with each hypothesis
under its Python name, so that a bug here can make a proof fail and never
prove another claim. One command holds the whole proof:

- ``def claim(a, b)`` is a theorem of its own, ``Lanky.<name>.claim``, with
  the claim's variables as parameters after the theorem's, the goal's guard
  among its hypotheses, and the goal's body as its statement. A call of
  ``claim`` inside it is a recursive call, which ``termination_by`` with the
  measure lanky finds (:func:`measure`) has Lean check is closer to a base
  case. The theorem itself is ``Lanky.<name>``, proved by applying the claim.
  A parameter of ``claim`` that names one of the theorem's generalizes it: the
  recursive call gives it a value, and the hypotheses that mention it become
  conditions to show there.
- ``if c:`` is ``by_cases``. A branch whose condition fixes integers, ``n ==
  1`` or ``a + b == 0`` among naturals, substitutes them.
- A fact at a point is the hypothesis applied to the values, each condition
  closed by ``omega``, or, over the reals, by the first of a few rules. A fact
  cited by its name alone is applied at the point found by matching it
  against the case's claim (:func:`lanky.proofs.match.unify`).
- ``return f, g`` is one step: ``exact``, or ``linear_combination`` with
  multipliers Python finds (:mod:`lanky.induction`), or ``linarith`` and
  ``nlinarith`` with the facts, in Mathlib; ``exact``, ``omega`` after the
  indices are normalized, or ``grind``, in core Lean. A bare ``return`` is
  lanky's whole-goal closers on the case.
- A cited theorem is restated as a hypothesis of the command, from its printed
  statement, and the proof rests on it in the ledger.
- The command ends with ``#print axioms``, whose answer is read positively
  (:func:`lanky.proofs.report.audit`).

Every emitted line, and every condition's ``by`` inside one, records the
Python line it came from (:class:`Origin`), so a message Lean gives at a
position is reported at the line the user wrote, in lanky's notation.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import substitute
from lanky.lean import (
    ELABORATION_OPTIONS,
    ROOT_NAMES,
    LeanStatement,
    UnsupportedTerm,
    codomain_bound,
    lean_identifier,
    number_type,
    render_prop,
    render_term,
    statement_of,
)
from lanky.prelude import FinType, Refined
from lanky.proofs.match import (
    Shape,
    affine,
    applications,
    decide,
    integer_sort,
    negated,
    pins,
    shape_of,
    unify,
)
from lanky.proofs.trace import Citation, ClaimDef, Given, Leaf, Node, Proof, ProofError
from lanky.terms import Add, Forall, LogicalAnd, Var, conjuncts, render

__all__ = [
    "Command",
    "Instance",
    "Measure",
    "Origin",
    "Step",
    "compile_proof",
    "cited_text",
    "measure",
]

#: The axioms a proof may rest on: the three Lean's own library uses.
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

#: The heartbeats one step may take, so that a stray ``nlinarith`` cannot spend
#: the command's whole time.
STEP_HEARTBEATS = 400000


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
    """A ``return`` as the report needs it: the case, its claim, and the facts at their points."""

    leaf: Leaf
    claim: Any
    instances: tuple[Instance, ...]
    conditions: tuple[tuple[Any, int], ...]
    types: Mapping[str, Any]
    multipliers: tuple[Any, ...] | None = None


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
        steps: Each ``return`` with facts, as the report reads it.
        cited: The theorems the proof cites, restated as hypotheses.
    """

    source: str
    lines: list[_Line]
    declared: str
    mathlib: bool
    measure: Measure | None
    summary: str
    steps: list[Step]
    cited: list[Any]

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

    The seam for the ``as_cited`` rule: once a proved theorem's command
    proves ``Lanky.<name>.as_cited``, its text is what is restated here, byte
    for byte, and checked against the cited theorem's cache entry. Until then
    the citation trusts the printer, as every citation does today, and the
    ledger bounds the citing proof by what it cites.

    Raises:
        UnsupportedTerm: If the printer cannot state the cited theorem.
    """
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


def _change(value: Any, name: str) -> int | None:
    """How much ``value`` is above the variable ``name``: ``-2`` for ``a - 2``; else ``None``."""
    form = affine(value)
    if form is None:
        return None
    rest = dict(form)
    if rest.pop(name, 0) != 1:
        return None
    if any(key is not None for key in rest):
        return None
    constant = rest.get(None, 0)
    return int(constant) if constant == int(constant) else None


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
            "call the claim where one argument is smaller, as a - 2, and stays a natural "
            "number, or climbs toward a bound"
        ),
    )


# }}}


# {{{ emitting the proof


@dataclass(eq=False)
class _Context:
    """What the emitter knows at a point of the tree.

    ``guards`` are the claim's own conditions, the goal's guard at its
    variables; ``conditions`` the case splits on the path, each with the line
    of its ``if``; ``facts`` everything that holds, for deciding.
    """

    pins: dict[str, Any]
    conditions: list[tuple[Any, int]]
    facts: list[Any]
    guards: tuple[Any, ...] = ()


class _Compiler:
    """The compile of one traced proof (see :func:`compile_proof`)."""

    def __init__(self, proof: Proof, mathlib: bool) -> None:
        self.proof = proof
        self.theorem = proof.theorem
        self.mathlib = mathlib
        theorem = proof.theorem
        self.goal = theorem.goal
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
        self.steps: list[Step] = []
        self.lines: list[_Line] = []

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
        lines.append(_Line(""))
        lines.append(
            _Line(f"#print axioms _root_.{self.declared}", Origin("audit", proof.lines[0]))
        )
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
        )

    def _summary(self, measured: Measure | None) -> str:
        """``induction on a, 3 cases, 3 steps``: the proof, as the ledger says it."""
        leaves = self.proof.leaves
        cases = len(leaves)
        steps = sum(1 for leaf in leaves if leaf.facts)
        routine = cases - steps
        parts = []
        if measured is not None:
            parts.append(measured.said)
        if cases > 1:
            parts.append(f"{cases} cases")
        parts.append("1 step" if steps == 1 else f"{steps} steps")
        if routine:
            parts.append("1 routine" if routine == 1 else f"{routine} routine")
        text = ", ".join(parts)
        if self.cited:
            used = [theorem.__name__ for _lean, _text, theorem in self.cited]
            listing = used[0] if len(used) == 1 else f"{', '.join(used[:-1])} and {used[-1]}"
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
        """The tactic block of a node of the case tree."""
        if node.leaf is not None and node.question is None:
            return self._leaf(node.leaf, context, claim)
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
        lines = [_Line(f"by_cases {lean_identifier(name)} : {condition}", origin)]
        for answer, branch in ((True, node.then), (False, node.otherwise)):
            prop = question.prop
            holds = prop if answer else negated(prop)
            inner = _Context(
                dict(context.pins),
                [*context.conditions, (holds, question.line)],
                [*context.facts, holds],
                context.guards,
            )
            body: list[_Line] = []
            if answer:
                body += self._pins(prop, inner, question.line)
            if branch is None:
                # a path no run took: its condition contradicts the path to it
                body.append(_Line("exfalso", origin))
                body.append(_Line("omega", origin))
            else:
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
        return out

    # }}}

    # {{{ a leaf

    def _leaf(self, leaf: Leaf, context: _Context, claim: Any) -> list[_Line]:
        """The block that closes one case: its facts and the step, or lanky's closers.

        A condition the path's facts decided made no split, and an equation
        among them that fixes integers fixes them here.
        """
        lines: list[_Line] = []
        for question in leaf.questions:
            if question.forced and question.answer:
                lines += self._pins(question.prop, context, question.line)
        here = substitute(claim, context.pins)
        if leaf.facts is None:
            return lines + self._routine(leaf, context, here)
        instances: list[Instance] = []
        for citation in leaf.facts:
            produced, made = self._citation(citation, leaf, context, here)
            lines += produced
            instances += made
        step = Step(
            leaf=leaf,
            claim=here,
            instances=tuple(instances),
            conditions=tuple(context.conditions),
            types=dict(self.types),
        )
        multipliers = self._multipliers(here, instances)
        step = replace(step, multipliers=multipliers)
        self.steps.append(step)
        origin = Origin("step", leaf.line, {"step": step})
        lines += self._closer(step, origin)
        return lines

    def _routine(self, leaf: Leaf, context: _Context, claim: Any) -> list[_Line]:
        """A bare ``return``: lanky's whole-goal closers on the case, its facts in scope."""
        origin = Origin("routine", leaf.line, {"claim": claim, "conditions": context.conditions})
        arms = ["omega", "(simp_all; done)", "(simp_all <;> omega)", "decide"]
        if self.mathlib:
            arms += [
                "norm_num",
                "(simp; done)",
                "positivity",
                "ring",
                "(field_simp; done)",
                "linarith",
                "nlinarith",
                "(push_cast; ring)",
            ]
        return [_Line("first", origin), *(_Line(f"  | {arm}", origin) for arm in arms)]

    def _citation(
        self, citation: Citation, leaf: Leaf, context: _Context, claim: Any
    ) -> tuple[list[_Line], list[Instance]]:
        """The ``have`` lines that state a cited fact at its point, one per part."""
        source = citation.source
        if isinstance(source, ClaimDef):
            return self._claim_call(citation, context)
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
                    values = self._point(citation, shape, context, claim)
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
        """``have f := h v₁ (by omega) ...``: one fact at its point, each condition discharged."""
        at = {var.name: value for (var, _), value in zip(shape.binders, values, strict=True)}
        pieces: list[tuple[str, Origin | None]] = [(lean, None)]
        for kind, item in shape.premises:
            if kind == "value":
                try:
                    pieces.append((self._render(at[item], context, atomic=True), None))
                except UnsupportedTerm as exc:
                    raise ProofError(
                        "unsupported",
                        f"Lean cannot state {citation.text()}'s point: {exc}",
                        citation.line,
                    ) from None
                continue
            condition = substitute(item, at) if item is not None else None
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
        body = substitute(shape.body, at)
        parts = conjuncts(body) if isinstance(body, prim.LogicalAnd) else (body,)
        names = [self.names.numbered("f") for _ in parts]
        instances = [
            Instance(citation, part, values, substitute(piece, context.pins), name)
            for piece, name in zip(parts, names, strict=True)
        ]
        if len(names) == 1:
            prefix = f"have {lean_identifier(names[0])} := "
        else:
            prefix = f"obtain ⟨{', '.join(lean_identifier(name) for name in names)}⟩ := "
        text, spans = prefix, []
        origin = Origin("cite", citation.line, {"citation": citation, "values": values})
        for index, (piece, piece_origin) in enumerate(pieces):
            if index:
                text += " "
            start = len(text)
            text += piece
            if piece_origin is not None:
                spans.append((start, len(text), piece_origin))
        return instances, [_Line(text, origin, tuple(spans))]

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

    def _point(self, citation: Citation, shape: Shape, context: _Context, claim: Any) -> tuple:
        """The point of a fact cited by name alone, by matching it against the case's claim.

        Raises:
            ProofError: When no single point fits.
        """
        unknowns = [var.name for var, _ in shape.binders]
        order = list(self.types)
        candidates: dict[tuple[str, ...], dict[str, Any]] = {}
        for pattern in applications(shape.body):
            for atom in applications(claim):
                solution = unify(pattern, atom, unknowns, order)
                if solution is None or set(solution) != set(unknowns):
                    continue
                key = tuple(render(solution[name]) for name in unknowns)
                candidates.setdefault(key, solution)
        if len(candidates) > 1:
            consistent = {
                key: solution
                for key, solution in candidates.items()
                if all(
                    decide(guard, context.facts, self.types) is not False
                    for guard in shape.at(solution)[1]
                )
            }
            if len(consistent) == 1:
                candidates = consistent
        if len(candidates) == 1:
            ((_, solution),) = candidates.items()
            return tuple(solution[name] for name in unknowns)
        name = citation.name
        if not candidates:
            raise ProofError(
                "no-point",
                f"{name}: no point of {name} fits a term of this case's claim, "
                f"{render(claim)}; write its point, as {name}({', '.join(unknowns)}) "
                "with the values meant",
                citation.line,
                fix=f"{name}({', '.join(unknowns)})",
            )
        example = next(iter(candidates))
        return_fix = f"{name}({', '.join(example)})"
        raise ProofError(
            "no-point",
            f"{name}: no single point of {name} fits this case's claim, {render(claim)}, "
            f"since {len(candidates)} do; write it, as {return_fix}",
            citation.line,
            fix=return_fix,
        )

    def _claim_call(
        self, citation: Citation, context: _Context
    ) -> tuple[list[_Line], list[Instance]]:
        """``have f := Lanky.<name>.claim ...``: the claim at smaller values, the recursive call."""
        claim = self.proof.claim
        assert claim is not None and citation.values is not None
        values = dict(zip(claim.params, citation.values, strict=True))
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
        """Multipliers that make the instances' combination the claim, as Python finds them."""
        if not (isinstance(claim, prim.Comparison) and claim.operator == "=="):
            return None
        if not instances or not all(
            isinstance(instance.body, prim.Comparison) and instance.body.operator == "=="
            for instance in instances
        ):
            return None
        from lanky.proofs.report import combination

        found = combination(claim, [instance.body for instance in instances], self.types)
        return None if found is None else tuple(found)

    def _closer(self, step: Step, origin: Origin) -> list[_Line]:
        """The step's closing tactic: what turns the facts into the case's claim."""
        names = [lean_identifier(instance.lean_name) for instance in step.instances]
        arms: list[str] = []
        if len(names) == 1:
            arms.append(f"exact {names[0]}")
        if self.mathlib:
            if step.multipliers is not None:
                combination = self._combination(step)
                if combination is not None:
                    arms.append(combination)
            if names:
                arms.append(f"linarith [{', '.join(names)}]")
                arms.append(f"nlinarith [{', '.join(names)}]")
            else:
                arms += ["linarith", "nlinarith"]
        else:
            arms += [
                "omega",
                f"(simp only [{self._qualified('Int.sub_add_cancel')}] at *; omega)",
                "grind",
            ]
        lines = [
            _Line(f"set_option maxHeartbeats {STEP_HEARTBEATS} in", origin),
            _Line("first", origin),
        ]
        lines += [_Line(f"  | {arm}", origin) for arm in arms]
        return lines

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


def _same_variable(value: Any, name: str) -> bool:
    """Whether ``value`` is the variable ``name`` itself."""
    return isinstance(value, prim.Variable) and value.name == name


def _mentions(term: Any, names: set[str]) -> bool:
    """Whether ``term`` mentions any of ``names``."""
    from lanky.terms import free_variables

    return bool(free_variables(term) & names)


def compile_proof(proof: Proof, mathlib: bool) -> Command:
    """The Lean command a traced proof compiles to (see the module).

    Raises:
        UnsupportedTerm: If the printer cannot state the theorem in this dialect.
        ProofError: For what the compile finds wrong before Lean is asked: no
            measure for the claim's calls, no single point for a fact cited by
            its name, a case split or a point Lean cannot state.
    """
    return _Compiler(proof, mathlib).compile()


def _is_zero(term: Any) -> bool:
    """Whether ``term`` is the number zero."""
    return isinstance(term, int) and not isinstance(term, bool) and term == 0
