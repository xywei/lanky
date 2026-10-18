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

from lanky.audit import audit_lines
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
from lanky.proofs.trace import (
    Citation,
    ClaimDef,
    Given,
    Leaf,
    LinkStep,
    Named,
    Node,
    Proof,
    ProofError,
    TracedChain,
)
from lanky.terms import Add, Comparison, Forall, LogicalAnd, Var, conjuncts, render

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
    """A ``return`` as the report needs it: the case, its claim, and the facts at their points."""

    leaf: Leaf
    claim: Any
    instances: tuple[Instance, ...]
    conditions: tuple[tuple[Any, int], ...]
    types: Mapping[str, Any]
    multipliers: tuple[Any, ...] | None = None
    line: int | None = None

    @property
    def where(self) -> int | None:
        """The Python line of the step: a link's own, or the ``return``'s."""
        return self.line if self.line is not None else self.leaf.line


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
        as_cited: The text a proof that cites this theorem restates, which the
            command proves as ``Lanky.<name>.as_cited``; ``None`` for none.
        audited: The theorems the command's axiom audit asks about.
        holes: The Python lines of the steps left open, ``by=...``.
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


class Premise:
    """A theorem a cited theorem's own proof cited: restated too, and rested on.

    Its ``as_cited`` text is a hypothesis of the cited theorem's
    ``as_cited``, so a citation of that theorem restates it as well, all the
    way down (:func:`lanky.citations.premises_of`). It has a theorem's
    ``__name__`` and ``fact_id``, which is all a restatement reads.
    """

    def __init__(self, name: str, fact_id: str) -> None:
        self.__name__ = name
        self.fact_id = fact_id

    def __repr__(self) -> str:
        """``<premise log_of_a_power>``."""
        return f"<premise {self.__name__}>"


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

    def __init__(self, proof: Proof, mathlib: bool, as_cited: str | None = None) -> None:
        self.proof = proof
        self.as_cited = as_cited
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
        self._premises(list(proof.cited))
        self.steps: list[Step] = []
        self.lines: list[_Line] = []
        self.outline: list[tuple[int | None, str, str, str, str, str]] = []
        # the case and the fact on the way the next row of the outline is in
        self._case = ""
        self._label = ""

    def _premises(self, theorems: list[Any]) -> None:
        """Restate the theorems the cited theorems' own proofs cited, after them (:class:`Premise`).

        Raises:
            ProofError: If a premise has no proved text, or the premises come
                round in a circle, naming them.
        """
        from lanky.citations import premises_of

        seen = {getattr(theorem, "fact_id", None) for theorem in theorems}
        stack = []
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
            citation = stack.pop(0)
            if citation.fact_id in seen or citation.restated is None:
                continue
            seen.add(citation.fact_id)
            lean = self.names.fresh(citation.name)
            self.cited.append((lean, citation.restated, Premise(citation.name, citation.fact_id)))
            stack.extend(citation.premises)

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
        routine = sum(1 for leaf in leaves if leaf.facts is None and leaf.chain is None)
        named = len({id(chain) for leaf in leaves for chain in leaf.named})
        holes = len(self.proof.holes)
        parts = []
        if measured is not None:
            parts.append(measured.said)
        if cases > 1:
            parts.append(f"{cases} cases")
        if steps or not routine:
            parts.append("1 step" if steps == 1 else f"{steps} steps")
        if named:
            parts.append("1 named fact" if named == 1 else f"{named} named facts")
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
            body: list[_Line] = self._pins(holds, inner, question.line)
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
        """The block that closes one case: its facts and the step, a chain, or lanky's closers.

        A condition the path's facts decided made no split, and an equation
        among them that fixes integers fixes them here. The facts on the way
        the case cites come first, each proved in a ``have`` of its own.
        """
        lines: list[_Line] = []
        for question in leaf.questions:
            if question.forced:
                lines += self._pins(question.condition, context, question.line)
        here = substitute(claim, context.pins)
        self._case = self._case_label(leaf)
        if leaf.facts is None and leaf.chain is None:
            return lines + self._routine(leaf, context, here)
        named: dict[int, Instance] = {}
        for chain in leaf.named:
            lines += self._named(chain, leaf, context, named)
        if leaf.chain is not None:
            return lines + self._chain(leaf.chain, leaf, context, here, named)
        produced, step = self._step(here, leaf.facts or (), leaf, context, named, None)
        return lines + produced

    def _case_label(self, leaf: Leaf) -> str:
        """``if a < 2``, ``when a >= 2``: the case of a leaf, as an outline names it."""
        split = [question for question in leaf.questions if not question.forced]
        if not split:
            return ""
        said = " and ".join(render(question.condition) for question in split)
        if len(split) == 1 and split[0].answer:
            return f"if {said}:"
        if all(not question.answer for question in split) and len(split) == 1:
            return "otherwise:"
        return f"when {said}:"

    def _step(
        self,
        goal: Any,
        facts: Sequence[Citation],
        leaf: Leaf,
        context: _Context,
        named: Mapping[int, Instance],
        line: int | None,
    ) -> tuple[list[_Line], Step]:
        """One step: the facts at their points, then what closes ``goal`` from them."""
        lines: list[_Line] = []
        instances: list[Instance] = []
        for citation in facts:
            produced, made = self._citation(citation, leaf, context, goal, named)
            lines += produced
            instances += made
        step = Step(
            leaf=leaf,
            claim=goal,
            instances=tuple(instances),
            conditions=tuple(context.conditions),
            types=dict(self.types),
            line=line,
        )
        step = replace(step, multipliers=self._multipliers(goal, instances))
        self.steps.append(step)
        origin = Origin("step", step.where, {"step": step})
        lines += self._closer(step, origin, context)
        self._outline_step(step, goal, line)
        return lines, step

    def _outline_step(self, step: Step, goal: Any, line: int | None) -> None:
        """A row of the outline ``--steps`` prints: the step, and what it follows from."""
        reasons = []
        for instance in step.instances:
            citation = instance.citation
            at = f"({', '.join(_shown(value) for value in instance.values)})"
            if citation.is_claim:
                reasons.append(("the claim", f" at {at}"))
            elif instance.values:
                reasons.append((citation.name, f" at {at}"))
            else:
                reasons.append((citation.name, ""))
        reasons = list(dict.fromkeys(reasons))
        if not reasons:
            reason = "by algebra"
        elif len(reasons) == 1:
            name, at = reasons[0]
            reason = f"by {name}{',' if at and name != 'the claim' else ''}{at}"
        else:
            said = [f"{name}{at}" for name, at in reasons]
            reason = f"by {', '.join(said[:-1])} and {said[-1]}"
        left, relation, right = render(goal), "", ""
        if isinstance(goal, Comparison):
            left, relation, right = render(goal.left), goal.operator, render(goal.right)
        if self._label:
            left = f"{self._label}: {left}"
            self._label = ""
        self.outline.append((step.where, self._case, left, relation, right, reason))
        self._case = ""

    def _named(
        self, chain: TracedChain, leaf: Leaf, context: _Context, named: dict[int, Instance]
    ) -> list[_Line]:
        """A fact on the way, ``recurrence = a[n].equals(...)``: ``have recurrence : ... := by``."""
        name = self.names.fresh(chain.name or "fact")
        origin = Origin("named", chain.line, {"chain": chain})
        try:
            statement = (
                f"{self._step_term(chain.start, context)} {_LEAN_RELATION[chain.relation]} "
                f"{self._step_term(chain.end, context)}"
            )
        except UnsupportedTerm as exc:
            raise ProofError(
                "unsupported", f"Lean cannot state {chain.name or 'the fact'}: {exc}", chain.line
            ) from None
        lines = [_Line(f"have {lean_identifier(name)} : {statement} := by", origin)]
        self._label = chain.name or ""
        if len(chain.links) == 1:
            left, link = next(chain.steps())
            body = self._link(left, link, leaf, context, named)
        else:
            body = self._calc(chain, leaf, context, named)
        lines += _indented(body, "  ", "  ")
        citation = Citation(Named(chain), None, chain.line)
        named[id(chain)] = Instance(citation, 0, (), substitute(chain.claim, context.pins), name)
        return lines

    def _link(
        self,
        left: Any,
        link: LinkStep,
        leaf: Leaf,
        context: _Context,
        named: Mapping[int, Instance],
    ) -> list[_Line]:
        """The block that proves one link of a chain: a step, or ``sorry`` for one left open."""
        goal = Comparison(
            substitute(left, context.pins), link.relation, substitute(link.term, context.pins)
        )
        if link.hole:
            self.outline.append(
                (
                    link.line,
                    self._case,
                    render(goal.left),
                    goal.operator,
                    render(goal.right),
                    "left open (by=...)",
                )
            )
            self._case = ""
            return [_Line("sorry", Origin("hole", link.line, {"claim": goal}))]
        lines, _step = self._step(goal, link.facts, leaf, context, named, link.line)
        return lines

    def _calc(
        self, chain: TracedChain, leaf: Leaf, context: _Context, named: Mapping[int, Instance]
    ) -> list[_Line]:
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
            body = self._link(left, link, leaf, context, named)
            lines += _indented(body, "      ", "      ")
        return lines

    def _chain(
        self,
        chain: TracedChain,
        leaf: Leaf,
        context: _Context,
        claim: Any,
        named: Mapping[int, Instance],
    ) -> list[_Line]:
        """A case proved by a chain: the ``calc`` itself, or the claim from it.

        Where the chain's ends print as the claim's sides, with its relation,
        the ``calc`` is the case's proof. Otherwise it is a fact of the case,
        ``have chain := calc ...``, and the claim follows from it as it
        stands, turned round, or up to how the sides print (``-x`` against
        ``(-1) * x``). A chain of equations about other terms than the claim's
        sides is refused before Lean is asked.
        """
        calc = self._calc(chain, leaf, context, named)
        if self._ends_print_as(chain, claim, context):
            return calc
        self._refuse_another_claim(chain, claim, context)
        name = self.names.numbered("chain")
        origin = Origin("chain-end", chain.links[-1].line, {"chain": chain, "claim": claim})
        lines = [_Line(f"have {lean_identifier(name)} :=", Origin("chain", chain.line))]
        lines += _indented(calc, "  ", "  ")
        attempts = [f"exact {name}"]
        relation = claim.operator if isinstance(claim, Comparison) else None
        if relation == "==" and chain.relation == "==":
            attempts.append(f"exact {name}.symm")
            if self.mathlib:
                from lanky.oracles.lean import combination_norm

                norm = combination_norm(
                    LeanStatement(
                        name="",
                        binders=(),
                        hypotheses=(),
                        goal="",
                        mathlib=True,
                        shadowed=self.shadowed,
                    )
                )
                ring = self._ring(claim)
                attempts.append(f"linear_combination (norm := {norm}) {name}")
                attempts.append(f"linear_combination (norm := {norm}) (-1 : {ring}) * {name}")
            else:
                simp = self._qualified("Int.sub_add_cancel")
                attempts.append(f"((try simp only [{simp}] at *) <;> omega)")
        elif self.mathlib:
            attempts += [f"linarith [{name}]", f"nlinarith [{name}]"]
        else:
            attempts.append("omega")
        lines.append(_Line(f"set_option maxHeartbeats {STEP_HEARTBEATS} in", origin))
        lines.append(_Line("first", origin))
        lines += [_Line(f"  | {attempt}", origin) for attempt in attempts]
        return lines

    def _ends_print_as(self, chain: TracedChain, claim: Any, context: _Context) -> bool:
        """Whether the chain's ends print as the claim's sides, with the claim's relation."""
        if not isinstance(claim, Comparison) or claim.operator != chain.relation:
            return False
        try:
            return self._step_term(chain.start, context) == self._step_term(
                claim.left, context
            ) and self._step_term(chain.end, context) == self._step_term(claim.right, context)
        except UnsupportedTerm:
            return False

    def _refuse_another_claim(self, chain: TracedChain, claim: Any, context: _Context) -> None:
        """Refuse a chain of equations not about the claim's sides, as far as sympy says."""
        from lanky.proofs.report import _algebra

        if not (
            isinstance(claim, Comparison) and claim.operator == "==" and chain.relation == "=="
        ):
            return
        algebra = _algebra(claim, self.types)
        if algebra is None:
            return
        shown = substitute(chain.claim, context.pins)
        try:
            claimed = algebra.side(claim, {})
            said = algebra.side(shown, {})
        except Exception:  # noqa: BLE001 - terms the algebra cannot read are Lean's to judge
            return
        sympy = algebra.sympy
        if sympy.simplify(claimed - said) == 0 or sympy.simplify(claimed + said) == 0:
            return
        raise ProofError(
            "chain",
            f"the chain ends at {render(shown.right)}, and it starts at {render(shown.left)}; "
            f"the claim of this case is {render(claim)}",
            chain.links[-1].line,
            fix="end the chain at the claim's other side, or name it and cite it",
        )

    def _ring(self, claim: Any) -> str:
        """The Lean type the claim's sides are numbers of."""
        try:
            return number_type(Add((claim.left, claim.right)), self.types, mathlib=True)
        except Exception:  # noqa: BLE001 - what cannot be typed is a real number to the closers
            return "ℝ"

    def _scope(self, context: _Context) -> Any:
        """The scope a step is compiled in, as :mod:`lanky.oracles.steps` reads it."""
        from lanky.oracles.steps import StepScope

        return StepScope(
            types=self.types,
            facts=tuple(context.facts),
            mathlib=self.mathlib,
            shadowed=self.shadowed,
            taken=self.names.used,
            path=self.proof.path,
        )

    def _step_term(self, term: Any, context: _Context) -> str:
        """A term of a step as Lean source, its natural exponents as ``.toNat``."""
        scope = self._scope(context)
        here = substitute(term, {**getattr(self, "renaming", {}), **context.pins})
        with proof_exponents(scope.natural):
            return render_term(here, self.types, self.mathlib, self.shadowed)

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
                "(field_simp; ring1)",
                "linarith",
                "nlinarith",
                "(push_cast; ring)",
            ]
        return [_Line("first", origin), *(_Line(f"  | {arm}", origin) for arm in arms)]

    def _citation(
        self,
        citation: Citation,
        leaf: Leaf,
        context: _Context,
        claim: Any,
        named: Mapping[int, Instance] | None = None,
    ) -> tuple[list[_Line], list[Instance]]:
        """The ``have`` lines that state a cited fact at its point, one per part.

        A fact on the way is in the context already, under its name.
        """
        source = citation.source
        if isinstance(source, Named):
            found = (named or {}).get(id(source.chain))
            if found is None:
                raise ProofError(
                    "cite",
                    f"{source.name} is cited before it is shown; name the step first, then cite it",
                    citation.line,
                )
            return [], [replace(found, citation=citation)]
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
        """``have f := h v₁ (by omega) ...``: one fact at its point, each condition discharged.

        A family of the fact bound to a function (:class:`~lanky.matching.FamilyValue`)
        is a ``fun``. Where that function's values are integers and the
        family's are reals, as ``one_more_term`` cited at ``sum(i**3 for i
        in Fin[n + 1])`` is, the fact at the point is about the reals, and
        the step about the integers: it is restated in the integers, the
        ring of its own terms, and shown from the fact through the cast,
        which is injective (:meth:`_through_the_cast`).
        """
        from lanky.matching import instantiate

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

    def _point(self, citation: Citation, shape: Shape, context: _Context, claim: Any) -> tuple:
        """The point of a fact cited by name alone, by matching it against the step it supports.

        The step is a link of a chain, or a case's claim for a ``return``. The
        point is the one at which the fact is about the step's terms and
        nothing else (:func:`lanky.matching.single_point`), solving offsets
        such as ``x + 2 = a``, binding values by type, and a family of the
        fact to a function by the higher-order rule. Where that rule finds no
        single point, the point that lines the fact's applications up with
        the claim's, one family at a time, is taken if there is one
        (:meth:`_unified`).

        Raises:
            ProofError: When no single point fits.
        """
        from lanky.induction import Lemma
        from lanky.matching import NoSinglePoint, single_point

        lemma = Lemma(citation.name, shape.binders, shape.premises, shape.body)
        terms = [claim.left, claim.right] if isinstance(claim, Comparison) else [claim]
        missed: NoSinglePoint | None = None
        try:
            return tuple(single_point(lemma, terms, self.types, context.facts, citation.name))
        except NoSinglePoint as exc:
            missed = exc
        except Exception:  # noqa: BLE001 - the matcher's failure leaves the point to the other rule
            pass
        try:
            return self._unified(citation, shape, context, claim)
        except ProofError:
            if missed is None or not missed.candidates:
                raise
        # the matcher's points say more than the other rule's, a family's
        # value among them: the fix is written with them, lambda and all
        from lanky.proofs.trace import shown

        point = ", ".join(shown(value) for value in missed.candidates[0])
        raise ProofError(
            "no-point",
            f"{citation.name}: {missed}",
            citation.line,
            fix=f"{citation.name}({point})",
        ) from None

    def _unified(self, citation: Citation, shape: Shape, context: _Context, claim: Any) -> tuple:
        """The point at which the fact's applications of a family are the claim's.

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

    def _closer(self, step: Step, origin: Origin, context: _Context) -> list[_Line]:
        """The step's closing tactic: what turns the facts into the step's claim.

        With Mathlib, the compiler first puts in what the proof never writes
        (:mod:`lanky.oracles.steps`): each fact with its casts pushed in, the
        facts that the integer denominators the case shows nonzero are not
        zero in the field (:func:`~lanky.oracles.steps.nonzero_lines`), and the
        rewrite that puts the goal's powers in the exponents its facts have
        (:func:`~lanky.oracles.steps.shift_lines`).
        """
        names = [lean_identifier(instance.lean_name) for instance in step.instances]
        claim = step.claim
        relation = claim.operator if isinstance(claim, Comparison) else None
        lines: list[_Line] = []
        scope = self._scope(context)
        if self.mathlib:
            from lanky.oracles.steps import nonzero_lines, shift_lines

            for name in dict.fromkeys(names):
                lines.append(_Line(f"try push_cast at {name}", origin))
            bodies = [instance.body for instance in step.instances]
            with proof_exponents(scope.natural):
                added = nonzero_lines([claim, *bodies, *(step.multipliers or ())], scope)
                added += shift_lines(claim, bodies, scope)
            lines += [_Line(text, origin) for text in added]
        arms: list[str] = []
        if len(names) == 1:
            arms.append(f"exact {names[0]}")
            if relation == "==":
                arms.append(f"exact {names[0]}.symm")
        if names and relation == "==":
            # a fact that rewrites a part of the step, under a function the
            # step applies to it, as the modulus squared does under log
            joined = ", ".join(dict.fromkeys(names))
            arms.append(f"(rw [{joined}]; done)")
            if len(names) == 1:
                arms.append(f"(rw [← {names[0]}]; done)")
            arms.append(f"(simp only [{joined}]; done)")
        if self.mathlib:
            complex_ = self._ring(claim) == "ℂ" if relation else False
            if step.multipliers is not None:
                with proof_exponents(scope.natural):
                    combination = self._combination(step)
                if combination is not None:
                    arms.append(combination)
            if not names and relation == "==":
                arms.append(f"linear_combination (norm := {self._norm()})")
            if not complex_:
                if names:
                    arms.append(f"linarith [{', '.join(names)}]")
                    arms.append(f"nlinarith [{', '.join(names)}]")
                else:
                    arms += ["linarith", "nlinarith"]
            if relation in ("<=", "<", ">=", ">", "!="):
                arms.append("positivity")
            if not names and relation == "==":
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
