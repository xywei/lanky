"""Claims a plugin hands Lean to check, part by part, with what its solver found.

The design idea. A plugin with a decision procedure of its own, loopty with
isl, settles its facts in milliseconds and at the trust of that procedure:
``decided``. Lean can do better than trust it, and it does not have to search
for that. The plugin states the claim as lanky terms built from its own
description of the object (a kernel's loops, guards and subscripts, a
schedule's maps), never from sets its solver computed, and Lean proves each
term with ``omega``. The solver's work is not wasted: it supplies hints, and
a hint carries no trust. A wrong one leaves a goal ``omega`` cannot close,
and the fact stays where the solver put it.

So the fact's term offers Lean an :class:`Obligation` through one method,
``lean_obligation()``, which the Lean oracle calls when it is asked about the
fact (see :class:`lanky.oracles.lean.LeanOracle`). The method returns
``None``, or an obligation whose :attr:`~Obligation.declined` says in words
why there is nothing for Lean to check, when the plugin cannot state the
claim. Nothing else about the plugin's term is read, so the plugin's own
oracle answers the same fact exactly as it did.

An obligation is a conjunction of :class:`Part` s, each a closed lanky term
proved on its own: a schedule's legality is one part per dependence class, so
the classes are checked in parallel, each with its own timeout, and the one
that fails is named. A part's :class:`Hints` are what ``omega`` cannot find:

- *instances* of a hypothesis that is a universal, ``∀ r, off (r + 1) = off r
  + cnt r``: ``omega`` never instantiates one, and the points a solver chose
  (``r`` itself, ``0`` and ``n``) are given as ``have`` lines;
- a *witness* for a goal that is an existential, the totality of a step or the
  definedness of a read: a piecewise function of the universal variables, one
  piece per region, which the plugin reads off isl's ``lexmin``/``lexmax`` or
  its functional form of a map, printed as ``refine ⟨w, ?_⟩`` under a case
  split on the regions;
- *splits*, disjunctions ``omega`` proves and then cases on, for the places
  its elimination is incomplete (it has no dark or grey shadows) and a split
  by the rational bounds rescues it, and to keep the work per case small.

A claim the solver refuted comes with a :class:`Counterexample`: the part it
breaks and a value for every variable of that part. Lean proves the negation
of the part there, by ``decide`` or ``omega``, which checks that the
counterexample is one: a solver's witness that is not a counterexample is
caught rather than printed.

Everything here is pure: the scripts are text, built from the part's term and
its printed statement (:func:`lanky.lean.statement_of`). The oracle sends
them (:meth:`lanky.oracles.lean.LeanOracle.establish`).
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import substitute
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    _affine,
    domain_guards,
    render_term,
    statement_of,
)
from lanky.prelude import FnType, Refined
from lanky.terms import Exists, Forall, conjuncts, init_args

__all__ = [
    "Counterexample",
    "Hints",
    "Instance",
    "Obligation",
    "Part",
    "Piece",
    "attempts",
    "negation_source",
    "obligation_of",
    "part_statement",
    "theorem_name",
]


@dataclass(frozen=True)
class Instance:
    """One hypothesis of a part taken at a point: ``have := h3 r``.

    ``hypothesis`` is the position of the hypothesis among the conjuncts of
    the part's guard (:func:`lanky.terms.conjuncts`), and the hypothesis has
    to be a universal; ``arguments`` are lanky terms, one for each of its
    binders, outermost first, over the part's own variables. The instance
    keeps the hypothesis's own guards as premises, so it says nothing outside
    them, and ``omega`` reads the implication.
    """

    hypothesis: int
    arguments: tuple[Any, ...]


@dataclass(frozen=True)
class Piece:
    """One piece of a witness for a goal that is an existential.

    ``values`` are lanky terms over the part's universal variables, one for
    each binder of the goal's existential, outermost first. ``condition`` is
    where the piece applies, a proposition over the same variables, or
    ``None`` for the last piece, which applies wherever the ones before it do
    not. The pieces of isl's ``lexmax`` are disjoint and cover the points
    where a witness exists, and a piece Lean cannot check fails the part.

    A goal that is a disjunction, of existentials or of propositions with no
    variable, has each piece name the disjunct it proves, ``disjunct``,
    counted from ``0``: a read is defined by whichever statement wrote its
    cell last, and isl says which where.
    """

    values: tuple[Any, ...]
    condition: Any = None
    disjunct: int | None = None


@dataclass(frozen=True)
class Hints:
    """What a solver found that ``omega`` does not look for (see the module docstring)."""

    instances: tuple[Instance, ...] = ()
    witness: tuple[Piece, ...] = ()
    splits: tuple[Any, ...] = ()

    def __bool__(self) -> bool:
        """Whether there is any hint at all."""
        return bool(self.instances or self.witness or self.splits)


@dataclass(frozen=True)
class Part:
    """One conjunct of a claim, proved by Lean on its own.

    ``name`` tells it apart within its obligation, and names its theorem;
    ``label`` says what it is in the plugin's words, ``u[t, i + 1] read after
    u[t + 1, i] is written``, which a ledger prints when the part is not
    proved. ``term`` is a closed lanky term: a universal whose guard holds
    the hypotheses, printed as a theorem whose parameters are its variables
    and hypotheses (:func:`lanky.lean.statement_of`).

    ``fallback``, when given, is asked for more hints only when ``omega`` and
    ``hints`` have not closed the part: what costs the solver more to find
    and is seldom needed, the case split ``omega``'s missing dark and grey
    shadows want. It takes nothing and returns :class:`Hints`.
    """

    name: str
    label: str
    term: Any
    hints: Hints = field(default_factory=Hints)
    fallback: Any = field(default=None, compare=False, repr=False)


@dataclass(frozen=True)
class Counterexample:
    """Where a refuted claim fails: one part, and a value for each of its variables.

    ``point`` maps the name of every binder of the part's term to an integer.
    ``text`` is the counterexample in the plugin's words, the pair of
    statement instances a schedule would reorder, say.
    """

    part: str
    point: Mapping[str, int]
    text: str = ""


@dataclass(frozen=True)
class Obligation:
    """A claim as Lean is to check it (see the module docstring).

    ``parts`` all have to be proved for the claim to be. ``counterexample``
    is set when the plugin's solver refuted the claim, and Lean then checks
    that it is one instead. ``declined`` says why there is nothing to check,
    and a non-empty one leaves the fact to the oracles after Lean.
    ``rests_on`` names the facts whose claims the parts take as hypotheses
    (a callee's postcondition, a cited theorem): a proof of the parts is a
    proof of the claim given those, and the fact rests on them.
    ``decider`` names the solver that decided the claim and found the hints,
    ``isl``, and ``stated_by`` the plugin that stated the parts from its own
    description, ``loopty``, for the ledger to say so.
    """

    parts: tuple[Part, ...] = ()
    counterexample: Counterexample | None = None
    declined: str = ""
    rests_on: tuple[str, ...] = ()
    decider: str = ""
    stated_by: str = ""


def obligation_of(term: Any) -> Obligation | None:
    """The obligation a fact's term offers Lean, or ``None`` when it offers none.

    A term offers one by having a ``lean_obligation()`` method (see the
    module docstring). A method that returns something else than an
    :class:`Obligation` offers none.
    """
    method = getattr(term, "lean_obligation", None)
    if not callable(method):
        return None
    obligation = method()
    return obligation if isinstance(obligation, Obligation) else None


# {{{ the scripts


def part_statement(part: Part, name: str) -> LeanStatement:
    """The part's term as a core-Lean theorem named ``name``.

    Core Lean whatever the session: a part is integer arithmetic, and the
    printed source is the one that replays with ``lean`` alone.

    Raises:
        UnsupportedTerm: If the part's term leaves the printer's fragment.
    """
    return statement_of(part.term, name, mathlib=False)


def _hypothesis_names(statement: LeanStatement) -> list[str]:
    """The names of the statement's hypotheses that are conjuncts of its guard, in order."""
    return [
        name
        for (name, _), term in zip(
            statement.hypotheses, statement.hypothesis_terms, strict=True
        )
        if term is not None
    ]


def _instance_line(
    statement: LeanStatement, part: Part, instance: Instance, index: int
) -> str:
    """``have hi0 := fun g0 g1 => h3 a g0 g1 b``: one hypothesis taken at a point.

    The hypothesis is printed one binder at a time with that binder's guards
    after it (:mod:`lanky.lean`), so a binder that is not the first follows
    the guards of the one before. Those are taken as the arguments of a
    function, which leaves them premises of the instance, as the guards of
    the last binder and the hypothesis's own guard are.

    Raises:
        UnsupportedTerm: If the instance names no universal hypothesis, or
            gives it a number of arguments other than its binders.
    """
    guards = list(conjuncts(part.term.guard)) if isinstance(part.term, Forall) else []
    if not 0 <= instance.hypothesis < len(guards):
        raise UnsupportedTerm(
            f"the instance names hypothesis {instance.hypothesis}, and the part has "
            f"{len(guards)}"
        )
    hypothesis = guards[instance.hypothesis]
    if not isinstance(hypothesis, Forall) or len(hypothesis.binders) != len(
        instance.arguments
    ):
        raise UnsupportedTerm(
            f"hypothesis {instance.hypothesis} is not a universal over "
            f"{len(instance.arguments)} variables"
        )
    name = _hypothesis_names(statement)[instance.hypothesis]
    types = dict(statement.types)
    pieces: list[str] = []
    premises: list[str] = []
    scope = dict(types)
    last = len(hypothesis.binders) - 1
    for position, ((var, domain), value) in enumerate(
        zip(hypothesis.binders, instance.arguments, strict=True)
    ):
        pieces.append(render_term(value, types, atomic=True))
        conditions = domain_guards(var, domain, scope)
        scope = {**scope, var.name: domain}
        if position == last:
            break
        for _ in conditions:
            premise = f"g{index}_{len(premises)}"
            premises.append(premise)
            pieces.append(premise)
    applied = f"{name} {' '.join(pieces)}"
    if premises:
        applied = f"fun {' '.join(premises)} => {applied}"
    return f"have hi{index} := {applied}"


def _applications(expr: Any, out: list[tuple[str, tuple[Any, ...], Any]]) -> None:
    """Every application of a family below ``expr``: ``(name, arguments, node)``."""
    if isinstance(expr, tuple | list):
        for item in expr:
            _applications(item, out)
        return
    if isinstance(expr, Forall | Exists):
        _applications(expr.body, out)
        if expr.guard is not None:
            _applications(expr.guard, out)
        return
    if isinstance(expr, prim.Call) and isinstance(expr.function, prim.Variable):
        out.append((expr.function.name, tuple(expr.parameters), expr))
        _applications(tuple(expr.parameters), out)
        return
    if isinstance(expr, prim.Subscript) and isinstance(expr.aggregate, prim.Variable):
        index = expr.index if isinstance(expr.index, tuple) else (expr.index,)
        out.append((expr.aggregate.name, index, expr))
        _applications(index, out)
        return
    if isinstance(expr, prim.ExpressionNode):
        _applications(init_args(expr), out)


def _form(expr: Any) -> dict[str, int] | None:
    """An argument as an affine form with no zero coefficient, or ``None``."""
    found = _affine(expr)
    if found is None:
        return None
    return {name: value for name, value in found.items() if value}


def _congruence_lines(
    statement: LeanStatement, part: Part, instances: Sequence[Instance], start: int
) -> list[str]:
    """Equations between an instance's cells and the claim's that are one cell.

    An instance of ``∀ r, off (r + 1) = off r + cnt r`` at ``q - 1`` reads
    ``off (q - 1 + 1)``, and ``omega`` takes it for an atom other than the
    claim's ``off q``: it reads arithmetic, not the arguments of a function.
    So each application of a family in an instance whose arguments are those
    of an application in the claim as affine forms, and not as text, gets
    ``have : off (q - 1 + 1) = off q``, which ``congr`` and ``omega`` prove.
    """
    if not isinstance(part.term, Forall):
        return []
    guards = list(conjuncts(part.term.guard))
    context: list[tuple[str, tuple[Any, ...], Any]] = []
    _applications(statement.goal_term, context)
    _applications([term for term in statement.hypothesis_terms if term is not None], context)
    lines: list[str] = []
    said: set[tuple[str, str]] = set()
    for instance in instances:
        hypothesis = guards[instance.hypothesis]
        values = {
            var.name: value
            for (var, _), value in zip(hypothesis.binders, instance.arguments, strict=True)
        }
        found: list[tuple[str, tuple[Any, ...], Any]] = []
        _applications(substitute(hypothesis.body, values), found)
        if hypothesis.guard is not None:
            _applications(substitute(hypothesis.guard, values), found)
        for name, arguments, node in found:
            forms = [_form(argument) for argument in arguments]
            if any(form is None for form in forms):
                continue
            for other, theirs, there in context:
                if other != name or len(theirs) != len(arguments):
                    continue
                if [_form(argument) for argument in theirs] != forms:
                    continue
                left = render_term(node, statement.types)
                right = render_term(there, statement.types)
                if left == right or (left, right) in said:
                    continue
                said.add((left, right))
                lines.append(
                    f"have hc{start + len(lines)} : {left} = {right} := "
                    "by congr 1 <;> omega"
                )
    return lines


def _disjuncts(prop: Any) -> int:
    """How many disjuncts a proposition has at its top level."""
    if isinstance(prop, prim.LogicalOr):
        return sum(_disjuncts(child) for child in prop.children)
    return 1


def _disjunct_list(prop: Any) -> list[Any]:
    """The disjuncts of a proposition, as the printer nests them: ``a ∨ (b ∨ c)``."""
    if isinstance(prop, prim.LogicalOr):
        out: list[Any] = []
        for child in prop.children:
            out.extend(_disjunct_list(child))
        return out
    return [prop]


def _navigation(index: int, count: int) -> list[str]:
    """``refine Or.inr ?_`` and ``refine Or.inl ?_`` down to the disjunct ``index``.

    ``∨`` is right associative, so ``a ∨ b ∨ c`` is ``a ∨ (b ∨ c)``: the
    last disjunct is reached by ``Or.inr`` alone.
    """
    lines = ["refine Or.inr ?_"] * index
    if index < count - 1:
        lines.append("refine Or.inl ?_")
    return lines


def _witness_lines(
    statement: LeanStatement, values: Sequence[Any], disjunct: int | None = None
) -> list[str]:
    """The script that proves the goal's existential at ``values``.

    The existential is printed one binder at a time, each followed by its
    conditions as conjuncts (``∃ y : Int, 0 ≤ y ∧ y < n ∧ ...``), so each
    binder gets its value, each condition ``omega``, and the body ``omega``
    last. ``disjunct`` picks one disjunct of a goal that is a disjunction,
    which is an existential, or a proposition with no variable that
    ``omega`` proves.
    """
    goal = statement.goal_term
    lines: list[str] = []
    if disjunct is not None:
        options = _disjunct_list(goal)
        if not 0 <= disjunct < len(options):
            raise UnsupportedTerm(f"the goal has no disjunct {disjunct}")
        lines += _navigation(disjunct, len(options))
        goal = options[disjunct]
        if not isinstance(goal, Exists):
            if values:
                raise UnsupportedTerm("a disjunct with no variable takes no values")
            return [*lines, "omega"]
    if not isinstance(goal, Exists) or len(goal.binders) != len(values):
        raise UnsupportedTerm(
            "a witness is for a goal that is an existential over as many variables "
            "as the witness has values"
        )
    scope = dict(statement.types)
    guards = list(conjuncts(goal.guard))
    last = len(goal.binders) - 1
    for position, ((var, domain), value) in enumerate(
        zip(goal.binders, values, strict=True)
    ):
        lines.append(f"refine ⟨{render_term(value, scope)}, ?_⟩")
        conditions = len(domain_guards(var, domain, scope))
        scope = {**scope, var.name: domain}
        if position == last:
            conditions += len(guards)
        lines.extend("refine ⟨by omega, ?_⟩" for _ in range(conditions))
    lines.append("omega")
    return lines


def _pieces_lines(statement: LeanStatement, pieces: Sequence[Piece], depth: int = 0) -> list[str]:
    """A case split on the pieces' conditions, each piece's witness in its case."""
    first, *rest = pieces
    if not rest or first.condition is None:
        return _witness_lines(statement, first.values, first.disjunct)
    condition = render_term(first.condition, statement.types)
    inner = _pieces_lines(statement, rest, depth + 1)
    lines = [f"by_cases hp{depth} : {condition}"]
    lines += [("· " if index == 0 else "  ") + line for index, line in
              enumerate(_witness_lines(statement, first.values, first.disjunct))]
    lines += [("· " if index == 0 else "  ") + line for index, line in enumerate(inner)]
    return lines


def hints_witness_only(part: Part) -> bool:
    """Whether the part's goal is a disjunction its witness pieces pick from."""
    return bool(part.hints.witness) and part.hints.witness[0].disjunct is not None


def attempts(part: Part, statement: LeanStatement) -> list[tuple[str, str]]:
    """The scripts tried on one part, as ``(how, tactic)``, ``omega`` alone first.

    ``how`` says in a few words what the script did besides ``omega``, for the
    ledger's detail. A hint that cannot be written for this statement (an
    instance of a hypothesis that is no universal, a witness for a goal that
    is no existential) is dropped and the attempts that can be written are
    still made: a hint is a suggestion, and the part is proved or not on what
    Lean accepts.
    """
    out: list[tuple[str, str]] = []
    goal = statement.goal_term
    if goal is True:
        # a claim with nothing at stake, the writes of a statement with one
        # instance: omega has no arithmetic to work on
        return [("trivial", "trivial")]
    if any(term is False for term in statement.hypothesis_terms):
        # a hypothesis that is false as written, a class of pairs the source
        # never runs in that order: omega reads arithmetic, not False
        return [("a hypothesis is False", "contradiction")]
    intro = "intros\n" if isinstance(goal, Forall) else ""
    if not isinstance(goal, Exists) and not (
        hints_witness_only(part) and isinstance(goal, prim.LogicalOr)
    ):
        out.append(("omega", f"{intro}omega"))
    hints = part.hints
    if not hints:
        return out
    lines: list[str] = []
    said: list[str] = []
    try:
        instances = [
            _instance_line(statement, part, instance, index)
            for index, instance in enumerate(hints.instances)
        ]
    except UnsupportedTerm:
        instances = []
    if instances:
        lines += instances
        lines += _congruence_lines(statement, part, hints.instances, 0)
        said.append(
            f"the hypotheses taken at {len(instances)} "
            f"point{'s' if len(instances) != 1 else ''}"
        )
    split_lines: list[str] = []
    for index, split in enumerate(hints.splits):
        try:
            text = render_term(split, statement.types)
        except UnsupportedTerm:
            continue
        pattern = " | ".join([f"hs{index}"] * _disjuncts(split))
        split_lines.append(f"have hs{index} : {text} := by omega")
        split_lines.append(f"rcases hs{index} with {pattern}")
    if split_lines:
        lines += split_lines
        said.append("a case split")
    if hints.witness and (
        isinstance(goal, Exists)
        or (isinstance(goal, prim.LogicalOr) and hints.witness[0].disjunct is not None)
    ):
        try:
            witness = _pieces_lines(statement, hints.witness)
        except UnsupportedTerm:
            witness = []
        if witness:
            if split_lines:
                lines.append("all_goals")
                lines += ["  " + line for line in witness]
            else:
                lines += witness
            pieces = len(hints.witness)
            said.append(
                "the witness" if pieces == 1 else f"a witness in {pieces} pieces"
            )
    elif lines:
        lines.append("all_goals omega" if split_lines else "omega")
    if said and lines:
        out.append((f"omega, with {' and '.join(said)}", intro + "\n".join(lines)))
    return out


def negation_source(
    part: Part, statement: LeanStatement, point: Mapping[str, int], decide: bool = True
) -> str:
    """The theorem that the part is false at ``point``, proved by ``decide`` or ``omega``.

    The statement is instantiated at the point, its binders in order with a
    ``decide`` for each guard a binder's domain puts between them, and what
    is left, the hypotheses implying the goal at the point, is a closed
    proposition ``decide`` evaluates in the kernel and ``omega`` refutes.

    Raises:
        UnsupportedTerm: If the point leaves a variable without a value, or a
            variable is a family, whose value at the point would be a
            function.
    """
    if not isinstance(part.term, Forall):
        raise UnsupportedTerm("a counterexample is a point of a universal")
    arguments: list[str] = []
    scope: dict[str, Any] = {}
    for var, domain in part.term.binders:
        base = domain
        while isinstance(base, Refined):
            base = base.base
        if isinstance(base, FnType):
            raise UnsupportedTerm(
                f"{var.name} is an array, and a counterexample gives it no value "
                "Lean can evaluate"
            )
        if var.name not in point:
            raise UnsupportedTerm(f"the counterexample gives {var.name} no value")
        value = int(point[var.name])
        arguments.append(str(value) if value >= 0 else f"({value})")
        arguments.extend("(by decide)" for _ in domain_guards(var, domain, scope))
        scope = {**scope, var.name: domain}
    name = statement.declared_name + "_false"
    proof = "revert hw\n  decide" if decide else "omega"
    option = "set_option synthInstance.maxSize 4096 in\n" if decide else ""
    return (
        f"{option}set_option autoImplicit false in\n"
        f"theorem {name} : ¬({statement.proposition}) := by\n"
        f"  intro h\n  have hw := h {' '.join(arguments)}\n  {proof}\n"
    )


# }}}


def theorem_name(owner: str, part: Part) -> str:
    """The name of a part's theorem: the claim's owner, then the part.

    :func:`lanky.lean.statement_of` makes it a Lean name, and declares it in
    the ``Lanky`` namespace.
    """
    return f"{owner}_{part.name}"
