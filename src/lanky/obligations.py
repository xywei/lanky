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
  by the rational bounds rescues it, and to keep the work per case small;
- *applications* of a hypothesis that is a theorem, cited by the plugin's
  object and stated in the part as it was proved: ``apply`` with the
  variables the plugin matched given by name, the others found by Lean where
  the theorem's conclusion is the goal, and each premise left a hypothesis
  of the part or arithmetic. Lean checks that the theorem applies, and so
  that the claim follows from it;
- *rewrites* with hypotheses that are equations, of two kinds, each
  :class:`Hints` entry saying by its type how it is used:

  - an :class:`Application` names an identity, a theorem whose conclusion is
    an equation, and the values of its variables: ``rw`` by it, before the
    applications, turns the goal's left side of it into its right side, so
    that a theorem stated of ``-beta / alpha`` applies to a goal that
    computes it another way. Its premises are left as goals, closed as an
    application's are;
  - a :class:`Rewrite` is one step of a script, in the order the plugin
    found them: what a program's statements store, unfolded into the claim
    wherever it applies, and a cited identity at the instances the plugin
    matched. Then the sums over a literal range are written out, and
    ``ring`` compares the two sides (Mathlib only).

Where unknowns multiply, a size times an index in a layout's address ``n * j
+ i``, ``omega`` reads each product as an atom of its own and knows nothing of
it. Three more hints take it the rest of the way, and the plugin finds them
from the shape of its claim, as ``nlinarith`` would search for them:

- *products*, ``0 ≤ a * b`` from ``0 ≤ a`` and ``0 ≤ b``, each factor shown by
  ``omega`` (``Int.mul_nonneg``): ``0 ≤ n * (n - 1 - j)`` bounds ``n * j`` by
  ``n * n - n``. A product marked ``in_cases`` is taken after the splits, in
  each case where its factors are not negative, and left out of the others;
- *quotients*, what Lean knows of ``a // m`` and ``a % m`` for a divisor that
  is not a number, which ``omega`` reads only by a number: the remainder and
  the quotient times the divisor add up to ``a``, the remainder is in ``0 ≤
  r < m`` and the quotient is not negative, each in the cases of the splits
  where its premise holds;
- *ring*, that the arithmetic is to be multiplied out before ``omega`` reads
  it: every product of sums is expanded and every product of atoms put in one
  order, so that ``n ^ 2 * k`` and ``k * (n * n)`` are one atom. A
  polynomial identity, ``n ^ 3 * e + n * j = ((e * n) * n + j) * n``, needs
  this and nothing else.

Each is a step of the argument, not a suggestion: where one of them is given,
the script is the one the plugin asked for, and a product or a quotient that
cannot be written fails it rather than being dropped.

A hypothesis that is a cited theorem's statement is named as a
:class:`Citation`: the Lean oracle restates it from the text the theorem's
own command proved, never by printing the theorem again, and refuses a part
whose conjunct is not the theorem's statement (:mod:`lanky.citations`).

A part about real numbers is printed in the Mathlib dialect and checked where
Mathlib is (:attr:`Part.mathlib`), its cases closed by ``linarith`` where an
integer part's are by ``omega``. One that reads an absolute value of a real
gets ``linarith`` with the bounds of each, ``0 ≤ |t|`` and ``-|t| ≤ t ≤
|t|``, which it does not know; a goal ``|a| ≤ b`` is taken apart into ``-b ≤
a`` and ``a ≤ b`` first, which is how a value within an allowance of another
is shown.

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

from lanky.audit import audit_lines
from lanky.induction import substitute
from lanky.lean import (
    LeanStatement,
    UnsupportedTerm,
    _affine,
    dialect,
    domain_guards,
    lean_identifier,
    number_type,
    render_term,
    statement_of,
)
from lanky.prelude import FinType, FnType, Refined
from lanky.terms import Exists, Forall, conjuncts, init_args

__all__ = [
    "Application",
    "Citation",
    "Counterexample",
    "Hints",
    "Instance",
    "Obligation",
    "Part",
    "Piece",
    "Product",
    "Quotient",
    "Rewrite",
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
class Application:
    """A hypothesis that is a theorem, applied to the goal: ``apply h3 (p := p) (c := c)``.

    ``hypothesis`` is its position among the conjuncts of the part's guard,
    as an :class:`Instance`'s is, and it has to be a universal; ``values``
    give some of its binders, by name, as lanky terms over the part's own
    variables: the families and the scalars a plugin matched to its arrays
    and sizes. Lean finds the others where the theorem's conclusion is the
    goal, and each premise left is a hypothesis of the part, or arithmetic
    ``omega`` proves, or, where Mathlib is, ``linarith``. A plugin that
    applies a cited theorem to what it decided (loopty applies one to a
    kernel's postcondition) states the theorem as a hypothesis of the part
    and says where it applies; Lean checks that it does.
    """

    hypothesis: int
    values: tuple[tuple[str, Any], ...] = ()


@dataclass(frozen=True)
class Product:
    """``0 ≤ left * right``, from ``0 ≤ left`` and ``0 ≤ right``: a step ``omega`` cannot take.

    ``left`` and ``right`` are lanky terms over the part's variables, and
    ``omega`` shows each factor not negative from the hypotheses and the
    hints before it: a factor that is another product's, written the same
    way, is that product's atom. One taken before the splits has to hold
    everywhere, and fails the script where it does not; one ``in_cases`` is
    taken after them, in each case where its factors are not negative, and
    left out of the others: ``0 ≤ n * (j' - j - 1)`` where ``j < j'``.
    """

    left: Any
    right: Any
    in_cases: bool = False


@dataclass(frozen=True)
class Quotient:
    """What Lean knows of ``dividend // divisor`` and ``dividend % divisor``.

    For a divisor that is not a number, which ``omega`` cannot divide by:
    that the remainder and the quotient times the divisor add up to the
    dividend, that the remainder is in ``0 ≤ r < divisor`` and that the
    quotient is not negative. They are taken after the splits, each in the
    cases where its premise holds (a positive divisor, a dividend that is not
    negative), so a split ``m ≤ 0 ∨ 0 < m`` keeps a divisor that can be zero.
    """

    dividend: Any
    divisor: Any


@dataclass(frozen=True)
class Rewrite:
    """A hypothesis that is an equation, the goal rewritten with it: ``simp only [h3]``.

    ``hypothesis`` is its position among the conjuncts of the part's guard,
    as an :class:`Instance`'s is, and it has to be a universal whose body is
    an equation. With no ``arguments``, the goal is rewritten with it from
    left to right wherever it applies, inside a sum too, each premise (a
    binder's bounds, the hypothesis's own guard) shown by ``omega`` from the
    part's hypotheses and the range of every sum the rewrite is under; the
    rewrites with no arguments that come one after another are made
    together, until none applies. That is how a plugin unfolds what its
    statements store, ``v[q, e, k, j, i] == sum(Fr[q, i, a] * w[q, e, k, j,
    a] for a in Fin[n])``, into a claim about what a program leaves.

    With ``arguments``, lanky terms over the part's own variables, one for
    each binder of the hypothesis, outermost first, the one instance is
    rewritten with, ``rw [← h1 n (by omega) (Fr (3 * x + 0)) ...]``, each
    premise shown by ``omega``. The value of a family may be a family of the
    part applied to its first arguments, ``Fr(3 * x + 0)``, which is the
    family of what is left. ``backwards`` rewrites the right side of the
    instance into its left. That is how a cited theorem, an identity such as
    sum factorization, is used where the plugin found its one side.
    """

    hypothesis: int
    arguments: tuple[Any, ...] = ()
    backwards: bool = False


@dataclass(frozen=True)
class Hints:
    """What a solver found that ``omega`` does not look for (see the module docstring).

    ``rewrites`` are equations among the part's hypotheses, of two kinds. An
    :class:`Application` names an identity and the values of its variables,
    rewritten in the goal before ``applications`` are applied. A
    :class:`Rewrite` is a step of the script that unfolds a goal with its
    equations, in order, and compares the two sides by ``ring``.
    """

    instances: tuple[Instance, ...] = ()
    witness: tuple[Piece, ...] = ()
    splits: tuple[Any, ...] = ()
    applications: tuple[Application, ...] = ()
    products: tuple[Product, ...] = ()
    quotients: tuple[Quotient, ...] = ()
    ring: bool = False
    rewrites: tuple[Rewrite | Application, ...] = ()

    def __bool__(self) -> bool:
        """Whether there is any hint at all."""
        return bool(
            self.instances
            or self.witness
            or self.splits
            or self.applications
            or self.products
            or self.quotients
            or self.ring
            or self.rewrites
        )

    @property
    def multiplies(self) -> bool:
        """Whether the part's arithmetic multiplies unknowns, and is multiplied out."""
        return bool(self.products or self.quotients or self.ring)


@dataclass(frozen=True)
class Citation:
    """A hypothesis of a part that restates a claim proved elsewhere: a cited theorem.

    ``hypothesis`` is its position among the conjuncts of the part's guard,
    as an :class:`Instance`'s is, and the conjunct is the claim's term as
    its theory states it (:attr:`lanky.theory.Theorem.term`); ``fact`` is the
    claim's fact id and ``name`` what a message calls it. The Lean oracle
    restates the hypothesis from the text the claim's own command proved
    (:attr:`lanky.lean.LeanStatement.as_cited`), never by printing the term
    again, so that a printer that dropped a condition of the claim could not
    hand the part a hypothesis that proves anything. A conjunct that is not
    the claim's term is refused before Lean is asked.
    """

    hypothesis: int
    fact: str
    name: str = ""


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

    ``mathlib`` marks a part about real numbers, which core Lean does not
    have: it is printed in the Mathlib dialect (``ℝ``) and checked only where
    Mathlib is imported, its cases closed by ``linarith`` where an integer
    part's are by ``omega``. Without Mathlib the claim is left to the oracles
    after Lean, which says why.

    ``citations`` name the hypotheses that restate a cited claim
    (:class:`Citation`), which the Lean oracle restates from the text the
    claim's command proved.
    """

    name: str
    label: str
    term: Any
    hints: Hints = field(default_factory=Hints)
    fallback: Any = field(default=None, compare=False, repr=False)
    mathlib: bool = False
    citations: tuple[Citation, ...] = ()


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


def part_statement(
    part: Part, name: str, restated: Mapping[int, str] | None = None
) -> LeanStatement:
    """The part's term as a Lean theorem named ``name``: core Lean, or Mathlib's for reals.

    Core Lean whatever the session for a part of integer arithmetic, so that
    the printed source is the one that replays with ``lean`` alone; the
    Mathlib dialect for a part about real numbers (:attr:`Part.mathlib`).
    ``restated`` gives the hypotheses restated from a cited claim's proved
    text, by their position among the guard's conjuncts (see
    :class:`Citation` and :func:`lanky.lean.statement_of`).

    Raises:
        UnsupportedTerm: If the part's term leaves the printer's fragment.
    """
    return statement_of(
        part.term,
        name,
        mathlib=bool(getattr(part, "mathlib", False)),
        restated=restated,
    )


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
    if isinstance(expr, prim.Call):
        # a family of families applied one argument at a time, R(a)(b), is
        # one application, as an array indexed R[a, b] is
        arguments: tuple[Any, ...] = ()
        head: Any = expr
        while isinstance(head, prim.Call):
            arguments = (*head.parameters, *arguments)
            head = head.function
        if isinstance(head, prim.Variable):
            out.append((head.name, arguments, expr))
            _applications(arguments, out)
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
                index = start + len(lines)
                if len(arguments) == 1:
                    lines.append(f"have hc{index} : {left} = {right} := by congr 1 <;> omega")
                    continue
                lines.append(_congruence_chain(statement, name, arguments, theirs, index))
    if getattr(part, "mathlib", False):
        # a premise of one omega cannot show leaves it out, and the rest stand
        lines = [f"try {line}" for line in lines]
    return lines


def _congruence_chain(
    statement: LeanStatement,
    name: str,
    mine: Sequence[Any],
    theirs: Sequence[Any],
    index: int,
) -> str:
    """``have hc : R x y = R x' y' := ...``: one argument at a time, by ``congrArg``.

    ``congr`` takes ``R (b + 2)`` apart into ``b + 2`` and further, to ``b``
    and ``2``, where ``2 + b`` on the other side has no such parts, so the
    equation is built argument by argument instead: each argument's
    equation by ``omega``, carried through the application by ``congrArg``
    of the application with that argument left out, and the steps chained
    by ``Eq.trans``. The application is written without the cast a natural
    value takes, as an equation of its values, which ``omega`` reads.
    """
    used = set(statement.variables) | {binder for binder, _ in statement.binders}
    hole = "x_cong"
    while hole in used:
        hole += "_"
    head = lean_identifier(name)
    first = [render_term(argument, statement.types, atomic=True) for argument in mine]
    second = [render_term(argument, statement.types, atomic=True) for argument in theirs]
    steps = []
    for position in range(len(first)):
        around = [*second[:position], hole, *first[position + 1 :]]
        equation = f"{first[position]} = {second[position]}"
        steps.append(
            f"(congrArg (fun {hole} => {head} {' '.join(around)}) (by omega : {equation}))"
        )
    proof = steps[0]
    for step in steps[1:]:
        proof = f"({proof}.trans {step})"
    return (
        f"have hc{index} : {head} {' '.join(first)} = {head} {' '.join(second)} := {proof}"
    )


def _discharged_instance_line(
    statement: LeanStatement, part: Part, instance: Instance, index: int
) -> str:
    """``try have hi0 := h3 a (by omega) b (by omega)``: an instance with its premises shown.

    For a part about reals, closed by ``linarith``, which reads equations and
    not the implications an instance of :func:`_instance_line` keeps: every
    premise, a binder's guard or a conjunct of the hypothesis's own guard, is
    shown by ``omega`` at the point. An instance whose premises do not hold
    there says nothing, and ``try`` leaves it out.

    Raises:
        UnsupportedTerm: As :func:`_instance_line` does.
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
    scope = dict(statement.types)
    pieces: list[str] = []
    for (var, domain), value in zip(hypothesis.binders, instance.arguments, strict=True):
        pieces.append(render_term(value, statement.types, atomic=True))
        pieces += ["(by omega)"] * len(domain_guards(var, domain, scope))
        scope = {**scope, var.name: domain}
    pieces += ["(by omega)"] * len(conjuncts(hypothesis.guard))
    return f"try have hi{index} := {name} {' '.join(pieces)}"


def _application_line(statement: LeanStatement, part: Part, application: Application) -> str:
    """``apply h3 (p := p) (c := c)``: a hypothesis that is a theorem, applied to the goal.

    Raises:
        UnsupportedTerm: If it names no universal hypothesis.
    """
    guards = list(conjuncts(part.term.guard)) if isinstance(part.term, Forall) else []
    if not 0 <= application.hypothesis < len(guards):
        raise UnsupportedTerm(
            f"the application names hypothesis {application.hypothesis}, and the part "
            f"has {len(guards)}"
        )
    hypothesis = guards[application.hypothesis]
    if not isinstance(hypothesis, Forall):
        raise UnsupportedTerm(f"hypothesis {application.hypothesis} is not a universal")
    binders = {var.name for var, _ in hypothesis.binders}
    name = _hypothesis_names(statement)[application.hypothesis]
    values = [
        f"({lean_identifier(binder)} := {_value(value, statement)})"
        for binder, value in application.values
        if binder in binders
    ]
    return " ".join(["apply", name, *values])


#: The longest literal range a sum the rewrites leave is written out over,
#: term by term: ``∑ d ∈ Finset.Ico 0 3, f d`` is ``f 0 + f 1 + f 2``.
_WRITTEN_OUT = 8


def _literal_ranges(expr: Any, out: set[int]) -> None:
    """The literal bounds of the sums below ``expr``: ``3`` for a sum over ``Fin[3]``."""
    from lanky.terms import Sum

    if isinstance(expr, tuple | list):
        for item in expr:
            _literal_ranges(item, out)
        return
    if isinstance(expr, Sum):
        for _var, domain in expr.binders:
            bound = getattr(domain, "bound", None)
            if (
                isinstance(domain, FinType)
                and isinstance(bound, int)
                and not isinstance(bound, bool)
                and 0 < bound <= _WRITTEN_OUT
            ):
                out.add(bound)
        _literal_ranges(expr.body, out)
        if expr.guard is not None:
            _literal_ranges(expr.guard, out)
        return
    if isinstance(expr, Forall | Exists):
        _literal_ranges(expr.body, out)
        if expr.guard is not None:
            _literal_ranges(expr.guard, out)
        return
    if isinstance(expr, prim.ExpressionNode):
        _literal_ranges(init_args(expr), out)


def _rewrite_lines(statement: LeanStatement, part: Part, rewrites: Sequence[Rewrite]) -> list[str]:
    """The script of :class:`Rewrite` hints: the rewrites in order, the sums written out, ring.

    Rewrites with no arguments that come one after another are one ``simp
    only``, whose discharger shows each premise by ``omega``, from the range
    of a sum the rewrite is under once ``Finset.mem_Ico`` has read its
    membership; with Mathlib, a premise that is a condition of the part's,
    a hypothesis that is no equation (``c t - y s ≠ 0`` for every ``s`` a
    sum ranges over), is shown by that hypothesis at the sum's point, its
    own premises by ``omega`` (:func:`_condition_dischargers`). A rewrite
    with arguments is a ``rw`` of that instance. Each
    line is for every goal left, so a rewrite that closes the goal by
    ``rfl`` leaves the lines after it nothing to do. Then a sum over a
    literal range, ``Finset.Ico 0 3``, is written out term by term, and
    ``ring_nf`` compares the two sides; a product whose factors the two
    sides order differently, under a sum where ``ring_nf`` normalizes each
    side's summand apart, is put in one order by ``mul_comm`` and
    ``mul_left_comm`` first.

    Raises:
        UnsupportedTerm: If a rewrite names no hypothesis, or one that is
            not a universal over as many variables as it has arguments.
    """
    guards = list(conjuncts(part.term.guard)) if isinstance(part.term, Forall) else []
    names = _hypothesis_names(statement)
    mathlib = bool(getattr(part, "mathlib", False))
    if mathlib:
        member = statement.qualified("Finset.mem_Ico")
        conditions = _condition_dischargers(statement, guards, names, member)
        discharge = f"(first | omega | (simp only [{member}] at *; omega){conditions})"
    else:
        discharge = "omega"
    lines: list[str] = []
    batch: list[str] = []
    rewritten: list[Any] = []

    def flush() -> None:
        if batch:
            lines.append(f"all_goals simp (disch := {discharge}) only [{', '.join(batch)}]")
            batch.clear()

    for rewrite in rewrites:
        if not 0 <= rewrite.hypothesis < len(guards):
            raise UnsupportedTerm(
                f"the rewrite names hypothesis {rewrite.hypothesis}, and the part has "
                f"{len(guards)}"
            )
        hypothesis = guards[rewrite.hypothesis]
        rewritten.append(hypothesis)
        name = names[rewrite.hypothesis]
        arrow = "← " if rewrite.backwards else ""
        if not rewrite.arguments:
            batch.append(f"{arrow}{name}")
            continue
        if not isinstance(hypothesis, Forall) or len(hypothesis.binders) != len(
            rewrite.arguments
        ):
            raise UnsupportedTerm(
                f"hypothesis {rewrite.hypothesis} is not a universal over "
                f"{len(rewrite.arguments)} variables"
            )
        flush()
        scope = dict(statement.types)
        pieces: list[str] = []
        for (var, domain), value in zip(hypothesis.binders, rewrite.arguments, strict=True):
            pieces.append(render_term(value, statement.types, atomic=True))
            pieces += ["(by omega)"] * len(domain_guards(var, domain, scope))
            scope = {**scope, var.name: domain}
        pieces += ["(by omega)"] * len(conjuncts(hypothesis.guard))
        lines.append(f"all_goals rw [{arrow}{name} {' '.join(pieces)}]")
    flush()
    if not mathlib:
        return [*lines, "all_goals first | omega | rfl"]
    ranges: set[int] = set()
    _literal_ranges([statement.goal_term, *rewritten], ranges)
    if ranges:
        ico = statement.qualified("Finset.Ico")
        shown = [
            f"show {ico} (0 : ℤ) {bound} = {{{', '.join(map(str, range(bound)))}}} by decide"
            for bound in sorted(ranges)
        ]
        written = ("Finset.sum_insert", "Finset.sum_singleton")
        lemmas = ", ".join([*shown, *map(statement.qualified, written)])
        lines.append(f"all_goals try simp (disch := decide) only [{lemmas}]")
    order = ", ".join(
        statement.qualified(name) for name in ("mul_comm", "mul_assoc", "mul_left_comm")
    )
    lines.append(
        "all_goals first | (ring_nf; done) "
        f"| (ring_nf; simp only [{order}]; done) | linarith"
    )
    return lines
def _condition_dischargers(
    statement: LeanStatement, guards: Sequence[Any], names: Sequence[str], member: str
) -> str:
    """The discharger's alternatives for a premise that is one of the part's conditions.

    A rewrite by a theorem with a condition, ``alpha ≠ 0``, under a sum
    leaves the condition at the sum's point, ``c t - y s ≠ 0`` with ``s ∈
    Finset.Ico 0 ns``, and the part states it for every point of the sum's
    range, ``∀ s, 0 ≤ s → s < ns → c t - y s ≠ 0``. Each such hypothesis, a
    universal whose body is no equation, is tried at the point by
    ``refine``, which unifies its conclusion with the premise first, its
    binders' bounds and its guard then shown by ``omega`` from the
    membership ``Finset.mem_Ico`` reads; a condition at no sum's point, a
    ``≠`` of the part's own variables, is ``assumption``. ``""`` for a part
    with no condition, whose discharger is as it was.
    """
    out: list[str] = []
    stated = False
    for name, hypothesis in zip(names, guards, strict=False):
        if not isinstance(hypothesis, Forall):
            # a condition at no sum's point, c t - y 0 ≠ 0, is a hypothesis as it is
            stated = stated or (
                isinstance(hypothesis, prim.Comparison) and hypothesis.operator == "!="
            )
            continue
        body = hypothesis.body
        if isinstance(body, prim.Comparison) and body.operator == "==":
            continue
        scope = dict(statement.types)
        pieces: list[str] = []
        for var, domain in hypothesis.binders:
            pieces.append("_")
            pieces += ["?_"] * len(domain_guards(var, domain, scope))
            scope = {**scope, var.name: domain}
        pieces += ["?_"] * len(conjuncts(hypothesis.guard))
        out.append(
            f"((try simp only [{member}] at *); refine {name} {' '.join(pieces)} <;> omega)"
        )
    if stated:
        out.insert(0, "assumption")
    return "".join(f" | {item}" for item in out)


def _value(value: Any, statement: LeanStatement) -> str:
    """A value a script gives a binder, printed in the statement's dialect and names.

    A part about reals is Mathlib's, and a value in it may be too: ``conj(z)``
    or a true division, which core Lean's printer declines.
    """
    return render_term(
        value, statement.types, mathlib=statement.mathlib, shadowed=statement.shadowed
    )


def _rewrite_line(statement: LeanStatement, part: Part, rewrite: Application) -> str:
    """``rw [h3 (alpha := c t - y s) (beta := z t - c t)]``: an identity, rewritten.

    The hypothesis is a universal whose body is an equation; its premises,
    a guard such as ``alpha ≠ 0``, are left as goals after the rewritten one.

    Raises:
        UnsupportedTerm: If it names no universal hypothesis that is an equation.
    """
    guards = list(conjuncts(part.term.guard)) if isinstance(part.term, Forall) else []
    if not 0 <= rewrite.hypothesis < len(guards):
        raise UnsupportedTerm(
            f"the rewrite names hypothesis {rewrite.hypothesis}, and the part has "
            f"{len(guards)}"
        )
    hypothesis = guards[rewrite.hypothesis]
    if not (
        isinstance(hypothesis, Forall)
        and isinstance(hypothesis.body, prim.Comparison)
        and hypothesis.body.operator == "=="
    ):
        raise UnsupportedTerm(f"hypothesis {rewrite.hypothesis} is no identity to rewrite by")
    binders = {var.name for var, _ in hypothesis.binders}
    name = _hypothesis_names(statement)[rewrite.hypothesis]
    values = [
        f"({lean_identifier(binder)} := {_value(value, statement)})"
        for binder, value in rewrite.values
        if binder in binders
    ]
    return f"rw [{' '.join([name, *values])}]"


def _absolute_values(statement: LeanStatement) -> list[str]:
    """Each real ``t`` the statement takes the absolute value of, as Lean source, once.

    The operands of ``|t|`` in the goal and the hypotheses, innermost first,
    each printed as the statement prints it. A complex one's modulus is a
    norm, whose bounds are another lemma's, and is left out, as is one under
    a binder of the goal or a hypothesis, which names what the script cannot.
    """
    found: list[Any] = []

    def visit(node: Any) -> None:
        if isinstance(node, tuple | list):
            for item in node:
                visit(item)
            return
        if isinstance(node, Forall | Exists) or not isinstance(node, prim.ExpressionNode):
            # under a binder, an operand names what the script cannot
            return
        visit(init_args(node))
        if type(node).__name__ == "Abs":
            found.append(node.operand)

    visit(statement.goal_term)
    visit([term for term in statement.hypothesis_terms if term is not None])
    out: list[str] = []
    for operand in found:
        try:
            if number_type(operand, statement.types, mathlib=True) == "ℂ":
                continue
            # printed as the statement is, in Mathlib's dialect
            text = render_term(
                operand, statement.types, mathlib=True, shadowed=statement.shadowed
            )
        except UnsupportedTerm:
            continue
        if text not in out:
            out.append(text)
    return out


def _absolute_value_attempts(statement: LeanStatement, intro: str) -> list[tuple[str, str]]:
    """``linarith`` with the bounds of every absolute value of a real, and ``abs_le`` first.

    ``linarith`` takes ``|t|`` for an atom and knows nothing of it: given
    ``0 ≤ |t|``, ``t ≤ |t|`` and ``-|t| ≤ t``, it reasons about a value
    within an allowance of another, ``|a - b| ≤ e * (|b| + 1)``, once the
    goal's own bars are taken apart (``abs_le``) into ``-e * (|b| + 1) ≤ a -
    b`` and ``a - b ≤ e * (|b| + 1)``. A statement with no absolute value of
    a real gets neither attempt.
    """
    operands = _absolute_values(statement)
    if not operands:
        return []
    nonneg = statement.qualified("abs_nonneg")
    above = statement.qualified("le_abs_self")
    below = statement.qualified("neg_abs_le")
    bounds = ", ".join(
        f"{lemma} ({operand})" for operand in operands for lemma in (nonneg, above, below)
    )
    out = []
    goal = statement.goal_term
    while isinstance(goal, Forall):
        goal = goal.body
    if (
        isinstance(goal, prim.Comparison)
        and goal.operator == "<="
        and type(goal.left).__name__ == "Abs"
    ):
        out.append(
            (
                "linarith, with the absolute values taken apart",
                f"{intro}rw [{statement.qualified('abs_le')}]\n"
                f"constructor <;> linarith [{bounds}]",
            )
        )
    out.append(("linarith, with the bounds of the absolute values", f"{intro}linarith [{bounds}]"))
    return out


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


#: The lemmas that multiply out integer arithmetic: powers by a number as
#: products, products of sums expanded, and every product of atoms put in one
#: order by commutativity and associativity, which ``simp`` rewrites with as an
#: ordered rewriting and so does not loop. A conjunct ``simp`` closes is
#: ``True``, which ``omega`` does not read, and goes.
_RING_LEMMAS = (
    "Int.pow_succ",
    "Int.pow_zero",
    "Int.one_mul",
    "Int.mul_one",
    "Int.zero_mul",
    "Int.mul_zero",
    "Int.mul_add",
    "Int.add_mul",
    "Int.mul_sub",
    "Int.sub_mul",
    "Int.neg_mul",
    "Int.mul_neg",
    "Int.mul_assoc",
    "Int.mul_comm",
    "Int.mul_left_comm",
    "true_and",
    "and_true",
)


def _counted(count: int, one: str, many: str) -> str:
    """``a product``, ``3 products``: a count of hints in words."""
    return one if count == 1 else f"{count} {many}"


def _product_line(statement: LeanStatement, product: Product, index: int) -> str:
    """``have hp0 : 0 ≤ n * (n - 1 - j) := Int.mul_nonneg (by omega) (by omega)``.

    Raises:
        UnsupportedTerm: If a factor leaves the printer's fragment.
    """
    text = render_term(prim.Product((product.left, product.right)), statement.types)
    lemma = statement.qualified("Int.mul_nonneg")
    return f"have hp{index} : 0 ≤ {text} := {lemma} (by omega) (by omega)"


def _quotient_lines(statement: LeanStatement, quotient: Quotient, index: int) -> list[str]:
    """What Lean knows of ``a // m`` and ``a % m``, as the statement prints them.

    A divisor that is not a positive number prints as ``Int.fdiv a m`` and
    ``Int.fmod a m`` (:func:`lanky.lean.render_term`), so the facts are
    those of ``Int.fdiv`` and ``Int.fmod``: ``Int.fmod a m + Int.fdiv a m * m
    = a``, the remainder in ``0 ≤ r < m`` where ``0 < m``, and the quotient
    not negative where neither is ``a`` nor ``m``. A positive number is a
    divisor ``omega`` divides by itself, and has none.

    Raises:
        UnsupportedTerm: If either operand leaves the printer's fragment.
    """
    divisor = quotient.divisor
    if isinstance(divisor, int) and not isinstance(divisor, bool) and divisor > 0:
        return []
    a = render_term(quotient.dividend, statement.types, atomic=True)
    m = render_term(divisor, statement.types, atomic=True)
    q = statement.qualified
    return [
        f"have hq{index} := {q('Int.fmod_add_fdiv_mul')} {a} {m}",
        f"have hq{index}_r := {q('Int.fmod_nonneg_of_pos')} {a} (show 0 < {m} by omega)",
        f"have hq{index}_s := {q('Int.fmod_lt_of_pos')} {a} (show 0 < {m} by omega)",
        f"have hq{index}_q := {q('Int.fdiv_nonneg')} (show 0 ≤ {a} by omega) "
        f"(show 0 ≤ {m} by omega)",
    ]


def _multiplied_attempt(
    statement: LeanStatement,
    hints: Hints,
    lines: Sequence[str],
    said: Sequence[str],
    split_lines: Sequence[str],
) -> tuple[str, str] | None:
    """The script for a part whose arithmetic multiplies unknowns (see the module).

    The instances first (``lines``), then the products that hold everywhere,
    then the splits; in each case, every fact about a quotient and every
    product ``in_cases`` whose premises ``omega`` shows there, each tried and
    left out where it does not hold; then the witness, given whole, of a goal
    that is an existential; and last the arithmetic multiplied out
    (:data:`_RING_LEMMAS`) in every hypothesis and the goal, and ``omega`` on
    what is left in each case. ``None`` when a product, a quotient or the
    witness cannot be written for this statement: unlike an instance, each is
    a step of the argument, and the attempt without it would fail.
    """
    goal = statement.goal_term
    out = list(lines)
    words = list(said)
    try:
        everywhere = [p for p in hints.products if not p.in_cases]
        in_cases = [p for p in hints.products if p.in_cases]
        for index, product in enumerate(everywhere):
            out.append(_product_line(statement, product, index))
        out += split_lines
        each = "all_goals " if split_lines else ""
        for index, quotient in enumerate(hints.quotients):
            out += [f"{each}try {line}" for line in _quotient_lines(statement, quotient, index)]
        for index, product in enumerate(in_cases, start=len(everywhere)):
            out.append(f"{each}try {_product_line(statement, product, index)}")
        witness = ""
        if hints.witness:
            if (
                len(hints.witness) != 1
                or hints.witness[0].condition is not None
                or hints.witness[0].disjunct is not None
                or not isinstance(goal, Exists)
                or len(goal.binders) != len(hints.witness[0].values)
            ):
                return None
            scope = dict(statement.types)
            for var, domain in goal.binders:
                if domain_guards(var, domain, scope):
                    # a binder with conditions of its own between the next
                    return None
                scope = {**scope, var.name: domain}
            values = ", ".join(
                render_term(value, statement.types) for value in hints.witness[0].values
            )
            witness = f"refine ⟨{values}, ?_⟩"
    except UnsupportedTerm:
        return None
    if hints.products:
        words.append(_counted(len(hints.products), "a product", "products"))
    if hints.quotients:
        words.append(_counted(len(hints.quotients), "a quotient", "quotients"))
    if split_lines:
        words.append("a case split")
    if witness:
        out.append(f"{each}{witness}")
        words.append("the witness")
    ring = ", ".join(statement.qualified(lemma) for lemma in _RING_LEMMAS)
    out.append(f"{each or 'all_goals '}(try simp only [{ring}] at *)")
    out.append("all_goals omega")
    words.append("the arithmetic multiplied out")
    listed = words[0] if len(words) == 1 else f"{', '.join(words[:-1])} and {words[-1]}"
    return f"omega, with {listed}", "\n".join(out)


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
    mathlib = bool(getattr(part, "mathlib", False))
    # a part about reals is closed by linarith, an integer one by omega
    closer = "linarith" if mathlib else "omega"
    if not isinstance(goal, Exists) and not (
        hints_witness_only(part) and isinstance(goal, prim.LogicalOr)
    ):
        out.append(("omega", f"{intro}omega"))
    if mathlib:
        out += _absolute_value_attempts(statement, intro)
    hints = part.hints
    if not hints:
        return out
    rewrites: list[str] = []
    for rewrite in getattr(hints, "rewrites", ()):
        if not isinstance(rewrite, Application):
            # a step of the unfolding script below, not an identity
            continue
        try:
            rewrites.append(_rewrite_line(statement, part, rewrite))
        except UnsupportedTerm:
            continue
    for application in getattr(hints, "applications", ()):
        try:
            line = _application_line(statement, part, application)
        except UnsupportedTerm:
            continue
        rest = "first | assumption | omega" + (" | linarith" if mathlib else "")
        if rewrites:
            # the identities first, which make the goal what the theorem concludes
            identities = "identity" if len(rewrites) == 1 else "identities"
            script = "\n".join(["intros", *rewrites, line, f"all_goals {rest}"])
            out.append((f"rewritten by the {identities}, the theorem applied", script))
        else:
            out.append(("the theorem applied", f"intros\n{line}\nall_goals {rest}"))
        if mathlib:
            # ``apply`` unifies the conclusion's numerals with the goal's, and
            # ``↑(1 : ℤ)`` is not ``(1 : ℂ)`` to it: rewrite the goal by the
            # theorem instead, and leave the numerals to norm_num
            by_theorem = "rw [" + line.removeprefix("apply ") + "]"
            to_nat = statement.qualified("Int.toNat")
            closers = f"{rest} | (norm_num [{to_nat}]; done)"
            script = "\n".join(["intros", *rewrites, by_theorem, f"all_goals {closers}"])
            what = "the theorem" if not rewrites else f"the {identities} and the theorem"
            out.append((f"rewritten by {what}", script))
    steps = [step for step in getattr(hints, "rewrites", ()) if isinstance(step, Rewrite)]
    if steps:
        try:
            script = _rewrite_lines(statement, part, steps)
        except UnsupportedTerm:
            script = []
        if script:
            if isinstance(goal, Forall):
                from lanky.oracles.lean import _goal_intro

                with dialect(mathlib):
                    names = _goal_intro(statement)[0]
                script = [f"intro {' '.join(names)}", *script]
            how = "the equations rewritten with, in order, then " + (
                "ring" if mathlib else "omega"
            )
            out.append((how, "\n".join(script)))
    lines: list[str] = []
    said: list[str] = []
    instances: list[str] = []
    usable: list[Instance] = []
    for instance in hints.instances:
        # an instance that cannot be written is dropped, and the others kept
        try:
            if mathlib:
                line = _discharged_instance_line(statement, part, instance, len(instances))
            else:
                line = _instance_line(statement, part, instance, len(instances))
        except UnsupportedTerm:
            continue
        instances.append(line)
        usable.append(instance)
    if instances:
        lines += instances
        lines += _congruence_lines(statement, part, usable, 0)
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
        lines_of_split = [
            f"have hs{index} : {text} := by omega",
            f"rcases hs{index} with {pattern}",
        ]
        if split_lines:
            # every case the splits before made is split again, not only the
            # first: the cases are their cross-product
            split_lines.append("all_goals")
            split_lines += ["  " + line for line in lines_of_split]
        else:
            split_lines += lines_of_split
    if getattr(hints, "multiplies", False) and not mathlib:
        # where unknowns multiply, the hints above are tried with the
        # products and quotients, and the arithmetic multiplied out
        found = _multiplied_attempt(statement, hints, lines, said, split_lines)
        if found is not None:
            out.append((found[0], intro + found[1]))
            return out
        # a witness in pieces, which that script does not give: the script
        # below, as a part with no products has it (Codex)
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
        lines.append(f"all_goals {closer}" if split_lines else closer)
    if said and lines:
        out.append((f"{closer}, with {' and '.join(said)}", intro + "\n".join(lines)))
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
        f"\n{audit_lines((name,))}\n"
    )


# }}}


def theorem_name(owner: str, part: Part) -> str:
    """The name of a part's theorem: the claim's owner, then the part.

    :func:`lanky.lean.statement_of` makes it a Lean name, and declares it in
    the ``Lanky`` namespace.
    """
    return f"{owner}_{part.name}"
