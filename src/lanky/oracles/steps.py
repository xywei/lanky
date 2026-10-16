"""Steps of a written proof, compiled to Lean: chains, named facts, and the facts a step cites.

The design idea. A step of a proof says what follows and why: a link of a
chain, ``.equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))``, or a case's
``return recurrence, claim(n - 1)``. Python decides what the step means, the
facts it cites and the point each is cited at, and writes the Lean that
checks it; Lean checks it, or says where it fails. Nothing Python writes here
is trusted: a wrong point, a wrong multiplier or a missing fact costs a step
that does not close, never a proof of something else, because the goal of
every step and the statement of every cited fact come from the claim and its
hypotheses, which the printer states (see :mod:`lanky.lean`).

*A step.* Each fact the step cites (:mod:`lanky.citations`) is put in the
context at its point, ``have h := recurrence (a - 2) (by omega) b (by
omega)``: a fact the proof left uncalled is at the one point that lines it up
with the step (:func:`lanky.matching.single_point`), and each condition it has
there is shown by ``omega`` where it is integer arithmetic and by Mathlib's
closers otherwise. Then the goal is closed, by the first of: the fact itself
(``exact``); a linear combination of the facts, with the multipliers Python
finds (:func:`lanky.induction.find_certificate`, limited to the facts cited);
``linarith`` and ``nlinarith`` with them. In core Lean, without Mathlib, it is
``omega`` once ``R (a - 2 + 2) b`` is written ``R a b``, then ``grind``. Each
step gets its own heartbeat budget, so one stray ``nlinarith`` cannot spend
the command's time.

*What the compiler adds, which the proof never writes.* A denominator that is
an integer the case shows is not zero gets the fact that it is not, cast into
the field, ``(n : ℂ) ≠ 0`` (:func:`nonzero_lines`), which is what ``field_simp``
needs to clear it; ``alpha * conj(alpha)`` gets the normSq rule. And an
exponent the case shows is a natural is ``e.toNat`` inside a step, where the
statement printer declines it (:func:`lanky.lean.proof_exponents`): where the
goal has ``x ^ n.toNat`` and a fact ``x ^ (n - 1).toNat``, the goal is
rewritten to ``x ^ (n - 1).toNat * x`` first (:func:`shift_lines`), so the two
are one atom to ``ring``.

*A chain* is a ``calc``, one link to a step, each closed as above. It is
compiled tolerantly: where its ends print as the claim's two sides the
``calc`` is the case's proof, and otherwise it is a fact of the case, ``have
chain := calc ...``, from which the claim is closed by ``linear_combination``,
which does not mind ``-x`` against ``(-1) * x``. A named chain, ``recurrence =
a[n].equals(...)``, is ``have recurrence : <its statement> := by ...``. A link
written ``by=...`` is ``sorry``, and its line is recorded (:attr:`Script.holes`):
the proof is then "closed with holes" (:func:`lanky.oracles.lean.holes_verdict`).

The output is a :class:`Script`: Lean lines, each with the Python line it
came from, which is how a message Lean gives is put back at its line; the
holes; the theorems the declaration has to take as hypotheses, by their cited
texts (:mod:`lanky.citations`); and the outline ``lanky check --steps``
prints (:func:`outline_text`).
"""

from __future__ import annotations

import os
from collections.abc import Iterable, Mapping, Sequence
from dataclasses import dataclass, field
from typing import Any

import pymbolic.primitives as prim

from lanky.chains import Chain, Link
from lanky.citations import Citation, citation_of
from lanky.induction import Case, Lemma, find_certificate
from lanky.lean import UnsupportedTerm, number_type, proof_exponents, render_term
from lanky.matching import (
    FamilyValue,
    NoSinglePoint,
    implied,
    instantiate,
    same,
    single_point,
)
from lanky.oracles.lean import COMBINATION_NORM
from lanky.prelude import FinType, FnType, Refined, Sort
from lanky.terms import Comparison, Elementary, Var, init_args, render

__all__ = [
    "DEFAULT_HEARTBEATS",
    "LinkDraw",
    "Script",
    "StepError",
    "StepScope",
    "chain_script",
    "draw_links",
    "drawn_status",
    "hole_script",
    "named_script",
    "nonzero_lines",
    "outline_text",
    "resolve",
    "shift_lines",
    "step_script",
]

#: The heartbeats one step may take, about a tenth of a 60-second command.
DEFAULT_HEARTBEATS = 400000

#: What a link's relation is in Lean.
_LEAN_RELATION = {"==": "=", "<=": "≤", "<": "<", ">=": "≥", ">": ">", "!=": "≠"}

#: The closers of a condition of a cited fact that is not integer arithmetic.
_MATHLIB_CONDITION = "(by first | assumption | omega | positivity | linarith | nlinarith)"

#: The same, in core Lean.
_CORE_CONDITION = "(by first | assumption | omega)"


class StepError(Exception):
    """A step lanky cannot write the Lean of, in the proof's terms, with the fix.

    Attributes:
        line: The Python line of the step.
        path: The file it is in.
        fix: What to write instead, or ``""``.
    """

    def __init__(
        self, message: str, line: int | None = None, path: str | None = None, fix: str = ""
    ) -> None:
        where = f"{os.path.basename(path)}:{line}" if path and line else (str(line or ""))
        super().__init__(f"{where}: {message}" if where else message)
        self.line = line
        self.path = path
        self.fix = fix


@dataclass
class StepScope:
    """What is in scope where a step is compiled.

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
        heartbeats: The budget of each step.
        path: The file of the proof, for messages.
    """

    types: Mapping[str, Any]
    facts: tuple[Any, ...] = ()
    mathlib: bool = True
    shadowed: frozenset[str] = frozenset()
    taken: set[str] = field(default_factory=set)
    heartbeats: int = DEFAULT_HEARTBEATS
    path: str | None = None

    def fresh(self, stem: str) -> str:
        """A name like ``stem`` that nothing in the declaration uses yet, then taken."""
        name, index = stem, 1
        while name in self.taken or name in self.types:
            name = f"{stem}_{index}"
            index += 1
        self.taken.add(name)
        return name

    def render(
        self, term: Any, atomic: bool = False, types: Mapping[str, Any] | None = None
    ) -> str:
        """A term as Lean source, in the scope's dialect, its natural exponents as ``.toNat``."""
        scope = dict(self.types if types is None else types)
        if isinstance(term, FamilyValue):
            inner = dict(scope)
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


@dataclass
class Script:
    """Lean a step compiles to, and what the declaration around it needs to know.

    Attributes:
        lines: The tactic lines, indented from ``0``, each with the Python
            line it came from (``None`` for what the compiler adds).
        holes: The Python lines of the steps left open (``by=...``), each
            compiled to ``sorry``.
        restated: The theorems the steps cite, by the name the declaration
            takes each as a hypothesis under, with the cited text to state it.
        rests_on: The ledger ids of the theorems cited, in order.
        outline: Rows of the proof's outline, ``(line, left, relation, term,
            reason)``, which :func:`outline_text` lays out.
    """

    lines: list[tuple[str, int | None]] = field(default_factory=list)
    holes: list[int | None] = field(default_factory=list)
    restated: dict[str, Citation] = field(default_factory=dict)
    rests_on: list[str] = field(default_factory=list)
    outline: list[tuple[int | None, str, str, str, str]] = field(default_factory=list)

    def add(self, text: str, line: int | None = None, indent: int = 0) -> None:
        """One more line, or several, each indented by ``indent`` spaces."""
        for each in text.splitlines():
            self.lines.append((" " * indent + each if each.strip() else each, line))

    def extend(self, other: Script, indent: int = 0) -> None:
        """Another script's lines, indented, and everything it records."""
        for text, line in other.lines:
            self.lines.append((" " * indent + text if text.strip() else text, line))
        self.holes.extend(other.holes)
        self.restated.update(other.restated)
        for item in other.rests_on:
            if item not in self.rests_on:
                self.rests_on.append(item)
        self.outline.extend(other.outline)

    def text(self, indent: int = 0, marks: bool = False) -> str:
        """The lines as Lean source, each ``-- file:line`` marked where ``marks`` is set."""
        out = []
        for text, line in self.lines:
            body = " " * indent + text if text.strip() else text
            if marks and line is not None:
                body = f"{body}  -- line {line}"
            out.append(body)
        return "\n".join(out)

    def sorry_lines(self, first: int) -> list[int]:
        """The lines of the command the holes' ``sorry`` are on, the script's first at ``first``.

        What :func:`lanky.oracles.lean.holes_verdict` takes as ``holes``: the
        lines counted from ``1`` in the command the script is placed in.
        """
        holes = set(self.holes)
        return [
            first + index
            for index, (text, line) in enumerate(self.lines)
            if text.strip() == "sorry" and line in holes
        ]

    def python_line(self, lean_line: int, first: int) -> int | None:
        """The Python line a line of the command came from, the script's first at ``first``."""
        index = lean_line - first
        while 0 <= index < len(self.lines):
            line = self.lines[index][1]
            if line is not None:
                return line
            index -= 1
        return None

    def cite(self, citation: Citation) -> None:
        """Record what a cited theorem asks of the declaration: its text, its premises', its id.

        A theorem cited is a hypothesis of the declaration, by its cited text
        (:mod:`lanky.citations`), and so is each theorem its own ``as_cited``
        takes, all the way down; the claim rests on each of them.
        """
        if citation.kind != "theorem":
            return
        self.restated[citation.head] = citation
        if citation.fact_id and citation.fact_id not in self.rests_on:
            self.rests_on.append(citation.fact_id)
        for premise in citation.premises:
            self.cite(premise)


# {{{ the facts a step cites


def resolve(
    reasons: Sequence[Any],
    terms: Sequence[Any],
    scope: StepScope,
    line: int | None = None,
) -> list[Citation]:
    """Each reason as a citation at its point: as written, or matched against ``terms``.

    ``terms`` are what the step is about: a link's two sides, or a case's
    claim. A fact left uncalled is at the one point that lines it up with
    them (:func:`lanky.matching.single_point`).

    Raises:
        StepError: If a reason is no fact, or no single point of an uncalled
            fact fits, with the fix: write the point.
    """
    out: list[Citation] = []
    for reason in reasons:
        try:
            citation = citation_of(reason, mathlib=scope.mathlib)
        except (TypeError, ValueError, UnsupportedTerm) as exc:
            raise StepError(str(exc), line, scope.path) from None
        if citation.point is None:
            try:
                lemma = citation.lemma
            except TypeError as exc:
                raise StepError(str(exc), line, scope.path) from None
            try:
                point = single_point(lemma, terms, scope.types, scope.facts, citation.name)
            except NoSinglePoint as exc:
                arguments = ", ".join(var.name for var, _ in lemma.binders)
                raise StepError(
                    str(exc), line, scope.path, fix=f"by={citation.name}({arguments})"
                ) from None
            citation = citation.at(point)
        elif len(citation.point) != len(citation.binders):
            raise StepError(
                f"{citation.name} is cited at {len(citation.point)} values, and it takes "
                f"{len(citation.binders)}",
                line,
                scope.path,
            )
        out.append(citation)
    return out


def _application(citation: Citation, scope: StepScope) -> str:
    """The Lean that applies a cited fact at its point, each condition discharged."""
    lemma = citation.lemma
    values = dict(zip((var.name for var, _ in lemma.binders), citation.point or (), strict=True))
    parts = [citation.head]
    for kind, item in lemma.premises:
        if kind == "value":
            parts.append(scope.render(values[item], atomic=True))
        else:
            parts.append(_discharger(instantiate(item, values), scope))
    return " ".join(parts)


def _discharger(condition: Any, scope: StepScope) -> str:
    """What shows a condition of a cited fact: ``(by omega)`` for integer arithmetic."""
    if _integer_arithmetic(condition, scope):
        return "(by omega)"
    return _MATHLIB_CONDITION if scope.mathlib else _CORE_CONDITION


def _integer_arithmetic(condition: Any, scope: StepScope) -> bool:
    """Whether a condition compares integers, which ``omega`` decides."""
    if not isinstance(condition, prim.Comparison):
        return False
    try:
        return all(
            number_type(side, scope.types, mathlib=scope.mathlib) not in ("ℝ", "ℂ")
            for side in (condition.left, condition.right)
        ) and not _applies_a_family(condition, scope)
    except Exception:  # noqa: BLE001 - a condition the printer cannot read is the closers'
        return False


def _applies_a_family(term: Any, scope: StepScope) -> bool:
    """Whether a term applies a family of the scope, which ``omega`` reads as an atom."""
    stack = [term]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Call | prim.Subscript):
            return True
        if isinstance(node, prim.ExpressionNode):
            stack.extend(init_args(node))
        elif isinstance(node, tuple):
            stack.extend(node)
    return False


# }}}


# {{{ what the compiler adds


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


def nonzero_lines(terms: Iterable[Any], scope: StepScope) -> list[str]:
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
    ring = scope.ring(*terms) if terms else "ℝ"
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


def shift_lines(goal: Any, facts: Sequence[Any], scope: StepScope) -> list[str]:
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
    from lanky.matching import _affine

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


# }}}


# {{{ a step


def step_script(
    goal: Any,
    reasons: Sequence[Any],
    scope: StepScope,
    line: int | None = None,
    *,
    hole: bool = False,
) -> Script:
    """The Lean that proves ``goal`` (a comparison) from ``reasons``, at Python line ``line``.

    The cited facts go into the context at their points, then the facts the
    compiler adds, then one closing tactic: the first of the attempts the
    module docstring lists that closes the goal, under the step's heartbeat
    budget. ``hole`` is a step written ``by=...``: ``sorry``.

    Raises:
        StepError: As :func:`resolve` does.
    """
    script = Script()
    if hole:
        script.add("sorry", line)
        script.holes.append(line)
        return script
    terms = [goal.left, goal.right] if isinstance(goal, prim.Comparison) else [goal]
    citations = resolve(reasons, terms, scope, line)
    names: list[str] = []
    instances: list[Any] = []
    for citation in citations:
        script.cite(citation)
        instances.append(citation.instance)
        if citation.kind == "named" and not citation.binders:
            # a fact on the way is in the context already, under its name
            names.append(citation.head)
            continue
        name = scope.fresh(_stem(citation))
        names.append(name)
        script.add(f"have {name} := {_application(citation, scope)}", line)
        if scope.mathlib:
            script.add(f"try push_cast at {name}", line)
    multipliers = _certificate(goal, citations, instances, names, scope)
    added = nonzero_lines([goal, *instances, *(multipliers or ())], scope)
    for each in added:
        script.add(each, None)
    for each in shift_lines(goal, instances, scope):
        script.add(each, None)
    attempts = _attempts(goal, names, multipliers, scope)
    script.add(_first(attempts, scope), line)
    return script


def _stem(citation: Citation) -> str:
    """The stem of the name a cited fact is put in the context under."""
    if citation.kind == "claim":
        return "ih"
    if citation.kind == "named":
        return f"{citation.head}_"
    return "h"


def _certificate(
    goal: Any,
    citations: Sequence[Citation],
    instances: Sequence[Any],
    names: Sequence[str],
    scope: StepScope,
) -> list[Any] | None:
    """The multipliers of the facts whose combination is the goal, or ``None``.

    lanky's search (:func:`lanky.induction.find_certificate`) on a case whose
    lemmas are exactly the facts cited, each at its point. Only an equation
    from equations; sympy is the search's, and without it there is none.
    """
    if not (isinstance(goal, prim.Comparison) and goal.operator == "=="):
        return None
    lemmas = []
    for name, instance in zip(names, instances, strict=True):
        if not (isinstance(instance, prim.Comparison) and instance.operator == "=="):
            continue
        lemmas.append(Lemma(name, (), (), instance))
    if not lemmas:
        return None
    families = frozenset(
        name for name, sort in scope.types.items() if isinstance(_base(sort), FnType)
    )
    bounds = {}
    for name, sort in scope.types.items():
        base = _base(sort)
        if isinstance(base, FinType):
            bounds[name] = (0, base.bound - 1)
        elif isinstance(base, Sort) and base.name == "Nat":
            bounds[name] = (0, None)
    case = Case(
        name="step",
        goal=goal,
        lemmas=tuple(lemmas),
        variables=dict(scope.types),
        bounds=bounds,
        families=families,
        facts=tuple(scope.facts),
    )
    try:
        uses = find_certificate(case)
    except Exception:  # noqa: BLE001 - a search that fails finds nothing, and Lean is asked anyway
        return None
    if not uses:
        return None
    multipliers: dict[str, Any] = {use.lemma: use.multiplier for use in uses}
    return [multipliers.get(name, 0) for name in names]


def _base(sort: Any) -> Any:
    """A sort with its refinements taken off."""
    while isinstance(sort, Refined):
        sort = sort.base
    return sort


def _combination(
    names: Sequence[str], multipliers: Sequence[Any], ring: str, scope: StepScope
) -> str | None:
    """``c₁ * h₁ + c₂ * h₂``, as ``linear_combination`` takes it; ``None`` for all zero."""
    parts: list[str] = []
    for name, multiplier in zip(names, multipliers, strict=True):
        if _number(multiplier, 0):
            continue
        if _number(multiplier, 1):
            term = name
        elif _number(multiplier, -1):
            parts.append(f"- {name}" if parts else f"-{name}")
            continue
        else:
            try:
                factor = scope.render(multiplier)
            except UnsupportedTerm:
                return None
            term = f"({factor} : {ring}) * {name}"
        parts.append(f"+ {term}" if parts else term)
    return " ".join(parts) if parts else None


def _number(value: Any, number: int) -> bool:
    """Whether a multiplier is the plain number ``number``."""
    return not isinstance(value, bool | prim.ExpressionNode) and value == number


def _attempts(
    goal: Any, names: Sequence[str], multipliers: Sequence[Any] | None, scope: StepScope
) -> list[str]:
    """The attempts that close the goal, in order; each closes it or fails."""
    attempts: list[str] = []
    relation = goal.operator if isinstance(goal, prim.Comparison) else None
    if len(names) == 1:
        attempts.append(f"exact {names[0]}")
        if relation == "==":
            attempts.append(f"exact {names[0]}.symm")
    if not scope.mathlib:
        attempts.append("((try simp only [Int.sub_add_cancel] at *) <;> omega)")
        attempts.append("omega")
        attempts.append("grind")
        return attempts
    norm = f"(norm := {COMBINATION_NORM})"
    if relation == "==":
        ring = scope.ring(goal.left, goal.right)
        if multipliers is not None:
            combination = _combination(names, multipliers, ring, scope)
            if combination is not None:
                attempts.append(f"linear_combination {norm} {combination}")
        if not names:
            attempts.append(f"linear_combination {norm}")
        elif multipliers is None and len(names) <= 3:
            # no search: the facts as they stand, each with either sign
            for signs in _signs(len(names)):
                terms = " ".join(
                    (f"+ {name}" if sign > 0 else f"- {name}")
                    if index
                    else (name if sign > 0 else f"-{name}")
                    for index, (name, sign) in enumerate(zip(names, signs, strict=True))
                )
                attempts.append(f"linear_combination {norm} {terms}")
    facts = f" [{', '.join(names)}]" if names else ""
    if relation in ("==", "<=", "<", ">=", ">") and scope.ring(goal.left, goal.right) != "ℂ":
        attempts.append(f"linarith{facts}")
        attempts.append(f"nlinarith{facts}")
    if relation in ("<=", "<", ">=", ">", "!="):
        attempts.append("positivity")
    if not names and relation == "==":
        attempts.append("ring1")
        attempts.append("(field_simp; ring1)")
    return attempts


def _signs(count: int) -> list[tuple[int, ...]]:
    """Every choice of a sign for each of ``count`` facts, all positive first."""
    out: list[tuple[int, ...]] = [()]
    for _ in range(count):
        out = [(*signs, sign) for signs in out for sign in (1, -1)]
    return out


def _first(attempts: Sequence[str], scope: StepScope) -> str:
    """The attempts as one tactic, under the step's heartbeat budget."""
    if len(attempts) == 1:
        body = attempts[0]
    else:
        body = "first\n" + "\n".join(f"  | {attempt}" for attempt in attempts)
    if scope.heartbeats:
        return f"set_option maxHeartbeats {scope.heartbeats} in\n{body}"
    return body


def hole_script(line: int | None) -> Script:
    """A step left open, ``by=...``: ``sorry``, its line recorded."""
    script = Script()
    script.add("sorry", line)
    script.holes.append(line)
    return script


# }}}


# {{{ chains


def _relation_text(relation: str) -> str:
    """A relation as Lean writes it."""
    return _LEAN_RELATION[relation]


def _link_script(left: Any, link: Link, scope: StepScope) -> Script:
    """The tactic block that proves one link: ``left relation link.term``."""
    goal = Comparison(left, link.relation, link.term)
    if link.hole:
        return hole_script(link.line)
    return step_script(goal, link.reasons, scope, link.line)


def _calc(chain: Chain, scope: StepScope) -> Script:
    """The chain as a ``calc``, a link to a step.

    Laid out as the check's prototypes were, which Lean takes: the first term
    after ``calc``, the first relation on the next line, the later links each
    starting ``_``, every link's tactic block indented under it.
    """
    script = Script()
    script.add(f"calc {scope.render(chain.start)}", chain.line)
    for index, (left, link) in enumerate(chain.steps()):
        relation = _relation_text(link.relation)
        term = scope.render(link.term)
        head = f"    {relation} {term} := by" if index == 0 else f"  _ {relation} {term} := by"
        script.add(head, link.line)
        script.extend(_link_script(left, link, scope), indent=6)
        script.outline.append(
            (
                link.line,
                render(left) if index == 0 else "",
                link.relation,
                render(link.term),
                _reason_text(link, scope, left),
            )
        )
    return script


def _reason_text(link: Link, scope: StepScope, left: Any) -> str:
    """The reason of a link as the outline says it: ``by recurrence, at (a - 2, b)``."""
    if link.hole:
        return "left open (by=...)"
    if not link.reasons:
        return "by algebra"
    try:
        citations = resolve(link.reasons, [left, link.term], scope, link.line)
    except StepError:
        return "by " + ", ".join(_reason_name(reason) for reason in link.reasons)
    return "by " + " and ".join(citation.described() for citation in citations)


def _reason_name(reason: Any) -> str:
    """What a reason is called, where its citation could not be read."""
    try:
        return citation_of(reason).name
    except Exception:  # noqa: BLE001 - a reason that is no fact is named as Python shows it
        return repr(reason)


def chain_script(chain: Chain, scope: StepScope, claim: Any = None) -> Script:
    """The Lean that proves the case's ``claim`` by ``chain``; or the chain alone, as a ``calc``.

    Where the chain's ends print as the claim's two sides, with the claim's
    relation, the ``calc`` is the proof. Otherwise the chain is a fact of the
    case, ``have chain := calc ...``, and the claim is closed from it: as
    it stands, turned round, or by ``linear_combination`` up to the printing
    of the sides (``-x`` against ``(-1) * x``), and ``linarith`` for an
    inequality.

    Raises:
        StepError: As :func:`resolve` does, and where the chain is not about
            the claim at all: its ends are not the claim's sides, as far as
            sympy can tell.
    """
    calc = _calc(chain, scope)
    if claim is None or _ends_print_as(chain, claim, scope):
        return calc
    _refuse_another_claim(chain, claim, scope)
    name = scope.fresh("chain")
    script = Script()
    first, *rest = calc.lines
    script.lines.append((f"have {name} := {first[0]}", first[1]))
    script.lines.extend(rest)
    script.holes.extend(calc.holes)
    script.restated.update(calc.restated)
    script.rests_on.extend(item for item in calc.rests_on if item not in script.rests_on)
    script.outline.extend(calc.outline)
    attempts = [f"exact {name}"]
    if claim.operator == "==" and chain.relation == "==":
        attempts.append(f"exact {name}.symm")
        if scope.mathlib:
            norm = f"(norm := {COMBINATION_NORM})"
            ring = scope.ring(claim.left, claim.right)
            attempts.append(f"linear_combination {norm} {name}")
            attempts.append(f"linear_combination {norm} (-1 : {ring}) * {name}")
        else:
            attempts.append("((try simp only [Int.sub_add_cancel] at *) <;> omega)")
    elif scope.mathlib:
        attempts += [f"linarith [{name}]", f"nlinarith [{name}]"]
    else:
        attempts.append("omega")
    script.add(_first(attempts, scope), chain.links[-1].line)
    return script


def _ends_print_as(chain: Chain, claim: Any, scope: StepScope) -> bool:
    """Whether the chain's ends print as the claim's sides, with the claim's relation."""
    if not isinstance(claim, prim.Comparison) or claim.operator != chain.relation:
        return False
    try:
        return scope.render(chain.start) == scope.render(claim.left) and scope.render(
            chain.end
        ) == scope.render(claim.right)
    except UnsupportedTerm:
        return False


def _refuse_another_claim(chain: Chain, claim: Any, scope: StepScope) -> None:
    """Raise where a chain of equations ends at other terms than an equation's sides.

    As far as sympy tells: ``claim.left - claim.right`` has to be the chain's
    ``start - end`` or its negative. Without sympy, or for terms it cannot
    read, nothing is refused here, and Lean says it.
    """
    if not (claim.operator == "==" and chain.relation == "=="):
        return
    if same(chain.start, claim.left) and not same(chain.end, claim.right):
        _difference_or_raise(chain, claim, scope)
    elif same(chain.start, claim.right) and not same(chain.end, claim.left):
        _difference_or_raise(chain, claim, scope)


def _difference_or_raise(chain: Chain, claim: Any, scope: StepScope) -> None:
    """Raise unless sympy says the chain's ends and the claim's sides differ as one difference."""
    from lanky.induction import _Algebra, _sympy, _Unsupported

    sympy = _sympy()
    if sympy is None:
        return
    families = frozenset(
        name for name, sort in scope.types.items() if isinstance(_base(sort), FnType)
    )
    case = Case("chain", claim, (), dict(scope.types), {}, families)
    algebra = _Algebra(sympy, case)
    try:
        claimed = algebra.side(claim, {})
        shown = algebra.side(chain.claim, {})
    except _Unsupported:
        return
    if sympy.simplify(claimed - shown) == 0 or sympy.simplify(claimed + shown) == 0:
        return
    left_matches = same(chain.start, claim.left)
    raise StepError(
        f"the chain ends at {render(chain.end)}; the claim's "
        f"{'right' if left_matches else 'left'} side is "
        f"{render(claim.right if left_matches else claim.left)}",
        chain.links[-1].line,
        scope.path,
    )


def named_script(chain: Chain, scope: StepScope, name: str | None = None) -> Script:
    """A named step, ``recurrence = a[n].equals(...)``: ``have recurrence : ... := by ...``.

    The statement is the chain's start, its relation and its end; its proof
    the link's step, or the ``calc`` of a chain of several links. ``name`` is
    the Lean name, the chain's Python name by default.
    """
    lean_name = name or chain.name or scope.fresh("fact")
    scope.taken.add(lean_name)
    statement = (
        f"{scope.render(chain.start)} {_relation_text(chain.relation)} {scope.render(chain.end)}"
    )
    script = Script()
    script.add(f"have {lean_name} : {statement} := by", chain.line)
    if len(chain.links) == 1:
        left, link = next(chain.steps())
        body = _link_script(left, link, scope)
        script.extend(body, indent=2)
        script.outline.append(
            (
                link.line,
                f"{lean_name}: {render(left)}",
                link.relation,
                render(link.term),
                _reason_text(link, scope, left),
            )
        )
        return script
    script.extend(_calc(chain, scope), indent=2)
    return script


# }}}


# {{{ without Lean: each step drawn


@dataclass(frozen=True)
class LinkDraw:
    """What drawing one link's two sides found.

    Attributes:
        line: The link's Python line.
        statement: The link as a proposition, as the report prints it.
        outcome: ``"tested"``, ``"refuted"`` or ``"undrawn"``.
        detail: For a refuted link the point and why; for an undrawn one why
            no value could be drawn; for a tested one how many draws.
    """

    line: int | None
    statement: str
    outcome: str
    detail: str


def draw_links(
    chain: Chain,
    variables: Sequence[tuple[str, Any]],
    hypotheses: Sequence[Any] = (),
    conditions: Sequence[Any] = (),
    samples: int = 100,
    seed: int = 0,
) -> list[LinkDraw]:
    """Draw each link of ``chain`` at points, where Lean cannot check it.

    Each link is a proposition, its left term against its right, which holds
    wherever the theorem's hypotheses and the case's conditions do, if the
    proof is right. It is drawn as a claim is (:func:`lanky.testing.check`),
    over ``variables``, the theorem's and the claim's ``(name, sort)`` pairs,
    under ``hypotheses`` and ``conditions``. A link false at a draw is
    ``refuted`` there, which catches a wrong step at its own line with no
    Lean at all. A link over a family that cannot be drawn, a table over
    ``Nat``, is ``undrawn``, and says why. A link left open, ``by=...``, is
    drawn too: it is a claim, if one nobody has proved.
    """
    from lanky.testing import OpenStatement, check

    out: list[LinkDraw] = []
    for left, link in chain.steps():
        prop = Comparison(left, link.relation, link.term)
        statement = render(prop)
        try:
            report = check(variables, [*hypotheses, *conditions], prop, samples, seed)
        except OpenStatement as exc:
            out.append(LinkDraw(link.line, statement, "undrawn", str(exc)))
            continue
        if report.counterexample is not None:
            point = ", ".join(f"{key}={value}" for key, value in report.counterexample.items())
            reason = f": {report.reason}" if report.reason else ""
            out.append(LinkDraw(link.line, statement, "refuted", f"at {point}{reason}"))
        elif report.valid == 0:
            out.append(LinkDraw(link.line, statement, "undrawn", report.reason))
        else:
            out.append(LinkDraw(link.line, statement, "tested", f"{report.valid} draws"))
    return out


def drawn_status(name: str, draws: Sequence[LinkDraw], path: str | None = None) -> tuple[str, str]:
    """What the draws of a proof's links say of it, without Lean: ``(outcome, message)``.

    ``"refuted"`` where a link failed at a draw, naming the first such link,
    its line and the point; ``"undrawn"`` where any link could not be drawn,
    which leaves the claim as the tester leaves it (``assumed`` for a family
    over ``Nat``), naming why; ``"tested"`` where every link held at its
    draws: the proof was tested step by step, and Lean did not check it.
    """
    base = os.path.basename(path) if path else ""

    def where(draw: LinkDraw) -> str:
        return f"{base}:{draw.line}" if base and draw.line is not None else f"line {draw.line}"

    for draw in draws:
        if draw.outcome == "refuted":
            return "refuted", (
                f"the step at {where(draw)}, {draw.statement}, is false {draw.detail}"
            )
    for draw in draws:
        if draw.outcome == "undrawn":
            return "undrawn", f"{name} reads assumed: {draw.detail}"
    return "tested", (
        f"the proof of {name} was tested step by step at drawn points, not checked by Lean"
    )


# }}}


# {{{ the outline


def outline_text(
    rows: Sequence[tuple[int | None, str, str, str, str]], path: str | None = None, indent: str = ""
) -> list[str]:
    """Rows of a proof's outline as ``lanky check --steps`` prints them, columns aligned.

    ``l2p.py:148  R[a, b] == -R[a - 2, b + 2]  by recurrence, at (a - 2, b)``,
    then each later link of the chain under the first, its relation under the
    first's.
    """
    if not rows:
        return []
    base = os.path.basename(path) if path else ""
    wheres = [
        f"{base}:{line}" if base and line is not None else ("" if line is None else str(line))
        for line, *_ in rows
    ]
    width_where = max(len(where) for where in wheres)
    width_left = max(len(left) for _, left, _, _, _ in rows)
    width_term = max(len(term) + len(relation) + 1 for _, _, relation, term, _ in rows)
    out = []
    for where, (_, left, relation, term, reason) in zip(wheres, rows, strict=True):
        statement = f"{relation} {term}"
        out.append(
            f"{where:<{width_where}}  {indent}{left:>{width_left}} "
            f"{statement:<{width_term}}  {reason}".rstrip()
        )
    return out


# }}}
