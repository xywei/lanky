"""What the check of a written proof says: Lean's answer, read back to the Python lines.

The design idea. Lean's failure only triggers a report; the report itself is
computed in Python, in lanky's notation, at the line the user wrote, with a
fix where one can be named. Lean's own words appear only under
``--show-lean``. Each message Lean gives is placed by its position in the
command (:meth:`lanky.proofs.compile.Command.origin_at`), and the kind of
piece it is about says which report it is:

- a step that does not follow: the case, what each cited fact says there, and
  what is left over once the facts are combined as best they can be
  (:func:`left_over`), with a fact cited at another point that makes the step
  follow, when there is one (:func:`fix_for`);
- a condition that is not met: ``stored needs a < 2, and this case has a >=
  2``;
- a call of the claim at a negative argument: ``claim(a - 2, b + 2) is at a
  negative a when a = 1: split off a < 2 first``;
- and what lanky refuses before Lean is asked (:class:`lanky.proofs.trace.ProofError`):
  a claim that is not called at smaller values, a theorem that calls itself,
  a fact cited by name that no single point fits.

The axiom audit is read positively (:func:`audit`): exactly one answer, naming
exactly the theorem, with no axiom outside Lean's own three.
"""

from __future__ import annotations

import os
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

from lanky.audit import TRUSTED_AXIOMS, audit_failure
from lanky.proofs.match import (
    Shape,
    affine,
    applications,
    from_affine,
    shape_of,
    unify,
)
from lanky.proofs.trace import Citation, ClaimDef, Given, Leaf, Proof, ProofError, shown
from lanky.terms import Forall, Var, init_args, render

__all__ = [
    "CLOSED_WITH_HOLES",
    "Failure",
    "audit",
    "case_text",
    "combination",
    "failure_of",
    "fix_for",
    "left_over",
    "read",
    "tidy",
    "verdict",
]


@dataclass(frozen=True)
class Failure:
    """One thing wrong with a written proof, as the report says it.

    Attributes:
        kind: What went wrong, one word (see :class:`lanky.proofs.trace.ProofError`;
            ``step``, ``condition``, ``negative``, ``time``, ``lean`` besides).
        line: The line of the body it is about, when there is one.
        headline: The report's first line, without the claim's name.
        lines: What follows, in lanky's notation.
        fix: What to write instead, when there is a fix to name.
    """

    kind: str
    line: int | None
    headline: str
    lines: tuple[str, ...] = ()
    fix: str | None = None

    def to_dict(self, path: str | None = None) -> dict[str, Any]:
        """The failure as the ledger keeps it, with the line's source when ``path`` is given."""
        out: dict[str, Any] = {
            "kind": self.kind,
            "line": self.line,
            "headline": self.headline,
            "lines": list(self.lines),
            "fix": self.fix,
        }
        if path and self.line:
            import linecache

            out["source"] = linecache.getline(path, self.line).strip()
            out["where"] = f"{os.path.basename(path)}:{self.line}"
        return out


def failure_of(error: ProofError) -> Failure:
    """The report of a proof lanky refused before Lean was asked."""
    headlines = {
        "self-reference": "the theorem calls itself",
        "no-point": "a fact cited by its name fits no single point",
        "measure": "the claim is not called at smaller values",
        "claim": "the claim is not defined as lanky reads it",
        "return": "a return gives something that is no fact",
        "question": "the proof asks a question lanky does not split on",
        "raised": "the proof raised",
        "paths": "the proof does not run the same way on every path",
        "cite": "a fact is cited at the wrong number of values",
        "unsupported": "Lean cannot state part of the proof",
    }
    return Failure(
        error.kind,
        error.line,
        headlines.get(error.kind, "the proof is refused"),
        (error.message,),
        error.fix,
    )


# {{{ the algebra of a step


def _algebra(claim: Any, types: Mapping[str, Any]) -> Any:
    """lanky's induction algebra for one step's terms, or ``None`` without sympy."""
    from lanky.induction import Case, _Algebra, _sympy
    from lanky.prelude import FnType, Refined

    sympy = _sympy()
    if sympy is None:
        return None
    families = set()
    for name, sort in types.items():
        while isinstance(sort, Refined):
            sort = sort.base
        if isinstance(sort, FnType):
            families.add(name)
    case = Case("step", claim, (), dict(types), {}, frozenset(families))
    return _Algebra(sympy, case)


def combination(claim: Any, bodies: Sequence[Any], types: Mapping[str, Any]) -> list[Any] | None:
    """Multipliers whose combination of ``bodies`` is ``claim``, all equations; ``None`` for none.

    lanky's certificate search (:func:`lanky.induction._solve`), limited to
    the instances the step cites. The multipliers are terms over the case's
    names, which ``linear_combination`` is handed; Lean checks them.
    """
    from lanky.induction import _Instance, _solve, _Unsupported

    algebra = _algebra(claim, types)
    if algebra is None:
        return None
    try:
        goal = algebra.side(claim, {})
        instances = []
        for body in bodies:
            side = algebra.side(body, {})
            instances.append(_Instance(None, (), side, algebra.applications(side)))  # type: ignore[arg-type]
        multipliers = _solve(algebra.sympy, goal, instances)
    except (_Unsupported, Exception):  # noqa: BLE001 - what the search cannot read has none
        return None
    if multipliers is None:
        return None
    return [algebra.back(multiplier) for multiplier in multipliers]


def left_over(claim: Any, bodies: Sequence[Any], types: Mapping[str, Any]) -> Any | None:
    """What is left of the claim once the facts are taken away as best they pair: a term ``== 0``.

    Each fact is taken with the multiplier that cancels a term it shares with
    what is left, and a fact that shares none, with the multiplier that pairs
    its term with one of the same family: the step's left side minus its
    right side, minus each fact times that multiplier. ``None`` without
    sympy, or for a term the algebra cannot read.
    """
    from lanky.induction import _Unsupported

    algebra = _algebra(claim, types)
    if algebra is None:
        return None
    sympy = algebra.sympy
    try:
        remainder = sympy.expand(algebra.side(claim, {}))
        sides = [sympy.expand(algebra.side(body, {})) for body in bodies]
    except (_Unsupported, Exception):  # noqa: BLE001 - what the algebra cannot read is left as is
        return None
    used = [False] * len(sides)

    def take(index: int, mine: Any, theirs: Any) -> None:
        nonlocal remainder
        own = sides[index].coeff(mine)
        if own == 0:
            return
        multiplier = remainder.coeff(theirs) / own
        remainder = sympy.expand(remainder - multiplier * sides[index])
        used[index] = True

    for _ in range(len(sides)):
        for index, side in enumerate(sides):
            if used[index]:
                continue
            shared = sorted(algebra.applications(side) & algebra.applications(remainder), key=str)
            if shared:
                take(index, shared[0], shared[0])
    for index, side in enumerate(sides):
        if used[index]:
            continue
        for mine in sorted(algebra.applications(side), key=str):
            theirs = [
                atom
                for atom in sorted(algebra.applications(remainder), key=str)
                if atom.func == mine.func
            ]
            if theirs:
                take(index, mine, theirs[0])
                break
    if remainder == 0:
        return 0
    return back(algebra, remainder)


def back(algebra: Any, expr: Any) -> Any:
    """A sympy expression of the step's algebra as a lanky term, a family's application included.

    :meth:`lanky.induction._Algebra.back` reads an expression with no
    application in it, a multiplier; what is left over of a step has them,
    ``D(a - 2, b + 3)``, each of which is read back as the family at its
    arguments, ``D[a - 2, b + 3]``.
    """
    from lanky.cas import from_sympy

    sympy = algebra.sympy
    atoms = sorted(algebra.applications(expr), key=str)
    variables: dict[str, Any] = {name: Var(name) for name in algebra.case.variables}
    marks = {}
    for index, atom in enumerate(atoms):
        mark = sympy.Symbol(f"lanky_application_{index}")
        marks[atom] = mark
        arguments = tuple(_tidy_argument(from_sympy(argument, variables)) for argument in atom.args)
        family = Var(str(atom.func))
        variables[mark.name] = family[arguments if len(arguments) > 1 else arguments[0]]
    return from_sympy(expr.xreplace(marks), variables)


def tidy(term: Any) -> Any:
    """``term`` with every family's argument written as its affine form: ``a`` for ``a - 2 + 2``."""
    from lanky.terms import Exists, Sum

    if isinstance(term, prim.Subscript):
        index = term.index if isinstance(term.index, tuple) else (term.index,)
        index = tuple(_tidy_argument(item) for item in index)
        return type(term)(tidy(term.aggregate), index if len(index) > 1 else index[0])
    if isinstance(term, prim.Call):
        return type(term)(
            tidy(term.function), tuple(_tidy_argument(item) for item in term.parameters)
        )
    if isinstance(term, Forall | Exists | Sum):
        return term
    if isinstance(term, prim.ExpressionNode):
        return type(term)(
            *(
                tidy(child) if not isinstance(child, tuple) else tuple(tidy(item) for item in child)
                for child in init_args(term)
            )
        )
    return term


def tidy_prop(prop: Any) -> Any:
    """A proposition with each side of a comparison written as its affine form, and tidied."""
    from lanky.terms import Comparison

    if isinstance(prop, prim.Comparison):
        sides = []
        for side in (prop.left, prop.right):
            form = affine(side)
            sides.append(tidy(side) if form is None else from_affine(form))
        return Comparison(sides[0], prop.operator, sides[1])
    return tidy(prop)


def _tidy_argument(argument: Any) -> Any:
    """An argument as its affine form, where it has one."""
    form = affine(argument)
    return tidy(argument) if form is None else from_affine(form)


# }}}


# {{{ the cases and what the facts say


def case_text(conditions: Sequence[tuple[Any, int]], path: str) -> str:
    """``When a + b != 0 and a >= 2 (every_box.py:48, 50)``; empty for no condition."""
    if not conditions:
        return ""
    said = " and ".join(render(condition) for condition, _ in conditions)
    lines = ", ".join(dict.fromkeys(str(line) for _, line in conditions if line))
    where = f" ({os.path.basename(path)}:{lines})" if lines else ""
    return f"When {said}{where}"


def _label(citation: Citation, values: Sequence[Any]) -> str:
    """How a fact at its point is named: ``pde(i, a - 2, b)``, or ``stored, at (i, a, b)``."""
    if citation.values is not None:
        return citation.text()
    if not values:
        return citation.name
    return f"{citation.name}, at ({', '.join(shown(value) for value in values)})"


def _shapes(source: Any, proof: Proof) -> list[Shape]:
    """The shape of each part of a cited fact, for finding it at another point."""
    if isinstance(source, ClaimDef):
        goal = proof.theorem.goal
        body = goal.body if isinstance(goal, Forall) else goal
        binders = tuple(
            (Var(name), domain) for name, domain in zip(source.params, source.domains, strict=True)
        )
        return [Shape(binders, tuple(("value", name) for name in source.params), body)]
    if isinstance(source, Given):
        return [shape_of(part) for part in source.parts]
    return [shape_of(source.term)]


def fix_for(step: Any, proof: Proof, measure: Any = None) -> tuple[int, Citation] | None:
    """A fact of the step cited at another point that makes the step follow, as Python finds it.

    Each fact cited at a point is put, in turn, at every point at which one
    of its terms is a term of the claim or of another fact of the step, and
    the step is tried again with the multiplier search
    (:func:`combination`): the first that works is the fix, as the index of
    the fact among the step's and the citation at the new point. Lean is
    asked to confirm it before the report calls it checked. The claim is put
    only at points closer to a base case, by ``measure``
    (:class:`lanky.proofs.compile.Measure`): never at its own point, which
    would make the step a circle.
    """
    instances = list(step.instances)
    claim = step.claim
    for index, instance in enumerate(instances):
        citation = instance.citation
        if citation.values is None:
            continue
        shapes = _shapes(citation.source, proof)
        if instance.part >= len(shapes):
            continue
        shape = shapes[instance.part]
        unknowns = [var.name for var, _ in shape.binders]
        others = [other.body for position, other in enumerate(instances) if position != index]
        targets: list[Any] = []
        for term in (*others, claim):
            for atom in applications(term):
                if all(render(atom) != render(seen) for seen in targets):
                    targets.append(atom)
        tried: set[tuple[str, ...]] = {tuple(render(value) for value in citation.values)}
        for pattern in applications(shape.body):
            for atom in targets:
                solution = unify(pattern, atom, unknowns, list(step.types))
                if solution is None or set(solution) != set(unknowns):
                    continue
                values = tuple(solution[name] for name in unknowns)
                key = tuple(render(value) for value in values)
                if key in tried:
                    continue
                if citation.is_claim and not _smaller(citation.source, values, measure):
                    continue
                tried.add(key)
                body, _guards = shape.at(solution)
                if combination(claim, [*others, body], step.types) is not None:
                    return index, Citation(citation.source, values, citation.line)
    return None


def _smaller(claim: ClaimDef, values: Sequence[Any], measure: Any) -> bool:
    """Whether the claim at ``values`` is closer to a base case than at its own variables."""
    from lanky.proofs.compile import _change

    at = dict(zip(claim.params, values, strict=True))
    if measure is None:
        changes = [_change(value, name) for name, value in at.items()]
        return any(change is not None and change <= -1 for change in changes)
    first = _change(at[measure.names[0]], measure.names[0])
    if measure.kind == "down":
        return first is not None and first <= -1
    if measure.kind == "up":
        return first is not None and first >= 1
    second = _change(at[measure.names[1]], measure.names[1])
    return (first is not None and first <= -1) or (
        first == 0 and second is not None and second <= -1
    )


# }}}


# {{{ reading Lean's answer


#: The axioms a proof may rest on: Lean's own three (:data:`lanky.audit.TRUSTED_AXIOMS`).
ALLOWED_AXIOMS = TRUSTED_AXIOMS

#: What a proof's verdict is when every ``sorry`` Lean found is at a step the
#: proof left open, ``by=...``, and nothing else is wrong: the claim reads
#: assumed there, and the ledger names the lines.
CLOSED_WITH_HOLES = "closed with holes"


def audit(
    messages: Sequence[Mapping[str, Any]], declared: str | Sequence[str], holes: bool = False
) -> str | None:
    """Why the axiom audit of ``declared`` is not positive; ``None`` when it is.

    The command ends with ``#print axioms _root_.<name>`` for each theorem it
    declares, and the answers are read as every command's are
    (:func:`lanky.audit.audit_failure`): exactly one answer naming exactly
    the theorem, its axioms among Lean's own three. A missing answer is a
    failure: a command that stopped Lean before the audit says nothing, and
    a theorem of the same name in another namespace is named otherwise.
    ``holes`` allows ``sorryAx`` too, for a proof whose steps left open are
    its only ``sorry``.
    """
    names = (declared,) if isinstance(declared, str) else tuple(declared)
    allowed = TRUSTED_AXIOMS | {"sorryAx"} if holes else TRUSTED_AXIOMS
    return audit_failure([str(message.get("data", "")) for message in messages], names, allowed)


def verdict(proof: Proof, command: Any, record: Mapping[str, Any]) -> tuple[str, list[Failure]]:
    """Lean's answer to a written proof: ``closed``, ``closed with holes`` or ``failed``.

    Closed is no error, no ``sorry`` and a positive audit. Closed with holes
    is the same, except that Lean found a ``sorry`` at each step the proof
    left open, ``by=...``, and nowhere else (:data:`CLOSED_WITH_HOLES`). A
    ``sorry`` anywhere else fails the proof, as an error does.
    """
    messages = list(record.get("messages") or ())
    errors = [message for message in messages if message.get("severity") == "error"]
    sorries = list(record.get("sorries") or ())
    allowed = set(getattr(command, "hole_lines", ()) or ())
    stray = [item for item in sorries if item.get("line") not in allowed]
    names = getattr(command, "audited", ()) or (command.declared,)
    if not errors and not sorries and audit(messages, names) is None:
        return "closed", []
    if not errors and sorries and not stray and audit(messages, names, holes=True) is None:
        return CLOSED_WITH_HOLES, []
    closed, failures = read(proof, command, record)
    return ("closed" if closed else "failed"), failures


def read(proof: Proof, command: Any, record: Mapping[str, Any]) -> tuple[bool, list[Failure]]:
    """Whether Lean accepted the command, and what is wrong where it did not.

    Accepted means no error, no ``sorry``, and a positive audit (:func:`audit`).
    Every error is read back to the piece of the proof it is about, one
    report per line of the body and kind, in the order of the lines. A
    failure of the measure is reported alone, as it was written.
    """
    messages = list(record.get("messages") or ())
    errors = [message for message in messages if message.get("severity") == "error"]
    sorries = list(record.get("sorries") or ())
    problem = audit(messages, getattr(command, "audited", ()) or (command.declared,))
    if not errors and not sorries and problem is None:
        return True, []
    failures: list[Failure] = []
    seen: set[tuple[Any, str]] = set()
    for error in errors:
        origin = command.origin_at(error.get("line"), error.get("column"))
        failure = _failure(proof, command, origin)
        key = (failure.line, failure.kind)
        if key in seen:
            continue
        seen.add(key)
        failures.append(failure)
    # a call at a negative argument is what makes the measure fail too, and
    # says how to fix it; otherwise a failing measure is reported alone
    negative = [failure for failure in failures if failure.kind == "negative"]
    if negative:
        return False, negative
    measured = [failure for failure in failures if failure.kind == "measure"]
    if measured:
        return False, measured[:1]
    if not failures:
        if sorries:
            failures.append(Failure("lean", None, "Lean accepted the proof with a sorry in it"))
        elif problem is not None:
            failures.append(Failure("lean", None, problem))
    failures.sort(key=lambda failure: (failure.line is None, failure.line or 0))
    return False, failures


def _failure(proof: Proof, command: Any, origin: Any) -> Failure:
    """The report of an error Lean gave at a piece of the proof (see the module)."""
    if origin is None:
        return Failure(
            "lean",
            None,
            "Lean did not accept the proof",
            ("--show-lean shows what Lean said",),
        )
    detail = origin.detail
    if origin.kind == "condition":
        return _condition(proof, origin)
    if origin.kind == "step":
        return _step(proof, command, detail["step"])
    if origin.kind == "routine":
        claim = detail.get("claim")
        case = case_text(detail.get("conditions") or (), proof.path)
        lead = f"{case}, the" if case else "The"
        return Failure(
            "routine",
            origin.line,
            "a case lanky was left to close does not follow",
            (f"{lead} case's claim is {render(claim)}, and lanky could not show it alone.",),
            "cite the facts it needs, as return f, g",
        )
    if origin.kind == "measure":
        claim = proof.claim
        params = ", ".join(claim.params) if claim else ""
        return Failure(
            "measure",
            origin.line,
            "the claim is not called at smaller values",
            (
                f"Lean could not show that each call of {claim.name if claim else 'claim'} is "
                f"at smaller values than ({params}).",
            ),
            "call the claim where one argument is smaller and stays a natural number",
        )
    if origin.kind in ("cite", "call"):
        citation = detail.get("citation")
        named = citation.text() if citation is not None else "a fact"
        return Failure(
            "lean",
            origin.line,
            f"Lean could not apply {named}",
            ("--show-lean shows what Lean said",),
        )
    if origin.kind == "chain-end":
        chain = detail.get("chain")
        claim = detail.get("claim")
        ends = f"{render(chain.start)} {chain.relation} {render(chain.end)}" if chain else "it"
        return Failure(
            "chain",
            origin.line,
            "the chain does not give the claim",
            (f"The chain shows {ends}; the claim of this case is {render(claim)}.",),
            "end the chain at the claim's other side",
        )
    if origin.kind in ("chain", "link", "named"):
        return Failure(
            "lean",
            origin.line,
            "Lean could not read a step of the chain",
            ("--show-lean shows what Lean said",),
        )
    if origin.kind in ("split", "pin"):
        return Failure(
            "lean",
            origin.line,
            f"Lean could not split the case on {render(detail.get('condition'))}",
            ("--show-lean shows what Lean said",),
        )
    return Failure(
        "lean", origin.line, "Lean did not accept the proof", ("--show-lean shows what Lean said",)
    )


def _condition(proof: Proof, origin: Any) -> Failure:
    """A condition of a fact at its point that the case does not show, or a negative argument."""
    detail = origin.detail
    citation: Citation = detail["citation"]
    condition = detail.get("condition")
    values = detail.get("values") or ()
    conditions = detail.get("conditions") or ()
    negative = detail.get("negative")
    if negative and citation.is_claim and citation.values is not None:
        claim = citation.source
        value = citation.values[list(claim.params).index(negative)]
        form = affine(value)
        drop = None
        if form is not None and set(form) <= {negative, None} and form.get(negative) == 1:
            drop = -form.get(None, 0)
        if drop is not None and drop > 0:
            at = int(drop) - 1
            return Failure(
                "negative",
                origin.line,
                "the claim is called at a negative argument",
                (
                    f"{citation.text()} is at a negative {negative} when {negative} = {at}: "
                    f"split off {negative} < {int(drop)} first.",
                ),
                f"split off {negative} < {int(drop)} first",
            )
        return Failure(
            "negative",
            origin.line,
            "the claim is called at a negative argument",
            (
                f"{citation.text()} may be at a negative {negative} in this case: split off "
                f"the cases where {render(value)} < 0 first.",
            ),
        )
    label = _label(citation, values)
    known = [*(detail.get("guards") or ()), *(fact for fact, _ in conditions)]
    has = " and ".join(render(tidy_prop(fact)) for fact in known) or "nothing that shows it"
    shown_condition = render(tidy_prop(condition)) if condition is not None else "a condition"
    return Failure(
        "condition",
        origin.line,
        "a condition of a cited fact is not met",
        (f"{label} needs {shown_condition}, and this case has {has}.",),
        f"cite {citation.name} in a case where {shown_condition}, or split that case off first",
    )


def _step(proof: Proof, command: Any, step: Any) -> Failure:
    """A step whose facts do not give the case's claim: what each says, and what is left over."""
    leaf: Leaf = step.leaf
    case = case_text(step.conditions, proof.path)
    lines = []
    lead = f"{case}, the step needs" if case else "The step needs"
    lines.append(f"{lead}   {render(tidy(step.claim))}")
    labels = [_label(instance.citation, instance.values) for instance in step.instances]
    width = max((len(label) for label in labels), default=0)
    for label, instance in zip(labels, step.instances, strict=True):
        lines.append(f"  {label.ljust(width)} says   {render(tidy(instance.body))}")
    remainder = left_over(step.claim, [instance.body for instance in step.instances], step.types)
    if remainder is not None and not _is_zero(remainder):
        lines.append("Left over:")
        lines.append(f"    {render(tidy(remainder))} == 0")
    fix = None
    found = fix_for(step, proof, command.measure)
    if found is not None:
        _index, citation = found
        fix = f"{citation.text()} makes the step follow"
    del leaf
    return Failure("step", step.where, "a step of its proof does not follow", tuple(lines), fix)


# }}}


def _is_zero(term: Any) -> bool:
    """Whether a term is the number zero; a term compared with ``0`` would build a proposition."""
    return isinstance(term, int | float) and not isinstance(term, bool) and term == 0
