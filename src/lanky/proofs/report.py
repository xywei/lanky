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
- the conclusion cited at a negative argument: ``ct.conclusion[a - 2, b + 2]
  is at a negative a when a = 1: split off a < 2 first``;
- and what lanky refuses before Lean is asked (:class:`lanky.proofs.trace.ProofError`):
  the conclusion cited at a point the loop has not filled in, a claim that
  calls itself, a case with no closing line, a form of lanky 0.5's proofs,
  a fact cited by name that no single point fits; and a step the native run
  finds false at drawn values (:mod:`lanky.proofs.native`).

The axiom audit is read positively (:func:`audit`): exactly one answer, naming
exactly the theorem, with no axiom outside Lean's own three.
"""

from __future__ import annotations

import os
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field, replace
from typing import Any

import pymbolic.primitives as prim

from lanky.audit import TRUSTED_AXIOMS, audit_failure
from lanky.citations import Citation
from lanky.proofs.cases import Shape, affine, from_affine, shape_of
from lanky.proofs.trace import Asserted, ClaimDef, Given, Leaf, Proof, ProofError, shown
from lanky.terms import Forall, Var, init_args, render

__all__ = [
    "CLOSED_WITH_HOLES",
    "Failure",
    "also_needs",
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
        repair: How the fix changes the proof, for Lean to confirm it
            (:func:`lanky.proofs._checked_fix`): ``("point", index,
            citation)`` puts the step's fact at ``index`` at another point,
            ``("add", citation)`` cites one more fact. Not kept in the ledger.
    """

    kind: str
    line: int | None
    headline: str
    lines: tuple[str, ...] = ()
    fix: str | None = None
    repair: Any = field(default=None, compare=False, repr=False)

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
        "self-reference": "the claim calls itself in its own proof",
        "removed": "the proof is written in a form of lanky 0.5",
        "later": "the conclusion is cited where the loop has not reached",
        "no-point": "a fact cited by its name fits no single point",
        "measure": "the conclusion is not cited at earlier points",
        "claim": "the claim's tree is not used as lanky reads it",
        "form": "the claim's tree is not used as lanky reads it",
        "close": "a case of the proof has no closing line",
        "return": "a return gives something that is no reason",
        "yield": "a yield is not where a point of the conclusion's domain is",
        "assert": "an assert is not a step lanky reads",
        "false": "a step of its proof is false",
        "question": "the proof asks a question lanky does not split on",
        "raised": "the proof raised",
        "paths": "the proof does not run the same way on every path",
        "cite": "a fact is cited at the wrong number of values",
        "unsupported": "Lean cannot state part of the proof",
        "chain": "the chain does not give the claim",
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
    return _Algebra(sympy, case, sums=True)


def combination(claim: Any, bodies: Sequence[Any], types: Mapping[str, Any]) -> list[Any] | None:
    """Multipliers whose combination of ``bodies`` is ``claim``, all equations; ``None`` for none.

    lanky's certificate search (:func:`lanky.induction._solve`), limited to
    the instances the step cites. The multipliers are terms over the case's
    names, which ``linear_combination`` is handed; Lean checks them.

    The search is linear in the atoms, the applications of families and the
    sums. A step that is one of its facts up to algebra, with an atom
    squared on both sides, is not linear in that atom: the claim at ``n -
    1`` that the cubes sum to the square of the sum, for the step from
    ``sum(i**3 for i in Fin(n)) + n**3`` to ``sum(i for i in Fin(n))**2 +
    n**3``. Where the search finds nothing, a fact the step is, or is the
    negation of, once each side is less the other, is taken alone, with the
    multiplier ``1`` or ``-1``.
    """
    from lanky.induction import _Instance, _solve, _Unsupported

    algebra = _algebra(claim, types)
    if algebra is None:
        return None
    sympy = algebra.sympy
    try:
        goal = algebra.side(claim, {})
        instances = []
        for body in bodies:
            side = algebra.side(body, {})
            instances.append(_Instance(None, (), side, algebra.applications(side)))  # type: ignore[arg-type]
    except (_Unsupported, Exception):  # noqa: BLE001 - what the search cannot read has none
        return None
    try:
        multipliers = _solve(sympy, goal, instances)
    except Exception:  # noqa: BLE001 - what the search cannot read has none
        multipliers = None
    if multipliers is None:
        multipliers = _one_of_them(sympy, goal, [instance.side for instance in instances])
    if multipliers is None:
        return None
    return [algebra.back(multiplier) for multiplier in multipliers]


def _one_of_them(sympy: Any, goal: Any, sides: Sequence[Any]) -> list[Any] | None:
    """Multipliers ``1`` or ``-1`` for the one fact the goal is, and ``0`` for the rest."""
    for index, side in enumerate(sides):
        for sign in (1, -1):
            try:
                if sympy.expand(goal - sign * side) != 0:
                    continue
            except Exception:  # noqa: BLE001 - what sympy cannot expand is not this fact
                break
            multipliers = [sympy.Integer(0)] * len(sides)
            multipliers[index] = sympy.Integer(sign)
            return multipliers
    return None


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
    arguments, ``D[a - 2, b + 3]``, and a sum's atom as the sum.
    """
    from lanky.cas import from_sympy

    sympy = algebra.sympy
    atoms = sorted(algebra.applications(expr), key=str)
    variables: dict[str, Any] = {name: Var(name) for name in algebra.case.variables}
    sums = {atom: term for term, atom in getattr(algebra, "atoms", ())}
    marks = {}
    for index, atom in enumerate(atoms):
        mark = sympy.Symbol(f"lanky_application_{index}")
        marks[atom] = mark
        if atom in sums:
            variables[mark.name] = sums[atom]
            continue
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
        goal = proof.conclusion
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
    of its terms is a term of the claim or of another fact of the step, as
    the matcher lines it up (:func:`lanky.matching.candidate_points`), and
    the step is tried again with the multiplier search
    (:func:`combination`): the first that works is the fix, as the index of
    the fact among the step's and the citation at the new point. Lean is
    asked to confirm it before the report calls it checked. The claim is put
    only at points closer to a base case, by ``measure``
    (:class:`lanky.proofs.compile.Measure`): never at its own point, which
    would make the step a circle.
    """
    from lanky.induction import Lemma
    from lanky.matching import candidate_points, instantiate

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
        if not isinstance(shape.body, prim.Comparison):
            continue
        unknowns = [var.name for var, _ in shape.binders]
        others = [other.body for position, other in enumerate(instances) if position != index]
        lemma = Lemma(citation.name, shape.binders, shape.premises, shape.body)
        tried: set[tuple[str, ...]] = {tuple(_key(value) for value in citation.values)}
        try:
            points = candidate_points(lemma, [*others, claim], step.types)
        except Exception:  # noqa: BLE001 - a fact the matcher cannot line up has no fix
            continue
        for values in points:
            key = tuple(_key(value) for value in values)
            if key in tried:
                continue
            if citation.is_claim and not _smaller(citation.source, values):
                continue
            tried.add(key)
            body = instantiate(shape.body, dict(zip(unknowns, values, strict=True)))
            if combination(claim, [*others, body], step.types) is not None:
                return index, replace(citation, values=tuple(values))
    return None


def _key(value: Any) -> str:
    """A value as text, to tell points apart: a term rendered, a family's value as a function."""
    shown_value = getattr(value, "shown", None)
    if callable(shown_value):
        return shown_value()
    return render(value) if hasattr(value, "mapper_method") else repr(value)


def _smaller(claim: ClaimDef, values: Sequence[Any]) -> bool:
    """Whether the conclusion at ``values`` comes earlier in the proof's loops (design 3.5)."""
    from lanky.proofs.trace import earlier_point

    return earlier_point(claim, values)


def also_needs(step: Any, proof: Proof, measure: Any = None) -> Citation | None:
    """A fact the proof has that the step does not cite, with which the step follows.

    The step's facts do not give its claim, and none of them cited at
    another point does either (:func:`fix_for`). So each fact the proof can
    cite is tried as one more: the theorem's hypotheses, in the order they
    are written, the claim at points closer to a base case, and the theorems
    the proof cites elsewhere. Each is put at every point at which one of
    its terms is a term of the step's claim or of a fact the step cites, and
    the first with which the multiplier search (:func:`combination`) finds
    the claim is the answer, cited at that point (by its name alone for a
    fact with no variables). ``None`` where none is found, and where the
    step's own facts already give its claim as Python sees it, which leaves
    Lean's failure to some other cause. Lean is asked to confirm it before
    the report calls it checked.
    """
    from lanky.induction import Lemma
    from lanky.matching import candidate_points

    instances = list(step.instances)
    bodies = [instance.body for instance in instances]
    if not _equation(step.claim) or not all(_equation(body) for body in bodies):
        # a combination is of equations, into an equation
        return None
    if combination(step.claim, bodies, step.types) is not None:
        return None
    terms = [*bodies, step.claim]
    cited: dict[str, set[tuple[str, ...]]] = {}
    for instance in instances:
        key = tuple(_key(value) for value in instance.values)
        cited.setdefault(instance.citation.name, set()).add(key)
    for source in _candidates(proof):
        shapes = _shapes(source, proof)
        if not shapes:
            continue
        unknowns = [var.name for var, _ in shapes[0].binders]
        if any([var.name for var, _ in shape.binders] != unknowns for shape in shapes):
            # the parts of p & q at different points: one citation cannot give both
            continue
        name = Citation(source, None, None).name
        tried = set(cited.get(name, ()))
        if not all(_equation(shape.body) for shape in shapes):
            continue
        if not unknowns:
            if () in tried:
                continue
            extra = [shape.body for shape in shapes]
            if combination(step.claim, [*bodies, *extra], step.types) is not None:
                return Citation(source, None, step.where)
            continue
        for shape in shapes:
            # the points at which one of its terms is one of the step's, as the
            # one matcher lines them up (:func:`lanky.matching.candidate_points`)
            lemma = Lemma(name, shape.binders, shape.premises, shape.body)
            try:
                points = candidate_points(lemma, terms, step.types)
            except Exception:  # noqa: BLE001 - a fact the matcher cannot line up adds nothing
                continue
            for values in points:
                key = tuple(_key(value) for value in values)
                if key in tried:
                    continue
                tried.add(key)
                if isinstance(source, ClaimDef) and not _smaller(source, values):
                    continue
                solution = dict(zip(unknowns, values, strict=True))
                extra = [each.at(solution)[0] for each in shapes]
                if combination(step.claim, [*bodies, *extra], step.types) is not None:
                    return Citation(
                        source,
                        tuple(values),
                        step.where,
                        bracket=True,
                    )
    return None


def _equation(term: Any) -> bool:
    """Whether a term is an equation, ``x == y``, which a linear combination combines."""
    return isinstance(term, prim.Comparison) and term.operator == "=="


def _candidates(proof: Proof) -> list[Any]:
    """What a proof can cite: the theorem's hypotheses, the claim, and the theorems it cites."""
    givens: dict[str, Given] = {}
    for leaf in proof.leaves:
        for citation in leaf.citations:
            if isinstance(citation.source, Given):
                givens.setdefault(citation.source.name, citation.source)
    out: list[Any] = []
    for name, prop in getattr(proof.theorem, "hypotheses", ()):
        # a fact has no truth value to ask for, so not ``givens.get(name) or ...``
        out.append(givens[name] if name in givens else Given(name, prop, None))  # type: ignore[arg-type]
    if proof.claim is not None:
        out.append(proof.claim)
    out.extend(proof.cited)
    return out


def written_with(step: Any, citation: Citation) -> str:
    """The step written to cite ``citation`` too: its ``assert``'s or ``yield``'s ``by(...)``."""
    owner = getattr(step, "owner", None)
    if isinstance(owner, Asserted):
        texts = [*(fact.text() for fact in owner.facts), citation.text()]
        return f"assert ..., by({', '.join(texts)})"
    leaf: Leaf | None = step.leaf
    facts = leaf.facts if leaf is not None else ()
    texts = [*(fact.text() for fact in facts or ()), citation.text()]
    word = "yield" if leaf is not None and leaf.point else "return"
    return f"{word} by({', '.join(texts)})"


def known_lines(
    claim: Any, types: Mapping[str, Any], exclude: Sequence[str] = ()
) -> tuple[list[str], list[str]]:
    """What :mod:`lanky.known` has of a step's shape, as the report says it, and the names.

    Each fact whose statement fits a term of ``claim`` (:func:`lanky.suggest.suggestions`),
    a line each: ``log_of_a_power rewrites log(x**n); here log(abs(alpha)**2),
    at x = abs(alpha), n = 2``; and the facts' names, each once, for the
    import. A suggestion is help, and one that cannot be made is left out
    without a word: two empty lists.
    """
    try:
        from lanky.suggest import suggestions

        fitting = suggestions(claim, dict(types), exclude=tuple(exclude))
    except Exception:  # noqa: BLE001 - a suggestion is help, and its failure no one's
        return [], []
    names = list(dict.fromkeys(suggestion.name for suggestion in fitting))
    return [suggestion.text for suggestion in fitting], names


# }}}


# {{{ reading Lean's answer


#: The axioms a proof may rest on: Lean's own three (:data:`lanky.audit.TRUSTED_AXIOMS`).
ALLOWED_AXIOMS = TRUSTED_AXIOMS

#: What a proof's verdict is when every ``sorry`` Lean found is at a step the
#: proof left open, ``by(...)``, and nothing else is wrong: the claim reads
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
    left open, ``by(...)``, and nowhere else (:data:`CLOSED_WITH_HOLES`). A
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
    failure of the measure is reported alone, as it was written, where it is
    the only one. Beside a step Lean could not show it is left out: the
    trace has already refused a citation at a point that is not earlier,
    and Lean leaves the measure unproved after a failed step too, where it
    holds, so the report said "the conclusion is not cited at earlier
    points" of a proof whose step was false.
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
    others = [failure for failure in failures if failure.kind != "measure"]
    if measured and not others:
        return False, measured[:1]
    failures = others
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
        lines = [f"{lead} case's claim is {render(claim)}, and lanky could not show it alone."]
        word = "yield" if detail.get("point") else "return"
        fix = f"give the facts it needs, as {word} by(f, g)"
        known, names = known_lines(claim, _case_types(proof), exclude=(proof.theorem.__name__,))
        if known:
            lines.append("What lanky knows of its shape:")
            lines += [f"  {line}" for line in known]
            fix += f", after from lanky.known import {', '.join(names)}"
        return Failure(
            "routine",
            origin.line,
            "a case lanky was left to close does not follow",
            tuple(lines),
            fix,
        )
    if origin.kind == "measure":
        claim = proof.claim
        params = ", ".join(claim.params) if claim else ""
        name = getattr(proof.theorem, "qualname", None) or proof.theorem.__name__
        return Failure(
            "measure",
            origin.line,
            "the conclusion is not cited at earlier points",
            (
                f"Lean could not show that each citation of {name}.conclusion is at an "
                f"earlier point of the loop than ({params}).",
            ),
            "cite the conclusion where one value is smaller and stays a natural number, or "
            "loop over a bounded domain with reversed(...) for a value that climbs",
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
    if origin.kind in ("chain", "link", "asserted", "asserted-end"):
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


def _case_types(proof: Proof) -> dict[str, Any]:
    """The sort of every name a case of the proof has: the theorem's variables and the claim's."""
    types = dict(getattr(proof.theorem, "variables", ()))
    if proof.claim is not None:
        types.update(zip(proof.claim.params, proof.claim.domains, strict=True))
    else:
        goal = getattr(proof.theorem, "goal", None)
        if isinstance(goal, Forall):
            types.update((var.name, domain) for var, domain in goal.binders)
    return types


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
                "the claim is cited at a negative value",
                (
                    f"{citation.text()} is at a negative {negative} when {negative} = {at}: "
                    f"split off {negative} < {int(drop)} first.",
                ),
                f"split off {negative} < {int(drop)} first",
            )
        return Failure(
            "negative",
            origin.line,
            "the claim is cited at a negative value",
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
    repair: Any = None
    found = fix_for(step, proof, command.measure)
    if found is not None:
        index, citation = found
        fix = f"{citation.text()} makes the step follow"
        repair = ("point", index, citation)
    else:
        extra = also_needs(step, proof, command.measure)
        if extra is not None:
            said = _instance_bodies(extra, proof)
            says = f", which says {render(tidy(said[0]))}" if len(said) == 1 else ""
            lines.append(f"It also needs {_label(extra, ())}{says}.")
            fix = written_with(step, extra)
            repair = ("add", extra)
    if fix is None:
        cited = [instance.citation.name for instance in step.instances]
        known, names = known_lines(step.claim, step.types, exclude=(*cited, proof.theorem.__name__))
        if known:
            lines.append("No fact the proof cites gets there. What lanky knows of its shape:")
            lines += [f"  {line}" for line in known]
            one = "it" if len(names) == 1 else "one of them"
            fix = (
                f"cite {one}, after from lanky.known import {', '.join(names)}; "
                "or split the step in two"
            )
        elif remainder is not None and not _is_zero(remainder):
            fix = "cite the fact that gives what is left over, or split the step in two"
    del leaf
    return Failure(
        "step", step.where, "a step of its proof does not follow", tuple(lines), fix, repair
    )


def _instance_bodies(citation: Citation, proof: Proof) -> list[Any]:
    """What a cited fact says at its point: one term per part."""
    shapes = _shapes(citation.source, proof)
    if citation.values is None:
        return [shape.body for shape in shapes]
    out = []
    for shape in shapes:
        values = {
            var.name: value for (var, _), value in zip(shape.binders, citation.values, strict=False)
        }
        out.append(shape.at(values)[0])
    return out


# }}}


def _is_zero(term: Any) -> bool:
    """Whether a term is the number zero; a term compared with ``0`` would build a proposition."""
    return isinstance(term, int | float) and not isinstance(term, bool) and term == 0
