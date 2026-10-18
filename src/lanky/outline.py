"""The proof lanky found, said back in Python: ``lanky check --proofs`` and ``--steps``.

The design idea. When lanky proves a claim alone, the proof is a Lean script
that the user never sees, and the search behind it found things the user
would want to know: which facts the step of an induction combines, at which
points, and in which order the sums of an identity are exchanged. Where that
can be said in Python, in the surface a written proof uses (see the decision
of 2026-10-16 on proofs in lanky), it is said so, in the claim's own names:
its variables, the names of its hypotheses, and points written as the user
writes them, ``a - 2`` where the search worked with a fresh ``k``. Where it
cannot, the rung of the ladder that closed the claim is named in words.

Two views read the same record. ``--proofs`` prints a body, ready to paste
under the claim's docstring::

    for a, b in ct.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence[a - 2, b], ct.conclusion[a - 2, b + 2], pde[a - 2, b])

It prints a loop only where the loop's order fits the proof it found: the
conclusion at an earlier point comes earlier in the loop, lexicographic in
the conclusion's ``for`` (design 3.5). Where the induction is on a variable
that is not the first, and an earlier one changes, no loop over the
conclusion's points as written fits, and the strategy is said in words,
with the order of the ``for`` that would fit.

and ``--steps`` prints its outline in lanky's notation, a chain of equations
for each case, with the point and the reason of every link. Nothing is read
back from Lean: the Lean oracle hands each script of its ladder over as a
:class:`Script`, a string that also carries the rung it belongs to and the
plan Python found for it (a :class:`FamilyPlan` for an induction over
families, a :class:`SumPlan` for an exchange of sums), and when a script
closes a claim, :func:`found_proof` turns the plan into the record kept in the
fact's provenance as ``found_proof``.

The record is a view, and untrusted like every other output of the search: a
mistake here can print a body that does not say what Lean checked, never a
claim Lean did not check. Building it never costs a proof, since a record
that cannot be built is left with the rung's name alone.

Points. A fact is cited at a point (``pde[a - 2, b]``) unless the point is
the only one at which the fact fits the case's claim, matched as a written
proof's uncalled fact is matched: each application of a family in the fact
against each in the claim, solving offsets such as ``x + 2 == a``. Then the
fact is cited by its name alone (``yield by(stored)``). The conclusion at an
earlier point is always cited at its point, ``name.conclusion[a - 2, b +
2]``, because that point is the induction.
"""

from __future__ import annotations

import numbers
import re
from collections.abc import Mapping
from dataclasses import dataclass
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import substitute
from lanky.prelude import FinType, Refined, Sort
from lanky.terms import (
    Abs,
    Elementary,
    Exists,
    Forall,
    Sum,
    Var,
    conjuncts,
    init_args,
    structurally_equal,
)

__all__ = [
    "FamilyPlan",
    "Script",
    "SumPlan",
    "found_proof",
    "hypothesis_names",
    "proof_lines",
    "python_source",
    "step_lines",
]


# {{{ what the ladder hands over


class Script(str):
    """A script of the Lean oracle's ladder, with its rung and what Python found for it.

    It is the script's text, and is used as one everywhere a script is: sent
    to Lean, kept in the proof cache, recorded as the proof's ``tactic``.
    What it adds is read only when the script closes a claim
    (:func:`found_proof`).

    Attributes:
        rung: The rung of the ladder the script belongs to, in words that
            follow the claim's name: ``by induction on n, taking the last
            term off the sum``. Empty for a script whose words are read off
            its text (:func:`_rung_of_text`).
        plan: What the search found, where it can be said in Python: a
            :class:`FamilyPlan` or a :class:`SumPlan`, or ``None``.
    """

    rung: str
    plan: Any

    def __new__(cls, text: str, rung: str = "", plan: Any = None) -> Script:
        """The script ``text``, with its rung and plan."""
        script = super().__new__(cls, text)
        script.rung = rung
        script.plan = plan
        return script


@dataclass(frozen=True, eq=False)
class FamilyPlan:
    """An induction over families as the search found it: its order, its step and its cases.

    The terms of each case are the case's own, as :mod:`lanky.induction`
    reads them: the order of the step is ``successor + step``, a variable
    named for the script, and :func:`found_proof` writes them back in the
    claim's names.

    Attributes:
        goal: The claim, the statement's goal: its binders are the claim's
            variables, its guard their conditions, its body the equation.
        target: The variable induced on, as the claim names it.
        order: The name the cases give it where it is still a variable.
        step: How far apart the orders of the step are.
        lowest: The lowest order the goal's guard admits (``1`` for ``n >=
            1``).
        successor: The name of the variable the step's order is
            ``successor + step`` of.
        hypothesis: The name of the induction hypothesis among each case's
            lemmas.
        renaming: The claim's variables the cases name otherwise, by the
            claim's name.
        base: The base, as ``(value, case, uses)``: one entry with value
            ``None`` when one certificate closes every order below the step,
            else one per order there that the goal's guard admits.
        inductive: The step, as ``(case, uses)``.
    """

    goal: Forall
    target: Var
    order: str
    step: int
    lowest: int
    successor: str
    hypothesis: str
    renaming: Mapping[str, Var]
    base: tuple[tuple[int | None, Any, tuple[Any, ...]], ...]
    inductive: tuple[Any, tuple[Any, ...]]


@dataclass(frozen=True, eq=False)
class SumPlan:
    """An exchange of finite sums as the search found it (see :mod:`lanky.sums`).

    Attributes:
        goal: The statement's goal: the equation, or a universal of one.
        left: The left side, its products distributed into its sums (a
            :class:`lanky.sums.Spread`).
        order: For each sum of the right side, from the outermost, which sum
            of the left side it is.
    """

    goal: Any
    left: Any
    order: tuple[int, ...]


# }}}


# {{{ the record


#: The words for a whole-goal tactic of the ladder, by the tactic as written.
_WHOLE_GOAL = {
    "omega": "by integer arithmetic",
    "decide": "by evaluating it",
    "simp": "by simplifying it",
    "simp_all": "by simplifying it with its hypotheses",
    "simp_all <;> omega": "by simplifying it, then by integer arithmetic",
    "norm_num": "by arithmetic on its numbers",
    "positivity": "by showing each part of it positive",
    "ring": "by algebra",
    "field_simp": "by algebra, clearing its denominators",
    "(field_simp; ring)": "by algebra, clearing its denominators",
    "linarith": "by linear arithmetic from its hypotheses",
    "nlinarith": "by nonlinear arithmetic from its hypotheses",
    "(push_cast; ring)": "by algebra",
}

#: The words for a script the ladder writes inline, by how its text starts.
_INLINE = (
    (
        "simp_all [",
        "by simplifying it with the rules for exp, log and sqrt, then linear arithmetic",
    ),
    ("simp (disch", "by simplifying it, a complex number by its real and imaginary parts"),
    ("simp [", "by simplifying it with the rules for exp, log and sqrt"),
    ("intro ", "under its quantifiers, by arithmetic and simplification"),
)


def _rung_of_text(text: str) -> str:
    """The words for a script that carries none: a whole-goal tactic, or an inline script."""
    words = _WHOLE_GOAL.get(text)
    if words is not None:
        return words
    if "Complex.ext_iff" in text:
        return "by simplifying it, a complex number by its real and imaginary parts"
    for start, words in _INLINE:
        if text.startswith(start):
            return words
    return "by a script of lanky's ladder"


def found_proof(
    fact: Any, statement: Any, tactic: str, *, given: bool = False
) -> dict[str, Any]:
    """The record of the proof lanky found, kept as ``found_proof`` in the fact's provenance.

    ``tactic`` is the script that closed the claim, a :class:`Script` where
    the ladder made it; ``given`` says it was given with ``use_tactic``.
    The record holds ``how``, the rung in words, and where Python can say the
    proof, ``body``, the lines of a Python body at the indentation of a
    function's body less one level, and ``steps``, its outline (see
    :func:`step_lines`). Everything is text, so the record is the same in
    ``--json`` and in a check run in a child process.
    """
    if given:
        return {"how": "by the Lean script use_tactic gives it"}
    plan = getattr(tactic, "plan", None)
    rung = getattr(tactic, "rung", "") or _rung_of_text(str(tactic).strip())
    record: dict[str, Any] = {"how": rung}
    owner = getattr(fact, "owner", None) or "claim"
    try:
        if isinstance(plan, FamilyPlan):
            record.update(_family_record(plan, hypothesis_names(fact, statement), owner))
        elif isinstance(plan, SumPlan):
            record.update(_sum_record(plan, owner))
    except Exception:  # noqa: BLE001 - the record is a view, and never costs the proof
        pass
    return record


def hypothesis_names(fact: Any, statement: Any) -> dict[str, str]:
    """The Python name of each hypothesis the Lean statement names, by its Lean name.

    The Lean statement names the conjuncts of the claim's guard in order
    (``h0``, ``h1``, ...), and the theorem names its hypotheses, the
    parameters annotated with propositions, in the ``sequent`` of its fact's
    provenance (:meth:`lanky.theory.Theorem.fact`). A hypothesis written ``p
    & q`` is two conjuncts, and both answer to its name. Empty where the two
    cannot be paired, and a name then reads as Lean's.
    """
    sequent = getattr(fact, "provenance", {}).get("sequent")
    entries = sequent.get("hypotheses") if isinstance(sequent, dict) else None
    guard = getattr(getattr(fact, "term", None), "guard", None)
    if not entries or guard is None:
        return {}
    names = [str(entry[0]) for entry in entries]
    if len(names) == 1:
        props = [guard]
    elif isinstance(guard, prim.LogicalAnd) and len(guard.children) == len(names):
        props = list(guard.children)
    else:
        return {}
    python = [name for name, prop in zip(names, props, strict=True) for _ in conjuncts(prop)]
    terms = statement.hypothesis_terms or (None,) * len(statement.hypotheses)
    lean = [
        name
        for (name, _), term in zip(statement.hypotheses, terms, strict=False)
        if term is not None
    ]
    if len(lean) != len(python):
        return {}
    return dict(zip(lean, python, strict=True))


# }}}


# {{{ the induction


#: Seconds sympy may take to write the terms of one case's chain, after the
#: proof; past them the case is one line, the claim and the facts it rests on.
CHAIN_SECONDS = 5.0

#: How many orders a step takes at a time, in words.
_AT_A_TIME = {2: "two", 3: "three", 4: "four"}


def _family_how(plan: FamilyPlan) -> str:
    """``by induction on a, two at a time``."""
    words = f"by induction on {plan.target.name}"
    if plan.step > 1:
        count = _AT_A_TIME.get(plan.step, str(plan.step))
        words += f", {count} at a time"
    return words


def _family_record(
    plan: FamilyPlan, names: Mapping[str, str], owner: str = "claim"
) -> dict[str, Any]:
    """The body and the outline of an induction over families.

    The body is a loop over ``owner.conclusion.domain``, printed only where
    its order fits the induction found (:func:`_loop_fits`); else the record
    holds the strategy in words alone, with the order of the conclusion's
    ``for`` that would fit.
    """
    variables = [var.name for var, _ in plan.goal.binders]
    order = plan.target.name
    cases: list[tuple[str | None, Any, tuple[Any, ...]]] = []
    for value, case, uses in plan.base:
        if value is None:
            orders = list(range(plan.lowest, plan.step))
            condition = (
                f"{order} == {orders[0]}" if len(orders) == 1 else f"{order} < {plan.step}"
            )
        else:
            condition = f"{order} == {value}"
        cases.append((condition, case, uses))
    cases.append((None, *plan.inductive))

    body = [f"for {', '.join(variables)} in {owner}.conclusion.domain:"]
    outline: list[tuple[str, list[tuple[str, str]]]] = []
    points: list[tuple[Any, ...]] = []
    for index, (condition, case, uses) in enumerate(cases):
        cited = _citations(plan, case, uses, names, owner, points)
        # the two conjuncts of p & q at one point are one citation
        texts = list(dict.fromkeys(text for text, _ in cited))
        # by() adds nothing: the case follows directly
        closed = f"yield by({', '.join(texts)})"
        if condition is None and index == 0:
            body.append(f"    {closed}")
        elif condition is None:
            body += ["    else:", f"        {closed}"]
        else:
            keyword = "if" if index == 0 else "elif"
            body += [f"    {keyword} {condition}:", f"        {closed}"]
        label = "otherwise:" if condition is None else f"if {condition}:"
        outline.append((label, _case_chain(plan, case, cited)))

    point = variables[0] if len(variables) == 1 else f"({', '.join(variables)})"
    head = f"the claim at {point}, for every {_binders_words(plan.goal)}, {_family_how(plan)}"
    steps = [head, *_outline(outline)]
    if _loop_fits(variables, points):
        return {"how": _family_how(plan), "body": body, "steps": steps}
    fitting = [order, *(name for name in variables if name != order)]
    how = _family_how(plan)
    if _loop_fits(fitting, [_reordered(variables, fitting, values) for values in points]):
        how += (
            f"; a loop over {owner}.conclusion.domain fits it with the conclusion's for "
            f"written {', '.join(fitting)}"
        )
    return {"how": how, "steps": steps}


def _loop_fits(variables: list[str], points: list[tuple[Any, ...]]) -> bool:
    """Whether each point the induction cites comes earlier in a loop over ``variables``.

    The loop's order is lexicographic in the conclusion's ``for``, outer
    variables first (design 3.5): the first variable where a cited point
    differs from the loop's has to be smaller there.
    """
    from lanky.proofs.trace import _earlier

    return all(
        _earlier(variables, values, [1] * len(variables)) is None
        and any(_key((value,)) != name for name, value in zip(variables, values, strict=True))
        for values in points
    )


def _reordered(variables: list[str], order: list[str], values: tuple[Any, ...]) -> tuple[Any, ...]:
    """A point's values in another order of the variables."""
    at = dict(zip(variables, values, strict=True))
    return tuple(at[name] for name in order)


def _binders_words(goal: Forall) -> str:
    """``a, b in Nat``, ``i in Fin[n] and a, b in Nat``, with the claim's guard after ``with``."""
    groups: list[tuple[str, list[str]]] = []
    for var, domain in goal.binders:
        text = _domain_source(domain)
        if groups and groups[-1][0] == text:
            groups[-1][1].append(var.name)
        else:
            groups.append((text, [var.name]))
    parts = [f"{', '.join(names)} in {text}" for text, names in groups]
    words = parts[0] if len(parts) == 1 else f"{', '.join(parts[:-1])} and {parts[-1]}"
    if goal.guard is not None:
        words += f" with {python_source(goal.guard)}"
    return words


def _user(plan: FamilyPlan, term: Any) -> Any:
    """A term of a case in the claim's names: the step's order ``successor + step`` is the order."""
    values: dict[str, Any] = {
        introduced.name: Var(name) for name, introduced in plan.renaming.items()
    }
    if plan.order != plan.target.name:
        values[plan.order] = plan.target
    values[plan.successor] = prim.Sum((plan.target, -plan.step))
    return _tidy(substitute(term, values))


def _point(values: tuple[Any, ...]) -> str:
    """``(a - 2, b)``, or ``n - 1`` for one value."""
    texts = [python_source(value) for value in values]
    return texts[0] if len(texts) == 1 else f"({', '.join(texts)})"


def _citations(
    plan: FamilyPlan,
    case: Any,
    uses: tuple[Any, ...],
    names: Mapping[str, str],
    owner: str = "claim",
    points: list[tuple[Any, ...]] | None = None,
) -> list[tuple[str, Any]]:
    """Each fact a case's certificate uses, cited as a written proof cites it, in chain order.

    Pairs of the citation's text and the use it stands for, one per use: the
    two conjuncts of ``p & q`` at one point are two uses with one text, which
    the body writes once and the outline takes a link each for.
    """
    lemmas = {lemma.name: lemma for lemma in case.lemmas}
    ordered = _chain_order(case, uses, lemmas)
    index = [var.name for var, _ in plan.goal.binders].index(plan.target.name)

    # the points each fact is used at, to tell whether its name alone says which
    found: dict[str, set[str]] = {}
    for use in ordered:
        if use.lemma != plan.hypothesis and use.lemma in lemmas:
            name = names.get(use.lemma, use.lemma)
            found.setdefault(name, set()).add(_key(use.arguments))

    cited: list[tuple[str, Any]] = []
    for use in ordered:
        lemma = lemmas.get(use.lemma)
        if lemma is None:
            continue
        values = tuple(_user(plan, value) for value in use.arguments)
        if use.lemma == plan.hypothesis:
            # the hypothesis takes the smaller order first; the claim, its variables in order
            values = (*values[1 : index + 1], values[0], *values[index + 1 :])
            text = f"{owner}.conclusion[{', '.join(python_source(value) for value in values)}]"
            if points is not None:
                points.append(values)
        else:
            name = names.get(use.lemma, use.lemma)
            alone = not lemma.binders or (
                len(found[name]) == 1 and _fits_alone(lemma, use, case)
            )
            text = name if alone else f"{name}[{', '.join(map(python_source, values))}]"
        cited.append((text, use))
    return cited


def _instance(lemma: Any, arguments: tuple[Any, ...]) -> Any:
    """A lemma's equation at the values of its binders."""
    values = {var.name: value for (var, _), value in zip(lemma.binders, arguments, strict=True)}
    return substitute(lemma.equation, values)


def _fits_alone(lemma: Any, use: Any, case: Any) -> bool:
    """Whether the case's claim fits the lemma at one point only, and that is the use's.

    Each application of a family in the lemma's equation is matched against
    each in the claim, solving the offsets of its binders (``x + 2 == a``
    gives ``x = a - 2``). A match that leaves a binder unsolved, or solves
    one two ways, is no match.
    """
    unknowns = [var.name for var, _ in lemma.binders]
    found: set[str] = set()
    for family, pattern in _applications(lemma.equation):
        for other, target in _applications(case.goal):
            if family != other or len(pattern) != len(target):
                continue
            solved = _solve(pattern, target, unknowns)
            if solved is not None:
                found.add(_key(tuple(solved[name] for name in unknowns)))
    return found == {_key(use.arguments)}


def _solve(
    pattern: tuple[Any, ...], target: tuple[Any, ...], unknowns: list[str]
) -> dict[str, Any] | None:
    """The values of ``unknowns`` that make the arguments ``pattern`` the arguments ``target``."""
    values: dict[str, Any] = {}
    for written, wanted in zip(pattern, target, strict=True):
        form = _affine(written)
        if form is None:
            if _key((written,)) != _key((wanted,)):
                return None
            continue
        present = [name for name in unknowns if form.get(name)]
        if not present:
            if _key((written,)) != _key((wanted,)):
                return None
            continue
        if len(present) > 1 or abs(form[present[0]]) != 1:
            return None
        name = present[0]
        rest = _from_affine({key: value for key, value in form.items() if key != name})
        # written = sign * name + rest, so name = sign * (wanted - rest)
        value = prim.Sum((wanted, prim.Product((-1, rest))))
        if form[name] < 0:
            value = prim.Product((-1, value))
        value = _tidy(value)
        if name in values and _key((values[name],)) != _key((value,)):
            return None
        values[name] = value
    if set(values) != set(unknowns):
        return None
    return values


def _applications(term: Any) -> list[tuple[str, tuple[Any, ...]]]:
    """Every application of a family in ``term``, as ``(family, arguments)``, outermost first."""
    found: list[tuple[str, tuple[Any, ...]]] = []
    stack = [term]
    while stack:
        node = stack.pop()
        spine = _spine(node)
        if spine is not None:
            found.append(spine)
            stack.extend(reversed(spine[1]))
            continue
        if isinstance(node, Forall | Exists | Sum):
            stack.extend(part for part in (node.guard, node.body) if part is not None)
        elif isinstance(node, tuple):
            stack.extend(reversed(node))
        elif isinstance(node, prim.ExpressionNode):
            for child in reversed(init_args(node)):
                stack.extend(reversed(child) if isinstance(child, tuple) else (child,))
    return found


def _spine(term: Any) -> tuple[str, tuple[Any, ...]] | None:
    """``(family, arguments)`` of a chain of applications, ``R(a)(b)`` and ``R[a, b]`` alike."""
    arguments: tuple[Any, ...] = ()
    node = term
    while isinstance(node, prim.Call | prim.Subscript):
        if isinstance(node, prim.Call):
            arguments = (*node.parameters, *arguments)
            node = node.function
        else:
            index = node.index if isinstance(node.index, tuple) else (node.index,)
            arguments = (*index, *arguments)
            node = node.aggregate
    if node is term or not isinstance(node, prim.Variable):
        return None
    return node.name, arguments


def _chain_order(case: Any, uses: tuple[Any, ...], lemmas: Mapping[str, Any]) -> list[Any]:
    """The uses in the order a chain from the claim's left side to its right takes them.

    The first is a use that mentions an application of the claim's left side,
    and each next one mentions an application the one before brought in, as
    a textbook's displayed calculation goes: ``R[a, b]``, the recurrence to
    ``-R[a - 2, b + 2]``, the claim there to ``-D[a - 2, b + 2]``, the PDE to
    ``D[a, b]``. Ties keep the order the search found the uses in.
    """
    atoms = []
    for use in uses:
        lemma = lemmas.get(use.lemma)
        applied = _applications(_instance(lemma, use.arguments)) if lemma is not None else []
        atoms.append({_key((prim.Variable(name), *arguments)) for name, arguments in applied})
    goal = case.goal
    start = _applications(goal.left) if isinstance(goal, prim.Comparison) else []
    if not start:
        start = _applications(goal)
    seen = {_key((prim.Variable(name), *arguments)) for name, arguments in start}
    latest = set(seen)
    remaining = list(range(len(uses)))
    ordered = []
    while remaining:
        pick = next((i for i in remaining if atoms[i] & latest), None)
        if pick is None:
            pick = next((i for i in remaining if atoms[i] & seen), remaining[0])
        remaining.remove(pick)
        ordered.append(uses[pick])
        fresh = atoms[pick] - seen
        seen |= atoms[pick]
        latest = fresh or latest
    return ordered


def _reason(plan: FamilyPlan, use: Any, text: str, lemma: Any, multiplier: str | None) -> str:
    """Why a link of a case's chain holds: ``by pde, at (a - 2, b)``."""
    if use.lemma == plan.hypothesis:
        reason = f"by the claim at {_point_of_call(text)}"
    else:
        name = text.split("[", 1)[0]
        reason = f"by {name}"
        if lemma is not None and lemma.binders:
            reason += f", at {_point(tuple(_user(plan, value) for value in use.arguments))}"
    if multiplier is not None:
        reason += f", times {multiplier}"
    return reason


def _together(plan: FamilyPlan, cited: list[tuple[str, Any]], lemmas: Mapping[str, Any]) -> str:
    """Why a case holds, said at once: ``from recurrence at (a - 2, b) and pde at (a - 2, b)``."""
    if not cited:
        return "by algebra"
    if len(cited) == 1:
        text, use = cited[0]
        return _reason(plan, use, text, lemmas.get(use.lemma), None)
    words = list(
        dict.fromkeys(
            _reason(plan, use, text, lemmas.get(use.lemma), None)[len("by ") :].replace(
                ", at ", " at "
            )
            for text, use in cited
        )
    )
    if len(words) == 1:
        return f"by {words[0]}"
    return f"from {', '.join(words[:-1])} and {words[-1]}"


def _point_of_call(text: str) -> str:
    """The point of ``name.conclusion[a - 2, b + 2]``: ``(a - 2, b + 2)``, or ``n - 1``."""
    inside = text[text.index("[") + 1 : -1]
    return f"({inside})" if "," in inside else inside


def _case_chain(
    plan: FamilyPlan, case: Any, cited: list[tuple[str, Any]]
) -> list[tuple[str, str]]:
    """A case's outline as ``(term, reason)`` lines: a chain from its claim's left side.

    Each link takes away one cited fact times its multiplier, so it follows
    from that fact by algebra, and the last link ends at the claim's right
    side. sympy writes the terms between, as the search found the
    multipliers with it; where it cannot, the case is one line, the claim
    with every fact it rests on.
    """
    from lanky.deadline import Expired, deadline

    lemmas = {lemma.name: lemma for lemma in case.lemmas}
    goal = case.goal
    claim_text = python_source(_user(plan, goal))
    owner = object()
    try:
        with deadline(CHAIN_SECONDS, owner):
            links = _sympy_chain(plan, case, cited, lemmas)
    except Expired as exc:
        if exc.owner is not owner:
            raise
        links = None
    except Exception:  # noqa: BLE001 - without sympy, or a term it cannot read: one line
        links = None
    if links is None:
        return [(claim_text, _together(plan, cited, lemmas))]
    left = python_source(_user(plan, goal.left))
    lines = []
    for position, (term, reason) in enumerate(links):
        lines.append((f"{left} == {term}" if position == 0 else f"== {term}", reason))
    return lines


def _sympy_chain(
    plan: FamilyPlan, case: Any, cited: list[tuple[str, Any]], lemmas: Mapping[str, Any]
) -> list[tuple[str, str]] | None:
    """The links of a case's chain, each term in the claim's names, with its reason."""
    from lanky.cas import sympy_module
    from lanky.induction import _Algebra

    sympy = sympy_module()
    algebra = _Algebra(sympy, case)
    goal = case.goal
    current = algebra.convert(goal.left, {})
    right = algebra.convert(goal.right, {})
    links: list[tuple[Any, str]] = []
    for text, use in cited:
        lemma = lemmas[use.lemma]
        side = algebra.side(_instance(lemma, use.arguments), {})
        multiplier = algebra.convert(use.multiplier, {})
        current = _tidied(sympy, current - multiplier * side)
        shown = None
        if multiplier not in (1, -1):
            shown = python_source(_coefficients_first(_user(plan, use.multiplier)))
        links.append((current, _reason(plan, use, text, lemma, shown)))
    if not links:
        return None
    if sympy.simplify(current - right) != 0:
        # the chain stops short of the claim: say what is left
        links.append((right, "by algebra"))
    out = []
    for position, (term, reason) in enumerate(links):
        if position == len(links) - 1:
            shown_term = _user(plan, goal.right)
        else:
            shown_term = _user(plan, _from_sympy(sympy, term))
        out.append((python_source(shown_term), reason))
    return out


def _tidied(sympy: Any, expr: Any) -> Any:
    """``expr`` with the coefficient of each application gathered and factored."""
    applications = sorted(expr.atoms(sympy.core.function.AppliedUndef), key=str)
    expanded = sympy.expand(expr)
    if not applications:
        return sympy.factor(expanded)
    return sympy.collect(expanded, applications, func=sympy.factor)


def _from_sympy(sympy: Any, expr: Any) -> Any:
    """A sympy expression as a lanky term, a family's application as one in brackets."""
    from lanky.cas import from_sympy

    applications = sorted(expr.atoms(sympy.core.function.AppliedUndef), key=str)
    marks = {
        application: sympy.Symbol(f"_lanky_application_{index}")
        for index, application in enumerate(applications)
    }
    variables = {
        mark.name: prim.Subscript(
            Var(application.func.__name__),
            tuple(_tidy(_from_sympy(sympy, argument)) for argument in application.args),
        )
        for application, mark in marks.items()
    }
    return _coefficients_first(_tidy(from_sympy(expr.xreplace(marks), variables)))


def _coefficients_first(term: Any) -> Any:
    """``term`` with the factors of each product in the order a hand writes them.

    sympy sorts the factors of a product its own way, which puts ``R[a - 2,
    b]`` before ``k**2``; a coefficient reads first: numbers, then the other
    factors, then the applications of families, each kept in its order.
    """
    if isinstance(term, tuple):
        return tuple(_coefficients_first(item) for item in term)
    if not isinstance(term, prim.ExpressionNode) or isinstance(term, Forall | Exists | Sum):
        return term
    if isinstance(term, Elementary):
        return Elementary(term.function, _coefficients_first(term.argument))
    if isinstance(term, Abs):
        return Abs(_coefficients_first(term.operand))
    rebuilt = type(term)(*(_coefficients_first(argument) for argument in init_args(term)))
    if isinstance(rebuilt, prim.Product):

        def rank(child: Any) -> int:
            if isinstance(child, numbers.Number):
                return 0
            return 2 if _spine(child) is not None else 1

        rebuilt = type(rebuilt)(tuple(sorted(rebuilt.children, key=rank)))
    return rebuilt


def _outline(cases: list[tuple[str, list[tuple[str, str]]]]) -> list[str]:
    """The cases' lines: labels in a column, chains under their first ``==``, reasons aligned."""
    width = max(len(label) for label, _ in cases) + 2
    rows: list[tuple[str, str]] = []
    for label, lines in cases:
        indent = " " * width
        under = 0
        for position, (term, reason) in enumerate(lines):
            if position == 0:
                under = term.find(" == ") + 1 if " == " in term else 0
                rows.append((f"  {label.ljust(width)}{term}", reason))
            else:
                rows.append((f"  {indent}{' ' * under}{term}", reason))
    column = max(len(text) for text, _ in rows) + 2
    return [f"{text.ljust(column)}{reason}".rstrip() for text, reason in rows]


# }}}


# {{{ the sums


def _sum_record(plan: SumPlan, owner: str = "claim") -> dict[str, Any]:
    """The chain of an exchange of sums: the left side, its sums in one order, the right side."""
    goal = plan.goal
    body_term = goal.body if isinstance(goal, Forall) else goal
    left, right = body_term.left, body_term.right
    spread = plan.left
    binders = [spread.binders[index] for index in plan.order]
    renaming = _original_names(spread, binders)
    middle = Sum(
        tuple((Var(renaming.get(var.name, var.name)), domain) for var, domain in binders),
        _renamed(spread.body, renaming),
        None,
    )
    head: list[str] = []
    indent = ""
    if isinstance(goal, Forall):
        variables = [var.name for var, _ in goal.binders]
        point = variables[0] if len(variables) == 1 else f"({', '.join(variables)})"
        head = [f"the claim at {point}, for every {_binders_words(goal)}"]
        indent = "  "
    first = python_source(left)
    if structurally_equal(middle, left):
        why = "the products distributed into the sums, which are in one order already"
        return {
            "how": "by distributing the products into the sums, which are in one order already",
            "steps": [*head, f"{indent}{first} == {python_source(right)}  {why}"],
        }
    order = ", ".join(renaming.get(var.name, var.name) for var, _ in binders)
    chain = [first, f"== {python_source(middle)}", f"== {python_source(right)}"]
    asserted = ["assert (", *(f"    {line}" for line in chain), ")"]
    if isinstance(goal, Forall):
        signature = ", ".join(var.name for var, _ in goal.binders)
        body = [
            f"for {signature} in {owner}.conclusion.domain:",
            *(f"    {line}" for line in asserted),
            "    yield by()",
        ]
    else:
        body = [*asserted, "return by()"]
    steps = [
        f"{indent}{first} == {python_source(middle)}",
        f"{indent}{' ' * (len(first) + 1)}== {python_source(right)}",
    ]
    reasons = [f"the sums in the order {order}", "the products distributed into the sums"]
    column = max(len(line) for line in steps) + 2
    return {
        "how": "by putting the sums in one order",
        "body": body,
        "steps": [
            *head,
            *(f"{line.ljust(column)}{reason}" for line, reason in zip(steps, reasons, strict=True)),
        ],
    }


def _original_names(spread: Any, binders: list[tuple[Var, Any]]) -> dict[str, str]:
    """The names the user gave the sums' binders, where :func:`lanky.sums.spread` made fresh ones.

    ``spread`` names a binder ``i_1`` for an ``i``; the ``i`` is given back
    unless two binders would share it or the summand already uses it.
    """
    taken = _names(spread.body) - {var.name for var, _ in binders}
    stems = {var.name: re.sub(r"_\d+$", "", var.name) for var, _ in binders}
    if len(set(stems.values())) != len(stems) or set(stems.values()) & taken:
        return {}
    return stems


def _renamed(term: Any, renaming: Mapping[str, str]) -> Any:
    return substitute(term, {old: Var(new) for old, new in renaming.items()})


def _names(term: Any) -> set[str]:
    """Every variable ``term`` mentions."""
    from lanky.sums import mentioned

    return mentioned(term)


# }}}


# {{{ integer arguments, normalized


def _affine(expr: Any) -> dict[str, int] | None:
    """``expr`` as an integer combination of variables plus a constant (key ``""``), or ``None``."""
    if isinstance(expr, bool):
        return None
    if isinstance(expr, numbers.Integral):
        return {"": int(expr)}
    if isinstance(expr, prim.Variable):
        return {expr.name: 1}
    if isinstance(expr, prim.Sum):
        total: dict[str, int] = {}
        for child in expr.children:
            form = _affine(child)
            if form is None:
                return None
            for key, value in form.items():
                total[key] = total.get(key, 0) + value
        return total
    if isinstance(expr, prim.Product):
        scale = 1
        inner: dict[str, int] | None = None
        for child in expr.children:
            if isinstance(child, numbers.Integral) and not isinstance(child, bool):
                scale *= int(child)
                continue
            if inner is not None:
                return None
            inner = _affine(child)
            if inner is None:
                return None
        inner = inner or {"": 1}
        return {key: scale * value for key, value in inner.items()}
    return None


def _from_affine(form: Mapping[str, int], order: list[str] | None = None) -> Any:
    """The term an affine form is: its variables in ``order``, then its constant."""
    names = [name for name in (order or sorted(form)) if name and form.get(name)]
    names += [name for name in sorted(form) if name and form.get(name) and name not in names]
    children: list[Any] = []
    for name in names:
        coefficient = form[name]
        var = Var(name)
        if coefficient == 1:
            children.append(var)
        elif coefficient == -1:
            children.append(prim.Product((-1, var)))
        else:
            children.append(prim.Product((coefficient, var)))
    constant = form.get("", 0)
    if constant or not children:
        children.append(constant)
    return children[0] if len(children) == 1 else prim.Sum(tuple(children))


def _tidy(expr: Any) -> Any:
    """``expr`` with each integer combination of variables in it normalized: ``a - 2 + 2`` is ``a``.

    The variables keep the order they first appear in, and the constant comes
    last, as a hypothesis is written: ``b + 2``, ``a - 2``.
    """
    if isinstance(expr, tuple):
        return tuple(_tidy(item) for item in expr)
    if isinstance(expr, Forall | Exists | Sum):
        guard = None if expr.guard is None else _tidy(expr.guard)
        return type(expr)(expr.binders, _tidy(expr.body), guard)
    if not isinstance(expr, prim.ExpressionNode):
        return expr
    if isinstance(expr, prim.Sum | prim.Product):
        form = _affine(expr)
        if form is not None:
            return _from_affine(form, _first_seen(expr))
    if isinstance(expr, Elementary):
        return Elementary(expr.function, _tidy(expr.argument))
    if isinstance(expr, Abs):
        return Abs(_tidy(expr.operand))
    rebuilt = type(expr)(*(_tidy(argument) for argument in init_args(expr)))
    # what a case pins leaves x ** 1 and x / 1, as in the claim at n == 1
    if isinstance(rebuilt, prim.Power) and _is_integer(rebuilt.exponent, 1):
        return rebuilt.base
    if isinstance(rebuilt, prim.Quotient) and _is_integer(rebuilt.denominator, 1):
        return rebuilt.numerator
    if isinstance(rebuilt, prim.Quotient) and _is_integer(rebuilt.numerator, 0):
        return 0
    return rebuilt


def _is_integer(value: Any, number: int) -> bool:
    """Whether ``value`` is the plain integer ``number``, and not a term that equals it."""
    return isinstance(value, numbers.Integral) and not isinstance(value, bool) and value == number


def _first_seen(expr: Any) -> list[str]:
    """The variables of ``expr`` in the order they first appear."""
    seen: list[str] = []
    stack = [expr]
    while stack:
        node = stack.pop()
        if isinstance(node, prim.Variable):
            if node.name not in seen:
                seen.append(node.name)
        elif isinstance(node, prim.ExpressionNode):
            stack.extend(reversed(init_args(node)))
        elif isinstance(node, tuple):
            stack.extend(reversed(node))
    return seen


def _key(values: tuple[Any, ...]) -> str:
    """A key that two points share exactly when they are the same once normalized."""
    return "\x00".join(python_source(_tidy(value)) for value in values)


# }}}


# {{{ Python source


# Python's precedences, loosest first.
_OR, _AND, _NOT, _CMP, _ADD, _MUL, _NEG, _POW, _ATOM = range(1, 10)


def python_source(expr: Any, outer: int = 0) -> str:
    """A term as Python source, as ``ruff format`` writes it, in the surface's conventions.

    A family's application is written in brackets, ``R[a, b]``, however it
    was applied; a sum is ``sum(... for i in Fin[n] ...)``; ``*``, ``/``,
    ``+`` and ``-`` have spaces around them, and ``**`` has none between
    simple operands (``r**k``), as ``ruff format`` hugs it. A fraction is a
    true division, ``1 / 3``.
    """
    if isinstance(expr, bool):
        return str(expr)
    if isinstance(expr, prim.Variable):
        return expr.name
    if isinstance(expr, Fraction):
        if expr.denominator == 1:
            return python_source(int(expr.numerator), outer)
        text = f"{expr.numerator} / {expr.denominator}"
        if expr.numerator < 0:
            text = f"-{-expr.numerator} / {expr.denominator}"
        return _wrap(text, _MUL, outer)
    if isinstance(expr, numbers.Number):
        text = repr(expr) if isinstance(expr, complex) else str(expr)
        return _wrap(text, _NEG if text.startswith("-") else _ATOM, outer)
    if isinstance(expr, Sum):
        guard = f" if {python_source(expr.guard, _OR)}" if expr.guard is not None else ""
        return f"sum({python_source(expr.body)} {_generators(expr)}{guard})"
    if isinstance(expr, Forall | Exists):
        word = "all" if isinstance(expr, Forall) else "any"
        guard = f" if {python_source(expr.guard, _OR)}" if expr.guard is not None else ""
        return f"{word}({python_source(expr.body)} {_generators(expr)}{guard})"
    if isinstance(expr, Abs):
        return f"abs({python_source(expr.operand)})"
    if isinstance(expr, Elementary):
        return f"{expr.function}({python_source(expr.argument)})"
    spine = _spine(expr)
    if spine is not None:
        name, arguments = spine
        return f"{name}[{', '.join(python_source(argument) for argument in arguments)}]"
    if isinstance(expr, prim.Comparison):
        text = (
            f"{python_source(expr.left, _CMP + 1)} {expr.operator} "
            f"{python_source(expr.right, _CMP + 1)}"
        )
        return _wrap(text, _CMP, outer)
    if isinstance(expr, prim.LogicalAnd | prim.LogicalOr):
        joiner, level = (" and ", _AND) if isinstance(expr, prim.LogicalAnd) else (" or ", _OR)
        text = joiner.join(python_source(child, level + 1) for child in expr.children)
        return _wrap(text, level, outer)
    if isinstance(expr, prim.LogicalNot):
        return _wrap(f"not {python_source(expr.child, _NOT)}", _NOT, outer)
    if isinstance(expr, prim.Sum):
        parts = []
        for position, child in enumerate(expr.children):
            negated = _negated(child)
            if position and negated is not None:
                parts.append(f" - {python_source(negated, _MUL)}")
            elif position and _negative_number(child):
                parts.append(f" - {python_source(-child, _MUL)}")
            elif position:
                parts.append(f" + {python_source(child, _ADD + 1)}")
            else:
                parts.append(python_source(child, _ADD))
        return _wrap("".join(parts), _ADD, outer)
    if isinstance(expr, prim.Product):
        negated = _negated(expr)
        if isinstance(negated, prim.Product) and _negated(negated) is None:
            # -x * y is (-x) * y, a product whose first factor stands behind the minus
            factors = [f"-{python_source(negated.children[0], _NEG)}"]
            factors += [python_source(child, _MUL + 1) for child in negated.children[1:]]
            return _wrap(" * ".join(factors), _MUL, outer)
        if negated is not None:
            return _wrap(f"-{python_source(negated, _NEG)}", _NEG, outer)
        factors = [python_source(expr.children[0], _MUL)]
        factors += [python_source(child, _MUL + 1) for child in expr.children[1:]]
        return _wrap(" * ".join(factors), _MUL, outer)
    if isinstance(expr, prim.QuotientBase):
        symbol = "/"
        if isinstance(expr, prim.FloorDiv):
            symbol = "//"
        elif isinstance(expr, prim.Remainder):
            symbol = "%"
        text = (
            f"{python_source(expr.numerator, _MUL)} {symbol} "
            f"{python_source(expr.denominator, _MUL + 1)}"
        )
        return _wrap(text, _MUL, outer)
    if isinstance(expr, prim.Power):
        base = python_source(expr.base, _POW + 1)
        exponent = python_source(expr.exponent, _NEG)
        joiner = "**" if _simple(expr.base) and _simple(expr.exponent) else " ** "
        return _wrap(f"{base}{joiner}{exponent}", _POW, outer)
    if isinstance(expr, prim.Call):
        arguments = ", ".join(python_source(argument) for argument in expr.parameters)
        return f"{python_source(expr.function, _ATOM)}({arguments})"
    return str(expr)


def _wrap(text: str, level: int, outer: int) -> str:
    return f"({text})" if level < outer else text


def _negated(expr: Any) -> Any:
    """What a product ``-1 * t`` negates, or ``None``."""
    if not isinstance(expr, prim.Product) or len(expr.children) < 2:
        return None
    first = expr.children[0]
    if isinstance(first, bool) or not isinstance(first, numbers.Integral) or first != -1:
        return None
    rest = expr.children[1:]
    return rest[0] if len(rest) == 1 else prim.Product(rest)


def _negative_number(value: Any) -> bool:
    return (
        isinstance(value, numbers.Real) and not isinstance(value, bool) and value < 0
    )


def _simple(expr: Any) -> bool:
    """Whether ``ruff format`` hugs ``**`` around an operand: a name or a plain number."""
    if isinstance(expr, prim.Variable):
        return True
    return (
        isinstance(expr, numbers.Number)
        and not isinstance(expr, bool | Fraction | complex)
    )


def _generators(expr: Forall | Exists | Sum) -> str:
    """``for i in Fin[n] for j in Fin[m]``."""
    return " ".join(f"for {var.name} in {_domain_source(domain)}" for var, domain in expr.binders)


def _domain_source(domain: Any) -> str:
    """A binder's domain as the user writes it: ``Fin[n]``, ``Nat``."""
    if isinstance(domain, FinType):
        return f"Fin[{python_source(domain.bound)}]"
    if isinstance(domain, Refined):
        props = " & ".join(f"({python_source(prop)})" for prop in domain.props)
        return f"{_domain_source(domain.base)} & {props}"
    if isinstance(domain, Sort):
        return str(domain)
    return str(domain)


# }}}


# {{{ the views


def _head(fact: Any) -> str:
    return f"{fact.owner or fact.id} at {fact.where}"


def proof_lines(fact: Any) -> list[str]:
    """What ``lanky check --proofs`` prints for a proved claim.

    ``PROOF name at file:line, how`` and, where the proof can be said in
    Python, a blank line and the body, indented as a function's body is, so
    that it pastes under the theorem's docstring.
    """
    found = fact.provenance.get("found_proof")
    proof = fact.provenance.get("proof")
    if not isinstance(found, dict) and isinstance(proof, dict) and proof.get("closed") is True:
        # proved by the body the file holds: it is already written out
        return [f"PROOF {_head(fact)}, by its proof as written, {proof.get('where')}"]
    if not isinstance(found, dict):
        return [f"PROOF {_head(fact)}, by {fact.decided_by or 'an oracle'}"]
    how = found.get("how") or "by lanky's ladder"
    body = found.get("body") or []
    if not body:
        return [f"PROOF {_head(fact)}, {how}"]
    return [f"PROOF {_head(fact)}, {how}:", "", *(f"    {line}" if line else "" for line in body)]


def step_lines(fact: Any) -> list[str]:
    """What ``lanky check --steps`` prints for a proved claim: its outline in lanky's notation.

    A claim with a written proof gets that proof's outline (:func:`written_step_lines`).
    """
    proof = fact.provenance.get("proof")
    if isinstance(proof, dict) and proof.get("outline"):
        return written_step_lines(fact)
    found = fact.provenance.get("found_proof")
    if not isinstance(found, dict):
        found = {"how": f"by {fact.decided_by or 'an oracle'}"}
    how = found.get("how") or "by lanky's ladder"
    # a rung with nothing more to say is an outline of one line
    steps = found.get("steps") or [f"the claim, {how}"]
    return [f"STEPS {_head(fact)}, as lanky found them:", *(f"  {line}" for line in steps)]


def written_step_lines(fact: Any) -> list[str]:
    """The outline of a written proof, as ``lanky check --steps`` prints it.

    A row per step, at its Python line: the case it is in, the step in
    lanky's notation, and the facts it follows from, at the points lanky
    found. The links of a chain are rows one under the other, each later
    one starting at the term the one before reached::

        STEPS compressed_taylor at l2p.py:130, as its proof says them:
          the claim at (a, b), by induction on a, 2 cases, 4 steps
          l2p.py:145  if a < 2:   R[a, b] == D[a, b]           by stored, at (a, b)
          l2p.py:148  otherwise:  R[a, b] == -R[a - 2, b + 2]  by recurrence, at (a - 2, b)
          l2p.py:149                      == -D[a - 2, b + 2]  by the claim at (a - 2, b + 2)
          l2p.py:150                      == D[a, b]           by pde, at (a - 2, b)

    lanky builds it from the proof as it compiled it; nothing is read back
    from Lean.
    """
    import os

    proof = fact.provenance.get("proof") or {}
    rows = [tuple(row) for row in proof.get("outline") or ()]
    base = os.path.basename(str(fact.provenance.get("path") or "")) or str(
        fact.where or ""
    ).split(":")[0]
    summary = proof.get("summary") or ""
    holes = proof.get("holes") or ()
    head = f"STEPS {_head(fact)}, as its proof says them:"
    out = [head, f"  the claim, {summary}" if summary else "  the claim"]
    if holes:
        out.append(f"  left open at {', '.join(str(hole) for hole in holes)}, assumed there")
    shown: list[tuple[str, str, str, str, str]] = []
    previous_right = None
    for line, case, left, relation, right, reason in rows:
        where = f"{base}:{line}" if line is not None else ""
        if not case and previous_right is not None and left == previous_right:
            left = ""
        shown.append((where, case, left, f"{relation} {right}".strip(), reason))
        previous_right = right
    if not shown:
        return out
    width_where = max(len(row[0]) for row in shown)
    width_case = max(len(row[1]) for row in shown)
    width_left = max(len(row[2]) for row in shown)
    width_step = max(len(row[3]) for row in shown)
    for where, case, left, step, reason in shown:
        out.append(
            f"  {where:<{width_where}}  {case:<{width_case}}  {left:>{width_left}} "
            f"{step:<{width_step}}  {reason}".rstrip()
        )
    return out


# }}}
