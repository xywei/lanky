"""Written proofs: a theorem's body says why it holds, and Lean checks it.

The design idea. Automation stays the default: a claim that lanky proves alone
needs no body. Where a proof helps, the theorem's body is the proof, in
ordinary Python that states facts and gives a reason for each, so that it
reads like a textbook proof read aloud::

    @theorem
    def every_box(..., pde: ..., centre: ..., stored: ..., centre_copy: ...,
                  copies: ..., recurrence: ...) -> all(R[i, a, b] == D[i, a, b] ...):
        def claim(i, a, b):
            if a + b == 0:
                return centre_copy, centre
            if a < 2:
                return copies, stored
            return recurrence(i, a - 2, b), claim(i, a - 2, b + 2), pde(i, a - 2, b)

        return claim

"The claim at (i, a, b): at order zero, by the centre's copy and the centre.
If a < 2, by the copies and what is stored. Otherwise by the recurrence, the
claim at (i, a - 2, b + 2) and the PDE. That proves the claim."

What each form means:

- a body of only a docstring, ``...`` or ``pass``: lanky finds the proof, as
  it always has;
- ``return f, g``: this case's claim follows from these facts, combined as
  lanky finds and Lean checks; a bare ``return``: lanky closes the case;
- ``pde(i, a - 2, b)``: a fact at a point, a hypothesis or a theorem, whose
  conditions are checked; ``stored`` alone: the same fact, at the point found
  by matching it against the case's claim; a hypothesis written ``p & q`` is
  cited as both parts;
- ``if`` / ``else``: a case split;
- ``def claim(i, a, b)``, returned: the claim at a point, and ``claim(i, a -
  2, b + 2)`` inside it the claim at values closer to a base case, which is
  induction.

``python file.py`` never calls a body. ``lanky check`` traces it, after every
run and draw of the check (:mod:`lanky.proofs.trace`), compiles it to one Lean
command (:mod:`lanky.proofs.compile`), and reads Lean's answer back to the
Python lines (:mod:`lanky.proofs.report`). A proof Lean accepts adds a line to
its claim's row, ``by its proof, file.py:41-48: induction on a, 3 cases, 3
steps``, and proves a claim lanky's search did not. One it does not is
reported at the line that fails, with the fix where one can be named, and
fails the check, also for a claim lanky proves alone, whose row still reads
proved by lanky's own proof: a broken proof is a failing test. A proof Lean
cannot be asked about, on a machine without Lean, or without Mathlib for a
claim only Mathlib states, is not checked, and says so.
"""

from __future__ import annotations

import time
from dataclasses import replace
from typing import Any

from lanky.citations import Citation
from lanky.ledger import Fact, Ledger, Status
from lanky.proofs.compile import Command, compile_proof
from lanky.proofs.report import CLOSED_WITH_HOLES, Failure, failure_of, fix_for, read, verdict
from lanky.proofs.trace import (
    Proof,
    ProofError,
    _tree,
    trace_proof,
    written_lines,
)
from lanky.terms import Var

__all__ = [
    "Proof",
    "ProofError",
    "check_written_proofs",
    "compile_proof",
    "prove",
    "trace_proof",
    "written_lines",
]


def check_written_proofs(ledger: Ledger, objects: Any, verbose: bool = False) -> None:
    """Check the written proof of every theorem among ``objects`` whose fact is in ``ledger``.

    :func:`lanky.check.check_path` calls this once every fact of the file is
    established, so that nothing a body does can change what a run or a draw
    of the check read. An axiom has no proof, and its body is not read.

    A proof that cites another theorem is checked after that theorem: one of
    the file with a written proof of its own is checked first, and one from
    another module (a fact of :mod:`lanky.known`, a theorem of a file the
    file imports) is established into this ledger, as a row marked with its
    module, so that what the proof rests on is in the ledger it is counted
    in (see the design's foreign facts). A citation restates the text the
    cited theorem's own command proved, which the Lean oracle keeps
    (:func:`lanky.citations.proved_texts`); the circle of two proofs citing
    each other is refused. Last, a fact a plugin stated that cites a theorem
    proved only now, and was restated by the printer when it was
    established, is asked of Lean again, from the text its command proved
    (:func:`_restate_from_proved`).
    """
    from lanky.theory import Axiom, Theorem

    pending: dict[str, Any] = {}
    for obj in objects:
        if not isinstance(obj, Theorem) or isinstance(obj, Axiom):
            continue
        if obj.fact_id not in ledger or written_lines(obj.fn) is None:
            continue
        pending.setdefault(obj.fact_id, obj)
    if not pending:
        return
    oracle = _lean_oracle()
    texts = getattr(oracle, "proved_texts", None)
    from lanky.citations import proved_texts

    if texts is not None:
        # a claim changed since its text was proved, in a long-lived process,
        # is not cited by that text, nor is any claim whose proof cited it
        texts.stale({fact.id: fact.term for fact in ledger if fact.term is not None})
    with proved_texts(texts if texts is not None else {}):
        done: set[str] = set()
        for identifier in list(pending):
            _check_in_order(identifier, pending, done, (), ledger, verbose)
    _restate_from_proved(ledger, oracle, verbose)


def _check_in_order(
    identifier: str,
    pending: dict[str, Any],
    done: set[str],
    path: tuple[str, ...],
    ledger: Ledger,
    verbose: bool,
) -> None:
    """Check one theorem's written proof after the theorems it cites (see the caller)."""
    if identifier in done:
        return
    theorem = pending[identifier]
    fact = ledger[identifier]
    started = time.monotonic()
    proof: Proof | None = None
    try:
        proof = trace_proof(theorem)
    except ProofError:
        proof = None
    except Exception:  # noqa: BLE001 - prove() says what the trace raised, at its line
        proof = None
    if proof is not None:
        for cited in proof.cited:
            cited_id = getattr(cited, "fact_id", None)
            if cited_id is None:
                continue
            if cited_id in pending and cited_id not in done:
                if cited_id in path or cited_id == identifier:
                    # every proof on the circle is refused, not only the one
                    # that closes it (Codex, #171): each would rest on another
                    # whose proof rests on it
                    circle = (*path, identifier)
                    circle = circle[circle.index(cited_id) :]
                    names = " -> ".join(pending[item].__name__ for item in (*circle, cited_id))
                    for item in circle:
                        done.add(item)
                        ledger.add(
                            _failed(
                                ledger[item],
                                _where(pending[item]),
                                None,
                                [
                                    Failure(
                                        "cite",
                                        None,
                                        "the proofs cite each other in a circle",
                                        (f"The proofs cite each other in a circle: {names}.",),
                                        "prove one of them without the other",
                                    )
                                ],
                                pending[item].path,
                            )
                        )
                    return
                _check_in_order(cited_id, pending, done, (*path, identifier), ledger, verbose)
                if identifier in done:
                    # refused as part of a circle the check above found
                    return
            elif cited_id not in ledger:
                _establish_foreign(cited, ledger, verbose)
    done.add(identifier)
    fact = ledger[identifier]
    try:
        checked = prove(theorem, fact, traced=proof)
    except Exception as exc:  # noqa: BLE001 - lanky's own failure is no verdict on the proof
        if verbose:
            import traceback

            traceback.print_exc()
        checked = _not_checked(
            fact,
            _where(theorem),
            f"lanky raised {type(exc).__name__} while it checked the proof: {exc} "
            "(--verbose prints where)",
        )
    ledger.add(checked)
    if verbose:
        said = checked.provenance.get("proof") or {}
        state = {True: "Lean accepted it", False: "it fails"}.get(
            said.get("closed"), f"not checked: {said.get('reason')}"
        )
        if said.get("closed") == "holes":
            state = "Lean accepted it, with steps left open"
        print(
            f"  its proof, {said.get('where')}: {said.get('summary') or ''}"
            f"{'; ' if said.get('summary') else ''}{state} "
            f"({time.monotonic() - started:.1f} s)"
        )


def _establish_foreign(theorem: Any, ledger: Ledger, verbose: bool) -> None:
    """Establish a theorem of another module into ``ledger``, as rows marked with its module.

    A proof's citation rests on the cited theorem, and a ledger counts an id
    it does not hold as assumed, so the theorem is established here, with
    its reading, as the file that states it would establish it, warm from
    the proof cache. Its rows say where it is from, ``lanky.known``.
    """
    from lanky.check import establish
    from lanky.plugins import registry

    module = getattr(theorem, "module", None) or ""
    for theory in registry.theories:
        for fact in theory.facts(theorem):
            if fact.id in ledger:
                continue
            if verbose:
                print(f"{module} {fact.owner}: {fact.statement} (cited from {module})")
            established = establish(fact, verbose=verbose)
            marked = established.with_status(established.status, module=module)
            ledger.add(replace(marked, where=module or marked.where))


def _restate_from_proved(ledger: Ledger, oracle: Any, verbose: bool) -> None:
    """Ask Lean again about each plugin fact restated by the printer where a proved text now exists.

    A part that cites a theorem restates the text its command proved
    (:mod:`lanky.citations`); a theorem proved only by its written proof has
    that text only once its proof is checked, after the plugin's facts were
    established, so their parts restated it by the printer. Each such fact is
    offered to the Lean oracle again, and its new answer is kept where it is
    at least as strong.
    """
    if oracle is None or getattr(oracle, "proved_texts", None) is None:
        return
    from lanky.check import _rest_on_the_reading

    for fact in list(ledger):
        printed = fact.provenance.get("lean_restated_by_printer")
        if not printed or not callable(getattr(fact.term, "lean_obligation", None)):
            continue
        cited = {
            note.get("fact")
            for record in fact.provenance.get("lean_parts") or ()
            if isinstance(record, dict)
            for note in record.get("cited", ())
            if note.get("restated") == "by the printer"
        }
        if not any(identifier in oracle.proved_texts for identifier in cited if identifier):
            continue
        if verbose:
            print(f"  {fact.owner}: {fact.statement} (asked again, from the texts proved since)")
        try:
            again = oracle.establish(fact)
        except Exception:  # noqa: BLE001 - the answer it had stands
            continue
        if again is None or again.status is Status.ASSUMED:
            continue
        if again.status in (Status.PROVED, Status.CERTIFIED) or fact.status is Status.ASSUMED:
            again = again.with_status(again.status, trust_class=oracle.trust_class())
            still = {
                note.get("theorem")
                for record in again.provenance.get("lean_parts") or ()
                if isinstance(record, dict)
                for note in record.get("cited", ())
                if note.get("restated") == "by the printer"
            }
            provenance = dict(again.provenance)
            if still:
                provenance["lean_restated_by_printer"] = sorted(str(name) for name in still)
            else:
                provenance.pop("lean_restated_by_printer", None)
            ledger.add(_rest_on_the_reading(replace(again, provenance=provenance)))


def _lean_oracle() -> Any:
    """The registered Lean oracle, or ``None``."""
    from lanky.oracles.lean import LeanOracle
    from lanky.plugins import registry

    return next((oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)), None)


def prove(theorem: Any, fact: Fact, traced: Proof | None = None) -> Fact:
    """``fact``, with what checking the theorem's written proof says (see the module).

    The proof's account is the provenance entry ``proof``: ``where`` it is
    written, a ``summary`` of it, whether Lean accepted it (``closed``:
    ``True``, ``"holes"`` for a proof accepted with steps left open,
    ``False``, or ``None`` when it was not checked, with the ``reason``), the
    ``failures`` when it was not accepted, each a dict of ``kind``, ``line``,
    ``headline``, ``lines``, ``fix``, ``source`` and ``where``, the
    ``holes``, the ``outline`` ``--steps`` prints, and the ``lean_source``.
    ``traced`` is the proof traced already, if it was.
    """
    if written_lines(theorem.fn) is None:
        return fact
    where = _where(theorem)
    if fact.status is Status.REFUTED or fact.provenance.get("unfaithful"):
        why = (
            "the claim is refuted"
            if fact.status is Status.REFUTED
            else ("its term is not what the annotations compute")
        )
        return _not_checked(fact, where, why)
    try:
        proof = traced if traced is not None else trace_proof(theorem)
    except ProofError as exc:
        return _failed(fact, where, None, [failure_of(exc)], theorem.path)
    oracle = _lean_oracle()
    if oracle is None:
        return _without_lean(fact, where, proof, "Lean", "no Lean oracle is registered")
    available, reason = oracle.availability()
    if not available:
        return _without_lean(fact, where, proof, "Lean", f"Lean is not available here ({reason})")
    mathlib = oracle.session.mathlib is not None
    from lanky.lean import UnsupportedTerm
    from lanky.oracles.lean import claim_statement

    try:
        as_cited = claim_statement(fact, mathlib).as_cited
    except UnsupportedTerm:
        as_cited = None
    try:
        command = compile_proof(proof, mathlib, as_cited)
    except UnsupportedTerm as exc:
        if not mathlib:
            return _without_lean(
                fact,
                where,
                proof,
                "Mathlib",
                "only Lean with Mathlib can state it (LANKY_LEAN_MATHLIB)",
            )
        return _not_checked(fact, where, f"Lean cannot state it: {exc}")
    except ProofError as exc:
        if exc.kind == "unsupported" and not mathlib:
            # a theorem it cites, a step's term or a point is about the reals,
            # which core Lean has no words for: not a fault of the proof
            return _without_lean(
                fact,
                where,
                proof,
                "Mathlib",
                "only Lean with Mathlib can state it (LANKY_LEAN_MATHLIB)",
            )
        return _failed(fact, where, None, [failure_of(exc)], theorem.path)
    texts = getattr(oracle, "proved_texts", None)
    mismatch = texts.mismatch(command.restated) if texts is not None else ""
    if mismatch:
        # compared before Lean is asked, and before the proof cache is read:
        # a warm check too restates only what the cited theorem's command proved
        failure = Failure(
            "cite",
            None,
            "a theorem its proof cites is restated other than as Lean proved it",
            (f"{mismatch[0].upper()}{mismatch[1:]}.",),
            "check the file again, so that the cited theorem's text is proved anew",
        )
        return _failed(fact, where, command, [failure], theorem.path)
    record, said, _cached = oracle.written(command.source, fact)
    if record is None:
        if said.startswith("TimeoutError") or "budget" in said:
            failure = Failure(
                "time",
                None,
                "Lean gave up on the proof after its share of the budget",
                (),
                "split a step in two, or cite the facts it needs",
            )
            return _failed(fact, where, command, [failure], theorem.path)
        return _not_checked(fact, where, said or "Lean did not answer")
    said_verdict, failures = verdict(proof, command, record)
    if said_verdict in ("closed", CLOSED_WITH_HOLES):
        inconsistent = _inconsistent_citations(fact, proof, mathlib)
        if inconsistent is not None:
            return _failed(fact, where, command, [inconsistent], theorem.path)
    if said_verdict == "closed":
        return _closed(fact, where, proof, command, oracle)
    if said_verdict == CLOSED_WITH_HOLES:
        return _holes(fact, where, proof, command)
    failures = [_checked_fix(failure, proof, command, oracle, fact) for failure in failures]
    return _failed(fact, where, command, failures, theorem.path)


def _inconsistent_citations(fact: Fact, proof: Proof, mathlib: bool) -> Failure | None:
    """Whether the theorems the proof cites without a proved text prove ``False`` together.

    A citation of a theorem whose own command proved no text (an axiom, a
    claim only tested, one whose Lean attempt failed) restates the statement
    the printer gives, and a printer that dropped a condition would let the
    proof prove anything: the design's T4, ``log_of_a_power`` without ``n >=
    0``, proves ``1 = 0``. So the oracles stronger than a heuristic are asked
    whether those statements prove ``False``, as a claim's hypotheses are
    (:func:`lanky.citations.vacuity_question`), taken where the proof takes
    them: once at the points that are numbers, and once for each case of the
    proof that takes them at points with variables, the claim's ``(a - 2,
    b)`` inside an induction, those variables bound and the case's
    conditions assumed, where some values satisfy the conditions
    (:func:`lanky.citations.satisfiable`). Where one shows they do, the proof
    fails, naming them. ``None`` where every citation is by a proved text, or
    none of them is shown inconsistent.
    """
    from lanky.check import _stronger_than_a_heuristic
    from lanky.citations import proved_text

    theorems = list(proof.cited)
    printed = [
        theorem
        for theorem in theorems
        if getattr(theorem, "term", None) is not None
        and proved_text(getattr(theorem, "fact_id", None), theorem.term) is None
    ]
    if not printed:
        return None
    found = None
    line: int | None = None
    for question, where in _vacuity_questions(fact, proof, theorems, mathlib):
        found = _stronger_than_a_heuristic(question)
        if found is not None:
            line = where
            break
    if found is None:
        return None
    oracle, result = found
    names = [theorem.__name__ for theorem in printed]
    said = names[0] if len(names) == 1 else f"{', '.join(names[:-1])} and {names[-1]}"
    one = len(names) == 1
    if line is None:
        line = next(
            (
                citation.line
                for leaf in proof.leaves
                for citation in leaf.citations
                if citation.name in names and citation.line is not None
            ),
            None,
        )
    return Failure(
        "cite",
        line,
        f"the {'theorem' if one else 'theorems'} its proof cites without a proved text "
        f"{'proves' if one else 'prove'} False",
        (
            f"{said}, as lanky states {'it' if one else 'them'} for Lean, "
            f"{'proves' if one else 'prove'} False ({result.status.value} by {oracle}): "
            f"a proof that cites {'it' if one else 'them'} could prove anything.",
        ),
        f"prove {said} first, so that a citation restates what Lean proved, or correct "
        f"{'its statement' if one else 'their statements'}",
    )


def _vacuity_questions(
    fact: Fact, proof: Proof, theorems: list[Any], mathlib: bool
) -> list[tuple[Fact, int | None]]:
    """The vacuity questions of a proof's printed citations, each with the line it is about.

    The first takes the theorems at the points that are numbers, or at none.
    Then one for each case whose citations are at points with variables, as
    :func:`_inconsistent_citations` says: the variables the points and the
    case's conditions mention are bound, with the sorts the proof gives them,
    and the conditions are its hypotheses after the texts. A case whose
    points or conditions cannot be stated, or for which no values satisfying
    its conditions are found, is not asked.
    """
    import os

    from lanky.citations import satisfiable, vacuity_question
    from lanky.matching import FamilyValue
    from lanky.terms import Forall, conjuncts, free_variables

    numbers = [
        (citation.source.fact_id, citation.values)
        for leaf in proof.leaves
        for citation in leaf.citations
        if getattr(citation.source, "fact_id", None) is not None
        and citation.values is not None
        and all(_a_number(value) for value in citation.values)
    ]
    out: list[tuple[Fact, int | None]] = []
    first = vacuity_question(fact.owner, theorems, fact.where, numbers, mathlib)
    if first is not None:
        out.append((first, None))
    theorem = proof.theorem
    sorts: dict[str, Any] = dict(theorem.variables)
    goal = theorem.goal
    guards: list[Any] = []
    if isinstance(goal, Forall):
        guards = list(conjuncts(goal.guard))
        for var, domain in goal.binders:
            sorts.setdefault(var.name, domain)
    if proof.claim is not None:
        sorts.update(zip(proof.claim.params, proof.claim.domains, strict=True))
    base = os.path.basename(proof.path)
    seen: set[int] = set()
    for leaf in proof.leaves:
        points = [
            (citation.source.fact_id, citation.values)
            for citation in leaf.citations
            if getattr(citation.source, "fact_id", None) is not None
            and citation.values is not None
            and not all(_a_number(value) for value in citation.values)
            and not any(isinstance(value, FamilyValue) for value in citation.values)
        ]
        if not points or id(leaf) in seen:
            continue
        seen.add(id(leaf))
        conditions = [*guards, *(condition for condition, _line in leaf.conditions)]
        try:
            needed: set[str] = set()
            for _fact_id, values in points:
                for value in values:
                    if hasattr(value, "mapper_method"):
                        needed |= set(free_variables(value))
            for condition in conditions:
                needed |= set(free_variables(condition))
        except Exception:  # noqa: BLE001 - what cannot be read is not asked
            continue
        names = _closed_under_sorts(needed, sorts)
        if names is None:
            continue
        variables = [(Var(name), sorts[name]) for name in sorts if name in names]
        if not satisfiable(variables, conditions):
            continue
        case = f"in the case at {base}:{leaf.line}" if leaf.line is not None else "in a case"
        question = vacuity_question(
            fact.owner,
            theorems,
            fact.where,
            points,
            mathlib,
            variables=variables,
            conditions=conditions,
            case=case,
        )
        if question is not None:
            out.append((question, leaf.line))
    return out


def _a_number(value: Any) -> bool:
    """Whether a point's value is a number, which a question can take a citation at."""
    import numbers

    return isinstance(value, numbers.Number) and not isinstance(value, bool)


def _closed_under_sorts(needed: set[str], sorts: dict[str, Any]) -> set[str] | None:
    """``needed`` with every name a sort of one of them mentions, ``Fin[n]``'s ``n``; or ``None``.

    ``None`` where a name has no sort the proof gives it, so the question
    cannot bind it.
    """
    from lanky.prelude import FinType, FnType, Refined
    from lanky.terms import free_variables

    names: set[str] = set()
    stack = list(needed)
    while stack:
        name = stack.pop()
        if name in names:
            continue
        if name not in sorts:
            return None
        names.add(name)
        pending = [sorts[name]]
        while pending:
            sort = pending.pop()
            if isinstance(sort, Refined):
                pending.append(sort.base)
            elif isinstance(sort, FinType):
                bound = sort.bound
                if hasattr(bound, "mapper_method"):
                    stack.extend(free_variables(bound))
            elif isinstance(sort, FnType):
                pending.extend((sort.domain, sort.codomain))
    return names


def _where(theorem: Any) -> str:
    """``file.py:41-48``: where a theorem's written proof is."""
    from os.path import basename

    lines = written_lines(theorem.fn)
    if lines is None:
        return basename(theorem.path)
    first, last = lines
    span = f"{first}-{last}" if last != first else f"{first}"
    return f"{basename(theorem.path)}:{span}"


def _source(command: Command) -> str:
    """The file that replays the proof: the command, after ``import Mathlib`` where it needs it."""
    return f"import Mathlib\n\n{command.source}" if command.mathlib else command.source


def _closed(fact: Fact, where: str, proof: Proof, command: Command, oracle: Any) -> Fact:
    """``fact`` proved by its written proof: the line the ledger adds, and the Lean that replays it.

    A claim lanky proved alone keeps its row, with the line added. One it did
    not is proved now, by Lean, resting on its reading as any proof does, and
    on the theorems the proof cites, their premises included. The command
    proved the claim's ``as_cited`` text too, which the Lean oracle keeps for
    the proofs and the parts that cite this theorem (:mod:`lanky.citations`).
    """
    from lanky.check import _rest_on_the_reading

    account = {
        "where": where,
        "summary": command.summary,
        "closed": True,
        "lean_source": _source(command),
        "outline": [list(row) for row in command.outline],
    }
    cited = tuple(command.rests_on)
    rests_on = tuple(dict.fromkeys((*fact.rests_on, *cited)))
    extra: dict[str, Any] = {}
    if command.as_cited is not None and fact.term is not None:
        from lanky.citations import Proved

        kept = oracle.proved_texts.record(
            Proved(
                fact.id,
                command.declared,
                command.as_cited,
                command.mathlib,
                fact.term,
                cited,
                source=command.source,
            )
        )
        if kept:
            extra["lean_as_cited"] = command.as_cited
    if fact.status in (Status.PROVED, Status.CERTIFIED):
        return replace(fact.with_status(fact.status, proof=account, **extra), rests_on=rests_on)
    session = oracle.session
    if command.mathlib:
        extra["lean_mathlib"] = session.mathlib_revision
    proved = fact.with_status(
        Status.PROVED,
        oracle.name,
        proof=account,
        tactic="its written proof",
        lean_source=_source(command),
        lean_version=session.version,
        trust_class=oracle.trust_class(),
        **extra,
    )
    return _rest_on_the_reading(replace(proved, rests_on=rests_on))


def _holes(fact: Fact, where: str, proof: Proof, command: Command) -> Fact:
    """``fact`` as it was, with a proof Lean accepted but for the steps it left open, ``by=...``.

    The claim is not proved by it: it reads as the other oracles left it,
    assumed where none settled it, and its row names the lines left open.
    """
    import os

    base = os.path.basename(proof.path)
    account = {
        "where": where,
        "summary": command.summary,
        "closed": "holes",
        "holes": [f"{base}:{line}" for line in command.holes],
        "lean_source": _source(command),
        "outline": [list(row) for row in command.outline],
    }
    return fact.with_status(fact.status, proof=account)


def _without_lean(fact: Fact, where: str, proof: Proof, missing: str, reason: str) -> Fact:
    """``fact``, its written proof not checked by Lean: each link of its chains drawn instead.

    Where the values can be drawn, each link's two sides are compared at
    drawn points, under the theorem's hypotheses and the case's conditions,
    so that a wrong step is caught at its own line with no Lean at all, and
    fails the check. A link over a family that cannot be drawn, a table over
    ``Nat``, leaves the proof unchecked, and says why.

    ``missing`` is what the machine lacks, ``Lean`` or ``Mathlib``, and the
    ``NOT CHECKED`` line says it in a clause, since the ``WITHOUT LEAN`` and
    ``WITHOUT MATHLIB`` lines above it say why and how to get it::

        NOT CHECKED harmonic at sumpy_recurrence.py:151: without Lean, each step
        of its proof was tested at drawn points instead (lines 161 and 162).

    ``reason`` is the long form, kept for ``--verbose`` and ``--json``.
    """
    draws = _draw_links(proof)
    if not draws:
        return _not_checked(fact, where, reason, f"without {missing}, its proof was not checked")
    for line, statement, outcome, detail in draws:
        if outcome == "refuted":
            failure = Failure(
                "false",
                line,
                "a step of its proof is false",
                (f"The step says {statement}, which is false {detail}.",),
                None,
            )
            return _failed(fact, where, None, [failure], proof.path)
    undrawn = [detail for _line, _statement, outcome, detail in draws if outcome == "undrawn"]
    if undrawn:
        return _not_checked(
            fact,
            where,
            f"{reason}; its steps could not be drawn: {undrawn[0]}",
            f"without {missing}, its proof was not checked, and its steps cannot be drawn "
            f"({_short(undrawn[0])})",
        )
    lines = sorted({line for line, *_ in draws if line is not None})
    return _not_checked(
        fact,
        where,
        f"{reason}; the proof of {proof.theorem.__name__} was tested step by step at drawn "
        f"points ({', '.join(str(line) for line in lines)}), not checked by Lean",
        f"without {missing}, each step of its proof was tested at drawn points instead"
        + (f" ({_lines(lines)})" if lines else ""),
    )


def _lines(lines: list[int]) -> str:
    """``line 161``, ``lines 161 and 162``, ``lines 161, 162 and 165``."""
    shown = [str(line) for line in lines]
    if len(shown) == 1:
        return f"line {shown[0]}"
    return f"lines {', '.join(shown[:-1])} and {shown[-1]}"


def _short(detail: str) -> str:
    """Why a draw could not be made, in its last clause: ``cannot tabulate a family over Nat``."""
    return detail.rsplit(": ", 1)[-1].rstrip(".")


def _draw_links(proof: Proof, samples: int = 50) -> list[tuple[int | None, str, str, str]]:
    """Each link of the proof's chains, drawn: ``(line, statement, outcome, detail)``.

    Each link is a claim over the theorem's variables and the claim's, drawn
    as a claim is (:func:`lanky.testing.check`), under the theorem's
    hypotheses, the goal's guard and the case's conditions.
    """
    from lanky.terms import Comparison, Forall, conjuncts, render
    from lanky.testing import OpenStatement, check

    theorem = proof.theorem
    variables = list(theorem.variables)
    goal = theorem.goal
    guards: list[Any] = []
    if proof.claim is not None:
        names = {name for name, _ in variables}
        for name, domain in zip(proof.claim.params, proof.claim.domains, strict=True):
            if name not in names:
                variables.append((name, domain))
        if isinstance(goal, Forall):
            guards = list(conjuncts(goal.guard))
    hypotheses = [part for _name, prop in theorem.hypotheses for part in conjuncts(prop)]
    out: list[tuple[int | None, str, str, str]] = []
    seen: set[int] = set()
    for leaf in proof.leaves:
        conditions = [condition for condition, _line in leaf.conditions]
        chains = (*leaf.named, *((leaf.chain,) if leaf.chain is not None else ()))
        for chain in chains:
            if id(chain) in seen:
                continue
            seen.add(id(chain))
            for left, link in chain.steps():
                prop = Comparison(left, link.relation, link.term)
                statement = render(prop)
                try:
                    report = check(variables, [*hypotheses, *guards, *conditions], prop, samples, 0)
                except OpenStatement as exc:
                    out.append((link.line, statement, "undrawn", str(exc)))
                    continue
                except Exception as exc:  # noqa: BLE001 - a draw that cannot run checks nothing
                    out.append((link.line, statement, "undrawn", f"{type(exc).__name__}: {exc}"))
                    continue
                if report.counterexample is not None:
                    point = ", ".join(
                        f"{key} = {value}" for key, value in report.counterexample.items()
                    )
                    out.append((link.line, statement, "refuted", f"at {point}"))
                elif report.valid == 0:
                    out.append((link.line, statement, "undrawn", report.reason or "no draw"))
                else:
                    out.append((link.line, statement, "tested", f"{report.valid} draws"))
    return out


def _failed(
    fact: Fact, where: str, command: Command | None, failures: list[Failure], path: str
) -> Fact:
    """``fact`` as it was, with the failures of its written proof; ``lanky check`` fails on them."""
    account: dict[str, Any] = {
        "where": where,
        "summary": command.summary if command is not None else "",
        "closed": False,
        "failures": [failure.to_dict(path) for failure in failures],
    }
    if command is not None:
        account["lean_source"] = _source(command)
    return fact.with_status(fact.status, proof=account)


def _not_checked(fact: Fact, where: str, reason: str, said: str | None = None) -> Fact:
    """``fact`` as it was, with why its written proof was not checked.

    ``said`` is the clause the ``NOT CHECKED`` line prints in place of ``its
    proof, file.py:41-48, was not checked: <reason>``, where a shorter one
    says it (:func:`_without_lean`).
    """
    account: dict[str, Any] = {"where": where, "closed": None, "reason": reason}
    if said is not None:
        account["said"] = said
    return fact.with_status(fact.status, proof=account)


def _checked_fix(
    failure: Failure, proof: Proof, command: Command, oracle: Any, fact: Fact
) -> Failure:
    """A step's fix, confirmed by Lean where it can be: ``(checked)`` after the fix when it is.

    The fix is the step's fact at another point (:func:`lanky.proofs.report.fix_for`),
    or one more fact cited (:func:`lanky.proofs.report.also_needs`), and the
    proof with it is compiled and asked of Lean, as the proof was.
    """
    if failure.kind != "step" or failure.fix is None:
        return failure
    step = next((step for step in command.steps if step.where == failure.line), None)
    if step is None:
        return failure
    repair = failure.repair
    if repair is None:
        found = fix_for(step, proof, command.measure)
        if found is None:
            return failure
        repair = ("point", *found)
    if repair[0] == "add":
        fixed = _with_added(proof, step, repair[1])
        if fixed is None:
            return failure
    else:
        _kind, index, citation = repair
        old = step.instances[index].citation
        fixed = _with_citation(proof, step.leaf, old, citation)
    try:
        again = compile_proof(fixed, command.mathlib)
    except Exception:  # noqa: BLE001 - a fix that does not compile is not checked
        return failure
    record, _said, _cached = oracle.written(again.source, fact)
    if record is None:
        return failure
    closed, failures = read(fixed, again, record)
    if closed or all(other.line != failure.line for other in failures):
        return replace(failure, fix=f"{failure.fix} (checked)")
    return failure


def _with_added(proof: Proof, step: Any, new: Citation) -> Proof | None:
    """``proof`` with one more fact cited at one step: in its link of a chain, or in its return.

    ``None`` for a link of a fact on the way, whose chain the citations of it
    name, and which is kept as it is.
    """
    leaf = step.leaf
    if step.line is not None and any(
        link.line == step.line for chain in leaf.named for link in chain.links
    ):
        return None
    in_the_chain = (
        step.line is not None
        and leaf.chain is not None
        and any(link.line == step.line for link in leaf.chain.links)
    )
    leaves = []
    for each in proof.leaves:
        if each is leaf:
            if in_the_chain:
                links = tuple(
                    replace(link, facts=(*link.facts, new)) if link.line == step.line else link
                    for link in each.chain.links
                )
                each = replace(each, chain=replace(each.chain, links=links))
            else:
                each = replace(each, facts=(*(each.facts or ()), new))
        leaves.append(each)
    return replace(proof, leaves=tuple(leaves), root=_tree(leaves))


def _with_citation(proof: Proof, leaf: Any, old: Citation, new: Citation) -> Proof:
    """``proof`` with one citation of one leaf put at another point, in a return or a link."""

    def swapped(citations: Any) -> tuple[Citation, ...]:
        return tuple(new if citation is old else citation for citation in citations)

    def chain_with(chain: Any) -> Any:
        if chain is None:
            return None
        links = tuple(replace(link, facts=swapped(link.facts)) for link in chain.links)
        return replace(chain, links=links)

    leaves = []
    for each in proof.leaves:
        if each is leaf:
            facts = None if each.facts is None else swapped(each.facts)
            # a fact on the way keeps its chain, which the citations of it name
            each = replace(each, facts=facts, chain=chain_with(each.chain))
        leaves.append(each)
    return replace(proof, leaves=tuple(leaves), root=_tree(leaves))
