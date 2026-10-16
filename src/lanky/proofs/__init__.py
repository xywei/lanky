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

from lanky.ledger import Fact, Ledger, Status
from lanky.proofs.compile import Command, compile_proof
from lanky.proofs.report import Failure, failure_of, fix_for, read
from lanky.proofs.trace import (
    Citation,
    Proof,
    ProofError,
    _tree,
    trace_proof,
    written_lines,
)

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
    """
    from lanky.theory import Axiom, Theorem

    for obj in objects:
        if not isinstance(obj, Theorem) or isinstance(obj, Axiom):
            continue
        if obj.fact_id not in ledger or written_lines(obj.fn) is None:
            continue
        fact = ledger[obj.fact_id]
        started = time.monotonic()
        checked = prove(obj, fact)
        ledger.add(checked)
        if verbose:
            said = checked.provenance.get("proof") or {}
            state = {True: "Lean accepted it", False: "it fails"}.get(
                said.get("closed"), f"not checked: {said.get('reason')}"
            )
            print(
                f"  its proof, {said.get('where')}: {said.get('summary') or ''}"
                f"{'; ' if said.get('summary') else ''}{state} "
                f"({time.monotonic() - started:.1f} s)"
            )


def _lean_oracle() -> Any:
    """The registered Lean oracle, or ``None``."""
    from lanky.oracles.lean import LeanOracle
    from lanky.plugins import registry

    return next((oracle for oracle in registry.oracles if isinstance(oracle, LeanOracle)), None)


def prove(theorem: Any, fact: Fact) -> Fact:
    """``fact``, with what checking the theorem's written proof says (see the module).

    The proof's account is the provenance entry ``proof``: ``where`` it is
    written, a ``summary`` of it, whether Lean accepted it (``closed``:
    ``True``, ``False``, or ``None`` when it was not checked, with the
    ``reason``), the ``failures`` when it was not accepted, each a dict of
    ``kind``, ``line``, ``headline``, ``lines``, ``fix``, ``source`` and
    ``where``, and the ``lean_source``.
    """
    lines = written_lines(theorem.fn)
    if lines is None:
        return fact
    from os.path import basename

    first, last = lines
    span = f"{first}-{last}" if last != first else f"{first}"
    where = f"{basename(theorem.path)}:{span}"
    if fact.status is Status.REFUTED or fact.provenance.get("unfaithful"):
        why = (
            "the claim is refuted"
            if fact.status is Status.REFUTED
            else ("its term is not what the annotations compute")
        )
        return _not_checked(fact, where, why)
    try:
        proof = trace_proof(theorem)
    except ProofError as exc:
        return _failed(fact, where, None, [failure_of(exc)], theorem.path)
    oracle = _lean_oracle()
    if oracle is None:
        return _not_checked(fact, where, "no Lean oracle is registered")
    available, reason = oracle.availability()
    if not available:
        return _not_checked(fact, where, f"Lean is not available here ({reason})")
    mathlib = oracle.session.mathlib is not None
    from lanky.lean import UnsupportedTerm

    try:
        command = compile_proof(proof, mathlib)
    except UnsupportedTerm as exc:
        if not mathlib:
            return _not_checked(
                fact, where, "only Lean with Mathlib can state it (LANKY_LEAN_MATHLIB)"
            )
        return _not_checked(fact, where, f"Lean cannot state it: {exc}")
    except ProofError as exc:
        return _failed(fact, where, None, [failure_of(exc)], theorem.path)
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
    closed, failures = read(proof, command, record)
    if closed:
        return _closed(fact, where, proof, command, oracle)
    failures = [_checked_fix(failure, proof, command, oracle, fact) for failure in failures]
    return _failed(fact, where, command, failures, theorem.path)


def _source(command: Command) -> str:
    """The file that replays the proof: the command, after ``import Mathlib`` where it needs it."""
    return f"import Mathlib\n\n{command.source}" if command.mathlib else command.source


def _closed(fact: Fact, where: str, proof: Proof, command: Command, oracle: Any) -> Fact:
    """``fact`` proved by its written proof: the line the ledger adds, and the Lean that replays it.

    A claim lanky proved alone keeps its row, with the line added. One it did
    not is proved now, by Lean, resting on its reading as any proof does, and
    on the theorems the proof cites.
    """
    from lanky.check import _rest_on_the_reading

    account = {
        "where": where,
        "summary": command.summary,
        "closed": True,
        "lean_source": _source(command),
    }
    cited = tuple(theorem.fact_id for theorem in command.cited)
    rests_on = tuple(dict.fromkeys((*fact.rests_on, *cited)))
    if fact.status in (Status.PROVED, Status.CERTIFIED):
        return replace(fact.with_status(fact.status, proof=account), rests_on=rests_on)
    session = oracle.session
    extra: dict[str, Any] = {}
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


def _not_checked(fact: Fact, where: str, reason: str) -> Fact:
    """``fact`` as it was, with why its written proof was not checked."""
    return fact.with_status(fact.status, proof={"where": where, "closed": None, "reason": reason})


def _checked_fix(
    failure: Failure, proof: Proof, command: Command, oracle: Any, fact: Fact
) -> Failure:
    """A step's fix, confirmed by Lean where it can be: ``(checked)`` after the fix when it is.

    The fix is the step's fact at another point (:func:`lanky.proofs.report.fix_for`),
    and the proof with it is compiled and asked of Lean, as the proof was.
    """
    if failure.kind != "step" or failure.fix is None:
        return failure
    step = next((step for step in command.steps if step.leaf.line == failure.line), None)
    if step is None:
        return failure
    found = fix_for(step, proof)
    if found is None:
        return failure
    index, citation = found
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


def _with_citation(proof: Proof, leaf: Any, old: Citation, new: Citation) -> Proof:
    """``proof`` with one citation of one leaf put at another point."""
    leaves = []
    for each in proof.leaves:
        if each is leaf:
            facts = tuple(new if citation is old else citation for citation in each.facts or ())
            each = replace(each, facts=facts)
        leaves.append(each)
    return replace(proof, leaves=tuple(leaves), root=_tree(leaves))
