"""The ledger of facts.

The design idea. Everything lanky knows is a :class:`Fact`: a statement, a
status saying how strongly it is established, and who established it. A theorem
is a fact. A side condition a decision procedure discharged is a fact. An
obligation nobody could establish is a fact too, with status ``ASSUMED``, which
is the point: an unproved obligation is recorded rather than lost.

The statuses are ordered by the strength of the evidence, from a property test
through a decision procedure and a proof to a rechecked certificate, plus two
that are not on that ladder: ``ASSUMED`` (nobody tried, or nobody could) and
``REFUTED`` (someone found a counterexample, which is knowledge as definite as a
proof, and the counterexample lives in the fact's provenance).

One mark sits beside the status rather than in it. A fact whose hypotheses an
oracle has shown inconsistent is *vacuous*: ``proved`` is still true of it, and
it says nothing, so the table prints ``proved (vacuous)`` and the provenance
says who showed it (see :func:`lanky.check.establish`).
"""

from __future__ import annotations

import enum
import json
import os
from dataclasses import dataclass, field, replace
from typing import Any

__all__ = ["Fact", "Ledger", "Status", "fact_id"]


def fact_id(
    kind: str,
    owner: str,
    module: str | None = None,
    line: int | None = None,
    detail: str = "",
) -> str:
    """Build a fact id that names a definition rather than only a name.

    A ledger is keyed by id (see :meth:`Ledger.add`), so two claims that share
    an id are one claim and the later one silently replaces the earlier. A
    qualified name alone is not enough to tell two definitions apart: two
    modules checked together may each have a ``scan_monotone``, and a decorator
    used twice in one module gives the same qualified name twice. The module
    name and the definition's line make the id unique per definition, and both
    are short enough to keep it readable; the ledger's table shows ``where`` and
    ``owner`` in their own columns, so the id itself is free to be long.

    The shape is ``kind:module.owner@line:detail``, with any part that is not
    known left out. ``detail`` is for a theory that claims several facts about
    one object, such as one obligation per array access.
    """
    name = f"{module}.{owner}" if module else owner
    at = f"@{line}" if line is not None else ""
    suffix = f":{detail}" if detail else ""
    return f"{kind}:{name}{at}{suffix}"


class Status(enum.Enum):
    """How strongly a :class:`Fact` is established.

    ``TESTED``
        The statement survived execution as a property test. Evidence, not proof.
    ``DECIDED``
        A decision procedure (isl, an SMT solver, Lean's ``decide``) answered
        affirmatively, trusted at that oracle's trust class.
    ``PROVED``
        A proof was found and accepted by the platform, but no reproducible
        artifact was retained.
    ``CERTIFIED``
        A proof was found and a certificate was recorded, so the claim can be
        rechecked independently of lanky.
    ``ASSUMED``
        Taken on faith: an axiom, or an obligation no oracle could establish.
        Tracked so it can never be silently lost.
    ``REFUTED``
        Shown false. The witness is in ``provenance``.
    """

    TESTED = "tested"
    DECIDED = "decided"
    PROVED = "proved"
    CERTIFIED = "certified"
    ASSUMED = "assumed"
    REFUTED = "refuted"


#: How much evidence each status represents; ``REFUTED`` is off the ladder.
STATUS_STRENGTH: dict[Status, int] = {
    Status.REFUTED: -1,
    Status.ASSUMED: 0,
    Status.TESTED: 1,
    Status.DECIDED: 2,
    Status.PROVED: 3,
    Status.CERTIFIED: 4,
}


@dataclass(frozen=True)
class Fact:
    """A single entry in the ledger.

    Attributes:
        id: Stable identifier, unique within one ledger. Re-adding the same id
            replaces the entry, which is how an oracle upgrades a fact.
        kind: What sort of claim this is, such as ``"theorem"``, ``"in-bounds"``
            or ``"cast"``. The theory that made the fact chooses the vocabulary.
        statement: The claim rendered as source text, for people to read.
        term: The claim as a term, for oracles to work on. ``None`` when the
            claim has no term form yet.
        status: How strongly the claim is established.
        decided_by: Name of the oracle that established it, or ``None``.
        provenance: How it was checked: tactic script, counterexample, witness
            instances, oracle version, timings. Deliberately untyped.
        where: Source location as ``file:line``.
        owner: Qualified name of the decorated object the claim belongs to.
    """

    id: str
    kind: str
    statement: str
    term: object | None = None
    status: Status = Status.ASSUMED
    decided_by: str | None = None
    provenance: dict = field(default_factory=dict)
    where: str = ""
    owner: str = ""

    @property
    def is_vacuous(self) -> bool:
        """Whether an oracle has shown that nothing satisfies this fact's hypotheses."""
        return bool(self.provenance.get("vacuous"))

    def with_status(
        self,
        status: Status,
        decided_by: str | None = None,
        **provenance: Any,
    ) -> Fact:
        """A copy of this fact with a new status and merged provenance."""
        return replace(
            self,
            status=status,
            decided_by=decided_by if decided_by is not None else self.decided_by,
            provenance={**self.provenance, **provenance},
        )

    def to_dict(self) -> dict:
        """A JSON-ready dictionary; the term is rendered to text."""
        from lanky.terms import render

        return {
            "id": self.id,
            "kind": self.kind,
            "statement": self.statement,
            "term": None if self.term is None else render(self.term),
            "status": self.status.value,
            "decided_by": self.decided_by,
            "provenance": self.provenance,
            "where": self.where,
            "owner": self.owner,
        }


class Ledger:
    """An ordered collection of facts, keyed by id.

    Order is the order in which facts were first added, which is import order
    of the file being checked, so a rendered ledger reads like the source.
    """

    def __init__(self, facts: Any = ()) -> None:
        self._facts: dict[str, Fact] = {}
        for fact in facts:
            self.add(fact)

    def add(self, fact: Fact) -> Fact:
        """Add a fact, or replace the one with the same id, keeping its place."""
        self._facts[fact.id] = fact
        return fact

    def __iter__(self) -> Any:
        """Iterate the facts in insertion order."""
        return iter(self._facts.values())

    def __len__(self) -> int:
        """The number of facts."""
        return len(self._facts)

    def __getitem__(self, fact_id: str) -> Fact:
        """The fact with this id."""
        return self._facts[fact_id]

    def __contains__(self, fact_id: object) -> bool:
        """Whether a fact with this id is in the ledger."""
        return fact_id in self._facts

    def by_status(self, status: Status) -> tuple[Fact, ...]:
        """Every fact with this status, in order."""
        return tuple(fact for fact in self if fact.status is status)

    def vacuous(self) -> tuple[Fact, ...]:
        """Every fact whose hypotheses were shown inconsistent, in order."""
        return tuple(fact for fact in self if fact.is_vacuous)

    def counts(self) -> dict[str, int]:
        """How many facts of each status, for a one-line summary."""
        out: dict[str, int] = {}
        for fact in self:
            out[fact.status.value] = out.get(fact.status.value, 0) + 1
        return out

    def to_json(self, indent: int = 2) -> str:
        """The ledger as JSON text."""
        return json.dumps([fact.to_dict() for fact in self], indent=indent, default=str)

    def render(self, width: int = 72) -> str:
        """A fixed-width table: status, decider, location, and statement.

        ``width`` bounds the statement column; everything else is sized to its
        contents, so the table stays readable in a terminal.

        A fact's location is ``basename:line``, which is short and enough for
        the usual ledger of one file. When two facts from different files share
        a basename the column would be ambiguous, so those rows, and only
        those, grow a parent directory; the full path stays in provenance.

        A vacuous fact's status carries the mark, as in ``proved (vacuous)``,
        and the summary line counts the vacuous facts after the statuses.
        """
        locations = _locations(list(self))
        rows = [
            (
                f"{fact.status.value} (vacuous)" if fact.is_vacuous else fact.status.value,
                fact.decided_by or "-",
                locations[index] or "-",
                fact.owner or "-",
                _clip(fact.statement, width),
            )
            for index, fact in enumerate(self)
        ]
        headers = ("status", "by", "where", "owner", "statement")
        if not rows:
            return "ledger is empty"
        widths = [
            max(len(headers[i]), max(len(row[i]) for row in rows))
            for i in range(len(headers))
        ]
        lines = [
            "  ".join(h.upper().ljust(w) for h, w in zip(headers, widths, strict=True)),
            "  ".join("-" * w for w in widths),
        ]
        lines += [
            "  ".join(cell.ljust(w) for cell, w in zip(row, widths, strict=True)).rstrip()
            for row in rows
        ]
        summary = ", ".join(f"{n} {name}" for name, n in sorted(self.counts().items()))
        vacuous = len(self.vacuous())
        if vacuous:
            summary += f"; {vacuous} vacuous"
        lines += ["", f"{len(self)} facts: {summary}"]
        return "\n".join(lines)

    def __repr__(self) -> str:
        """Summarize the ledger by status counts."""
        return f"Ledger({len(self)} facts, {self.counts()})"


def _locations(facts: list[Fact]) -> list[str]:
    """The ``where`` column, disambiguated where two files share a basename.

    Two facts collide when they print the same ``basename:line`` but came from
    different files, which ``provenance["path"]`` says. A colliding row is
    printed as ``parent/basename:line``; a fact with no path in its provenance
    cannot be disambiguated and is left as it is.
    """
    by_where: dict[str, set[str]] = {}
    for fact in facts:
        path = fact.provenance.get("path")
        if fact.where and path:
            by_where.setdefault(fact.where, set()).add(str(path))
    out = []
    for fact in facts:
        path = fact.provenance.get("path")
        if path and len(by_where.get(fact.where, ())) > 1:
            parent = os.path.basename(os.path.dirname(str(path)))
            out.append(f"{parent}/{fact.where}" if parent else fact.where)
        else:
            out.append(fact.where)
    return out


def _clip(text: str, width: int) -> str:
    """Shorten ``text`` to ``width`` characters, marking what was dropped."""
    text = " ".join(text.split())
    return text if len(text) <= width else text[: width - 3] + "..."
