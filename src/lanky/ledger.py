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
says who showed it (see :func:`lanky.check.establish`). An *axiom*, a fact of
kind ``"axiom"``, is ``assumed`` on a citation rather than for want of an
oracle, and the table prints ``assumed (axiom)``. A fact settled by an oracle
of the ``heuristic`` trust class, one whose answer is not guaranteed (see
:data:`lanky.plugins.TRUST_STRENGTH`), prints ``decided (heuristic)``, so that
it is not read as the answer of a decision procedure.

Facts rest on facts. A fact's ``rests_on`` names the ids of the facts it was
established from: the lemmas a theorem ``uses``, the axioms a derivation
cites, the callee postcondition a plugin restates. A status says how strongly
a fact is established *given* those, so a proof from an assumption is worth
no more than the assumption. The ledger reads that off the graph
(:meth:`Ledger.support`): a fact's effective strength is the weakest status
over everything it rests on, directly or through other facts, a heuristic's
being the weaker of two alike, and the assumptions among those are what it is
established *under*. The table prints ``proved under jump, compact``, and an
``EFFECTIVE`` column when some fact is weaker than its own status says.
"""

from __future__ import annotations

import enum
import json
import os
from collections import Counter
from dataclasses import dataclass, field, replace
from typing import Any

__all__ = ["Fact", "Ledger", "Status", "Support", "fact_id"]


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
        rests_on: The ids of the facts this one was established from, in the
            order they were named. The status is the fact's own; what it is
            worth once those are counted is the ledger's question (see
            :meth:`Ledger.support`). A list is kept as a tuple, and a single
            string is refused rather than read as one id per character.
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
    rests_on: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        """Keep ``rests_on`` a tuple of ids, and refuse anything else in it."""
        rests_on = self.rests_on
        if isinstance(rests_on, str):
            raise TypeError(
                f"{self.id}: rests_on is a tuple of fact ids, and a single id is "
                f"written ({rests_on!r},)"
            )
        rests_on = tuple(rests_on)
        for entry in rests_on:
            if not isinstance(entry, str):
                raise TypeError(
                    f"{self.id}: rests_on names facts by id, a string, and "
                    f"{entry!r} is a {type(entry).__name__}"
                )
        object.__setattr__(self, "rests_on", rests_on)

    @property
    def is_vacuous(self) -> bool:
        """Whether an oracle has shown that nothing satisfies this fact's hypotheses."""
        return bool(self.provenance.get("vacuous"))

    @property
    def is_heuristic(self) -> bool:
        """Whether the oracle that settled this fact is of the ``heuristic`` trust class.

        :func:`lanky.check.establish` records the settling oracle's trust
        class in the provenance as ``trust_class``.
        """
        return self.provenance.get("trust_class") == "heuristic"

    @property
    def is_axiom(self) -> bool:
        """Whether this fact is assumed on a citation (see :func:`lanky.theory.axiom`).

        An axiom is not offered to the oracles: it is ``assumed`` because its
        author takes it on the citation in ``provenance["cite"]``, not because
        no oracle could establish it.
        """
        return self.kind == "axiom"

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
        """A JSON-ready dictionary; the term is rendered to text.

        This is the fact on its own. What it is worth given what it rests on
        needs the other facts, and :meth:`Ledger.to_dicts` adds it.
        """
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
            "rests_on": list(self.rests_on),
        }


@dataclass(frozen=True)
class Support:
    """What one fact is worth in a ledger, once what it rests on is counted.

    Attributes:
        effective: The weakest status over the fact and every fact it rests on,
            directly or through others, in the order of
            :data:`STATUS_STRENGTH`. A fact that rests on nothing is worth its
            own status. ``refuted`` here, on a fact that is not refuted itself,
            means it rests on one that is.
        under: The ids of the assumptions among the facts it rests on, in the
            order they are reached: those ``assumed`` or ``refuted``, those the
            ledger does not hold, and those that rest on themselves. Empty when
            the fact is established from established facts alone.
        heuristic: Whether the weakest of them was settled by a heuristic (see
            :attr:`Fact.is_heuristic`). Of two facts with one status, the one a
            heuristic settled is the weaker, so a proof that rests on a
            lemma a heuristic decided is worth ``decided (heuristic)``, and not
            the ``decided`` of a decision procedure.
    """

    effective: Status
    under: tuple[str, ...]
    heuristic: bool = False

    @property
    def text(self) -> str:
        """What the fact is worth as the table prints it: ``decided (heuristic)``, say."""
        return self.effective.value + (" (heuristic)" if self.heuristic else "")


class Ledger:
    """An ordered collection of facts, keyed by id.

    Order is the order in which facts were first added, which is import order
    of the file being checked, so a rendered ledger reads like the source.
    """

    def __init__(self, facts: Any = ()) -> None:
        self._facts: dict[str, Fact] = {}
        self._circles: frozenset[str] | None = None
        for fact in facts:
            self.add(fact)

    def add(self, fact: Fact) -> Fact:
        """Add a fact, or replace the one with the same id, keeping its place."""
        self._facts[fact.id] = fact
        self._circles = None
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

    # {{{ what a fact rests on

    def _reached(self, rests_on: tuple[str, ...]) -> list[str]:
        """Every id reachable from ``rests_on`` along ``rests_on``, each once, in order.

        Depth first, in the order each fact names its own, so a theorem's
        assumptions come out in the order its ``uses`` lists them. An id the
        ledger does not hold is reached and goes no further; a cycle is walked
        once.
        """
        reached: list[str] = []
        seen: set[str] = set()
        pending = list(reversed(rests_on))
        while pending:
            current = pending.pop()
            if current in seen:
                continue
            seen.add(current)
            reached.append(current)
            fact = self._facts.get(current)
            if fact is not None:
                pending.extend(reversed(fact.rests_on))
        return reached

    def _on_circles(self) -> frozenset[str]:
        """The ids of the facts that rest, through some chain, on themselves.

        Those are the facts that name themselves, and the facts of every
        strongly connected component of more than one fact in the graph of
        ``rests_on``, found once for the whole ledger (Tarjan's algorithm) and
        kept until a fact is added. Asking each fact whether it reaches itself
        would walk the graph once per fact per fact, which on a long chain
        costs minutes. The walk keeps its own stack rather than recursing, so
        that a long chain does not reach Python's recursion limit either.
        """
        if self._circles is not None:
            return self._circles
        graph = {
            fact_id: tuple(entry for entry in fact.rests_on if entry in self._facts)
            for fact_id, fact in self._facts.items()
        }
        index: dict[str, int] = {}
        low: dict[str, int] = {}
        stack: list[str] = []
        on_stack: set[str] = set()
        circles = {fact_id for fact_id, entries in graph.items() if fact_id in entries}
        for root in graph:
            if root in index:
                continue
            index[root] = low[root] = len(index)
            stack.append(root)
            on_stack.add(root)
            work = [(root, iter(graph[root]))]
            while work:
                node, entries = work[-1]
                for entry in entries:
                    if entry not in index:
                        index[entry] = low[entry] = len(index)
                        stack.append(entry)
                        on_stack.add(entry)
                        work.append((entry, iter(graph[entry])))
                        break
                    if entry in on_stack:
                        low[node] = min(low[node], index[entry])
                else:
                    work.pop()
                    if work:
                        parent = work[-1][0]
                        low[parent] = min(low[parent], low[node])
                    if low[node] == index[node]:
                        component = []
                        while True:
                            member = stack.pop()
                            on_stack.discard(member)
                            component.append(member)
                            if member == node:
                                break
                        if len(component) > 1:
                            circles.update(component)
        self._circles = frozenset(circles)
        return self._circles

    def support(self, fact: Fact | str) -> Support:
        """What a fact is worth here, given what it rests on (see :class:`Support`).

        Four things make a fact an assumption of the facts that rest on it. It
        is ``assumed``: an axiom, or an obligation nobody established. It is
        ``refuted``, so whatever was derived from it was derived from something
        false. The ledger does not hold it, which is the case of a claim in
        another file, since each file checked has a ledger of its own, and of
        an id written wrong: nothing here established it, and it counts as
        ``assumed`` (``lanky check`` names such an id under the table). Or it
        rests on itself, through some chain: a circular argument establishes
        nothing, so every fact on the circle, and every fact that rests on
        one, is worth ``assumed`` at most, and a fact on a circle is among its
        own assumptions.

        ``fact`` is a fact or an id; a fact not in the ledger is read against
        the ledger all the same. Of two facts with one status, one settled by
        a heuristic is the weaker (see :attr:`Support.heuristic`).
        """
        if isinstance(fact, str):
            fact = self._facts[fact]
        reached = self._reached(fact.rests_on)
        circles = self._on_circles()
        circular = {current for current in reached if current in circles}
        under: list[str] = []
        weakest, heuristic = fact.status, fact.is_heuristic
        for current in reached:
            held = self._facts.get(current)
            status = Status.ASSUMED if held is None else held.status
            if held is None or status in (Status.ASSUMED, Status.REFUTED) or current in circular:
                under.append(current)
            settled_by_heuristic = held is not None and held.is_heuristic
            if (STATUS_STRENGTH[status], not settled_by_heuristic) < (
                STATUS_STRENGTH[weakest],
                not heuristic,
            ):
                weakest, heuristic = status, settled_by_heuristic
        if circular and STATUS_STRENGTH[weakest] > STATUS_STRENGTH[Status.ASSUMED]:
            weakest, heuristic = Status.ASSUMED, False
        return Support(effective=weakest, under=tuple(under), heuristic=heuristic)

    def _label(self, fact_id: str, owners: Counter) -> str:
        """How the table names a fact another one rests on.

        By its owner when that names one fact in the ledger, which is the
        readable case of a theorem or an axiom, and by its id otherwise: a
        plugin's kernel owns many facts, and an id the ledger does not hold
        has no owner to show.
        """
        fact = self._facts.get(fact_id)
        if fact is not None and fact.owner and owners[fact.owner] == 1:
            return fact.owner
        return fact_id

    # }}}

    def to_dicts(self) -> list[dict]:
        """Every fact as a JSON-ready dictionary, with what it is worth here.

        :meth:`Fact.to_dict`, plus ``effective``, the status the fact is worth
        once what it rests on is counted, ``effective_heuristic``, whether a
        heuristic settled the fact that status is read off, and ``under``, the
        ids of the assumptions it is established under (see :meth:`support`).
        All three are there for every fact, a fact that rests on nothing
        carrying its own status, its own mark and an empty list.
        """
        out = []
        for fact in self:
            support = self.support(fact)
            out.append(
                {
                    **fact.to_dict(),
                    "effective": support.effective.value,
                    "effective_heuristic": support.heuristic,
                    "under": list(support.under),
                }
            )
        return out

    def to_json(self, indent: int = 2) -> str:
        """The ledger as JSON text: :meth:`to_dicts`, dumped."""
        return json.dumps(self.to_dicts(), indent=indent, default=str)

    def _status_cell(self, fact: Fact, support: Support, owners: Counter) -> str:
        """The status column of one row: the status, its marks, and what it is under."""
        cell = fact.status.value
        if fact.is_axiom:
            cell += " (axiom)"
        if fact.is_heuristic:
            cell += " (heuristic)"
        if fact.is_vacuous:
            cell += " (vacuous)"
        if support.under:
            cell += " under " + ", ".join(self._label(entry, owners) for entry in support.under)
        return cell

    def render(self, width: int = 72) -> str:
        """A fixed-width table: status, decider, location, and statement.

        ``width`` bounds the statement column; everything else is sized to its
        contents, so the table stays readable in a terminal.

        A fact's location is ``basename:line``, which is short and enough for
        the usual ledger of one file. When two facts from different files share
        a basename the column would be ambiguous, so those rows, and only
        those, grow a parent directory; the full path stays in provenance.

        A vacuous fact's status carries the mark, as in ``proved (vacuous)``,
        and the summary line counts the vacuous facts after the statuses. An
        axiom's reads ``assumed (axiom)``, and a fact a heuristic settled reads
        ``decided (heuristic)``.

        A fact established under assumptions (see :meth:`support`) says so
        after its status, as in ``proved under jump, compact``. When any fact
        is worth less than its own status, because it rests on something
        weaker, the table grows an ``EFFECTIVE`` column after the status with
        what each fact is worth; ``decided (heuristic)`` there is a fact
        resting on one a heuristic decided. A ledger in which nothing rests on
        anything renders as it always did.
        """
        facts = list(self)
        if not facts:
            return "ledger is empty"
        locations = _locations(facts)
        owners = Counter(fact.owner for fact in facts)
        supports = [self.support(fact) for fact in facts]
        weaker = any(
            support.effective is not fact.status or support.heuristic is not fact.is_heuristic
            for fact, support in zip(facts, supports, strict=True)
        )
        rows = [
            (
                self._status_cell(fact, support, owners),
                *((support.text,) if weaker else ()),
                fact.decided_by or "-",
                locations[index] or "-",
                fact.owner or "-",
                _clip(fact.statement, width),
            )
            for index, (fact, support) in enumerate(zip(facts, supports, strict=True))
        ]
        headers = (
            "status",
            *(("effective",) if weaker else ()),
            "by",
            "where",
            "owner",
            "statement",
        )
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
