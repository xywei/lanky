"""Citations restated only from text Lean proved.

The design idea. A proof that cites a theorem takes the theorem's statement as
a hypothesis: loopty's part that applies ``compressed_taylor`` to a kernel's
postcondition (:class:`lanky.obligations.Application`), the series a kernel
adds (``line_taylor``), the passes a program's postcondition unfolds through
(``sum_factorization``). Lean then checks the step from the hypothesis to the
claim, and nothing checks the hypothesis: it is printed from the theorem's
term, and a printer that dropped a condition of it would hand the part a
hypothesis that proves anything. ``log_of_a_power`` restated without ``0 ≤
n`` proves ``1 = 0``, with no error and no axiom beyond Lean's own.

So the text a citation restates is never printed for the citation. Each
claim's command proves one more theorem after its own,
``Lanky.name.as_cited``, whose statement is the claim as one proposition
(:attr:`lanky.lean.LeanStatement.as_cited`), proved from the claim's theorem;
when the command closes, that text is a proved fact, and the oracle keeps it
here, by the claim's fact id (:class:`ProvedTexts`), whether Lean answered
now or the proof cache kept its answer. A part that cites the claim
(:class:`lanky.obligations.Citation`) restates exactly that text, byte for
byte, as a hypothesis before any variable of its own, where no name of the
part can mean anything in it (:func:`restatements`). Its source holds the
text, so its proof-cache entry is the entry of a proof from that text.

Two checks keep the restatement honest:

- The conjunct the part cites has to be the claim's term as its theory
  states it (:func:`lanky.terms.structurally_equal`). A part that cites a
  claim and restates something else is refused before Lean is asked, with
  the claim named: that is the misrestated citation, caught where it is
  made.
- A text is kept only from a command that closed with it, so a cited claim
  whose ``as_cited`` did not follow from its own theorem (a printer whose two
  readings of the claim disagree) has no text kept, and is not proved
  either.

A claim with no text kept (one only tested, an axiom, one whose Lean attempt
failed, or one this process did not check) is restated by the printer, as
every citation was before, and the part says so (``restated by the
printer``). The ledger bounds what rests on it: a fact is worth at most what
it rests on, and a part's fact rests on the claims it cites.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from lanky.terms import Forall, conjuncts, structurally_equal

__all__ = ["Proved", "ProvedTexts", "Restatement", "restatements"]


@dataclass(frozen=True)
class Proved:
    """The text a claim's command proved as ``as_cited``, and where it came from.

    ``fact`` is the claim's fact id, ``name`` the theorem its command
    declared (``Lanky.compressed_taylor``), ``text`` the proposition its
    ``as_cited`` states, ``mathlib`` whether it is printed in Mathlib's
    dialect, and ``term`` the claim's term, which a citation's conjunct has
    to be.
    """

    fact: str
    name: str
    text: str
    mathlib: bool
    term: Any = field(compare=False)


class ProvedTexts:
    """The ``as_cited`` texts of the claims a Lean oracle proved, by fact id.

    Filled as claims are proved (:meth:`record`), the proof cache's answers
    included, so a warm check knows the same texts as the check that asked
    Lean. A claim proved again replaces its text, and :meth:`forget` drops a
    claim's when it is checked and not proved.
    """

    def __init__(self) -> None:
        self._texts: dict[str, Proved] = {}

    def record(self, proved: Proved) -> None:
        """Keep the text a claim's command proved."""
        self._texts[proved.fact] = proved

    def forget(self, fact: str) -> None:
        """Drop what was kept of a claim that is no longer proved."""
        self._texts.pop(fact, None)

    def get(self, fact: str) -> Proved | None:
        """The text kept for the claim ``fact``, or ``None``."""
        return self._texts.get(fact)

    def __contains__(self, fact: object) -> bool:
        return fact in self._texts

    def __len__(self) -> int:
        return len(self._texts)


@dataclass(frozen=True)
class Restatement:
    """How a part's citations are restated (:func:`restatements`).

    ``texts`` maps the position of each restated conjunct to the text it is
    restated as; ``notes`` say, for each citation, whether its text is the
    one its claim's command proved or the printer's, as provenance; and
    ``refused``, when it is not empty, why the part is not sent to Lean.
    """

    texts: dict[int, str] = field(default_factory=dict)
    notes: tuple[dict[str, Any], ...] = ()
    refused: str = ""


def restatements(part: Any, proved: ProvedTexts) -> Restatement:
    """The texts ``part`` restates its citations as, or why it is refused.

    Each :class:`~lanky.obligations.Citation` whose claim has a proved text
    is restated as that text, once its conjunct is shown to be the claim's
    term. One whose conjunct is something else refuses the part. One whose
    claim has no proved text is left to the printer, and noted.
    """
    citations = tuple(getattr(part, "citations", ()) or ())
    if not citations:
        return Restatement()
    term = getattr(part, "term", None)
    guards = list(conjuncts(term.guard)) if isinstance(term, Forall) else []
    texts: dict[int, str] = {}
    notes: list[dict[str, Any]] = []
    for citation in sorted(citations, key=lambda citation: citation.hypothesis):
        name = citation.name or citation.fact
        if not 0 <= citation.hypothesis < len(guards):
            return Restatement(
                refused=(
                    f"the part cites {name} at hypothesis {citation.hypothesis}, and has "
                    f"{len(guards)}"
                )
            )
        found = proved.get(citation.fact)
        if found is None:
            notes.append(
                {
                    "theorem": name,
                    "fact": citation.fact,
                    "restated": "by the printer",
                    "why": f"no command of this check proved {name}'s statement",
                }
            )
            continue
        if not structurally_equal(guards[citation.hypothesis], found.term):
            return Restatement(
                refused=(
                    f"the part restates {name} as something other than the statement "
                    f"Lean proved of it, so Lean is not asked: a hypothesis that is not "
                    f"what {found.name} proves could prove anything"
                )
            )
        texts[citation.hypothesis] = found.text
        notes.append(
            {
                "theorem": name,
                "fact": citation.fact,
                "restated": f"as {found.name}.as_cited, which its command proved",
            }
        )
    return Restatement(texts=texts, notes=tuple(notes))
