"""What a proof cites: one :class:`Citation` for every fact cited, and how each is restated in Lean.

The design idea. A step of a proof gives its reasons by name: a hypothesis of
the theorem (``pde``), a theorem (``log_of_a_power``), the claim at a smaller
point (``claim[a - 2, b + 2]``), or the theorem at smaller values
(``claim(n - 1)``). A part a plugin states cites theorems the same way, as
hypotheses: loopty's part that applies ``compressed_taylor`` to a kernel's
postcondition, the series a kernel adds (``line_taylor``), the passes a
program's postcondition unfolds through (``sum_factorization``). Each is a
:class:`Citation`: what is cited, and where. In a written proof, where is the
line and the point, if the proof wrote one; a fact left uncalled, ``by(pde)``,
has no point, and :mod:`lanky.matching` finds it from the step's own terms. In
a part, where is the hypothesis of the part that restates the theorem.

A theorem is cited through its *cited text*. A citation of a theorem ``B``
in a proof of ``A`` is a hypothesis of ``A``'s Lean declaration, ``(B : ...)``,
and so is a part's: Lean checks the step from the hypothesis to the claim, and
nothing checks the hypothesis. A hypothesis restated wrongly, one that drops a
condition, proves anything: ``log_of_a_power`` restated without ``0 ≤ n``
proves ``1 = 0``, with no error and no axiom beyond Lean's own.

So the text a citation restates is never printed for the citation. Each
claim's command proves one more theorem after its own,
``Lanky.name.as_cited``, whose statement is the claim as one proposition
(:attr:`lanky.lean.LeanStatement.as_cited`), proved from the claim's theorem;
when the command closes, that text is a proved fact, and the oracle keeps it
here, by the claim's fact id (:class:`ProvedTexts`), whether Lean answered now
or the proof cache kept its answer. A text is kept only from a command whose
source holds it as that theorem's statement, byte for byte
(:func:`closed_with`): on a warm check, the source is the one the proof cache
kept its answer for, so the string is compared with ``B``'s cache entry and
not with what the printer says today. A citation restates exactly that text,
and a written proof's restated texts are compared again with the kept ones
before Lean is asked, warm or not. A part's citation restates the text as a
hypothesis before any variable of its own, where no name of the part can mean
anything in it (:func:`restatements`). The citing source holds the text, so
its proof-cache entry is the entry of a proof from that text.

Two more checks keep a restatement honest:

- The conjunct a part cites has to be the claim's term as its theory states
  it (:func:`lanky.terms.structurally_equal`). A part that cites a claim and
  restates something else is refused before Lean is asked, with the claim
  named: that is the misrestated citation, caught where it is made.
- A text is kept only for the term it was proved for, so a theorem changed in
  a long-lived process is not cited by its old text (:meth:`ProvedTexts.stale`).

A claim with no text kept (one only tested, an axiom, one whose Lean attempt
failed, or one this process did not check) is restated by the printer, as
every citation was before, and the citation says so (``restated by the
printer``). The ledger bounds what rests on it, a fact being worth at most
what it rests on, and Lean is asked whether those printed texts prove
``False`` where the proof takes them (:func:`vacuity_question`).
"""

from __future__ import annotations

import itertools
import re
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from typing import Any

from lanky.terms import Forall, conjuncts, render, structurally_equal

__all__ = [
    "Citation",
    "CitedText",
    "Premise",
    "Proved",
    "ProvedTexts",
    "Restatement",
    "closed_with",
    "premises_of",
    "proved_text",
    "proved_texts",
    "restatements",
    "vacuity_question",
]


@dataclass(frozen=True, eq=False)
class Citation:
    """One fact cited, and where: by a step of a written proof, or by a hypothesis of a part.

    Attributes:
        source: What is cited: a hypothesis of the theorem being proved
            (:class:`lanky.proofs.trace.Given`), a theorem
            (:class:`lanky.theory.Theorem`), the claim at a point
            (:class:`lanky.proofs.trace.ClaimDef`), or a theorem known by
            its proved text alone (:class:`Premise`).
        values: The point, a value per variable of the fact, outermost
            first; ``None`` for a fact cited by its name alone, whose point
            the step it supports gives (:mod:`lanky.matching`).
        line: The line of the proof the citation was written on.
        hypothesis: For a part's citation, the position of the hypothesis
            that restates the theorem among the conjuncts of the part's guard,
            as an :class:`lanky.obligations.Instance`'s is. The conjunct has
            to be the theorem's term as its theory states it.
        bracket: For a citation of the claim, whether it was written at a
            point of the conclusion, ``claim[a - 2, b + 2]``, rather than at
            values of the theorem's parameters, ``claim(n - 1)``.
    """

    source: Any
    values: tuple[Any, ...] | None = None
    line: int | None = None
    hypothesis: int | None = None
    bracket: bool = False

    @property
    def name(self) -> str:
        """The name the fact is cited by: ``pde``, ``log_of_a_power``, ``claim``."""
        source = self.source
        for attribute in ("__name__", "name"):
            name = getattr(source, attribute, None)
            if isinstance(name, str) and name:
                return name
        return getattr(source, "qualname", None) or repr(source)

    @property
    def fact(self) -> str:
        """The ledger id of a cited theorem, which the citing claim rests on; ``""`` for none."""
        return getattr(self.source, "fact_id", None) or ""

    @property
    def is_claim(self) -> bool:
        """Whether this is the claim at a point, which is the induction."""
        from lanky.proofs.trace import ClaimDef

        return isinstance(self.source, ClaimDef)

    def text(self, values: tuple[Any, ...] | None = None) -> str:
        """How the citation is written: ``pde(i, a - 2, b)``, ``stored`` alone, ``claim[n - 1]``."""
        values = self.values if values is None else values
        if values is None:
            return self.name
        written = getattr(self.source, "written", None)
        if self.is_claim and callable(written):
            return str(written(tuple(values), self.bracket))
        if self.bracket:
            return f"{self.name}[{', '.join(_shown(value) for value in values)}]"
        return f"{self.name}({', '.join(_shown(value) for value in values)})"


def _shown(value: Any) -> str:
    """A value as a citation writes it: a term rendered, a family's value as a function."""
    shown = getattr(value, "shown", None)
    if callable(shown):
        return shown()
    return render(value) if hasattr(value, "mapper_method") else repr(value)


class Premise:
    """A theorem a cited theorem's own proof cited, known by the text its command proved.

    Its ``as_cited`` text is a hypothesis of the cited theorem's ``as_cited``,
    ``theorem Lanky.B.as_cited (C : ⟨C's text⟩) : ⟨B's text⟩ := Lanky.B C``,
    so a citation of ``B`` restates ``C``'s text as well, and rests on it,
    all the way down (:func:`premises_of`). It has a theorem's ``__name__``
    and ``fact_id``, which is all a restatement reads, its ``text``, and its
    own ``premises``.
    """

    def __init__(
        self, name: str, fact_id: str, text: str, premises: tuple[Premise, ...] = ()
    ) -> None:
        self.__name__ = name
        self.fact_id = fact_id
        self.text = text
        self.premises = premises

    def __repr__(self) -> str:
        """``<premise log_of_a_power>``."""
        return f"<premise {self.__name__}>"


# {{{ cited texts


@dataclass(frozen=True)
class CitedText:
    """What a proved theorem's own command proved for its citers.

    The command that proves a theorem ``B`` ends with ``Lanky.B.as_cited``,
    whose statement is the text a citation of ``B`` restates. Where ``B``'s
    proof cites ``C``, that theorem takes ``C``'s text as a hypothesis, so a
    citation of ``B`` restates ``C``'s text as well, and rests on it.

    Attributes:
        name: The theorem's name, under which a citing declaration takes the text.
        text: The statement of its ``as_cited`` theorem, byte for byte.
        premises: The fact ids of the theorems its ``as_cited`` takes, in order.
    """

    name: str
    text: str
    premises: tuple[str, ...] = ()


#: What each proved theorem's own command proved for its citers, by fact id:
#: a :class:`CitedText`, a :class:`Proved`, or its text alone; or the Lean
#: oracle's :class:`ProvedTexts` itself. The check of a file sets it as it goes.
_PROVED_TEXTS: ContextVar[Any] = ContextVar("lanky_proved_texts", default=None)


@contextmanager
def proved_texts(texts: Mapping[str, Any] | ProvedTexts) -> Iterator[None]:
    """Use ``texts``, ``{fact id: CitedText or text}``, as what the cited theorems' commands proved.

    The check of a file establishes a cited theorem before the theorems that
    cite it, and its proof records the text its ``Lanky.B.as_cited`` theorem
    states and the premises it takes; the check hands them over here, so
    that a citation of ``B`` restates exactly that text, and its premises'
    (see the module docstring and :class:`CitedText`). The text is read
    afresh at each citation, so the citing command's source, which is its
    proof cache's key, changes with it: a warm check never reuses a proof
    made against another text.
    """
    token = _PROVED_TEXTS.set(texts if isinstance(texts, ProvedTexts) else dict(texts))
    try:
        yield
    finally:
        _PROVED_TEXTS.reset(token)


def proved_text(fact_id: str | None, term: Any = None) -> CitedText | None:
    """The text a theorem's own command proved, as the check recorded it; ``None`` for none.

    What :func:`proved_texts` set, for the theorem with this fact id, read
    as a :class:`CitedText`: its name, its ``as_cited`` text and the
    theorems that text takes as premises. Given the citing theorem's
    ``term``, a text recorded for another term under the same fact id (a
    theorem changed in a long-lived process, whose new statement Lean has
    not proved) is no proved text of it, and ``None`` is returned.
    """
    texts = _PROVED_TEXTS.get()
    found = None if texts is None or fact_id is None else texts.get(fact_id)
    if found is None or isinstance(found, CitedText):
        return found
    if isinstance(found, Proved):
        if term is not None and found.term is not None and not structurally_equal(found.term, term):
            return None
        return CitedText(found.name.removeprefix("Lanky."), found.text, found.premises)
    return CitedText(fact_id or "", str(found))


def premises_of(fact_id: str, seen: tuple[str, ...] = (), term: Any = None) -> tuple[Premise, ...]:
    """The theorems a proved theorem's ``as_cited`` takes, each by its proved text.

    Each premise has to be a proved text itself: the soundness of a
    citation is an induction over what each proved theorem rests on, and a
    premise with no proved text breaks it. Given the cited theorem's
    ``term``, a text recorded for another term has no premises of it
    (:func:`proved_text`).

    Raises:
        ValueError: If a premise has no proved text, naming it, or if the
            premises come round to a theorem again, naming the circle.
    """
    found = proved_text(fact_id, term)
    if found is None:
        return ()
    out: list[Premise] = []
    for premise in found.premises:
        if premise in (*seen, fact_id):
            circle = " -> ".join((*seen, fact_id, premise))
            raise ValueError(f"the citations go round in a circle: {circle}")
        cited = proved_text(premise)
        if cited is None:
            raise ValueError(
                f"{found.name} was proved citing {premise}, which has no proved text; "
                "a citation rests on proved texts all the way down"
            )
        out.append(
            Premise(cited.name, premise, cited.text, premises_of(premise, (*seen, fact_id)))
        )
    return tuple(out)


def closed_with(source: str, name: str, text: str) -> bool:
    """Whether the command ``source`` proves ``text`` as ``name.as_cited``, byte for byte.

    ``name`` is the theorem's Lean name, ``Lanky.B``. The command that
    proves ``B`` states its ``as_cited`` theorem on a line of its own after
    the theorem's head, ``theorem Lanky.B.as_cited ... :`` and then
    ``    <text> :=``, as :meth:`lanky.lean.LeanStatement.source` and a
    written proof's command (:mod:`lanky.proofs.compile`) both write it.
    The text is compared as the string it is: a command that states any
    other text, or none, did not prove it.
    """
    head = f"theorem {name}.as_cited"
    lines = source.splitlines()
    for index, line in enumerate(lines[:-1]):
        if not (line == head + " :" or (line.startswith(head + " (") and line.endswith(" :"))):
            continue
        statement = lines[index + 1]
        if statement in (f"    {text} :=", f"    {text} := by"):
            return True
    return False


# }}}


# {{{ the vacuity question


def vacuity_question(
    owner: str,
    theorems: Sequence[Any],
    where: str | None = None,
    points: Sequence[tuple[str, tuple[Any, ...]]] = (),
    mathlib: bool = False,
    variables: Sequence[tuple[Any, Any]] = (),
    conditions: Sequence[Any] = (),
    case: str = "",
) -> Any:
    """Whether the cited theorems without a proved text prove ``False`` together, as a fact.

    A citation restated from a printed text trusts the printer, and a text
    that dropped a condition could prove anything (the check's T4: a
    ``log_of_a_power`` without ``n >= 0`` proves ``1 = 0``). So the check
    asks, as it asks whether a claim's hypotheses are vacuous
    (:func:`lanky.check.hypotheses_fact`), whether those texts prove
    ``False``: the fact returned is that question, of kind ``"hypotheses"``,
    which the Lean oracle answers with its short ladder and the vacuity
    budget; established, the citing claim has to fail. ``None`` where every
    theorem cited has a proved text, and there is nothing to ask.

    A text that dropped a condition is false at a point, and no tactic of
    the short ladder looks for one; a proof that exploits it takes it at
    such a point. ``points`` are where the citing proof takes the theorems,
    ``(fact id, values)``, and the question is then a part whose hypotheses
    are taken there (:class:`lanky.obligations.Instance`), as the proof
    took them, in the dialect ``mathlib`` says. Points with variables, the
    claim's ``(a - 2, b)`` inside an induction, need those variables bound:
    ``variables`` are ``(Var, sort)`` binders over them and ``conditions``
    what holds in the case the points are taken in, the hypotheses after
    the texts. Such a question shows the texts prove ``False`` only if the
    case can happen, so the caller asks it unless the case is shown not to:
    where values satisfying ``conditions`` are found (:func:`satisfiable`),
    and where none are but the conditions alone are not shown to prove
    ``False``. ``case`` names it.
    """
    from lanky.ledger import Fact
    from lanky.terms import LogicalAnd

    printed = [
        theorem
        for theorem in dict.fromkeys(theorems)
        if getattr(theorem, "term", None) is not None
        and proved_text(getattr(theorem, "fact_id", None), theorem.term) is None
    ]
    if not printed:
        return None
    terms = tuple(theorem.term for theorem in printed)
    guards = (*terms, *conditions)
    guard = guards[0] if len(guards) == 1 else LogicalAnd(guards)
    names = ", ".join(theorem.__name__ for theorem in printed)
    term: Any = Forall(tuple(variables), False, guard)
    position = {theorem.fact_id: index for index, theorem in enumerate(printed)}
    taken: list[tuple[int, tuple[Any, ...]]] = []
    seen: set[tuple[str, tuple[str, ...]]] = set()
    for fact_id, values in points:
        # a point once, told apart by its text: a term is not hashed
        key = (fact_id, tuple(_shown(value) for value in values))
        if key in seen or fact_id not in position:
            continue
        seen.add(key)
        if isinstance(terms[position[fact_id]], Forall):
            taken.append((position[fact_id], tuple(values)))
    if variables and not taken:
        return None
    if taken:
        from lanky.obligations import Hints, Instance, Obligation, Part

        label = f"the theorems {owner} cites without a proved text, where its proof takes them"
        if case:
            label += f" {case}"
        part = Part(
            "citations",
            label,
            term,
            Hints(instances=tuple(Instance(index, values) for index, values in taken)),
            mathlib=mathlib,
        )
        term = _Question(Obligation(parts=(part,)), names, case)
    suffix = "@" + re.sub(r"[^0-9A-Za-z]+", "-", case).strip("-") if case else ""
    said = f" {case}" if case else ""
    return Fact(
        id=f"{owner}:citations{suffix}",
        kind="hypotheses",
        statement=(
            f"the theorems {owner} cites without a proved text ({names}) are inconsistent{said}"
        ),
        term=term,
        where=where,
        owner=owner,
    )


class _Question:
    """The question of :func:`vacuity_question` taken at points, as Lean is asked it."""

    def __init__(self, obligation: Any, names: str, case: str = "") -> None:
        self.obligation = obligation
        self.names = names
        self.case = case

    def lean_obligation(self) -> Any:
        return self.obligation

    def __str__(self) -> str:
        where = f" {self.case}" if self.case else ""
        return f"{self.names}, where the proof takes them{where}, prove False"


#: The values tried for each integer variable when a case is looked for a point of.
_INTEGERS = (0, 1, 2, 3, 4, 5, 6, -1, -2, -3)

#: The values tried for a real or complex variable.
_NUMBERS = (1, 2, 0, -1, 3)

#: How many points are tried at most.
_TRIES = 4096

#: How many of the integers a case's conditions name are tried, with their neighbours.
_NAMED = 8


def _integers_named(conditions: Sequence[Any]) -> tuple[int, ...]:
    """The integers ``conditions`` name, past the small ones, each with its neighbours."""
    import numbers

    from lanky.terms import init_args

    found: dict[int, None] = {}
    stack = list(conditions)
    while stack and len(found) < _NAMED:
        item = stack.pop()
        if isinstance(item, bool):
            continue
        if isinstance(item, numbers.Integral):
            if int(item) not in _INTEGERS:
                found[int(item)] = None
            continue
        if isinstance(item, (tuple, list)):
            stack.extend(item)
        elif hasattr(item, "mapper_method"):
            try:
                stack.extend(init_args(item))
            except Exception:  # noqa: BLE001 - what cannot be taken apart names nothing
                continue
    return tuple(
        value + step for value in found for step in (0, -1, 1) if value + step not in _INTEGERS
    )


def satisfiable(variables: Sequence[tuple[Any, Any]], conditions: Sequence[Any]) -> bool:
    """Whether some values of ``variables`` satisfy ``conditions`` and their domains, as found.

    A point is looked for among small numbers: each integer variable
    (``Nat``, ``Int``, a point of ``Fin``) from ``0`` up and a little below,
    and at the integers the conditions name and their neighbours (``n ==
    100`` is met at ``100``), each real or complex one among a few. ``True``
    where one is found. ``False`` says only that none was found: a family, a
    variable of another sort, or a condition that cannot be evaluated at
    numbers, makes it ``False`` too, so a caller that needs to know a case
    cannot happen asks a prover (:func:`lanky.proofs._ruled_out`).
    """
    from lanky.induction import domain_conditions
    from lanky.prelude import FinType, FnType, Refined, Sort
    from lanky.terms import evaluate

    named = _integers_named(conditions)
    integers = tuple(dict.fromkeys((*_INTEGERS, *named)))
    choices: list[tuple[Any, ...]] = []
    tests = list(conditions)
    for var, sort in variables:
        base = sort
        while isinstance(base, Refined):
            base = base.base
        tests += list(domain_conditions(var, sort))
        if isinstance(base, FinType) or (isinstance(base, Sort) and base.name in ("Nat", "Int")):
            choices.append(integers)
        elif isinstance(base, Sort) and base.name in ("Real", "Complex"):
            choices.append(_NUMBERS)
        elif isinstance(base, FnType):
            # a family is a value of its own sort, whatever the point; no
            # condition of the case may read it
            choices.append((None,))
        else:
            return False
    names = [var.name for var, _ in variables]
    for count, values in enumerate(itertools.product(*choices)):
        if count >= _TRIES:
            return False
        context = {name: value for name, value in zip(names, values, strict=True)}
        try:
            if all(evaluate(test, context) is True for test in tests):
                return True
        except Exception:  # noqa: BLE001 - a condition that cannot be evaluated finds no point
            return False
    return False


# }}}


# {{{ the texts a Lean oracle keeps


@dataclass(frozen=True)
class Proved:
    """The text a claim's command proved as ``as_cited``, and where it came from.

    ``fact`` is the claim's fact id, ``name`` the theorem its command
    declared (``Lanky.compressed_taylor``), ``text`` the proposition its
    ``as_cited`` states, ``mathlib`` whether it is printed in Mathlib's
    dialect, and ``term`` the claim's term, which a citation's conjunct has
    to be. ``premises`` are the fact ids of the theorems the claim's own
    proof cited, which its ``as_cited`` takes as hypotheses (a written
    proof's citations; see :class:`CitedText`). ``source`` is the command
    that closed, the one Lean answered or the proof cache kept the answer
    for, which has to state ``text`` as its ``as_cited`` (:func:`closed_with`).
    """

    fact: str
    name: str
    text: str
    mathlib: bool
    term: Any = field(compare=False)
    premises: tuple[str, ...] = ()
    source: str = field(default="", compare=False, repr=False)


class ProvedTexts:
    """The ``as_cited`` texts of the claims a Lean oracle proved, by fact id.

    Filled as claims are proved (:meth:`record`), the proof cache's answers
    included, so a warm check knows the same texts as the check that asked
    Lean. A claim proved again replaces its text, and :meth:`forget` drops a
    claim's when it is checked and not proved.
    """

    def __init__(self) -> None:
        self._texts: dict[str, Proved] = {}

    def record(self, proved: Proved) -> bool:
        """Keep the text a claim's command proved; whether it was kept.

        A text whose command is given and does not state it as the claim's
        ``as_cited`` is not kept (:func:`closed_with`): on a warm check the
        command is the one the proof cache kept an answer for, so this is
        the comparison of the text with the cited theorem's cache entry. A
        text that replaces another drops the texts that took the old one as
        a premise (:meth:`forget`), since their ``as_cited`` theorems take
        the old text as a hypothesis.
        """
        if proved.source and not closed_with(proved.source, proved.name, proved.text):
            self.forget(proved.fact)
            return False
        old = self._texts.get(proved.fact)
        if old is not None and old.text != proved.text:
            self._forget_citers(proved.fact)
        self._texts[proved.fact] = proved
        return True

    def forget(self, fact: str) -> None:
        """Drop what was kept of a claim that is no longer proved.

        And of every claim whose text takes it as a premise, all the way up
        (Codex, #171): their ``as_cited`` theorems restate its old text, so
        a citation of them would restate it too.
        """
        self._texts.pop(fact, None)
        self._forget_citers(fact)

    def _forget_citers(self, fact: str) -> None:
        """Drop the texts that take ``fact``'s as a premise, and theirs, and so on."""
        stack = [fact]
        while stack:
            current = stack.pop()
            citers = [other for other, kept in self._texts.items() if current in kept.premises]
            for other in citers:
                del self._texts[other]
            stack.extend(citers)

    def stale(self, terms: Mapping[str, Any]) -> list[str]:
        """Forget each text kept for another term than ``terms`` gives its claim; their ids.

        ``terms`` maps fact ids to the claims' terms as the check now reads
        them. A claim changed under its fact id in a long-lived process,
        and not asked of Lean again, keeps the text its earlier statement
        proved; it is dropped here, with the texts that cite it.
        """
        dropped = []
        for fact, term in terms.items():
            kept = self._texts.get(fact)
            if kept is None or kept.term is None or term is None:
                continue
            if not structurally_equal(kept.term, term):
                self.forget(fact)
                dropped.append(fact)
        return dropped

    def mismatch(self, restated: Sequence[tuple[str, str, str, Any]]) -> str:
        """Why a command's restated texts are not the kept ones; ``""`` when every one is.

        ``restated`` holds ``(name, fact id, text, term)`` for each theorem a
        citing command takes as a hypothesis, ``term`` its statement (``None``
        for a :class:`Premise`). Each with a text kept here for that term has
        to restate that text, byte for byte. One with none kept is restated
        by the printer, which :func:`vacuity_question` is about.
        """
        for name, fact, text, term in restated:
            kept = self._texts.get(fact)
            if kept is None or kept.text == text:
                continue
            if term is not None and kept.term is not None and not structurally_equal(
                kept.term, term
            ):
                # a text kept for the theorem's old statement is no text of it
                continue
            return (
                f"the proof restates {name} as a text other than the one its command proved, "
                "so Lean is not asked: a hypothesis that is not what Lean proved of it could "
                "prove anything"
            )
        return ""

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

    Each :class:`Citation` of the part names the hypothesis that restates a
    theorem. One whose claim has a proved text is restated as that text,
    once its conjunct is shown to be the claim's term. One whose conjunct is
    something else refuses the part. One whose claim has no proved text is
    left to the printer, and noted.
    """
    citations = tuple(getattr(part, "citations", ()) or ())
    if not citations:
        return Restatement()
    term = getattr(part, "term", None)
    guards = list(conjuncts(term.guard)) if isinstance(term, Forall) else []
    texts: dict[int, str] = {}
    notes: list[dict[str, Any]] = []
    for citation in sorted(citations, key=lambda citation: citation.hypothesis or 0):
        name = citation.name or citation.fact
        position = citation.hypothesis
        if position is None or not 0 <= position < len(guards):
            return Restatement(
                refused=f"the part cites {name} at hypothesis {position}, and has {len(guards)}"
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
        if not structurally_equal(guards[position], found.term):
            return Restatement(
                refused=(
                    f"the part restates {name} as something other than the statement "
                    f"Lean proved of it, so Lean is not asked: a hypothesis that is not "
                    f"what {found.name} proves could prove anything"
                )
            )
        texts[position] = found.text
        notes.append(
            {
                "theorem": name,
                "fact": citation.fact,
                "restated": f"as {found.name}.as_cited, which its command proved",
            }
        )
    return Restatement(texts=texts, notes=tuple(notes))


# }}}
