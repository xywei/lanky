"""What a proof cites: facts, at a point or not, and how each is restated in Lean.

The design idea. A step of a proof gives its reasons by name: a hypothesis of
the theorem (``pde``), a theorem (``log_of_a_power``), the claim at a smaller
point (``claim(a - 2, b + 2)``), or a fact on the way that an earlier line
named (``recurrence``). Each reason is a :class:`Citation`: what the proof
called it, the fact as a lanky term, how Lean applies it, and the point it is
cited at, if the proof wrote one. A fact left uncalled, ``by=pde``, has no
point here; :mod:`lanky.matching` finds it from the step's own terms.

What a proof body holds while it is traced is not a citation but a handle the
tracer gave it: the hypothesis ``pde`` as a parameter, ``claim`` as a function
that records its calls. Any object can be a reason that answers
``__lanky_citation__()`` with its :class:`Citation`; :class:`Hypothesis` is the
handle for a hypothesis (calling it, ``pde(a - 2, b)``, cites it at a point),
and :func:`citation_of` also reads a named chain (:class:`lanky.chains.Chain`)
and a :class:`lanky.theory.Theorem` passed as it is.

A theorem is cited through its *cited text*. A citation of a theorem ``B``
in a proof of ``A`` is a hypothesis of ``A``'s Lean declaration, ``(B : ...)``,
and a hypothesis restated wrongly, one that drops a condition, proves
anything. So the text restated is the one ``B``'s own command proved, its
``Lanky.B.as_cited`` theorem, read from what the check of ``B`` recorded
(:func:`proved_texts`), byte for byte; where there is none, ``B`` was not
proved, and the text is printed from ``B``'s term, trusting the printer as
every citation did before, with ``B``'s id in what ``A`` rests on so that the
ledger bounds ``A`` by ``B``'s status. The citation says which it is
(:attr:`Citation.proved_text`).
"""

from __future__ import annotations

import sys
from collections.abc import Iterator, Mapping, Sequence
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, replace
from typing import Any

import pymbolic.primitives as prim

from lanky.induction import Lemma, domain_conditions, substitute
from lanky.terms import Forall, Var, conjuncts, render

__all__ = [
    "Citation",
    "CitedText",
    "Cited",
    "Hypothesis",
    "citation_of",
    "fact_lemma",
    "premises_of",
    "proved_texts",
    "restated_text",
    "vacuity_question",
]


@dataclass(frozen=True, eq=False)
class Citation:
    """One reason a step gives: a fact, how Lean applies it, and where it is cited.

    Attributes:
        name: What the proof called it, for messages and outlines: ``pde``,
            ``recurrence``, ``log_of_a_power``, or ``the claim``.
        proposition: The fact as a lanky term: a :class:`~lanky.terms.Forall`
            over the values it is cited at, or a closed proposition.
        head: The Lean text the fact is applied by, its values after it:
            ``pde``, ``recurrence``, ``Lanky.compressed_taylor.claim D R pde
            stored recurrence``.
        point: The values the proof cited it at, one per binder of
            :attr:`proposition`, in order; ``None`` for a fact left uncalled,
            whose point a step's terms give (:mod:`lanky.matching`). A fact
            with no binders is at the empty point.
        line: The line the citation was written on.
        kind: ``"hypothesis"``, ``"theorem"``, ``"claim"`` or ``"named"``.
        fact_id: For a theorem, the ledger id the citing claim rests on.
        restated: For a theorem, the text the citing declaration takes it as,
            a hypothesis named :attr:`head` (see :func:`restated_text`).
        proved_text: Whether :attr:`restated` is the text the theorem's own
            command proved, and not one printed here.
        premises: For a theorem whose own proof cited others, those
            theorems, each by its proved text: its ``as_cited`` theorem takes
            them as hypotheses, so a citer restates them too (see
            :class:`CitedText`).
    """

    name: str
    proposition: Any
    head: str
    point: tuple[Any, ...] | None = None
    line: int | None = None
    kind: str = "hypothesis"
    fact_id: str | None = None
    restated: str | None = None
    proved_text: bool = False
    premises: tuple[Citation, ...] = ()

    @property
    def lemma(self) -> Lemma:
        """The fact as a lemma: its binders, the premises Lean applies it to, its proposition."""
        lemma = fact_lemma(self.head, self.proposition)
        if lemma is None:
            raise TypeError(
                f"{self.name} states {render(self.proposition)}, which is no fact a step "
                "can cite: a comparison, under universals"
            )
        return lemma

    @property
    def binders(self) -> tuple[tuple[Var, Any], ...]:
        """The values the fact is cited at, as its binders: ``(variable, domain)`` pairs."""
        return self.lemma.binders

    def at(self, point: tuple[Any, ...]) -> Citation:
        """The same fact, at ``point``."""
        return replace(self, point=tuple(point))

    @property
    def instance(self) -> Any:
        """The fact at its point, as a comparison; ``None`` for a fact with no point yet."""
        if self.point is None:
            return None
        lemma = self.lemma
        values = dict(zip((var.name for var, _ in lemma.binders), self.point, strict=True))
        return substitute(lemma.equation, values)

    @property
    def guards(self) -> tuple[Any, ...]:
        """What the fact needs at its point: its premises' propositions there, in order."""
        if self.point is None:
            return ()
        lemma = self.lemma
        values = dict(zip((var.name for var, _ in lemma.binders), self.point, strict=True))
        return tuple(substitute(guard, values) for guard in lemma.guards)

    def described(self, point: tuple[Any, ...] | None = None) -> str:
        """The citation as an outline says it: ``pde, at (a - 2, b)``, ``the claim at (a - 2)``."""
        point = self.point if point is None else point
        if not point:
            return self.name
        values = ", ".join(_shown(value) for value in point)
        if self.kind == "claim":
            return f"{self.name} at ({values})"
        return f"{self.name}, at ({values})"


def _shown(value: Any) -> str:
    """A value as a message prints it: a term rendered, a family's value as a function."""
    shown = getattr(value, "shown", None)
    if callable(shown):
        return shown()
    if isinstance(value, prim.ExpressionNode):
        return render(value)
    return repr(value)


def fact_lemma(head: str, proposition: Any) -> Lemma | None:
    """A fact as a lemma: its binders, the premises Lean applies it to, its comparison.

    As :func:`lanky.induction.lemma_of`, level by level as Lean prints a
    universal: each binder with its domain's guards after it, and a level's
    own guard after its last binder, one premise per conjunct. A comparison of
    any kind is taken, ``<=`` and ``!=`` as well as ``==``, so a step can cite
    an inequality. ``None`` for a fact whose innermost body is no comparison,
    and for one whose levels rebind a name.
    """
    binders: list[tuple[Var, Any]] = []
    premises: list[tuple[str, Any]] = []
    node = proposition
    while isinstance(node, Forall):
        for var, domain in node.binders:
            binders.append((var, domain))
            premises.append(("value", var.name))
            premises += [("proof", guard) for guard in domain_conditions(var, domain)]
        premises += [("proof", guard) for guard in conjuncts(node.guard)]
        node = node.body
    if not isinstance(node, prim.Comparison):
        return None
    names = [var.name for var, _ in binders]
    if len(set(names)) != len(names):
        return None
    return Lemma(head, tuple(binders), tuple(premises), node)


# {{{ handles a proof body holds


class Hypothesis:
    """A hypothesis of the theorem being proved, as a proof body holds it.

    Cited uncalled, ``by=pde``, at the point a step's terms give; called,
    ``pde(a - 2, b)``, at that point (a :class:`Cited`). Its values are the
    binders of its universal, in order, and a call with another number of
    them is refused at its line.
    """

    def __init__(self, name: str, proposition: Any, head: str | None = None) -> None:
        self.name = name
        self.proposition = proposition
        self.head = head or name

    def __lanky_citation__(self) -> Citation:
        """The hypothesis, uncalled."""
        return Citation(self.name, self.proposition, self.head)

    def __call__(self, *values: Any) -> Cited:
        """The hypothesis at a point, cited from the line of the call.

        Raises:
            TypeError: If the number of values is not the number of its binders.
        """
        frame = sys._getframe(1)
        citation = self.__lanky_citation__()
        expected = [var.name for var, _ in citation.binders]
        if len(values) != len(expected):
            names = ", ".join(expected) or "none"
            raise TypeError(
                f"line {frame.f_lineno}: {self.name} is cited at {len(values)} "
                f"value{'s' if len(values) != 1 else ''}, and it takes {len(expected)} "
                f"({names}), in that order"
            )
        return Cited(replace(citation, point=tuple(values), line=frame.f_lineno))

    def __repr__(self) -> str:
        """``<hypothesis pde: all(...)>``."""
        return f"<hypothesis {self.name}: {render(self.proposition)}>"


class Cited:
    """A fact at a point, as ``pde(a - 2, b)`` gives it."""

    def __init__(self, citation: Citation) -> None:
        self.citation = citation

    def __lanky_citation__(self) -> Citation:
        """The citation, at its point."""
        return self.citation

    def __repr__(self) -> str:
        """``<pde, at (a - 2, b)>``."""
        return f"<{self.citation.described()}>"


# }}}


# {{{ reading a reason


def citation_of(reason: Any, *, mathlib: bool = True) -> Citation:
    """The :class:`Citation` a reason given to ``by=`` or returned by a case stands for.

    A citation is itself; an object that answers ``__lanky_citation__`` is
    what it answers; a named chain (:class:`lanky.chains.Chain`) is the fact
    it shows, cited by its name; a :class:`lanky.theory.Theorem` is the
    theorem, uncalled, restated by its cited text (:func:`restated_text`), in
    the dialect ``mathlib`` says.

    Raises:
        TypeError: For anything else, naming what it is.
    """
    from lanky.chains import Chain

    if isinstance(reason, Citation):
        return reason
    answer = getattr(reason, "__lanky_citation__", None)
    if callable(answer):
        found = answer()
        if not isinstance(found, Citation):
            raise TypeError(f"{reason!r} answered {found!r} for its citation")
        return found
    if isinstance(reason, Chain):
        name = reason.name
        if name is None:
            where = reason.links[-1].where or "its line"
            raise TypeError(
                f"the chain at {where} is cited without a name; name it, as in "
                "recurrence = a[n].equals(..., by=ode), and cite recurrence"
            )
        return Citation(name, reason.claim, name, (), reason.line, "named")
    from lanky.theory import Theorem

    if isinstance(reason, Theorem):
        text, proved = restated_text(reason, mathlib=mathlib)
        return Citation(
            reason.__name__,
            reason.term,
            reason.__name__,
            kind="theorem",
            fact_id=reason.fact_id,
            restated=text,
            proved_text=proved,
            premises=premises_of(reason.fact_id) if proved else (),
        )
    raise TypeError(
        f"{reason!r} is no fact a step can cite: a hypothesis, a theorem, a fact on the "
        "way or the claim at a point"
    )


# }}}


# {{{ cited texts


@dataclass(frozen=True)
class CitedText:
    """What a proved theorem's own command proved for its citers.

    The command that proves a theorem ``B`` ends with ``Lanky.B.as_cited``,
    whose statement is the text a citation of ``B`` restates. Where ``B``'s
    proof cites ``C``, that theorem takes ``C``'s text as a hypothesis,
    ``theorem Lanky.B.as_cited (C : ⟨C's text⟩) : ⟨B's text⟩ := Lanky.B C``,
    so a citation of ``B`` restates ``C``'s text as well, and rests on it.

    Attributes:
        name: The theorem's name, under which a citing declaration takes the text.
        text: The statement of its ``as_cited`` theorem, byte for byte.
        premises: The fact ids of the theorems its ``as_cited`` takes, in order.
    """

    name: str
    text: str
    premises: tuple[str, ...] = ()


#: What each proved theorem's own command proved for its citers, by fact id:
#: a :class:`CitedText`, or its text alone. The check of a file sets it as it goes.
_PROVED_TEXTS: ContextVar[Mapping[str, Any] | None] = ContextVar("lanky_proved_texts", default=None)


@contextmanager
def proved_texts(texts: Mapping[str, Any]) -> Iterator[None]:
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
    token = _PROVED_TEXTS.set(dict(texts))
    try:
        yield
    finally:
        _PROVED_TEXTS.reset(token)


def _proved(fact_id: str | None) -> CitedText | None:
    """The proved text recorded for a theorem, as a :class:`CitedText`, or ``None``."""
    found = (_PROVED_TEXTS.get() or {}).get(fact_id)
    if found is None or isinstance(found, CitedText):
        return found
    return CitedText(fact_id or "", str(found))


def restated_text(theorem: Any, *, mathlib: bool = True) -> tuple[str, bool]:
    """The text a citation of ``theorem`` restates, and whether its own command proved it.

    The proved text when the check recorded one (:func:`proved_texts`); else
    the statement printed from the theorem's term, in the dialect ``mathlib``
    says, which trusts the printer, as a citation without a proved text does
    (:func:`vacuity_question` is then what bounds the damage).

    Raises:
        lanky.lean.UnsupportedTerm: If there is no proved text and the
            printer declines the theorem's statement.
    """
    found = _proved(theorem.fact_id)
    if found is not None:
        return found.text, True
    from lanky.lean import print_lean

    return print_lean(theorem.term, mathlib=mathlib), False


def premises_of(fact_id: str, seen: tuple[str, ...] = ()) -> tuple[Citation, ...]:
    """The theorems a proved theorem's ``as_cited`` takes, each a citation by its proved text.

    Each premise has to be a proved text itself: the soundness of a
    citation is an induction over what each proved theorem rests on, and a
    premise with no proved text breaks it.

    Raises:
        ValueError: If a premise has no proved text, naming it, or if the
            premises come round to a theorem again, naming the circle.
    """
    found = _proved(fact_id)
    if found is None:
        return ()
    out: list[Citation] = []
    for premise in found.premises:
        if premise in (*seen, fact_id):
            circle = " -> ".join((*seen, fact_id, premise))
            raise ValueError(f"the citations go round in a circle: {circle}")
        cited = _proved(premise)
        if cited is None:
            raise ValueError(
                f"{found.name} was proved citing {premise}, which has no proved text; "
                "a citation rests on proved texts all the way down"
            )
        out.append(
            Citation(
                cited.name,
                None,
                cited.name,
                kind="theorem",
                fact_id=premise,
                restated=cited.text,
                proved_text=True,
                premises=premises_of(premise, (*seen, fact_id)),
            )
        )
    return tuple(out)


def vacuity_question(owner: str, citations: Sequence[Citation], where: str | None = None) -> Any:
    """Whether the cited theorems without a proved text prove ``False`` together, as a fact.

    A citation restated from a printed text trusts the printer, and a text
    that dropped a condition could prove anything (the check's T4: a
    ``log_of_a_power`` without ``n >= 0`` proves ``1 = 0``). So the check
    asks, as it asks whether a claim's hypotheses are vacuous
    (:func:`lanky.check.hypotheses_fact`), whether those texts alone prove
    ``False``: the fact returned is that question, of kind ``"hypotheses"``,
    which the Lean oracle answers with its short ladder and the vacuity
    budget; established, the citing claim has to fail. ``None`` where every
    citation is by a proved text, and there is nothing to ask.
    """
    from lanky.ledger import Fact
    from lanky.terms import LogicalAnd

    printed = [
        citation
        for citation in citations
        if citation.kind == "theorem"
        and not citation.proved_text
        and citation.proposition is not None
    ]
    if not printed:
        return None
    terms = tuple(citation.proposition for citation in printed)
    guard = terms[0] if len(terms) == 1 else LogicalAnd(terms)
    names = ", ".join(citation.name for citation in printed)
    return Fact(
        id=f"{owner}:citations",
        kind="hypotheses",
        statement=f"the theorems {owner} cites without a proved text ({names}) are inconsistent",
        term=Forall((), False, guard),
        where=where,
        owner=owner,
    )


# }}}
