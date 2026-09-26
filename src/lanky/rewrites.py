"""The ``@rewrite`` shape: a source, a target, and what has to hold between them.

The design idea. Much of what a consumer of lanky wants checked is a
transformation: a loop nest recast by a schedule, an integral representation
taken to the boundary by the jump relations, a direct formula replaced by a
recurrence. Each is a *rewrite*. Some tool turns a source into a target, and an
obligation between the two says when that was sound. The tool that did the
rewriting (loopy, pytential's operator classes, a person at a blackboard) is
not what the ledger trusts. The oracle that discharges the obligation is, and
the ledger names it.

A rewrite is one fact of one shape. Its kind is ``"rewrite"``, its term is a
:class:`RewriteTerm` holding the source, the target and the obligation, which
is what an oracle works on, and its statement reads ``source ~> target
(obligation)``. The obligation is a short name the deciding oracle recognizes,
``"equal"`` when nothing else is said: a plugin that decides ``"jump
relations"`` takes the rewrites that name it and declines the rest, so a
rewrite no oracle can decide stays ``assumed``, as every obligation nobody
established does. What a decision rests on, such as the axioms a rule engine
applied, goes in the fact's ``rests_on``, as for any fact.

There are two ways in. ``@rewrite`` decorates a function of no arguments that
returns the pair ``(source, target)``. The function is the rewriter: it runs
once, where it is decorated, and the object it becomes registers itself for
``lanky check`` as a theorem does. A plugin that builds its facts itself, as
loopty does for each step of a schedule, calls :func:`rewrite_fact`, and may
hand the fact back already decided when its decision procedure ran as the step
was taken. A subclass of :class:`Rewrite` can claim more than the rewrite, a
verdict about its target say, by overriding :meth:`Rewrite.facts`.
"""

from __future__ import annotations

import functools
import inspect
import os
from collections.abc import Iterable
from dataclasses import dataclass
from typing import Any

from lanky.ledger import Fact, Status, fact_id
from lanky.plugins import registry
from lanky.terms import render
from lanky.theory import fact_ids

__all__ = ["Rewrite", "RewriteTerm", "RewriteTheory", "rewrite", "rewrite_fact"]


@dataclass(frozen=True, eq=False)
class RewriteTerm:
    """What a rewrite claims, as the term an oracle decides.

    Attributes:
        source: What was rewritten.
        target: What the rewriter made of it.
        obligation: What has to hold between the two, named so that an oracle
            can tell whether it is one it decides. ``"equal"`` when nothing
            else is said.

    Two terms are equal only when they are the same object. A source or a
    target may be a lanky term, whose ``==`` builds a proposition rather than
    answering, so the fields are not compared. A plugin that needs more than
    the three fields to decide its obligation (the rules it may apply, say)
    subclasses this and adds them.
    """

    source: Any
    target: Any
    obligation: str = "equal"

    def __str__(self) -> str:
        """``source ~> target (obligation)``, each side rendered as a term."""
        return f"{render(self.source)} ~> {render(self.target)} ({self.obligation})"


def _obligation(value: Any) -> str:
    """The obligation a rewrite names, or ``TypeError`` saying what one is."""
    if not isinstance(value, str) or not value.strip():
        raise TypeError(
            f"a rewrite's obligation is a short name an oracle recognizes, such as "
            f"'equal' or 'jump relations'; got {value!r}"
        )
    return value


def rewrite_fact(
    term: RewriteTerm,
    *,
    owner: str,
    module: str | None = None,
    line: int | None = None,
    path: str | None = None,
    where: str = "",
    detail: str = "",
    rests_on: Iterable[str] = (),
) -> Fact:
    """One rewrite as a ledger entry, before any oracle has seen it.

    The fact's id is built by :func:`lanky.ledger.fact_id` with kind
    ``"rewrite"``, so ``detail`` tells apart several rewrites one object
    claims, one per step of a schedule, say. ``path`` and ``line`` go into
    the provenance, where :func:`lanky.check.check_path` reads which file a
    fact belongs to when its object wraps no function. The status is
    ``assumed``; a plugin that decided the obligation already returns the
    fact through :meth:`~lanky.ledger.Fact.with_status`.

    Raises:
        TypeError: If ``term`` is not a :class:`RewriteTerm`.
    """
    if not isinstance(term, RewriteTerm):
        raise TypeError(f"a rewrite fact's term is a RewriteTerm, not {term!r}")
    provenance: dict[str, Any] = {}
    if path is not None:
        provenance["path"] = path
    if line is not None:
        provenance["line"] = line
    return Fact(
        id=fact_id("rewrite", owner, module=module, line=line, detail=detail),
        kind="rewrite",
        statement=str(term),
        term=term,
        status=Status.ASSUMED,
        decided_by=None,
        provenance=provenance,
        where=where,
        owner=owner,
        rests_on=tuple(rests_on),
    )


class Rewrite:
    """A rewrite read off a function: the pair it returns, and the obligation named.

    Attributes:
        source: The first of the pair the function returned.
        target: The second.
        obligation: What has to hold between them (see :class:`RewriteTerm`).
        uses: The ids of the facts the rewrite rests on, from ``uses=``, read
            as :func:`lanky.theory.fact_ids` reads a theorem's. The oracle
            that decides the rewrite may add to them the facts it applied.

    Raises:
        TypeError: If the function takes arguments, since it is run once with
            none, or returns anything but a pair.
    """

    #: What the claim is called in messages. Its fact's kind is ``"rewrite"``
    #: whatever a subclass calls it, since that is the shape an oracle reads.
    noun = "rewrite"

    def __init__(self, fn: Any, *, obligation: Any = "equal", uses: Any = ()) -> None:
        self.fn = fn
        functools.update_wrapper(self, fn)
        self.obligation = _obligation(obligation)
        self.uses = fact_ids(uses)
        code = fn.__code__
        self.path = code.co_filename
        self.line = code.co_firstlineno
        self.where = f"{os.path.basename(code.co_filename)}:{code.co_firstlineno}"
        self.qualname = getattr(fn, "__qualname__", fn.__name__)
        self.module = getattr(fn, "__module__", "") or ""
        required = [
            name
            for name, parameter in inspect.signature(fn).parameters.items()
            if parameter.default is inspect.Parameter.empty
            and parameter.kind not in (parameter.VAR_POSITIONAL, parameter.VAR_KEYWORD)
        ]
        if required:
            raise TypeError(
                f"{self.qualname} at {self.where}: a rewrite's function takes no "
                f"arguments, since it is the rewriter and is run once where it is "
                f"decorated; it asks for {', '.join(required)}"
            )
        pair = fn()
        if not isinstance(pair, tuple) or len(pair) != 2:
            raise TypeError(
                f"{self.qualname} at {self.where}: a rewrite's function returns the "
                f"pair (source, target), and this one returned {pair!r}"
            )
        self.source, self.target = pair

    @property
    def term(self) -> RewriteTerm:
        """The claim as the term an oracle decides."""
        return RewriteTerm(self.source, self.target, self.obligation)

    @property
    def statement(self) -> str:
        """``source ~> target (obligation)``."""
        return str(self.term)

    @property
    def fact_id(self) -> str:
        """The id the rewrite's fact carries, unique per definition, as a theorem's is."""
        return fact_id("rewrite", self.qualname, module=self.module, line=self.line)

    def fact(self) -> Fact:
        """This rewrite as a ledger entry, before any oracle has seen it."""
        return rewrite_fact(
            self.term,
            owner=self.qualname,
            module=self.module,
            line=self.line,
            path=self.path,
            where=self.where,
            rests_on=self.uses,
        )

    def facts(self) -> tuple[Fact, ...]:
        """Every fact this object claims: the rewrite's own, and nothing else here.

        A subclass that claims more about its target overrides this, keeping
        :meth:`fact` among what it returns.
        """
        return (self.fact(),)

    def __call__(self) -> Any:
        """The target: what the rewriter made of the source."""
        return self.target

    def __repr__(self) -> str:
        """Print the name and the statement."""
        return f"<{self.noun} {self.__name__}: {self.statement}>"


class RewriteTheory:
    """The built-in theory of rewrites: ``@rewrite``, and whatever :class:`Rewrite` claims."""

    name = "rewrite"

    def __call__(self, obj: Any, /) -> Rewrite:
        """Decorate ``obj`` as a rewrite and register it."""
        return rewrite(obj)

    def facts(self, obj: Any, /) -> tuple:
        """The facts a rewrite claims, or nothing for an object it does not own."""
        return tuple(obj.facts()) if isinstance(obj, Rewrite) else ()


#: The theory itself.
rewrite_theory = RewriteTheory()
registry.register_theory(rewrite_theory)


def rewrite(fn: Any = None, /, *, obligation: Any = "equal", uses: Any = ()) -> Any:
    """Take a function returning ``(source, target)`` as a :class:`Rewrite`, and register it.

    Written bare, ``@rewrite``, the obligation is ``"equal"``; or
    ``@rewrite(obligation="jump relations", uses=[...])``. The function runs
    once, here, with no arguments. ``uses=`` names facts the rewrite rests on,
    as for :func:`lanky.theory.theorem`.

    Raises:
        TypeError: When the obligation is not a name, an entry of ``uses=``
            names no one fact, or the positional argument is not the function
            to decorate, as in ``@rewrite("equal")``, where ``obligation=``
            was meant.
    """
    if fn is not None and (not callable(fn) or isinstance(fn, Rewrite)):
        raise TypeError(
            f"@rewrite decorates a function returning (source, target), and {fn!r} "
            "is not one; the obligation goes in obligation='...'"
        )
    checked = _obligation(obligation)
    rests_on = fact_ids(uses)

    def decorate(fn: Any) -> Rewrite:
        return registry.register_object(Rewrite(fn, obligation=checked, uses=rests_on))

    return decorate if fn is None else decorate(fn)
