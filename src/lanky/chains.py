"""Chains: a calculation in a proof, one link at a time, each with its reason.

The design idea. A textbook writes a calculation as a column: ``R[a, b]``,
then "= -R[a - 2, b + 2] (by the recurrence)", then the next line with its
reason. A proof body writes the same column in Python::

    return (
        R[a, b]
        .equals(-R[a - 2, b + 2], by=recurrence)
        .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))
        .equals(D[a, b], by=pde)
    )

which is how ``ruff format`` leaves a chain whose first term is on a line of
its own. Each call is one *link*: the relation, the term it reaches, and the
reason, ``by=``. Five words name the relations, read as the textbook reads
them: :meth:`Chain.equals`, :meth:`Chain.at_most`, :meth:`Chain.less_than`,
:meth:`Chain.at_least` and :meth:`Chain.more_than`, and every lanky term has
them too (:class:`lanky.terms.SymbolicMixin`), so a chain starts at a term.
It never starts at a Python number, which has no such method: the number is
written on the right.

``==`` is not the word for a link. ``==`` states a claim and ``.equals``
derives a step with a reason; Python's chained ``a == b == c`` carries no
reason, and it is a scheduled ``and`` besides.

What ``by=`` takes. A fact: a hypothesis of the theorem, a theorem, a fact
of :mod:`lanky.known`, the claim at a point (``claim(a - 2, b + 2)``), or a
fact on the way that an earlier line named. A fact may be called at a point,
``pde(a - 2, b)``, or left uncalled, ``by=pde``, where lanky finds the point
from the link's own terms (:mod:`lanky.matching`). A tuple of facts is the
link's reasons together. With no ``by=`` the link is algebra alone; the
hypotheses in scope still cover side conditions such as a nonzero
denominator. And ``by=...``, Python's ``Ellipsis``, leaves the link open: a
*hole*. The proof then closes "with holes", and the claim reads assumed, with
the lines of its holes named, until they are filled.

A named step. ``recurrence = a[n].equals(..., by=ode)`` is Dafny's ``assert
... by`` in Python: a fact on the way, named so that a later line can cite
it, ``return recurrence, claim(n - 1)``. The name is the Python name the
chain is assigned to, read off the source (:attr:`Chain.name`). A Python
name for a term, ``ratio = -beta / alpha``, is nothing new: it is the term.

Nothing here proves anything. A chain is a record of what the proof says,
built when a proof body is traced (under ``lanky check``, never on import and
never under ``python file.py``), with the line each link was written on. The
proof's compile makes it a ``calc`` (:mod:`lanky.proofs.compile`), and without
Lean each link's two sides are drawn at points (:mod:`lanky.proofs`). A chain
is not a proposition, and asking one for its truth value, as an ``if`` does,
is refused.
"""

from __future__ import annotations

import ast
import functools
import linecache
import os
import sys
from collections.abc import Iterator
from dataclasses import dataclass
from typing import Any

import pymbolic.primitives as prim

__all__ = [
    "RELATIONS",
    "WORDS",
    "Chain",
    "ChainError",
    "Link",
    "combined_relation",
    "link",
]

#: The words a link is written with, and the relation each states.
RELATIONS: dict[str, str] = {
    "equals": "==",
    "at_most": "<=",
    "less_than": "<",
    "at_least": ">=",
    "more_than": ">",
}

#: The word for each relation, as a message or an outline says it.
WORDS: dict[str, str] = {relation: word for word, relation in RELATIONS.items()}

#: Which way each relation goes: up for ``<=`` and ``<``, down for ``>=`` and ``>``.
_DIRECTION = {"==": 0, "<=": 1, "<": 1, ">=": -1, ">": -1}


class ChainError(TypeError):
    """A link written in a way no proof can read, named at its line with the fix."""


@dataclass(frozen=True, eq=False)
class Link:
    """One link of a chain: the relation, the term it reaches, and why.

    Attributes:
        relation: ``"=="``, ``"<="``, ``"<"``, ``">="`` or ``">"``.
        term: The term the link reaches, a lanky term or a number.
        reasons: What ``by=`` gave, as a tuple: each a fact the link cites
            (a hypothesis, a theorem, the claim at a point, a named chain),
            in the order written. Empty for a link that is algebra alone and
            for a hole.
        hole: Whether the link was written ``by=...``: left open.
        line: The source line the link's call is on, which is the line its
            word is on in a chain laid out a link to a line.
        path: The file the link was written in.
    """

    relation: str
    term: Any
    reasons: tuple[Any, ...] = ()
    hole: bool = False
    line: int | None = None
    path: str | None = None

    @property
    def word(self) -> str:
        """The word the link was written with: ``equals``, ``at_most``, ..."""
        return WORDS[self.relation]

    @property
    def algebra(self) -> bool:
        """Whether the link cites nothing and is no hole: algebra alone."""
        return not self.reasons and not self.hole

    @property
    def where(self) -> str:
        """``file.py:149``, or the line alone, or nothing."""
        if self.line is None:
            return ""
        if self.path is None:
            return str(self.line)
        return f"{os.path.basename(self.path)}:{self.line}"


def combined_relation(relations: Any) -> str:
    """The relation a chain of these links states between its ends.

    Equalities keep the relation of the others; ``<=`` and ``<`` give ``<``,
    and so do ``>=`` and ``>`` give ``>``. All equalities give ``==``.

    Raises:
        ValueError: If the links go both ways, ``<=`` and ``>=``.
    """
    result = "=="
    for relation in relations:
        if relation == "==":
            continue
        if result == "==":
            result = relation
            continue
        if _DIRECTION[relation] != _DIRECTION[result]:
            raise ValueError(f"{result} then {relation}")
        if relation in ("<", ">"):
            result = relation
    return result


class Chain:
    """A calculation: a term, then links, each to a term with its reason.

    Built by the relation words of a term (:class:`lanky.terms.SymbolicMixin`)
    and extended by the same words on the chain, each of which returns a new
    chain: a chain once named is never changed by a later link.

    Attributes:
        start: The term the chain starts at.
        links: Its links, in the order written.
    """

    __slots__ = ("links", "start")

    def __init__(self, start: Any, links: tuple[Link, ...]) -> None:
        self.start = start
        self.links = links

    # {{{ the words

    def equals(self, term: Any, *, by: Any = None) -> Chain:
        """One more link: the chain's last term equals ``term``, by ``by``."""
        return link(self, "==", term, by, sys._getframe(1))

    def at_most(self, term: Any, *, by: Any = None) -> Chain:
        """One more link: the chain's last term is at most ``term``, by ``by``."""
        return link(self, "<=", term, by, sys._getframe(1))

    def less_than(self, term: Any, *, by: Any = None) -> Chain:
        """One more link: the chain's last term is less than ``term``, by ``by``."""
        return link(self, "<", term, by, sys._getframe(1))

    def at_least(self, term: Any, *, by: Any = None) -> Chain:
        """One more link: the chain's last term is at least ``term``, by ``by``."""
        return link(self, ">=", term, by, sys._getframe(1))

    def more_than(self, term: Any, *, by: Any = None) -> Chain:
        """One more link: the chain's last term is more than ``term``, by ``by``."""
        return link(self, ">", term, by, sys._getframe(1))

    # }}}

    # {{{ what it says

    @property
    def end(self) -> Any:
        """The term the chain ends at."""
        return self.links[-1].term

    @property
    def relation(self) -> str:
        """The relation the chain states between its ends (:func:`combined_relation`)."""
        return combined_relation(link.relation for link in self.links)

    @property
    def claim(self) -> Any:
        """What the chain shows, as a proposition: its start, its relation, its end."""
        from lanky.terms import Comparison

        return Comparison(self.start, self.relation, self.end)

    def steps(self) -> Iterator[tuple[Any, Link]]:
        """Each link with the term it starts from: ``(left, link)``, in order."""
        left = self.start
        for each in self.links:
            yield left, each
            left = each.term

    @property
    def holes(self) -> tuple[int | None, ...]:
        """The lines of the links written ``by=...``, in order."""
        return tuple(each.line for each in self.links if each.hole)

    @property
    def line(self) -> int | None:
        """The line of the chain's first link."""
        return self.links[0].line

    @property
    def path(self) -> str | None:
        """The file the chain was written in."""
        return self.links[0].path

    @property
    def lines(self) -> tuple[int | None, int | None]:
        """The lines of its first and its last link."""
        return self.links[0].line, self.links[-1].line

    @property
    def name(self) -> str | None:
        """The Python name the chain is assigned to, as ``recurrence = a[n].equals(...)``.

        Read off the source: the assignment whose value is the call of the
        chain's last link, with one name as its target. ``None`` for a chain
        returned or passed as it is, and for one whose source cannot be read
        (code compiled from a string); a compiler names such a fact itself.
        """
        if self.path is None or self.links[-1].line is None:
            return None
        return _assigned_name(self.path, self.links[-1].line)

    # }}}

    def __bool__(self) -> bool:
        """Refuse: a chain is a step of a proof, and not a condition.

        Raises:
            ChainError: Always, naming the chain's line.
        """
        raise ChainError(
            f"the chain at {self.links[0].where or 'this line'} was asked for its truth "
            "value, as an if or an and asks; a chain is a step of the proof and not a "
            "condition: write the condition as a comparison, as in if a < 2:"
        )

    def __repr__(self) -> str:
        """``<chain R[a, b] == -R[a - 2, b + 2] == ... at l2p.py:148>``."""
        parts = [_shown(self.start)]
        for each in self.links:
            parts.append(f"{each.relation} {_shown(each.term)}")
        where = self.links[0].where
        text = " ".join(parts) if len(parts) <= 4 else " ".join([*parts[:3], "..."])
        return f"<chain {text}{f' at {where}' if where else ''}>"


def _shown(term: Any) -> str:
    """A term as a message prints it."""
    from lanky.terms import render

    if isinstance(term, prim.ExpressionNode):
        return render(term)
    return repr(term)


def link(left: Any, relation: str, term: Any, by: Any, frame: Any) -> Chain:
    """Add the link ``left relation term`` with its reason ``by``, written in ``frame``.

    ``left`` is a term, which starts a chain, or a chain, which goes on.
    ``frame`` is the frame that called the word, whose line the link is on.

    Raises:
        ChainError: For a term that is a proposition (a link reaches a
            term), for a ``by=`` that is no fact, and for a link that turns
            the chain the other way (``at_most`` after ``at_least``).
    """
    from lanky.terms import PropositionMixin

    line = getattr(frame, "f_lineno", None)
    path = getattr(getattr(frame, "f_code", None), "co_filename", None)
    where = f"{os.path.basename(path)}:{line}" if path and line else "this line"
    word = WORDS[relation]
    if isinstance(left, PropositionMixin):
        raise ChainError(
            f"{where}: .{word}(...) is called on the proposition {_shown(left)}; a "
            f"chain starts at a term, as in R[a, b].{word}(...)"
        )
    if isinstance(term, PropositionMixin | bool) or isinstance(term, Chain):
        what = "a chain" if isinstance(term, Chain) else "a proposition"
        raise ChainError(
            f"{where}: .{word}({_shown(term)}) reaches {what}; a link reaches a term, "
            f"as in .{word}(-R[a - 2, b + 2], by=recurrence)"
        )
    reasons, hole = _reasons(by, word, where)
    if isinstance(left, Chain):
        start, links = left.start, left.links
    else:
        start, links = left, ()
    if links:
        try:
            combined_relation((*(each.relation for each in links), relation))
        except ValueError:
            raise ChainError(
                f"{where}: .{word}(...) turns the chain the other way after "
                f".{_last_order(links)}(...); a chain goes one way: split it in two, "
                "or name the first part and cite it"
            ) from None
    return Chain(start, (*links, Link(relation, term, reasons, hole, line, path)))


def _last_order(links: tuple[Link, ...]) -> str:
    """The word of the last link of ``links`` that is not an equality."""
    for each in reversed(links):
        if each.relation != "==":
            return each.word
    return "equals"


def _reasons(by: Any, word: str, where: str) -> tuple[tuple[Any, ...], bool]:
    """``by=`` as a tuple of reasons, and whether it is a hole.

    Raises:
        ChainError: For a reason that cannot be a fact: a string, a number, a
            truth value, ``None`` inside a tuple, or ``...`` beside facts.
    """
    if by is None:
        return (), False
    if by is Ellipsis:
        return (), True
    reasons = tuple(by) if isinstance(by, tuple | list) else (by,)
    for reason in reasons:
        if reason is Ellipsis:
            raise ChainError(
                f"{where}: .{word}(..., by=...) leaves the step open, and takes no facts "
                "beside it; write by=... alone, or the facts alone"
            )
        if reason is None or isinstance(reason, str | bytes | int | float | complex):
            raise ChainError(
                f"{where}: .{word}(..., by={reason!r}) names no fact; by= takes a "
                "hypothesis, a theorem, a fact on the way or the claim at a point, or "
                "a tuple of them, as in by=(recurrence, pde)"
            )
        if isinstance(reason, prim.ExpressionNode):
            raise ChainError(
                f"{where}: .{word}(..., by={_shown(reason)}) is a term, which is no "
                "reason; by= takes a fact: a hypothesis, a theorem, a fact on the way "
                "or the claim at a point"
            )
    return reasons, False


# {{{ the name a chain is assigned to


@functools.lru_cache(maxsize=64)
def _module_tree(path: str, stamp: tuple[int, int]) -> ast.Module | None:
    """The parsed source of ``path``, or ``None`` where it cannot be read."""
    del stamp  # in the key alone, so that an edited file is read again
    lines = linecache.getlines(path)
    if not lines:
        return None
    try:
        return ast.parse("".join(lines), filename=path)
    except SyntaxError:
        return None


def _stamp(path: str) -> tuple[int, int]:
    """What tells one version of a file from another: its time and size."""
    try:
        status = os.stat(path)
    except OSError:
        return (0, 0)
    return (status.st_mtime_ns, status.st_size)


def _assigned_name(path: str, line: int) -> str | None:
    """The one name an assignment binds whose value is a link's call at ``line``.

    The value has to be a call of one of the relation words, and the call
    whose word is on ``line`` the outermost one: the chain's last link.
    """
    tree = _module_tree(path, _stamp(path))
    if tree is None:
        return None
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign) and len(node.targets) == 1:
            target, value = node.targets[0], node.value
        elif isinstance(node, ast.AnnAssign) and node.value is not None:
            target, value = node.target, node.value
        else:
            continue
        if not isinstance(target, ast.Name) or not isinstance(value, ast.Call):
            continue
        function = value.func
        if not (isinstance(function, ast.Attribute) and function.attr in RELATIONS):
            continue
        if getattr(function, "end_lineno", None) == line:
            return target.id
    return None


# }}}
