"""Chains: a calculation in a proof, written as Python writes a chained comparison.

The design idea. A textbook writes a calculation as a column: ``R[a, b]``,
then "= -R[a - 2, b + 2]", then the next line, with the reasons beside it. A
proof writes the same calculation as an ``assert`` of Python's own chained
comparison, its reasons after it::

    assert R[a, b] == -R[a - 2, b + 2] == -D[a - 2, b + 2] == D[a, b], by(
        recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde
    )

Each comparison is a *link*: the relation and the term it reaches. ``==``,
``<=``, ``<``, ``>=`` and ``>`` mix as they do in Python, and the chain
states the relation they make together between its two ends
(:func:`combined_relation`). The trace reads the links off the questions
Python asks of the comparisons (:mod:`lanky.proofs.trace`), and the compile
makes the chain a ``calc``, each link closed from the facts of the
``by(...)`` that fit it (:mod:`lanky.proofs.compile`).

lanky 0.5 wrote a link as a method of a term, ``R[a, b].equals(-R[a - 2, b +
2], by=recurrence)``, with four siblings, ``at_most``, ``less_than``,
``at_least`` and ``more_than``. They are refused now, with the ``assert`` to
write (:func:`refuse_word`).
"""

from __future__ import annotations

import os
from typing import Any

import pymbolic.primitives as prim

__all__ = [
    "RELATIONS",
    "WORDS",
    "combined_relation",
    "refuse_word",
]

#: The words lanky 0.5 wrote a link with, and the relation each states.
RELATIONS: dict[str, str] = {
    "equals": "==",
    "at_most": "<=",
    "less_than": "<",
    "at_least": ">=",
    "more_than": ">",
}

#: The word for each relation, as a message says it.
WORDS: dict[str, str] = {relation: word for word, relation in RELATIONS.items()}

#: Which way each relation goes: up for ``<=`` and ``<``, down for ``>=`` and ``>``.
_DIRECTION = {"==": 0, "<=": 1, "<": 1, ">=": -1, ">": -1}


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


def _shown(term: Any) -> str:
    """A term as a message prints it."""
    from lanky.terms import render

    if isinstance(term, prim.ExpressionNode):
        return render(term)
    return repr(term)


def refuse_word(left: Any, relation: str, term: Any, by: Any, frame: Any) -> None:
    """Refuse lanky 0.5's ``x.equals(y, by=f)``, with the ``assert`` to write instead.

    Raises:
        lanky.surface.RemovedForm: Always, with the line to write:
            ``assert x == y, by(f)``.
    """
    from lanky.surface import RemovedForm, reason_text

    word = WORDS[relation]
    line = getattr(frame, "f_lineno", None)
    path = getattr(getattr(frame, "f_code", None), "co_filename", None)
    where = f"{os.path.basename(path)}:{line}: " if path and line else ""
    if by is None:
        reason = ""
    elif by is Ellipsis:
        reason = ", by(...)"
    else:
        reasons = by if isinstance(by, tuple | list) else (by,)
        reason = f", by({', '.join(reason_text(item) for item in reasons)})"
    written = f"assert {_shown(left)} {relation} {_shown(term)}{reason}"
    raise RemovedForm(
        f"{where}.{word}(...) is how lanky 0.5 wrote a step; a step is an assert of the "
        f"comparison, its reasons after it",
        written,
    )
