"""The two words a written proof adds to Python: ``by`` and ``claim``.

The design idea (the decision of 2026-10-18, proofs in lanky read as
engineers write checks). A proof is the checks an engineer already writes,
``assert``, ``if`` and ``for``, with the reason for each step after it::

    from lanky import by, claim, theorem


    @theorem
    def line_taylor(...) -> all(a[n] == ... for n in Nat if n >= 1):
        for n in claim.dom:
            if n == 1:
                yield by(first_term)
            else:
                assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode)
                yield by(claim[n - 1])

- ``by(f, g)`` is the reason for a step: in an ``assert``'s message, where
  Python reads it only when the step fails, after ``yield`` for the point the
  loop is at, after ``return`` for a claim with no variables. ``by(...)``,
  Python's ``Ellipsis``, leaves the step open.
- ``claim`` is the theorem being proved, as Flask's ``request`` is the request
  being served: ``claim.dom`` is the domain of its conclusion, ``claim[p]``
  the conclusion at an earlier point of that domain, ``claim(...)`` the
  theorem at smaller values of its parameters.

``claim`` is a proxy for what lanky sets while it runs or traces a body, kept
in a context variable (:func:`claiming`): outside a theorem's body it
refuses, since there is no theorem for it to be.

Nothing here proves anything. ``by(...)`` records the facts it is given, and
``claim`` hands each question to the run in progress: the trace
(:mod:`lanky.proofs.trace`), which records the proof for Lean, or the native
run (:mod:`lanky.proofs.native`), which runs the body at drawn values.
"""

from __future__ import annotations

import sys
from collections.abc import Iterator
from contextlib import contextmanager
from contextvars import ContextVar
from typing import Any

import pymbolic.primitives as prim

__all__ = [
    "By",
    "OutsideAProof",
    "RemovedForm",
    "by",
    "claim",
    "claiming",
    "reason_text",
]


class OutsideAProof(RuntimeError):
    """``claim`` used where no theorem's body runs."""


class RemovedForm(TypeError):
    """A form of lanky 0.5's proofs, refused with the line to write in 0.6.

    Attributes:
        fix: The line to write instead.
    """

    def __init__(self, message: str, fix: str | None = None) -> None:
        super().__init__(message if fix is None else f"{message}; write {fix}")
        self.message = message
        self.fix = fix


# {{{ by


def reason_text(fact: Any) -> str:
    """A fact as a proof writes it: ``ode``, ``pde(i, a - 2, b)``, ``claim[n - 1]``."""
    text = getattr(fact, "text", None)
    if callable(text):
        try:
            return str(text())
        except Exception:  # noqa: BLE001 - a fact that cannot say itself is named
            pass
    for attribute in ("__name__", "name"):
        name = getattr(fact, attribute, None)
        if isinstance(name, str) and name:
            return name
    if isinstance(fact, prim.ExpressionNode):
        from lanky.terms import render

        return render(fact)
    return repr(fact)


class By:
    """The reasons for a step, as ``by(f, g)`` gives them.

    Attributes:
        facts: The facts, in the order written: hypotheses of the theorem,
            theorems, facts of :mod:`lanky.known`, the claim at a point.
        hole: Whether the step was left open, ``by(...)``.
    """

    __slots__ = ("facts", "hole")

    def __init__(self, facts: tuple[Any, ...], hole: bool = False) -> None:
        self.facts = facts
        self.hole = hole

    def __bool__(self) -> bool:
        """Refuse: a reason is no condition."""
        raise TypeError(
            "by(...) is the reason for a step, not a condition; it goes after the step, "
            "as in assert x == y, by(f)"
        )

    def __repr__(self) -> str:
        """``by(ode)``, as it was written; Python prints it when a native step fails."""
        if self.hole:
            return "by(...)"
        return f"by({', '.join(reason_text(fact) for fact in self.facts)})"

    __str__ = __repr__


def by(*facts: Any) -> By:
    """The reasons for a step: ``assert x == y, by(f, g)``, ``yield by(f)``, ``return by(f)``.

    Each fact is a hypothesis of the theorem (``ode``), a theorem or a fact
    of :mod:`lanky.known` (``log_of_a_power``), either at a point
    (``pde(i, a - 2, b)``) or alone, where lanky finds the point from the
    step; or the claim at an earlier point (``claim[n - 1]``) or at smaller
    values (``claim(n - 1)``). ``by(...)``, Python's ``Ellipsis``, leaves the
    step open: the proof holds but for it, and the claim's row names the
    line. ``by()`` with no facts is algebra alone, as an ``assert`` with no
    message is.

    Raises:
        TypeError: For a reason that cannot be a fact: a string, a number, a
            truth value, ``None``, a term, or ``...`` beside facts.
    """
    flat: list[Any] = []
    for fact in facts:
        if isinstance(fact, tuple | list):
            flat.extend(fact)
        else:
            flat.append(fact)
    if any(fact is Ellipsis for fact in flat):
        if len(flat) != 1:
            raise TypeError(
                "by(...) leaves the step open, and takes no facts beside it; write by(...) "
                "alone, or the facts alone"
            )
        return By((), True)
    for fact in flat:
        if isinstance(fact, By):
            raise TypeError("by(...) takes facts, not another by(...): write by(f, g) once")
        if fact is None or isinstance(fact, str | bytes | bool | int | float | complex):
            raise TypeError(
                f"by({fact!r}) names no fact; by takes a hypothesis, a theorem, a fact lanky "
                "knows or the claim at a point, as in by(recurrence, claim[n - 1])"
            )
        if isinstance(fact, prim.ExpressionNode):
            raise TypeError(
                f"by({reason_text(fact)}) is given a term, which is no reason; by takes a "
                "fact: a hypothesis, a theorem, a fact lanky knows or the claim at a point"
            )
    return By(tuple(flat), False)


# }}}


# {{{ claim


#: What ``claim`` stands for while a body runs or is traced, or ``None``.
_CLAIM: ContextVar[Any] = ContextVar("lanky_claim", default=None)

#: What ``claim`` says outside a theorem's body.
OUTSIDE = "claim is the theorem being proved; it means something only inside a theorem's body"


@contextmanager
def claiming(current: Any) -> Iterator[None]:
    """Have ``claim`` stand for ``current`` while the block runs (a trace or a native run)."""
    token = _CLAIM.set(current)
    try:
        yield
    finally:
        _CLAIM.reset(token)


def current_claim() -> Any:
    """What ``claim`` stands for here, or ``None`` outside a theorem's body."""
    return _CLAIM.get()


class _Claim:
    """``claim``: the theorem being proved, inside its body (see the module).

    Each use is handed to the run in progress, which answers it: ``claim.dom``
    (its ``dom()``), ``claim[p]`` (``at``), ``claim(...)`` (``call``) and
    ``claim.n`` (``handle``).
    """

    __slots__ = ()

    @staticmethod
    def _current() -> Any:
        current = _CLAIM.get()
        if current is None:
            raise OutsideAProof(OUTSIDE)
        return current

    @property
    def dom(self) -> Any:
        """The domain of the claim's conclusion: ``for n in claim.dom:``."""
        return self._current().dom(sys._getframe(1))

    def __getitem__(self, point: Any) -> Any:
        """The conclusion at ``point``, which comes earlier in the loop: ``claim[n - 1]``."""
        return self._current().at(point, sys._getframe(1))

    def __call__(self, *values: Any, **named: Any) -> Any:
        """The theorem at other values of its parameters, smaller ones: ``claim(n - 1)``."""
        return self._current().call(values, named, sys._getframe(1))

    def __getattr__(self, name: str) -> Any:
        """A variable of the conclusion as a handle, ``claim.n``, for messages."""
        if name.startswith("_"):
            raise AttributeError(name)
        return self._current().handle(name)

    def __iter__(self) -> Any:
        """Refuse: the points are ``claim.dom``'s."""
        self._current()
        raise TypeError("claim is the theorem; its points are claim.dom's: for n in claim.dom:")

    def __bool__(self) -> bool:
        """Refuse: the claim is a fact, cited at a point."""
        self._current()
        raise TypeError(
            "claim is the theorem being proved, not a condition; cite it at a point, as "
            "claim[n - 1], or at other values, as claim(n - 1)"
        )

    def __repr__(self) -> str:
        """What ``claim`` stands for here, or what it is."""
        current = _CLAIM.get()
        if current is None:
            return "<claim: the theorem being proved, inside a theorem's body>"
        return repr(current)


#: The theorem being proved (see :class:`_Claim`).
claim = _Claim()


# }}}
