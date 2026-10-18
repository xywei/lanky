"""What a written proof adds to Python: ``by``, and a claim's tree of parts.

The design idea (the decision of 2026-10-18, proofs in lanky read as
engineers write checks). A proof is the checks an engineer already writes,
``assert``, ``if`` and ``for``, with the reason for each step after it, and
the claim's own name spelled out::

    from lanky import by, claim


    @claim
    def line_taylor(...) -> all(a[n] == ... for n in Nat if n >= 1):
        for n in line_taylor.conclusion.domain:
            if n == 1:
                yield by(first_term)
            else:
                assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode[n - 1])
                yield by(line_taylor.conclusion[n - 1])

- ``by(f, g)`` is the reason for a step: in an ``assert``'s message, where
  Python reads it only when the step fails, after ``yield`` for the point the
  loop is at, after ``return`` for a claim proved without a loop. ``by()``
  adds nothing: the step follows directly. ``by(...)``, Python's
  ``Ellipsis``, leaves the step open.
- A claim is addressed through its tree (:class:`Conclusion`,
  :class:`Conditions`): ``line_taylor.conditions`` and
  ``line_taylor.conclusion`` are its two halves, ``line_taylor.conditions.ode``
  one condition, ``line_taylor.conclusion.domain`` the points the conclusion's
  ``for`` ranges over, ``line_taylor.conclusion[n - 1]`` the conclusion at a
  point, and ``every_box.conclusion[i].domain`` the domain of a conclusion
  that is itself a ``for`` at each point. Brackets give a point; parentheses
  give a claim for inputs, ``gauss(n - 1)``.

Nothing here proves anything. ``by(...)`` records the facts it is given, and
a part of the tree hands each question to the run in progress, the one
:func:`lanky.proofs.trace.active` answers: the trace
(:mod:`lanky.proofs.trace`), which records the proof for Lean, or the native
run (:mod:`lanky.proofs.native`), which runs the body at drawn values.
Outside both, the parts say what they are, and a domain refuses to be walked,
since only a proof has the inputs it is the domain at.
"""

from __future__ import annotations

import sys
from typing import Any

import pymbolic.primitives as prim

__all__ = [
    "By",
    "ClaimCondition",
    "Conclusion",
    "Conditions",
    "Domain",
    "FormError",
    "OutsideAProof",
    "RemovedForm",
    "by",
    "levels",
    "reason_text",
]


class OutsideAProof(RuntimeError):
    """A part of a claim's tree that means something only inside a proof, used outside one."""


class FormError(TypeError):
    """A form a proof refuses, with the line to write instead.

    Attributes:
        message: What is wrong, in the proof's own terms.
        fix: The line to write instead, when there is one.
        kind: What kind of refusal it is, as a :class:`lanky.proofs.trace.ProofError` names it.
    """

    kind = "form"

    def __init__(self, message: str, fix: str | None = None) -> None:
        super().__init__(message if fix is None else f"{message}; write {fix}")
        self.message = message
        self.fix = fix


class RemovedForm(FormError):
    """A form of lanky 0.5's proofs, refused with the line to write in 0.6."""

    kind = "removed"


# {{{ by


def reason_text(fact: Any) -> str:
    """A fact as a proof writes it: ``ode``, ``pde[i, a - 2, b]``, ``f.conclusion[n - 1]``."""
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
        facts: The facts, in the order written: conditions of the claim,
            other claims, facts of :mod:`lanky.known`, the claim's own
            conclusion at an earlier point.
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

    Each fact is a condition of the claim (``ode``), another claim or a fact
    of :mod:`lanky.known` (``log_of_a_power``), for given inputs
    (``gauss(n - 1)``) or alone, or a statement at a point of its domain
    (``pde[i, a - 2, b]``, ``line_taylor.conclusion[n - 1]``); a fact alone
    is applied where lanky finds it fits the step. ``by()`` adds nothing:
    the step follows directly, by lanky's strategies and the steps asserted.
    ``by(...)``, Python's ``Ellipsis``, leaves the step open: the proof
    holds but for it, and the claim's row names the line.

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
                f"by({fact!r}) names no fact; by takes a condition, a claim, a fact lanky "
                "knows or a conclusion at a point, as in by(ode[n - 1])"
            )
        if isinstance(fact, prim.ExpressionNode):
            raise TypeError(
                f"by({reason_text(fact)}) is given a term, which is no reason; by takes a "
                "fact: a condition, a claim, a fact lanky knows or a conclusion at a point"
            )
    return By(tuple(flat), False)


# }}}


# {{{ the tree: conditions and conclusion


def levels(goal: Any) -> list[tuple[tuple[tuple[Any, Any], ...], Any]]:
    """The domains a conclusion nests, outermost first: ``(binders, guard)`` per ``for``.

    ``all(... for i in A for a in B if g)`` is one level, whose points are
    ``(i, a)``; ``all(all(... for a in B) for i in A)`` is two, the
    conclusion at ``i`` a statement with a domain of its own. A conclusion
    with no ``for`` has none.
    """
    from lanky.terms import Forall

    out: list[tuple[tuple[tuple[Any, Any], ...], Any]] = []
    node = goal
    while isinstance(node, Forall) and node.binders:
        out.append((tuple(node.binders), node.guard))
        node = node.body
    return out


def _names(level: tuple[tuple[tuple[Any, Any], ...], Any]) -> list[str]:
    return [var.name for var, _ in level[0]]


def _point_text(names: list[str]) -> str:
    return names[0] if len(names) == 1 else ", ".join(names)


def _source(term: Any) -> str:
    """A term or a sort as Python writes it: ``all(S[n] == n for n in Nat)``, ``Fin[n]``."""
    try:
        from lanky.outline import python_source

        if hasattr(term, "mapper_method"):
            return python_source(term)
    except Exception:  # noqa: BLE001 - a term the printer cannot write is shown as lanky has it
        pass
    try:
        from lanky.outline import _domain_source

        return _domain_source(term)
    except Exception:  # noqa: BLE001 - a sort the printer cannot write is shown as it prints
        return str(term)


def _active() -> Any:
    from lanky.proofs.trace import active

    return active()


def _shown(value: Any) -> str:
    """A value at a point, as a proof writes it."""
    shown = getattr(value, "shown", None)
    if callable(shown):
        return str(shown())
    if hasattr(value, "mapper_method"):
        from lanky.terms import render

        return render(value)
    return repr(value)


class Conclusion:
    """``name.conclusion``: a claim's conclusion, the whole statement or at a point of it.

    ``name.conclusion.domain`` is the domain of its ``for``, which the
    claim's proof loops over; ``name.conclusion[p]`` the conclusion at the
    point ``p`` of that domain, which may have a domain of its own when the
    conclusion nests a ``for`` (``every_box.conclusion[i].domain``). Inside
    the claim's own proof a conclusion is for the inputs of that proof; in
    another proof, for the inputs lanky finds by matching, or those a call
    gave (``other(x, y).conclusion[p]``). Cited in ``by(...)``, it is a fact.

    Attributes:
        claim: The claim it is the conclusion of.
        point: The values given so far, one tuple per nested ``for``.
        inputs: The values of the claim's inputs a call gave, or ``None``.
    """

    __slots__ = ("claim", "inputs", "point")

    def __init__(
        self, claim: Any, point: tuple[tuple[Any, ...], ...] = (), inputs: Any = None
    ) -> None:
        self.claim = claim
        self.point = point
        self.inputs = inputs

    @property
    def _name(self) -> str:
        return getattr(self.claim, "__qualname__", None) or self.claim.__name__

    @property
    def levels(self) -> list[tuple[tuple[tuple[Any, Any], ...], Any]]:
        """The domains the whole conclusion nests (:func:`levels`)."""
        return levels(self.claim.goal)

    @property
    def values(self) -> tuple[Any, ...]:
        """The point given so far, flat: ``(i, a - 2, b + 2)``."""
        return tuple(value for level in self.point for value in level)

    @property
    def domain(self) -> Domain:
        """The domain of the conclusion's ``for`` here: ``for n in name.conclusion.domain:``."""
        found = self.levels
        depth = len(self.point)
        if depth >= len(found):
            if not found:
                raise FormError(
                    f"{self._name}'s conclusion has no for, so it has no domain to loop over; "
                    "a claim proved without a loop ends with return by(...)",
                    "return by(...)",
                )
            raise FormError(
                f"{self.text()} is one statement, at one point, with no domain of its own",
                f"{self._spelled(depth - 1)}.domain",
            )
        return Domain(self)

    def __getitem__(self, point: Any) -> Conclusion:
        """The conclusion at a point of its domain: ``name.conclusion[n - 1]``."""
        values = point if isinstance(point, tuple) else (point,)
        found = self.levels
        depth = len(self.point)
        if depth >= len(found):
            if not found:
                raise FormError(
                    f"{self._name}'s conclusion has no for, so it has no points; cite it whole, "
                    f"as by({self._name})",
                    f"by({self._name})",
                )
            raise FormError(
                f"{self.text()} is one statement, at one point, with no points of its own"
            )
        names = _names(found[depth])
        if len(values) != len(names):
            deeper = [name for level in found[depth + 1 :] for name in _names(level)]
            if deeper and len(values) == len(names) + len(deeper):
                chunks, start = [], 0
                for level in found[depth:]:
                    size = len(_names(level))
                    chunks.append(values[start : start + size])
                    start += size
                nested = "".join(
                    f"[{', '.join(_shown(value) for value in chunk)}]" for chunk in chunks
                )
                raise FormError(
                    f"{self._spelled(depth)}'s points are ({', '.join(names)}), and at each of "
                    f"them the conclusion has a domain of its own over "
                    f"({', '.join(deeper)}); give a point a level at a time",
                    f"{self._spelled(depth)}{nested}",
                )
            raise FormError(
                f"the points of {self._spelled(depth)} are ({', '.join(names)}), and "
                f"{len(values)} {'value is' if len(values) == 1 else 'values are'} given; "
                "give a value for each",
                f"{self._spelled(depth)}[{_point_text(names)}]",
            )
        return Conclusion(self.claim, (*self.point, tuple(values)), self.inputs)

    def _spelled(self, depth: int) -> str:
        """``every_box.conclusion[i]``: the part at ``depth`` levels, its points written by name."""
        head = f"{self._name}.conclusion"
        found = self.levels
        for level in range(min(depth, len(self.point))):
            head += f"[{', '.join(_shown(value) for value in self.point[level])}]"
        for level in range(len(self.point), depth):
            if level < len(found):
                head += f"[{_point_text(_names(found[level]))}]"
        return head

    def text(self) -> str:
        """How the part is written: ``line_taylor.conclusion[n - 1]``, ``gauss(m).conclusion``."""
        head = self._name
        if self.inputs is not None:
            head += f"({', '.join(_shown(value) for value in self.inputs)})"
        head += ".conclusion"
        for level in self.point:
            head += f"[{', '.join(_shown(value) for value in level)}]"
        return head

    def __iter__(self) -> Any:
        """Refuse: the points are its domain's."""
        raise FormError(
            f"{self.text()} is a statement; its points are its domain's",
            f"for {_point_text(self._next_names())} in {self.text()}.domain:",
        )

    def _next_names(self) -> list[str]:
        found = self.levels
        depth = len(self.point)
        return _names(found[depth]) if depth < len(found) else ["n"]

    def __call__(self, *values: Any, **named: Any) -> Any:
        """Refuse: a point is given in brackets, inputs to the claim in parentheses."""
        raise FormError(
            f"{self.text()}(...) gives a conclusion values in parentheses; brackets give a "
            "point of its domain, and parentheses give the claim inputs, as "
            f"{self._name}(...).conclusion",
            f"{self.text()}[{_point_text(self._next_names())}]",
        )

    def __bool__(self) -> bool:
        """Refuse: a conclusion is a fact to cite, not a truth value."""
        raise TypeError(
            f"{self.text()} is a statement to cite, as by({self.text()}), not a truth value"
        )

    def __repr__(self) -> str:
        """``<line_taylor.conclusion: all(...)>``, the statement as Python writes it."""
        goal = self.claim.goal
        said = _source(goal)
        if self.point:
            return f"<{self.text()} of {said}>"
        return f"<{self.text()}: {said}>"


class Domain:
    """``name.conclusion.domain``: the points a conclusion's ``for`` ranges over, in its order.

    Walked only inside the claim's own proof, by the run in progress: one
    symbolic point in a trace, the first points in increasing order in a
    native run. ``reversed(...)`` walks a bounded domain from the top down,
    for an argument that climbs toward a bound.
    """

    __slots__ = ("conclusion",)

    def __init__(self, conclusion: Conclusion) -> None:
        self.conclusion = conclusion

    def _run(self) -> Any:
        conclusion = self.conclusion
        run = _active()
        name = conclusion._name
        if run is None:
            raise OutsideAProof(
                f"{conclusion.text()}.domain is the points {name}'s proof loops over; they are "
                f"walked inside that proof, under lanky check or by {name}.run_proof(...)"
            )
        own = getattr(run, "theorem", None)
        if own is not conclusion.claim:
            mine = getattr(own, "__qualname__", None) or getattr(own, "__name__", "the claim")
            raise FormError(
                f"a proof loops over its own conclusion's domain, and this is {mine}'s proof; "
                f"{name}'s conclusion is cited at a point, as {name}.conclusion[...]",
                f"for ... in {mine}.conclusion.domain:",
            )
        return run

    def __iter__(self) -> Any:
        """The loop over the points, in increasing order."""
        return self._run().loop(self.conclusion, False, sys._getframe(1))

    def __reversed__(self) -> Any:
        """The loop over a bounded domain's points, from the top down."""
        return self._run().loop(self.conclusion, True, sys._getframe(1))

    def __bool__(self) -> bool:
        """Refuse: a domain is looped over, not asked."""
        raise TypeError(f"{self.conclusion.text()}.domain is looped over, not asked for a value")

    def __repr__(self) -> str:
        """``<line_taylor.conclusion.domain: n in Nat if n >= 1>``."""
        found = self.conclusion.levels
        depth = len(self.conclusion.point)
        if depth >= len(found):
            return f"<{self.conclusion.text()}.domain>"
        binders, guard = found[depth]
        said = ", ".join(f"{var.name} in {_source(domain)}" for var, domain in binders)
        if guard is not None:
            said += f" if {_source(guard)}"
        return f"<{self.conclusion.text()}.domain: {said}>"


class Conditions:
    """``name.conditions``: the half of a claim it assumes, each condition by its name.

    ``line_taylor.conditions.ode`` is the condition ``ode``; inside
    ``line_taylor``'s own proof it is the fact ``ode`` names there. The
    conditions of a ``with`` block the claim is defined in are among them,
    first. Its inputs are no conditions: they are given to the claim, as
    ``line_taylor(a)``.
    """

    __slots__ = ("_claim",)

    def __init__(self, claim: Any) -> None:
        self._claim = claim

    @property
    def _names(self) -> list[str]:
        return [name for name, _ in self._claim.hypotheses]

    def __getattr__(self, name: str) -> Any:
        """One condition, by its name."""
        if name.startswith("_"):
            raise AttributeError(name)
        claim = self._claim
        title = getattr(claim, "__qualname__", None) or claim.__name__
        props = dict(claim.hypotheses)
        if name not in props:
            inputs = [variable for variable, _ in claim.variables]
            listed = ", ".join(self._names) or "none"
            if name in inputs:
                raise AttributeError(
                    f"{name} is an input of {title}, not a condition; its conditions are "
                    f"{listed}"
                )
            raise AttributeError(f"{title} has no condition {name}; its conditions are {listed}")
        run = _active()
        if run is not None:
            return run.condition(claim, name, sys._getframe(1))
        return ClaimCondition(claim, name, props[name])

    def __iter__(self) -> Any:
        """The conditions, in order, each a :class:`ClaimCondition`."""
        return iter(
            ClaimCondition(self._claim, name, prop) for name, prop in self._claim.hypotheses
        )

    def __len__(self) -> int:
        """How many conditions the claim has."""
        return len(self._claim.hypotheses)

    def __dir__(self) -> list[str]:
        """The conditions' names, for a REPL's completion."""
        return self._names

    def __repr__(self) -> str:
        """``<line_taylor.conditions: first_term, ode>``."""
        title = getattr(self._claim, "__qualname__", None) or self._claim.__name__
        return f"<{title}.conditions: {', '.join(self._names) or 'none'}>"


class ClaimCondition:
    """One condition of a claim, read outside a proof: its name and what it says.

    Attributes:
        claim: The claim it is a condition of.
        name: Its name, the parameter's.
        prop: What it says, as a term.
    """

    __slots__ = ("claim", "name", "prop")

    def __init__(self, claim: Any, name: str, prop: Any) -> None:
        self.claim = claim
        self.name = name
        self.prop = prop

    def text(self) -> str:
        """``line_taylor.conditions.ode``."""
        title = getattr(self.claim, "__qualname__", None) or self.claim.__name__
        return f"{title}.conditions.{self.name}"

    def __repr__(self) -> str:
        """``<line_taylor.conditions.ode: all(...)>``."""
        return f"<{self.text()}: {_source(self.prop)}>"


# }}}
