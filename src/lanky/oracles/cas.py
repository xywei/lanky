"""The computer-algebra oracle: an identity a simplifier takes to zero.

The design idea. Much of what a numerical code claims is an identity between
two formulas: a recurrence and the direct formula it stands for, a translation
and the series it re-expands. A computer algebra system settles most such
claims at a fixed size in a moment, by simplifying the difference of the two
sides to zero, and a test of the code usually does exactly that. The ledger
should say so, and say how much it is worth: a simplifier is neither a proof,
nor a decision procedure, since it can fail to see that a true identity holds
and its answers are not guaranteed. Its trust class is ``heuristic`` (see
:data:`lanky.plugins.TRUST_STRENGTH`), so a fact it decides reads
``decided (heuristic)``, a counterexample the property tester finds overrules
it, and it is never asked whether a fact's hypotheses are inconsistent.

The oracle takes a statement that asserts equations, alone, in a conjunction,
or under universal quantifiers whose variables range over numbers, and whose
sides are arithmetic with ``exp``, ``log``, ``sqrt`` and ``abs``; the fragment,
and how each variable's sort becomes a sympy assumption, is
:mod:`lanky.cas`'s. For each equation it asks ``sympy.simplify`` for the
difference of the two sides, and decides the statement when every difference
is ``0``. It answers nothing else. A difference that does not simplify to
``0`` is not a counterexample, since sympy may simply not have found the
identity, so the fact is declined with the difference in the reason, and the
property tester, which can refute, is asked next.

The hypotheses are not read: an identity that holds for every value of its
variables holds wherever they do. And what sympy decides is read at the points
Python evaluates a statement at. A real logarithm or square root is taken only
where sympy can show that its argument is not negative, so neither is read as
a complex number Python never computes, and where a denominator or a
logarithm's argument is zero Python raises and the readings are not compared
(see :mod:`lanky.cas`).

Simplification can take long on a large expression, and so can building it:
sympy's constructors evaluate as they build. Each fact gets
``LANKY_CAS_TIMEOUT`` seconds (60 by default) for both, the translation of the
statement into sympy and the simplification, after which it is declined, as a
Lean attempt that runs out of time is; before the deadline only the
statement's shape is read, which builds nothing (#77). The deadline is an
interval timer, so it holds where the check runs in the main thread of a POSIX
process, which is where ``lanky check`` runs it, and it is not set elsewhere or
when another timer is already running. An evaluation that is one long
operation in C, such as an integer power of a number sympy has just folded,
``(x - x + 3) ** 10**10``, does not return to the interpreter while it runs,
and the timer is heard only after it; the property tester would compute the
same power.

The oracle is available where sympy imports, the ``cas`` extra, and
``LANKY_CAS_DISABLE=1`` makes it a declared no-op, as ``LANKY_LEAN_DISABLE``
does Lean's. sympy is imported on the first fact, not with lanky.
"""

from __future__ import annotations

import math
import os
import time
from importlib.metadata import PackageNotFoundError, version
from importlib.util import find_spec

import pymbolic.primitives as prim

from lanky.cas import Untranslatable, check_shape, equations, sympy_module
from lanky.deadline import Expired, deadline
from lanky.ledger import Fact, Status
from lanky.terms import render

__all__ = ["DEFAULT_TIMEOUT", "CasOracle"]

#: Seconds the simplifier may take over one fact before it is declined, unless
#: ``LANKY_CAS_TIMEOUT`` says otherwise.
DEFAULT_TIMEOUT = 60.0

#: How much of a term or a difference a reason quotes.
_QUOTED = 160


#: The deadline each fact gets (see :mod:`lanky.deadline`), and what it raises.
_deadline = deadline
_Expired = Expired


def _quoted(text: str) -> str:
    """``text`` on one line, shortened to what a reason quotes."""
    text = " ".join(str(text).split())
    return text if len(text) <= _QUOTED else text[: _QUOTED - 3] + "..."


def _sympy_version() -> str | None:
    """The installed sympy's version, read without importing it."""
    try:
        return version("sympy")
    except PackageNotFoundError:
        return None


class CasOracle:
    """Decide an identity by simplifying the difference of its sides to zero, with sympy."""

    name = "cas"

    def __init__(self, timeout: float | None = None) -> None:
        #: Seconds per fact; ``None`` reads ``LANKY_CAS_TIMEOUT`` when a fact is offered.
        self.timeout = timeout

    def trust_class(self) -> str:
        """A simplifier, whose answers are not guaranteed: ``heuristic``."""
        return "heuristic"

    def availability(self) -> tuple[bool, str]:
        """Whether sympy is here to be asked, and the one-line reason if not.

        Answered without importing sympy, which takes a moment, so ``lanky
        check`` does not pay for it to print a status line.
        """
        if os.environ.get("LANKY_CAS_DISABLE"):
            return False, "disabled by LANKY_CAS_DISABLE"
        if find_spec("sympy") is None:
            return False, 'sympy is not installed (pip install "lanky[cas]")'
        installed = _sympy_version()
        return True, f"sympy {installed}" if installed else ""

    def can_establish(self, fact: Fact, /) -> bool:
        """Whether the fact asserts equations of a shape the bridge takes (see :mod:`lanky.cas`).

        Only the shape is read, the sorts and the nodes
        (:func:`lanky.cas.check_shape`), and nothing is translated: sympy
        evaluates as it builds, so a translation can take time, and that is
        done in :meth:`establish`, within the deadline (#77). A real
        logarithm or square root whose argument sympy cannot show is not
        negative is refused by the translation, so such a statement is taken
        here and declined there, with the reason.
        """
        if not isinstance(fact.term, prim.ExpressionNode):
            return False
        try:
            check_shape(fact.term)
        except Untranslatable:
            return False
        return True

    def _seconds(self) -> float:
        """The deadline for one fact, in seconds.

        Raises:
            ValueError: If ``LANKY_CAS_TIMEOUT`` is not a finite number,
                ``nan`` and ``inf`` included, which :meth:`establish`
                declines the fact for, saying so.
        """
        if self.timeout is not None:
            return self.timeout
        given = os.environ.get("LANKY_CAS_TIMEOUT")
        if given is None:
            return DEFAULT_TIMEOUT
        try:
            seconds = float(given)
        except ValueError:
            seconds = math.nan
        if not math.isfinite(seconds):
            raise ValueError(
                f"LANKY_CAS_TIMEOUT is {given!r}, which is not a finite number of seconds"
            )
        return seconds

    def establish(self, fact: Fact, /) -> Fact | None:
        """``DECIDED`` when sympy takes every equation's difference to ``0``; declined otherwise.

        A decision records the number of equations as ``cas_equations``, the
        seconds it took as ``cas_seconds``, and sympy's version as
        ``cas_version``. A decline, of a statement outside the fragment, of an
        equation whose difference sympy leaves at something other than ``0``,
        or of a fact the deadline cut short, carries the reason as
        ``declined`` (see :func:`lanky.cli.decline_lines`).

        The deadline covers the translation of the statement into sympy as
        well as the simplification (#77): sympy's constructors evaluate as
        they build, and a large statement spent its time there before the
        timer was armed. An evaluation that is one long operation in C, an
        integer power of a number sympy has just folded, does not return to
        the interpreter, and the timer is heard only after it.

        The fact's deadline is its own (:attr:`lanky.deadline.Expired.owner`):
        a deadline set around the oracle, under which this one sets no timer,
        is its caller's, and what it raises is raised again, not taken for
        sympy running out of time.
        """
        try:
            check_shape(fact.term)
            sympy = sympy_module()
        except (Untranslatable, ImportError) as exc:
            return self._declined(fact, str(exc))
        try:
            seconds = self._seconds()
        except ValueError as exc:
            return self._declined(fact, str(exc))
        started = time.monotonic()
        translating = True
        owner = object()
        try:
            with _deadline(seconds, owner):
                found = equations(fact.term)
                translating = False
                for equation in found:
                    difference = sympy.simplify(equation.left - equation.right)
                    if difference != 0:
                        return self._declined(
                            fact,
                            f"sympy simplifies the difference of the sides of "
                            f"{_quoted(render(equation.term))} to {_quoted(difference)}, "
                            "not 0",
                        )
        except _Expired as exc:
            if exc.owner is not owner:
                raise
            if translating:
                return self._declined(
                    fact, f"sympy did not finish translating the statement within {seconds:g} s"
                )
            return self._declined(fact, f"sympy did not finish within {seconds:g} s")
        except Untranslatable as exc:
            return self._declined(fact, str(exc))
        except Exception as exc:  # noqa: BLE001 - a simplifier that fails declines
            return self._declined(fact, f"sympy raised {type(exc).__name__}: {_quoted(exc)}")
        return fact.with_status(
            Status.DECIDED,
            self.name,
            cas_equations=len(found),
            cas_seconds=round(time.monotonic() - started, 3),
            cas_version=f"sympy {sympy.__version__}",
        )

    def _declined(self, fact: Fact, reason: str) -> Fact:
        """The fact unchanged, with why the simplifier did not decide it."""
        return fact.with_status(fact.status, declined=f"{self.name}: {reason}")
