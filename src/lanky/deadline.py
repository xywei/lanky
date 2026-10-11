"""A deadline for Python work an oracle does, kept by an interval timer.

The design idea. An oracle that runs another program, Lean, keeps a timeout by
waiting for it; an oracle whose work is Python, sympy's simplification or the
search for an induction's certificate, has to be interrupted in the middle of
it. The interval timer does that: ``SIGALRM`` arrives, and its handler raises
:class:`Expired` in whatever Python code is running. The CAS oracle gives each
fact a deadline (:mod:`lanky.oracles.cas`), and the Lean oracle gives the
search it runs before its attempts what is left of the fact's budget
(:mod:`lanky.oracles.lean`).

The timer is the process's, so the deadline holds only where it can be owned:
in the main thread of a POSIX process, which is where ``lanky check`` and
pytest run the oracles, and when no other interval timer is running, which it
would clobber. Elsewhere the block runs without one. An evaluation that is one
long operation in C does not return to the interpreter while it runs, and the
handler runs only after it.
"""

from __future__ import annotations

import signal
import threading
from collections.abc import Iterator
from contextlib import contextmanager
from typing import Any

__all__ = ["Expired", "deadline"]


class Expired(BaseException):
    """The work ran past its deadline.

    A ``BaseException``, as ``KeyboardInterrupt`` is, so that no ``except
    Exception`` inside sympy, or inside a plugin's certificate hook, takes it
    for a failure of its own and goes on. :attr:`owner` is what the deadline
    was set for, so that a caller can tell its own deadline from one set
    around it.
    """

    def __init__(self, owner: Any = None) -> None:
        super().__init__(owner)
        #: The ``owner`` the deadline was set with (see :func:`deadline`).
        self.owner = owner


@contextmanager
def deadline(seconds: float | None, owner: Any = None) -> Iterator[None]:
    """Raise :class:`Expired` in the block once ``seconds`` have passed, where that can be done.

    That is in the main thread of a process with ``signal.setitimer`` and no
    interval timer of its own running, which would be clobbered. Elsewhere the
    block runs without a deadline, and so it does when the timer will not
    take ``seconds``: a deadline too long for it to hold, or one that is not a
    number, and ``None``, ``0`` or a negative number, which ask for none.
    Either way the ``SIGALRM`` handler is the one there was before, once the
    block is over or the timer has refused.

    What is raised carries ``owner`` (:attr:`Expired.owner`): a caller that
    catches its own deadline checks it, since an :class:`Expired` raised in
    the block can be a deadline's set around it, under which this one sets no
    timer. A timer that goes off as the block ends raises as the timer is
    stopped, and the handler there was is put back all the same.
    """
    if (
        not seconds
        or seconds <= 0
        or not hasattr(signal, "setitimer")
        or threading.current_thread() is not threading.main_thread()
        or signal.getitimer(signal.ITIMER_REAL)[0] > 0
    ):
        yield
        return

    def expire(signum: int, frame: Any) -> None:
        raise Expired(owner)

    previous = signal.signal(signal.SIGALRM, expire)
    try:
        signal.setitimer(signal.ITIMER_REAL, seconds)
    except (OverflowError, ValueError, OSError):
        signal.signal(signal.SIGALRM, previous)
        yield
        return
    try:
        yield
    finally:
        try:
            # the handler runs here if the timer went off as the block ended
            signal.setitimer(signal.ITIMER_REAL, 0)
        finally:
            signal.signal(signal.SIGALRM, previous)
