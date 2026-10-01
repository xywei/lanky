"""Test configuration: pytest's test-runner fixture, and core Lean unless asked.

``LANKY_LEAN_MATHLIB`` switches the Lean oracle to Mathlib mode (see
:mod:`lanky.mathlib`), and the suite is written for core Lean: the documented
ledgers read ``tested`` for Gauss's sum, which Mathlib proves. So the variable
is taken out of the environment before any test runs, whatever the shell that
started the suite exported, and handed to the tests in ``tests/test_mathlib.py``
through the ``mathlib_project`` fixture; those set it again where they want
Mathlib mode, and skip when there is none.
"""

from __future__ import annotations

import os
import time

import pytest

pytest_plugins = ["pytester"]

#: The Mathlib project the suite was started with, or ``None``.
MATHLIB_PROJECT = os.environ.pop("LANKY_LEAN_MATHLIB", None) or None


@pytest.fixture(scope="session")
def mathlib_project() -> str | None:
    """The Lake project with Mathlib that ``LANKY_LEAN_MATHLIB`` named, or ``None``."""
    return MATHLIB_PROJECT


#: Whether this system has ``/proc``, where a process's start time is read.
_PROC = os.path.exists("/proc/self/stat")


def _stat_fields(pid: int) -> list[str] | None:
    """The fields of ``/proc/<pid>/stat`` from the third on, or ``None`` if it cannot be read.

    They follow the command's closing bracket, since a command may hold spaces
    and brackets: the state is the first, and the start time, field 22, the
    twentieth.
    """
    try:
        with open(f"/proc/{pid}/stat", encoding="utf-8") as handle:
            fields = handle.read().rsplit(")", 1)[1].split()
    except (OSError, IndexError):
        return None
    return fields if len(fields) > 19 else None


class ProcessWatch:
    """Whether one process has ended, asked so that the answer cannot flip back (#53).

    The child-process tests watched a pid and failed now and then on a busy
    machine, after a run of three seconds, saying that a process had outlived
    its deadline. Their watcher read ``os.kill(pid, 0)`` and then
    ``/proc/<pid>/stat``, and counted a process as alive where the second
    could not be read. A process that ends is a zombie until it is reaped,
    and while it is reaped there is a moment in which ``kill`` still finds it
    and its ``/proc`` entry is already gone: the loop that waited saw the
    zombie and stopped, and the assertion after it asked again, in that
    moment, and read the process as running. Here an entry that cannot be
    read, where there is a ``/proc``, is a process that has gone, and
    :meth:`wait` answers once.

    Two more ways a pid can mislead are closed while at it. A pid another
    user's process took raised ``PermissionError``, and is a process that has
    ended. And one the same user's process took read as the watched one, so
    the start time is read when the watch begins, while the process is known
    to be there, and a pid with another start time since is a process that
    has ended. Where there is no ``/proc`` a process is gone when its pid is.
    """

    def __init__(self, pid: int) -> None:
        self.pid = pid
        fields = _stat_fields(pid) if _PROC else None
        self.started = fields[19] if fields is not None else None

    def gone(self) -> bool:
        """Whether the process has ended; one ended and not yet reaped counts."""
        try:
            os.kill(self.pid, 0)
        except ProcessLookupError:
            return True
        except PermissionError:  # the pid is another user's process now
            return True
        if not _PROC:  # alive, as far as can be told
            return False
        fields = _stat_fields(self.pid)
        if fields is None:  # reaped while it was looked at
            return True
        return fields[0] == "Z" or (self.started is not None and fields[19] != self.started)

    def wait(self, timeout: float) -> bool:
        """Whether the process ends within ``timeout`` seconds."""
        deadline = time.monotonic() + timeout
        while not self.gone():
            if time.monotonic() > deadline:
                return False
            time.sleep(0.05)
        return True

    def kill(self) -> None:
        """End the process, if it has not ended, and nothing else that took its pid."""
        import signal

        if not self.gone():
            try:
                os.kill(self.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
