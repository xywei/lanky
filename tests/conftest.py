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

import pytest

pytest_plugins = ["pytester"]

#: The Mathlib project the suite was started with, or ``None``.
MATHLIB_PROJECT = os.environ.pop("LANKY_LEAN_MATHLIB", None) or None


@pytest.fixture(scope="session")
def mathlib_project() -> str | None:
    """The Lake project with Mathlib that ``LANKY_LEAN_MATHLIB`` named, or ``None``."""
    return MATHLIB_PROJECT
