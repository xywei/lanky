"""``python -m lanky.mathlib DIR``: set up the pinned Mathlib project.

The command is :func:`lanky.mathlib.main`, run from a module of its own:
``python -m`` imports the package ``lanky`` before it runs anything, and
``import lanky`` imports :mod:`lanky.mathlib`, since the Lean oracle and
:mod:`lanky.semantics` read the project from it. When the command was
``lanky/mathlib.py`` run as ``__main__``, Python ran a second copy of a module
it had already imported, and said so first in a ``RuntimeWarning`` from runpy
(#162). Nothing imports this module, so running it warns of nothing.
"""

from __future__ import annotations

from lanky.mathlib import main

if __name__ == "__main__":
    raise SystemExit(main())
