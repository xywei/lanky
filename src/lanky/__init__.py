"""lanky: a Python-hosted proof language with Lean 4 as the platform.

lanky is shaped like mypy: hints are inert, the body is executable Python, and an
external command does the checking. A theorem is a typed Python function whose
parameters are its variables and hypotheses and whose return annotation is its
goal. Annotations are not parsed, they are *evaluated*, in a scope where unknown
names become symbolic variables, so a dependent hint such as
``Fn[Fin[n + 1], Nat]`` is an ordinary Python expression. The same annotation,
evaluated at concrete values, is a ``bool``, which is why every theorem is also a
property test and the file still runs under plain ``python``.

What lanky itself owns is small: terms, the prelude of sorts and index types, a
ledger of facts (each with a status: tested, decided, proved, certified, assumed,
refuted) and four plugin interfaces (theories, oracles, executors, CLI verbs)
discovered through entry points. Lean is an oracle and the property tester is an
oracle; a polyhedral plugin such as loopty registers its own theory, its own
decision procedure, and its own verbs, and lanky never imports it.

Three commands over one file: ``python file.py`` runs it, ``pytest`` tests the
theorems, ``lanky check file.py`` prints the ledger of every claim and who
decided it.
"""

from __future__ import annotations

import lanky.oracles  # noqa: F401 - importing lanky registers the built-in oracles
from lanky.check import check_path
from lanky.ledger import Fact, Ledger, Status, Support, fact_id
from lanky.plugins import Executor, Oracle, Registry, Theory, Verb, registry
from lanky.prelude import Bool, Fin, Fn, Int, Nat, Prop, Real, Sort
from lanky.terms import (
    Abs,
    Exists,
    Forall,
    Scope,
    Sum,
    Undecided,
    Var,
    abs_,
    evaluate,
    exists,
    forall,
    render,
)
from lanky.terms import sum_ as sum  # noqa: A004 - lanky.sum is a reduction term
from lanky.theory import Theorem, theorem

__version__ = "0.1.0.dev0"

__all__ = [
    "Abs",
    "Bool",
    "Executor",
    "Exists",
    "Fact",
    "Fin",
    "Fn",
    "Forall",
    "Int",
    "Ledger",
    "Nat",
    "Oracle",
    "Prop",
    "Real",
    "Registry",
    "Scope",
    "Sort",
    "Status",
    "Sum",
    "Support",
    "Theorem",
    "Theory",
    "Undecided",
    "Var",
    "Verb",
    "__version__",
    "abs_",
    "check_path",
    "evaluate",
    "exists",
    "fact_id",
    "forall",
    "registry",
    "render",
    "sum",
    "theorem",
]
