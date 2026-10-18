"""lanky: a Python-hosted proof language with Lean 4 as the platform.

lanky is shaped like mypy: hints are inert, the body is executable Python, and an
external command does the checking. A claim, ``@claim``, is a typed Python
function whose parameters are its variables and conditions and whose return
annotation is its goal; a named set of conditions several claims share is a
``@condition``, and the claims of a ``with`` block of it hold under it.
Annotations are not parsed, they are *evaluated*, in a scope where unknown
names become symbolic variables, so a dependent hint such as
``Fn[Fin[n + 1], Nat]`` is an ordinary Python expression. The same annotation,
evaluated at concrete values, is a ``bool``, which is why every claim is also a
property test and the file still runs under plain ``python``.

What lanky itself owns is small: terms, the prelude of sorts and index types, a
ledger of facts (each with a status: tested, decided, proved, certified, assumed,
refuted; and the facts it rests on, which bound what it is worth) and four
plugin interfaces (theories, oracles, executors, CLI verbs) discovered through
entry points. Lean is an oracle, sympy is one where it is installed, a
simplifier whose answers the ledger marks as a heuristic's, and the property
tester is one; a polyhedral plugin such as loopty registers its own theory,
its own decision procedure, and its own verbs, and lanky never imports it. A
result lanky cannot establish enters on a source, through ``@claim(cite=...)``, and a
transformation some other tool made enters as a rewrite, through
``@rewrite``: a source, a target, and the obligation between them that an
oracle discharges.

Three commands over one file: ``python file.py`` runs it, ``pytest`` tests the
claims, ``lanky check file.py`` prints the ledger of every claim and who
decided it.

Where a proof helps, the claim's body is the proof, in the Python an
engineer already writes: ``assert x == y, by(f)`` for a step, ``if`` for
cases, ``for n in name.conclusion.domain:`` and ``yield by(...)`` for each
point of the conclusion (see :mod:`lanky.proofs`).
"""

from __future__ import annotations

import lanky.oracles  # noqa: F401 - importing lanky registers the built-in oracles
from lanky.check import check_path
from lanky.conditions import Condition, ConditionNotMet, Conditions, condition
from lanky.ledger import Fact, Ledger, Status, Support, fact_id
from lanky.plugins import Executor, Oracle, Registry, Theory, Verb, registry
from lanky.prelude import Bool, Complex, Fin, Fn, Int, Nat, Prop, Real, Sort
from lanky.rewrites import Rewrite, RewriteTerm, rewrite
from lanky.surface import by
from lanky.terms import (
    Abs,
    Elementary,
    Exists,
    Forall,
    Scope,
    Sum,
    Undecided,
    Var,
    abs_,
    conj,
    evaluate,
    exists,
    exp,
    forall,
    imag,
    log,
    real,
    render,
    sqrt,
)
from lanky.terms import sum_ as sum  # noqa: A004 - lanky.sum is a reduction term
from lanky.theory import Axiom, CitedClaim, Claim, Theorem, axiom, claim, theorem

__version__ = "0.5.0"

__all__ = [
    "Abs",
    "Axiom",
    "Bool",
    "CitedClaim",
    "Claim",
    "Complex",
    "Condition",
    "ConditionNotMet",
    "Conditions",
    "Elementary",
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
    "Rewrite",
    "RewriteTerm",
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
    "axiom",
    "by",
    "check_path",
    "claim",
    "condition",
    "conj",
    "evaluate",
    "exists",
    "exp",
    "fact_id",
    "forall",
    "imag",
    "log",
    "registry",
    "render",
    "real",
    "rewrite",
    "sqrt",
    "sum",
    "theorem",
]
