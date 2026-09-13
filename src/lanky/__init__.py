"""lanky: a Python-hosted proof language with Lean 4 and Mathlib as the platform.

lanky is shaped like mypy: hints are inert, the body is executable Python, and an
external command does the checking. Theorems are typed Python functions (variables
are parameters, hypotheses are parameters annotated with propositions, the goal is
the return annotation); proofs are Python programs that drive Lean tactics over a
live goal; the recorded tactic script is the certificate; under plain ``python`` the
theorems run as property tests. Lean is the platform and lanky is a hosted language
on it -- the Kotlin/JVM relationship -- so all of Mathlib and every Lean tactic are
reachable. lanky itself is a thin plugin host: it defines a ledger of facts (each
with a status: tested, decided, proved, certified, assumed) and four plugin
interfaces (theories, oracles, executors, CLI verbs).

This is a placeholder release to reserve the name. The architecture is prepared,
not implemented.
"""

__version__ = "0.0.1"

__all__ = ["__version__"]
