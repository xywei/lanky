"""The oracles lanky ships, and their registration.

The design idea. An oracle is the only thing that can improve a fact's status,
and it must say how much it should be trusted. lanky ships three: a Lean oracle
(kernel evidence, available only when Lean is installed), a computer-algebra
oracle (a heuristic, available only when sympy is installed) and the property
tester (evidence, not proof). A plugin such as loopty adds a decision procedure
between the first two. ``lanky check`` tries them from the strongest trust class
that is willing to take the fact to the weakest, so a proved fact is never
merely tested.

Importing this package registers the three in :data:`lanky.plugins.registry`.
Neither Lean's driver nor sympy is imported with it.
"""

from __future__ import annotations

from lanky.oracles.cas import CasOracle
from lanky.oracles.lean import LeanOracle
from lanky.oracles.test import TestOracle
from lanky.plugins import registry

__all__ = ["CasOracle", "LeanOracle", "TestOracle"]

registry.register_oracle(LeanOracle())
registry.register_oracle(CasOracle())
registry.register_oracle(TestOracle())
