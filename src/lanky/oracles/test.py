"""The property-test oracle: the weakest oracle, and the one always available.

The design idea. A statement whose variables have sorts is a predicate, so it
can be sampled. That is evidence and not proof, which is exactly what the trust
class ``test`` records in the ledger. Its real value is the other direction: a
counterexample is definite, so this oracle is the one that can answer
``REFUTED``, and it carries the counterexample in the fact's provenance where a
reader can see it.

A pass over zero valid draws establishes nothing, so in that case the oracle
leaves the status alone, records ``untested`` and the reason in the fact's
provenance, and the fact is reported as ``ASSUMED`` rather than as a vacuous
pass.
"""

from __future__ import annotations

import pymbolic.primitives as prim

from lanky.ledger import Fact, Status
from lanky.terms import Forall, conjuncts
from lanky.testing import check

__all__ = ["TestOracle"]


class TestOracle:
    """Establish facts by sampling them."""

    name = "property-test"

    #: Not a pytest test class, despite the name.
    __test__ = False

    def __init__(self, samples: int = 200, seed: int = 0) -> None:
        self.samples = samples
        self.seed = seed

    def trust_class(self) -> str:
        """Evidence from execution, the weakest class."""
        return "test"

    def can_establish(self, fact: Fact, /) -> bool:
        """Willing to try any fact that has a term to evaluate."""
        return isinstance(fact.term, prim.ExpressionNode)

    def establish(self, fact: Fact, /) -> Fact | None:
        """Sample the fact's term; ``TESTED``, ``REFUTED``, or decline."""
        term = fact.term
        if isinstance(term, Forall):
            variables = [(var.name, domain) for var, domain in term.binders]
            hypotheses = list(conjuncts(term.guard))
            goal = term.body
        else:
            variables, hypotheses, goal = [], [], term
        try:
            report = check(variables, hypotheses, goal, self.samples, self.seed)
        except Exception as exc:  # noqa: BLE001 - an oracle that cannot run declines
            return fact.with_status(
                fact.status, reason=f"{self.name} could not run: {exc}"
            )
        if not report.ok:
            return fact.with_status(
                Status.REFUTED,
                self.name,
                counterexample=report.counterexample,
                samples=report.samples,
                valid=report.valid,
                reason=report.reason,
            )
        if report.valid == 0:
            # A pass over no valid draw is not evidence, so the status must not
            # improve. Returning the fact with the reason rather than ``None``
            # keeps the attempt in the ledger: the row stays ``ASSUMED`` and
            # says why nothing tested it. A draw the statement could not be
            # answered at (an unwitnessed existential over a sampled domain)
            # lands here too, which is the point: it is not a refutation.
            return fact.with_status(
                fact.status,
                untested=report.reason or "no draw satisfied the hypotheses",
                samples=report.samples,
                valid=0,
                undecided=report.undecided or None,
                skipped=report.skipped or None,
            )
        extra = {"undecided": report.undecided} if report.undecided else {}
        return fact.with_status(
            Status.TESTED,
            self.name,
            samples=report.samples,
            valid=report.valid,
            **extra,
        )
