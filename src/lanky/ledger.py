"""The ledger of facts.

PREPARED, NOT IMPLEMENTED.

The ledger is lanky's single source of truth about what is known and how strongly
it is known. Every claim a lanky program makes -- a theorem, a side condition
discharged by a decision procedure, an assumption deliberately left open -- becomes
a :class:`Fact` carrying a :class:`Status`. Plugins (theories, oracles, executors)
read and write facts; CLI verbs report on them.

Nothing here does any work yet: this module fixes the vocabulary that the rest of
lanky will be built against.
"""

from __future__ import annotations

import enum
from dataclasses import dataclass, field


class Status(enum.Enum):
    """How strongly a :class:`Fact` is established.

    The members are ordered from weakest to strongest evidence:

    ``TESTED``
        The statement survived execution as a property test under plain ``python``.
        Evidence, not proof.
    ``DECIDED``
        A decision procedure (an oracle such as isl, an SMT solver, or a Lean
        ``decide``) answered affirmatively, trusted at that oracle's trust class.
    ``PROVED``
        A proof was found and accepted by the platform, but no reproducible
        artifact has been retained.
    ``CERTIFIED``
        A proof was found and a certificate was recorded -- for the Lean platform,
        a generated Lean file plus a source map back to the Python program -- so
        the claim can be rechecked by the Lean kernel independently of lanky.
    ``ASSUMED``
        Deliberately taken on faith: an axiom, a ``sorry``, or an interface
        contract owed by someone else. Tracked so it can never be silently lost.
    """

    TESTED = "tested"
    DECIDED = "decided"
    PROVED = "proved"
    CERTIFIED = "certified"
    ASSUMED = "assumed"


@dataclass(frozen=True)
class Fact:
    """A single entry in the ledger.

    Attributes:
        statement: The claim itself, rendered as source text (Lean syntax on the
            Lean platform).
        status: How strongly the claim is established; see :class:`Status`.
        decided_by: Name of the oracle or executor that established the claim, or
            ``None`` when nothing has established it yet (e.g. a pure assumption).
        provenance: Free-form record of where the claim came from and how it was
            checked -- source location, tactic script, certificate path, oracle
            version, trust class, timing. Left untyped on purpose while the
            architecture settles.
    """

    statement: str
    status: Status
    decided_by: str | None = None
    provenance: dict = field(default_factory=dict)
