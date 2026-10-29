# Evidence supplied by plugins

A plugin can describe a transformation and check its evidence without adding a
new lanky status, importing a compiler into lanky, or requiring Lean. Use a Fact
with the actual predicate in `term`, checker details in `provenance`, and every
prerequisite fact ID in `rests_on`. The theory chooses its vocabulary and an
oracle implements `can_establish`, `establish` and `trust_class`.

The plugin owns the correspondence between its statement and the input/output
objects. Check schema, input/output identity, assumptions, target/numeric
semantics and relevant tool versions before consuming evidence. Identities
prevent stale replay; a matching hash does not establish the predicate. An
independent checker must reconstruct or validate the claimed relation against
the actual objects, not merely accept the producer's success flag. Keep the
untrusted producer's choices separate from hypotheses of the statement.

Record what was checked. A backend decision is `decided` at the audited oracle's
trust class for that particular predicate. An independent decision can establish
the same claim with its own provenance. Lean acceptance is `proved` for the
statement Lean checked. A proof's strength about the source still depends on
source reading, correspondence and call contracts through `rests_on`; inspect
`Ledger.support` and the JSON's `effective` field, not status alone.

Missing prerequisites stay assumed. Refuted prerequisites cannot support a
successful chain. Include the prerequisite facts in the ledger when available;
a nicer label for a missing fact does not establish it. Preserve earlier scope
information when a stronger oracle checks the fact. Do not replace a claim with
a broader one when upgrading its status.

Return an unchanged/assumed fact with `declined` for an unsupported statement or
unavailable evidence. A timeout is not a counterexample. An exception caught by
`establish` is recorded as `raised`, with its oracle and exception type, while
other applicable oracles may still answer. Explicitly invalid evidence may be
refuted as an evidence-validity claim; that alone need not refute the underlying
mathematical proposition. Keep those claims distinct in user-facing facts.

`certified` retains its existing requirement: a proof artifact that can be
rechecked independently of lanky. A JSON record, digest, successful compilation
or a sampled agreement is not that artifact. Lanky trusts plugin implementations
to obey the status contract; it does not automatically authenticate an arbitrary
plugin's claimed proof or decide compiler-specific validity. Introduce a generic
artifact/replay facility only when a real artifact needs one.

`tests/test_plugin_evidence.py` provides a compiler-free fixture for the existing
contract, covering multiple prerequisites, stale evidence, unsupported schemas,
exceptions and preservation of scope through a stronger oracle. The fake prover
tests dispatch only and supplies no mathematical proof. A real plugin must test
its independent statement construction and checker against corrupted evidence.

Missing canonical claim IDs have readable display names in the table, qualified
when names collide. This is only presentation: `under` and `rests_on` retain the
full IDs in JSON, and a missing fact remains unresolved. Plugin-specific IDs
keep their original spelling unless an actual fact supplies a label.

A test oracle that counts coverage of a universal goal should record
`goal_reached` as a nonnegative integer, including positive counts. Zero means
no sampled draw reached the guarded body; an absent count means coverage was
not measured. If a tester settles a fact without this count, lanky asks later
testers for it while preserving the first verdict, decider and sample counts.
A later counterexample is recorded as a semantics disagreement. Zero coverage
triggers the existing guard-emptiness check and warning; it is not by itself a
proof that the goal is vacuous.
