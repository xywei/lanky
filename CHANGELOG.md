# Changelog

All notable changes to lanky are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions follow
[PEP 440](https://peps.python.org/pep-0440/).

## [0.1.0.dev0] - 2026-09-18

The first release in which something works. `lanky check FILE` imports a file,
turns every decorated object into facts, asks the oracles strongest first, and
prints a ledger naming who decided what.

### Added

- **Terms** (`lanky.terms`). Every lanky term is a subclass of an ordinary
  pymbolic node, so `off(0) == 0` inside an annotation builds a `Comparison`
  rather than answering a bool, and `&`, `|`, `~` build the connectives. Four
  nodes are new: `Forall`, `Exists`, `Sum` (a generator reduction) and `Abs`.
  `Scope` is a dict whose `__missing__` invents a variable, and
  `evaluate_annotations` evaluates a function's annotations in it with
  `all`, `any`, `sum` and `abs` replaced by the quantifiers and the reduction.
- **Prelude** (`lanky.prelude`). Sorts `Nat`, `Int`, `Bool` (exact), `Real`
  (approx) and `Prop`, each carrying an exactness class; the index type `Fin[n]`,
  concrete or symbolic; function types `Fn[A, B]`; and refinement by `T & prop`.
- **Ledger** (`lanky.ledger`). `Status` is `tested, decided, proved, certified,
  assumed, refuted`. A `Fact` carries its statement, its term, its status, its
  decider, its provenance and its source location. `Ledger.render()` prints the
  fixed-width table; `Ledger.to_json()` serialises it.
- **Plugin host** (`lanky.plugins`). Theories, oracles, executors and CLI verbs,
  discovered through the `lanky.theories`, `lanky.oracles`, `lanky.executors`
  and `lanky.verbs` entry-point groups. Oracles report a trust class
  (`kernel` > `decision-procedure` > `test`) and answer `can_establish(fact)`.
- **Theorems** (`lanky.theory`). `@theorem` reads a sequent off the signature:
  parameters annotated with sorts are variables, parameters annotated with
  propositions are hypotheses, the return annotation is the goal. The decorated
  object is inert and callable, and offers `.statement`, `.term`, `.fact()`,
  `.test()`, `.report()` and `.lean()`.
- **Property testing** (`lanky.testing`). Samplers per sort, `Fraction` for the
  exact sorts, tables for function parameters. Definitional hypotheses such as
  `off(0) == 0` and a scan recurrence are *satisfied* by construction rather than
  rejection-sampled, so a theorem about a scan is genuinely tested. A pass with
  no valid draws is not evidence and the oracle declines it.
- **Lean oracle** (`lanky.oracles.lean`, `lanky.lean`). A printer from lanky
  terms to core Lean 4, and an oracle over lean-interact that elaborates one
  declaration per attempt down a ladder of `omega`, `decide`, `simp`, `simp_all`,
  two intro-plus-closer scripts and an induction strategy read off the term. Core
  Lean only: no Mathlib is fetched or needed. Install it with the `lean` extra.
- **Commands.** `lanky check FILE [--json OUT] [--verbose]`, exit code 1 when any
  fact is refuted; `lanky --version`; plugin verbs appear as subcommands, which
  is how `lanky run` reaches loopty's executor.
- **pytest plugin.** Registered under `pytest11`, so `pytest a_file_of_theorems.py`
  collects each theorem as a test item.
- **Semantics notes** (`lanky.semantics`). Detection of the two places lanky's
  Python reading of a statement and Lean's differ: subtraction over `Nat`
  (Lean truncates at zero) and floor division or remainder over `Int`. A fact
  whose term uses one carries the note in its provenance, `lanky check
  --verbose` prints it, and when a stronger oracle established such a fact the
  property tester is still run as a cross-check so that a counterexample under
  the Python reading is recorded rather than lost.
- **Example.** `examples/gauss.py`, two worked theorems, runnable three ways.
- **Documentation.** A README that leads with what works, and
  `docs/quickstart.md`, which walks the worked file end to end with the output
  the commands print.

### Changed

Everything in this section is from the audit pass over the first draft, and is
listed because it changes behaviour a reader could already have depended on.

- **Guards are checked for the ways they go silently wrong.** A generator's
  `if` clause is still how a guard is written, but joining two propositions
  with Python's `or`, using `and` or `or` as a value, writing `not` in a guard,
  or asking for the truth value of a proposition from inside a function an
  annotation calls now raise `SymbolicBoolError` naming `&`, `|` and `~`.
  Previously an `or` guard was silently narrowed to its left half and an `and`
  in a body silently dropped its left operand.
- **Plugins are installed once per name.** `Registry.register_*` ignores a
  second plugin with a name already registered (pass `replace=True` to swap
  one), so a theory that arrives both in process and through an entry point no
  longer computes every fact twice.
- **`check_path` scopes and releases what it imported.** The objects an import
  decorated are collected through the new `Registry.collecting()` and dropped
  afterwards, and the module is no longer left in `sys.modules`, so checking
  many files in one process neither mixes their ledgers nor accumulates them.
- **A vacuous test says so.** The property-test oracle used to decline a pass
  over zero valid draws silently; it now leaves the status alone and records
  `untested`, the reason and `valid: 0` in the fact's provenance.
- **Draws are ordered by what they depend on.** `def t(f: Fn[Fin[n], Nat], n:
  Nat)` used to fail sampling with an unknown-variable error from pymbolic
  because `f` was drawn before `n`; the tester now draws a size before the
  family it sizes, keeping signature order otherwise.
- **The Lean REPL cache is durable.** It now defaults to
  `$XDG_CACHE_HOME/lanky/lean-repl` (`~/.cache/lanky/lean-repl`) rather than to
  a directory inside the installed `lean_interact` package, which any reinstall
  of the driver deleted. `LANKY_LEAN_CACHE_DIR` still overrides it.
- **`--verbose` does not overstate the Lean oracle.** Availability reads
  `available (untested until the first fact: the REPL is built on demand)`
  until something has been attempted, and names the Lean version afterwards.
- **The ledger's `where` column is disambiguated.** Two facts from different
  files that share a basename are printed with a parent directory.
- **`lanky check` reports a bad command apart from a bad file.** A file that
  does not exist prints one line and exits 2; a file that raises while it is
  imported prints the traceback and exits 1, rather than letting an exception
  escape the CLI.
- **A private theorem is not collected.** The pytest plugin skips a `Theorem`
  bound to a name starting with an underscore, so a module can keep a statement
  it does not want run.

### Notes

- Overriding `==` to build propositions removes pymbolic's structural equality on
  lanky nodes. Use `lanky.terms.structurally_equal` and never key a container by
  an expression.
- A file carrying statements needs `from __future__ import annotations` and a
  ruff `F821` per-file ignore: a size such as `n` is a symbolic variable lanky
  invents and has no binding a static checker can see.
- The Lean toolchain is not installed in CI, so the Lean tests skip there and the
  facts Lean would prove are tested instead. The ledger says which happened.
- Python's `and` between two propositions in a generator's `if` clause is *not*
  refused: CPython compiles a conjunction in a comprehension filter into two
  successive tests, so both halves are captured and the guard is the one that
  was written. It cannot be told apart from two `if` clauses in the bytecode.
  `&` is still what to write.
- A statement is read twice and the two readings can differ. `lanky.semantics`
  reports that rather than reconciling it; the module docstring explains why
  truncating the evaluator to match Lean would be wrong for a flattened
  pymbolic sum.
