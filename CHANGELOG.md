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
- **A sampled existential is undecided, not refuted.** `any(...)` over a sort
  such as `Nat` used to answer `False` when none of its four draws was a
  witness, which reported a true theorem as `REFUTED`; the evaluator now raises
  `lanky.terms.Undecided` there, the tester drops the draw and counts it in
  `TestReport.undecided`, and the fact stays `ASSUMED` with the reason in its
  provenance. An existential over `Fin` is enumerated and still answers both
  ways.
- **Hypotheses survive a theorem with no sort variables.** `Theorem.term` used
  to return the bare goal whenever there were no sort-valued parameters, which
  dropped every hypothesis; it now builds the guarded `Forall` with an empty
  binder tuple, so an implication with a false antecedent is no longer refuted
  by its own hypothesis.
- **A theorem's fact id names its definition.** `Fact.id` is now
  `theorem:<module>.<qualname>@<line>` rather than `theorem:<qualname>`, built
  by the new `lanky.ledger.fact_id`, so two same-named theorems collected in one
  ledger are two facts instead of one silently replacing the other.
- **Semantics notes see inside a domain.** `lanky.semantics` walks refinement
  predicates, `Fin` bounds and `Fn` domains and codomains, so a statement whose
  only `Nat` subtraction is in `n : Nat & (n - 1 < n)` or in `Fin[n - 1]` now
  carries the note it always should have.
- **A synthesized table value stays inside its codomain.** A definitional
  hypothesis such as `f(0) == -1` for an `f : Fn[Fin[1], Nat]` used to write
  `-1` into the drawn table and let the goal be refuted by a point outside its
  sort; the assignment is now checked with the new `lanky.testing.in_sort` and
  the draw is dropped instead.
- **A closed Boolean statement is a fact.** `-> 1 == 2` is answered by Python
  while the annotation is evaluated, so the term is the `bool` `False`; the
  property-test oracle declined anything that was not a pymbolic node, and the
  falsest theorem there is sat in the ledger as `assumed` with the check
  exiting 0. It is now `REFUTED` with an explicit empty counterexample and a
  reason, `True` is `TESTED`, a parameter annotated with a concrete bool is a
  hypothesis rather than a sort nothing can sample, the Lean printer writes
  such a statement as the proposition `True` or `False` rather than as a `Bool`
  literal leaning on a coercion, and `lanky check` exits 1.
- **Division by zero is a semantics gap of its own.** Lean's `Nat` and `Int`
  division are total (`x / 0` is `0`, `x % 0` is `x`) and Python's raise, so
  `n // 0 == 0` was `PROVED` with no note while calling it raised
  `ZeroDivisionError`. `lanky.semantics.DIVISION_BY_ZERO` is recorded for any
  divisor that is not a nonzero literal, over `Nat` as well as `Int`; the
  property tester now counts such a draw as undecided rather than crashing, and
  the cross-check records in the provenance that the sampled reading could not
  be run.
- **A family application has to stay inside the domain it declares.**
  `Fn[Fin[n], B]` prints as an unrestricted `Nat -> B`, which is sound only
  where every application is in bounds, and nothing checked it: `f(n)` for an
  `f : Fn[Fin[n], Nat]` became a Lean tautology and was `PROVED` while the
  tester raised `IndexError` on the same statement. The new
  `lanky.lean.check_applications` discharges each application's bound by affine
  arithmetic over the enclosing binders and declines the whole statement with
  `UnsupportedTerm` when it cannot (`off(r + 1)` against `Fn[Fin[n + 1], Nat]`
  with `r` in `Fin[n]` still goes through), and a table applied outside its
  domain now makes the draw undecided rather than raising, so neither reading
  can call an ill-typed application a proof.
- **Every level of a chained application is checked.** `f(0)(1)` for an
  `f : Fn[Fin[1], Fn[Fin[1], Nat]]` was validated only at `f(0)`, because the
  outer call's function is a call rather than a variable, so Lean proved the
  reflexive statement over the erased total `Nat -> Nat -> Nat` while the
  tester had no inner entry to compare; `check_applications` now walks the
  declared type alongside the arguments and discharges each level against its
  own `Fin` bound, and a chain longer than the type has arguments (which Lean
  would not elaborate) is declined too.
- **A refined family domain is declined rather than stripped to its base.**
  `f: Fn[Fin[1] & False, Nat]` with `f(0) == f(0)` passed the bound check
  against the base `Fin[1]` and became a reflexive Lean theorem, though the
  domain is empty and the tester cannot tabulate it. The erasure keeps the
  `Fin` bound as a guard and the refinement not at all, and the affine reading
  of the binders cannot establish a predicate, so an application over a
  refined domain raises `UnsupportedTerm`.
- **The application check sees inside a binder's domain.** It visited only a
  domain's `Fin` bound, so a refinement predicate such as
  `i : Nat & (f(n) != f(n))` over an `f : Fn[Fin[n], Nat]` went unchecked and
  handed Lean an impossible hypothesis about an erased point, from which it
  proved `1 = 2`. Refinement predicates, `Fin` bounds and nested family types
  are now all traversed under the binders they sit in, the predicates with
  their own binder in scope because that is what they talk about.
- **A short-circuiting quantifier restores the binder it shadowed.**
  `all(any(i == 0 for i in Fin[1]) & (i < 2) for i in Fin[3])` evaluated to
  `True`: `lanky.terms.LankyEvaluationMapper.assignments` restored the binding
  only after its loop, which `map_exists` returned out of at the first witness,
  so the outer `i < 2` was answered at the inner `i = 0`. The restoration is
  now in a `finally` and the walk is closed explicitly on every exit path, so
  the statement evaluates to `False` and the tester reports `REFUTED`.
- **A function-typed domain is bracketed in Lean.** `lanky.lean.lean_type`
  printed `Fn[Fn[Fin[n], Nat], Nat]` as `Nat → Nat → Nat`, which the right
  associativity of `→` reads as a family of families and not as
  `(Nat → Nat) → Nat`, so a higher-order parameter applied to a family did
  not elaborate. A domain whose type is an arrow, refined or not, is now
  parenthesized; a codomain needs no brackets and gets none.
- **An availability probe that raises makes its oracle unavailable.**
  `lanky.plugins.oracle_availability` let an exception from an oracle's
  `availability()` escape, and `establish` and `oracle_lines` both ask it
  before any per-oracle handler, so one broken optional oracle aborted the
  check and `lanky check` reported the checked file as unimportable. The
  exception is now the reason the oracle is unavailable, and the other
  oracles run.
- **`lanky check` asks whether the file exists rather than reading it off an
  exception.** Every `FileNotFoundError` out of `check_path` was reported as
  "no such file" with exit code 2, including one the checked file raised
  itself by opening a data file that is not there. The target's existence is
  now checked before it is imported, and an error raised inside it is an
  import failure with its traceback and exit code 1.
- **Checking a file twice collects the claims it imports twice.** `check_path`
  withdrew the checked module from `sys.modules` but not the modules it
  imported, so a second check of a file that imports a theorem from a
  neighbouring module found the neighbour cached and returned a ledger
  without its claims. The modules the file's own directory supplied to the
  import (a module `a.b` found as `a/b.py` or `a/b/__init__.py` next to the
  file, or through a neighbouring directory that is a symbolic link) are now
  withdrawn too; an installed package imported for the first time stays
  imported, even when it sits below the file's directory, and so does a new
  submodule of a package that was imported before the check, which would
  otherwise be split between two copies.
- **A refutation names the quantified point that made it false.** The
  property tester built a counterexample from the drawn variables alone, and
  a quantifier's binding lived in the evaluator's own copy of the context, so
  `all(i < 2 for i in Fin[n + 3])` was refuted at `{'n': 3}` with nothing
  saying `i = 2`. The goal is now walked along its universal quantifiers and
  conjunctions, one point at a time in the evaluator's order, and the first
  failing point joins the counterexample; a binder that shadows a drawn
  variable does not overwrite it.
- **A goal or a hypothesis that is not a proposition is refused.**
  `def t(n: Nat) -> n + 1` claims nothing, and Lean declines it because its
  goal has type `Nat`, but the property tester applied Python's truthiness to
  every draw and reported it `TESTED`; a hypothesis was coerced the same way,
  and so was every operand of `&`, `|` and `~`, every guard and every body of
  a quantifier, so `(n + 1) | (n > 5)` and `any(i + 1 for i in Fin[n + 2])`
  passed too, and so did a refinement by a number. The new
  `lanky.terms.truth_value` (also exported from `lanky.testing`) accepts a
  `bool` or a numpy boolean and raises `TypeError` for anything else; the
  evaluator reads every connective, guard and quantifier body through it,
  and the tester, `Theorem.__call__` and `Refined.holds` read what a whole
  proposition evaluates to the same way, so such a fact stays `ASSUMED` with
  the reason in its provenance.
- **A binder that captures a name its own domain mentions is declined by the
  Lean printer.** In `def bad(i: Nat) -> all(i > 0 for i in Fin[i])` the
  `Fin[i]` is evaluated before the generator binds its `i`, so it is the
  parameter, and the statement is false at `i = 1`; printed with its guard
  after the binder it read `∀ i : Nat, i < i → i > 0`, which `omega` proves,
  so with Lean installed the ledger said `proved`. `check_applications` now
  raises `UnsupportedTerm` for such a binder, and the tester refutes the
  statement.
- **A refined codomain is honoured when a family's entries are drawn.** An
  entry has no name, so `sample_value` accepted every value of a refined
  codomain's base: `f : Fn[Fin[1], Nat & False]` got a table holding an
  ordinary natural, and `-> False`, true because no such `f` exists, was
  refuted. A refinement that names only variables already drawn is now
  evaluated once per table, and an empty codomain means there is no draw; one
  that names anything else skips the draw; a family over an empty domain
  still needs no entry. A refinement that cannot be evaluated at a draw, such
  as `Nat & (10 // n > 1)` at `n = 0`, skips that draw, for a codomain and for
  a named variable alike, where its `ZeroDivisionError` used to end the whole
  test.
- **Two families are equal when their values are.** `lanky.testing.Table`
  had no equality of its own, so `f == g` compared two drawn tables by
  identity, and over `Fn[Fin[0], Nat]`, where it is true because there is one
  function out of an empty domain, it was refuted. A table now compares its
  values, recursively for a family of families, and is unhashable like the
  list it wraps.

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
- The test for the eager (non-`from __future__`) annotation path builds its
  fixture with `compile(..., dont_inherit=True)`. Without that flag `compile`
  inherits the future statements of the test module, so the fixture's
  annotations came back as strings and the eager path went untested.
