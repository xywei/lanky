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
- **Commands.** `lanky check FILE... [--json OUT] [--verbose]`, exit code 1 when
  any fact is refuted; `lanky --version`; plugin verbs appear as subcommands, which
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
- **A check collects the claims the file defines, and only those.**
  `check_path` handed the theories every object the import registered, so a
  theorem imported from a neighbouring module was in the first check of a
  file and missing from the second, which found the neighbour cached and ran
  nothing. An object is now collected when the checked file defined it,
  which is read off the function it wraps (the file its code was compiled
  from, and the module namespace it was defined in) or, for an object that
  wraps no function, off the path its facts record; the order of the imports
  plays no part. A claim that lives in an imported module is checked by
  checking its file, and `lanky check` takes several files (`lanky check
  main.py helpers.py`), printing each file's ledger under a `==> FILE <==`
  heading; `--json` writes one list of all their facts. Nothing is withdrawn
  from `sys.modules` for this: an imported module stays imported, as it
  would anywhere else.
- **A checked file inside a package can import relatively.** `import_path`
  loaded every file as a top-level module named `lanky_checked_<stem>`, so
  `from .helpers import claim` in `pkg/mod.py` failed with "attempted
  relative import with no known parent package" and `lanky check` reported
  an import failure. The module keeps that name and is given its package:
  `__package__` and `__spec__.parent` both name it, and the directory the
  package is found from is on `sys.path` while the file executes. The
  package is imported by the file's first relative import, the ordinary way;
  a file with no relative import never runs its package's `__init__`. When
  the package's `__init__` imports the checked file itself, that copy's
  claims are not collected a second time. A package of the same name that
  the process already imported from another directory, as the first file of
  `lanky check a/pkg/mod.py b/pkg/mod.py` leaves behind, is refused with
  `ImportError` rather than lent to the second file, whose relative imports
  would otherwise have been answered by the first tree's modules.
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
- **A theorem needs a goal.** `@theorem` on a function with no return
  annotation, or with `-> None`, raises `TypeError` naming the function and
  its line. Such a theorem read as `True` when it was called or sampled, and
  as `assumed` in the ledger, where no oracle takes a fact without a term.
- **Two families are equal when their values are.** `lanky.testing.Table`
  had no equality of its own, so `f == g` compared two drawn tables by
  identity, and over `Fn[Fin[0], Nat]`, where it is true because there is one
  function out of an empty domain, it was refuted. A table now compares its
  values, recursively for a family of families, and is unhashable like the
  list it wraps.
- **CI runs the suite with Lean as well.** The Lean tests skipped in CI, all
  seventeen of them, so nothing there showed the `proved lean` row the README
  leads with. A second job, `test with Lean`, installs elan, Lean v4.29.1 (a
  toolchain lean-interact 0.11.5's REPL has a build for, which v4.34 is not)
  and the `lean` extra, caches the toolchain and the built REPL, and runs the
  whole suite with the oracle on. It sets `LANKY_LEAN_TEST_REQUIRED=1`, under
  which a Lean test that cannot get a Lean session fails where it used to
  skip, so the job cannot pass by running none of them; the availability test
  that passed without Lean by returning early now skips there instead. The job
  then runs `lanky check examples/gauss.py` and asserts the README's `proved
  lean` row, and the suite compares the README's abridged table and the
  quickstart's full one with what the check prints, with Lean and, reading
  the row as `tested`, without it. The first run with Lean failed two tests
  of multi-file checking that counted `1 facts: 1 tested` for a claim Lean
  proves; they now pin the decider with `LANKY_LEAN_DISABLE`.
- **Every refuted fact says what refuted it.** `lanky check` printed the
  details of a `REFUTED` fact only when its provenance had a
  `counterexample`, so a fact refuted with a reason and no assignment to show,
  which is what loopty reports for a kernel body it cannot trace, got a bare
  `REFUTED` line and its reason was in the JSON alone; loopty put an empty
  counterexample into the fact to have it printed. Under each `REFUTED` line
  there is now the counterexample when it names something, then the fact's
  `reason` whenever it has one, each of its lines indented, and
  `no witness recorded` when there is neither (a plugin's own `witness`, as
  loopty's isl oracle records, counts as one and stays in the JSON). An empty
  counterexample is no longer printed: `-> 1 == 2` shows its reason without
  the `counterexample: {}` line above it. The JSON ledger keeps every field,
  the empty counterexample included. The new `lanky.cli.refutation_lines`
  builds the block.
- **A quantifier over a refined domain reads the refinement.** The property
  tester read a binder over `Fin[n] & p` or `Nat & p`, which a plugin
  building terms by hand can write, as if `p` were not there: the domain had
  no `points`, so it went to the sampler, which drew from the base without
  judging `p`. `∀ k ∈ Fin[n + 2] & (k > 0), k > 0` was refuted at `k = 0`,
  outside its own domain, and `∃ k ∈ Fin[n + 2] & (k > 0), k == 0` was
  `tested` on a witness the domain excludes, while the Lean printer read both
  correctly. `lanky.terms.LankyEvaluationMapper` now gives a refined domain
  the points of its base at which the refinement holds, judged with the
  binder bound, as a guard is judged, and the domain is enumerated exactly
  when its base is, so the first statement is `tested` and the second is
  refuted with a reason saying that no point of the enumerated domain is a
  witness. A `forall` over a sampled refinement that rejects every draw
  (`Nat & (k == 1000)`) raises `Undecided` (the new
  `lanky.terms.decline_empty_walk`) rather than passing on no point, so the
  fact stays `ASSUMED` with the reason; an existential over one was already
  undecided. A definitional hypothesis over a refined domain is assigned at
  the admitted points only, where the walk used to fail and end the test. A
  value of a refined sort drawn without a variable name is judged as a
  family's entry is instead of being drawn from the base, and
  `lanky.terms.free_variables` counts the names a refined binder domain
  mentions, which it used to miss.
- **Every oracle reads a statement as integer arithmetic.** The Lean
  printer wrote a `Nat` variable as a Lean `Nat`, whose subtraction truncates
  at zero, so `def truncated(n: Nat) -> n - 1 >= 0` was `proved` by Lean while
  the property tester refuted it at `n = 0`, and `lanky check` exited 0 where
  Lean was installed and 1 where it was not (#6). A natural (a `Nat` variable,
  or a point of `Fin[m]`) now prints as an `Int` with `0 ≤ n`, and `n < m` for
  `Fin[m]`, as hypotheses; every operation is `Int`'s; and `//` and `%` print
  as `Int.fdiv` and `Int.fmod`, which round as Python's do, except that a
  positive literal divisor prints as `/` and `%`, which agree with them there
  and which `omega` understands. A family's natural values stay `Nat` in its
  type, `Int → Nat`, and an application used as a number is cast,
  `(f i : Int)`. A family over `Nat` is applied only where the argument can
  be shown non-negative, or is another family's natural value, and an
  exponent has to be a literal, a natural
  variable (printed `n.toNat`) or a natural value. A literal base is ascribed,
  `(2 : Int) ^ m.toNat`: with its variable only in the `Nat` exponent,
  `1 - 2 ** m >= 0` had no `Int` in it, Lean read its numerals as `Nat`, and
  proved it. `truncated` is now refuted with and without Lean, and
  `n - 1 <= n` is still proved. The notes
  `lanky.semantics.NAT_SUBTRACTION` and `INT_DIVISION` are gone with the gaps
  they named, and so are `uses_subtraction` and `uses_floor_division`;
  `DIVISION_BY_ZERO` stays, because `Int.fdiv x 0` is `0` where Python
  raises. The induction strategy trades a natural for the `Nat` it is
  (`Int.eq_ofNat_of_zero_le`) before it induces, so `scan_monotone` is still
  proved; the cheap ladder ends with `simp_all <;> omega`, because a fact
  `simp` knew about a `Nat`, such as `0 < n + 1`, is `omega`'s about an
  `Int`; and an arm of the closers that leaves the goal open no longer ends
  the `first` it is in. A script pinned with `use_tactic` proves the printed
  statement, so one written for the `Nat` reading needs the same trade.
- **A claim with inconsistent hypotheses is vacuous, and the ledger says so.**
  From `n > 2` and `n < 1`, `omega` proves `n == n + 1`. The row read
  `proved lean` with nothing under the table, and the property tester, which
  would have found that no draw satisfied the hypotheses, was never asked
  (#5). The tester now cross-checks every fact with hypotheses (a guard, a
  binder into `Fin` or a refinement, or a family whose values are restricted
  so) that a stronger oracle established. When
  no draw satisfies the hypotheses, whoever established the fact, the
  stronger oracles are asked whether the hypotheses alone prove `False`
  (`lanky.check.hypotheses_fact`; for Lean that is the cheap ladder). If one
  does, the provenance records `vacuous`, `vacuous_by` and
  `vacuous_evidence`, the status column reads `proved (vacuous)`, the summary
  line counts vacuous facts, a `VACUOUS` block follows the table, and
  `lanky check` exits 1; the status itself stays what the oracle said. If
  none can, the provenance records `unsatisfied` ("hypotheses never satisfied
  in 4000 draws") and a `WARNING` line follows the table, with exit code 0:
  hypotheses that hold only where the sampler does not look, such as
  `n == 1000` over naturals drawn up to five, leave the same record. A test
  that could not draw at all, because a sort has no sampler (a family over
  `Nat`, `lanky.testing.Unsampleable`), is not taken for hypotheses that
  never held: its reason says that no draw could be completed, the stronger
  oracles are still asked, and nothing is printed when none can answer. A
  refinement that raises at a draw, as `Nat & (10 // n > 1)` does at `n = 0`,
  makes the draw undecided, as the same guard does
  (`lanky.testing.Unevaluable`), so it is not taken for a hypothesis that
  failed. A satisfiable hypothesis changes nothing. A counterexample the cross-check
  finds under a stronger oracle's proof is recorded under `SEMANTICS` whether
  or not the fact carries a note, since with one reading of arithmetic it
  means one of the oracles is wrong.

### Notes

- Overriding `==` to build propositions removes pymbolic's structural equality on
  lanky nodes. Use `lanky.terms.structurally_equal` and never key a container by
  an expression.
- A file carrying statements needs `from __future__ import annotations` and a
  ruff `F821` per-file ignore: a size such as `n` is a symbolic variable lanky
  invents and has no binding a static checker can see.
- CI runs the suite twice: without Lean, on Python 3.12 and 3.13, where the Lean
  tests skip and the facts Lean would prove are tested instead, and with Lean
  v4.29.1, where they run. The ledger says which happened.
- Python's `and` between two propositions in a generator's `if` clause is *not*
  refused: CPython compiles a conjunction in a comprehension filter into two
  successive tests, so both halves are captured and the guard is the one that
  was written. It cannot be told apart from two `if` clauses in the bytecode.
  `&` is still what to write.
- A statement is read as integer arithmetic by every oracle, and Lean is given
  that reading rather than the evaluator being made to truncate: pymbolic has
  no subtraction node, so `a - b + c` is one flattened sum that has lost the
  association truncation depends on. Division by zero, total in Lean and an
  exception in Python, is the gap `lanky.semantics` still reports.
- The test for the eager (non-`from __future__`) annotation path builds its
  fixture with `compile(..., dont_inherit=True)`. Without that flag `compile`
  inherits the future statements of the test module, so the fixture's
  annotations came back as strings and the eager path went untested.
