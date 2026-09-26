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
- **Mathlib mode** (`lanky.mathlib`, `lanky.lean`, `lanky.oracles.lean`), the
  Mathlib part of #3. Opt-in: `LANKY_LEAN_MATHLIB` names a Lake project with
  Mathlib fetched, and with it unset the oracle, the printer and the ladder are
  the core ones, unchanged. lanky ships the project in
  `src/lanky/mathlib-project/`, pinned to Mathlib v4.29.1 on Lean v4.29.1 (the
  toolchain the core-Lean CI job uses, and one lean-interact's REPL has a
  build for), with every dependency at a commit in `lake-manifest.json`.
  `python -m lanky.mathlib DIR` writes it and runs `lake exe cache get`,
  never a build of Mathlib, and says what to export. The oracle reads the
  variable when it wants a session, so the registered oracle follows it,
  keeps a session per mode, and in Mathlib mode starts the REPL in the project
  with lean-interact's `LocalProject` (told not to build it), imports Mathlib
  once, and elaborates every attempt in the environment the import left. A
  server the driver killed after a timeout is started again with Mathlib
  imported before the next attempt. A project that is not ready makes the
  oracle unavailable with the reason and the command that fixes it, rather
  than fall back to core Lean, and a `LANKY_LEAN_VERSION` other than the
  project's toolchain is refused. A proof records the Mathlib revision as
  `lean_mathlib`, and its `lean_source` starts with `import Mathlib` so it
  replays as a file. The theorem is declared as `Lanky.<name>`: Mathlib
  declares lemmas such as `mul_comm` and `sq_nonneg` at the root, and a claim
  named after one would be refused as already declared at every attempt.
  - The printer's Mathlib dialect (`print_lean(..., mathlib=True)`, and the
    same keyword on `statement_of`, `lean_type`, `domain_guards` and
    `Theorem.lean`) prints the core fragment as core Lean does, and adds
    `Real` and `Complex` as `ℝ` and `ℂ`; a float or a non-integral `Fraction`
    as the exact rational, ascribed `ℝ` even when integral; a complex literal
    around `Complex.I`; true division in `ℝ`, or `ℂ` when a side is complex;
    `|x|`, and `‖z‖` for a complex `z`; `exp`, `log` and `sqrt` as
    `Real.exp`, `Real.log` and `Real.sqrt`, and `Complex.exp`; and a sum over
    `Fin` binders as `∑ i ∈ Finset.Ico (0 : ℤ) n`, with a guard or a
    refinement as `with`. A floor division by a literal is ascribed,
    `(n / 2 : ℤ)`, so that next to a real it is cast whole rather than turned
    into real division of the cast `n`; the sum's lower bound is ascribed, and
    so is a body that is an integer numeral, since Lean reads an untyped
    numeral as a `Nat`, where `sum(i - 1 for i in Fin[3])` and
    `sum(1 for i in Fin[n]) - 3` truncate. It declines a sum over `Nat`, a
    `Fin` with a real bound (which the tester truncates), a floor division or
    remainder of a real, an order between complex numbers, and a complex
    logarithm or square root (`cmath` picks a side of the branch cut by the
    sign of a zero, and Lean's `ℂ` has no signed zero), each of which would
    print a meaning Python does not give. An `Elementary` node built by hand
    with a function other than those three is declined too.
  - The ladder, in Mathlib mode, runs the core attempts first (their closers
    extended with `linarith`, `nlinarith`, `positivity`, `ring_nf` and
    `norm_num`), then `norm_num`, `positivity`, `ring`, `field_simp`,
    `linarith`, `nlinarith`, `push_cast; ring` and two `simp` calls with the
    `exp` and `sqrt` lemmas outside the simp set, and then
    `reduction_scripts`: an induction on a natural parameter that a sum's bound
    mentions, peeling the last term off the sum in each case. Gauss's sum in
    `examples/gauss.py` is proved by it.
- **`Complex`, and `exp`, `log` and `sqrt`** (`lanky.prelude`, `lanky.terms`).
  `Complex` is a sort, `approx` by default as `Real` is; the tester draws
  complex floats, with small dyadic parts for `Complex.exact`, which keep
  ring arithmetic exact. `lanky.exp`, `lanky.log` and `lanky.sqrt` build an
  `Elementary` node from a term and are `math`'s functions at a real number
  and `cmath`'s at a complex one. Where Python gives no value (`log(0)`,
  `sqrt(-1)`, an `exp` that overflows a float) evaluation raises
  `UndefinedValue`, and the tester drops that draw as it drops a division by
  zero, rather than count a counterexample.
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
- **Facts rest on facts** (`lanky.ledger`). `Fact.rests_on` holds the ids of
  the facts a fact was established from, as a tuple (a single string is
  refused rather than read as one id per character). `Ledger.support(fact)`
  reads the graph and returns a `Support`: `effective`, the weakest status over
  the fact and everything it rests on, directly or through other facts, in the
  order of the status ladder with `refuted` below `assumed`; and `under`, the
  ids of the assumptions among them, in the order they are reached. An
  assumption is a fact that is `assumed` (an axiom, or an obligation nobody
  established) or `refuted`, an id the ledger does not hold (a claim of
  another file, since each file checked has a ledger of its own, or an id
  written wrong), or a fact on a circle of facts that rest on each other,
  since a circular argument establishes nothing and every fact on the circle
  or above it is worth `assumed` at most. Which facts are on a circle is found
  once per ledger, so a long chain of facts is read in seconds. The table
  names the
  assumptions after the status, as in `proved under jump, compact`, by owner
  when the owner names one fact in the ledger and by id otherwise, and grows an
  `EFFECTIVE` column when some fact is worth less than its own status; a
  ledger in which nothing rests on anything renders as before. `Fact.to_dict`
  carries `rests_on`, and `Ledger.to_dicts`, which `Ledger.to_json` and
  `lanky check --json` now write, adds `effective` and `under` for every fact.
  The exit code does not change: a fact resting on a refuted one fails the
  check through the refuted one. `lanky check` names each id a fact rests on
  that its ledger does not hold in an `UNRESOLVED` line under the table, since
  in the row it reads like any other assumption and a misspelt one would pass
  for one; that does not fail the check either, because an id of another
  file's fact is the same case.
- **`@axiom(cite=...)`** (`lanky.theory`). A statement written like a theorem
  and taken on a citation, for a result lanky cannot establish, such as a jump
  relation from a textbook. `Axiom` is a `Theorem` whose fact has kind
  `axiom`, id `axiom:<module>.<qualname>@<line>`, status `assumed` and the
  citation as `cite` in its provenance; the table prints `assumed (axiom)`.
  The citation is required: `@axiom` bare, or with a citation that is missing,
  empty or not a string, raises `TypeError` where it is written. `lanky check`
  asks no oracle to establish an axiom, and has the oracles of the `test`
  trust class look for a counterexample to it, which is kept: an axiom copied
  down wrong is `refuted (axiom)` and fails the check. What the sampling
  says about the hypotheses is kept too: an axiom whose hypotheses no draw
  satisfied is examined for vacuity as a theorem is, so hypotheses a stronger
  oracle shows inconsistent make it `assumed (axiom) (vacuous)` and fail the
  check, and otherwise it gets the `WARNING` line; that oracle is asked about
  the hypotheses alone, never about the axiom. Its semantics gaps (a division
  by something that may be zero) are recorded in its provenance as a
  theorem's are. The pytest plugin collects and samples an axiom as it does a
  theorem.
- **`@theorem(uses=[...])`.** A theorem names the facts it rests on:
  theorems, axioms, `Fact`s or fact ids (`lanky.theory.fact_ids`), which
  become its fact's `rests_on`. A single entry need not be in a list; an entry
  that names no one fact, such as a plugin's object that owns several, is
  refused where the decorator is written, and so is `uses=None`, which is
  what a name bound to nothing by mistake holds (a theorem that uses nothing
  leaves `uses=` out). So is a positional argument that is not the function
  to decorate: `@theorem(gauss)` and `@axiom("Kress")` are `uses=` and
  `cite=` without their keywords, and say so. The oracles are not handed the
  statements a theorem uses: what `uses=` records is what the theorem is
  worth. `@theorem` written bare works as before, and so does `@theorem()`.
- **Example.** `examples/gauss.py`, two worked theorems, runnable three ways,
  and `examples/nicomachus.py`: Nicomachus's theorem as an axiom, and the
  closed form of the sum of cubes, tested under it.
- **Documentation.** A README that leads with what works, and
  `docs/quickstart.md`, which walks the worked file end to end with the output
  the commands print, and then the axiom example, whose table the suite
  compares with a real run.

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
  loopty's isl oracle records, counted as one; it is now printed too, see
  below). An empty counterexample is no longer printed: `-> 1 == 2` shows its
  reason without the `counterexample: {}` line above it. The JSON ledger keeps every field,
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
  (`Nat & (k == 1000)`) raises `Undecided` rather than passing on no point,
  so the fact stays `ASSUMED` with the reason; an existential over one was already
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
- **A sampled quantifier can be refuted but never confirmed.** A `forall`
  over a sampled domain such as `Nat` that held at its four draws answered
  `True` wherever it stood, which is evidence where the statement asserts it
  and a certainty nowhere, so under a negation it became a refutation of a
  true statement (`~all(k < 100 for k in Nat)`), in a hypothesis it admitted
  a draw the statement excludes (`h: all(k < m for k in Nat)` with the goal
  `m < 0`), and a sum over draws of `Nat` was added up as if it were the sum
  over `Nat`; all three were `refuted`, at counterexamples that do not replay
  (#14). The evaluator now tracks where each proposition stands, as the new
  `lanky.terms.Polarity`: the goal and what it asserts stand `POSITIVE`; a
  hypothesis, the operand of `~`, and the guard and the refinements of a
  universal stand `NEGATIVE`; a proposition used as a value, in a comparison,
  an arithmetic operation, a call or a sum, stands `MIXED`; an existential's
  guard and refinements stand where it does. A sampled `forall` that holds at
  every draw answers `True` only standing `POSITIVE`, and raises `Undecided`
  anywhere else; one a draw breaks is `False` everywhere, and an existential
  a draw witnesses is `True` everywhere, as before. A sum over a sampled
  domain raises `Undecided` wherever it stands. `lanky.terms.evaluate` takes
  the polarity (`POSITIVE` by default) and the property tester reads each
  hypothesis standing `NEGATIVE`, so the three statements are `assumed` with
  the reason and `lanky check` exits 0; `all(k < 3 for k in Nat)` as a goal is
  still refuted. A quantified definitional hypothesis over a sampled domain,
  such as `all(f(k) == 0 for k in Nat)`, is left to the hypothesis filter,
  where it used to be walked without a sampler and end the test with "cannot
  enumerate the binder domain".
- **A guard no draw passes leaves a sampled `forall` undecided.**
  `all(k < 0 for k in Nat if k > 100)` is false at `k = 101`, and no draw of
  `k` passed the guard, so the `forall` held at no point and the fact was
  `tested` over 200 valid draws of which none evaluated the body (#11). It
  raises `Undecided` now, with a reason saying that no draw passed the guard,
  exactly as the refinement spelling `k` in `Nat & (k > 100)` already did, so
  the two spellings of one statement agree; a guarded `forall` over `Fin` is
  unchanged. Both cases, and the three above, are settled by the new
  `lanky.terms.LankyEvaluationMapper.guarded_assignments`, which the tester's
  counterexample walk shares; `decline_empty_walk` is gone. A walk decides
  whether it sampled by whether it drew, not by what its binders are: over
  `i in Fin[n], k in Nat` at `n = 0` nothing is drawn and the domain is empty,
  so the universal is vacuously `True`, the existential `False` and the sum
  `0`. The existential, and a universal over a sampled refinement, used to be
  undecided there, and the refutation of such an existential says why every
  point was tried.
- **A later binder's domain names the binders before it.**
  `lanky.terms.free_variables` reported `i` free in
  `all(j < n for i in Fin[n] for j in Fin[i])`, whose inner `Fin[i]` is the
  outer binder, because the domains were never reduced by the binders that
  precede them (#12). Each domain is now read with the earlier binders bound,
  and a binder's own domain, which is evaluated before it exists, keeps its
  free names. A family whose codomain is refined by such a quantifier is
  tested where its entries used to be refused, and an inner binder that shares
  a parameter's name no longer orders the draws.
- **An integral `Fraction` prints as the integer it is.** The Lean printer
  ascribed `Int` to an `int` base of a power but not to `Fraction(2, 1)`,
  which printed as the bare numeral `2`, so `1 - Fraction(2, 1) ** n >= 0`,
  built node by node, was a statement about `Nat` that Lean proved by
  truncation and Python refutes at `n = 1` (#16). An integral `Fraction` is
  now read as the `int` it equals wherever a literal is treated specially: a
  power's base is ascribed, a literal exponent is taken, a positive literal
  divisor prints as `/`, and a negative summand as a subtraction. The
  semantics note and the bounds check of a family application read it the same
  way, so a `Fraction(2, 1)` divisor carries no division-by-zero note and a
  family applied at `Fraction(0, 1)` is in bounds. The evaluator takes a
  `Fraction` literal as the constant it is, where pymbolic refused it as an
  invalid foreign object and the tester could not run the statement, so the
  claim is now refuted at `n = 1` with Lean and without.
- **The quickstart's `gap.py` transcripts are held to a real run.** A test
  writes `gap.py` from the quickstart's own snippet, with `examples/gauss.py`'s
  imports, and compares what `lanky check` prints with the quickstart's
  blocks, with Lean and without: the `truncated` refutation, and for
  `div_zero` the `SEMANTICS` block with Lean and the `assumed` row without
  (#18). It found the `truncated` block one line short since every refuted
  fact started printing its reason.
- **In Mathlib mode, a true division, a logarithm and a square root are noted
  where the readings part.** Besides an integer division that may be by zero,
  a fact's `semantics` provenance names a true division by anything but a
  nonzero literal (`x / 0` is `0` in a Mathlib field) and a `log` or `sqrt`
  of anything but a positive literal (Mathlib's are total). Only in Mathlib
  mode: core Lean declines all three, so there is no second reading to part
  from, and a core-mode fact records what it did before.
- **The suite runs in core-Lean mode.** `tests/conftest.py` takes
  `LANKY_LEAN_MATHLIB` out of the environment before any test runs and hands
  it to `tests/test_mathlib.py` alone, so a developer who exports it still sees
  the documented ledgers, which read `tested` for Gauss's sum.
- **An optional CI job for Mathlib mode.** `test with Lean and Mathlib` sets
  up the pinned project with `python -m lanky.mathlib`, caches Mathlib's
  compiled files keyed by the manifest, runs `tests/test_mathlib.py` with
  `LANKY_LEAN_MATHLIB_TEST_REQUIRED=1` (a missing project fails instead of
  skipping), and checks that `lanky check examples/gauss.py` proves both
  rows. It may fail without failing the run.
- **The Lean CI job keeps a uv cache of its own.** It shared one with the
  job that does not sync the `lean` extra, and downloaded lean-interact
  again on every run; its setup-uv step now has `cache-suffix: lean` (#19).
- **A refutation's witness is printed, whichever plugin recorded it.**
  `refutation_lines` counted a plugin's `witness` against `no witness
  recorded` without printing it, since printing it looked like lanky knowing
  a plugin's provenance keys, so a fact loopty's isl oracle refuted, with the
  cell that escapes an array as its witness, came out with an empty block and
  the witness in the JSON alone (#20). The block under a `REFUTED` line is now
  built from three standard provenance keys, read the same way for every
  oracle and plugin: the `counterexample` and the `witness`, each when it is
  not empty, and then the `reason`, which usually talks about them. A value
  that prints as several lines is indented line by line. A plugin's own keys,
  such as loopty's `witness_text`, stay in the JSON.

### Notes

- Overriding `==` to build propositions removes pymbolic's structural equality on
  lanky nodes. Use `lanky.terms.structurally_equal` and never key a container by
  an expression.
- A file carrying statements needs `from __future__ import annotations` and a
  ruff `F821` per-file ignore: a size such as `n` is a symbolic variable lanky
  invents and has no binding a static checker can see.
- CI runs the suite twice: without Lean, on Python 3.12 and 3.13, where the Lean
  tests skip and the facts Lean would prove are tested instead, and with Lean
  v4.29.1, where they run. The ledger says which happened. A third, optional
  job runs the Mathlib tests against the pinned Mathlib.
- Over `Real` and `Complex` the tester's reading is floating point (fractions
  for `Real.exact`) and Mathlib's is exact, so an identity that holds up to
  rounding is refuted without Mathlib and proved with it. That is what the
  exactness class says, and it is not noted as a gap; #33 asks which reading
  should decide.
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
