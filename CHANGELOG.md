# Changelog

All notable changes to lanky are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions follow
[PEP 440](https://peps.python.org/pep-0440/).

## [Unreleased]

### Added

- **Chains, the steps of a written proof** (the proof interface of
  2026-10-16, increment I2). A proof body writes a calculation as a textbook
  does, a link to a line, each with its reason:

  ```python
  return (
      R[a, b]
      .equals(-R[a - 2, b + 2], by=recurrence)
      .equals(-D[a - 2, b + 2], by=claim(a - 2, b + 2))
      .equals(D[a, b], by=pde)
  )
  ```

  `.equals`, `.at_most`, `.less_than`, `.at_least` and `.more_than` are on
  every term and on a chain (`lanky.chains`). `by=` takes a fact, a tuple of
  facts, or `...`, a step left open; with no `by=` the link is algebra alone.
  A chain assigned to a name, `recurrence = a[n].equals(..., by=ode)`, is a
  fact later lines cite by that name. A fact left uncalled is cited at the
  one point that lines it up with the step (`lanky.matching`): offsets are
  solved (`R[x + 2, y]` against `R[a, b]` is `x = a - 2`), values are bound
  by type, and a family of a fact's own binds to a function of the
  variables a sum binds (`sum(f[k] for k in Fin[n + 1])` against `sum(r**k
  for k in Fin[n])`), the rule loopty's matcher shares. Where no single
  point fits, or several do, the message names them and says to write it.
- **The Lean of a step** (`lanky.oracles.steps`). A chain is a `calc`, each
  link closed by its facts at their points: `exact`, then a
  `linear_combination` whose multipliers lanky's search finds among the
  facts cited, then `linarith`; in core Lean `omega` and `grind`. The
  compiler adds what a reader never writes: that an integer denominator the
  case shows is not zero is not zero in the field, and the shift
  `n.toNat = (n - 1).toNat + 1` where a fact has the power one order down.
  Where the chain's ends print as the claim's sides the `calc` is the proof,
  and otherwise the claim follows from it by `linear_combination`; a chain
  about something else is refused, naming its end and the claim's side. A
  named chain is a `have`. `by=...` is a `sorry` at a recorded line, and a
  command whose only `sorry` are those closes "with holes"
  (`holes_verdict`, `LeanSession.answer_with_holes`). Without Lean, each link
  is drawn at points, so a wrong step is caught at its line, and a link over
  a family that cannot be drawn says so (`draw_links`). A theorem cited is
  restated by the text its own command proved where the check recorded one
  (`lanky.citations.proved_texts`), and its id is what the citing claim rests
  on. The proof-trace mode that runs a body, `if` as a case split and
  `claim` as the induction, is the next increment's; the design's examples
  1.1 and 1.2, compiled by this one into the recursive theorems the
  prototypes checked, close in Lean with Mathlib with clean axioms.
- **`examples/line_taylor.py` writes its proof** in the theorem's body, the
  recurrence named on the way, and its names are the design's: the
  coefficient family is `a`, the hypotheses `nonzero` and `first_term`.

### Fixed

- **`python -m lanky.mathlib DIR` starts without a warning** (#162). The
  command the `WITHOUT MATHLIB` line and the README give printed a
  `RuntimeWarning` from runpy before its own first line, saying the module
  had been imported already and that running it might be unpredictable:
  `import lanky` imports `lanky.mathlib`, since the Lean oracle and
  `lanky.semantics` read the project from it, and `python -m` imports `lanky`
  first. `lanky.mathlib` is now a package, and the command is its `__main__`,
  which nothing imports. What the command does is unchanged, and so is
  `from lanky import mathlib`.

## [0.4.0] - 2026-10-16

Checking a file again is fast, and the ledger says why a row is not proved.
A check after the first starts no Lean, also for a question the first check
ran out of time on: the proof cache keeps where such a question stopped, and
replays it until the check is given more time (#134, #155). `python -m
lanky.mathlib DIR` keeps Mathlib's downloads inside `DIR` (#151), and
`--verbose` names the Lean the REPL runs (#152). An oracle that raises is
named in the ledger, a theorem Lean's printer declines says why, a Mathlib
project that fails to import says so, and `--show-lean` names each owner's
theorems apart (#137, #132, #138, #120, #112). The test suite runs under
`pytest -n` with Mathlib required, and test workers no longer race to build
the Lean REPL (#148, #149, #147, #122). loopty 0.4.0 needs this release.

### Fixed

- **An oracle that raises is named in the ledger** (#137). One that raised
  over a fact was passed over without a word except under `--verbose`: a bug
  in one of Lean's strategies made the oracle raise on a claim, and the row
  read `tested`, with nothing in the JSON saying that Lean was asked at all.
  The fact now records the oracle and the exception as `raised`, and `lanky
  check` prints them under the table, in a `RAISED` line that says the
  oracle failed and not the claim, and that `--verbose` prints where: it
  prints the traceback now. An oracle that raises while it samples a claim
  again, or while it is asked whether a claim is vacuous, is named the same
  way, with what it was asked. `lanky.cli.report_raised` prints the lines for
  a plugin's verb.
- **A theorem Lean's printer declines says so under `--verbose`** (#132).
  The Lean oracle is not offered a statement its printer cannot state, and the
  row read `tested` with nothing saying that Lean was not asked, or why:
  `flattening` in `examples/sum_factorization.py`, which applies a family at
  `i // n**2`, had its reason in the example's docstring alone. An oracle may
  now say why it will not take a fact (`not_taken`, beside `availability`),
  and Lean's gives the printer's reason as `lean_declined`, which `--json`
  carries, `--verbose` prints in a `NOT PROVED` line (`property-test tested
  it; Lean was not asked: ...`), and `--show-lean` prints beside a statement
  only Mathlib can state.
- **A Mathlib project Lean cannot import says so, once** (#138). The REPL
  answers an `import Mathlib` that fails with an empty environment and no
  error, so a project whose compiled files a `lake exe cache get` that
  stopped half way had damaged started a session with no Mathlib in it, and
  every claim about reals read `not proved by Lean: expected token`. A
  Mathlib session now checks the import with a command only Mathlib
  elaborates, and when it fails asks Lean to import Mathlib on its own, which
  says why. The oracle is then unavailable, the `WITHOUT LEAN` line gives the
  reason, `Mathlib could not be imported from DIR: failed to read file
  '...', invalid header; run `lake exe cache get!` there`, and the claims stay
  `tested`. An import that runs out of time says how to give it more.
- **`--show-lean` names each theorem apart** (#120). The theorem of a part
  is named after the claim's owner and the part, so the facts of one owner
  declared theorems of one name: loopty's stencil printed `theorem
  Lanky.jacobi_in_bounds` once for each of its three accesses, which a reader
  could not tell apart and Lean would not take in one file. A theorem a row
  above it named is shown as `Lanky.jacobi_in_bounds_2`, `_3` and on, counted
  over the whole ledger, so a theorem has one name whatever `--show-lean TEXT`
  keeps. The provenance and the proof cache keep the source Lean was given.
- **`math.floor` of a variable in an annotation names the call and what to
  write** (#112). `math.floor(x) >= x - 1` failed while the file was read
  with pymbolic's `UnknownVariableError: x`, and `math.floor(exp(x))` with
  its `UnsupportedExpressionError`, neither naming the call. Both are now a
  `TypeError` that does: `math.floor(x) applies Python's math.floor to a
  symbolic value, which lanky has no term for: ... Write x // 1, which is the
  floor of x as a term`, and `math.ceil` the same, with `-(-x // 1)`. Every
  other function of Python's `math` module asks for a float, and is refused
  naming the term and the terms to write instead. Code that is not an
  annotation's, a kernel's body that loopty traces among it, gets pymbolic's
  error as before.

- **A check after the first starts no Lean, also where the first ran out of
  time** (#134). An attempt the budget cut short, or one that timed out, was
  not kept in the proof cache, since asked again it may be answered, so the
  check after a cold one started Lean for it: on loopty's `l2p.py` with
  Mathlib, the second check started a session for the vacuity question of
  `on_every_triangle`, whose budget the cold check had spent, and only the
  third started none. The cache now keeps where such a question stopped,
  with the budget and timeout it had and what the check said of it, for a
  claim, a part of a plugin's claim and a counterexample. A check given no
  more time reads it back, passes over the attempts left unanswered and
  says what the first check said, without Lean; one given more time, a
  larger budget or timeout, asks Lean again. The record never proves
  anything: a claim proved after an attempt that timed out is proved by
  the kept answer that closed it, read back as before.
- **A counterexample to a part about reals is read back without Mathlib**
  (#155). The cache was read first only for a counterexample to an integer
  part, so with Mathlib a warm check started the session that imports
  Mathlib for one the cold check had confirmed, or had run out of time on.
  It is now read under the Mathlib project's key, as the part's answers
  are, and the warm check says what the cold one said without a session.
  A counterexample to an integer part beside a part about reals no longer
  imports Mathlib at all: it is checked in core Lean, where its part is.
- **A part's stop record names the attempts its fallback adds** (#155).
  The record of where a part stopped was kept under its own attempts
  alone, so a plugin that changed the case splits its fallback gives, the
  statement and the part's hints the same, had a warm check say the old
  "ran out of time" again instead of trying the new splits. The record is
  now kept under every attempt the check reached, the fallback's among
  them once it was asked for, so new ones are asked; a fallback the check
  did not reach is not asked for to make the key. A record never proved
  anything, so only a part left open was affected.
- **`python -m lanky.mathlib mathlib` keeps the downloads in `mathlib`**
  (#155). With a relative `DIR`, the cache tool, which runs in the project,
  read `MATHLIB_CACHE_DIR=mathlib/.lake/mathlib-cache` from there, so the
  408 MB of archives went to `mathlib/mathlib/.lake/mathlib-cache`, and the
  command reported 0 MB in the place it meant. `DIR` and a relative
  `MATHLIB_CACHE_DIR` are now read from the current directory before the
  tool starts, and the closing lines name the project in full: `ready:
  export LANKY_LEAN_MATHLIB=/home/you/mathlib`, which works from anywhere.
- **`python -m lanky.mathlib DIR` keeps Mathlib's packed downloads in the
  project** (#151). The cache tool kept its 408 MB of archives in
  `~/.cache/mathlib`, outside `DIR`, so deleting the project left them
  behind. They now go to `DIR/.lake/mathlib-cache`, unless
  `MATHLIB_CACHE_DIR` names a place for them, and the command says where
  they are and how large they are. The module's docstring suggested
  `~/.cache/lanky/mathlib` for the project, and now says `~/mathlib`, as
  the README and the ledger's `WITHOUT MATHLIB` line do.
- **`lanky check --verbose` names the Lean the REPL runs** (#152). Before
  the first fact the oracle's line named the Mathlib project and not the
  Lean, and a reader checking a setup ran `lean --version` beside it, which
  is the Lean on `PATH`. It now says `the REPL is built on demand, Lean
  v4.29.1, with Mathlib v4.29.1 from DIR`: the project's toolchain and the
  Mathlib it pins, or in core mode the pinned Lean or the one on `PATH`. A
  `LANKY_LEAN_VERSION` that is not the Mathlib project's toolchain is the
  reason the line gives, as the session gives it when it refuses to start.
- **Processes that start Lean at once on an empty cache build the REPL
  once** (#122). lean-interact builds the REPL with `lake build` in its
  directory in the cache, and locks the checkout but not the build, so
  pytest's workers, or `lanky check` runs side by side, built it at once,
  and some failed with `the Lean REPL could not be built`. Where the Lean
  is not pinned, a process whose build failed opened its session with the
  next toolchain elan had: the suite's keyword test, run in one, read the
  sixteen words Lean v4.33.0-rc1 reserves that v4.29.1 does not. A session
  now holds a lock on a file in the cache while it sets its REPL up, so the
  others wait for the first build and use it.
- **With `pytest -n`, the Mathlib tests find the project** (#148). The
  suite's conftest takes `LANKY_LEAN_MATHLIB` out of the environment, which
  under pytest-xdist happened before the workers started, so in every
  worker the Mathlib tests skipped, or failed under
  `LANKY_LEAN_MATHLIB_TEST_REQUIRED`. Each worker is now handed the
  project.
- **The test of an interrupted child holds on a loaded machine** (#149).
  The child's `SIGTERM` handler printed, and a signal that came while the
  child's own `print("ready")` still held standard output made that print
  raise `RuntimeError: reentrant call`, so the child exited 1: one run in
  eight on a host running twice as many processes as it has threads. The
  handler now writes past `sys.stdout`, and is given more than a second.
- **The suite passes where loopty is installed beside lanky** (#147).
  `test_the_built_in_plugins_are_registered` asserted that lanky's two
  theories were the only ones, and loopty's entry point adds `kernel`. It
  now asserts that lanky's come first.

## [0.3.0] - 2026-10-15

Lean checks what a plugin decides, and Mathlib proves claims for every size.
A plugin's claim comes to Lean as parts, each with the hints its solver found,
and Lean proves each part again, `omega` first and then with the hints. loopty
states its isl facts this way. `lanky check --show-lean` prints the Lean, a
proof cache keeps Lean's answers, and a warm check starts no Lean (#118). In
Mathlib mode lanky now proves equations between finite sums (an exchange of
sums, sum factorization and the Kronecker mixed product, for every size),
claims for every order from an order on, the total of a scatter, a scatter as
the transpose of a gather, and identities about the parts of a complex number.
A family takes several indices (`Fn[Fin[n], Fin[m], Real]`, applied as
`F[i, j]`), a literal domain can stand beside a symbolic one, and a hypothesis
that is a theorem is applied. The ledger prints every statement whole, and
under the table it says what the machine lacks for a row to be proved, with
the command that installs it. loopty's five demonstrations need this release,
and loopty 0.3.0 raises its floor to it.

### Added

- **What a row lacks to be proved, said under the table.** Without Lean a
  theorem read `assumed` or `tested` and a fact isl decided `decided`, and
  nothing said that Lean would prove them, or what to install. `lanky
  check` now prints a line for each piece the machine lacks, with the rows
  Lean would prove with it and the command that installs it:

  ```text
  WITHOUT LEAN: compressed_taylor, on_every_triangle and 40 more rows are not proved. To have Lean prove what it can: pip install "lanky[lean]", and Lean v4.29.1 from elan (elan default leanprover/lean4:v4.29.1).
  WITHOUT MATHLIB: compressed_taylor, on_every_triangle and 3 more rows are not proved, since only Lean with Mathlib can state them. To have Lean prove them: python -m lanky.mathlib ~/mathlib (about 7 GB), then export LANKY_LEAN_MATHLIB=~/mathlib.
  ```

  and a `WITHOUT SYMPY` line, with the `cas` extra, for an induction over
  families where Lean has Mathlib and sympy is missing, which used to leave
  the claim `assumed` with no word why. A plugin's claim is counted where its
  obligation has parts for Lean, and under Mathlib where a part is about real
  numbers, both read without Lean; one its plugin states for its solver
  only, and a claim whose reading is refuted, are not. A Lean that is
  installed and does not start is named by its reason rather than a command
  (`LeanOracle.missing`, `LeanOracle.remedy`, and `lanky.cli.report_missing`,
  which a plugin's verb that prints a ledger can call too).
- **Hints for arithmetic where unknowns multiply** (`lanky.obligations`:
  `Product`, `Quotient`, `Hints.ring`). `omega` reads `n * j` as an atom it
  knows nothing of, so a layout's address at every size, `i + n * j`, was
  out of its reach. A plugin now gives the steps it lacks: `0 ≤ a * b` from
  `0 ≤ a` and `0 ≤ b` (`Int.mul_nonneg`), before a case split or in each
  case where its factors are not negative (`in_cases`); what Lean knows of
  `c // n` and `c % n` for a divisor that is no number (`Int.fmod_add_fdiv_mul`
  and the remainder's bounds), in the cases where the divisor is positive;
  and the arithmetic multiplied out by `simp` with the ring lemmas of `Int`,
  so that `n ^ 2 * k` and `k * (n * n)` are one atom, before `omega` runs.
  The script says so, `omega, with 2 products and the arithmetic multiplied
  out`. All in core Lean, no Mathlib. loopty states a layout at every order
  with them (S1, grudge's DOFArray and #418's `dim_tags`). A part's fallback
  adds its split to these hints, and to a theorem's application, rather than
  putting them aside.
- **Rewrites, a hint for a plugin's part** (`lanky.obligations.Rewrite`,
  `Hints.rewrites`). A part may ask for its goal to be rewritten with its
  hypotheses that are equations, in order: with no arguments, wherever one
  applies, under a sum too (`simp only`, each premise shown by `omega` from
  the range of the sums it is under); with arguments, at that one instance
  (`rw`), a family's value perhaps a family of the part applied to its first
  arguments, `Fr (3 * x + 0)`, and right to left where asked. Then a sum over
  a literal range is written out term by term and `ring_nf` compares the two
  sides. loopty states a program's postcondition so: what its calls store,
  unfolded into the claim, and a cited identity, sum factorization, used at
  the sections of the arrays where its one side is. `Hints.rewrites` holds
  both kinds of rewrite, each said by its type: a `Rewrite` is a step of
  this script, and an `Application` an identity rewritten before a theorem
  is applied (below).
- **A literal domain beside a symbolic one in an annotation**
  (`lanky.terms.literal_binders`, `MixedDomains`). `all(grad[x, e] == ...
  for x in Fin[3] for e in Fin[ne])` and `sum(... for d in Fin[3] for c in
  Fin[n])` were refused ("mixing concrete and symbolic domains in one
  comprehension is not supported"), so a claim over the three components of
  a gradient had to nest a walk over `Fin[3]` outside it. Now an annotation
  whose first reading mixes them is read again with each literal domain a
  binder, `forall x in Fin(3), e in Fin(ne)`, which Lean states as it states
  `Fin(n)`. An annotation that does not mix reads as before, a sum over
  `Fin[2]` alone still its two terms; one whose body uses the point as a
  Python value, an index into a tuple, is refused as before, and the
  refusal names the mix.
- **The parts of a complex number: `real`, `imag` and `conj`** (`lanky.real`,
  `lanky.imag`, `lanky.conj`), numpy's names, as nodes of the same kind as
  `exp`, `log` and `sqrt`. Python computes them as `.real`, `.imag` and
  `.conjugate()`, so that of a real number they are the number, `0` and the
  number, and of a truth value or a family Python has none, and Lean is
  shown none; the property tester takes a drawn complex number apart exactly;
  Lean prints `Complex.re z`, `Complex.im z` and `(starRingEnd ℂ) z`,
  Mathlib's conjugate. In Mathlib mode a statement that takes a part gets two
  more attempts, before Mathlib's whole-goal tactics: `z * conj(z)` written as
  `normSq z` cast into `ℂ`, the divisions cleared by `field_simp` with each
  hypothesis `z != 0` said of `normSq z`, and `ring`; and `normSq` written as
  the squares of the parts. So `-beta * conj(alpha) * (1 / real(alpha *
  conj(alpha))) == -beta / alpha`, a complex division multiplied out by the
  conjugate as a kernel computes it, is proved. `lanky.terms.reading_annotation()`
  says whether an annotation is being read, for a library whose functions
  make nodes of their own (loopty's `loopty.math`).
- **An identity rewritten before a theorem is applied** (`Hints.rewrites`).
  A part may name a hypothesis that is an identity, a universal whose body
  is an equation, with the values of its variables: `rw [h1 (alpha := c t -
  y s) (beta := z t - c t)]` turns the goal's left side of it into its right
  side, so that a theorem stated of `-beta / alpha` applies to a goal that
  computes it by the conjugate. Where Mathlib is, a theorem is also applied
  by rewriting the goal with it and leaving the numerals to `norm_num`,
  since `apply` does not unify `↑(1 : ℤ)` with `(1 : ℂ)`.
- **Absolute values given to `linarith` with their bounds.** A part about
  reals that takes the absolute value of a real gets `linarith` with
  `abs_nonneg`, `le_abs_self` and `neg_abs_le` of each, and a goal `|a| <= b`
  is taken apart by `abs_le` first: so a value within an allowance of
  another, `|a - b| <= e * (|b| + 1)`, is proved from an equation for `a`.
- **The total of a scatter, in Mathlib mode** (`lanky.oracles.lean.fiber_scripts`).
  A goal `sum(y[i] for i in Fin[nv]) == sum(g for c in Fin[nc] for k in
  Fin[d])`, either way round, where `y[i]` is the sum over the cells a map
  sends to `i`, `sum(g for c ... for k ... if cell[c, k] == i)`, written out
  or given by a hypothesis `all(y[i] == ... for i in Fin[nv])`, is proved by
  a script Python writes from the statement: rewrite `y` under the sum,
  turn the filter into an `if` (`Finset.sum_filter`), move the sum over `i`
  inside the map's arguments one exchange at a time (`Finset.sum_comm`,
  stepping under the outer sum on both sides with `Finset.sum_congr`), add
  up the `if` (`Finset.sum_ite_eq`), and show the cell is a node from the
  bound the map's type gives (below). That is a scatter-add keeping the
  total on every mesh, which the S3 demonstration of loopty states for
  PyOP2's assembly loop.
- **A scatter as the transpose of a gather, in Mathlib mode.** The same
  script takes the fibers' sums written out with a weight at `i`,
  `sum(sum(h[p] for p in Fin[nf] if node[p] == i) * u[i] for i in Fin[nv])
  == sum(h[p] * u[node[p]] for p in Fin[nf])`, either side of the product:
  the weight moves into the sums and their `if` (`Finset.sum_mul`,
  `ite_mul`) before the exchanges, and `Finset.sum_ite_eq` puts it at
  `node[p]`. That is a face lift as the transpose of the face gather, which
  the advection demonstration of loopty states for grudge's right-hand side;
  the total of a scatter is its weight `1`.
- **A conjunction, a conjunct at a time, in Mathlib mode**
  (`lanky.oracles.lean.conjunction_scripts`). A claim over a concrete
  `Fin[3]`, `all(... for j in Fin[3])`, is the conjunction of its three
  instances, which `ring` proves one at a time and not at once; the ladder
  now splits it with `And.intro` and closes each conjunct.
- **Families with several indices.** `Fn[A, B, C]` is a family with two
  indices, the family of families `Fn[A, Fn[B, C]]`, and any number of
  indices is curried the same way; a matrix is `Fn[Fin[n], Fin[m], Real]`.
  It is applied at all of its indices at once, `F[i, j]` or `F(i, j)`, as
  well as one at a time, `F(i)(j)`, and the three are one entry to every
  reading: the property tester's tables, the families the check of a
  reading draws as they are applied, a theorem called as a function, which
  takes nested lists, an array or a function for such a family (a function
  taking the indices at once, `lambda i, j: ...`, or one at a time), and
  Lean, which writes `F i j`. A value of another shape (a flat list for a
  matrix, an array with an axis too many, a dict) is refused with the
  parameter's name, its type and the shape it takes, and a family applied
  at more indices than it has says how many it has. A hypothesis that
  defines a family entry by entry, `all(F[i, j] == ... for i in Fin[n] for
  j in Fin[n])`, fills the tester's table, as `f(i) == ...` always did, and
  a counterexample shows a matrix as nested lists. `FnType.indices` and
  `FnType.entries` read a family's index types and what it holds, and
  `lanky.testing.apply_at` applies a family at several indices in turn. A
  claim that wrote `F[i, j]` used to be untestable ("could not run").
- **Exchanging finite sums, in Mathlib mode** (`lanky.sums`,
  `lanky.oracles.lean.sum_scripts`). An equation between sums, products of
  sums and quotients of a sum, under any universals, is proved by
  distributing the products into the sums (`Finset.mul_sum`,
  `Finset.sum_mul`, `Finset.sum_div`), exchanging the left side's sums one
  adjacent pair at a time until they are in the right side's order
  (`Finset.sum_comm`, in a `conv` per exchange), and comparing the summands
  under all of them (`Finset.sum_congr`, then `ring`). Python finds the
  order: `lanky.sums.spread` reads a side as `simp` leaves it, and
  `lanky.sums.orders` the orders of the sums whose domains agree and under
  which the summands are equal, by sympy where it is installed, within the
  claim's Lean budget. Lean checks the script; an order that is wrong costs
  an attempt. Sum factorization, a tensor-product operator applied as three
  one-axis passes, and the Kronecker product's mixed product are proved
  this way for every size.
- **A claim for every order from an order on.** The induction over families
  proves `all(c(n) == ... for n in Nat if n >= 1)`: a lower bound on the
  order in the goal's guard raises the steps tried, the orders below it are
  base cases `omega` closes from the guard, and the induction hypothesis is
  taken only where the guard admits it. A step over `ℝ` or `ℂ` shows first
  that the orders it reaches, `k + 1` to `k + step` cast into the ring, are
  not zero, which `field_simp` cannot see past `↑k + 1`. The certificate
  search splits a power whose exponent is a sum, so that `(-b / a) ** (k +
  2)` and `(-b / a) ** (k + 1)` share a factor, and a residual sympy's
  `simplify` leaves is evaluated at exact points before the certificate is
  proposed. `COMBINATION_NORM` has a last arm for such a step: the power
  split, the denominators cleared, and `ring_nf` after them;
  `lanky.oracles.lean.combination_norm(statement)` names its lemmas as the
  statement does.
- **Two demonstrations for Mathlib mode.** `examples/sum_factorization.py`:
  grudge's tensor-product operators on hexahedra (inducer/grudge PR #418),
  the exchange of two sums, sum factorization and the mixed product proved
  for every size, and numpy's dense `kron(H, kron(G, F))` with the first
  axis fastest tested. `examples/line_taylor.py`: the line-Taylor expansion
  pytential's QBX evaluates a layer potential on its own surface with, the
  coefficients of `log(alpha + tau * beta)` proved for every order under the
  differential equation the logarithm solves, `line_ode`, cited, and sumpy's
  own `LineTaylorLocalExpansion` decided against them through order 6. The
  quickstart has a section on each.
- **A plugin's claim checked by Lean, part by part, with its solver's hints**
  (`lanky.obligations`). A fact's term may offer Lean an `Obligation` through
  one method, `lean_obligation()`: parts, each a closed lanky term proved on
  its own, and for each the hints a decision procedure found, which carry no
  trust (`Hints`: `Instance`s of a universal hypothesis, a witness in
  `Piece`s for an existential goal, which may pick the disjunct it proves,
  and case splits for what `omega` lacks). The Lean oracle proves every part,
  `omega` first and then with the hints, the parts at once in a pool of
  sessions (`LANKY_LEAN_JOBS`, up to four) within the fact's budget; a fact
  whose parts are all proved is `proved` by `lean`, resting besides on what
  the obligation names, with the file that replays it and a record of each
  part (`lean_parts`), and one that is not keeps its status, with the parts
  and why in plain words (`lean_reason`: the parts by their labels, and
  whether Lean ran out of time or found no proof; what Lean said stays in
  each part's record), for the oracles after Lean. A claim the solver
  refuted comes with its `Counterexample`, and Lean proves the part false
  there by `decide` or `omega` (`lean_counterexample`, `lean_refuted_by`),
  or says it cannot, which is a disagreement (`lean_disagrees`). A refuted
  fact with no counterexample keeps its status: Lean only checks a
  refutation, and never turns one into a proof. An instance's cells that are
  the claim's written otherwise are equated for `omega`. An obligation names
  the plugin that stated it (`stated_by`). loopty states its isl facts this
  way.
- **Lean's answers kept by their source** (`ProofCache`): every declaration
  an obligation sends, accepted or refused by Lean, under the hash of the
  Lean version and the source, in `LANKY_LEAN_PROOF_CACHE` (`off` for none;
  by default `proofs` beside the REPL's build), and read back the next time;
  a timeout is not kept. `LeanSession.answer` says whether an answer is
  Lean's own, and `LeanSession.twin` starts another REPL from a running
  one's setup.
- **`lanky check --show-lean [TEXT]`** prints the Lean of every row that has
  some, or of the rows whose owner, id or statement contains `TEXT`: the file
  that replays a proof, each part of a plugin's claim as it was tried, the
  theorem that a refuted claim is false at its counterexample, and the
  statement of a claim Lean did not prove. A long theorem is shown one
  parameter to a line. A `LEAN` line under the table says, per decision
  procedure, how many of the facts it decided Lean proved, how many it did
  not and how many the plugin has not stated for Lean yet, and whose
  statements Lean proved; a `NOT PROVED` line names a fact a decision
  procedure decided and Lean did not prove, with the parts and why, and with
  `--verbose` one Lean was not asked about; a `REFUTED` block ends with
  whether Lean confirmed the counterexample. Lean's own words (`omega`,
  `decide`, its error messages) appear only under `--show-lean`. `lanky.cli.report_proved`,
  `report_unproved` and `report_lean` print them for a plugin's verb.
- **A plugin's parts about real numbers** (`Part(..., mathlib=True)`),
  printed with `ℝ` and checked in the Mathlib session, their cases closed by
  `linarith`; a hypothesis's instance whose cells the claim writes
  otherwise is equated cell by cell (`congrArg` through every argument of a
  curried family). Without Mathlib the claim is left to the oracles after
  Lean, with the reason: core Lean has no real numbers.
- **A hypothesis that is a theorem, applied** (`Hints.applications`,
  `Application`). A plugin that cites a theorem for a claim states the
  theorem as a hypothesis of the part and names the values it matched; Lean
  is asked for `intros; apply h0 (p := p) (c := c)` and closes what is left
  from the part's other hypotheses, by `omega`, or `linarith` where Mathlib
  is. loopty states a kernel's `uses=` this way:

  ```python
  hints = Hints(applications=(Application(0, (("p", p), ("c", c))),))
  Part("applied", "on_the_triangle gives R == D", claim, hints, mathlib=True)
  ```
- **The sumpy demonstration's corollary on the triangle** (#86):
  `examples/sumpy_recurrence.py` has a fourth fact, the reconstruction over
  `a + b <= p` for every order `p`, by the recurrence inside it, proved by
  Lean with Mathlib under `harmonic`. The induction over families uses a
  hypothesis where its guards follow from the goal's own guards, not only
  from the variables' bounds (`Case.facts`): `k + b + 2 <= p` from the
  goal's `a + b <= p` at `a = k + 2`.

### Changed

- **The README opens with a front page**: lanky's story first, a claim
  written as Python and proved by Lean, the ledger, and facts that rest on
  facts, with two rows from loopty's flagship where a kernel cites a
  theorem; then loopty's five demonstrations in a table, how to run them,
  with Lean and Mathlib, and where the limits are. The
  paragraph about loopty under "What nothing else does", whose refusal was
  quoted in an older wording, now points to that section. Run it and
  Install install this release from PyPI: loopty's demonstrations no longer
  need lanky's `main`.
- **`lanky check` prints every statement whole** (#142). A statement too
  long for its column was cut at 72 characters, so a theorem showed its
  variables and never its conclusion, and a postcondition, a theorem applied
  to a kernel or a comparison with upstream lost its end. A statement that
  fits is still one line; a longer one goes on under the statement column,
  broken at spaces. A theorem is printed a part to a line: its variables,
  each hypothesis under the name of its parameter (`| pde: ...`), and the
  goal after `|-`, from the `sequent` its fact now carries in its
  provenance. Any other statement is broken before an `and` that joins two
  claims, after a label's `:` or a quantifier's `.`, or before a guard's
  `where`, outside brackets where it can be, and indented a step for each
  bracket it breaks inside. The column is 100 characters wide where it was
  72, so that most of a kernel's facts are one line and the table does not
  double in height; in a terminal it takes what the other columns leave,
  between 40 and 100, and written to a file or a pipe it is 100, so a
  transcript does not depend on the window it was made in
  (`Ledger.render(width=100, columns=...)`, `lanky.cli.terminal_columns`).
- **`LANKY_LEAN_DISABLE` prints what a machine without Lean prints**, the
  `WITHOUT LEAN` line (under Added) included, so a CI job that sets it checks the
  transcripts such a machine shows.
- **A warm check starts no Lean REPL** (#118). The Lean oracle reads every
  attempt of every part from the proof cache first, under the version of the
  Lean it would run (the pool's, else `LANKY_LEAN_VERSION`, else the
  toolchain found), and starts a session only for a part with an attempt
  that is not kept; a counterexample is checked from the cache the same
  way. A theorem of lanky's own is kept and read back the same way, every
  attempt of its ladder and its side conditions, where before it was asked
  of Lean on every check: a Mathlib theorem whose ladder tried a few dozen
  attempts was most of a warm check's time. Mathlib's answers are kept
  under the project's toolchain and Mathlib revision together, read from its
  files, so a part about reals and a Mathlib theorem are read back without
  importing Mathlib, and a Mathlib upgrade reads no stale answer. `lanky
  check` on a file checked before, with nothing changed, prints the same
  ledger without starting Lean:

  ```console
  $ lanky check examples/gauss.py   # the second time: no REPL, same rows
  ```
- The `LEAN` line under the ledger counts the claims about reals core Lean
  was not asked apart, and says where Lean checks them: `LEAN proved all 11
  facts isl decided; 2 more are about real numbers, which Lean checks where
  Mathlib is (LANKY_LEAN_MATHLIB)`. It said they were not stated for Lean
  yet, and left out one a cited theorem decided.
- A family of families prints as the family with several indices it is:
  `Fn[Fin(n), Nat, Nat]` where it was `Fn[Fin(n), Fn[Nat, Nat]]`, in a
  statement and in a reason that names the sort.

### Fixed

- **A generator's binder names are read once per code object** (#125).
  `sum(... for p in Fin[n])` disassembled its generator at every call to
  name its binders, and a kernel run natively sums once per instance: that
  was about 15 of the 45 seconds `lanky check` took over loopty's
  hexahedra demonstration. The rest was loopty's interpreter, which loopty
  makes faster on its side.
- **A family applied at another's value, `u[node[p]]`, printed.** For a
  `node: Fn[Fin[nf], Fin[nv]]` and a `u: Fn[Fin[nv], Real]`, `node[p]` is
  not affine, so the printer could not place it in `u`'s domain and declined
  the statement ("applies u outside the domain it declares"), though its
  value is a point of `Fin[nv]` by `node`'s type. A theorem's statement
  takes `node`'s bound as a hypothesis, so Lean knows it too, and the
  application is in the domain where the values' bound is at most the
  domain's; printed as one proposition, with no such hypothesis, it is
  declined as before, and so is a map whose values reach past the domain.
- **A family whose type mentions a name bound again inside is declined.**
  `node: Fn[Fin[1], Fin[n]]` under an inner `n in Fin[m]`, or `u: Fn[Fin[m],
  Int]` under an inner `m in Fin[5]`: the bounds the printer read the
  application against were the inner name's, and the family's type means
  the outer one, so an application past the family's domain could look in
  bounds. The refusal names the name and asks for the inner binder to be
  named apart. A family bound after the inner name means that one, as a cited
  theorem's own parameters do inside a claim with the same names, and is
  read as before.
- **A fact a plugin names shortly is named so in the status column.** A
  fact that rests on one of a kernel's many facts showed that fact's id,
  `decided under assumption:demo.k@4:[c].assume('n % 4 == 0')` for a cast
  under a schedule's assumption; a `label` in the fact's provenance is
  shown instead where the owner does not name one fact, `decided under
  assume('n % 4 == 0')`.
- **A family whose values are a `Fin` keeps their bound in Lean.**
  `cell: Fn[Fin[nc], Fin[d], Fin[nv]]` prints as `Int → Int → Nat`, which
  says the values are not negative and not that they are below `nv`, so a
  claim resting on that bound was a stronger claim in Lean than in Python,
  and one Lean could not prove. The statement now takes the bound as a
  hypothesis after the family, `∀ c, 0 ≤ c → c < nc → ∀ j, 0 ≤ j → j < d →
  (cell c j : Int) < nv` (`lanky.lean.codomain_bound`), and
  `LeanStatement.codomain_bounds` names it for a strategy.
- **A fact a plugin hands over already settled** (loopty's casts, decided
  by isl as each schedule step is taken) is no longer counted as settled by
  an oracle that hands it back as it came, with only its notes on why it did
  not prove it: the walk goes on to the next oracle, and the fact keeps the
  trust class its checker gave it. An oracle settles such a fact when it
  changes its status or says it decided it (`decided_by`).
- A hypothesis that defines a family written with brackets,
  `all(f[i] == 2 * i for i in Fin[n])`, was read only as a filter on random
  draws, which met it at the smallest sizes alone, so that a false claim
  about such a family could read `tested` on them. It fills the tester's
  table now, as `f(i) == 2 * i` did.
- A dict given for a family to a theorem called as a function was read as
  the list of its keys. It is refused, with the shapes a family takes.

## [0.2.0] - 2026-10-11

The faithful fact (#91). lanky reads an annotation by running its Python on
symbolic terms, and every oracle is handed the term that run builds. Each
theorem and axiom now gets a second fact, its reading: the annotations are run
again as plain Python at drawn points, in a copy of the module's state taken
just before the claim was read, and the term has to compute the same at each.
That closes the class the 0.1.0 Known limits named, an operation that answers
from a term object rather than through its overloads (`is`, an attribute, a
hash, a text or a truth value inside a helper or a library, a comparison of
types; #79, #80, #88): such a reading is refuted at a point, and no oracle is
asked about the claim. Every ledger changes shape. Each claim is followed by
its reading, and every pass, decision and proof rests on it, so a proof is
worth `tested` in the `EFFECTIVE` column. A theorem in a loopty file has its
reading too, and loopty, whose documented ledgers show it, raises its floor to
lanky 0.2.0.

The check was hardened in the same waves: each draw has a time budget of its
own (#101, #113, #114), what follows an operation with no value is compared
(#99), and a cached helper, a `:=` in a lambda and a parameter named like a
builtin read as written (#105). Outside it: Python's `abs` of a term is
lanky's `Abs` (#94), `exp`, `log` and `sqrt` of a number stay exact (#81), a
negative number to a power that is not an integer is Python's complex value
(#89), the CAS oracle translates within its deadline (#77), the Lean ladder
has a budget per fact (#83), and the cross-check hears every tester (#41).
The README's Known limits section lists the open issues a user is most
likely to meet, each with what to do about it.

### Added

- **The `faithful` fact (#91).** lanky reads an annotation by running its
  Python on symbolic terms, and every oracle is handed the term that run
  builds. `lanky.faithful.faithful_fact(theorem)` checks that reading by its
  results: each annotation, the goal, each hypothesis and each variable's
  sort, is run again as plain Python at drawn values, in the module as lanky
  found it when it read the claim (`Theorem.snapshot`, below); the term is
  evaluated at the same values, and the two have to agree.
  - The snapshot (`lanky.faithful.capture`, `Snapshot`; #102, #103). Just
    before a claim is read, what its annotations reach is copied: the names
    they read, the functions of the user's modules they call (the claim's
    module and the modules beside it, under the file's source roots), the
    names those read, their defaults and what they close over, with tables,
    lists, sets, tuples and numpy arrays copied item by item and nested, up
    to `COPY_ITEMS = 65536` items and `COPY_ELEMENTS = 2 ** 20` array
    elements. The functions are bound to the copy, two that closed over one
    cell close over one copy of it, a view of an array is made again over
    the copy of the array it views, so that a write through one view is read
    through another, and a `functools.partial`, a function behind
    `functools.lru_cache`, with the entries its cache holds and its hit and
    miss counts (#105), and a
    method bound to a copied table (`TABLE.get`) are made again around the
    copies. Every draw runs in a
    copy of that copy, so a helper reads what it read when the claim was
    read, whatever the module rebinds or changes in place after the claim
    (`TABLE.clear()`, `list.append`, `ARRAY[:] = 0`), and whatever a helper
    changed at the draw before.
  - What the copy cannot hold as it was is not pretended: an object of a type
    it does not know (an instance of a class of the user's, a random
    generator), a structure past the budget, a class of the user's that holds
    a method or data, a value read off a class or an installed module by name
    that would need a copy (`Rules.table`), a function behind
    `functools.lru_cache` whose entries cannot be read off its cache, and a
    module of the user's that a function imports as it runs. A reading that
    reaches any of it and agrees
    at every draw is `assumed`, not `tested`, with each such object and why
    in the reason, so a proof of the claim reads `proved under
    faithful:name`. Libraries, lanky included, are read as they are.
  - The draws: six of small values and domain ends first (`CORNERS`, every
    natural the tester draws and a domain's first and last points, smallest
    first, so a refutation names a small point); then one at each integer
    written in the claim, in the helpers it calls and in what they read, and
    next to it (up to `WRITTEN` of them, none past `WRITTEN_MAX = 4096`, and
    for a value that sizes a domain, none past the size at which the claim's
    nested domains hold about `SIZE_POINTS = 1024` points, a draw at which a
    reading walks more than `WALK_POINTS = 32768` all the same being given up
    as `unwalked`), so that a helper misread only at `6`, or at a key `1000`
    of a table, is reached; then 32
    of the property tester's (`SAMPLES`), with definitional hypotheses
    satisfied by construction. A bounded quantifier is enumerated, and one
    over a sort runs over a sample of it, the written integers included, the
    same on both sides (`lanky.terms.concrete_sorts`). A family over a sort,
    `Fn[Nat, Real]`, which the tester cannot tabulate, is drawn at each point
    as either reading applies it (`DrawnFamily`). A refinement no draw
    satisfies is drawn from what it refines: the readings are compared
    whether or not the hypotheses hold.
  - Both readings read the connectives and the quantifiers as lanky does,
    three-valued, passing over whatever an operand or a point raised: the
    rerun's `~`, `&` and `|` of truth values are `not`, `and` and `or`
    (Python's `~True` is `-2`, and its `|` asked `f(-1)` of `(i == 0) | (f(i -
    1) <= f(i))` at `i = 0`), and its `all` and `any` over a generator walk
    every point, with the `if` clauses as one conjunction of guards, as the
    term holds them, so an earlier clause with no answer and a later one that
    rejects the point read alike in either order (#97). Python's `all` stops
    at the first point that raises, and a comparison that stopped there on
    both sides never compared the points after it: `all(f(i) * 0 + (1 // i) *
    0 == table(i) for i in Fin[n])`, misread at `table(1)`, read `tested` and
    Lean proved its term. A `sum` walks every point too, has no value where a
    point has none, and is then compared point by point.
  - What follows an operation with no value (#99). Inside any other
    operation Python stops at the operand that has no value, and so does the
    term, so what came after it was compared on neither side: `all(f(i) * 0 +
    1 // (i - i) == table(i) for i in Fin[n])`, misread at `table(0)`, read
    `tested`, and Lean proved its term, where `1 // 0` is `0`. A draw at which
    both readings of an annotation have no value is read again on both sides
    with what Python has no value for read as Lean has it
    (`lanky.terms.totalized`): `x / 0` and `x // 0` are `0`, `x % 0` is `x`,
    `0 ** -k` is `0`, a logarithm or a square root outside its Python domain
    is Mathlib's, and a family outside its domain is `0` (a family that is `0`
    everywhere for a family of families, `False` for truth values). Where both then have
    a value they have to agree, and a disagreement refutes the reading, with
    `totalized` and what the first reading `stopped` at in its provenance.
    The rerun reads so the operators the annotation writes, and the term all
    of its own, so a helper's division, which the rerun leaves Python's, gives
    the second reading no value and says nothing more. A draw whose second
    reading is given up is given up, and the first reading's agreement there
    is not counted.
  - A time budget per draw (#101). The readings of a claim's annotations at
    one draw, and the draw's second reading with them, may take
    `DRAW_SECONDS = 5` seconds, and a power or a left shift either asks for
    may have `POWER_BITS = 2 ** 20` bits; past either, the draw is given up
    as `slow`, as a walk past `WALK_POINTS` is given up as `unwalked`. The
    walks and the term's reading ask for the time as they go, and the user's
    code, the annotations and the functions of the claim's module and of the
    modules under its source roots, the methods of their classes included,
    is watched with `sys.monitoring` while the draws run, so that a helper's
    own loop, or a helper that calls itself, is stopped at its next call or
    turn of a loop. No interval timer keeps that time, so a `lanky.deadline`
    set around the check keeps its own, and what it raises passes through
    the check to its owner. A draw given up stays given up where a helper
    catches everything, the giving up included, and answers. A helper that
    took time exponential in its argument, at a value the claim writes, ran
    as long as Python took.
  - Each draw has that time of its own, a written value past one too slow
    to draw at too (#114): a helper too slow at `999` that answers
    otherwise at `1000` is refuted there. Past `SLOW_DRAWS = 4` draws of a
    claim given up as `slow`, the check makes no more, and the reading is
    declined, naming them (#113), so a helper slow at the small values the
    corners and the tester draw costs a claim five draws' time, 25 seconds,
    where one cost 95.
  - The term is evaluated at the same values in Python's arithmetic, its
    sums added with Python's `sum` over the same values, which compensates as
    it adds since 3.12, so that both readings round alike.
  - Agreement: the same truth value or the same value, exactly. A truth value
    against a number disagrees, and so does an exception on one side only,
    whatever it is: `i.name` raising at a number where the term has a value,
    and a division by zero where Python has no answer and the term has one,
    as `(f(i) * 0 == 1 // i + 1) | (i is not 0)` at `i = 0`, whose term reads
    `or True`. Where both have no answer for one reason (a family outside its
    domain, a division by zero, an elementary function outside its domain, an
    overflow), they agree. Nothing is put down to rounding: a helper
    answering `x * (1 + 1e-12)` at a number and `x` at a term is refuted, where
    a tolerance would have let the CAS decide `1.0*x == x`.
  - The fact, of kind `faithful` (`lanky.ledger.FAITHFUL`), id
    `faithful:module.name@line`, owner and location the claim's, statement
    `the term computes what the annotations compute`, is `refuted` by
    `python` at the first draw that disagrees, with the draw as
    `counterexample`, the annotation as written as `witness`, and both
    answers in the `reason` (and as `python_answer`, `term_answer`);
    `tested` by `python` when every annotation was compared at some draw and
    none disagreed, with the counts; and `assumed`, with the reason as
    `declined`, when one cannot be compared: a free name, a sort no value can
    be drawn of, an annotation Python evaluated when the function was
    defined, one with no answer on both sides at any draw.
- `Theorem.faithful_fact()`, made once per claim; `Theorem.fact(reading)`,
  which records the reading's id as `faithful` and, when it is refuted, why,
  as `unfaithful`; `Theorem.snapshot` and `Theorem.namespace`, the
  snapshot's copy of the module's globals; `Fact.is_reading`.
- `lanky.terms.code_reads(code)` and `CodeReads`: the names a code object
  and the code compiled inside it read from their globals, which of them
  only to read an attribute off (`helpers.TABLE`), what they close over and
  import, read off the instructions.
- `lanky.terms.concrete_sorts`, `sort_points` and `rerunning`: what a sort
  iterates while an annotation is run again at concrete values.
- `lanky.terms.totalized` and `is_totalized`: a block in which
  `elementary_value`, a `lanky.testing.Table` and the faithful fact's
  operators read what Python has no value for as Lean has it (#99), and
  `lanky.testing.totalized_value`, what a family is there outside its domain,
  with the `codomain` a `Table` now takes.
- `lanky.faithful.DRAW_SECONDS`, `POWER_BITS` (#101) and `SLOW_DRAWS`
  (#113).
- **The pytest plugin fails a theorem whose reading is refuted**, with the
  annotation, the draw and the reason, before any draw of its term, which
  would test another statement.
- **A budget for the Lean ladder** (#83). `LANKY_LEAN_BUDGET` (120 s by
  default) caps the whole ladder of one fact, and `LANKY_LEAN_VACUITY_BUDGET`
  (30 s) that of a question whether a fact is vacuous, whose answer is
  almost always no; `0` is no budget, and `LeanOracle(budget=...,
  vacuity_budget=...)` sets them for one oracle. A budget that is not a
  finite number, from the variable or the constructor, declines the fact,
  saying so, rather than leaving the ladder unbounded. A statement no attempt fits
  paid for every attempt, each up to `LANKY_LEAN_TIMEOUT`, and nothing
  bounded the ladder: `lanky check examples/sumpy_recurrence.py` took 491 s
  in Mathlib mode before its large row was declined for Lean. The budget
  counts the search for the family induction's certificates, which is
  Python and ran with no budget at all (about 10 s per Helmholtz claim on
  an older machine), the side conditions and every attempt; it starts once
  the REPL is running, so starting it, which imports Mathlib, counts against
  no fact. An attempt is given what is left when that is less than its
  timeout, and a fact whose budget runs out keeps its status and says after
  how many attempts (`lean_reason`, `lean_budget`). `lean_tried` counts the
  attempts made. `LeanSession.ready()` starts the REPL, or starts again one
  a timeout killed, and `LeanSession.run(source, until)` takes the end of a
  budget.
- `lanky.deadline`: `deadline(seconds, owner)` and `Expired`, the interval
  timer the CAS oracle kept as its own, shared with the Lean oracle's
  search; an `Expired` names its deadline's owner, so a caller tells its
  own from one set around it. A timer that goes off as the block ends no
  longer leaves the deadline's handler installed: it raised in the
  `finally` that stops the timer, before the handler there was was put
  back, so the next `SIGALRM`, meant for someone else, raised `Expired`.
- `lanky.cas.check_shape(term)`: everything `equations` refuses a statement
  for, checked without sympy and without building anything, but whether a
  real logarithm's or square root's argument may be negative, which only
  sympy can say (#77).

### Changed

- **Each theorem and axiom is two facts.** `TheoremTheory.facts` yields the
  claim and then its reading, so every ledger has a row under each claim,
  `tested python ... the term computes what the annotations compute`, and its
  count of facts doubles for theorems; `--json` has the reading as an entry
  of kind `faithful`. A plugin's facts are not read, so loopty's kernels and
  programs have no such row (they have `trace-faithful`), and a theorem a
  loopty file holds has one.
- **Every pass, decision and proof of a claim rests on its reading**
  (`rests_on` gains the reading's id), so the ledger's weakest link shows
  it: a proof is worth `tested` in the `EFFECTIVE` column, which every
  ledger with a proof now has, and `proved under faithful:name` where the
  reading could not be run. An axiom does not rest on its reading, since it
  is `assumed` on its citation whatever that is worth, unless the reading is
  refuted.
- **A claim whose reading is refuted is offered to no oracle**, the property
  tester included, and stays `assumed`, resting on the refuted reading, so it
  is worth `refuted` and `lanky check` exits 1. `lanky.check.establish`
  returns a reading's fact as it is: it was established when it was made.
- The table names a reading `faithful:owner` where it names a fact, and
  counts readings apart from claims, so `proved under harmonic` still names
  the axiom `harmonic` and not its reading.
- A reading left `assumed` gets a `DECLINED` line only where something rests
  on it, a pass or a proof of its claim. Otherwise its claim is an axiom, or
  is `assumed` itself, and its own line says why; the pytential
  demonstration's eight axioms about boundaries, which no draw can make,
  print none.
- A later claim of an id that is refused as a duplicate (#52) takes its
  reading with it.
- **An annotation that reads `all`, `any`, `sum` or `abs` in a module that
  binds the name to anything but Python's builtin or lanky's own is refused
  while it is read** (#100), naming the binding and the fix: leave the
  builtin unbound in a module of claims, or call the module's function under
  another name (`np.abs`). lanky reads these four names in an annotation as
  its own, put in the scope after the module's globals, so a module's own
  `def all(gen): return False`, or numpy's `abs` from `from numpy import
  abs`, was passed over and the claim proved under lanky's reading.
  `from lanky import sum` is lanky's own and still reads, and a name the
  annotation does not read, one a helper calls, is no matter: the helper
  calls the module's binding in both readings.
- The README's Known limits section says what the check is and what it
  cannot see, points no draw reaches and claims whose annotations cannot be
  run at a point, and then lists the open issues a user is most likely to
  meet, each in plain words with its fix or workaround: a theorem called
  directly (#96), `math.floor` of a variable (#112), `min` and `max` (#66),
  a family over `Nat` (#98), a slow step in C (#108), an installed package's
  state (#104), what follows a helper's operation with no value (#107), and
  Windows (#47, #48). The issues it named that are fixed are gone from it.
  Its status paragraph is 0.2.0's. The quickstart has a Check the reading
  section, and every ledger in both is run again.
- The publish workflow builds in a job that can only read the repository, with
  a checkout that keeps no credentials, and uploads from a second job that
  alone may ask for the token PyPI trusts and runs no checkout or build. Before,
  one job held `id-token: write` while it ran the build, so the build backend
  or anything it pulled in could have asked for that token.
- **Python's `abs` of a term is lanky's `Abs`** (#94), as an annotation's
  `abs` is. It was pymbolic's `Call` of a variable named `abs`: an order of
  it raised `expressions don't have an order`, and `==` and `!=` of it were
  pymbolic's structural equality, a `bool` while the term was built, so
  `(127 == abs(c[i])) * 1` held `0` in a loopty kernel whose body compares.
- **`exp`, `log` and `sqrt` of a number in an annotation stay exact** (#81).
  They were computed by `math` while the annotation was read, so `exp(1) >
  2.718281828459045` was the constant `False`, and the tester refuted a
  claim true of `e`. Called by the annotation's own code, `lanky.exp(1)` is
  an `Elementary` node now, which the tester encloses, the Lean printer
  writes `Real.exp 1` and the CAS bridge reads as sympy's `E`. Anywhere
  else it is Python's value, as before: in the file run as a program, in the
  annotation run again by the faithfulness check, and in a function the
  annotation calls, whose code may compute with the number as Python does.
  An annotation whose `log(0)` or `sqrt(-1)` raised while it was read is
  read now, and meets the gap to Mathlib's total functions as `log(x)` under
  `x == 0` does: in Mathlib mode Lean proves `log(0) == 0`, with the
  semantics note. Python that asks for a number gets the one Python
  computes, as in a helper: `math.floor(exp(2))` and `math.isclose(exp(1),
  math.e)` ask the term for its float, which a term with no variable in it
  now gives, as Python reads it, where pymbolic's float knew no lanky node.
- **`all` and `any` over a concrete domain join the terms they are given.**
  A body that is a term at each point, `all(exp(k) >= 1 + k for k in
  range(4))` now that `exp(k)` is one (#81), is the conjunction, or the
  disjunction, of its values, unless a concrete value settles it. The
  builtin asked each value for a truth value: a proposition refused it, so
  that annotation could not be read, and a term that is a number answered
  from its structure, so `all(f(k) for k in range(3))` of a family was
  `True`; such a number is now held in the conjunction, and has no truth
  value there for any oracle.
- **A negative number to a power that is not an integer is Python's complex
  value** (#89). The tester's exact reading left it undecided, so a claim
  false only at negative bases, `(x ** 3) ** Fraction(1, 3) == x`, read
  `tested` on the positive draws. It is the principal value now, as
  `cmath` computes it, `|x| ** p * (cos(πp) + i sin(πp))`, exact for an
  exponent with denominator two and enclosed part by part otherwise, so
  that claim is refuted at `x = -1`; an order with it is refused, as Python
  refuses one.
- **The cross-check hears every tester** (#41). It stopped at the first
  tester of the `test` class with anything to say about the hypotheses, so
  a plugin's sampler ahead of the property tester that drew nothing valid
  kept the property tester's `goal_reached: 0` from being heard, and a proof
  of a goal whose guard is empty read `proved` with a warning about the
  hypotheses. What is said about the hypotheses comes from the first tester
  that says anything, and the goal's count from the first that has one, as
  for an axiom; a counterexample still ends the walk, and is recorded alone.
- **The CAS oracle translates a statement within its deadline** (#77).
  `can_establish` read the whole statement into sympy, and `establish` read
  it again before it armed the timer, and sympy's constructors evaluate as
  they build. `can_establish` reads the shape now (`check_shape`), and the
  translation is inside `LANKY_CAS_TIMEOUT`, declined as `sympy did not
  finish translating the statement within ... s` when it runs out there. The
  deadline is the oracle's own: a deadline set around it, which is its
  caller's, is raised again rather than taken for sympy running out. A
  real `log` or `sqrt` of what sympy cannot show is not negative is found
  out in the translation, so such a statement is taken and declined, with
  the reason, where it was not taken at all.
- **A question whether a fact is vacuous gets the attempts that can answer
  it** (#83). Its goal is `False` under binders, so the ladder leaves out the
  inductions, over a family, on a recurrence and on a reduction's bound, and
  the whole-goal tactics that close only an equation or an order:
  `positivity`, `ring`, `field_simp` and `ring` after `push_cast`.
- The sumpy demonstration says what its tolerance is relative to (#78): the
  difference of a reconstructed coefficient and mpmath's derivative is
  measured against the derivative or `1`, whichever is larger, relative
  above `1` and absolute below, where the finite differences are accurate
  to the kernel's scale and a derivative that is `0` at a point comes out as
  a few units in its last digits. The docstrings, the reason of a
  refutation, the run's last lines and the quickstart called it relative;
  the `mpmath` oracle records it as `tolerance`, and `difference` and
  `TOLERANCE_POLICY` name it.
- The tests that time an attempt out give one that sleeps in Lean for five
  seconds a tenth of one (#85), where a quick `omega` given a microsecond
  could be answered before lean-interact's timeout was kept, on a busy
  machine, and read as closed.

### Fixed

- An annotation that agreed at a draw on which a later annotation was then
  given up, as too slow or unwalked, no longer keeps that agreement: a draw's
  comparisons count only once the whole draw, its second reading included,
  is made. Before, an annotation that agreed only at such draws could make
  the reading read tested.

- **A function behind `functools.lru_cache` is copied with its entries**
  (#105). The snapshot made it again with an empty cache, and later declined
  a reading that reached one with entries: an entry answers where the
  function, run on the copy, may answer otherwise. The copy is now a cache
  of the same size around the copy of the function, holding the same
  entries, their results copied, in the order the cache evicts them, and
  counting its hits and misses on from the original's, so a claim that reads
  a cached value from before it, or the cache's counts, reads `tested`,
  where it was refuted and then declined. The entries are read off the cache as the
  garbage collector lists them, and a cache whose entries cannot be read so
  is shared, and the reading declined, naming it. So is a reading whose
  draw's copy cannot make again what the snapshot copied
  (`Snapshot.fresh_copy`), which the draw read as it was, saying nothing.
- **`:=` in a lambda of the annotation's binds in the lambda** (#105). The
  rerun bound every `:=` in the annotation's globals, where one in a
  generator binds, so with a module-level `x = 1`, `((lambda: (x := n))() ==
  n) & (x == 1)` read `x == 1` as `n == 1` and was refuted. A `:=` in a
  lambda now sets the lambda's own variable, from an operand of `&` or a
  quantifier inside it too.
- **A parameter named like a builtin the module binds is the parameter**
  (#105). #100's refusal read every name the annotation reads, so after
  `from numpy import abs`, `def identity(abs: Nat) -> abs == abs` was
  refused, though in both readings `abs` is the parameter. A parameter's
  name is exempt from it, and the rerun does not read a parameter named
  `all`, `any` or `sum` as a quantifier or a sum.

## [0.1.0] - 2026-10-08

The first release on PyPI, where only the 0.0.1 placeholder that reserved the
name was before. `lanky check` prints one ledger of the claims in a file, each
with its status and who established it: tested by the property tester,
decided (heuristic) by the CAS oracle where sympy is installed (the `cas`
extra), and proved by Lean where the `lean` extra and a toolchain are, in
core Lean or, with the Mathlib project `python -m lanky.mathlib` sets up,
over the reals and the complex numbers and by induction over families of
expressions. A fact can rest on others, a theorem on the axioms it cites,
and a row says what it is worth given what it rests on. The README's Known
limits section says where a proof can be of something other than the claim:
an annotation is traced Python, and an operation that answers from a term
object rather than through its overloads (`is`, an attribute, a hash or a
text inside a helper or a library, a comparison of types) is not checked yet
(#79, #80, #88). The check that closes the class, a `faithful` fact for every
claim (#91), is planned for 0.2.0.

The entries below are every change since 0.1.0.dev0. Neither development
version was published. 0.1.0.dev1 was the version on `main` from 2026-09-30,
when a fact id changed, and loopty, which builds its ids with the same
function, raised its floor to match.

### Added

- `lanky.check.module_name(path)`: the module name a file's path gives it
  under its source root (the last of `source_roots`), dotted.
  `root/pkg/sub/mod.py` is `pkg.sub.mod`, a package's `__init__.py` is the
  package, and a file outside any package is its stem. `None` for a path that
  names no file, such as the `<string>` of a function compiled from a string
  or a symbolic link that leads back to itself.
- `lanky.cli.decline_lines(fact)`: the lines `lanky check` prints under a
  `DECLINED` line, from the standard provenance key `declined` (#37).
- `lanky.intervals.complex_log_value`, `complex_sqrt_value`, `atan2_value`
  and `pi_value`: the principal complex logarithm and square root of the
  exact reading, the argument of a complex number in `(-π, π]`, and `π`
  (#51).
- `lanky.lean.global_name(name)` and `lanky.lean.ROOT_NAMES`: a root
  declaration as a statement's source names it, `_root_.Int` where a variable
  is named `Int`; and `LeanStatement.shadowed` and `LeanStatement.qualified`,
  which carry that to a tactic script (#43).
- `LeanStatement.side_conditions`: the statements Lean has to prove before a
  Mathlib statement means in Lean what it means in Python, one per argument
  of a complex logarithm or square root, that it is off the branch cut; and
  `lanky.oracles.lean.SIDE_CONDITION_TACTICS`, what the oracle tries on them
  (#59). A proof of a statement with any lists them in its provenance as
  `lean_side_conditions`.
- `lanky.lean.elementary_arguments(term)`: every `exp`, `log` and `sqrt` in a
  term, with what its argument is as a number (`Int`, `Real` or `Complex`) as
  the printer reads it (#59).
- **A computer-algebra oracle, `cas`, behind a `cas` extra** (#3). It is of
  the `heuristic` trust class, so a fact it decides reads
  `decided (heuristic)`, the property tester still samples it, and a
  counterexample overrules it. It takes a statement that asserts equations,
  alone, in a conjunction, or under universals whose variables range over
  numbers, with sides built from arithmetic, `abs`, `exp`, `log` and
  `sqrt`, and decides it when `sympy.simplify` takes the difference of the
  sides of every equation to `0`. It decides nothing else: a difference
  left over is no counterexample, since sympy may not have found the
  identity, so the fact is declined with the difference in the reason, and
  the tester, which can refute, is asked next. The hypotheses are not read,
  since an identity that holds everywhere holds wherever they do. A fact
  gets `LANKY_CAS_TIMEOUT` seconds (60), and `LANKY_CAS_DISABLE=1` turns
  the oracle off, as `LANKY_LEAN_DISABLE` does Lean's. It is available
  where sympy imports (`pip install lanky[cas]`), and sympy is imported on
  the first fact it is offered, never with lanky. A decision records
  `cas_equations`, `cas_seconds` and `cas_version`.
- `lanky.cas`: the bridge the oracle reads statements through, and that a
  plugin building claims from sympy's output can use. `to_sympy(term,
  symbols)` and `equations(term)` take a lanky term to sympy, a variable as
  a symbol with what its sort grants (`Real` is real, `Int` an integer, and
  `Nat` and a point of `Fin[n]` an integer that is not negative) and a
  float as the rational it holds; `from_sympy(expr)` builds lanky's own
  nodes back, a rational as a `Fraction`, a negative power as a quotient
  and a half power as `lanky.sqrt`. Both are strict: a family, a
  subscript, a reduction, a floor division, a variable whose sort is not a
  set of numbers or that no quantifier binds, a real `log` or `sqrt` of an
  argument sympy cannot show is not negative (below zero sympy's value is
  complex, Python's `math` raises and Mathlib's is real), a sympy float and
  `pi` raise `lanky.cas.Untranslatable` with the reason.
- `examples/sumpy_recurrence.py`, a second worked case of a consumer (#3).
  It claims that sumpy's compressed Taylor wrangler for the 2-D Laplace
  kernel (`LinearPDEBasedExpansionTermsWrangler`) reconstructs every
  derivative of `log r` through order 6 from the 13 it stores, with the
  recurrence read off the wrangler, and checks the claim twice in one
  ledger: `tested` by mpmath, which takes the derivatives numerically at 20
  points, and `decided (heuristic)` by the CAS oracle, which simplifies the
  28 equations sympy's derivatives give. Above them is the kernel's
  harmonicity, `G_xx + G_yy == 0` away from the origin, an axiom taken on
  its citation, which neither row rests on and a proof for every order
  would. sumpy, sympy and mpmath are imported inside the script, and its
  tests skip where sumpy is not importable.
- `lanky.terms.BuiltinName` and `lanky.terms.EVALUATED_BUILTINS`: the name of
  one of Python's builtins in an annotation, which is a variable where it is
  named and the builtin where it is called at concrete arguments, and the
  builtins that are (#63).
- **Induction over families of expressions, in Mathlib mode** (#3). A claim
  about every order, a universal over naturals whose body is an equation
  between applications of the statement's families, under hypotheses that
  are equations under universals of their own (a recurrence, a PDE, what
  holds at the lowest orders), is proved by strong induction on the order,
  with the goal's other variables free in the induction hypothesis
  (`lanky.oracles.lean.family_induction_scripts`, in the ladder after the
  core attempts). The step size is read off the hypotheses: one that relates
  `R(a + 2)` to `R(a)` makes it 2. The orders below the step are the base,
  closed for all of them at once or one at a time after `interval_cases`,
  and the order `k + step` is the step. Each case is closed by
  `linear_combination` over the hypotheses and the induction hypothesis,
  normalized by `ring`, by `ring_nf` where two uses write one point
  differently, or by `field_simp` and `ring` where there are denominators
  (`lanky.oracles.lean.COMBINATION_NORM`), and every guard of a hypothesis
  it applies is discharged by `omega`. Python searches and Lean checks: the
  combination, which hypothesis at which point and with which multiplier,
  is found by `lanky.induction.find_certificate`, and a wrong one costs an
  attempt, never a proof.
- `lanky.induction`: the search. A `Case` is one case of the induction, its
  goal and the `Lemma`s it may use; a finder takes a case and returns the
  `Use` of each lemma, at the values it is applied at and with its
  multiplier. lanky's finder instantiates a lemma where one of its
  applications of a family is an atom of the goal, by solving the affine
  equations between their arguments, and the instances' atoms in turn, for
  a few rounds; proposes an instance only where the case's bounds show its
  guards as affine inequalities over the integers, so the induction
  hypothesis is used only below the order being proved and a hypothesis
  only inside the domain it quantifies; and solves for the multipliers over
  the rational functions of the statement's other variables, so that
  Helmholtz's step takes the induction hypothesis times `-k**2`. It is
  sympy's (the `cas` extra), and finds nothing without it. Also
  `lemma_of(name, term)`, `domain_conditions(var, domain)`, `substitute` and
  `substitute_domain`.
- The certificate hook: `lanky.oracles.lean.use_certificate(claim, finder)`
  has the induction ask `finder` instead of lanky's search, for a plugin
  that knows its multipliers; and `LeanOracle.certificates`, where it is
  kept. `tactic_ladder(statement, finder)` takes one too. A case says which
  variable is induced on and with what step (`Case.order`, `Case.step`), so
  a hook can answer for the induction it means, and a script is written for
  every variable and step whose cases it answers, Lean judging each.
- `lanky.oracles.lean.decline(claim, reason)`: the Lean oracle leaves one
  claim to the oracles after it, recording the reason as `declined`, without
  opening a session; kept in `LeanOracle.declines`.
- `lanky.lean.render_term(expr, types, ...)` and `lanky.lean.number_type`:
  a term printed inside a proof, with the names a statement bound around it
  typed, and the ring its value is in, which a multiplier is ascribed.
- The sumpy demonstration's third row, the claim for every order (#3). Over
  two tables of reals indexed by `(a, b)`, the derivatives `D` and the
  reconstruction `R`: if `D` satisfies the PDE at every order, and `R` is
  `D` where the wrangler stores and follows the recurrence everywhere else,
  then `R` is `D`. The recurrence is read off the PDE sumpy declares for the
  kernel, as the wrangler reads it, and the wrangler's weights through the
  order are checked against it exactly; a wrangler whose weights do not
  follow it makes no claim for every order. The row rests on `harmonic`,
  through `@reconstructs(..., uses=harmonic)`. With Mathlib, Lean proves it,
  and the ledger reads `tested`, `decided (heuristic)` and `proved under
  harmonic`; without, it is `assumed under harmonic`. Running the file
  prints the recurrence and the PDE it comes from. Opaque functions with
  declared recurrences, for the Helmholtz kernels, #3's last primitive, are
  #82.
- `lanky.terms.free_names(term)` and `lanky.terms.sort_free_names(sort,
  own)`: every name a term or a sort mentions that nothing in it binds,
  wherever it stands, a family's type and a sort that is itself a name
  included. They are the walk the Lean printer declines a statement for,
  which was private to it, and the tester uses it too (#67, #74).
  `free_variables`, which a plugin sizes a kernel with, is unchanged.
- `lanky.testing.OpenStatement`, a `TypeError` that names the free names of
  a statement the tester refuses to sample, and
  `lanky.testing.statement_free_names(variables, hypotheses, goal)`, which
  finds them (#67). `lanky.testing.no_sampler(sort)` says why no value of a
  sort can be drawn at any size, and `SAMPLED_SORTS` are the sorts the
  tester draws (#74).
- `lanky.lean.ELABORATION_OPTIONS`: what every declaration the Lean oracle
  sends is elaborated under, `set_option autoImplicit false in` (#68).

### Changed

- **Packaged for the first release.** The version is 0.1.0, the classifiers
  say `Development Status :: 3 - Alpha` and `Framework :: Pytest`, and the
  project's URLs name the quickstart, this file and the issue tracker. The
  sdist holds the package, the tests, the examples and the documentation the
  tests compare with a real run, named in `pyproject.toml` rather than every
  file git does not ignore, and hatchling 1.27 or later builds it, for the
  license metadata. The publish workflow stops on a tag that is not the
  package's version in `pyproject.toml` and `lanky.__version__`, checks that
  it built one sdist and one wheel of that version, and runs `twine check`
  on them before it publishes. The README installs from PyPI with `pip`,
  extras, Lean and Mathlib included, says where the project stands, has a
  Known limits section, and links the quickstart, this file and the license
  by their full addresses, so that the links work on PyPI as well.
- **Mathlib mode no longer spends minutes on the sumpy demonstration** (#71).
  The CAS's row, 28 equations through order 6, is declined for Lean
  (`decline`), since Lean's row is the claim for every order, and the ladder
  has no strategy for a conjunction that size: `lanky check
  examples/sumpy_recurrence.py` took 491 s with Mathlib, and takes about a
  minute now, most of it importing Mathlib and asking whether the third
  row's hypotheses are inconsistent and its goal's domain empty. A budget
  for the whole ladder, which any statement no attempt fits still lacks, is
  #83.
- The optional `test with Lean and Mathlib` CI job installs sumpy, runs
  `tests/test_sumpy_recurrence.py` with `tests/test_mathlib.py`, and checks
  that the demonstration's claim for every order is `proved under
  harmonic`.

- **Lean proved two kinds of false statement, and does not now** (#61, #64).
  A wrong proof is the worst thing a proof host can report, so these lead.
  - *An existential's disjunctive condition is bracketed* (#61). The printer
    joins an existential's conditions, its domain's guards, a refinement's
    propositions and the generator's guard, to its body with `∧`, and
    printed each at the precedence of an arrow's antecedent, as a
    universal's are. `∨` binds more loosely than `∧`, so a condition that
    was a disjunction went unbracketed and Lean read another statement:
    `any(x == -1 for x in Fin[m] if (x > 5) | (x < 1))` was `∃ x : Int, 0 ≤
    x ∧ x < m ∧ x > 5 ∨ x < 1 ∧ x = -1`, which `x = -1` satisfies, and a
    script pinned with `use_tactic` proved it with `-1` as the witness,
    while the guard admits no point that is `-1` and the tester refutes the
    claim. A refinement of the domain and the guard of an existential with
    no binders were printed the same way, in both dialects. An existential's
    conditions are printed as conjuncts now, `(x > 5 ∨ x < 1)`, as a
    reduction's `with` clause already was; a universal's are joined with `→`,
    which binds more loosely than `∨`, and print as before.
  - *A statement with a free name is not handed to Lean* (#64). A name
    nothing in a statement binds was printed as it stands, and Lean read it
    as whatever it or Mathlib declares under that name, or, where there is
    none, bound it implicitly at a type it inferred. `round(0.5) == 1` was
    `round (1 / 2 : ℝ) = 1` in Mathlib mode, proved about Mathlib's `round`,
    which rounds half up, where Python's rounds half to even and gives `0`;
    and `def free_goal() -> x - 1 >= 0`, with `x` bound nowhere, was
    `theorem Lanky.free_goal : x - 1 ≥ 0`, about a natural `x`, which
    `omega` proved in core Lean. `lanky.lean.statement_of`, which arranges
    what the oracle proves, declines a term with a free name now, naming
    it: in a body, a guard or a binder's domain, in a family's type, and a
    plain pymbolic `Variable` that a term built by hand holds. `print_lean`,
    which shows a term, still prints an open one as it stands. Such a
    statement reads `assumed`, and the tester's `DECLINED` line names the
    name (#67, below); and Lean elaborates every declaration with
    `autoImplicit` off, so that it would refuse a free name the printer let
    through (#68, below).
  - *A dict or a set lookup keyed by a term is refused in an annotation*
    (#73). A dict or a set finds a key by its hash before it compares
    anything, and a term's hash is its structure's, so a term used as a key
    matched no concrete key and the lookup answered as if it were absent,
    without asking the term for a truth value lanky could refuse:
    `{0: 1}.get(i, 0)` was `0` while the annotation was read, and `all(f(i)
    * 0 == {0: 1}.get(i, 0) for i in Fin[n])` became `f(i)*0 == 0`, which
    Lean proved with `omega`, in core and in Mathlib mode, and which is
    false at `i = 0`. `i in {0, 1}` was `False` the same way, and `{0:
    1}[i]` raised `KeyError`. While an annotation is evaluated, a term's
    hash is refused with `TypeError` when it is asked for by the
    annotation's own code, as a dict or a set lookup or display there asks
    for it (a builtin such as `dict.get` has no frame of its own), and the
    message names the fix: a family for a table indexed by a term, and
    comparisons joined with `|` for a membership test. lanky's and
    pymbolic's own hashing runs in their frames and is unaffected. A builtin
    the annotation calls by name runs in lanky's `BuiltinName`, whose frame
    stands in for the annotation's, so `set(i for k in range(1))`, `dict((i,
    1) for k in range(1))` and a key function handed to `max` or `sorted`
    that looks `i` up are refused too. Which annotation is being read is a
    context's own, so two threads reading annotations at once do not unmark
    each other's. This is the frame-based reading the `if` clause check uses
    (#63). A function the annotation calls is not the annotation's code, and
    a lookup there is not refused (#80).
  - *A term made into text, or read as a number's truth value, is refused in
    an annotation* (#73). A term's text is what it is written as, and its
    truth value as a number was pymbolic's, each the same at every value the
    term takes, and neither asked lanky anything: `{"0": 1}.get(f"{i}", 0)`
    was `0`, `len(f"{i}")` was `1`, `1 if i else 0` was `1`, `i and True`
    was `True` and `(i - i) or 5` was `i - i`, and Lean proved the
    statements built on them, false at `i = 0`, or at `i = 10` for the
    length. An f-string, `str.format` or a `%` format of a term, and Python's
    `and`, `or` and `not`, a conditional expression or an `if` clause on a
    term that is a number, are refused in the frames a hash is, naming the
    fix: compare the term, as in `i != 0`. `str(i)` and `repr(i)` were
    refused already, as builtins applied to a term, and so was a
    proposition's truth value anywhere but an `if` clause. Python's `is` and
    a term's attributes still answer about the term and not its value
    (#88).
  - *Every declaration is elaborated with `autoImplicit` off* (#68). Lean
    binds a name a declaration's signature does not know as an implicit
    argument, at a type it infers, which is how `theorem Lanky.free_goal :
    x - 1 ≥ 0` became a statement about a natural `x` (#64). Every
    declaration the oracle sends, and every side condition of a complex
    logarithm or square root, is preceded by `set_option autoImplicit false
    in` now (`lanky.lean.ELABORATION_OPTIONS`), so that a name the printer
    let through would be an unknown identifier to Lean rather than a
    variable. The printer still declines such a statement first, so no
    status changes, but every `lean_source` a proof records has the line
    before each declaration, after `import Mathlib` in Mathlib mode.
- **The tester declines a statement with a free name, and `lanky check`
  says which** (#67). A name nothing in a statement binds, a misspelt
  parameter, has no value at a draw. `n + m >= n` raised at the first draw,
  and the fact read `assumed` with the reason in its provenance alone, where
  `lanky check` does not print it, while Lean declined it without a word.
  `(n >= 0) | (m > 0)`, which never asks for `m`, read `tested`.
  `lanky.testing.check` refuses such a statement before it draws anything
  now, raising `OpenStatement` with the names, and the property-test oracle
  records that as `declined`, so `lanky check` prints a `DECLINED` line:
  `property-test: the statement mentions m, which no parameter or binder of
  it binds, ...`. The names are the ones the Lean printer declines a
  statement for, read from its sorts too, so a misspelt sort is one, and
  from inside a list, a nested tuple or a dict an argument is written as,
  which the walk used to stop at (#87); a variable binds its name in every
  sort, whatever order the parameters are written in. `Theorem.report` and
  `Theorem.test` raise, and the pytest plugin fails such a theorem, naming
  the names. A plugin's fact that mentions names on purpose, such as an
  array a kernel reads, is declined by the tester the same way, and gets
  the line where no other oracle takes it.
- **A family whose values the tester cannot draw is not passed on its empty
  draws** (#74). `f: Fn[Fin[n], Flaot]`, with a misspelt sort, or `f:
  Fn[Fin[n], Fn[Nat, Nat]]`, whose values are families over `Nat` and
  cannot be tabulated, could be drawn only where `n` is `0`, as the empty
  table, where `all(f(i) >= 0 for i in Fin[n])` holds; every other draw
  was unsampleable, and the claim read `tested` on the draws at `n = 0`
  alone. A misspelt sort is a free name now (above). A family whose values
  have no sampler is refused at every size, its empty domain included
  (`lanky.testing.no_sampler`), so no draw is completed and the fact stays
  `assumed`, with `no draw could be completed: cannot draw the values of
  ...` in its provenance.
- **A `Fraction` is an operand, as an `int` or a `float` is** (#76).
  pymbolic's operators take no `Fraction`, so Python fell back on the
  `Fraction`'s own: `x ** Fraction(1, 3)` became `x ** 0.3333333333333333`,
  a float every oracle reads as the rational it holds and not as a cube
  root, so the tester refuted `(x ** Fraction(1, 3)) ** 3 == x` at `x = 2`;
  and `Fraction(1, 3) * x` raised `TypeError`. A term's arithmetic operators
  build the node for a `Fraction` operand themselves now, on either side,
  as pymbolic builds it for a number. For `Fraction(1, 3) ** x` Python asks
  the `Fraction` first, and before CPython 3.12.5 its `__pow__` turned
  itself into a float for an exponent it did not know (CPython gh-119189),
  so the term was handed `0.3333333333333333`; the base is taken back from
  the `__pow__` that made the float, and is the `Fraction` on every
  version.
- **A negation renders as a unary minus** (#69). `render(-x)` was `-1*x`,
  since pymbolic builds a negation as a product whose first factor is `-1`,
  and only a summand was read back as a subtraction: the ledger showed
  `-1*x == -1*x` for `-x == -x`. A negation is a unary minus wherever it
  stands now, `-x`, `-x*y` and `(-x)**2`, at the precedence Python gives
  one. Five more places where the text read as another number than the
  term are bracketed: a negated floor division as the first summand,
  `-(n // 2) + 1`, which printed as `-n // 2 + 1`, Python's `(-n) // 2 +
  1`; a factor after the first that is a product or a division itself,
  `a*(b // c)`; a negative literal as a base, `(-2)**n`; a power as a base,
  `(x**y)**2`; and a `Fraction`, which prints with a slash, as an exponent
  or a divisor, `x**(1/3)`. Only the text changes.
- **A builtin in an annotation is Python's, or refused** (#63). An annotation
  is evaluated in a `Scope`, which invents a variable for every name it does
  not have, and Python looks a name up there before it looks at the
  builtins, so every builtin but `all`, `any`, `sum` and `abs` was a
  variable: `min(x, y)` and `complex(x, 1)` applied a free name, as a family
  is applied, and read `assumed` with nothing to say why, or `proved` about
  Lean's own `min` (#64). A builtin's name is a
  `lanky.terms.BuiltinName` now. Called at concrete arguments, it is the
  builtin, if it is one of `EVALUATED_BUILTINS`, those that compute a value
  from their arguments alone: `round(0.5) == 1` is Python's `0 == 1`, which
  the tester refutes, and `complex(-1, -0.0)` is the complex number with its
  negative zero, which an annotation could write only as `-(1 + 0j)`. Called
  with a term among its arguments it is refused where the annotation is
  evaluated, naming it (`min(x, y) applies Python's min to a symbolic
  value`), and so is a call of a builtin that is no part of a statement,
  `print`, `open` or `eval`; giving `min` and `max` a meaning as terms is
  #66. A builtin a statement calls runs with binder tracing suspended, so a
  symbolic domain it would iterate, `max(f(k) for k in Fin[n])`, and a
  proposition it would ask for a truth value are refused rather than read
  as a binder or a guard of the quantifier around it. A builtin that hands
  back an iterator, `zip`, `enumerate` or `reversed`, is run to the end
  where it is called, for the same reason: its iterator did its work later,
  while the generator around it was traced, so `zip(Fin[n], Fin[n])` bound
  two independent binders where Python pairs each point with itself, and
  `all(k == 0 for k, i in enumerate(Fin[n]))`, false wherever `n > 1`, was
  proved. Named and not called, a builtin is the free name it was, which a
  plugin can refuse, as loopty refuses a kernel's `a: float`; a theorem
  refuses a parameter or a goal annotated with one, `x: int`, which made
  `int` a hypothesis and `x` a free name that Lean bound as a natural, and
  the type itself, which the annotation is without `from __future__ import
  annotations`, naming the lanky sort meant (`Int` or `Nat`, `Real`,
  `Complex`, `Bool`). So it does a builtin named anywhere inside an
  annotation: `f: Fn[Fin[n], float]` made `float` the sort of the family's
  values, which the tester could not draw, and passed on the draws where the
  family is empty, so `all(f(i) >= 0 for i in Fin[n])` read `tested`.
- **Only a generator's `if` clause records a guard** (#63). Three more ways
  of asking for a truth value inside a quantifier were read as its `if`
  clause, and Lean proved what they made of the statement, which Python
  refutes. A conditional expression picks a branch by its condition, so
  `all((f(i) if i < 3 else -1) >= 0 for i in Fin[n])` became `f(i) >= 0` for
  `i < 3`, false in Python wherever `n > 3`. `not c` in a body became the
  guard `c` and the body `False`, so `~any(not (i < k) for ...)` held. And
  a comparison of two tuples or lists compares their items with `==` until
  two differ, so `all((i, 0) == (k, 0) for ...)` was `True` wherever `i ==
  k`, and so was `all(i == k for ... if (i, 0) <= (k, 0))`. The check used to
  read any layout it did not know as a guard; it now recognizes the `if`
  clause by what it does with a point it rejects, going back to the loop for
  the next one, and refuses everything else, naming the three. Two tuples
  compared with `==` in an `if` clause are still read, item by item, which
  is what their equality means.
- **A truth value a builtin asks for while a generator is traced is refused**
  (#63). The one place Python may ask for the truth value of a proposition
  is a generator's `if` clause, and lanky reads the frame that asked to tell
  it from a mistake. A builtin has no frame of its own, so `min(i, j)` with
  Python's own `min`, which a module that imports it, or code that builds a
  term without a `Scope`, still calls, asked for `j < i` from the generator's
  frame, and the answer was recorded as its guard: `all(min(i, j) == j for i
  in Fin[n] for j in Fin[n])`, false at `i = 0, j = 1`, became `j == j`
  wherever `j < i`, which Lean proves. And `if i in range(3)` asked for `i ==
  0` and stopped there. A truth value asked for by a call, by an `in` test or
  by the step of a loop over an iterator a builtin made is refused now, as
  one asked for by an `if` inside a function the annotation calls already
  was.
- **A fact id names its definition by the path of the file that defines it**
  (#22). The id is `kind:module.owner@line`, and `module` was the name the
  module was imported under. `lanky check helpers.py` imports the file under a
  name of its own, so a lemma was `theorem:lanky_checked_helpers.lemma@12` in
  its own ledger and `theorem:helpers.lemma@12` in the `rests_on` of a file
  that does `from helpers import lemma`; a relative import in a package gave a
  third name. The module is now `lanky.check.module_name` of the file the
  function's code was compiled from, for a theorem, an axiom and a rewrite,
  and `lanky.ledger.fact_id` documents it as what a plugin passes, so one
  definition has one id whether its file is checked directly or imported, and
  an `UNRESOLVED` line under a file's table names the id the other file's
  ledger holds. A function with no file behind it keeps its `__module__`.
  Every id a check of a file prints and writes with `--json` changes with
  it: `examples/nicomachus.py`'s `theorem:lanky_checked_nicomachus.gauss@33`
  is now `theorem:nicomachus.gauss@33`, and a file in a package is named by
  its dotted path, `theorem:pkg.helpers.lemma@12`.
  Ledgers are still one per file, and two files at the same place under
  different roots (`a/helpers.py`, `b/helpers.py`) share a module name, as a
  file of a namespace package (a directory with no `__init__.py`) shares its
  stem with a file of that name beside the package; their facts are told
  apart by `where` and the `path` in the provenance.
- **The property tester reads the reals exactly** (#33). It computed `Real`
  and `Complex` in floating point, so `exp(x + y) == exp(x) * exp(y)` and
  `(x + 0.1) - 0.1 == x` were refuted by rounding, and `lanky check` exited 1
  on claims Lean proves over `ℝ`; `exp(x - 1000) > 0` was refuted because the
  float underflows to `0.0`; and a proof of `x / y * y == x` got a
  `SEMANTICS` block whose counterexample was a rounding error. `Real` and
  `Complex` are now drawn as fractions (a `Complex` as the new
  `lanky.intervals.ComplexValue`, two fractions), whatever their exactness
  class, which still says how a kernel computes and no longer what a
  statement means. The tester evaluates in the new exact reading
  (`lanky.terms.exact_reading`): a float literal is the rational it holds,
  as the Lean printer reads it, `n / 2` and `2 ** -1` of integers are
  fractions, and `exp`, `log`, `sqrt` and the complex `exp` are exact where
  the value is rational (`exp(0)`, `log(1)`, `sqrt(9/4)`) and enclosed in a
  `lanky.intervals.Interval` where it is not: rational endpoints, rounded
  outward to 128 bits, summed from their series with every rounding bounded,
  and no dependency. A comparison is true where the enclosures prove it,
  false where they exclude it, which keeps a refutation as definite as a
  proof, and undecided where they straddle it. An equality between
  transcendental numbers is never proved that way, so one that stands
  `POSITIVE`, where the statement asserts it, holds when its sides agree to
  64 bits, which is evidence as a sampled universal's pass is; anywhere else
  it is undecided, as is an order whose enclosures overlap. One enclosure is
  one number and equal to itself, and one operation on the same numbers, the
  exponential of one argument or `2 * exp(x)` at one draw, is one enclosure,
  so a table the tester fills from a definition such as
  `f(i) == 2 * exp(x)` satisfies that definition when it is read back as a
  hypothesis, and `exp(x) - exp(x)` is `0`. A complex `log` or `sqrt`
  (until #51, below), an `exp` past `2**14`, a negative number to a power
  that is not an integer, and arithmetic with a float infinity or NaN are
  undecided rather than guessed; a comparison with an infinity or a NaN is
  Python's.
  `lanky.exp(0.5)` at a number, `evaluate` outside the exact reading and
  `Theorem.__call__` are Python's, as before. So the claims
  above are `tested`, `x + 1e-20 == x`, which every float draw passed, is
  refuted, and the claims in the Mathlib tests that were private because the
  tester refuted them are public and collected.
- **The tester encloses the complex logarithm and square root** (#51). Every
  draw of a statement that applied `log` or `sqrt` to a complex number was
  undecided, so `exp(log(z + 2)) == z + 2` over `abs(z) < 1` read `assumed`
  with `untested` in its provenance, and no oracle decided it. They are
  Python's principal branches now, as `cmath` computes them: `log z` is
  `log|z| + i atan2(im z, re z)`, with an arctangent series and `π` from
  Machin's formula enclosing the argument, and `sqrt z` is the principal
  root, exact where it is rational (`sqrt(-3 + 4i)` is `1 + 2i`). The
  arctangent is summed in units scaled to its argument, so the argument of a
  number just off the positive real axis, `1 + 2**-300 i` say, is enclosed as
  closely relative to its size as any other, and its sign is decided. On the
  branch cut, the non-positive real axis, `cmath` picks a side by the sign
  of a zero imaginary part, which a fraction does not have, so an argument
  on it, or an enclosure meeting it, is undecided, and the logarithm of a
  complex zero has no value, as in Python. That claim is `tested`, and
  `sqrt(z * z) == z` is refuted at a draw with a negative real part. The
  Lean printer declined both, since Lean's `ℂ` has no signed zero either,
  until #59, below.
- **Mathlib mode prints the complex logarithm and square root** (#59). Both
  were declined, so a statement that took either was decided by the tester
  alone. Mathlib's `Complex.log z` is `Real.log ‖z‖ + arg z * I`, with the
  argument in `(-π, π]`, and `Complex.sqrt z` is `z ^ (2⁻¹ : ℂ)`, the root of
  half the argument: off the branch cut, the non-positive real axis, these
  are `cmath`'s principal branches, which the tester encloses (#51). On the
  cut they part, since `cmath` picks a side by the sign of a zero imaginary
  part and Lean's `ℂ` has none: `log(x * complex(-1, -0.0)) ==
  log(x * complex(-1, 0.0))` is `log x - πi` against `log x + πi` in Python
  at every positive `x`, and a theorem `simp` proves in Lean. So the printer
  prints `Complex.log` and `Complex.sqrt`, and a statement that takes one
  carries side conditions (`LeanStatement.side_conditions`): for each
  argument `a`, that it is off the cut, `0 < Complex.re a ∨ Complex.im a ≠
  0` for a logarithm, which leaves out zero, where `cmath.log` raises and
  Lean's logarithm is `0`, and `0 ≤ Complex.re a ∨ Complex.im a ≠ 0` for a
  square root, which is `0` at `0` in both readings. A side condition
  quantifies over the binders around the argument, under the guards Python
  has evaluated by the time it reaches it: the hypotheses, a refinement, and
  the `if` of a generator around it. The Lean oracle proves the side
  conditions before it tries the statement, with `norm_num` and the
  arithmetic tactics on the hypotheses, and declines the statement, saying
  which one it could not prove, when it cannot; so what Lean proves never
  reaches the cut, where the two readings are one. The example above is
  declined, and so is `exp(log(z)) == z` for a nonzero `z`, which holds on
  both sides of the cut but has nothing to keep `z` off it. A literal
  argument on the cut, or a complex zero under a logarithm, which only a
  term built by hand holds (`lanky.log` of a number is Python's value), is
  declined where it is printed, and a complex logarithm or square root in a
  binder's domain outright. A proof's `lean_source` proves the side conditions first, under
  `Lanky.<name>_branch_cut_<i>`, and then the statement. The ladder's `simp`
  lemmas gain `Complex.exp_log` and `Complex.sqrt`, and a statement with side
  conditions gets two more attempts, a `simp` with `Complex.ext_iff` and the
  same `simp` with a discharger that shows `Complex.exp_log`'s argument
  nonzero from the hypotheses with the arithmetic tactics, so
  `exp(log(x + 1j)) == x + 1j`, `exp(log(x + y * 1j)) == x + y * 1j` under
  `y > 0`, and `sqrt(x + y * 1j) ** 2 == x + y * 1j` under `y != 0` read
  `proved lean`. A complex argument no longer gets the
  `semantics` note of the real logarithm and square root, whose gap its side
  conditions close.
- **`lanky check` says why an oracle declined a fact** (#37). An oracle that
  takes a fact and finds it outside what it decides returns it unchanged,
  and can say why; the pytential demonstration's rule engine did, in its
  provenance as `declined`, and the row read `assumed` with nothing under
  the table, as for a claim no oracle knows. `declined` is a standard
  provenance key now, read the same way whatever the plugin, and a fact
  left `assumed` that has one gets a `DECLINED <owner> at <where>:
  <statement>` line under the table with the reason indented under it,
  after the `CITED` lines. A list holds one reason per oracle, and
  `check_path` keeps the reason of each oracle that declined a fact, in the
  order they were asked, where each one's would otherwise take the place of
  the one before. A fact a weaker oracle
  went on to settle, and an axiom, get none, and the exit code does not
  change. The Lean oracle records the standard key beside `lean_declined`
  when it is asked directly about a statement it cannot print.
- **A Lean theorem is declared as `Lanky.<name>` in core mode too** (#39,
  #43). Core Lean declares `and_comm`, `trivial`, `id`, `absurd`, `congr`
  and more at the root, so a claim named like one was refused as already
  declared at every attempt and read `tested`; so was `inferInstanceAs`, a
  keyword that is also a declaration, and `True_`, which cleaning turns into
  `True`. Mathlib mode already declared its statements in the `Lanky`
  namespace. The `lean_source` of every core proof changes with it:
  `theorem commutes ...` is `theorem Lanky.commutes ...`.
- **A variable named like a root name the printer writes** (#43). After a
  binder `(Int : Int)`, `Int` is the variable, so `def f(Int: Nat, b: Nat)`
  printed `(b : Int)` with the variable as a type and was refused with "type
  expected", and `Int.fdiv` was read as a field of it. In a statement with a
  variable named `Int`, `Nat`, `Bool`, `Real`, `Complex`, `Finset`, `True` or
  `False`, and only there, those names are printed from the root,
  `_root_.Int`, in the statement and in the tactic scripts: the casts, the
  floor division, the literals, `Complex.I`, `Real.exp`, `Finset.Ico`, and the
  lemmas the induction and Mathlib's attempts name. Every other statement
  prints as before.
- **A variable named `rfl` or `_` is introduced under a fresh name** (#43).
  `intro rfl` and an `rcases` pattern `⟨b, rfl⟩` read `rfl` as a
  substitution, so the induction strategy failed on a goal variable named
  `rfl` with "subst failed", and an `rcases` pattern reads `_` as a hole. The
  strategy introduces such a variable as `x` (or the next fresh name), and
  so does the Mathlib reduction induction for a parameter.
- **A Lean REPL ends with the process that started it, however it ends**
  (#46). lean-interact starts the REPL in a session of its own, and an
  attempt's timeout is kept by the lanky process, so a process ended by a
  signal, which runs nothing on the way out, left its REPL going on with its
  attempt: `lanky check` of one root, or a program calling `check_path` or
  the oracle, ended by `kill`, and a child of `lanky check` sent `SIGKILL`
  directly. Each lanky process now starts a small reaper with its first
  REPL, a Python process in a session of its own that reads a pipe from it,
  and when the pipe closes, which the kernel does however the process ended,
  kills every REPL process group it was handed. A session that closes takes
  its REPL back first. A forked process lets go of its parent's end of the
  pipe, which it inherits and which kept the parent's REPLs going for as
  long as the fork ran, and starts a reaper of its own. And Ctrl-C during
  an attempt stops the REPL where the command is interrupted: lean-interact
  reads the answer in a thread the interpreter waits for on its way out,
  before anything registered at exit runs, so an interrupted `lanky check`
  used to wait until the attempt finished. POSIX only; on Windows nothing
  changes.

- **The quantifiers are three-valued** (#29). A quantifier evaluated its body
  point by point and gave up at the first point it had no answer at, an
  undecided operand or a division by zero, though a later point settles it:
  `all(~all(k < 100 for k in Nat) & (i < 1) for i in Fin[n + 2])` read
  `assumed`, and the same claim spelled out at `i = 0` and `i = 1` was
  refuted, since #25 made the connectives three-valued. A universal is now
  read as the conjunction of its points and an existential as their
  disjunction, as `lanky.terms.conjoin` and `disjoin` read operands: a point
  with no answer is passed over, a later point where the body fails refutes
  the universal (and one where it holds witnesses the existential), and when
  nothing settles the quantifier the first open answer is raised again. A
  point whose guard or refinement has no answer is yielded by
  `LankyEvaluationMapper.guarded_assignments` as the new
  `lanky.terms.OpenPoint` rather than ending the walk; a universal's such
  point is settled when the body holds there, an existential's when it fails
  there, and it is open otherwise. So is a binder whose domain cannot be
  enumerated (`j in Fin[10 // i]` at `i = 0`), which stands for its points
  as a whole and has no body to read. The evaluator, the tester's walk of a
  universal goal and the hypotheses read the points this way, so the claim
  above is refuted at `i = 1` with Lean and without. A sampled walk keeps its
  rules: a universal's pass is undecided where it does not stand `POSITIVE`,
  a walk that reached no point is undecided, and a point whose guard has no
  answer is not one it reached. A sum is unchanged: a point it cannot place
  leaves it with no value. A point after one with no answer is evaluated
  now, so a body that is not a proposition there is refused where the
  earlier point used to hide it, as #25 has it for an operand.
- **A parameterless theorem's goal is read as its goal** (#35). With no
  parameters and no hypotheses, `Theorem.term` was the goal itself, and every
  reader of a term takes a `Forall` apart into variables, hypotheses and
  goal: `def closed() -> all(k >= 0 for k in Nat if k > 100)` had `k` read as
  the statement's variable and its guard as the statement's hypotheses, so
  `lanky check` warned "hypotheses never satisfied in 4000 draws" about a
  theorem with none, and with Lean a flipped guard was vacuous because "the
  hypotheses are inconsistent", while `pytest`, which hands the oracle the
  goal as a goal, said that no draw could decide the statement. The goal's
  guard was examined one level down as well, at a universal inside the goal,
  against the rule that only the goal's outermost quantifier is. The term is
  now a `Forall` with no binders and no guard around the goal, so every
  reader sees the goal as the goal: such a theorem reads `assumed` with the
  reason `pytest` gives, a flipped guard is vacuous because "the goal's guard
  is empty wherever the hypotheses hold", and only the goal's outermost
  quantifier is examined. The empty binders print as nothing, in the ledger
  and in Lean, where the theorem is stated with no parameters and a
  quantified goal. A closed statement whose goal Python already answered,
  `-> 1 == 2`, keeps the `bool` for its term.
- **Two claims with one fact id fail the check** (#52). An id names a
  definition by its module, qualified name and line, so a function that
  decorates a nested definition each time it is called gives every claim it
  makes one id, and `check_path` added each to the ledger with `Ledger.add`,
  which replaces a fact of the same id: the ledger kept the last claim and
  dropped the others without a word, a refuted one included, and `lanky
  check` exited 0 on a factory whose first claim, `n + 1 == n`, is false.
  `check_path` now checks the first claim of an id and keeps it, records
  each later one on it, by its statement, as `duplicate_claims` in its
  provenance, and does not check it. The new `Ledger.duplicated()` returns
  the facts so marked, and `lanky check` prints a `DUPLICATE` block for each
  definition under the table, naming it and, for each of its ids, the claim
  that was checked and those that were not (a loopty kernel owns a fact per
  obligation, and gets one block for all of them), and exits 1, whatever the
  claims say:
  each claim needs an id of its own, a definition of its own or a
  `__qualname__` of its own given to the function before it is decorated.
  `Ledger.add` still replaces, which is how an oracle upgrades a fact. A
  plugin's facts are collected the same way, so two loopty kernels one
  factory makes are refused too. An object registered twice is one object,
  and its claims are collected once.
- **A pass on thin evidence says so** (#55). The tester drops a draw the
  statement cannot be answered at and draws another, until it has enough
  valid ones, so a pass counts only what it could decide, and that can be a
  few points: `exp(x) * exp(-x) <= 1` is decided only at `x = 0`, where the
  value is rational, and read `tested` on 200 valid draws, all at `x = 0`,
  out of some 3100, with nothing but the `undecided` count in the JSON to
  say so. A pass now gets a `reason` when the draws that decided nothing
  outnumber the valid ones, or when the valid draws take fewer distinct
  assignments than `lanky.testing.DISTINCT_FLOOR` (three) while the draws
  that reached the statement took more, so that a domain with one or two
  assignments, a `Bool` or a hypothesis `n == 0`, is not thin for having
  few. The new `lanky.testing.thin_pass_reason` builds it, as
  `goal_unreached_reason` builds the line for a goal whose guard no draw
  passed; it says how many draws decided nothing, names the valid
  assignments when there are at most three, and gives the reason one
  undecided draw had on a line of its own. It covers every way a draw is
  dropped, a comparison the enclosures cannot settle, a division by zero, an
  undecided quantifier. The status stays `tested`; the property-test oracle
  records the reason in the provenance, and `lanky check` prints it under
  the table as a `WARNING`, with exit code 0. A fact a stronger oracle
  established gets no such reason from its cross-check, since the pass is
  not what it rests on.
- **A comparison of an `^`, a `<<` or a `>>` is a proposition.** The three
  built pymbolic's own nodes, which no lanky operator re-tagged, so `==` of
  one compared it structurally and answered `False`, and `<` raised a
  `TypeError`: loopty traced a kernel's `when((k ^ 1) == 0)` as a guard that
  never holds, and `(k << 1) != 4` as one that always does. They are lanky's
  `BitwiseXor`, `LeftShift` and `RightShift` now, re-tagged as the other
  arithmetic is, and their comparisons build `Comparison`. `&`, `|` and `~`
  stay the logical connectives.

### Notes

- Over `Real` and `Complex` the tester and Mathlib read one statement, over
  `ℝ` and `ℂ` (#33), but the tester's enclosures decide less than a proof: an
  equality of transcendental numbers holds on evidence where it is asserted,
  and is undecided under a negation or in a hypothesis, and an order whose
  enclosures overlap is undecided. Such a draw is not noted as a gap, since
  both readings have an answer there.
- The pytest-plugin tests pass where lanky is importable and not installed,
  `PYTHONPATH=src python -m pytest`, as well as under `uv run pytest` (#40):
  they relied on pytest loading the plugin through its `pytest11` entry
  point, which only an installed distribution registers, and now name it
  with `-p lanky.pytest_plugin` where the entry point is missing or
  entry-point plugins are off. Each runs both ways.
- The two child-process tests that failed now and then under load (#53)
  asked whether a process had ended twice, in a wait loop and then in the
  assertion after it, and read `/proc` in between. A process that ends is a
  zombie until it is reaped, and while it is reaped `kill(pid, 0)` still
  finds it and its `/proc` entry is already gone, which the watcher read as
  a process still running: the loop saw the zombie and stopped, and the
  assertion read it as alive. They watch a process with
  `tests/conftest.ProcessWatch` now, which reads an unreadable entry as a
  process that has gone and answers once, and which also reads a pid another
  process has taken since, by its start time, as a process that has ended.
  Their deadlines are a minute, which a passing run never waits for. The
  code under test does not change.
- The suite runs with the CAS oracle off unless a test asks for it, as it
  runs without Mathlib: `tests/conftest.py` sets `LANKY_CAS_DISABLE`, and the
  `cas` fixture takes it out and skips where sympy is not installed. With
  the oracle on, thirteen tests read `decided (heuristic)` where they pin
  `tested` on an identity such as `n + 0 == n`, and nothing else changes,
  the documented ledgers included. CI's `test with Lean` job installs the
  `cas` extra, so the oracle's tests run there, and sumpy from PyPI, so the
  sumpy demonstration's do (#75); the main job installs no extra, as before.

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
    `sum(1 for i in Fin[n]) - 3` truncate. A body, and the operand of `|x|`,
    that is arithmetic on numerals alone, which only a term built node by node
    holds, is ascribed `ℤ` the same way, as a comparison with no variable in it
    is: `|1 - 2| = 0` and a sum of `1 - 2` equal to `0` were proved over `Nat`.
    It declines a sum over `Nat`, a
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
- **Rewrites** (`lanky.rewrites`). A transformation some tool made, stated
  as a claim: a source, a target, and the obligation between them that an
  oracle discharges (#2). `@rewrite` decorates a function of no arguments that
  returns `(source, target)`, runs it once where it is decorated, and
  registers a `Rewrite`; `obligation=` names what has to hold (`"equal"` by
  default) and `uses=` works as it does for `@theorem`. The fact has kind
  `rewrite`, id `rewrite:<module>.<qualname>@<line>`, a `RewriteTerm` (source,
  target, obligation, compared by identity, since a side may be a lanky term)
  as its term, and the statement `source ~> target (obligation)`. No built-in
  oracle takes a `RewriteTerm`, so a rewrite stays `assumed` until an oracle
  that knows its obligation decides it. `rewrite_fact` builds the same fact
  for a plugin that makes its facts itself, as loopty's schedule steps do,
  and a subclass of `Rewrite` claims more about its target by overriding
  `facts`. A function that takes arguments or returns anything but a pair,
  an obligation that is not a name, and `@rewrite("equal")` are refused where
  they are written. The theory, named `rewrite`, is built in beside
  `theorem`; `lanky.Rewrite`, `lanky.RewriteTerm` and `lanky.rewrite` are
  exported.
- **The `heuristic` trust class** (`lanky.plugins.TRUST_STRENGTH`). Between
  `test` and `decision-procedure`, for a decider that may fail to answer
  inside its own fragment, or whose answers are not guaranteed: a
  computer-algebra simplifier, a rule set with gaps (#2). A rule engine
  complete for the fragment it accepts, answering every claim in it and
  declining everything else, is a decision procedure for that fragment and
  says so. A heuristic is asked after a decision procedure and before the
  property tester (an oracle naming the class used to rank below the tester,
  as an unknown class still does), and a fact it settles reads
  `decided (heuristic)` in the table (`Fact.is_heuristic`). Its answer is not
  guaranteed and a counterexample is, so a fact a heuristic established is
  sampled all the same, once, with or without hypotheses, and a
  counterexample overrules it: the fact is `refuted` by the tester, with
  `overruled` in its provenance naming the heuristic. What rests on a fact a
  heuristic settled is worth a heuristic's answer: of two facts with one
  status the heuristic's is the weaker, `Support.heuristic` says so, the
  `EFFECTIVE` column prints `decided (heuristic)`, and `--json` carries
  `effective_heuristic` for every fact. For the same reason a heuristic is
  not asked whether a fact's hypotheses are inconsistent: a vacuous fact
  fails the check, and where no draw satisfies the hypotheses there is no
  sample to overrule a wrong answer.
- **Example.** `examples/gauss.py`, two worked theorems, runnable three ways,
  and `examples/nicomachus.py`: Nicomachus's theorem as an axiom, and the
  closed form of the sum of cubes, tested under it. `examples/pytential_skie.py`
  (#2) asks of five integral representations, Laplace Dirichlet with the
  double and the single layer, Laplace Neumann with the single layer, and
  Helmholtz with the combined field for Dirichlet and for Neumann data,
  whether each gives a boundary equation of the second kind on a closed
  boundary of class C². Each is a rewrite from the representation's trace to
  its boundary operator under the obligation `jump relations`, a verdict
  about that operator, and for a second-kind claim the arithmetic that the
  identity coefficient is not zero, which Lean proves as integer arithmetic
  on the numerator. The verdicts are decided by a rule engine in
  `examples/layer_potentials.py` whose rules are eight `@axiom`s, the four
  jump relations and the three compactness statements from Kress's *Linear
  Integral Equations* and Colton and Kress, and the hypersingularity of `D'`,
  read off the axioms' statements; it claims `decision-procedure` for the
  fragment it accepts and declines the rest with the reason. The single
  layer is refused as first kind (no identity term), and the Neumann data
  as not second kind because `D'` is no multiple of the identity plus a
  compact operator. `python` prints the table and the reasons; `lanky check`
  exits 0 with every verdict `decided` by `layer-rules` under the axioms it
  applied. Where pytential imports, the demonstration also translates the
  five built with `pytential.sym`, and two of pytential's own
  `DirichletOperator` pairs, through `layer_potentials.from_pytential`;
  pytential is never a lanky dependency and `import lanky` does not import
  it.
- **Sums of index types** (`lanky.prelude.SumType`). `Fin[n] + Fin[m]` is
  the disjoint union of the two, a point of which is a point of one piece
  together with the position of that piece. The pieces keep their order, and
  a sum of sums is flat. A piece may be an index type a plugin defines, which
  builds the sum with `SumType.of` from its own `__add__` and `__radd__`, as
  loopty's polyhedral domains do for its array arguments over a union of
  pieces (loopty #12). lanky only carries a sum: it is not a binder domain,
  and iterating one says so.
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
- **A goal whose own guard never holds is vacuous, and the ledger says so.**
  A scan postcondition with its guard flipped,
  `all(off(p) <= off(q) for p in Fin[n + 1] for q in Fin[n + 1] if (p < q) & (p > q))`,
  holds at every draw because its guard holds at no point, and the row read
  `tested`, or `proved lean`, since `omega` proves it from the guard, with
  nothing under the table (#17). #5 looked at the theorem's hypotheses and not
  at the guard of a quantifier inside the goal. The property tester now
  counts, per draw the hypotheses admit, whether the goal's quantifier got
  through to a point of its guarded domain (`TestReport.goal_reached`), and a
  goal that never did records `goal_reached: 0`; under `pytest` such a theorem
  is skipped, with the guard in the reason. A fact whose goal is a universal
  is cross-checked by the tester when a stronger oracle established it, as a
  fact with hypotheses already was. When no draw got through, the stronger
  oracles are asked whether the guard is empty for every assignment the
  hypotheses admit (`lanky.check.goal_guard_fact`, the goal with its body
  replaced by `False`). If one proves it, the fact is marked `vacuous`, with
  `vacuous_by` and `vacuous_evidence`, exactly as #5 marks inconsistent
  hypotheses: the row reads `proved (vacuous)`, a `VACUOUS` block follows the
  table, and `lanky check` exits 1. If none can, and some draws were valid,
  the provenance records `goal_unreached` ("the goal's guard p < q and p > q
  never held in 200 valid draws") and a `WARNING` line follows the table, with
  exit code 0. A guard that is empty only for some values of the variables,
  as `Fin[n]` is at `n = 0`, gets through at some draw and is never flagged. A
  goal with no guard whose domain never has a point, such as `Fin[n - n]`, is
  the same case. An axiom's goal guard is examined as a theorem's is, and the
  stronger oracles are asked about the guard, never about the axiom. Only the
  goal's outermost quantifier is examined.
- **A symbolic guard over a concrete domain is refused rather than dropped.**
  `sum(1 for i in Fin[3] if n > 100) == 0` became `False` while the annotation
  was evaluated, and was refuted at `n = 3`, where it is true, with Lean and
  without (#24). Over a concrete domain the generator binds no binder and the
  builtin answers over the values it yielded, and capturing the guard answers
  `True`, so every point was yielded and the guard was lost; `all` and `any`
  lost it the same way whenever the body was concrete, so
  `any(i >= 0 for i in Fin[3] if n > 100)` read `tested`. `lanky.terms.forall`,
  `exists` and `sum_` now raise `SymbolicBoolError` when the trace bound no
  binder and recorded a guard, naming the guard and the ways to keep the
  condition: outside the quantifier, as in `~(condition) | all(body for ...)`,
  when it does not mention the loop variable, or over a domain with a symbolic
  bound, where the quantifier is a term that keeps its guard. The file does not
  import, and `lanky check` prints the traceback and exits 1. A concrete guard
  over a concrete domain is Python's, as before.
- **The connectives are three-valued.** A connective stopped at the first
  operand the tester could not decide, so `~all(k < 100 for k in Nat) | (n >= 0)`
  read `assumed` and the same disjunction with its operands swapped read
  `tested` (#25). The new `lanky.terms.conjoin` and `disjoin` read their
  operands as Kleene's strong connectives: a false operand settles a
  conjunction and a true one a disjunction, whatever an operand before it
  could not answer, and when nothing settles it the first open answer is
  raised again. An open answer is `Undecided`, or a `ZeroDivisionError`,
  which is Python's side of Lean's total division. The evaluator's `&` and
  `|`, the tester's walk of a conjunction in the goal, the list of hypotheses
  and the propositions of a refinement all read their operands this way, so
  the order they are written in no longer changes what a draw decides: both
  disjunctions read `tested`, a conjunction whose first conjunct is undecided
  and whose second is false is refuted, and a draw one hypothesis breaks is
  rejected however the others come out. A false operand still stops the walk,
  so `(k > 0) & (10 // k > 1)` never divides by zero. An operand after an
  undecided one is evaluated now, and one that is not a proposition is refused
  where the undecided operand used to hide it.
- **A refinement is read as the hypothesis it is.** `n: Nat & all(k < n + 100
  for k in Nat)` stopped the property test: `Refined.holds` evaluated the
  refinement with no sampler, the quantifier over `Nat` raised `ValueError`,
  and the row read `assumed` with "property-test could not run" (#26).
  `Refined.holds` takes a sampler and reads its propositions standing
  `NEGATIVE`, and the tester hands it one made from the draw's random source
  and the values drawn so far, for a parameter's refinement, a family's
  codomain, and a refinement of the binder domain of a definitional
  hypothesis. A draw of `k` that breaks the universal rejects the value, and
  one at which it held at every draw leaves the draw undecided, so `refined`
  reads `assumed` with a reason that names the refinement; an existential a
  draw witnesses admits the value.
- **Files from different source roots are checked in processes of their
  own.** `lanky check a/claims.py b/claims.py` checked the files one after
  another in one process, so when each directory held its own `helpers.py`,
  the second file's `import helpers` found the first directory's module in
  `sys.modules`, and its claims were decided against code it does not
  contain, without a word (#9). Two trees' packages of one name were refused
  with an `ImportError` instead, which failed the check on a file that is
  fine. The command now groups the files by their source roots, the
  directories a check puts on `sys.path` (the file's own, and for a file in a
  package the one its package is found from), which the new
  `lanky.check.source_roots` returns. Files that share their roots, a single
  file always among them, are checked in the command's own process one after
  another, and print what they always printed. When the roots differ, each
  group is checked in a child process of its own, one after another, started
  with the same interpreter, `sys.path`, `sys.argv`, working directory and
  environment, and what a child prints is copied line by line to the
  command's standard output and error. The ledgers come out root by root, in
  the order each root first appears on the command line, and `--json` lists
  the facts in that order. A child that ends before it reports, because a
  checked file called `sys.exit` while it was imported or because it could
  not be started, is named in a line and fails the check, and the other roots
  are still checked. A child finds its plugins through their entry points, as
  the `lanky` command does. `check_path` keeps its behavior, which its
  docstring now states: it imports into the process that calls it, and still
  refuses a package of one name imported from another directory.
- **`lanky check` names each axiom's citation.** An axiom's `cite` was in
  the JSON alone, though it is the one thing that stands behind an
  `assumed (axiom)` row (#2). Each axiom now gets a `CITED` line right under
  the table, `CITED nicomachus at nicomachus.py:38: Nicomachus of Gerasa,
  Introduction to Arithmetic`, one per axiom in the table's order, a refuted
  one included; a citation of several lines is indented under its first. The
  exit code does not change, and the quickstart's table for
  `examples/nicomachus.py` has the line.
- **The oracle that settles a fact leaves its trust class.** A status says
  what kind of evidence a fact has; how far its decider is to be trusted was
  nowhere in the ledger. `lanky.check.establish` now records the trust class
  of the oracle that established or refuted a fact as `trust_class` in its
  provenance, which is what the table's `decided (heuristic)` mark reads.
- **A comparison with no variable in it is integer arithmetic in Lean.** The
  printer wrote a closed comparison, which only a term built node by node can
  hold, with bare numerals, and Lean read those as `Nat`: `1 - 2 >= 0` was a
  truncated subtraction Lean proved and Python refuted, and `-1 != 0` did not
  elaborate. Its left side is now ascribed, `(1 - 2 : Int) ≥ 0`, as a literal
  base of a power already was, and so is a base of a power with no variable
  in it: `(1 - 2) ** n >= 0` printed as `(1 - 2) ^ n.toNat ≥ 0`, which Lean
  read over `Nat` and proved. The demonstration's coefficient facts are such
  comparisons.
- **A Lean attempt that times out costs that attempt alone.** In core-Lean
  mode lean-interact kills the REPL when a command runs past
  `LANKY_LEAN_TIMEOUT` and does not start it again, and the session kept the
  dead server: every later attempt, on that fact and on every fact after it
  in the same `lanky check`, came back as "The Lean server is not running",
  while the session recorded no error and `availability()` still said the
  oracle was available (#32). A core session now starts the server again
  before the next command, as a Mathlib session already did, importing
  Mathlib again; a server that will not start again is the session's error
  from then on. The test that a timeout is not a refutation gives its oracle a
  session of its own, since the timeout that applies is the session's: handed
  the module's session, the oracle never timed out.
- **A name Lean would read as something else is printed so that it reads it
  as written.** A theorem or a variable whose Python name is a Lean keyword
  (`scoped`, `fun`, `at`, `show`, `end`, and with Mathlib `lemma`, `to` and
  `over`) was printed as it stands, Lean could not parse the statement, and
  the fact fell through to the tester with the parse error as its
  `lean_reason` (#38). Such a name is now quoted, `«fun»`, wherever it is
  printed: the theorem's name, the parameters and propositions, a bound
  variable, an exponent's `.toNat`, a reduction's binder, and the ladder's
  `intro`, `obtain` and `induction`; so is a name with a letter outside
  ASCII. The new `lanky.lean.lean_identifier` does it, from the words the
  parser table of Lean v4.29.1 reserves with `import Lean` and with the
  pinned Mathlib, and the Lean tests compare that list with the table of the
  Lean they run against. The hypotheses are named `h0`, `h1`, ... as before,
  unless a variable of the statement has the name, and then with a suffix,
  `h0_1`: `def named(h0: Nat, b: Nat) -> h0 + b == b + h0` shadowed its
  variable with the hypothesis `0 ≤ h0`, and Lean read the goal's `h0` as the
  proof. The ladder's `intro` names a goal binder's guards the same way,
  clear of every binder of the goal, where a guard of `a` named `hd` was
  shadowed by a later binder `hd`. The questions whether a claim is vacuous
  are printed the same way, so a claim over such names whose hypotheses, or
  whose goal's guard, Lean shows empty is now vacuous and fails the check,
  where it got a warning. And a variable named `true` or `false` made the
  Boolean literal name the variable: `def truth(true: Bool) -> true == True`
  printed as `true = true`, which Lean proved, though the claim is false at
  `true = False`. Where such a variable is in scope the literal is now
  `Bool.true`, and the tester refutes the claim. `LeanStatement` gains
  `variables`, the lanky names of its binders; its `binders` hold the names
  as Lean source.
- **A child of `lanky check` lives inside the command's life.** Three edges of
  the child processes that check each source root (#28). A child is started
  with the interpreter's command-line options, as `multiprocessing` starts its
  workers (`-O`, `-W`, `-X` and the rest), where only the environment
  variables that mirror some of them reached it. It is sent `SIGTERM` when
  the command's process ends (`PR_SET_PDEATHSIG` on Linux, a thread watching
  the parent's pid elsewhere), so a `SIGTERM` or a `SIGKILL` sent to the
  command alone, which ends it with nothing run on the way out, no longer
  leaves the child checking for no one until its next write. On `SIGTERM` a
  child kills the Lean REPLs it started before it ends, with the new
  `lanky.oracles.lean.kill_servers`: lean-interact starts the REPL in a
  session of its own, which no signal sent to the child reaches, and it went
  on with the attempt it was given, however long that ran. An interrupt that
  reaches the command alone sends the child `SIGTERM` for the same reason,
  where it sent `SIGKILL`, and `SIGKILL` only if the child is still there
  five seconds later. And once a child has exited, only what it wrote is
  copied: the bytes its pipes held when it exited, rather than everything up
  to their end. A process a checked file left running, with the child's
  output as its own, held the command up until it closed it; what it writes
  is now read and dropped, however often it writes, and a slow standard
  output (a pager) loses nothing the child wrote. All but the first are for
  Linux and macOS: on Windows a child is not told that the command ended,
  is stopped with `TerminateProcess`, which runs nothing in it, and has its
  streams read to their end (#47, #48). (Where every file shares one root
  there is no child, and such a process holds whatever reads the command's
  own output, as it would for any program.) No verdict and no ledger
  changes.

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
