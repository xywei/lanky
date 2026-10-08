# Changelog

All notable changes to lanky are recorded here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/); versions follow
[PEP 440](https://peps.python.org/pep-0440/).

## [Unreleased]

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
