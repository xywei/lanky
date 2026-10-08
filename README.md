# lanky

Python for math you can check.

A lanky file is ordinary Python. The claims live in the annotations, the bodies
run, and one command tells you which claims are proved, which are decided, which
are only tested, and which nobody could establish.

```python
from lanky import theorem
from lanky.prelude import Fin, Fn, Nat


@theorem
def scan_monotone(
    n: Nat,
    cnt: Fn[Fin[n], Nat],
    off: Fn[Fin[n + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),
) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
    """The offsets of an exclusive scan over counts are monotone."""
```

Parameters annotated with sorts are the variables, parameters annotated with
propositions are the hypotheses, and the return annotation is the goal. There is
no new syntax and no parser: lanky evaluates the annotations, and `==` inside one
builds a proposition instead of answering a bool.

Three commands, all of them working today:

```console
$ python examples/gauss.py           # theorems run as property tests
$ pytest examples/gauss.py           # the same theorems, collected as test items
$ lanky check examples/gauss.py      # the ledger: every claim and who decided it
STATUS  BY             WHERE        OWNER          STATEMENT
------  -------------  -----------  -------------  --------------------------------------------
tested  property-test  gauss.py:31  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == ...
proved  lean           gauss.py:39  scan_monotone  n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fi...

2 facts: 1 proved, 1 tested
```

(Abridged: the statement column is trimmed here to fit the page, and this run
is on a machine with the `lean` extra installed. CI runs it on one too, and
checks this table against what it prints.
[docs/quickstart.md](https://github.com/xywei/lanky/blob/main/docs/quickstart.md)
has the untrimmed table.)

That second row is what the project is for. The same file, on a machine without
Lean, reads `tested property-test` and exits 0 just the same: the status column
says how much the claim is worth, and nothing else changes.

## What nothing else does

- **One ledger for evidence of every strength.** A random-draw pass, an isl
  decision and a Lean proof are all facts in one table, each with a status, a
  decider, a provenance and a source location. Property-testing tools give you
  the first, SMT wrappers the second, proof assistants the third, and none of
  them will tell you, for one file, which is which. A fact can rest on others,
  and is worth no more than they are: a proof from a cited axiom reads
  `proved under` that axiom, and is worth what the axiom is.
- **Statements are the signature.** A theorem is a typed Python function. It
  imports, it is callable, it is collected by pytest, and it is readable by
  someone who has never seen a proof assistant.
- **A refutation is a witness, not a verdict.** `REFUTED` carries the
  counterexample, the offending point, or the pair of statement instances that
  makes an ordering wrong. So does the exception a caller sees.
- **A thin host with real plugins.** lanky knows nothing about arrays or loops.
  Its sister project [loopty](https://github.com/xywei/loopty) plugs in a theory
  of loop kernels, an isl oracle, a loopy executor and a `run` verb, and then
  `lanky check` decides in-bounds and disjointness obligations for a sparse
  matrix-vector product, and an illegal loop tiling is refused with

  ```text
  tile(t,i,8,8) illegal: instance S0[t=0, i=8] writes u[1, 8] read by
  S0[t=1, i=7] scheduled earlier
  ```

  (one line in the terminal, wrapped here)

  lanky never imports loopty. It finds it through entry points and asks it what
  it can do. `examples/pytential_skie.py` is a second consumer in miniature: a
  rule engine decides, under eight cited axioms, which of five integral
  representations give a boundary equation of the second kind. And
  `examples/sumpy_recurrence.py` is a third: sumpy's compressed Taylor
  wrangler for the 2-D Laplace kernel claims that its recurrence reconstructs
  every derivative, and the ledger has the claim `tested` by mpmath and
  `decided (heuristic)` by sympy through order 6, and, with Mathlib, `proved
  under harmonic` by Lean for every order, the kernel's harmonicity
  `assumed` on its citation.

## Status

This is 0.1.0, the first release. The core works; the edges are sharp. Below
is what works, what works in part and what does not work yet, and after it,
under Known limits, a kind of claim Lean can prove although the annotation
means something else: read that before you rely on a proof. CI runs the
suite on every change, without Lean on Python 3.12 and 3.13 and with Lean
v4.29.1, and holds the tables on this page and in the quickstart to what
`lanky check` prints. Until 1.0 an interface a plugin uses can change in a
minor release; the CHANGELOG says when one does, and loopty raises its floor
to match.

**Works.**

- `lanky check FILE... [--json OUT] [--verbose]`, exit code 1 on any
  refutation or vacuous claim. Each refuted fact is repeated under the table
  with its counterexample, its witness and its reason, the three standard
  provenance keys, read the same way whichever oracle or plugin refuted it; or
  with `no witness recorded` when it carries none of them. Each axiom is named
  under the table in a `CITED` line with its citation, and a fact left
  `assumed` that an oracle looked at and declined, saying why, in a
  `DECLINED` line with the reason it gave as `declined`, a standard provenance
  key too; neither changes the exit code. A statement that mentions a name
  nothing in it binds, a misspelt parameter or sort, gets one from the
  property tester, which names the name and draws nothing. Two claims with
  one fact id, which a factory gives the claims it makes since an id names a
  definition, fail the check: the first is checked and the others are named
  in a `DUPLICATE` block, unchecked, rather than one silently replacing
  another. Files from different source roots are checked in a process per
  root, so two directories that each hold a `helpers.py` are each checked
  against their own.
- `@theorem`: statement from the signature, `.statement`, `.term`, `.fact()`,
  `.test()`, `.report()`, `.lean()`; callable on concrete values.
- `@axiom(cite=...)`: a statement written like a theorem and taken on a
  citation. Its fact is `assumed (axiom)`, with the citation in its
  provenance; no oracle is asked to establish it, and the property tester
  still looks for a counterexample, so an axiom copied down wrong is refuted
  (and one whose hypotheses nothing satisfies is caught as vacuous).
- Facts rest on facts. `@theorem(uses=[...])` names the theorems, axioms or
  fact ids a theorem rests on, and a plugin sets `Fact.rests_on` on the facts
  it builds. The ledger reads the graph: a row says what it is established
  under (`tested under nicomachus`), and an `EFFECTIVE` column gives the
  weakest status over everything a fact rests on whenever that is weaker than
  its own. `--json` carries `rests_on`, `effective`, `effective_heuristic`
  and `under`. An id no fact in the ledger has counts as an assumption, and
  `lanky check` names it under the table. An id names a definition by the
  module its file's path gives it under its source root,
  `theorem:helpers.lemma@12`, and not by the name the module was imported
  under, so a theorem has the same id in its own file's ledger and in the
  `rests_on` of a file that imports it. A plugin keys its facts the same way,
  with `lanky.ledger.fact_id` and `lanky.check.module_name`.
  `examples/nicomachus.py` is the worked case.
- `@rewrite`: a transformation as a claim. A function of no arguments returns
  `(source, target)`, `obligation=` names what has to hold between them, and
  the fact reads `source ~> target (obligation)`, with a `RewriteTerm` for an
  oracle that knows the obligation to decide. A plugin builds the same shape
  with `lanky.rewrites.rewrite_fact`, and a subclass of `Rewrite` can claim
  more about its target. `examples/pytential_skie.py` is the worked case.
- Trust classes, strongest first: `kernel`, `decision-procedure`, `heuristic`,
  `test`. A decider complete for the fragment it accepts is a decision
  procedure; one that can fail to answer inside it, or whose answers are not
  guaranteed, such as a simplifier, is a `heuristic`. The table marks a fact
  one decided `decided (heuristic)`, and a counterexample the property tester
  finds overrules it. What rests on such a fact is worth `decided (heuristic)`
  at most, in the `EFFECTIVE` column and as `effective_heuristic` in the JSON.
  The oracle that settles a fact leaves its trust class in the provenance.
- The CAS oracle, `cas`, a `heuristic`, where sympy is installed (the `cas`
  extra). It decides a statement that asserts equations, alone, in a
  conjunction or under universals over numbers, with sides built from
  arithmetic, `abs`, `exp`, `log` and `sqrt`, when `sympy.simplify` takes
  the difference of the sides of every equation to `0`, and it declines
  everything else, a difference left over included, with the reason: what
  sympy cannot simplify away is no counterexample, and the property tester
  is asked next. A variable is a symbol with what its sort grants, so
  `sqrt(x**2) == abs(x)` is decided for a real `x` and declined for a
  complex one, and the hypotheses are not read. `lanky.cas` is the bridge,
  both ways, and refuses what it cannot translate faithfully: a family, a
  reduction, a floor division, a variable whose sort is not a set of
  numbers, a real `log` or `sqrt` of what sympy cannot show is not
  negative, where sympy's value is complex and Python's `math` raises.
  sympy is imported on the first fact, never with lanky.
- The ledger: six statuses, provenance, JSON, a rendered table.
- The prelude: `Nat`, `Int`, `Real`, `Complex`, `Bool`, `Prop`, `Fin[n]`,
  `Fn[A, B]`, refinement by `T & prop`, the sum `Fin[n] + Fin[m]` of index
  types (carried for plugins, not yet a binder domain), exactness classes;
  and `lanky.exp`, `lanky.log` and `lanky.sqrt`, which build a term from a
  term and are `math`'s (or `cmath`'s) functions at a number.
- Property testing, including satisfying a definitional hypothesis by
  construction rather than rejection sampling, so a theorem about a scan is
  genuinely tested and not vacuously passed. A synthesized value has to land
  inside the family's codomain, so an unsatisfiable definition drops the draw
  rather than putting a point outside its sort into it. A pass over zero valid
  draws is never reported as `TESTED`: the fact stays `ASSUMED` and its
  provenance says `untested` and why. The reals are read exactly, as Lean
  reads them: `Real` and `Complex` are drawn as fractions whatever their
  exactness class, and `exp`, `log` and `sqrt` are enclosed in intervals
  where their values are not rational (`src/lanky/intervals.py`), so a claim
  is refuted only where the enclosures exclude it.
- Refusing the ways a statement can silently mean something other than what was
  written: a guard joined with Python's `or`, an `and` or `or` used as a value,
  a `not` in a guard, an `if` statement inside a function an annotation
  calls, and a symbolic guard over a concrete domain (`if n > 100` in a sum
  over `Fin[3]`), which a walk of the domain would drop. The connectives are
  `&`, `|` and `~`. Only a generator's `if` clause records a guard: a
  conditional expression (`a if i < 3 else b`), a `not` in a body and a
  comparison of two tuples or lists, which compares their items, are refused
  inside a quantifier, where each used to be read as its guard. A builtin of
  Python's in an annotation is Python's at concrete arguments (`round(0.5)`
  is `0`, and `complex(-1, -0.0)` keeps its negative zero) and refused at a
  variable, naming it (`min(x, y)`), where it used to be a free name; so is
  a truth value a builtin asks for inside a quantifier (`min(i, j)`, `i in
  range(3)`), which used to be recorded as the quantifier's guard, and a
  symbolic domain `zip` or `enumerate` walks. A theorem refuses a parameter
  annotated with a builtin type, `x: int`, or naming one anywhere in its
  annotation, `f: Fn[Fin[n], float]`, and names the sort meant. A term is no
  key of a dict and no member of a set in an annotation: `{0: 1}.get(i, 0)`
  and `i in {0, 1}` are refused, where the lookup answered from the term's
  hash as if the key were absent and Lean proved what that left. Nor is a
  term text, `f"{i}"`, or a truth value, `1 if i else 0`, which answered
  the same at every value; compare it instead, `i != 0`.
- One reading of arithmetic for every oracle. `Nat` means an integer that is
  not negative, and the Lean printer says so: a natural is an `Int` with
  `0 ≤ n` as a hypothesis, and `//` and `%` are `Int.fdiv` and `Int.fmod`,
  which round the way Python's do. What Lean proves is what the property
  tester tests, so a claim is refuted, or not, whether or not Lean is
  installed: `n - 1 >= 0` over `Nat` is refuted everywhere, and `n - 1 <= n`
  is still proved where Lean is. A comparison with no variable in it, which
  only a plugin builds, is ascribed `Int` as well. A `Fraction` is a number
  like an `int`: `x ** Fraction(1, 3)` is a cube root, and not a power to the
  float nearest a third. Every declaration Lean is sent is elaborated with
  `autoImplicit` off, so a name its signature does not bind is an unknown
  identifier to Lean and never a variable Lean picks a type for.
- Vacuous claims are caught. When no draw satisfies a fact's hypotheses, the
  stronger oracles are asked whether the hypotheses alone prove `False`. If one
  does, the row reads `proved (vacuous)` and `lanky check` exits 1: the claim
  is true and says nothing, which is usually a mistake in the hypotheses. If
  none can, a warning says the hypotheses were never satisfied. A goal whose
  own guard never holds, a flipped or off-by-one generator guard, is caught
  the same way: when no draw gets through the goal quantifier's guard, the
  stronger oracles are asked whether it is empty wherever the hypotheses hold,
  and a guard empty only for some values, as `Fin[n]` is at `n = 0`, is never
  flagged.
- A statement the annotation already answered is a claim like any other:
  `-> 1 == 2` is `refuted`, `lanky check` prints why under the table, and it
  exits 1 on it.
- The Lean oracle over core Lean 4, with a tactic ladder and an induction
  strategy read off the term. No Mathlib is fetched or needed. CI runs the
  suite against Lean v4.29.1 as well as without Lean. A name Python accepts
  and Lean reserves, a variable `fun` or a theorem `scoped`, is printed
  quoted (`«fun»`). A theorem is declared as `Lanky.<name>`, so a claim
  named like a core declaration (`and_comm`, `id`, `trivial`) is not refused
  as already declared; a variable named like a root name the printer writes
  (`Int`, `Nat`, `Bool`, `Finset`) has those printed `_root_.Int` in its
  statement; and a variable named `rfl` or `_`, which `intro` and `rcases`
  read as patterns, is introduced under a fresh name. A statement that
  mentions a name nothing in it binds is declined, naming it: Lean would read
  the name as its own declaration of it, Mathlib's `round` for Python's, or
  bind it implicitly at a type of its own choosing, and prove another
  statement. An existential's conditions are conjuncts, so a disjunction
  among them is bracketed, as Python groups it. An attempt that runs
  past `LANKY_LEAN_TIMEOUT` costs that attempt alone: the REPL the driver
  killed is started again for the next. And a REPL ends with the process
  that started it, however that process ends, a `SIGKILL` included: a small
  reaper process per lanky process kills it when the pipe from lanky
  closes, and Ctrl-C during an attempt stops it at once.
- Mathlib mode, opt-in: `LANKY_LEAN_MATHLIB` names a Lake project with
  Mathlib fetched, and `python -m lanky.mathlib DIR` sets one up from the
  project lanky ships, pinned to Mathlib v4.29.1 and every dependency at a
  commit. The oracle imports Mathlib once and prints statements over `Real`
  and `Complex` (`ℝ` and `ℂ`), sums (`∑` over `Finset.Ico`), absolute values,
  true division, floats as the rationals Python holds, and `exp`, `log` and
  `sqrt` (`Real.exp` and the rest, and `Complex.exp`, `Complex.log` and
  `Complex.sqrt`). A complex `log` or `sqrt` is Python's principal branch
  off its branch cut and not on it, so Lean proves a statement that takes
  one only after it proves that every argument stays off the cut (#59). The
  ladder goes on to `norm_num`, `positivity`, `ring`, `field_simp`,
  `linarith` and `nlinarith`, and to an induction for a sum whose bound a
  natural parameter sets, so Gauss's sum in `examples/gauss.py` reads
  `proved lean`. With the variable unset, the oracle is the core one,
  exactly.
  [docs/quickstart.md](https://github.com/xywei/lanky/blob/main/docs/quickstart.md#prove-it-with-mathlib)
  walks through it.
- Induction over families, in Mathlib mode: a claim about every order, a
  universal over naturals whose body is an equation between applications of
  the statement's families, is proved by strong induction on the order, and
  each case is closed by `linear_combination` over the hypotheses and the
  induction hypothesis, normalized by `ring`, or by `field_simp` and `ring`.
  Python finds the combination (`lanky.induction`, with sympy, the `cas`
  extra): which hypothesis to use at which point, and the multipliers, which
  may be expressions in the statement's other variables; Lean checks it.
  `lanky.oracles.lean.use_certificate` is the hook through which a plugin
  hands over multipliers of its own, and `lanky.oracles.lean.decline` leaves
  a claim to the oracles after Lean, saying why. The sumpy demonstration's
  claim for every order is proved this way.
- Plugin discovery by entry point, and `lanky <verb>` from the registry.
- The pytest plugin.

**Partial.**

- The property tester satisfies hypotheses of the shape `f(i) == e` by
  assignment and rejection-samples everything else, so an awkward hypothesis can
  end with no valid draws. The fact is then `ASSUMED`, never falsely `TESTED`.
- `min` and `max` of a variable have no term yet (#66), so an annotation that
  applies one to a variable is refused.
- Division by zero is the one place the readings part. Lean's division is
  total, so `n // 0 == 0` is a theorem there and a `ZeroDivisionError` in
  Python; the fact carries a note, the ledger says what the sampled reading
  could not do, and the exit code stays 0. See `src/lanky/semantics.py`.
- Vacuity is found by sampling first, and sampling cannot tell hypotheses that
  hold nowhere from hypotheses that hold only where it does not look
  (`n == 1000`, with naturals drawn up to five). Both get the warning until an
  oracle proves the hypotheses inconsistent; without one, a vacuous claim
  warns and does not fail the check. A statement over a sort the tester cannot
  draw, such as a family over `Nat`, gets no warning, because no draw reached
  its hypotheses. A goal's guard is read the same way, and only the goal's
  outermost quantifier is: a guard nested deeper in the goal is not examined.
  That holds for a theorem with no parameters as well, whose goal is a goal
  and has no hypotheses to be mistaken for.
- Python's `and` between two propositions in a generator's `if` clause happens
  to produce the conjunction that was written, because of how CPython compiles
  a comprehension filter, so it is not refused. It cannot be told apart from
  two `if` clauses in the bytecode. Write `&`.
- The Lean induction strategy is a shape matcher, not proof search. A statement
  needing a different induction or a lemma falls through to the tester;
  `lanky.oracles.lean.use_tactic` pins a script by hand. The induction over
  families searches, but only for a linear combination: a step that needs a
  hypothesis used other than as an equation to combine, an inequality, or an
  instance whose guards are not linear arithmetic over the integers is not
  found, nor is a base case that holds only because the goal's own guard
  excludes it (`all(f(n) == n for n in Nat if n >= 1)`, whose order 0 is no
  equation to combine). A function Mathlib does not have, a Bessel or Hankel
  function, has no form yet in which its recurrence is declared and a proof
  rests on it (#82).
- The Lean printer covers core Lean: `Sum`, `Abs`, `Real`, true division and
  an exponent that could be negative raise rather than emit source Lean would
  reject. In Mathlib mode all but the last are printed, and what is still
  declined is a sum over `Nat`, a `Fin` with a real bound, a floor division or
  a remainder of a real, an order between complex numbers, and a complex
  logarithm or square root that Lean cannot show stays off its branch cut:
  each would be printed with a meaning Python does not give it. Showing that
  takes the hypotheses and guards around the argument and two cheap attempts,
  so `exp(log(z)) == z` for a nonzero `z`, true on both sides of the cut, is
  declined all the same.
- Over `Real` and `Complex` the tester's enclosures decide less than Lean
  does. Two enclosures can never show two transcendental numbers equal, so an
  equality counts as holding where the statement asserts it and its two sides
  agree to 64 bits: `exp(x + y) == exp(x) * exp(y)` is `tested`, as a
  sampled universal is, on evidence. Under a negation, in a hypothesis, or as
  a value, the same agreement decides nothing, and neither does an order whose
  enclosures overlap, such as `exp(x) * exp(-x) <= 1` at any `x` but `0`
  (#33). Its pass rests on the draws at `x = 0` alone, and says so: the row
  reads `tested`, and a `WARNING` under the table says that the pass rests on
  thin evidence. A complex `log` and `sqrt` are Python's principal branches,
  enclosed off their branch cut, the non-positive real axis, where Python
  picks a side by the sign of a zero, which an exact number does not have
  (#51). On the cut, an `exp` of an argument past `2**14`, and a negative
  number to a power that is not an integer, the draw is left undecided.
  Where Lean is total and Python raises (a division by zero, the logarithm of
  zero, the square root of a negative number), the fact carries a note in
  Mathlib mode, as an integer division by zero does in either mode.
- A family prints as a total function, so every application of one has to be
  shown in bounds before the statement can go to Lean. The check is affine
  arithmetic over the enclosing binders, not a solver, so an argument it cannot
  settle is declined rather than assumed: the statement falls through to the
  tester, which is a proof fewer and never a proof too many.
- Sampling quantifiers over `Nat` draws a handful of points. That is evidence of
  the weakest kind and the ledger says so. A sampled quantifier can be refuted
  but never confirmed: a `forall` that a draw breaks is really false, and an
  `any` that a draw witnesses really true, but an `any` that no draw witnesses
  is undecided, not false, and a `forall` that holds at every draw counts as
  evidence only where the statement asserts it. Under `~`, in a hypothesis or
  the guard of an `all`, and inside a sum or a comparison it is undecided, and
  so is a `forall` whose guard or refinement no draw passes, and a sum over
  draws of `Nat`. The tester declines such a draw and, when no draw decides the
  statement, the fact stays `ASSUMED` with the reason. A declined draw is
  replaced by another, so a pass counts only the draws it could decide; when
  those are outnumbered by the declined ones, or take fewer than three
  distinct assignments when the draws, decided or not, took more, the pass
  stays `tested` and gets a `reason`, printed under the table as a
  `WARNING`. Over `Fin` the domain is enumerated and both answers hold. The
  connectives are three-valued: an operand the draws leave open does not
  decide `&` or `|`, and a false conjunct or a true disjunct settles it
  however the operands are ordered. So are the quantifiers, an `all` being
  the conjunction of its points and an `any` their disjunction: a point the
  draws leave open, or whose guard has no answer, does not end the walk, and
  `all(p(i) for i in Fin[2])` reads as `p(0) & p(1)` does. A refinement is
  read as the hypothesis it is, so one that quantifies over `Nat` rejects a
  draw that breaks it and leaves one it held at undecided. A quantifier over a
  refined domain `T & p`, which a plugin building terms by hand can write,
  ranges over the points of `T` where `p` holds, as the Lean printer reads it:
  enumerated when `T` is, filtered draws when it is sampled.

**Not yet.**

- `CERTIFIED`. The Lean source and the tactic script are in provenance; nothing
  replays them under a checker yet.
- Real analysis beyond what the ladder finds: Mathlib mode states it, and the
  ladder is a fixed set of tactics, not proof search, so a statement that needs
  a lemma by name falls through to the tester (`use_tactic` pins a script).
- A proof scripting surface: today a proof is a tactic ladder lanky drives, not a
  Python program over a live goal.

## Known limits

An annotation is traced Python: lanky runs it on symbolic terms, and the claim
is the term the run builds. An operation that goes through a term's overloads,
an operator, a comparison, a quantifier, a family applied to an index, builds
more of the term. One that answers from the term object instead gives a
concrete answer while the annotation is read, the same at every value, and the
term then says something other than what was written. lanky refuses the cases
it can see in the annotation's own code (a term's hash, text or truth value,
an `if` statement, a builtin of Python's at a variable). These it does not
check yet:

- `is`, and a term's attributes. `i is not 0` is `True` at every `i`, and
  `i.name` is `"i"`, so `all((f(i) * 0 == 1) | (i is not 0) for i in Fin[n])`,
  false at `i = 0`, is proved by core Lean
  ([#88](https://github.com/xywei/lanky/issues/88)).
- A hash, a text or a truth value asked for inside a helper function or a
  library rather than in the annotation itself. `{0: 1}.get(i, 0)` in a
  function the annotation calls answers as if the key were absent, `0` at
  every `i` ([#80](https://github.com/xywei/lanky/issues/80)).
- Comparing or hashing the types. `Fin[n] != Fin[3]` compares the bounds as
  structures and is `True` while the annotation is read, at `n = 3` too
  ([#79](https://github.com/xywei/lanky/issues/79)).

Each has a false claim that Lean proves. The fix is decided, and planned for
0.2.0 ([#91](https://github.com/xywei/lanky/issues/91)): a check rather than
more rules. Each claim gets a `faithful` fact, for which the annotation's
Python is rerun at drawn concrete points and its term has to agree there;
every decision and proof rests on that fact, and a disagreement refutes the
reading. Until then, write a claim with the operators, quantifiers and sorts
lanky provides, and read its statement (the ledger's `STATEMENT` column, or
`.statement`): it is the claim the oracles were given.

## Install

```sh
pip install lanky
```

lanky needs Python 3.12 or later. In a uv project, `uv add lanky`, and the
same for the extras below. The examples and the quickstart are in the
repository and not in the package; clone it to follow them.

The CAS oracle is an extra, which installs sympy:

```sh
pip install "lanky[cas]"
```

Where sympy imports, the oracle is on: an identity sympy simplifies reads
`decided (heuristic)  cas` rather than `tested  property-test`.
`LANKY_CAS_DISABLE=1` turns it off, and `LANKY_CAS_TIMEOUT` caps the seconds
sympy may take over one fact (60).

The Lean oracle is an extra, because it pulls a sizable dependency tree and needs
a Lean toolchain on `PATH`:

```sh
pip install "lanky[lean]"
```

Lean comes from elan, its toolchain manager
([installation](https://github.com/leanprover/elan#installation)).
The toolchain the oracle runs on has to be one the Lean REPL has a build for.
With lean-interact 0.11.5 that is a Lean release up to v4.32.0 (or
v4.33.0-rc1), which elan's current `stable` is not. Given a newer `lean`, the
oracle tries each other toolchain elan has installed, newest first, and then
the newest version the REPL has, which elan downloads when the REPL is first
built. CI uses v4.29.1:

```sh
elan toolchain install leanprover/lean4:v4.29.1
elan default leanprover/lean4:v4.29.1
```

Mathlib mode needs the same extra and toolchain, and a Lake project with
Mathlib fetched, about 7 GB on disk. lanky ships the project, pinned, and one
command writes it and fetches Mathlib:

```sh
python -m lanky.mathlib ~/mathlib    # writes the pinned project, runs `lake exe cache get`
export LANKY_LEAN_MATHLIB=~/mathlib
```

The command never builds Mathlib from source; it fetches the compiled files
Mathlib publishes, keeping the packed downloads in `MATHLIB_CACHE_DIR`
(default `~/.cache/mathlib`). The first session of a process imports Mathlib, which takes
seconds and about 1.5 GB of memory. The induction over families finds its
combinations with sympy, so a claim for every order wants both extras,
`pip install "lanky[lean,cas]"`.

Without the extra, every Lean test skips with a one-line reason and the weaker
oracles do the work. `lanky check --verbose` prints each oracle and whether it
is available. The first use builds a Lean REPL, which takes about a minute and
the network, and caches it in `$XDG_CACHE_HOME/lanky/lean-repl`
(`~/.cache/lanky` by default), outside the virtual environment so that a
reinstall does not throw it away. Useful environment variables:
`LANKY_LEAN_DISABLE=1` makes the oracle a declared no-op (the main CI job sets
it), `LANKY_LEAN_VERSION` pins a toolchain and skips the probe,
`LANKY_LEAN_CACHE_DIR` moves the cache, `LANKY_LEAN_TIMEOUT` caps each
tactic attempt, `LANKY_LEAN_MATHLIB` turns Mathlib mode on, and
`LANKY_LEAN_MATHLIB_IMPORT_TIMEOUT` caps the Mathlib import (600 s).

For work on lanky itself:

```sh
uv sync --group dev --extra lean --extra cas
uv run pytest -q
uv run ruff check .
```

The suite runs with the CAS oracle off, as it runs without Mathlib, and turns
it on in the tests that are about it, which skip without sympy.
`tests/test_sumpy_recurrence.py` skips without sumpy, which no extra
installs: `uv pip install sumpy` puts it in the environment.

CI runs the suite twice. The main job, on Python 3.12 and 3.13, installs no
Lean and sets `LANKY_LEAN_DISABLE=1`, so it sees what a user without the
extras sees. The job named `test with Lean` installs elan, Lean v4.29.1, the
`lean` and `cas` extras and sumpy, caches the toolchain and the built REPL
between runs, and runs the same suite with the Lean oracle on and
`LANKY_LEAN_TEST_REQUIRED=1`, under which a Lean test that cannot get a Lean
session fails instead of skipping. It then runs
`lanky check examples/gauss.py` and checks that the `proved lean` row at the top
of this page is a row the check printed. The suite compares the rest of that
table, and the quickstart's, with the real output in both jobs, reading the
row as `tested property-test` in the main one.

A third job, `test with Lean and Mathlib`, is optional: it may fail without
failing the run, since it depends on fetching Mathlib from outside GitHub. It
sets up the pinned project with `python -m lanky.mathlib`, caching Mathlib's
compiled files between runs, installs sumpy, runs `tests/test_mathlib.py`
and `tests/test_sumpy_recurrence.py` with the project required, and checks
that `lanky check examples/gauss.py` proves both rows and that the sumpy
demonstration's claim for every order is `proved under harmonic`.
The suite otherwise runs in core-Lean mode wherever it runs: it takes
`LANKY_LEAN_MATHLIB` out of its environment and hands it to the Mathlib tests
alone.

A file that carries statements needs `from __future__ import annotations` and a
ruff `F821` per-file ignore, because a size such as `n` is a symbolic variable
lanky invents while evaluating the annotation and has no binding a static checker
can see.

## Architecture

Four ideas, and everything else is one of them.

**Terms.** pymbolic is the expression language, the same one loopy uses, so a
statement and a generated kernel cannot drift apart in translation. lanky adds
`Forall`, `Exists`, `Sum`, `Abs` and `Elementary` (`exp`, `log`, `sqrt`) as
pymbolic subclasses, and comparison operators on them build propositions. The
property tester evaluates them in an exact reading of the reals, rationals and
interval enclosures (`lanky.intervals`), and the file run as a program
evaluates them as Python does.

**Facts and the ledger.** A `Fact` is a statement, a term, a status, a decider,
a provenance, a source location, and the ids of the facts it rests on. `Status`
is `tested, decided, proved, certified, assumed, refuted`. The ledger is the
output of a check and the thing a reviewer reads; it reads the facts' graph as
well, so a fact's status is shown with the assumptions it rests on and what it
is worth given them.

**Four plugin interfaces.** *Theories* turn decorated objects into facts.
*Oracles* establish facts and report a trust class. *Executors* run a decorated
object. *Verbs* are CLI subcommands. Each is an entry-point group:
`lanky.theories`, `lanky.oracles`, `lanky.executors`, `lanky.verbs`.

**Oracles strongest first.** Each plugin is installed once per name, so a
theory that arrives both in process and through an entry point does its work
once. Trust classes are ordered `kernel` (Lean) >
`decision-procedure` (isl) > `heuristic` (a simplifier: sympy, the `cas`
oracle) > `test` (property test). Each oracle answers
`can_establish(fact)`; `check_path` offers each fact to the strongest one that
says yes and stops at the first answer. A fact nobody establishes is `ASSUMED`,
which is not a failure. An oracle that cannot answer declines, so a timeout is
never read as a counterexample. One that took a fact and found it outside what
it decides returns it unchanged with the reason as `declined`, and `lanky
check` prints that under the table for a fact that stays `ASSUMED`.

Decorators are inert and registering: `@theorem` returns a callable object that
runs natively and puts itself in the registry. `lanky check FILE` imports the
file and reads the registry, keeping the claims defined in that file and none
from the modules it imports; `lanky check a.py b.py` checks both, each for its
own. A process imports a module of one name once, so files whose source roots
differ (the directories a check puts on `sys.path`: the file's own, and the one
its package is found from) are checked in child processes, one per root, while
files that share their roots share a process as they always did. A child runs
with the command's interpreter options (`-O`, `-W`, `-X`). On Linux and macOS
it is also sent `SIGTERM` when the command ends, however it ends, and kills
the Lean REPLs it started before it goes; and once it has exited, what it
wrote is copied and nothing a checked file left running holds the command up.
`check_path`, the function
underneath, imports into the process that calls it. No environment variable
changes what the code means.

## Name

- "Lean Annotations Natively Kernel-check Your math".
- LANK + y, where LANK = Lean Annotations, Native Kernel, and *lank* means long
  and thin, next to *lean*.

## Documentation

- [docs/quickstart.md](https://github.com/xywei/lanky/blob/main/docs/quickstart.md):
  the worked file, end to end, with the output the commands actually print,
  a second one with an axiom, the pytential demonstration, where a rule engine
  checks a derivation under the axioms it rests on, and the sumpy
  demonstration, where a recurrence is tested by mpmath and decided by sympy
  through an order, and proved by Lean with Mathlib for every order.
- [CHANGELOG.md](https://github.com/xywei/lanky/blob/main/CHANGELOG.md).
- [loopty](https://github.com/xywei/loopty): the sister project and lanky's
  first plugin: a typed polyhedral layer over loopy, where the facts are about
  loop kernels and isl decides them.

## AI disclosure

This project is developed with substantial assistance from AI coding agents
(Anthropic's Claude, via Claude Code). Design, direction, and review are by Xiaoyu
Wei. Generated text and code are reviewed before release, but readers should assume
AI involvement throughout.

## License

MIT. See [LICENSE](https://github.com/xywei/lanky/blob/main/LICENSE).
