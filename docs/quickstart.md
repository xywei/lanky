# Quickstart

One file, four commands, and the output each one prints, then a second file
with an axiom in it. Everything below was run in this repository on 2026-09-25
with `uv run`; the numbers and the Lean source are copied from the terminal, not
written from memory. The one thing that drifts is a timing, which is a property
of the machine and not of the claim. The `lanky check` tables are held to more
than that: the test suite compares them with a real run, `gauss.py`'s as it
stands where Lean is installed (CI has a job for that) and with its `proved` row
read as `tested` where it is not. That holds for the `gap.py` blocks in
[One reading of arithmetic](#one-reading-of-arithmetic) too: the suite writes
`gap.py` from the snippet shown there and checks it both ways.

```sh
git clone https://github.com/xywei/lanky.git
cd lanky
uv sync --group dev              # add --extra lean for the Lean oracle
```

## The file

`examples/gauss.py` holds two theorems. The first is Gauss's schoolboy sum:

```python
@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""
```

The second is the theorem a sparse matrix layout needs:

```python
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

Nothing here is new syntax. `n: Nat` is a variable, `h0: off(0) == 0` is a
hypothesis (a parameter whose annotation is a proposition), and the return
annotation is the goal. The annotations are Python expressions that lanky
evaluates: `==` on a lanky term builds a proposition rather than answering a
bool, `all(...)` over a generator becomes a universal quantifier, the generator's
`if` clause becomes its guard, and `sum(...)` becomes a reduction. A file like
this needs `from __future__ import annotations` so the annotations are not
evaluated by Python first.

The bodies are docstrings. A theorem's body is never executed by lanky.

Notice that `off` is a parameter and not a return value. That is deliberate and
it is the same convention a kernel uses: a kernel writes its output into an array
its caller allocated, so the claim about the output is a claim about a parameter.
That is what lets this theorem be the postcondition of a kernel somewhere else.

## Run it as a program

```console
$ uv run python examples/gauss.py
gauss at n = 4: True
scan_monotone at n = 3: True (hypotheses {'h0': True, 'hs': True})

gauss: n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
  ok after 50 valid draws of 50

scan_monotone: n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat] | off(0) == 0, forall r in Fin(n). off(r + 1) == off(r) + cnt(r) |- forall a in Fin(n + 1), b in Fin(n + 1) where a <= b. off(a) <= off(b)
  ok after 50 valid draws of 50
```

A theorem is callable: `gauss(n=4)` evaluates the hypotheses and the goal on
concrete values and reports what it found. `.report(n=50)` samples.

`50 valid draws of 50` is worth a second look. `scan_monotone` has a recurrence
as a hypothesis, and a random `off` satisfies it essentially never, so rejection
sampling would report `0 valid draws` and prove nothing. The sampler instead
*satisfies* definitional hypotheses of the shape `f(i) == e` by construction, so
all fifty draws are real evidence. When it cannot, the count says so and the
oracle declines rather than claiming a pass.

## Run it as a test suite

```console
$ uv run pytest examples/gauss.py -q
..                                                                       [100%]
2 passed in 0.03s
```

lanky registers a pytest plugin under the `pytest11` entry point, so each
theorem in a collected module becomes a test item.

## Check it

```console
$ uv run lanky check examples/gauss.py
STATUS  BY             WHERE        OWNER          STATEMENT
------  -------------  -----------  -------------  ------------------------------------------------------------------------
tested  property-test  gauss.py:31  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
proved  lean           gauss.py:39  scan_monotone  n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat] | off(0) ==...

2 facts: 1 proved, 1 tested
```

This is the command the project exists for. It imported the file, read the
registry the decorators filled, turned each theorem into a `Fact`, and offered
each fact to the oracles strongest first.

The table holds the claims defined in `gauss.py` itself. A theorem the file
imports from another module is not in it, whether or not that module was
imported before, so checking a file twice gives the same table twice. To check
the other module's claims, list its file as well: `lanky check a.py b.py`
prints one ledger per file, each under a `==> a.py <==` heading. A file inside
a package may use relative imports; it is given its package while it is
checked.

The two rows differ, and the difference is the product.

- `scan_monotone` is `proved` by `lean`. The Lean oracle printed the statement as
  core Lean 4, found a tactic script, and elaborated the whole declaration in a
  fresh environment. There is no Mathlib anywhere in this.
- `gauss` is `tested` by `property-test`. Its reduction needs `Finset`, which
  needs Mathlib, so the Lean printer declines the term and the next oracle down
  takes it. In Mathlib mode Lean proves it too; see
  [Prove it with Mathlib](#prove-it-with-mathlib).

Without the Lean extra installed, or with `LANKY_LEAN_DISABLE=1`, both rows read
`tested property-test` and the exit code is 0 either way. Nothing about the code
changes; only the strength of the evidence does, and the table says which.

`--verbose` prints the oracles and their availability first:

```console
$ uv run lanky check examples/gauss.py --verbose
lean (kernel): available (untested until the first fact: the REPL is built on demand)
property-test (test): available
...
```

The parenthetical is the honest part. What was checked is cheap: `lean` is on
`PATH` and the driver imports. Whether a REPL can actually be built is found out
on the first fact and then remembered, so after anything has been attempted the
line names the Lean version in use instead.

On a machine with no Lean it reads
`lean (kernel): unavailable: lean_interact is not installed (pip install lanky[lean])`,
which is a one-line reason and not an error.

## Read the provenance

```console
$ uv run lanky check examples/gauss.py --json out.json
```

The proved fact carries the Lean version, the tactic script and the whole
declaration that closed it (line-wrapped here; the stored source puts the
statement on one line):

```text
lean_version: v4.29.1

theorem scan_monotone (n : Int) (h0 : 0 ≤ n) (cnt : Int → Nat) (off : Int → Nat)
    (h1 : (off 0 : Int) = 0)
    (h2 : ∀ r : Int, 0 ≤ r → r < n → (off (r + 1) : Int) = (off r : Int) + (cnt r : Int)) :
    ∀ a : Int, 0 ≤ a → a < n + 1 → ∀ b : Int, 0 ≤ b → b < n + 1 → a ≤ b →
      (off a : Int) ≤ (off b : Int) := by
  intro a hd hd_1 b hd_2 hd_3 hg
  obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le hd_2
  induction b with
  | zero =>
    first | omega | (have hzero : a = ((0 : Nat) : Int) := (by omega); subst hzero; ...) | ...
  | succ k ih =>
    have hcast : ((k + 1 : Nat) : Int) = (k : Int) + 1 := (by omega)
    try simp only [hcast] at *
    first | (have hstep := h2 k (by omega) (by omega)) | skip
    by_cases hlt : (k : Int) < a
    ...
```

Three representation choices are visible there. A natural is an `Int` with
`0 ≤ n` as a hypothesis, which is the integer reading every oracle shares (see
[One reading of arithmetic](#one-reading-of-arithmetic) below). A bounded
quantifier prints as a guarded `Int` quantifier, `∀ a : Int, 0 ≤ a → a < n + 1
→ ...`, rather than `∀ a : Fin (n + 1)`, because `omega` reasons about linear
integer arithmetic and the `Fin` form would bring coercions the lanky statement
does not mean. And `Fn[Fin[n], Nat]` prints as the total function `Int → Nat`,
whose values are cast, `(off a : Int)`, where they are used as numbers, with
boundedness living in the guards, which is sound as long as the statement
never mentions a point outside them. That last clause is a
check and not a hope: before printing anything, lanky shows that every
application of a family stays inside its domain, reading the argument as an
affine expression in the enclosing binders, so `off(r + 1)` against an
`off : Fn[Fin[n + 1], Nat]` with `r` in `Fin[n]` goes through and `off(n + 1)`
is declined with `UnsupportedTerm`. A declined statement falls to the property
tester, which has nothing to compare at such a point either and says so.

The script was not written by hand. The ladder tries `omega`, `decide`, `simp`,
`simp_all`, `simp_all <;> omega` and two intro-plus-closer scripts, and then an
induction strategy that reads its induction variable, its split variable and
every fresh name off the term. A guard `a <= b` says `b` is reached from `a` by
steps, so `b` is what gets induced on. It is an `Int`, so the script first
trades it for the natural it is, through its `0 ≤ b` hypothesis, and inducts on
that. When the ladder runs out, the fact comes back unchanged with
`lean_tried` in its provenance and the property tester takes it.

`lanky.oracles.lean.use_tactic(scan_monotone, "...")` pins a script by hand when
the ladder cannot find one, and the ledger records a pinned script exactly the
way it records a found one.

## One reading of arithmetic

A lanky statement is read by more than one oracle: the property tester
evaluates it with Python's arithmetic, and Lean elaborates what the printer
sends it. They read the same statement, the integer one. `Nat` means an integer
that is not negative, so a natural prints as an `Int` with `0 ≤ n` as a
hypothesis, subtraction is integer subtraction, and `//` and `%` print as
`Int.fdiv` and `Int.fmod`, which round toward negative infinity as Python's do
(a positive literal divisor prints as `/` and `%`, which agree with them there
and which `omega` understands). Lean's truncated `Nat` subtraction never
appears.

Put this in `gap.py`, with the same two imports `examples/gauss.py` has:

```python
@theorem
def truncated(n: Nat) -> n - 1 >= 0:
    """False at n = 0, and false in Lean too."""
```

```console
$ uv run lanky check gap.py
STATUS   BY             WHERE     OWNER      STATEMENT
-------  -------------  --------  ---------  ---------------------
refuted  property-test  gap.py:7  truncated  n : Nat |- n - 1 >= 0

1 facts: 1 refuted

REFUTED truncated at gap.py:7: n : Nat |- n - 1 >= 0
  counterexample: {'n': 0}
  the goal is false at this assignment
```

That is the output with the Lean extra and without it, and `lanky check` exits
1 either way. Lean is given `theorem truncated (n : Int) (h0 : 0 ≤ n) : n - 1 ≥
0`, which is false at `n = 0` as the Python reading is, so no tactic closes it
and the tester's counterexample is the answer. A statement whose integer
reading is true keeps its proof: `n - 1 <= n` reads `proved lean`.

One gap is left. Division by anything that is not a nonzero literal is total in
Lean, where `Int.fdiv n 0` is `0`, and an exception in Python. Put
`def div_zero(n: Nat) -> n // 0 == 0` in the same `gap.py` in place of
`truncated`, and with Lean the row reads `proved lean` with this under the
table:

```text
SEMANTICS div_zero at gap.py:7: no draw could decide the statement: the statement divides by zero at this draw, which Python raises on and Lean's total integer division does not, so the two readings differ here rather than the statement being false
  division or remainder by a divisor that is not a nonzero literal: Lean's integer division is total (Int.fdiv x 0 is 0 and Int.fmod x 0 is x) while Python raises ZeroDivisionError, so the sampled reading cannot answer where Lean can
```

(two lines in the terminal, each wrapped by your pager rather than by lanky.)
The sampled reading is not a counterexample there, and it is not agreement
either: it is a reading that could not be run, which is worth saying. Without
Lean the row is `assumed`, and the exit code is 0 both ways, because nothing
was refuted. `lanky.semantics.notes(term)` is the check.

## Take a result on a citation

Some results lanky cannot establish. A sum needs Mathlib in Lean, and a theorem
from a textbook may need a great deal more. Such a result enters the ledger on
the word of a reference, as an axiom, and what is derived from it says so.
`examples/nicomachus.py` holds Gauss's sum again, Nicomachus's theorem as an
axiom, and the closed form of the sum of cubes, which follows from the two:

```python
@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@theorem(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """Four times the sum of the cubes of ``0 .. n`` is ``(n * (n + 1)) ** 2``."""
```

An axiom is written like a theorem, and `cite=` is required: `@axiom` without
it raises `TypeError` where it is written, because an axiom with nothing behind
it is what an `assumed` theorem already is. `uses=` takes theorems, axioms,
facts or fact ids, and becomes the `rests_on` of the theorem's fact.

```console
$ uv run lanky check examples/nicomachus.py
STATUS                   EFFECTIVE  BY             WHERE             OWNER       STATEMENT
-----------------------  ---------  -------------  ----------------  ----------  ------------------------------------------------------------------------
tested                   tested     property-test  nicomachus.py:33  gauss       n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
assumed (axiom)          assumed    -              nicomachus.py:38  nicomachus  n : Nat |- sum(i**3 for i in Fin(n + 1)) == sum(i for i in Fin(n + 1)...
tested under nicomachus  assumed    property-test  nicomachus.py:43  cubes       n : Nat |- 4*sum(i**3 for i in Fin(n + 1)) == (n*(n + 1))**2

3 facts: 1 assumed, 2 tested
```

The same with Lean and without it, since every statement has a sum in it
(Mathlib mode, below, proves `gauss` and `cubes`). Three things in that table
are new.

- `assumed (axiom)`. The axiom is taken on its citation, which `--json`
  carries as `cite` in its provenance, and no oracle is asked to establish it.
  It is still sampled for a counterexample, because a citation copied down
  wrong states something the reference does not.
- `tested under nicomachus`. `cubes` survived its draws, and the status names
  the assumptions it rests on: whatever it rests on, directly or through other
  facts, that nothing here established. That is an axiom, another `assumed`
  fact, a `refuted` one, a fact on a circle of facts that rest on each other,
  or an id this ledger does not hold: a theorem of another file, since each
  file checked has a ledger of its own, or an id written wrong. `lanky check`
  names such an id in an `UNRESOLVED` line under the table, since in the row it
  reads like any other assumption. `gauss` is not among them, because it is
  tested.
- The `EFFECTIVE` column. What each fact is worth once what it rests on is
  counted: the weakest status over the fact and everything below it, so a
  proof from an assumption is worth the assumption. The column is there only
  when some fact is worth less than its own status says, so a ledger in which
  nothing rests on anything, like `gauss.py`'s, looks as it always did.

The status column is still each fact's own. `tested` says how strongly `cubes`
is established given what it uses; the oracles decide it as they decide any
theorem, and are not handed the statements it uses. `--json` carries
`rests_on`, `effective` and `under` for every fact, and the exit code depends
on none of them: it is 0 here, since nothing is refuted.

Copy the axiom down wrong, with `i**2` for `i**3` on the left, and the property
tester refutes it. The row reads `refuted (axiom)`, `cubes` is worth `refuted`
in the `EFFECTIVE` column, the counterexample is printed under the table, and
`lanky check` exits 1. So does an axiom whose hypotheses were copied down so
that nothing satisfies them, once Lean shows them inconsistent: it reads
`assumed (axiom) (vacuous)`, as a theorem would read `proved (vacuous)`.
`pytest examples/nicomachus.py` samples the axiom as a test item too.

A plugin's facts rest on facts the same way: it sets `rests_on` on the facts
it builds, naming other facts by id.

## Prove it with Mathlib

Core Lean cannot state `gauss`: a sum is Mathlib's `Finset.sum`. Mathlib mode is
opt-in. It needs the `lean` extra and a toolchain, as core Lean does, plus a
Lake project with Mathlib fetched, and an environment variable naming that
project. lanky ships the project, pinned: Mathlib v4.29.1 on Lean v4.29.1, with
every dependency at a commit in its `lake-manifest.json`. One command sets it
up:

```console
$ uv run python -m lanky.mathlib ~/mathlib
wrote the pinned Mathlib project (v4.29.1) to /home/you/mathlib
...
Completed successfully!
ready: export LANKY_LEAN_MATHLIB=/home/you/mathlib
```

(abridged: the middle is Lake cloning Mathlib and the cache tool fetching it.)
It writes three files and runs `lake exe cache get`, which clones Mathlib and
its dependencies at the pinned commits and fetches the compiled files Mathlib
publishes: about 7 GB on disk and a few minutes. It never builds Mathlib from
source, which would take hours. Then:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/gauss.py
STATUS  BY    WHERE        OWNER          STATEMENT
------  ----  -----------  -------------  ------------------------------------------------------------------------
proved  lean  gauss.py:31  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
proved  lean  gauss.py:39  scan_monotone  n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat] | off(0) ==...

2 facts: 2 proved
```

Both rows are proved now. The oracle started its REPL in the project, imported
Mathlib once (seconds, and about 1.5 GB of memory), and elaborated each attempt
in the environment the import left. `scan_monotone` is proved as before, by the
same induction: a statement core Lean could print is printed the same way, and
the core attempts run first, with Mathlib's closing tactics added to theirs. `gauss` is printed in the Mathlib dialect,

```text
theorem gauss (n : Int) (h0 : 0 ≤ n) :
    2 * (∑ i ∈ Finset.Ico 0 (n + 1), i) = n * (n + 1)
```

where `Fin[n + 1]` is `Finset.Ico 0 (n + 1)` over `Int`, so the binder is an
integer as a quantifier's is. The core attempts fail, and so do Mathlib's
whole-goal ones (`norm_num`, `positivity`, `ring`, `field_simp`, `linarith`,
`nlinarith`, and three that combine them with `push_cast` and `simp`), and the
last script is an induction on `n`,
which the ladder chose because `n` is a natural parameter that the bound of a
sum mentions: trade `n` for the natural it is, and in each case take the last
term off the sum, which leaves the induction hypothesis and a polynomial
identity for `linarith`. The provenance records the script, the Mathlib
revision as `lean_mathlib`, and the source as a file that replays it, starting
with `import Mathlib`. `--verbose` names the project while nothing has been
tried, and then `Lean v4.29.1 with Mathlib v4.29.1 (...)`.

The same variable makes `examples/nicomachus.py` read `proved` for `gauss` and
`proved under nicomachus` for `cubes`, which the induction proves on its own.
It is still worth `assumed`, because `uses=` says what it rests on.

What the Mathlib dialect adds, in brief (`src/lanky/lean.py` has the whole
account):

- `Real` and `Complex` are `ℝ` and `ℂ`, and `lanky.exp`, `lanky.log` and
  `lanky.sqrt` are `Real.exp`, `Real.log` and `Real.sqrt`, or `Complex.exp`
  and `Complex.log` of a complex argument. At a number they are Python's
  `math` and `cmath` functions, so the file still runs.
- A float literal is the rational number Python holds, `(1 / 2 : ℝ)` for
  `0.5`, and true division is division in a field, `(x : ℝ) / y`, because
  Python's `/` does not divide integers as integers either.
- `abs(x)` is `|x|`, and `‖z‖` for a complex `z`, which is the modulus Python
  computes.
- An integer floor division next to a real is ascribed, `x + (n / 2 : ℤ)`:
  Lean casts every leaf of an arithmetic tree to the widest type in it, and
  without the ascription `n / 2` would divide the cast `n` in `ℝ`.

The readings of a real statement are not one reading. The property tester
computes `Real` in floating point, with fractions for `Real.exact`, and Lean
over `ℝ`: `exp(x + y) == exp(x) * exp(y)` is refuted by rounding without
Mathlib and proved with it. Where Lean's functions are total and Python's
raise, the fact carries a note, as `div_zero` does above: a true division by
something that may be zero, and a logarithm or square root of something that
may leave its Python domain. `def neg(x: Real & (x < 0)) -> sqrt(x) == 0` is
proved with Mathlib, whose square root of a negative number is `0`, and no
draw can evaluate it in Python.

## What to try next

- Write a false theorem and check it. The status is `refuted`, the
  counterexample is in the provenance, `lanky check` repeats the fact under
  the table with the counterexample and the reason, and it exits 1. The block
  under a `REFUTED` line is built from three standard provenance keys, read
  the same way whichever oracle or plugin refuted the fact: the
  `counterexample`, a `witness` (a plugin's refuting object, such as the cell
  loopty's isl oracle finds outside an array), and the `reason`, each when it
  says something, or `no witness recorded` when none does. That holds
  for `def impossible() -> 1 == 2` as well, which has no variable to name in a
  counterexample: Python answers the annotation itself, the term is the `bool`
  `False`, and the row still reads `refuted`, with the reason (the statement
  is the constant `False`) printed where a counterexample would be. The JSON
  keeps the empty counterexample.
- Leave off a theorem's return annotation. `@theorem` raises `TypeError`
  where the function is defined, because a theorem needs a goal, and
  `lanky check` reports the file as one that does not import.
- Write a theorem whose hypotheses no sample can satisfy, such as
  `def vacuous(n: Nat, h: (n > 2) & (n < 1)) -> n == n + 1`. Without Lean the
  fact comes back `assumed`, rather than passing vacuously; its provenance
  carries `untested` with the reason and `valid: 0`, and under the table:

  ```text
  WARNING vacuous at vacuous.py:7: hypotheses never satisfied in 4000 draws
    no oracle could show them inconsistent, so the claim may be vacuous
  ```

  With Lean, `omega` proves the goal from the contradictory hypotheses, which
  is a valid proof of a claim that says nothing. The tester's cross-check
  finds that no draw satisfied the hypotheses, Lean then proves them
  inconsistent on their own (`theorem vacuous ... : False`), and the ledger
  says so and exits 1:

  ```text
  STATUS            BY    WHERE         OWNER    STATEMENT
  ----------------  ----  ------------  -------  ---------------------------------------
  proved (vacuous)  lean  vacuous.py:7  vacuous  n : Nat | n > 2 and n < 1 |- n == n + 1

  1 facts: 1 proved; 1 vacuous

  VACUOUS vacuous at vacuous.py:7: n : Nat | n > 2 and n < 1 |- n == n + 1
    the hypotheses are inconsistent: proved by lean, so the goal is never at stake
    hypotheses never satisfied in 4000 draws
  ```

  `--json` carries the mark as `vacuous` in the provenance, next to the proof
  of inconsistency. Hypotheses that hold only where the sampler does not look,
  `h: n == 1000` with naturals drawn up to five, get the warning on both
  machines: Lean proves the claim and cannot prove `False`, and the exit code
  is 0. Under `pytest` a theorem with unsatisfiable hypotheses is reported as
  skipped.
- Write `def unwitnessed() -> any(x == 100 for x in Nat)` and check it with
  `LANKY_LEAN_DISABLE=1`, so that the property tester is the only oracle. `Nat`
  is sampled rather than enumerated, so no draw witnesses the statement, and no
  draw refutes it either: the row reads `assumed`, its provenance says why, and
  `lanky check` exits 0. Write the same shape over an index type,
  `def enumerated(n: Nat) -> any(i == 0 for i in Fin[n + 1])`, and the domain is
  walked rather than sampled, so that row reads `tested`. (With Lean on the
  machine both rows read `proved lean` instead: `simp` finds the witness the
  sampler cannot. The point is what each oracle can honestly say, and the
  status column is where it says it.)
- The mirror image is a sampled `all`, again with `LANKY_LEAN_DISABLE=1`.
  `def bounded(n: Nat) -> all(k < 100 for k in Nat)` holds at every draw, and
  the row reads `tested`: that is evidence, and the goal is where the
  statement asserts it. Negate it,
  `def denied(n: Nat) -> ~all(k < 100 for k in Nat)`, which is true, and the
  same draws would refute it, so the tester reads a pass of a sampled `all`
  under `~`, in a hypothesis or the guard of an `all`, or inside a sum as
  undecided: the row reads `assumed`, with the reason. A draw that breaks a
  sampled `all` is a counterexample wherever it stands.
- `uv sync --group dev --extra lean`, put a Lean toolchain the REPL supports on
  `PATH` (the README's Install section says which; CI uses v4.29.1), and watch
  a row change from `tested` to `proved`. The first run builds a Lean REPL,
  takes about a minute, and is cached in `$XDG_CACHE_HOME/lanky/lean-repl`
  (`~/.cache/lanky/lean-repl` by default), which is outside the virtual
  environment and survives a reinstall; `LANKY_LEAN_CACHE_DIR` moves it and
  `LANKY_LEAN_VERSION` skips the toolchain probe.
- Install [loopty](https://github.com/xywei/loopty) in the same environment and
  run `lanky check` on a file of loop kernels. The same table fills with
  in-bounds and disjointness facts decided by isl, and `lanky run` appears as a
  subcommand because loopty registered a verb.

## Where things are

| what | where |
|---|---|
| terms, the scope, annotation evaluation | `src/lanky/terms.py` |
| sorts, `Fin`, `Fn`, refinement | `src/lanky/prelude.py` |
| `Status`, `Fact`, `Ledger`, and what a fact rests on | `src/lanky/ledger.py` |
| the four plugin protocols and the registry | `src/lanky/plugins.py` |
| `@theorem`, `@axiom`, `Theorem` and `Axiom` | `src/lanky/theory.py` |
| samplers and the property tester | `src/lanky/testing.py` |
| where the readings still differ: division by zero, `log`, `sqrt` | `src/lanky/semantics.py` |
| the Lean printer, core Lean's dialect and Mathlib's | `src/lanky/lean.py` |
| Mathlib mode: the pinned project and its setup | `src/lanky/mathlib.py`, `src/lanky/mathlib-project/` |
| the oracles | `src/lanky/oracles/` |
| `check_path` and the CLI | `src/lanky/check.py`, `src/lanky/cli.py` |
