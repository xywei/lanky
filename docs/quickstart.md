# Quickstart

One file, four commands, and the output each one prints, then a second file
with an axiom in it, and a third in which a rule engine checks a derivation.
Everything below was run in this repository with `uv run`, the last section on
2026-09-26 and the rest on 2026-09-25; the numbers and the Lean source are
copied from the terminal, not written from memory. The one thing that drifts
is a timing, which is a property of the machine and not of the claim. The
`lanky check` tables are held to more than that: the test suite compares them
with a real run, `gauss.py`'s as it stands where Lean is installed (CI has a
job for that) and with its `proved` row read as `tested` where it is not, and
the demonstration's the other way round. That holds for the `gap.py` blocks in
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
  takes it.

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

CITED nicomachus at nicomachus.py:38: Nicomachus of Gerasa, Introduction to Arithmetic
```

The same with Lean and without it, since every statement has a sum in it. Four
things in that output are new.

- `assumed (axiom)`. The axiom is taken on its citation, which the `CITED`
  line under the table shows and `--json` carries as `cite` in its provenance,
  and no oracle is asked to establish it. It is still sampled for a
  counterexample, because a citation copied down wrong states something the
  reference does not.
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
- The `CITED` line. Each axiom is named under the table with the citation it
  is taken on, one line per axiom in the table's order, since that is what
  stands behind its row and behind every `under` that names it.

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

## Check a derivation against what it rests on

Much of what a consumer of lanky wants checked is a transformation rather than
a formula: an integral representation taken to the boundary, a loop nest
rescheduled. That is a *rewrite*. Some tool turns a source into a target, and
an obligation between the two says when that was sound. `@rewrite` states one:
it decorates a function of no arguments that returns `(source, target)`, with
`obligation="..."` naming what has to hold (`"equal"` by default). Its fact
has kind `rewrite`, a `lanky.RewriteTerm` as its term and the statement
`source ~> target (obligation)`, and an oracle that knows the obligation
decides it; nothing else takes it, so an undecided rewrite stays `assumed`. A
plugin that builds its facts itself calls `lanky.rewrites.rewrite_fact`.

`examples/pytential_skie.py` is the worked case. It asks, for five integral
representations of the kind a pytential user writes, whether each gives a
boundary integral equation of the second kind on a closed boundary of class
C²: `c*I` plus a compact operator, with `c` not zero. Its rule engine, an
algebra of the operators `I`, `S`, `D`, `S'` and `D'` with polynomial
coefficients, is in `examples/layer_potentials.py`, where a plugin's would be;
lanky itself knows nothing about layer potentials.

```console
$ uv run python examples/pytential_skie.py
On a closed boundary of class C2, each representation gives, from the side shown:

problem                                         representation            boundary equation                        verdict
----------------------------------------------  ------------------------  ---------------------------------------  --------------------------------
Laplace, interior Dirichlet                     u = D sigma               (-1/2*I + D) sigma = f                   second kind
Laplace, interior Dirichlet                     u = S sigma               S sigma = f                              refused: no identity term
Laplace, interior Neumann                       u = S sigma               (1/2*I + S') sigma = g                   second kind
Helmholtz, exterior Dirichlet (combined field)  u = (D - 1j*eta*S) sigma  (1/2*I + D - 1j*eta*S) sigma = f         second kind
Helmholtz, exterior Neumann (Burton-Miller)     u = (D - 1j*eta*S) sigma  (1j/2*eta*I + D' - 1j*eta*S') sigma = g  refused: D' is not c*I + compact

laplace_dirichlet_dlp: the identity coefficient is -1/2, not 0, and the rest is compact (D by compact_D). Under jump_D, compact_D.
laplace_dirichlet_slp: the identity coefficient is 0 and the rest is compact (S by compact_S): the operator is compact. Under jump_S, compact_S.
laplace_neumann_slp: the identity coefficient is 1/2, not 0, and the rest is compact (S' by compact_Sp). Under jump_Sp, compact_Sp.
helmholtz_combined_field: the identity coefficient is 1/2, not 0, and the rest is compact (D by compact_D, S by compact_S). Under jump_D, jump_S, compact_D, compact_S.
helmholtz_burton_miller: D' is not c*I + compact (hypersingular_Dp) and its coefficient is 1, not 0, while the rest is compact (S' by compact_Sp): the operator is not c*I + compact either. Under jump_Dp, jump_Sp, compact_Sp, hypersingular_Dp.

pytential is not importable here, so the rows were built with this file's operators alone.

The axioms are taken on a citation: `lanky check examples/pytential_skie.py` lists them, and what each verdict is decided under.
```

Each claim is a rewrite from the trace of a representation to the operator it
is said to give, under the obligation `jump relations`, together with a
verdict about that operator. The rules are eight axioms, each with its
citation: the four jump relations, `compact(S)`, `compact(D)`, `compact(S')`,
and `~scalar_plus_compact(D')`, which says that `D'`, being hypersingular, is
no multiple of the identity plus a compact operator. The engine reads its
rules off their statements and applies nothing else.

```console
$ uv run lanky check examples/pytential_skie.py
STATUS                                                        EFFECTIVE  BY             WHERE                  OWNER                     STATEMENT
------------------------------------------------------------  ---------  -------------  ---------------------  ------------------------  ------------------------------------------------------------------------
assumed (axiom)                                               assumed    -              pytential_skie.py:94   jump_S                    gamma : C2Boundary, s : Side |- trace(S, s) == S
assumed (axiom)                                               assumed    -              pytential_skie.py:99   jump_D                    gamma : C2Boundary, s : Side |- trace(D, s) == 1/2*s*I + D
assumed (axiom)                                               assumed    -              pytential_skie.py:104  jump_Sp                   gamma : C2Boundary, s : Side |- normal_derivative(S, s) == -1/2*s*I + S'
assumed (axiom)                                               assumed    -              pytential_skie.py:109  jump_Dp                   gamma : C2Boundary, s : Side |- normal_derivative(D, s) == D'
assumed (axiom)                                               assumed    -              pytential_skie.py:114  compact_S                 gamma : C2Boundary |- compact(S)
assumed (axiom)                                               assumed    -              pytential_skie.py:119  compact_D                 gamma : C2Boundary |- compact(D)
assumed (axiom)                                               assumed    -              pytential_skie.py:124  compact_Sp                gamma : C2Boundary |- compact(S')
assumed (axiom)                                               assumed    -              pytential_skie.py:129  hypersingular_Dp          gamma : C2Boundary |- ~scalar_plus_compact(D')
decided under jump_D                                          assumed    layer-rules    pytential_skie.py:151  laplace_dirichlet_dlp     trace(D, INTERIOR) ~> -1/2*I + D (jump relations)
tested                                                        tested     property-test  pytential_skie.py:151  laplace_dirichlet_dlp     coefficient of I: -1/2 != 0
decided under jump_D, compact_D                               assumed    layer-rules    pytential_skie.py:151  laplace_dirichlet_dlp     -1/2*I + D is second kind
decided under jump_S                                          assumed    layer-rules    pytential_skie.py:157  laplace_dirichlet_slp     trace(S, INTERIOR) ~> S (jump relations)
decided under jump_S, compact_S                               assumed    layer-rules    pytential_skie.py:157  laplace_dirichlet_slp     S is first kind: no identity term
decided under jump_Sp                                         assumed    layer-rules    pytential_skie.py:163  laplace_neumann_slp       normal_derivative(S, INTERIOR) ~> 1/2*I + S' (jump relations)
tested                                                        tested     property-test  pytential_skie.py:163  laplace_neumann_slp       coefficient of I: 1/2 != 0
decided under jump_Sp, compact_Sp                             assumed    layer-rules    pytential_skie.py:163  laplace_neumann_slp       1/2*I + S' is second kind
decided under jump_D, jump_S                                  assumed    layer-rules    pytential_skie.py:169  helmholtz_combined_field  trace(D - 1j*eta*S, EXTERIOR) ~> 1/2*I + D - 1j*eta*S (jump relations)
tested                                                        tested     property-test  pytential_skie.py:169  helmholtz_combined_field  coefficient of I: 1/2 != 0
decided under jump_D, jump_S, compact_D, compact_S            assumed    layer-rules    pytential_skie.py:169  helmholtz_combined_field  1/2*I + D - 1j*eta*S is second kind
decided under jump_Dp, jump_Sp                                assumed    layer-rules    pytential_skie.py:175  helmholtz_burton_miller   normal_derivative(D - 1j*eta*S, EXTERIOR) ~> 1j/2*eta*I + D' - 1j*eta...
decided under jump_Dp, jump_Sp, compact_Sp, hypersingular_Dp  assumed    layer-rules    pytential_skie.py:175  helmholtz_burton_miller   1j/2*eta*I + D' - 1j*eta*S' is not second kind: D' is not c*I + compact

21 facts: 8 assumed, 10 decided, 3 tested

CITED jump_S at pytential_skie.py:94: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_D at pytential_skie.py:99: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_Sp at pytential_skie.py:104: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_Dp at pytential_skie.py:109: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_S at pytential_skie.py:114: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_D at pytential_skie.py:119: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_Sp at pytential_skie.py:124: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED hypersingular_Dp at pytential_skie.py:129: D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3
```

That is the output without Lean. With the `lean` extra the three coefficient
rows read `proved  lean`: `coefficient of I: -1/2 != 0` goes to Lean as
`(-1 : Int) ≠ 0`, the numerator's being nonzero, since core Lean has no
rationals, and that arithmetic is the one part of the argument Lean touches.
Nothing about compactness is claimed proved. Those are the `assumed (axiom)`
rows, each verdict is `decided under` the ones it used, and in the `EFFECTIVE`
column it is worth what they are.

- **The decider says how far to trust it.** `layer-rules` has the trust class
  `decision-procedure`, as isl does. It accepts one-sided traces of
  combinations of `S` and `D` of one kernel, boundary operators made of `I`,
  `S`, `D`, `S'`, `D'` and such traces, and polynomial coefficients; within
  that fragment it answers every claim by exact polynomial arithmetic, and it
  declines everything outside it with the reason (a verdict that depends on a
  parameter's value, two operators that are not a multiple of the identity
  plus a compact one, two kernels, a trace no axiom gives). A decider that can
  fail to answer inside its own fragment, or whose answers are not
  guaranteed, such as a computer-algebra simplifier, declares the class
  `heuristic`, which ranks between `test` and `decision-procedure`. The table
  marks a fact one decided as `decided (heuristic)`, a counterexample the
  property tester finds overrules it, and only a decision procedure or a
  kernel can make a fact vacuous.
- **A refusal is a verdict, and names its term.** The single layer is claimed
  of the first kind (no identity term), and the Neumann trace of the combined
  field is claimed not of the second kind because of `D'`; both are decided.
  Claim the second kind for either and the verdict is refuted, with the term
  that prevents it in the reason.
- **A wrong derivation fails the check.** Write `1/2*I + D` for the interior
  trace of `D` and the rewrite is refuted, with the difference, `-I`, in the
  reason. Copy a jump relation down with its sign flipped and every rewrite
  that applies it is refuted, and the verdicts resting on those are worth
  `refuted` in the `EFFECTIVE` column.
- **pytential is optional.** Where it imports, the demonstration builds the
  five again with `pytential.sym` and translates them with
  `layer_potentials.from_pytential`, which reads `qbx_forced_limit` as the
  side, and checks two of pytential's own `DirichletOperator` pairs against
  the same rules. pytential is imported inside the demonstration only; it is
  not a dependency of lanky, and `import lanky` does not import it.

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
| `@rewrite`, `Rewrite`, `RewriteTerm` and `rewrite_fact` | `src/lanky/rewrites.py` |
| samplers and the property tester | `src/lanky/testing.py` |
| where the readings still differ: division by zero | `src/lanky/semantics.py` |
| the Lean printer | `src/lanky/lean.py` |
| the oracles | `src/lanky/oracles/` |
| `check_path` and the CLI | `src/lanky/check.py`, `src/lanky/cli.py` |
| the pytential demonstration, and its rule engine | `examples/pytential_skie.py`, `examples/layer_potentials.py` |
