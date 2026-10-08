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

Files from different source roots, the directories a check puts on
`sys.path` (the file's own, and for a file in a package the one its package is
found from), are checked in processes of their own, one per root, because a
process imports a module of one name once: `lanky check a/claims.py
b/claims.py` checks each file against the `helpers.py` beside it. Files that
share their roots share a process, and `check_path` imports into the process
that calls it. A child runs with the interpreter options the command was
started with, as in `python -O -m lanky.cli check ...`, and ends with the
command.

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

set_option autoImplicit false in
theorem Lanky.scan_monotone (n : Int) (h0 : 0 ≤ n) (cnt : Int → Nat) (off : Int → Nat)
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

The first line keeps Lean from binding a name the theorem does not, at a
type it would pick: lanky declines a statement with such a name before Lean
sees it, and with `autoImplicit` off Lean would refuse one too, as an unknown
identifier.

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
1 either way. Lean is given `theorem Lanky.truncated (n : Int) (h0 : 0 ≤ n) :
n - 1 ≥ 0`, which is false at `n = 0` as the Python reading is, so no tactic closes it
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

The same with Lean and without it, since every statement has a sum in it
(Mathlib mode, below, proves `gauss` and `cubes`). Four things in that output
are new.

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
`rests_on`, `effective`, `effective_heuristic` and `under` for every fact, and
the exit code depends on none of them: it is 0 here, since nothing is refuted.

Copy the axiom down wrong, with `i**2` for `i**3` on the left, and the property
tester refutes it. The row reads `refuted (axiom)`, `cubes` is worth `refuted`
in the `EFFECTIVE` column, the counterexample is printed under the table, and
`lanky check` exits 1. So does an axiom whose hypotheses were copied down so
that nothing satisfies them, once Lean shows them inconsistent: it reads
`assumed (axiom) (vacuous)`, as a theorem would read `proved (vacuous)`.
`pytest examples/nicomachus.py` samples the axiom as a test item too.

A plugin's facts rest on facts the same way: it sets `rests_on` on the facts
it builds, naming other facts by id.

An id names a definition: `theorem:nicomachus.gauss@33` is the kind, the
module, the qualified name and the line. The module is the name the file's
path gives it under its source root, `nicomachus` for `examples/nicomachus.py`
and `pkg.helpers` for `root/pkg/helpers.py`, and not the name it was imported
under. So a theorem that `main.py` imports with `from helpers import lemma`
and names in `uses=` has the id there that it has in `helpers.py`'s own
ledger, `theorem:helpers.lemma@12` in both. `lanky check main.py helpers.py`
still gives each file its own ledger, so `main.py`'s names the id in an
`UNRESOLVED` line, and it is the id of the row in `helpers.py`'s ledger and in
the `--json` list. A plugin builds its ids with `lanky.ledger.fact_id(kind,
owner, module, line)`, and `lanky.check.module_name(path)` gives it the module
of the file a definition's code was compiled from; loopty keys every fact of a
kernel that way.

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
rules off their statements and applies nothing else about layer potentials;
of operators in general it uses only that compact ones form a linear space and
that the identity is not one of them.

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
- **A decline says why.** A claim outside the fragment is declined with the
  reason. Claim the second kind for the interior trace of `eta*D`:

  ```python
  @rules.second_kind
  def depends_on_eta():
      """Second kind only when eta is not 0."""
      return trace(eta * D, INTERIOR), -eta / 2 * I + eta * D
  ```

  The rewrite is decided, and the verdict, `-1/2*eta*I + eta*D is second
  kind`, reads `assumed`, as a claim no oracle knows does. Under the table
  `lanky check` prints `DECLINED depends_on_eta at` its place, with the reason
  the rules gave indented under it: `layer-rules: the identity coefficient
  -1/2*eta mentions eta, so the verdict depends on its value`. `declined` is
  a standard provenance key, read the same way whatever the plugin, and it
  does not change the exit code.
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

## Decide an identity with a computer algebra system

Between a sample and a proof there is a third kind of evidence: a computer
algebra system that simplifies the difference of two formulas to zero, which
is how a test of a numerical code usually checks an identity at a fixed size.
The `cas` extra installs sympy, and with it lanky's oracle `cas`, of the trust
class `heuristic`:

```sh
uv add "lanky[cas]"
```

It takes a statement that asserts equations, alone, in a conjunction or under
universals whose variables range over numbers, with sides built from
arithmetic, `abs`, `exp`, `log` and `sqrt`, and asks `sympy.simplify` for the
difference of the sides of each equation. When every one is `0`, the row
reads `decided (heuristic)  cas`: `exp(x + y) == exp(x) * exp(y)` over `Real`,
which the property tester tests and core Lean cannot state, is one. When one
is not, sympy may only have failed to find the identity, so the fact is
declined, with the difference in the reason, and the tester, which can refute
it, is asked next. A variable is a sympy symbol with what its sort grants, real
for `Real` and an integer that is not negative for `Nat` and `Fin[n]`, so
`sqrt(x**2) == abs(x)` is decided over `Real` and declined over `Complex`,
where it is false. A logarithm or a square root of a real argument is taken
only where sympy can show the argument is not negative: below zero sympy's
value is complex, where Python's `math` raises and Mathlib's is real, so
`sqrt(x)**2 == x` over `Real` is left to the tester, and over `Nat` decided.
The hypotheses are not read, since an identity that holds everywhere holds
wherever they do. And a fact sympy decided is sampled all the
same: a counterexample overrules it, as it overrules any heuristic.
`LANKY_CAS_DISABLE=1` turns the oracle off, and `LANKY_CAS_TIMEOUT` caps the
seconds sympy may take over one fact (60).

`examples/sumpy_recurrence.py` is the worked case, and a consumer of the kind
the pytential demonstration is. sumpy's `LinearPDEBasedExpansionTermsWrangler`
stores only the Taylor coefficients of a kernel that the kernel's PDE does not
determine, and reconstructs the rest by a recurrence: the 2-D Laplace kernel
`log r` is harmonic, so a derivative with two or more `x`'s is minus the one
with two `x`'s fewer and two `y`'s more. The claim is that every coefficient
through order 6 it reconstructs is the derivative it stands for. The
recurrence is read off the wrangler, which is handed a symbol for each stored
derivative and gives back each coefficient as a combination of them, so the
claim is about sumpy's code and not a transcription of it. sumpy, and sympy
and mpmath through it, are imported inside the file; none of them is a
dependency of lanky, and `uv pip install sumpy` puts sumpy in the environment.

```console
$ uv run python examples/sumpy_recurrence.py
sumpy's compressed Taylor wrangler for G = log(sqrt(x**2 + y**2)), the 2-D Laplace
kernel, stores 13 of the 28 derivatives through order 6 and reconstructs the rest:

(a, b)  reconstructed  direct derivative of G                                                             difference (sympy)  difference (mpmath)
------  -------------  ---------------------------------------------------------------------------------  ------------------  -------------------
(0, 0)  stored         log(x**2 + y**2)/2                                                                 0                   within 1e-20
(0, 1)  stored         y/(x**2 + y**2)                                                                    0                   within 1e-20
(1, 0)  stored         x/(x**2 + y**2)                                                                    0                   within 1e-20
(0, 2)  stored         (x - y)*(x + y)/(x**2 + y**2)**2                                                   0                   within 1e-20
(1, 1)  stored         -2*x*y/(x**2 + y**2)**2                                                            0                   within 1e-20
(2, 0)  -(0, 2)        -(x - y)*(x + y)/(x**2 + y**2)**2                                                  0                   within 1e-20
(0, 3)  stored         -2*y*(3*x**2 - y**2)/(x**2 + y**2)**3                                              0                   within 1e-20
(1, 2)  stored         -2*x*(x**2 - 3*y**2)/(x**2 + y**2)**3                                              0                   within 1e-20
(2, 1)  -(0, 3)        2*y*(3*x**2 - y**2)/(x**2 + y**2)**3                                               0                   within 1e-20
(3, 0)  -(1, 2)        2*x*(x**2 - 3*y**2)/(x**2 + y**2)**3                                               0                   within 1e-20
(0, 4)  stored         -6*(x**2 - 2*x*y - y**2)*(x**2 + 2*x*y - y**2)/(x**2 + y**2)**4                    0                   within 1e-20
(1, 3)  stored         24*x*y*(x - y)*(x + y)/(x**2 + y**2)**4                                            0                   within 1e-20
(2, 2)  -(0, 4)        6*(x**2 - 2*x*y - y**2)*(x**2 + 2*x*y - y**2)/(x**2 + y**2)**4                     0                   within 1e-20
(3, 1)  -(1, 3)        -24*x*y*(x - y)*(x + y)/(x**2 + y**2)**4                                           0                   within 1e-20
(4, 0)  (0, 4)         -6*(x**2 - 2*x*y - y**2)*(x**2 + 2*x*y - y**2)/(x**2 + y**2)**4                    0                   within 1e-20
(0, 5)  stored         24*y*(5*x**4 - 10*x**2*y**2 + y**4)/(x**2 + y**2)**5                               0                   within 1e-20
(1, 4)  stored         24*x*(x**4 - 10*x**2*y**2 + 5*y**4)/(x**2 + y**2)**5                               0                   within 1e-20
(2, 3)  -(0, 5)        -24*y*(5*x**4 - 10*x**2*y**2 + y**4)/(x**2 + y**2)**5                              0                   within 1e-20
(3, 2)  -(1, 4)        -24*x*(x**4 - 10*x**2*y**2 + 5*y**4)/(x**2 + y**2)**5                              0                   within 1e-20
(4, 1)  (0, 5)         24*y*(5*x**4 - 10*x**2*y**2 + y**4)/(x**2 + y**2)**5                               0                   within 1e-20
(5, 0)  (1, 4)         24*x*(x**4 - 10*x**2*y**2 + 5*y**4)/(x**2 + y**2)**5                               0                   within 1e-20
(0, 6)  stored         120*(x - y)*(x + y)*(x**2 - 4*x*y + y**2)*(x**2 + 4*x*y + y**2)/(x**2 + y**2)**6   0                   within 1e-20
(1, 5)  stored         -240*x*y*(x**2 - 3*y**2)*(3*x**2 - y**2)/(x**2 + y**2)**6                          0                   within 1e-20
(2, 4)  -(0, 6)        -120*(x - y)*(x + y)*(x**2 - 4*x*y + y**2)*(x**2 + 4*x*y + y**2)/(x**2 + y**2)**6  0                   within 1e-20
(3, 3)  -(1, 5)        240*x*y*(x**2 - 3*y**2)*(3*x**2 - y**2)/(x**2 + y**2)**6                           0                   within 1e-20
(4, 2)  (0, 6)         120*(x - y)*(x + y)*(x**2 - 4*x*y + y**2)*(x**2 + 4*x*y + y**2)/(x**2 + y**2)**6   0                   within 1e-20
(5, 1)  (1, 5)         -240*x*y*(x**2 - 3*y**2)*(3*x**2 - y**2)/(x**2 + y**2)**6                          0                   within 1e-20
(6, 0)  -(0, 6)        -120*(x - y)*(x + y)*(x**2 - 4*x*y + y**2)*(x**2 + 4*x*y + y**2)/(x**2 + y**2)**6  0                   within 1e-20

Every reconstructed coefficient is the direct derivative. sympy simplifies each
difference to 0, and mpmath's derivatives, at 30 digits, agree to within 1e-20
of each other, relative, at 20 points.

Through order 6 the wrangler follows the recurrence
reconstructed(a + 2, b) == -reconstructed(a, b + 2), which is the PDE sumpy
declares for the kernel, G_xx + G_yy == 0, solved for G_xx.

`lanky check examples/sumpy_recurrence.py` puts the claim in the ledger: tested by
mpmath, decided by the CAS oracle where sympy is installed, and proved for every
order by Lean where Mathlib is, under the kernel's harmonicity.
```

The ledger has the one claim three times, with the evidence for each, under the
kernel's harmonicity:

```console
$ uv run lanky check examples/sumpy_recurrence.py
STATUS                  BY      WHERE                    OWNER              STATEMENT
----------------------  ------  -----------------------  -----------------  ------------------------------------------------------------------------
assumed (axiom)         -       sumpy_recurrence.py:128  harmonic           x : Real, y : Real | x**2 + y**2 > 0 |- (1 - 2*x**2 / (x**2 + y**2)) ...
tested                  mpmath  sumpy_recurrence.py:712  compressed_taylor  at 20 points: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, ...
decided (heuristic)     cas     sumpy_recurrence.py:712  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- reconstructed(a, b) == diff(l...
assumed under harmonic  -       sumpy_recurrence.py:712  compressed_taylor  every order: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a...

4 facts: 2 assumed, 1 decided, 1 tested

CITED harmonic at sumpy_recurrence.py:128: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6
```

- **The harmonicity.** `harmonic` is an axiom: `G_xx + G_yy == 0` away from
  the origin, with the second derivatives sympy's, taken on its citation and
  sampled for a counterexample. It is the PDE the wrangler's recurrence comes
  from. The first two rows below do not rest on it, since each checks the
  reconstruction against the derivatives themselves, one order at a time; the
  third, the claim for every order, does.
- **The claim at points.** mpmath takes every derivative numerically, by
  finite differences at 30 digits, at 20 points away from the origin, and
  finds each reconstructed one within `1e-20` of the derivative it stands
  for. The oracle that does it, `mpmath`, of the trust class `test`, is the
  file's own, as a plugin's would be.
- **The claim as formulas.** One statement over real `x` and `y`, with
  `x**2 + y**2 > 0` as its hypothesis and an equation per coefficient, between
  the wrangler's combination of sympy's derivatives and sympy's derivative.
  The CAS oracle simplifies each of the 28 differences to `0`, and the
  property tester samples the statement afterwards and finds nothing against
  it. The two rows share the recurrence and no other computation.
- **Without the oracle**, `LANKY_CAS_DISABLE=1`, the second row reads
  `tested  property-test`: the tester evaluates the same 28 equations exactly,
  in rational arithmetic, at each of its draws.
- **The claim for every order.** Over two tables of reals indexed by `(a,
  b)`, the derivatives `D` and the reconstruction `R`: if `D` satisfies the
  PDE at every order, `D(a + 2)(b) + D(a)(b + 2) == 0`, and `R` is `D` where
  the wrangler stores (`a < 2`) and follows the recurrence `R(a + 2)(b) ==
  -R(a)(b + 2)` everywhere else, then `R` is `D`. The derivatives of `log r`
  at a point are such a `D`, by `harmonic`, which is why the row reads
  `under harmonic`, and the wrangler's reconstruction is such an `R`: the
  recurrence is read off the PDE sumpy declares for the kernel, as the
  wrangler reads it, and the wrangler's weights through order 6 are checked
  against it, as the Python run above says. Core Lean cannot state the row,
  since it is over the reals, and the tester cannot draw a table over `Nat`,
  so it is `assumed` here; Lean proves it with Mathlib (see
  [Prove it with Mathlib](#prove-it-with-mathlib)).
- **A wrong recurrence fails the check.** Flip the sign of one reconstructed
  coefficient in the wrangler and the first two rows are refuted: mpmath
  names the coefficient and the point, sympy declines with the difference it
  is left with, twice a stored derivative, and the tester finds a point of
  its own. `lanky check` exits 1. The third row is not there: the wrangler's
  weights no longer follow its PDE's recurrence, so it makes no claim for
  every order.

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
source, which would take hours. The project is wherever you put it; the cache
tool keeps what it downloads (about 400 MB, packed) in `MATHLIB_CACHE_DIR`,
by default `$XDG_CACHE_HOME/mathlib` or `~/.cache/mathlib`, and the REPL lanky
builds goes where `LANKY_LEAN_CACHE_DIR` says, as in core mode. Then:

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
the core attempts run first, with Mathlib's closing tactics added to theirs.
`gauss` is printed in the Mathlib dialect,

```text
theorem Lanky.gauss (n : Int) (h0 : 0 ≤ n) :
    2 * (∑ i ∈ Finset.Ico (0 : ℤ) (n + 1), i) = n * (n + 1)
```

where `Fin[n + 1]` is `Finset.Ico (0 : ℤ) (n + 1)`, so the binder is an
integer as a quantifier's is: the ascription keeps it one even when the bound
is a literal, which Lean would otherwise read as a `Nat`, where `i - 1`
truncates. Every Mathlib statement is declared in the `Lanky` namespace,
because Mathlib declares lemmas such as `mul_comm` at the root and a claim of
that name would otherwise be refused as already declared. The core attempts
fail, and so do Mathlib's whole-goal ones (`norm_num`, `positivity`, `ring`,
`field_simp`, `linarith`, `nlinarith`, and three that combine them with
`push_cast` and `simp`), and the last script is an induction on `n`, which the
ladder chose because `n` is a natural parameter that the bound of a sum
mentions: trade `n` for the natural it is, and in each case take the last term
off the sum, which leaves the induction hypothesis and a polynomial identity
for `linarith`. The provenance records the script, the Mathlib revision as
`lean_mathlib`, and the source as a file that replays it, starting with
`import Mathlib`. `--verbose` prints the project on the Lean oracle's line.

The same variable makes `examples/nicomachus.py` read `proved` for `gauss` and
`proved under nicomachus` for `cubes`, which the induction proves on its own.
It is still worth `assumed`, because `uses=` says what it rests on.

What the Mathlib dialect adds, in brief (`src/lanky/lean.py` has the whole
account):

- `Real` and `Complex` are `ℝ` and `ℂ`, and `lanky.exp`, `lanky.log` and
  `lanky.sqrt` are `Real.exp`, `Real.log` and `Real.sqrt`, and
  `Complex.exp`, `Complex.log` and `Complex.sqrt` of a complex argument. The
  complex `log` and `sqrt` are `cmath`'s principal branches off the branch
  cut, the non-positive real axis, and not on it: `cmath` picks a side of the
  cut by the sign of a zero imaginary part, and Lean's `ℂ` has no signed
  zero. So a statement that takes one comes with side conditions, that every
  argument stays off the cut, which Lean proves from the hypotheses and
  guards around it before it tries the statement; when it cannot, the
  statement is declined, and the reason names the side condition. With
  `y != 0` among the hypotheses, `sqrt(x + y * 1j) ** 2 == x + y * 1j` is
  proved, and `exp(log(z)) == z` over every nonzero `z` is declined. The
  tester reads them as `cmath`'s principal branches too, enclosed off the cut
  and undecided on it. At a number they are Python's `math` and `cmath`
  functions, so the file still runs.
- A float literal is the rational number Python holds, `(1 / 2 : ℝ)` for
  `0.5`, and true division is division in a field, `(x : ℝ) / y`, because
  Python's `/` does not divide integers as integers either.
- `abs(x)` is `|x|`, and `‖z‖` for a complex `z`, which is the modulus Python
  computes.
- An integer floor division next to a real is ascribed, `x + (n / 2 : ℤ)`:
  Lean casts every leaf of an arithmetic tree to the widest type in it, and
  without the ascription `n / 2` would divide the cast `n` in `ℝ`.

The property tester reads a real statement as Lean does, over `ℝ`. It draws
`Real` and `Complex` as fractions, whatever their exactness class, and
encloses `exp`, `log` and `sqrt` in intervals with rational endpoints where
their values are not rational, so `(x + 1) - 1 == x` holds exactly and
`exp(x + y) == exp(x) * exp(y)` holds to within enclosures that agree to far
more bits than a float has. Both are `tested` without Mathlib and `proved`
with it, and a real claim is `refuted` only at a draw where the enclosures
exclude it. An equality whose sides agree counts as holding only where the
statement asserts it; under a negation or in a hypothesis the agreement
decides nothing, and neither does an order the enclosures straddle. So
`exp(x) * exp(-x) <= 1` is decided only at `x = 0`, where the value is
rational, and the tester draws again in place of every draw it drops, so all
200 valid draws are there, out of some three thousand. The row reads
`tested`, and a `WARNING` under the table says that the pass rests on thin
evidence: how many draws decided nothing, that the valid ones are all at
`{'x': Fraction(0, 1)}`, and, on a line of its own, why one draw decided
nothing. A pass gets that warning whenever the draws it dropped outnumber
the ones it decided, or its decided draws take fewer than three distinct
assignments when the draws, decided or not, took more; the JSON has it as
the fact's `reason`. Where Lean's functions are total and Python's raise, the
fact carries a note in Mathlib mode, as `div_zero` does above: a true
division by something that may be zero, and a logarithm or square root of
something that may leave its Python domain.
`def neg(x: Real & (x < 0)) -> sqrt(x) == 0` is proved with Mathlib, whose
square root of a negative number is `0`, and no draw can evaluate it in Python.

### A claim for every order

With the same variable, the sumpy demonstration's third row is proved:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/sumpy_recurrence.py
STATUS                 EFFECTIVE            BY      WHERE                    OWNER              STATEMENT
---------------------  -------------------  ------  -----------------------  -----------------  ------------------------------------------------------------------------
assumed (axiom)        assumed              -       sumpy_recurrence.py:128  harmonic           x : Real, y : Real | x**2 + y**2 > 0 |- (1 - 2*x**2 / (x**2 + y**2)) ...
tested                 tested               mpmath  sumpy_recurrence.py:712  compressed_taylor  at 20 points: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, ...
decided (heuristic)    decided (heuristic)  cas     sumpy_recurrence.py:712  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- reconstructed(a, b) == diff(l...
proved under harmonic  assumed              lean    sumpy_recurrence.py:712  compressed_taylor  every order: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a...

4 facts: 1 assumed, 1 decided, 1 proved, 1 tested

CITED harmonic at sumpy_recurrence.py:128: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6
```

The claim is over two tables, `D` and `R` (see the
[demonstration](#decide-an-identity-with-a-computer-algebra-system)), and Lean
proves it by strong induction on `a`, with `b` free in the induction
hypothesis:

```text
theorem Lanky.compressed_taylor (D : Int → Int → ℝ) (R : Int → Int → ℝ)
    (h0 : ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → D (a + 2) b + D a (b + 2) = 0)
    (h1 : ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → a < 2 → R a b = D a b)
    (h2 : ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → R (a + 2) b = (-1) * R a (b + 2)) :
    ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → R a b = D a b := by
  intro a hd
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  clear hd
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b hd_1
    by_cases hbase : a < 2
    · linear_combination (norm := ...) h1 a (by omega) b (by omega) (by omega)
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, a = k + 2 := ⟨a - 2, by omega⟩
      linear_combination (norm := ...) h2 k (by omega) b (by omega)
        - h0 k (by omega) b (by omega) - ih k (by omega) (b + 2) (by omega)
```

(the `norm` is `ring`, after the casts are pushed down to the variables, with
`ring_nf` and `field_simp` to fall back on; it is spelled out as
`lanky.oracles.lean.COMBINATION_NORM`). Below the step, `a < 2`, the stored
coefficient is the derivative, by `h1`. At `a = k + 2`, the goal `R (k + 2) b
= D (k + 2) b` is the recurrence at `(k, b)`, less the PDE at `(k, b)`, less
the induction hypothesis at `(k, b + 2)`: `linear_combination` moves
everything to one side and `ring` checks that what is left is `0`. Lean does
not find that combination, and lanky does not ask it to. Python does
(`lanky.induction`): the applications of the families in the goal are atoms,
each hypothesis is instantiated where one of its applications is an atom, the
instances bring in atoms of their own, and once the goal is a combination of
the instances the multipliers solve a linear system over the rational
functions of the statement's other variables, with sympy (the `cas` extra).
Each use has to satisfy its hypothesis's guards, which the search reads as
affine inequalities, so the induction hypothesis is only ever used below the
order it is proving. Python searches, Lean checks: a wrong certificate is one
failed attempt, never a wrong proof.

The search is lanky's default certificate hook. A plugin that knows its
multipliers, from the coefficients of a PDE say, can hand them over with
`lanky.oracles.lean.use_certificate(claim, finder)`, where `finder` takes a
`lanky.induction.Case` and returns the uses of its lemmas. A multiplier can be
an expression: for Helmholtz's PDE, `D(a + 2)(b) + D(a)(b + 2) + k**2 *
D(a)(b) == 0`, the step also takes the induction hypothesis at `(k, b)`,
times `-k**2`; and a step that is a rational-function identity, such as
`f(n + 1) == f(n) + 1 / ((n + 1) * (n + 2))` with `f(n) == n / (n + 1)`, is
closed by `field_simp` and `ring`. The strategy is Mathlib's, since
`linear_combination` is, and it takes a goal that is a universal over
naturals whose body is an equation between applications of the statement's
families.

The CAS's row is the claim through order 6, and Lean is not asked about it:
the demonstration declines it for Lean
(`lanky.oracles.lean.decline(claim, reason)`), since Lean's row is the one
for every order, and the ladder spent minutes on 28 equations at once before
the CAS oracle decided them in a second. The check takes about a minute, most
of it importing Mathlib and asking Lean whether the third row's hypotheses
are inconsistent and its goal's domain empty, which they are not.

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
- Call one of Python's builtins in a claim. At numbers it is Python's:
  `def half() -> round(0.5) == 1` is `0 == 1`, answered while the annotation
  is read, and the row reads `refuted`, as running the file would say. At a
  variable it is refused where the theorem is defined, naming it:
  `def smaller(x: Real, y: Real) -> min(x, y) <= x` raises `TypeError`,
  `min(x, y) applies Python's min to a symbolic value`. lanky has no term for
  `min` yet, and the free name it used to be was read by Lean as Lean's own
  `min`. `def wrong(x: int) -> x - 1 >= 0` is refused too, naming `Int` and
  `Nat`: `int` is Python's type, and not a sort. So is `f: Fn[Fin[n], float]`,
  naming `Real`.
- Look a point up in a dict: `def looked_up(n: Nat, f: Fn[Fin[n], Nat]) ->
  all(f(i) * 0 == {0: 1}.get(i, 0) for i in Fin[n])`. A dict finds a key by
  its hash, and a term's hash is its structure's, so the lookup would answer
  `0`, as if `i` were never `0`, and the claim would be `f(i)*0 == 0`. A term
  is unhashable to an annotation's own code instead, so the theorem is
  refused where it is defined (`i was hashed by the annotation, as a dict or
  a set lookup or display there hashes its keys`), and so is `i in {0, 1}`.
  A table indexed by a point is a family, with hypotheses that give its
  values.
- Misspell a name: `def typo(n: Nat) -> n + m >= n`. No parameter binds `m`,
  so no draw gives it a value, and the tester draws nothing; Lean is not
  handed it either. The row reads `assumed`, and the tester says why under
  the table:

  ```text
  DECLINED typo at typo.py:7: n : Nat |- n + m >= n
    property-test: the statement mentions m, which no parameter or binder of it binds, so no draw gives it a value and the statement cannot be tested; a name misspelt, not imported, or meant as a parameter is the usual cause
  ```

  A misspelt sort, `f: Fn[Fin[n], Flaot]`, is named the same way. Under
  `pytest` such a theorem fails, naming the name.
- Choose a branch inside a quantifier: `all((f(i) if i < 3 else -1) >= 0 for
  i in Fin[n])`. The conditional asks `i < 3` for a truth value, which lanky
  has only where it records a guard, so it is refused where the theorem is
  defined, as `not` in a body and a comparison of two tuples are. A
  condition on the points goes in the generator's `if` clause, written with
  `&`, `|` and `~`.
- Make two claims from one definition, with a function that decorates a
  nested `def` each time it is called. A fact id names a definition, so both
  claims have one id; the first is checked and stays in the table, and
  `lanky check` names the others in a `DUPLICATE` block under it, unchecked,
  and exits 1. A factory that wants several claims gives each function a
  `__qualname__` of its own before it decorates it.
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
- A goal's own guard can be vacuous too. Flip the one in `scan_monotone`'s
  goal in `examples/gauss.py`, `if (a < b) & (a > b)` for `if a <= b`. The
  hypotheses still hold at every draw, and so does the goal, because its
  guard holds at no point, so nothing about the offsets is at stake. The
  property tester counts, per draw, whether the goal's quantifier got through
  its guard to a point, and when it never did, it says so. Without Lean the
  row reads `tested`, and under the table:

  ```text
  WARNING scan_monotone at gauss.py:39: the goal's guard a < b and a > b never held in 200 valid draws
    no oracle could show it empty, so the goal may be vacuous
  ```

  With Lean, `omega` proves the goal from its guard, and Lean is then asked
  whether the guard is empty wherever the hypotheses hold, which is the goal
  with its body replaced by `False`. It is, so the row reads
  `proved (vacuous)`, a `VACUOUS` block follows the table, and `lanky check`
  exits 1. A guard that is empty only for some values of the variables, as
  `Fin[n]` is at `n = 0`, gets through at some draw and is never flagged. A
  guard that holds only where the sampler does not look, such as `a == 7`, gets
  the warning with Lean too, since Lean cannot show it empty. Under `pytest`
  such a theorem is skipped, with the guard in the reason.
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
  sampled `all` is a counterexample wherever it stands. An undecided operand
  does not decide a connective, though: `~all(k < 100 for k in Nat) | (n >= 0)`
  reads `tested`, because `n >= 0` holds at every draw and a disjunction with
  a true operand is true, and it reads the same with the operands swapped.
  Nor does an undecided point decide a quantifier, whose points are a
  conjunction (`all`) or a disjunction (`any`):
  `all(~all(k < 100 for k in Nat) & (i < 1) for i in Fin[n + 2])` is refuted
  at `i = 1`, though its body has no answer at `i = 0`, as the same claim
  spelled out point by point is. A point whose guard has no answer, as
  `if 10 // i > 3` at `i = 0`, is settled by a body that holds there, for an
  `all`, or fails there, for an `any`, and is open otherwise.
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
| where the readings still differ: division by zero, `log`, `sqrt` | `src/lanky/semantics.py` |
| the Lean printer, core Lean's dialect and Mathlib's | `src/lanky/lean.py` |
| Mathlib mode: the pinned project and its setup | `src/lanky/mathlib.py`, `src/lanky/mathlib-project/` |
| induction over families: the search for a certificate, and the script Lean checks | `src/lanky/induction.py`, `src/lanky/oracles/lean.py` |
| the oracles | `src/lanky/oracles/` |
| `check_path` and the CLI | `src/lanky/check.py`, `src/lanky/cli.py` |
| the pytential demonstration, and its rule engine | `examples/pytential_skie.py`, `examples/layer_potentials.py` |
| the bridge to sympy, and the CAS oracle | `src/lanky/cas.py`, `src/lanky/oracles/cas.py` |
| the sumpy demonstration, and its `mpmath` oracle | `examples/sumpy_recurrence.py` |
