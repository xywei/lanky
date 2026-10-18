# Quickstart

One file, four commands, and the output each one prints. Then named
conditions, claims taken on a citation, a rule engine that checks a
derivation, the proofs lanky finds, and proofs you write in Python.
Everything below was run in this repository with `uv run`, the `lanky check`
tables last on 2026-10-18; the numbers and the Lean source are copied from the
terminal, not written from memory. The one thing that drifts
is a timing, which is a property of the machine and not of the claim. The
`lanky check` tables are held to more than that: the test suite compares them
with a real run, `gauss.py`'s as it stands where Lean is installed (CI has a
job for that) and with its `proved` row read as `tested` where it is not, and
the demonstration's the other way round. That holds for the files you are
asked to write as well: the suite writes `gap.py`, `misread.py`,
`upwind_step.py`, `between.py` and `table.py` from the snippets shown here,
and checks what each prints.

To use lanky in a project of your own, `pip install lanky`; the README's
[Install](../README.md#install) section has the extras, Lean and Mathlib. To
follow along here, clone the repository, which has the examples:

```sh
git clone https://github.com/xywei/lanky.git
cd lanky
uv sync --group dev              # add --extra lean for the Lean oracle, --extra cas for the CAS one
uv pip install sumpy             # for examples/line_taylor.py and examples/sumpy_recurrence.py
```

`examples/line_taylor.py` and `examples/sumpy_recurrence.py` check sumpy's own
code, so they import sumpy, which no extra installs; without it, `lanky
check` says so and names the command.

## The file

`examples/gauss.py` holds two claims. The first is Gauss's schoolboy sum:

```python
@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""
```

The second is the fact a sparse matrix layout needs:

```python
@claim
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
`if` clause becomes its guard, and `sum(...)` becomes a reduction. In an
annotation `all`, `any`, `sum` and `abs` are lanky's, so an annotation that
calls one of them in a module that binds the name to a function of its own,
as `from numpy import abs` does, is refused; call that one by another name,
`np.abs`. A file like this needs `from __future__ import annotations` so the
annotations are not evaluated by Python first.

The bodies are docstrings, so these claims have no proof written out, and
lanky's strategies try to prove them. A body can also be the proof, written
in Python ([Write a proof](#write-a-proof)). Importing or running the file
never runs a proof.

Notice that `off` is a parameter and not a return value. That is deliberate and
it is the same convention a kernel uses: a kernel writes its output into an array
its caller allocated, so the claim about the output is a claim about a parameter.
That is what lets this claim be the postcondition of a kernel somewhere else.

## Run it as a program

```console
$ uv run python examples/gauss.py
gauss at n = 4: True
scan_monotone at n = 3: True

gauss: n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
  ok after 50 valid draws of 50

scan_monotone: n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat] | off(0) == 0, forall r in Fin(n). off(r + 1) == off(r) + cnt(r) |- forall a in Fin(n + 1), b in Fin(n + 1) where a <= b. off(a) <= off(b)
  ok after 50 valid draws of 50
```

A claim is callable: `gauss(n=4)`, or `gauss(4)`, answers whether it holds
at those values, `True` or `False`. Where one of a claim's conditions fails
at the values, the question does not apply, and the call raises
`lanky.ConditionNotMet`, naming the condition. Calling a claim never runs
its proof. `.report(n=50)` samples. Both evaluate the term lanky built from
the annotations, and neither checks that the term is what the annotations
say; `lanky check` and `pytest` do, as
[Check the reading](#check-the-reading) shows
([#96](https://github.com/xywei/lanky/issues/96)).

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
claim in a collected module becomes a test item.

## Check it

```console
$ uv run lanky check examples/gauss.py
STATUS  EFFECTIVE  BY             WHERE        OWNER          STATEMENT
------  ---------  -------------  -----------  -------------  -------------------------------------------------------------------------
tested  tested     property-test  gauss.py:31  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
tested  tested     python         gauss.py:31  gauss          the term computes what the annotations compute
proved  tested     lean           gauss.py:39  scan_monotone  n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat]
                                                              | h0: off(0) == 0
                                                              | hs: forall r in Fin(n). off(r + 1) == off(r) + cnt(r)
                                                              |- forall a in Fin(n + 1), b in Fin(n + 1) where a <= b. off(a) <= off(b)
tested  tested     python         gauss.py:39  scan_monotone  the term computes what the annotations compute

4 facts: 1 proved, 3 tested

WITHOUT MATHLIB: gauss is not proved, since only Lean with Mathlib can state it. To have Lean prove it: python -m lanky.mathlib ~/mathlib (about 7 GB), then export LANKY_LEAN_MATHLIB=~/mathlib.
```

This is the command the project exists for. It imported the file, read the
registry the decorators filled, turned each claim into a `Fact`, and offered
each fact to the oracles strongest first. Each claim is two rows: the claim,
and under it its reading, which [Check the reading](#check-the-reading) below
is about.

The table holds the claims defined in `gauss.py` itself. A claim the file
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

The two claims differ, and the difference is the product.

- `scan_monotone` is `proved` by `lean`. The Lean oracle printed the statement as
  core Lean 4, found a tactic script, and elaborated the whole declaration in a
  fresh environment. There is no Mathlib anywhere in this.
- `gauss` is `tested` by `property-test`. Its reduction needs `Finset`, which
  needs Mathlib, so the Lean printer declines the term and the next oracle down
  takes it. In Mathlib mode Lean proves it too; see
  [Prove it with Mathlib](#prove-it-with-mathlib).
- Under each claim, `tested python` is its reading: the term every oracle is
  handed is what lanky's run of the annotations on symbolic terms built, and
  the annotations, run again as plain Python at drawn values, computed what
  the term computes at every draw. A proof is of the term, so it rests on its
  reading, and the `EFFECTIVE` column says what it is worth: `proved`,
  worth `tested`.

Without the Lean extra installed, or with `LANKY_LEAN_DISABLE=1`, both claims
read `tested property-test`, the `EFFECTIVE` column is not printed, since
nothing is then worth less than its own status, and the exit code is 0 either
way. Nothing about the code changes; only the strength of the evidence does,
and the table says which.

What a row lacks to be proved here is said under the table, a line for each
piece that is missing, with the rows that need it and the command that
installs it. Core Lean cannot state Gauss's sum, so the `WITHOUT MATHLIB`
line above names `gauss`. On a machine without Lean, or with
`LANKY_LEAN_DISABLE=1`, the check also prints, above it,

```text
WITHOUT LEAN: gauss and scan_monotone are not proved. To have Lean prove what it can: pip install "lanky[lean]", and Lean v4.29.1 from elan (elan default leanprover/lean4:v4.29.1).
```

and where Mathlib is set up but sympy is not, an induction over families,
whose steps sympy finds, gets a `WITHOUT SYMPY` line that names the `cas`
extra. A Lean that is installed and cannot be started has no command to
give: its line names the reason instead, as `--verbose` does below.

A statement too long for its column is printed whole, on the lines under its
row: a claim a part to a line, its variables, each hypothesis under the
name of its parameter, and `|-` before the goal, as `scan_monotone`'s is
above; any other statement wrapped outside the brackets where it can be, and
indented under a bracket where it cannot.

`--verbose` prints the oracles and their availability first:

```console
$ uv run lanky check examples/gauss.py --verbose
lean (kernel): available (untested until the first fact: the REPL is built on demand, Lean v4.29.1)
property-test (test): available
...
```

The parenthetical is the honest part. What was checked is cheap: `lean` is on
`PATH` and the driver imports. The Lean named is the one the REPL will run,
`LANKY_LEAN_VERSION` when it pins one and else the `lean` on `PATH`; with
Mathlib it is the project's toolchain, and the line names the Mathlib too
(`Lean v4.29.1, with Mathlib v4.29.1 from /home/you/mathlib`). Whether a REPL
can actually be built is found out on the first fact and then remembered, so
after anything has been attempted the line names the Lean version in use
instead.

On a machine with no Lean it reads
`lean (kernel): unavailable: lean_interact is not installed (pip install "lanky[lean]")`,
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
theorem Lanky.scan_monotone (n : Int) (h0_1 : 0 ≤ n) (cnt : Int → Nat) (off : Int → Nat)
    (h0 : (off 0 : Int) = 0)
    (hs : ∀ r : Int, 0 ≤ r → r < n → (off (r + 1) : Int) = (off r : Int) + (cnt r : Int)) :
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
    first | (have hstep := hs k (by omega) (by omega)) | skip
    by_cases hlt : (k : Int) < a
    ...

set_option autoImplicit false in
theorem Lanky.scan_monotone.as_cited :
    ∀ n : Int, 0 ≤ n → ∀ cnt : Int → Nat, ∀ off : Int → Nat, (off 0 : Int) = 0 →
      (∀ r : Int, 0 ≤ r → r < n → ...) → ∀ a : Int, ... → (off a : Int) ≤ (off b : Int) :=
  Lanky.scan_monotone

#print axioms _root_.Lanky.scan_monotone
#print axioms _root_.Lanky.scan_monotone.as_cited
```

The first line keeps Lean from binding a name the theorem does not, at a
type it would pick: lanky declines a statement with such a name before Lean
sees it, and with `autoImplicit` off Lean would refuse one too, as an unknown
identifier.

The hypotheses have the names the file gives them, `h0` and `hs`, so the
script cites `hs k` where the file says `hs`. The ones lanky adds, the `0 ≤
n` that makes `n` a natural, take a name no parameter has, here `h0_1`. A
hypothesis written `p & q` is two, `name_1` and `name_2`.

The command proves two more things. `Lanky.scan_monotone.as_cited` is the
claim as one proposition, proved from the theorem: a proof or a kernel that
cites `scan_monotone` restates exactly that text, which Lean has proved, and
never prints the claim again. And the last lines are an axiom audit. A claim
reads proved only when Lean answers it, once for each theorem and about that
theorem, with nothing beyond `propext`, `Classical.choice` and `Quot.sound`:
a proof resting on `sorry`, or on `native_decide`, which trusts the compiler,
is not a proof, and neither is a command that stopped Lean before the audit,
or declared the theorem somewhere else (`lanky.audit`).

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
way it records a found one. The script is the proof that follows `:= by`, and
lanky writes every command around it, so a script with a `#` command such as
`#exit`, `set_option`, `native_decide`, a `namespace` or a declaration is never
sent to Lean. Importing the file still works, as `python` needs it to;
`lanky check` reads the claim as the other oracles leave it, names the script
under the table with what was found and what to write instead, and fails:

```text
REFUSED scan_monotone at gauss.py:39: the script use_tactic gives it is not sent to Lean, since it has #exit, a Lean command.
  Fix: take #exit out; lanky writes every command around the script, and lanky check --show-lean prints them.
```

The same source is one flag away without the JSON: `lanky check
examples/gauss.py --show-lean` prints, after everything else, the Lean of every
row that has some, the file that replays a proof and the statement of a claim
Lean did not prove, and `--show-lean scan_monotone` only the rows whose owner,
id or statement contains `scan_monotone`. The table itself never shows Lean.

A plugin's claims go through the same oracle. loopty states each fact isl
decides about a kernel as lanky terms, in parts (one per dependence class of a
loop transformation, say), with what isl found as hints, which Lean checks and
does not trust; a fact whose parts Lean proves reads `proved lean`, a line
under the table says how many of isl's facts Lean proved and how, and one Lean
did not prove keeps `decided`, with a `NOT PROVED` line naming the part and
why. `lanky.obligations` has the details.

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
@claim
def truncated(n: Nat) -> n - 1 >= 0:
    """False at n = 0, and false in Lean too."""
```

```console
$ uv run lanky check gap.py
STATUS   BY             WHERE     OWNER      STATEMENT
-------  -------------  --------  ---------  ----------------------------------------------
refuted  property-test  gap.py:7  truncated  n : Nat |- n - 1 >= 0
tested   python         gap.py:7  truncated  the term computes what the annotations compute

2 facts: 1 refuted, 1 tested

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
`truncated`, and with Lean the row reads `proved` by `lean`, worth its
`tested` reading, with this under the table:

```text
SEMANTICS div_zero at gap.py:7: no draw could decide the statement: the statement divides by zero at this draw, which Python raises on and Lean's total integer division does not, so the two readings differ here rather than the statement being false
  division or remainder by a divisor that is not a nonzero literal: Lean's integer division is total (Int.fdiv x 0 is 0 and Int.fmod x 0 is x) while Python raises ZeroDivisionError, so the sampled reading cannot answer where Lean can
```

(two lines in the terminal, each wrapped by your pager rather than by lanky.)
The sampled reading is not a counterexample there, and it is not agreement
either: it is a reading that could not be run, which is worth saying. Without
Lean the row is `assumed`, and the exit code is 0 both ways, because nothing
was refuted. `lanky.semantics.notes(term)` is the check. The reading is
`tested` both ways: run again as Python, the annotation raises
`ZeroDivisionError` at every draw, and so does its term, and two readings
with no value at a point for one reason agree there.

## Check the reading

An annotation is Python, and lanky reads it by running it on symbolic terms:
`==` builds a proposition, `all(...)` a quantifier, `f(i)` an application.
Most of Python goes through a term's overloads and builds more of the term.
Some of it answers from the term object instead, the same at every value the
term stands for, and then the term every oracle is handed says something else
than what was written: `is`, an attribute, a hash, a text, a number's truth
value, a comparison of two types, in the annotation or in a function or a
library it calls. lanky refuses the cases it can see while it reads, and
checks the rest by their results. Put this in `misread.py`, with the same two
imports:

```python
def table(i):
    return {0: 1}.get(i, 0)


@claim
def looked_up(n: Nat, f: Fn[Fin[n], Nat]) -> all(f(i) * 0 == table(i) for i in Fin[n]):
    """False at i = 0, where the table gives 1."""
```

```console
$ uv run lanky check misread.py
STATUS                            EFFECTIVE  BY      WHERE          OWNER      STATEMENT
--------------------------------  ---------  ------  -------------  ---------  ---------------------------------------------------------------
assumed under faithful:looked_up  refuted    -       misread.py:11  looked_up  n : Nat, f : Fn[Fin(n), Nat] |- forall i in Fin(n). f(i)*0 == 0
refuted                           refuted    python  misread.py:11  looked_up  the term computes what the annotations compute

2 facts: 1 assumed, 1 refuted

REFUTED looked_up at misread.py:11: the term computes what the annotations compute
  counterexample: {'n': 1, 'f': [1]}
  witness: the goal, all(f(i) * 0 == table(i) for i in Fin[n])
  the goal, run again as Python at these values, computes False, and its term, forall i in Fin(n). f(i)*0 == 0, computes True: the term says something else than what was written, so no oracle that decides or proves is asked about the claim
```

While the annotation is read, `i` is a term, the dict has no key it hashes
to, and `table(i)` is `0`, so the term is `f(i)*0 == 0`, which Lean proves
with `omega`. Each claim also gets a fact of kind `faithful`, its reading:
the annotations are run again as plain Python at drawn values, the term is
evaluated at the same values, and the two have to agree. At `n = 1`,
`table(0)` is `1`, and the goal is false where its term is true. So the
reading is refuted, with the draw, the annotation as written and both
answers; the claim is offered to no oracle, Lean included, and stays
`assumed` under its refuted reading, worth `refuted`; and `lanky check` exits
1. That is the output with Lean and without it. `pytest misread.py` fails the
claim with the same draw.

- **The draws.** Six of small values and domain ends come first, every
  natural the tester draws and a domain's first and last points, smallest
  first, so a refutation names a small point; then one at each integer
  written in the claim, or in a helper it calls, and next to it, so that a
  helper that answers otherwise only at `1000` is reached there; then 32 of
  the property tester's, with a definitional hypothesis satisfied by
  construction, as the tester satisfies it. The readings are compared whether
  or not a draw satisfies the hypotheses. A bounded quantifier is enumerated,
  as Python enumerates it, and one over a sort, `for k in Nat`, runs over a
  sample of about five of its values and the integers the claim writes, the
  same on both sides. A family over a sort, `Fn[Nat, Real]`, which the tester
  cannot tabulate, is drawn at each point as either reading applies it.
- **The module as it was.** The annotations run again in a copy of what
  they reach, taken just before the claim was read: the names they read, the
  functions of this module and of the modules beside it that they call, and
  the tables, lists and arrays those read and close over. So a
  `TABLE.clear()` after the claim does not change what `table(0)` gives the
  rerun, and each draw starts from that copy, whatever a helper changed at
  the draw before. What the copy cannot hold as it was, an object of a class
  of yours, a class that holds methods or data, a structure past the budget,
  leaves the reading `assumed`, naming it.
- **Agreement.** The same truth value, or the same value, for every
  annotation: the goal, each hypothesis and each variable's sort. A truth
  value against a number disagrees, and so does an exception on one side
  only, whatever it is: `i.name` raising at a number where its term has a
  value, or `1 // i` leaving Python with no answer at `i = 0` where the term
  has one. Where both have no answer for one reason, a family applied outside
  its domain or a division by zero, they agree, and the draw is read again
  with what Python has no value for read as Lean has it, `x // 0` as `0` say,
  so that what Python would have evaluated after it is compared too. `~`,
  `&` and `|` of truth values are lanky's `not`, `and` and `or` there too, and
  not Python's `~True`, which is `-2`, and they and the quantifiers are read
  three-valued on both sides, as lanky reads them: an operand or a point with no answer,
  whatever was raised, is passed over, and one after it that settles the
  whole settles it. So `(i == 0) | (f(i - 1) <= f(i))` is true at `i = 0`,
  and a misreading at `i = 1` is compared even where both readings have no
  answer at `i = 0`, where Python's `all` would stop. The two readings make
  the same operations in the same order, a sum included, so nothing is put
  down to rounding.
- **What rests on it.** Every pass, decision and proof of a claim rests on
  its reading, which is why `scan_monotone`'s proof above is worth `tested`.
  A reading that cannot be run at a point is `assumed`, with the reason: a
  variable of a sort no value can be drawn of, an annotation Python evaluated
  when the function was defined, without `from __future__ import
  annotations`, one that had no answer on both sides at any draw, or one that
  reaches what the copy could not hold as it was. A proof
  of such a claim reads `proved under faithful:name`, worth `assumed`, and a
  `DECLINED` line under the table gives the reason.
- **It is sampled.** A disagreement only at a point no draw reaches escapes
  it, as a counterexample no draw reaches escapes the tester. A draw whose
  readings take more than five seconds is given up, and a helper is stopped
  there; past four such draws of a claim, the check makes no more, and the
  reading is `assumed`. One step Python takes in C, `sum(range(10 ** n))`
  inside a helper, and a library's own code are not stopped, and run to
  their end ([#108](https://github.com/xywei/lanky/issues/108)).

## Name a condition

Results often share their conditions, and engineers give those conditions a
name: the CFL condition, an expansion point that is not zero, a conforming
mesh. lanky has a word for one, `@condition`. It is stated once, and the
claims that hold under it are written in a `with` block. You find one the
way you fix a failing test: red, then green.

### Red, then green

One step of the upwind scheme for `u_t + c u_x = 0` moves each value toward
its upwind neighbour by the Courant number `nu`, which is `c * dt / h`. Put
this in `upwind_step.py`:

```python
from __future__ import annotations

from lanky import claim, condition
from lanky.prelude import Real


@condition
def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
    """The CFL condition: the Courant number is between 0 and 1."""


@claim
def upwind_bounded() -> all(
    abs(u0 - nu * (u0 - u1)) <= max(abs(u0), abs(u1))
    for nu in Real for u0 in Real for u1 in Real
):
    """One upwind step does not grow the solution."""
```

`cfl` is a condition: a typed variable, a named condition on it and a
docstring, with no goal and no body. `upwind_bounded` is a claim with no
proof. It says that one step is never larger than the larger of the two
values it mixes, whatever the Courant number. That is false, and the check
shows where:

```console
$ uv run lanky check upwind_step.py
STATUS   BY             WHERE              OWNER           STATEMENT
-------  -------------  -----------------  --------------  ------------------------------------------------------------------------------------------
tested   property-test  upwind_step.py:7   cfl             can hold: nu : Real | nu >= 0 and nu <= 1
refuted  property-test  upwind_step.py:12  upwind_bounded  forall nu in Real, u0 in Real, u1 in Real. abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))
tested   python         upwind_step.py:12  upwind_bounded  the term computes what the annotations compute

3 facts: 1 refuted, 2 tested

REFUTED upwind_bounded at upwind_step.py:12: forall nu in Real, u0 in Real, u1 in Real. abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))
  counterexample: {'nu': Fraction(-7, 3), 'u0': Fraction(2, 1), 'u1': Fraction(1, 4)}
  the goal is false at this assignment
  The condition cfl in this file excludes every failing draw: put the claim under with cfl as (nu, stable).
```

The claim is red, as a failing test is, and `lanky check` exits 1. At
`nu = -7/3` the step runs against the wind and the value grows. The last
line is the one to read. lanky tried each `@condition` in the file on the
draws that failed: `cfl` is false at every one of them, and true at a draw
that passed. So put the claim under it, as the line says, and take `nu` out
of the claim's own `for`, since the condition binds it now:

```python
with cfl as (nu, stable):

    @claim
    def upwind_bounded() -> all(
        abs(u0 - nu * (u0 - u1)) <= max(abs(u0), abs(u1)) for u0 in Real for u1 in Real
    ):
        """One upwind step does not grow the solution."""
```

```console
$ uv run lanky check upwind_step.py
STATUS  BY             WHERE              OWNER           STATEMENT
------  -------------  -----------------  --------------  --------------------------------------------------------------------------------------------------
tested  property-test  upwind_step.py:7   cfl             can hold: nu : Real | nu >= 0 and nu <= 1
tested  property-test  upwind_step.py:14  upwind_bounded  under cfl (stable): forall u0 in Real, u1 in Real. abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))
tested  python         upwind_step.py:14  upwind_bounded  the term computes what the annotations compute

3 facts: 3 tested
```

Read it aloud: *"Assume the CFL condition: nu is between 0 and 1. Then one
upwind step is never larger than the larger of the two values."* The claim
is green: it held at every draw, and `lanky check` exits 0. The table reads
the same with Lean and without it; under it, a `WITHOUT MATHLIB` line says
that Lean needs Mathlib to state a claim about real numbers. With Mathlib,
lanky's strategies find no proof alone, and say what might help:

```text
NOT PROVED upwind_bounded at upwind_step.py:14: under cfl (stable): forall u0 in Real, u1 in Real. abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))
  Lean found no proof alone. What lanky knows of its shape:
    abs_of_negative rewrites abs(x); here abs(u0 - nu*(u0 - u1)), at x = u0 - nu*(u0 - u1)
    abs_of_positive rewrites abs(x); here abs(u0 - nu*(u0 - u1)), at x = u0 - nu*(u0 - u1)
    triangle_inequality bounds abs(x + y) from above; here abs(u0 - nu*(u0 - u1)), at x = u0, y = -nu*(u0 - u1)
  A proof cites them by name: from lanky.known import abs_of_negative, abs_of_positive, triangle_inequality
```

A written proof starts from there ([Write a proof](#write-a-proof)).

That is the whole loop. A claim that fails at its draws is a red test, with
the values that fail it, and lanky names any condition in the file that rules
those values out. Adding the condition makes the claim green. A proof, yours
or one lanky's strategies find, makes it proved.

### What `with` does

- `with cfl as (nu, stable):` binds every name in `cfl`'s signature, in
  order: its variables and its named conditions. Another count, or another
  name, is refused, and the message shows the signature.
- Every claim defined in the block holds under the condition. Its statement
  is the condition's variables and conditions, then its own, and its row in
  the ledger says so first: `under cfl (stable): ...`. A row that cites the
  claim says `under cfl`.
- The condition has a row of its own, `can hold: ...`, which checks by draws
  that its conditions can hold at all. A condition is assumed, not claimed,
  so this row is never `proved`. A condition that can never hold is
  `vacuous`, and fails the check.
- A `with` block is not a Python scope. The claims in it keep their
  module-level names, and are cited, called and tested by those names.
- A claim in the block that declares a bound name as its own parameter is
  refused. So is a claim after the block that still uses one: `nu belongs to
  cfl; use it inside with cfl as (nu, stable):`.
- Several conditions compose: in one `with` statement, `with cfl as (...),
  mesh as (...):`, or in Python's parenthesized form over several lines, or
  one `with` inside another. A variable that two conditions both declare,
  with one sort, is one variable.

### Three things to assume

`with` assumes one of three things:

| You write | It assumes |
|---|---|
| `with cfl as (nu, stable):` | a condition |
| `with between.conditions as (u0, u1, rising):` | another claim's conditions, without its goal |
| `with between as (u0, u1, rising):` | a whole claim, its goal included |

Put this in `between.py`:

```python
from __future__ import annotations

from lanky import claim, condition
from lanky.prelude import Real


@condition
def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
    """The CFL condition: the Courant number is between 0 and 1."""


with cfl as (nu, stable):

    @claim
    def between(u0: Real, u1: Real, rising: u0 <= u1) -> (
        (u0 <= u0 - nu * (u0 - u1)) & (u0 - nu * (u0 - u1) <= u1)
    ):
        """With u0 <= u1, one upwind step lands between them."""


with cfl as (nu, stable), between.conditions as (u0, u1, rising):

    @claim
    def no_overshoot() -> u0 - nu * (u0 - u1) <= u1:
        """Under the same conditions, the step does not pass its upwind neighbour."""


with cfl as (nu, stable), between as (u0, u1, rising):

    @claim
    def bounded() -> abs(u0 - nu * (u0 - u1)) <= max(abs(u0), abs(u1)):
        """Given that it lands between them, the step is no larger than either."""
```

```console
$ uv run lanky check between.py
STATUS  BY             WHERE          OWNER         STATEMENT
------  -------------  -------------  ------------  ----------------------------------------------------------------------------
tested  property-test  between.py:7   cfl           can hold: nu : Real | nu >= 0 and nu <= 1
tested  property-test  between.py:14  between       under cfl (stable): u0 : Real, u1 : Real
                                                    | rising: u0 <= u1
                                                    |- u0 <= u0 - nu*(u0 - u1) and u0 - nu*(u0 - u1) <= u1
tested  python         between.py:14  between       the term computes what the annotations compute
tested  property-test  between.py:23  no_overshoot  under cfl (stable), between.conditions (rising): u0 - nu*(u0 - u1) <= u1
tested  python         between.py:23  no_overshoot  the term computes what the annotations compute
tested  property-test  between.py:30  bounded       under cfl (stable), between: abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))
tested  python         between.py:30  bounded       the term computes what the annotations compute

7 facts: 7 tested
```

- `no_overshoot` holds under the same conditions as `between`: `between`'s
  own `rising`, and `cfl`, which `between` holds under. Its `with` names
  `cfl` too, because `between`'s conditions only make sense where `cfl` is
  in force. Leave `cfl` out and lanky refuses the block, with the line to
  write: *"with between.conditions as (u0, u1, rising): assumes between,
  which holds under cfl, and cfl is not in force here; write with cfl as
  (nu, stable), between.conditions as (u0, u1, rising):"*.
- `bounded` assumes `between` whole, its goal included, so a proof of
  `bounded` can cite `between` by name. A claim built on another rests on
  it: its row reads `under ... between`, and it is worth no more than
  `between` is. Nothing built on an unproved claim passes for proved.

### Two claims under one condition

In loopty's `examples/layer_potential.py`, the series of a logarithm and of
a reciprocal share their expansion point `alpha`, which must not be zero.
That is a condition, and both claims hold under it:

```python
@condition
def away_from_zero(alpha: Complex, beta: Complex, nonzero: alpha != 0):
    """The expansion point alpha is not zero."""


with away_from_zero as (alpha, beta, nonzero):

    @claim
    def line_taylor(
        a: Fn[Nat, Complex],
        first_term: alpha * a[1] == beta,
        ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
    ) -> all(a[n] == coefficient(-beta / alpha, n) for n in Nat if n >= 1):
        """The Taylor coefficients of log(alpha + tau * beta), from the ODE they satisfy."""
        for n in line_taylor.conclusion.domain:
            if n == 1:
                yield by(first_term)
            else:
                assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode[n - 1])
                yield by(line_taylor.conclusion[n - 1])

    @claim
    def reciprocal_taylor(
        b: Fn[Nat, Complex],
        first_term: b[0] == 1,
        ode: all(alpha * b[n + 1] + beta * b[n] == 0 for n in Nat),
    ) -> all(b[n] == (-beta / alpha) ** n for n in Nat):
        """The Taylor coefficients of alpha / (alpha + tau * beta)."""
        for n in reciprocal_taylor.conclusion.domain:
            if n == 0:
                yield by(first_term)
            else:
                assert b[n] == (-beta / alpha) * b[n - 1], by(ode[n - 1])
                yield by(reciprocal_taylor.conclusion[n - 1])
```

Read aloud: *"Assume alpha is not zero. line_taylor: for each n, in order.
At n = 1, by the first term. Otherwise the ODE at n − 1 gives a[n] from
a[n − 1], and it holds by line_taylor at n − 1."* `coefficient(r, n)` is a
helper in the file, `-(r ** n) / n`. The bodies are proofs, which
[Write a proof](#write-a-proof) explains. Put in a file of their own,
`taylor.py`, with the imports and the helper, and checked with Mathlib, each
row names the condition first, and its last line says how the proof went:

```text
proved  tested     lean           taylor.py:19  line_taylor        under away_from_zero (nonzero): a : Fn[Nat, Complex]
                                                                   | first_term: alpha*a[1] == beta
                                                                   | ode: forall n in Nat where n >= 1. (n + 1)*alpha*a[n + 1] + n*beta*a[n] == 0
                                                                   |- forall n in Nat where n >= 1. a[n] == -(-beta / alpha)**n / n
                                                                   by its proof, taylor.py:26-31: induction on n, 2 cases, 3 steps
...
proved  tested     lean           taylor.py:33  reciprocal_taylor  under away_from_zero (nonzero): b : Fn[Nat, Complex]
                                                                   | first_term: b[0] == 1
                                                                   | ode: forall n in Nat. alpha*b[n + 1] + beta*b[n] == 0
                                                                   |- forall n in Nat. b[n] == (-beta / alpha)**n
                                                                   by its proof, taylor.py:40-45: induction on n, 2 cases, 3 steps
```

A claim elsewhere that cites `line_taylor` reads `under away_from_zero`, so
the condition is never lost on the way.

### A condition in the scheme's own variables

`examples/upwind.py` states the CFL condition in the scheme's own variables,
the wave speed `c`, the time step `dt` and the mesh width `h`, and claims two
things under it:

```python
@condition
def cfl(
    c: Real,
    dt: Real,
    h: Real,
    forward: c >= 0,
    positive: (dt > 0) & (h > 0),
    stable: c * dt <= h,
):
    """The CFL condition of the upwind scheme for u_t + c u_x = 0, with c >= 0."""


with cfl as (c, dt, h, forward, positive, stable):

    @claim
    def courant() -> c * dt / h <= 1:
        """Under the CFL condition, the Courant number is at most one."""

    @claim
    def no_new_extremum(u_left: Real, u: Real, rising: u_left <= u) -> (
        (u_left <= u - c * dt / h * (u - u_left)) & (u - c * dt / h * (u - u_left) <= u)
    ):
        """An upwind step keeps each value between its old value and its upwind neighbour."""


@claim
def courant_number(ok: cfl(c, dt, h)) -> 0 <= c * dt / h:
    """Wherever the CFL condition holds, the Courant number is not negative either."""
```

Read it aloud: *"The CFL condition is c, dt and h with c not negative, dt
and h positive, and c dt at most h. Under it, the Courant number is at most
one, and an upwind step makes no new extremum."*

Parentheses give a claim or a condition for inputs. Called at numbers, a
condition says whether it holds, and so does a claim. A claim under a
condition takes the condition's variables like its own: with `dt` and `h`
the fractions `1/10` and `1/5`, `courant(c=1, dt=dt, h=h)` is `True`. Where
one of its conditions fails, the question does not apply, and the call says
so instead of answering: `courant(c=3, dt=dt, h=h)` raises
`lanky.ConditionNotMet`, *"courant does not apply at these values: its
condition stable of cfl, c*dt <= h, fails there"*. Calling a claim never
runs its proof. In an annotation, a condition called at symbolic values is
the proposition, as `ok: cfl(c, dt, h)` is in `courant_number`, where it
also gives `c`, `dt` and `h` their sorts.

```console
$ uv run python examples/upwind.py
cfl(c=1, dt=1/10, h=1/5) = True
cfl(c=3, dt=1/10, h=1/5) = False
courant at them: True
no_new_extremum at u_left = 0, u = 1: True
```

The ledger names the condition before each claim's own variables and
hypotheses, as the file does:

```console
$ uv run lanky check examples/upwind.py
STATUS  BY             WHERE         OWNER            STATEMENT
------  -------------  ------------  ---------------  -----------------------------------------------------------------------------
tested  property-test  upwind.py:33  cfl              can hold: c : Real, dt : Real, h : Real | c >= 0, dt > 0 and h > 0, c*dt <= h
tested  property-test  upwind.py:47  courant          under cfl (forward, positive, stable): c*dt / h <= 1
tested  python         upwind.py:47  courant          the term computes what the annotations compute
tested  property-test  upwind.py:51  no_new_extremum  under cfl (forward, positive, stable): u_left : Real, u : Real
                                                      | rising: u_left <= u
                                                      |- u_left <= u - c*dt / h*(u - u_left) and u - c*dt / h*(u - u_left) <= u
tested  python         upwind.py:51  no_new_extremum  the term computes what the annotations compute
tested  property-test  upwind.py:58  courant_number   c : Real, dt : Real, h : Real | cfl(c, dt, h) |- c*dt / h >= 0
tested  python         upwind.py:58  courant_number   the term computes what the annotations compute

7 facts: 7 tested
```

In `courant_number`, `cfl(c, dt, h)` is printed as it is written. The
property tester draws the condition's variables with each claim's own, and
satisfies the condition's conditions as it satisfies a claim's hypotheses;
the check of each claim's reading runs the condition's annotations again at
the same draws. A first version of `cfl` had no `positive: dt > 0`, and the
tester refuted `no_new_extremum` at `dt = -7/3`: a step back in time is no
upwind step. Lean, with Mathlib, is handed each claim with the condition's
conditions as hypotheses, and a written proof cites them by name, `stable`
or `positive`, as it cites its own.

## Take a result on a citation

Some results lanky cannot establish. A sum needs Mathlib in Lean, and a theorem
from a textbook may need a great deal more. Such a result enters the ledger on
the word of a reference, as a claim taken on a source, and what is derived
from it says so. `examples/citation.py` holds Gauss's sum again, Nicomachus's
theorem taken on a citation, and the closed form of the sum of cubes, which
follows from the two. (`examples/nicomachus.py` proves Nicomachus's theorem,
by a chain through a fact lanky knows; see
[A fact over a family](#a-fact-over-a-family).)

```python
@claim(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@claim(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """Four times the sum of the cubes of ``0 .. n`` is ``(n * (n + 1)) ** 2``."""
```

A cited claim is written like any claim, with `cite=` naming the source. An
empty source raises `TypeError` where it is written, because a claim with
nothing behind it is what an `assumed` claim already is. `uses=` takes
claims, cited claims, facts or fact ids, and becomes the `rests_on` of the
claim's fact. (lanky 0.5 wrote `@axiom(cite=...)`, which is refused now with
the line to write.)

```console
$ uv run lanky check examples/citation.py
STATUS                   EFFECTIVE  BY             WHERE           OWNER       STATEMENT
-----------------------  ---------  -------------  --------------  ----------  -------------------------------------------------------------------------
tested                   tested     property-test  citation.py:34  gauss       n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
tested                   tested     python         citation.py:34  gauss       the term computes what the annotations compute
assumed (cited)          assumed    -              citation.py:39  nicomachus  n : Nat |- sum(i**3 for i in Fin(n + 1)) == sum(i for i in Fin(n + 1))**2
tested                   tested     python         citation.py:39  nicomachus  the term computes what the annotations compute
tested under nicomachus  assumed    property-test  citation.py:44  cubes       n : Nat |- 4*sum(i**3 for i in Fin(n + 1)) == (n*(n + 1))**2
tested                   tested     python         citation.py:44  cubes       the term computes what the annotations compute

6 facts: 1 assumed, 5 tested

WITHOUT MATHLIB: gauss and cubes are not proved, since only Lean with Mathlib can state them. To have Lean prove them: python -m lanky.mathlib ~/mathlib (about 7 GB), then export LANKY_LEAN_MATHLIB=~/mathlib.

CITED nicomachus at citation.py:39: Nicomachus of Gerasa, Introduction to Arithmetic
```

The same with Lean and without it, since every statement has a sum in it
(Mathlib mode, below, proves `gauss` and `cubes`), but for the `WITHOUT
MATHLIB` line, which core Lean prints and a machine without Lean does not.
Four things in that output are new.

- `assumed (cited)`. The claim is taken on its citation, which the `CITED`
  line under the table shows and `--json` carries as `cite` in its provenance,
  and no oracle is asked to establish it. It is still sampled for a
  counterexample, because a citation copied down wrong states something the
  reference does not.
- `tested under nicomachus`. `cubes` survived its draws, and the status names
  the assumptions it rests on: whatever it rests on, directly or through other
  facts, that nothing here established. That is a cited claim, another `assumed`
  fact, a `refuted` one, a fact on a circle of facts that rest on each other,
  or an id this ledger does not hold: a claim of another file, since each
  file checked has a ledger of its own, or an id written wrong. `lanky check`
  names such an id in an `UNRESOLVED` line under the table, since in the row it
  reads like any other assumption. `gauss` is not among them, because it is
  tested.
- The `EFFECTIVE` column. What each fact is worth once what it rests on is
  counted: the weakest status over the fact and everything below it, so a
  proof from an assumption is worth the assumption. The column is there only
  when some fact is worth less than its own status says: in `gauss.py`'s
  ledger where Lean proves `scan_monotone`, whose proof is worth the
  `tested` reading it rests on, and not where it does not.
- The `CITED` line. Each cited claim is named under the table with the
  citation it is taken on, one line per claim in the table's order, since that is what
  stands behind its row and behind every `under` that names it.

A cited claim has a reading too, `tested` here. Nothing about the cited
claim rests on it, since the claim is `assumed` on its citation whatever its
reading is worth, but a refuted one would fail the check, and leave
everything that rests on the claim worth `refuted`.

The status column is still each fact's own. `tested` says how strongly `cubes`
is established given what it uses; the oracles decide it as they decide any
claim, and are not handed the statements it uses. `--json` carries
`rests_on`, `effective`, `effective_heuristic` and `under` for every fact, and
the exit code depends on none of them: it is 0 here, since nothing is refuted.

Copy the cited claim down wrong, with `i**2` for `i**3` on the left, and the
property tester refutes it at `n = 3`. The row reads `refuted (cited)`,
`cubes` is worth `refuted` in the `EFFECTIVE` column, the counterexample is
printed under the table, and `lanky check` exits 1. So does a cited claim whose hypotheses were copied
down so that nothing satisfies them, once Lean shows them inconsistent: it
reads `assumed (cited) (vacuous)`, as a proved claim would read `proved
(vacuous)`. `pytest examples/citation.py` samples the cited claim as a test
item too.

A plugin's facts rest on facts the same way: it sets `rests_on` on the facts
it builds, naming other facts by id.

An id names a definition: `claim:citation.gauss@34` is the kind, the
module, the qualified name and the line. The module is the name the file's
path gives it under its source root, `citation` for `examples/citation.py`
and `pkg.helpers` for `root/pkg/helpers.py`, and not the name it was imported
under. So a claim that `main.py` imports with `from helpers import lemma`
and names in `uses=` has the id there that it has in `helpers.py`'s own
ledger, `claim:helpers.lemma@12` in both. `lanky check main.py helpers.py`
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
verdict about that operator. The rules are eight claims taken on a
citation: the four jump relations, `compact(S)`, `compact(D)`, `compact(S')`,
and `~scalar_plus_compact(D')`, which says that `D'`, being hypersingular, is
no multiple of the identity plus a compact operator. The engine reads its
rules off their statements and applies nothing else about layer potentials;
of operators in general it uses only that compact ones form a linear space and
that the identity is not one of them.

```console
$ uv run lanky check examples/pytential_skie.py
STATUS                                                        EFFECTIVE  BY             WHERE                  OWNER                     STATEMENT
------------------------------------------------------------  ---------  -------------  ---------------------  ------------------------  -----------------------------------------------------------------------------------------
assumed (cited)                                               assumed    -              pytential_skie.py:94   jump_S                    gamma : C2Boundary, s : Side |- trace(S, s) == S
assumed                                                       assumed    -              pytential_skie.py:94   jump_S                    the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:99   jump_D                    gamma : C2Boundary, s : Side |- trace(D, s) == 1/2*s*I + D
assumed                                                       assumed    -              pytential_skie.py:99   jump_D                    the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:104  jump_Sp                   gamma : C2Boundary, s : Side |- normal_derivative(S, s) == -1/2*s*I + S'
assumed                                                       assumed    -              pytential_skie.py:104  jump_Sp                   the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:109  jump_Dp                   gamma : C2Boundary, s : Side |- normal_derivative(D, s) == D'
assumed                                                       assumed    -              pytential_skie.py:109  jump_Dp                   the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:114  compact_S                 gamma : C2Boundary |- compact(S)
assumed                                                       assumed    -              pytential_skie.py:114  compact_S                 the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:119  compact_D                 gamma : C2Boundary |- compact(D)
assumed                                                       assumed    -              pytential_skie.py:119  compact_D                 the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:124  compact_Sp                gamma : C2Boundary |- compact(S')
assumed                                                       assumed    -              pytential_skie.py:124  compact_Sp                the term computes what the annotations compute
assumed (cited)                                               assumed    -              pytential_skie.py:129  hypersingular_Dp          gamma : C2Boundary |- ~scalar_plus_compact(D')
assumed                                                       assumed    -              pytential_skie.py:129  hypersingular_Dp          the term computes what the annotations compute
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
decided under jump_Dp, jump_Sp                                assumed    layer-rules    pytential_skie.py:175  helmholtz_burton_miller   normal_derivative(D - 1j*eta*S, EXTERIOR) ~> 1j/2*eta*I + D' - 1j*eta*S' (jump relations)
decided under jump_Dp, jump_Sp, compact_Sp, hypersingular_Dp  assumed    layer-rules    pytential_skie.py:175  helmholtz_burton_miller   1j/2*eta*I + D' - 1j*eta*S' is not second kind: D' is not c*I + compact

29 facts: 16 assumed, 10 decided, 3 tested

WITHOUT LEAN: laplace_dirichlet_dlp, laplace_neumann_slp and helmholtz_combined_field are not proved. To have Lean prove what it can: pip install "lanky[lean]", and Lean v4.29.1 from elan (elan default leanprover/lean4:v4.29.1).

CITED jump_S at pytential_skie.py:94: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_D at pytential_skie.py:99: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_Sp at pytential_skie.py:104: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED jump_Dp at pytential_skie.py:109: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_S at pytential_skie.py:114: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_D at pytential_skie.py:119: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED compact_Sp at pytential_skie.py:124: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6 (Laplace); D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3 (Helmholtz)
CITED hypersingular_Dp at pytential_skie.py:129: D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, 4th ed., Springer, 2019, ch. 3
```

That is the output without Lean. Each cited claim's reading is `assumed`: no
boundary can be drawn, so its annotations cannot be run again at a point, and
nothing rests on it, so no `DECLINED` line says so. With the `lean` extra
the three coefficient rows read `proved  lean`: `coefficient of I: -1/2 != 0` goes to Lean as
`(-1 : Int) ≠ 0`, the numerator's being nonzero, since core Lean has no
rationals, and that arithmetic is the one part of the argument Lean touches.
Nothing about compactness is claimed proved. Those are the `assumed (cited)`
rows, each verdict is `decided under` the ones it used, and in the `EFFECTIVE`
column it is worth what they are.

- **The decider says how far to trust it.** `layer-rules` has the trust class
  `decision-procedure`, as isl does. It accepts one-sided traces of
  combinations of `S` and `D` of one kernel, boundary operators made of `I`,
  `S`, `D`, `S'`, `D'` and such traces, and polynomial coefficients; within
  that fragment it answers every claim by exact polynomial arithmetic, and it
  declines everything outside it with the reason (a verdict that depends on a
  parameter's value, two operators that are not a multiple of the identity
  plus a compact one, two kernels, a trace no cited claim gives). A decider that can
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
uv sync --group dev --extra cas    # in this checkout; pip install "lanky[cas]" elsewhere
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
seconds sympy may take over one fact (60), translating the statement into
sympy and simplifying it.

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
difference to 0, and mpmath's derivatives, at 30 digits, agree at 20 points to
within 1e-20, relative to the derivative or to 1, whichever is larger.

Through order 6 the wrangler follows the recurrence
reconstructed(a + 2, b) == -reconstructed(a, b + 2), which is the PDE sumpy
declares for the kernel, G_xx + G_yy == 0, solved for G_xx.

`lanky check examples/sumpy_recurrence.py` puts the claim in the ledger: tested by
mpmath, decided by the CAS oracle where sympy is installed, and proved for every
order by Lean where Mathlib is, under the kernel's harmonicity at every order.
```

The ledger has the kernel's harmonicity, a claim with a proof, and the one
claim four times, with the evidence for each, and before the last two the one
step the claim takes on a citation:

```console
$ uv run lanky check examples/sumpy_recurrence.py
STATUS                                 EFFECTIVE            BY      WHERE                    OWNER              STATEMENT
-------------------------------------  -------------------  ------  -----------------------  -----------------  ---------------------------------------------------------------------------------------------------
decided (heuristic)                    tested               cas     sumpy_recurrence.py:153  harmonic           x : Real, y : Real
                                                                                                                | away: x**2 + y**2 > 0
                                                                                                                |- (1 - 2*x**2 / (x**2 + y**2)) / (x**2 + y**2) + (1 - 2*y**2 / (x**2 + y**2)) / (x**2 + y**2) == 0
tested                                 tested               python  sumpy_recurrence.py:153  harmonic           the term computes what the annotations compute
tested                                 tested               mpmath  sumpy_recurrence.py:894  compressed_taylor  at 20 points: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= 6
decided (heuristic)                    decided (heuristic)  cas     sumpy_recurrence.py:894  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- reconstructed(a, b)
                                                                                                                  == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= 6
assumed (cited)                        assumed              -       sumpy_recurrence.py:894  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- every order:
                                                                                                                  diff(G, x, a + 2, y, b) + diff(G, x, a, y, b + 2) == 0 for every a, b,
                                                                                                                  with G = log(sqrt(x**2 + y**2)): harmonic differentiated a times in x and b times in y
assumed under harmonic at every order  assumed              -       sumpy_recurrence.py:894  compressed_taylor  every order: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for every a, b,
                                                                                                                  by reconstructed(a + 2, b) == -reconstructed(a, b + 2)
assumed under harmonic at every order  assumed              -       sumpy_recurrence.py:894  compressed_taylor  every order p: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= p,
                                                                                                                  by reconstructed(a + 2, b) == -reconstructed(a, b + 2) inside it

7 facts: 3 assumed, 2 decided, 2 tested

WITHOUT LEAN: harmonic and compressed_taylor are not proved. To have Lean prove what it can: pip install "lanky[lean]", and Lean v4.29.1 from elan (elan default leanprover/lean4:v4.29.1).
WITHOUT MATHLIB: harmonic and compressed_taylor are not proved, since only Lean with Mathlib can state them. To have Lean prove them: python -m lanky.mathlib ~/mathlib (about 7 GB), then export LANKY_LEAN_MATHLIB=~/mathlib.

CITED compressed_taylor at sumpy_recurrence.py:894: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6

NOT CHECKED harmonic at sumpy_recurrence.py:153: without Lean, each step of its proof was tested at drawn points instead (line 161).
```

- **The harmonicity.** `harmonic` is a claim with a proof: `G_xx + G_yy == 0` away from
  the origin, with the second derivatives sympy's. It is the PDE the
  wrangler's recurrence comes from. Its body is its proof, a calculation of
  two steps, read aloud: "Let r2 be x**2 + y**2. The Laplacian equals 2 / r2
  minus 2 (x**2 + y**2) / r2**2, which equals 0." lanky's search finds a
  proof alone too, clearing the denominators and then by algebra, so the
  body is for the reader.

  ```python
  @claim
  def harmonic(x: Real, y: Real, away: x**2 + y**2 > 0) -> laplacian(log_r, x, y) == 0:
      r2 = x**2 + y**2
      assert laplacian(log_r, x, y) == 2 / r2 - 2 * (x**2 + y**2) / r2**2 == 0
      return by()
  ```

  Without Lean the CAS oracle decides it, and the `NOT CHECKED` line says that
  each step was tested at drawn points instead; with Mathlib Lean proves it
  (see [A claim for every order](#a-claim-for-every-order)). Its reading is
  `tested`: the annotation, sympy's Laplacian included, run again as Python
  at drawn points, computes what its term does.
- **The PDE at every order.** The claim's first two rows do not rest on the
  harmonicity, since each checks the reconstruction against the derivatives
  themselves, one order at a time. The last two, for every order, take the
  harmonicity differentiated: every derivative `diff(G, x, a, y, b)`
  satisfies the PDE too, because `G` is smooth away from the origin and its
  derivatives commute with the Laplacian. lanky has no derivative of an
  order it does not know to state that with (#174), so the claim takes it
  on Kress's word, as a fact of its own, `assumed (cited)`, resting on
  `harmonic`: `@reconstructs(log_r, order=ORDER, uses=harmonic,
  cite=KRESS)`. The rows that rest on it name it, `under harmonic at every
  order`, and its `CITED` line under the table gives the reference.
- **The claim at points.** mpmath takes every derivative numerically, by
  finite differences at 30 digits, at 20 points away from the origin, and
  finds each reconstructed one within `1e-20` of the derivative it stands
  for, relative to the derivative or to 1, whichever is larger: relative to
  a derivative of size 1 or more, and absolutely below that, where the
  finite differences are accurate to their digits of the kernel's scale
  rather than of the derivative's, and a derivative that is `0` at a point
  comes out as a few units in its last digits. The oracle that does it,
  `mpmath`, of the trust class `test`, is the file's own, as a plugin's
  would be, and records the tolerance with the fact.
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
  at a point are such a `D`, by the PDE at every order, which is why the row
  reads `under harmonic at every order`, and the wrangler's reconstruction is
  such an `R`: the
  recurrence is read off the PDE sumpy declares for the kernel, as the
  wrangler reads it, and the wrangler's weights through order 6 are checked
  against it, as the Python run above says. Core Lean cannot state the row,
  since it is over the reals, and the tester cannot draw a table over `Nat`,
  so it is `assumed` here; Lean proves it with Mathlib (see
  [Prove it with Mathlib](#prove-it-with-mathlib)).
- **The claim on the triangle of every order.** What a wrangler of order `p`
  does: it has the coefficients up to that order, and follows the
  recurrence only where the derivative it gives is inside it. Over the order
  `p` as well as the two tables: `R` is `D` where the wrangler stores and
  the order reaches (`a < 2` and `a + b <= p`), and follows the recurrence
  where `a + b + 2 <= p`; then `R` is `D` on the triangle `a + b <= p`. It is
  the corollary a kernel of order `p` cites, since its arrays end at the
  order, and it rests on the PDE at every order as the claim for every order
  does.
- **A wrong recurrence fails the check.** Flip the sign of one reconstructed
  coefficient in the wrangler and the first two rows are refuted: mpmath
  names the coefficient and the point, sympy declines with the difference it
  is left with, twice a stored derivative, and the tester finds a point of
  its own. `lanky check` exits 1. The last two rows are not there: the
  wrangler's weights no longer follow its PDE's recurrence, so it makes no
  claim for every order.

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
Mathlib's packed downloads (410 MB) are in /home/you/mathlib/.lake/mathlib-cache, inside the project: deleting the project deletes them
ready: export LANKY_LEAN_MATHLIB=/home/you/mathlib
```

(abridged: the middle is Lake cloning Mathlib and the cache tool fetching it.)
It writes three files and runs `lake exe cache get`, which clones Mathlib and
its dependencies at the pinned commits and fetches the compiled files Mathlib
publishes: about 7 GB on disk and a few minutes. It never builds Mathlib from
source, which would take hours. The project is wherever you put it, and holds
everything the command fetched: the cache tool keeps what it downloads (about
400 MB, packed) in the project's `.lake/mathlib-cache`, so deleting `~/mathlib`
deletes all of it, unless `MATHLIB_CACHE_DIR` names another place, and the
line before `ready` says where they are. The REPL lanky builds goes where
`LANKY_LEAN_CACHE_DIR` says, as in core mode. Then:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/gauss.py
STATUS  EFFECTIVE  BY      WHERE        OWNER          STATEMENT
------  ---------  ------  -----------  -------------  -------------------------------------------------------------------------
proved  tested     lean    gauss.py:31  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
tested  tested     python  gauss.py:31  gauss          the term computes what the annotations compute
proved  tested     lean    gauss.py:39  scan_monotone  n : Nat, cnt : Fn[Fin(n), Nat], off : Fn[Fin(n + 1), Nat]
                                                       | h0: off(0) == 0
                                                       | hs: forall r in Fin(n). off(r + 1) == off(r) + cnt(r)
                                                       |- forall a in Fin(n + 1), b in Fin(n + 1) where a <= b. off(a) <= off(b)
tested  tested     python  gauss.py:39  scan_monotone  the term computes what the annotations compute

4 facts: 2 proved, 2 tested
```

Both claims are proved now, each worth the `tested` reading it rests on. The
oracle started its REPL in the project, imported
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
`field_simp`, `linarith`, `nlinarith`, `ring` after `push_cast` and after
`field_simp`, and two with `simp`), and the last script is an induction on `n`, which the
ladder chose because `n` is a natural parameter that the bound of a sum
mentions: trade `n` for the natural it is, and in each case take the last term
off the sum, which leaves the induction hypothesis and a polynomial identity
for `linarith`. The provenance records the script, the Mathlib revision as
`lean_mathlib`, and the source as a file that replays it, starting with
`import Mathlib`. `--verbose` prints the project on the Lean oracle's line.

The same variable makes `examples/citation.py` read `proved` for `gauss` and
`proved under nicomachus` for `cubes`, which the induction proves on its own.
It is still worth `assumed`, because `uses=` says what it rests on. In
`examples/nicomachus.py`, whose `nicomachus` is a claim with a proof (see
[A fact over a family](#a-fact-over-a-family)), all three read `proved`.

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

With the same variable, the sumpy demonstration's harmonicity is proved, by
the two steps of its body, and so are its last two rows, under the PDE at
every order, the one step they take on a citation:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/sumpy_recurrence.py
STATUS                                EFFECTIVE            BY      WHERE                    OWNER              STATEMENT
------------------------------------  -------------------  ------  -----------------------  -----------------  ---------------------------------------------------------------------------------------------------
proved                                tested               lean    sumpy_recurrence.py:153  harmonic           x : Real, y : Real
                                                                                                               | away: x**2 + y**2 > 0
                                                                                                               |- (1 - 2*x**2 / (x**2 + y**2)) / (x**2 + y**2) + (1 - 2*y**2 / (x**2 + y**2)) / (x**2 + y**2) == 0
                                                                                                               by its proof, sumpy_recurrence.py:160-162: 2 steps
tested                                tested               python  sumpy_recurrence.py:153  harmonic           the term computes what the annotations compute
tested                                tested               mpmath  sumpy_recurrence.py:894  compressed_taylor  at 20 points: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= 6
decided (heuristic)                   decided (heuristic)  cas     sumpy_recurrence.py:894  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- reconstructed(a, b)
                                                                                                                 == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= 6
assumed (cited)                       assumed              -       sumpy_recurrence.py:894  compressed_taylor  x : Real, y : Real | x**2 + y**2 > 0 |- every order:
                                                                                                                 diff(G, x, a + 2, y, b) + diff(G, x, a, y, b + 2) == 0 for every a, b,
                                                                                                                 with G = log(sqrt(x**2 + y**2)): harmonic differentiated a times in x and b times in y
proved under harmonic at every order  assumed              lean    sumpy_recurrence.py:894  compressed_taylor  every order: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for every a, b,
                                                                                                                 by reconstructed(a + 2, b) == -reconstructed(a, b + 2)
proved under harmonic at every order  assumed              lean    sumpy_recurrence.py:894  compressed_taylor  every order p: reconstructed(a, b) == diff(log(sqrt(x**2 + y**2)), x, a, y, b) for a + b <= p,
                                                                                                                 by reconstructed(a + 2, b) == -reconstructed(a, b + 2) inside it

7 facts: 1 assumed, 1 decided, 3 proved, 2 tested

CITED compressed_taylor at sumpy_recurrence.py:894: R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6
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
order it is proving. The goal's own guards count too: the claim on the
triangle asks the recurrence only where `a + b + 2 <= p`, and its step at
`a = k + 2` takes it at `(k, b)` because the goal's guard there is `k + 2 + b
<= p`, which `omega` reads off the hypotheses the case introduced. Python
searches, Lean checks: a wrong certificate is one failed attempt, never a
wrong proof.

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
of it importing Mathlib and asking Lean whether the last two rows'
hypotheses are inconsistent and their goals' domains empty, which they are
not. Each
ladder has a budget, `LANKY_LEAN_BUDGET` (120 s) for a claim and
`LANKY_LEAN_VACUITY_BUDGET` (30 s) for each of those two questions, which
also leave out the attempts that cannot show `False`, such as the
inductions; the search for the induction's multipliers counts against the
claim's.

### Exchange finite sums

A tensor-product operator on a hexahedral element is built from three
one-dimensional ones, `F` along the first axis, `G` along the second and `H`
along the third: its entry at the row `(a, b, c)` and the column `(p, q, r)` is
`H[c, r] * G[b, q] * F[a, p]`, the Kronecker product `H (x) G (x) F`. Sum
factorization applies it in three one-axis passes rather than as the dense
`n**3 x n**3` matrix, which is what grudge does (inducer/grudge PR #418).
`examples/sum_factorization.py` states why that is right, at every size `n`:

```python
@claim
def sum_factorization(
    n: Nat,
    F: Fn[Fin[n], Fin[n], Real],
    G: Fn[Fin[n], Fin[n], Real],
    H: Fn[Fin[n], Fin[n], Real],
    u: Fn[Fin[n], Fin[n], Fin[n], Real],
    a: Fin[n],
    b: Fin[n],
    c: Fin[n],
) -> sum(
    kron(H, G, F)(a, b, c, p, q, r) * u[p, q, r] for p in Fin[n] for q in Fin[n] for r in Fin[n]
) == sum(
    H[c, r] * sum(G[b, q] * sum(F[a, p] * u[p, q, r] for p in Fin[n]) for q in Fin[n])
    for r in Fin[n]
):
```

A matrix is a family with two indices, `Fn[Fin[n], Fin[n], Real]`, which is
`Fn[Fin[n], Fn[Fin[n], Real]]`, and its entry is `F[a, p]`, as numpy writes
it; `F(a, p)` and `F(a)(p)` are the same entry, to the tester, to the check of
the reading and to Lean, which writes `F a p`. Called as a function, a claim
takes a nested list, a numpy array or a function for such a family
(`F=lambda a, p: ...`), and a value of another shape is refused with the shape
it takes. A hypothesis may define a matrix entry by entry, `all(F[i, j] == ...
for i in Fin[n] for j in Fin[n])`, and the tester then fills in its entries
rather than waiting for a random draw to meet it. `kron` is a helper in the
file that returns the entry of `H (x) G (x) F`, and the reading of the
annotation expands it. The row `(a, b, c)` is a parameter rather than a
quantifier in the goal: the statement is the same, a claim's parameters are
universal, and the tester draws a row rather than walking all `n**3` of them,
each a sum of `n**3` terms (#125). Run as a program, the file applies grudge's weak
derivative both ways at orders 1 to 7 (`python examples/sum_factorization.py`);
checked with Mathlib:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/sum_factorization.py
STATUS  EFFECTIVE  BY             WHERE                     OWNER              STATEMENT
------  ---------  -------------  ------------------------  -----------------  --------------------------------------------------------------------------------------------------
proved  tested     lean           sum_factorization.py:68   exchange           n : Nat, m : Nat, f : Fn[Fin(n), Fin(m), Real]
                                                                               |- sum(sum(f[i, j] for j in Fin(m)) for i in Fin(n))
                                                                                   == sum(sum(f[i, j] for i in Fin(n)) for j in Fin(m))
tested  tested     python         sum_factorization.py:68   exchange           the term computes what the annotations compute
proved  tested     lean           sum_factorization.py:89   sum_factorization  n : Nat, F : Fn[Fin(n), Fin(n), Real], G : Fn[Fin(n), Fin(n), Real], H : Fn[Fin(n), Fin(n), Real],
                                                                                 u : Fn[Fin(n), Fin(n), Fin(n), Real], a : Fin(n), b : Fin(n), c : Fin(n)
                                                                               |- sum(H[c, r]*G[b, q]*F[a, p]*u[p, q, r] for p in Fin(n), q in Fin(n), r in Fin(n))
                                                                                   == sum(H[c, r]*sum(G[b, q]*sum(F[a, p]*u[p, q, r] for p in Fin(n)) for q in Fin(n))
                                                                                     for r in Fin(n))
tested  tested     python         sum_factorization.py:89   sum_factorization  the term computes what the annotations compute
proved  tested     lean           sum_factorization.py:113  mixed_product      n : Nat, A : Fn[Fin(n), Fin(n), Real], B : Fn[Fin(n), Fin(n), Real], C : Fn[Fin(n), Fin(n), Real],
                                                                                 D : Fn[Fin(n), Fin(n), Real], i : Fin(n), k : Fin(n), p : Fin(n), q : Fin(n)
                                                                               |- sum(A[i, j]*B[k, s]*(C[j, p]*D[s, q]) for j in Fin(n), s in Fin(n))
                                                                                   == sum(A[i, j]*C[j, p] for j in Fin(n))*sum(B[k, s]*D[s, q] for s in Fin(n))
tested  tested     python         sum_factorization.py:113  mixed_product      the term computes what the annotations compute
tested  tested     property-test  sum_factorization.py:143  flattening         n : Nat, F : Fn[Fin(n), Fin(n), Real], G : Fn[Fin(n), Fin(n), Real], H : Fn[Fin(n), Fin(n), Real],
                                                                                 a : Fin(n), b : Fin(n), c : Fin(n), p : Fin(n), q : Fin(n), r : Fin(n)
                                                                               |- H[(a + n*b + n**2*c) // n**2, (p + n*q + n**2*r) // n**2]*G[(a + n*b + n**2*c) // n % n,
                                                                                     (p + n*q + n**2*r) // n % n]*F[(a + n*b + n**2*c) % n, (p + n*q + n**2*r) % n]
                                                                                   == H[c, r]*G[b, q]*F[a, p]
tested  tested     python         sum_factorization.py:143  flattening         the term computes what the annotations compute

8 facts: 3 proved, 5 tested
```

Lean proves the factorization in three steps, and lanky finds the one that
is a search. Distribute each factor into the sums inside it
(`Finset.mul_sum`, `Finset.sum_mul`, `Finset.sum_div`): the right side is
then a sum over `r`, `q` and `p`, in that order, and the left side a sum over
`p`, `q` and `r`. Exchange adjacent sums of the left side until the orders
agree (`Finset.sum_comm`, one exchange at a time), and compare the summands
under all three sums at once (`Finset.sum_congr`), which `ring` does. Which
sums to exchange is what Python finds (`lanky.sums`): it reads both sides as
`simp` leaves them and tries the orders of the left side's sums whose domains
agree with the right side's, comparing the summands with sympy (the `cas`
extra) where it is installed, and the script it writes exchanges them:

```text
  try simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  all_goals (conv_lhs => enter [2, x]; rw [Finset.sum_comm])
  all_goals (conv_lhs => rw [Finset.sum_comm])
  all_goals (conv_lhs => enter [2, x]; rw [Finset.sum_comm])
  all_goals refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x_1 _ =>
    Finset.sum_congr rfl fun x_2 _ => ?_
  all_goals first | ring1 | ...
```

Lean checks it: an order that is wrong is an attempt that fails, never a
proof. `mixed_product` is the Kronecker product's mixed product property,
`(A (x) B)(C (x) D) = AC (x) BD` entry by entry, which is the same two steps
with a product of two sums on the right. A sum with an `if`, a sum whose
bound is another sum's binder (a triangle) and a sum over a sort are not
exchanged this way.

`flattening` stays `tested`, and Lean is not asked: it says which factor of
modepy's dense matrix comes last, `kron(H, kron(G, F))` with the first axis
fastest, and that takes `i // n**2` and `i % n` of a size `n` that is a
variable. lanky shows a family's argument is in its domain by linear
arithmetic over the binders, and does not hand Lean a statement where it
cannot (#126).

### A claim from an order on

`examples/line_taylor.py` checks the expansion pytential evaluates a layer
potential on its own surface with: sumpy's line-Taylor expansion of the 2-D
Laplace kernel, `log |alpha + tau * beta|` expanded in `tau` along the line
from a center through a target. Read as complex numbers, its coefficients are
the real parts of those of `log(alpha + tau * beta)`, and the claim for every
order is below. The file reads sumpy's own expansion, so it needs sumpy, as
`examples/sumpy_recurrence.py` does: `uv pip install sumpy` in a checkout,
`pip install sumpy` beside an install from PyPI.

```python
@claim
def line_taylor(
    alpha: Complex,
    beta: Complex,
    a: Fn[Nat, Complex],
    nonzero: alpha != 0,
    first_term: alpha * a[1] == beta,
    ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
) -> all(a[n] == -((-beta / alpha) ** n) / n for n in Nat if n >= 1):
    """The line-Taylor coefficients of ``log(alpha + tau * beta)``, at every order."""
    for n in line_taylor.conclusion.domain:
        if n == 1:
            yield by(first_term)
        else:
            assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode[n - 1])
            yield by(line_taylor.conclusion[n - 1])
```

`first_term` and `ode` are the differential equation the logarithm solves
along the line, `(alpha + tau * beta) * f'(tau) == beta`, read on its
coefficients at `tau ** 0` and at `tau ** n`. The equation is the claim
`line_ode`: sympy differentiates the logarithm, `beta / (alpha + tau *
beta)`, and what is left is algebra, which lanky proves alone. Comparing the
coefficients is the one step taken on a citation, as differentiating the PDE
at every order is in the sumpy demonstration above: lanky has no power
series to state it with (#174). No row claims it. `line_taylor` is about any
table that satisfies the two hypotheses, and the CAS row below checks sumpy's
own coefficients, order by order.

The body is the proof, as a reader says it: "For each n, in order. At n = 1,
by the first term. Otherwise the ODE at n − 1 gives a[n] from a[n − 1], and
it holds by line_taylor at n − 1." The claim's own name is spelled out, and
its parts are addressed through it: `line_taylor.conclusion.domain` is the
points the conclusion's `for` ranges over, in increasing order, and
`line_taylor.conclusion[n - 1]` is the conclusion at the point before, which
the loop has filled in: the induction. `assert ..., by(ode[n - 1])` is a step
with its reason, the ODE at the point `n - 1`, and the step is known for the
rest of its case; `yield by(...)` closes the case. Brackets give a point of a
domain, and parentheses give another claim its inputs, as `gauss(n - 1)`
does below. Each step becomes a line of Lean, which checks it; `python` never
runs a proof. A step left open is written `by(...)`, and the claim then reads
assumed, with the line named.

The file prints sumpy's coefficients beside the closed form:

```console
$ uv run python examples/line_taylor.py
k  closed form                sympy: sumpy's / k! - closed form  sumpy's / k! at a point
-  -------------------------  ---------------------------------  -----------------------
0  log|alpha|                 0                                  0.458145
1  re(-(-beta/alpha)**1 / 1)  0                                  -0.05
2  re(-(-beta/alpha)**2 / 2)  0                                  0.21
3  re(-(-beta/alpha)**3 / 3)  0                                  0.0210833
4  re(-(-beta/alpha)**4 / 4)  0                                  -0.0430437
5  re(-(-beta/alpha)**5 / 5)  0                                  -0.00881975
6  re(-(-beta/alpha)**6 / 6)  0                                  0.0114608

With alpha = a0 + a1*1j the center less the source and beta = b0 + b1*1j the target
less the center, sumpy's line-Taylor coefficients of log|x| are the real parts of
the series of log(alpha + tau*beta) through order 6; the point is
alpha = 3/2 - 1/2*1j, beta = 1/4 + 1j.

`lanky check examples/line_taylor.py` puts it in the ledger: decided through the
order by the CAS oracle, and the closed form proved for every order by Lean where
Mathlib is installed, as is the differential equation the kernel solves.
```

and with Mathlib:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/line_taylor.py
STATUS               EFFECTIVE            BY      WHERE               OWNER          STATEMENT
-------------------  -------------------  ------  ------------------  -------------  ------------------------------------------------------------------------------
proved               tested               lean    line_taylor.py:117  line_ode       alpha : Complex, beta : Complex, tau : Real
                                                                                     | off: alpha + tau*beta != 0
                                                                                     |- (alpha + tau*beta)*(beta / (alpha + beta*tau)) == beta
tested               tested               python  line_taylor.py:117  line_ode       the term computes what the annotations compute
proved               tested               lean    line_taylor.py:133  line_taylor    alpha : Complex, beta : Complex, a : Fn[Nat, Complex]
                                                                                     | nonzero: alpha != 0
                                                                                     | first_term: alpha*a[1] == beta
                                                                                     | ode: forall n in Nat where n >= 1. (n + 1)*alpha*a[n + 1] + n*beta*a[n] == 0
                                                                                     |- forall n in Nat where n >= 1. a[n] == -(-beta / alpha)**n / n
                                                                                     by its proof, line_taylor.py:147-152: induction on n, 2 cases, 3 steps
tested               tested               python  line_taylor.py:133  line_taylor    the term computes what the annotations compute
decided (heuristic)  decided (heuristic)  cas     line_taylor.py:301  qbx_expansion  a0, a1, b0, b1 : Real | a0**2 + a1**2 > 0 |- with alpha = a0 + a1*1j
                                                                                       and beta = b0 + b1*1j, sumpy's coefficient(0) == log(abs(alpha))
                                                                                       and coefficient(k) / k! == re(-(-beta / alpha)**k / k) for 1 <= k <= 6

5 facts: 1 decided, 2 proved, 2 tested
```

The row's last line says the body proved it too: `by its proof`, with where
the proof is and what it is. lanky's own search proves the claim as well,
and the paragraph below is how; a broken body would still fail the check.

The claim starts at order 1, and the induction takes that into account. Its
guard, `n >= 1`, leaves order 0 without an equation, and the induction
hypothesis holds only from order 1, so the step is tried two orders at a time
as well as one: order 0 is a base case the guard rules out, which `omega`
closes from the guard, order 1 is `first_term` times `1 / alpha`, and the step at
`k + 2` is the recurrence at `k + 1` and the induction hypothesis at `k + 1`,
with multipliers that divide by `(k + 2) * alpha`. The step shows first that
`k + 1` and `k + 2` are not zero in `ℂ`, which `field_simp` cannot see for
itself, and the combination splits the power `(-beta / alpha) ** (k + 2)`
before it clears the denominators. Python finds the multipliers, as it does
for every order of the sumpy recurrence, and Lean checks them. The CAS row is
sumpy's own expansion through order 6, compared with the closed form, which
ties the claim to the code pytential runs. Without Mathlib the claim for
every order reads `assumed`: the property tester draws no family over `Nat`.
`line_ode` reads `decided (heuristic)`, by the CAS oracle.

### The proof lanky found

What the search found can be read back in Python. After the ledger,
`--proofs` prints the proof of each proved claim as a body, in the
claim's own names, ready to paste under its docstring. For `line_taylor`,
whose body is a chain, it is the proof lanky's search found on its own, in
the shorter form a proof takes when every step is routine algebra:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/line_taylor.py --proofs line_taylor
...
PROOF line_taylor at line_taylor.py:133, by induction on n, two at a time:

    for n in line_taylor.conclusion.domain:
        if n == 1:
            yield by(first_term)
        else:
            yield by(ode[n - 1], line_taylor.conclusion[n - 1])
```

Read aloud: for each `n`; if `n` is 1, by `first_term`; otherwise by `ode` at
`n - 1` and the conclusion at `n - 1`. The conclusion at a smaller order is
the induction, and a fact is written at a point only where the point says
something: `first_term` has none, and `ode` fits the claim at `n - 1` and at
`n`, so its point is written. The multipliers are not: lanky finds them.
`--proofs` prints a loop only where its order fits the induction lanky
found, the conclusion at an earlier point coming earlier in the loop; where
an induction on the second variable of `for a in Nat for n in Nat` cites the
conclusion at `(a + 1, n - 1)`, no loop over `(a, n)` fits, and it names the
strategy in words, with the order of the conclusion's `for` that a loop would
fit.

`--steps` prints the outline of a proof in lanky's notation: of the proof as
written, where the claim has one, a row per step at its Python line, with
the case it is in and the facts it follows from at the points lanky found;
and otherwise of the proof the search found, each case a chain of equations
from the claim's left side to its right, with the fact, the point and the
multiplier of every link. Each case is named as the body reads, in its
order: after `if a + b == 0:`, the next case of `every_box` is `if a < 2:`,
and the last `otherwise:`; a split under one that held says its condition
the other way round, `if a < 2 and b >= 2:`.

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/line_taylor.py --steps line_taylor
...
STEPS line_taylor at line_taylor.py:133, as its proof says them:
  the claim, induction on n, 2 cases, 3 steps
  line_taylor.py:149  if n == 1:  a[1] == -(-beta / alpha)**1 / 1               by first_term
  line_taylor.py:151  otherwise:  a[n] == (n - 1) / n*(-beta / alpha)*a[n - 1]  by ode, at (n - 1)
  line_taylor.py:152              a[n] == -(-beta / alpha)**n / n               by the claim at (n - 1)
```

lanky builds both from the proof, and reads nothing back from Lean. An
exchange of sums, `exchange` in `examples/sum_factorization.py`, is printed as
a chain from its left side, through the left side with its sums in the order
found, to its right side. A proof by any other rung of the ladder names the
rung, as in `by integer arithmetic` or `by induction on n, taking the last
term off the sum`.

## Write a proof

lanky finds a proof where it can, and a claim it proves alone needs no body.
Where it cannot, or where a proof helps the reader, the claim's body is the
proof. It is written with the checks an engineer already writes, `assert`,
`if` and `for`, and the reason for each step comes after it, in `by(...)`.

### The whole language, on one card

```python
from __future__ import annotations          # every lanky file: annotations are read by lanky, not run on import
from lanky import by, claim, condition
```

| You write | It means |
|---|---|
| `@condition def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)): """..."""` | a named set of assumptions: typed variables and named conditions, a docstring, no goal, no body |
| `@claim def name(variables, named conditions) -> goal:` | a claim. With no body, lanky's strategies try to prove it; with a body, the body is its proof. |
| `@claim(cite="Ahlfors 1979, ch. 5")` | a claim taken on a source |
| `with cfl as (nu, stable):` | assuming cfl. `as` binds every name of its signature, in order. Every claim defined in the block holds under it. |
| `with some_claim.conditions as (...)` | assuming another claim's conditions |
| `with some_claim as (...)` | assuming a whole claim, its goal included |
| `cfl(nu=0.5)`, `gauss(n - 1)` | parentheses give a claim or condition for given inputs (its typed parameters): natively `True` or `False`, in `by(...)` a fact, in a conclusion a statement to prove. Calling a claim evaluates its statement; it never runs its proof. |
| `assert x == y, by(f, g)` | a step: `x == y` holds by these facts. It is known for the rest of its case. Chains (`x == y == z`) and `<=`, `<`, `>=`, `>` work as in Python. |
| `assert x == y` | a step that lanky closes by itself (algebra and its strategies) |
| `line_taylor.conditions`, `line_taylor.conclusion` | the two halves of a claim; `line_taylor.conditions.ode` is one condition |
| `for n in line_taylor.conclusion.domain:` | each point the conclusion's `for` ranges over, in increasing order; `for i, a, b in ...domain:` for several variables of one `for` |
| `every_box.conclusion[i].domain` | a nested domain: the conclusion at a point is itself a `for` |
| `yield by(f, g)` | closes the case at this point |
| `return by(f, g)` | closes a claim proved without a loop over its conclusion's domain |
| `by()` | nothing to add: it follows directly (lanky's strategies, with the steps asserted) |
| `by(...)` | a step or case left open: the proof holds but for it, and the row names the line |
| a fact by name: `ode`, `pde`, `gauss` | lanky finds the point or inputs at which it applies |
| `ode[n - 1]`, `pde[i, a - 2, b]`, `every_box.conclusion[i][a, b]` | brackets give a statement at a point of its domain |
| `line_taylor.conclusion[n - 1]` inside `line_taylor`'s proof | the claim's own conclusion at an earlier point: induction. It is checked to be earlier. |

Four rules hold the card together:

- **Parentheses give a claim for inputs; brackets give a statement at a
  point of its domain.** These are Python's own call and index.
- **Everything is addressed through the tree:** `name.conditions`,
  `name.conclusion`, `name.conclusion.domain`, `name.conclusion[p]`,
  `name.conclusion[p].domain`. A claim has no `.domain` of its own, and
  lanky refuses one with the fix shown.
- **Every case of a proof ends with a closing line**, `yield by(...)` or
  `return by(...)`, and `by()` when nothing is needed. No case is left
  looking skipped.
- **The claim's own name is spelled out** in its proof. There is no `this`
  and no `self` (in a class, write `MyClass.name`, as Python requires). A
  claim refers to itself only through its conclusion's points, so it never
  calls itself. A variable you induct on belongs in the conclusion's `for`.

**Inputs and points.** A claim's inputs are its typed parameters; its
conditions are never passed. Inside its own proof, `name.conclusion` is the
conclusion for this proof's inputs. A cited `other.conclusion[p]` finds the
other claim's inputs by matching, or takes them from a call,
`other(x, y).conclusion[p]`. A conclusion `all(... for i in A for a in B
for b in C if g)` has one domain, whose points are `(i, a, b)` where the
guard holds. A conclusion `all(all(... for a in B) for i in A)` has a domain
over `i`, and `conclusion[i]` has its own domain over `a`.

### A proof is a loop that fills in a table

Put this in `table.py`:

```python
from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fn, Int, Nat


@claim
def compressed_taylor(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """What sumpy stores of a harmonic table, reconstructed, is the table."""
    for a, b in compressed_taylor.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)
```

It is the claim of the [sumpy demonstration](#decide-an-identity-with-a-computer-algebra-system)
over tables of integers, so that core Lean checks it. `D` is any table that
satisfies Laplace's equation at every order, as a harmonic kernel's
derivatives do. `R` agrees with `D` where sumpy stores (`a < 2`), and
follows the recurrence everywhere else. `examples/every_box.py` is the same
proof over tables of reals, box by box in sumpy's storage order, where the
base case rests on two pairs of hypotheses. lanky's search does not split a
case on the conditions of the facts it combines (#140), so it does not find
that proof alone; with Mathlib, the written one reads `by its proof,
every_box.py:113-119: induction on a, 3 cases, 3 steps`.

Read it aloud: *"For each point (a, b) of the conclusion, in order. If a <
2, by what is stored. Otherwise by the recurrence, the conclusion at (a − 2,
b + 2), and the PDE."* The point (a − 2, b + 2) comes earlier in the loop
than (a, b), because `a`, the outer variable, is smaller there.

For an engineer, the claim is a table of true and false over its domain,
and the proof is a loop that fills it in, in order. Each entry may use
entries already filled. That is induction, with no function standing for a
proof. It reads like the kernel that fills the table itself, here
`examples/every_box.py`'s claim beside loopty's kernel:

```python
# loopty kernel                                 # lanky proof
for box, a, b in R.dom:                         for i, a, b in every_box.conclusion.domain:
    if a < 2:                                       if a + b == 0:
        R[box, a, b] = C[box, a, b]                     yield by(centre_copy, centre)
    else:                                           elif a < 2:
        R[box, a, b] = -R[box, a - 2, b + 2]            yield by(copies, stored)
                                                    else:
                                                        yield by(recurrence, every_box.conclusion[i, a - 2, b + 2], pde)
```

- `stored`, `recurrence` and `pde` are cited by name alone, and lanky finds
  the point at which each applies by matching it against the case: `stored`
  at `(a, b)`, `recurrence` and `pde` at `(a - 2, b)`. Write the point
  yourself where you want to say it, in brackets: `recurrence[a - 2, b]`.
- `yield by(...)` closes the case at the point the loop is at. A `yield`
  serves the innermost loop over a domain.
- The step can be written out as a calculation, Python's own chained
  comparison in one `assert`, with the facts it uses after it. Its two ends
  are the case's two sides, so the case then closes with `yield by()`:

  ```python
          else:
              assert R[a, b] == -R[a - 2, b + 2] == -D[a - 2, b + 2] == D[a, b], by(
                  recurrence[a - 2, b], compressed_taylor.conclusion[a - 2, b + 2], pde[a - 2, b]
              )
              yield by()
  ```

  Each link is a step at the line of the term it reaches, and each fact
  serves the links it fits.

A conclusion can nest its domains. `examples/every_box.py`'s claim over every
box `i` could read `all(all(... for a in Nat for b in Nat if a + b <= p) for
i in Fin[n])`, and its proof is then two loops:

```python
    for i in every_box.conclusion.domain:
        for a, b in every_box.conclusion[i].domain:
            if a + b == 0:
                yield by(centre_copy, centre)
            elif a < 2:
                yield by(copies, stored)
            else:
                yield by(recurrence, every_box.conclusion[i][a - 2, b + 2], pde)
```

A cited point must come earlier in the loops: lexicographic in the binders,
outer domains first, and strict. An argument from the point above, toward a
bound, walks a bounded domain from the top down, and "earlier" then means
earlier in that reversed loop:

```python
@claim
def climb(
    p: Nat, H: Fn[Nat, Int], top: H[p] == 0, step: all(H[k] == H[k + 1] for k in Nat if k < p)
) -> all(H[k] == 0 for k in Nat if k <= p):
    for k in reversed(climb.conclusion.domain):
        if k == p:
            yield by(top)
        else:
            yield by(step[k], climb.conclusion[k + 1])
```

A claim with no `for` in its conclusion has no loop, and closes with
`return by(...)`, as `log_of_the_modulus` does in
[What lanky knows](#what-lanky-knows).

### Two runs of one body

Running or importing the file runs no proof: `python table.py` prints
nothing, and `pytest` tests the statement. The body runs only under `lanky
check`, in two ways.

- **Natively**, at the check's draws, as plain Python. The values are exact,
  `Fraction`s and exact complex numbers, never floats.
  `compressed_taylor.conclusion.domain` gives the domain's first points, and
  a table over the naturals, such as `D` and `R`, is filled in from the
  hypotheses that define it. Each `assert`, and the conclusion at each point
  where its case closes, is checked at those values. A failure is reported
  at its line, with its numbers, and needs no Lean. The native run only
  tests: it never proves.
- **Traced**, on symbolic values, once per path through the body. The loop
  gives one symbolic point, with the domain's guard known, and Lean proves
  each step and each case. The conclusion over its points is a theorem of
  its own in Lean, and a cited earlier point is a call of it, with the
  measure lanky finds: an argument that gets smaller at every call, one that
  climbs toward a bound under `reversed(...)`, or a pair. `--show-lean`
  prints it.

With core Lean, the claim reads `proved`, and its row says how, on a line
of its own:

```console
$ uv run lanky check table.py
STATUS  EFFECTIVE  BY      WHERE       OWNER              STATEMENT
------  ---------  ------  ----------  -----------------  --------------------------------------------------------------------
proved  tested     lean    table.py:7  compressed_taylor  D : Fn[Nat, Nat, Int], R : Fn[Nat, Nat, Int]
                                                          | pde: forall a in Nat, b in Nat. D[a + 2, b] + D[a, b + 2] == 0
                                                          | stored: forall a in Nat, b in Nat where a < 2. R[a, b] == D[a, b]
                                                          | recurrence: forall a in Nat, b in Nat. R[a + 2, b] == -R[a, b + 2]
                                                          |- forall a in Nat, b in Nat. R[a, b] == D[a, b]
                                                          by its proof, table.py:16-20: induction on a, 2 cases, 2 steps
tested  tested     python  table.py:7  compressed_taylor  the term computes what the annotations compute

2 facts: 1 proved, 1 tested
```

Without Lean the row reads `assumed`, since the property tester draws no
table over `Nat`, and a line under the table says what the native run did
instead:

```text
NOT CHECKED compressed_taylor at table.py:7: without Lean, its proof was not checked by Lean; it was run at 8 drawn values instead, and every step held.
```

`--steps` prints the proof's outline, a row per step at its Python line,
with the points lanky found for the facts cited by name:

```text
$ uv run lanky check --steps compressed_taylor table.py
...
STEPS compressed_taylor at table.py:7, as its proof says them:
  the claim, induction on a, 2 cases, 2 steps
  table.py:18  if a < 2:   R[a, b] == D[a, b]  by stored, at (a, b)
  table.py:20  otherwise:  R[a, b] == D[a, b]  by recurrence at (a - 2, b), the claim at (a - 2, b + 2) and pde at (a - 2, b)
```

`lanky check` refuses to run under `python -O`, which removes every
`assert`, and with them every step: *"lanky check reads each assert of a
written proof as a step, and python -O removes every assert; run it without
-O (and without PYTHONOPTIMIZE)"*. To run a proof by hand, in a REPL or
under pdb, call `compressed_taylor.run_proof(D=..., R=...)` with the tables.
Floats compare exactly there, so give it `Fraction`s.

### When a step fails

Write the last case as a calculation, and drop a sign in the middle:

```python
        else:
            assert R[a, b] == -R[a - 2, b + 2] == D[a - 2, b + 2] == D[a, b], by(
                recurrence[a - 2, b], compressed_taylor.conclusion[a - 2, b + 2], pde[a - 2, b]
            )
            yield by()
```

The native run finds it before Lean is asked, with Lean or without:

```console
$ uv run lanky check table.py
...
UNPROVED compressed_taylor at table.py:7: a step of its proof is false.

  table.py:20    assert R[a, b] == -R[a - 2, b + 2] == D[a - 2, b + 2] == D[a, b], by(

  At a = 2, b = 0: the left side is 5, the right side -5.
```

A step can also be true and still not follow from what it cites. Cite the
conclusion one cell off, with each fact at its point:

```python
            yield by(recurrence[a - 2, b], compressed_taylor.conclusion[a - 2, b + 3], pde[a - 2, b])
```

Every step holds at the draws, so the native run passes it, and Lean does
not:

```console
$ uv run lanky check table.py
...
UNPROVED compressed_taylor at table.py:7: a step of its proof does not follow.

  table.py:20    yield by(recurrence[a - 2, b], compressed_taylor.conclusion[a - 2, b + 3], pde[a - 2, b])

  When a >= 2 (table.py:17), the step needs   R[a, b] == D[a, b]
    recurrence[a - 2, b]                       says   R[a, b] == -R[a - 2, b + 2]
    compressed_taylor.conclusion[a - 2, b + 3] says   R[a - 2, b + 3] == D[a - 2, b + 3]
    pde[a - 2, b]                              says   D[a, b] + D[a - 2, b + 2] == 0
  Left over:
      D[a - 2, b + 2] + R[a - 2, b + 3] - D[a - 2, b + 3] - R[a - 2, b + 2] == 0
  Fix: compressed_taylor.conclusion[a - 2, b + 2] makes the step follow (checked).
```

Python computes what is left over, from the facts at their points; Lean only
says that the step failed. The fix is the fact at another point, and
`(checked)` means Lean accepted the proof with it. Where no fact the step
cites works at any point, the report looks for one the proof can cite and
did not, a hypothesis, the conclusion at an earlier point or a claim the
proof cites elsewhere, and names it with the step as it would be written,
`Fix: yield by(...) (checked)`. And where nothing in the proof gets there,
it names the facts of `lanky.known` whose shape the step has, the term each
fits and its values there, as for a claim with no proof (see
[What lanky knows](#what-lanky-knows)):

```text
  No fact the proof cites gets there. What lanky knows of its shape:
    log_of_a_power rewrites log(x**n); here log(abs(alpha)**2), at x = abs(alpha), n = 2
    modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha
  Fix: cite one of them, after from lanky.known import log_of_a_power, modulus_squared; or split the step in two.
```

Where Lean is installed, lanky also reads each citation as it compiles the
proof, and names one that cannot apply before Lean is asked. A fact cited
where its condition does not hold is named, with the case:

```text
  table.py:20    yield by(stored[a, b], recurrence[a - 2, b], compressed_taylor.conclusion[a - 2, b + 2], pde[a - 2, b])

  stored[a, b] needs a < 2, and this case has a >= 2.
  Fix: cite stored in a case where a < 2, or split that case off first.
```

So is the conclusion cited below zero, here with the first case written `if
a < 1:`, which leaves `a = 1` to the recurrence:

```text
  table.py:20    yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)

  compressed_taylor.conclusion[a - 2, b + 2] is at a negative a when a = 1: split off a < 2 first.
  Fix: split off a < 2 first.
```

A broken proof fails the check, even for a claim lanky could prove alone.
Its row still reads `proved`, by lanky's own proof, and a `WARNING` line
says that your proof fails at its line and that lanky proved the claim
without it. The multipliers each step is closed with are kept, by the step,
beside the proof cache, so a check of a proof that has not changed runs no
sympy and sends Lean the same text; Lean checks them whatever they are.

### What lanky refuses

lanky refuses a proof it would have to guess at, at its line and before
Lean is asked, with the line to write:

- **A case with no closing line.** `continue`, a bare `return` or a path that
  just ends reads as "skipped":

  ```text
  UNPROVED compressed_taylor at table.py:7: a case of the proof has no closing line.

    table.py:18    continue

    when a < 2 (table.py:17), continue at line 18 ends the case with no closing line: close it with yield by() if it follows directly, or give its reasons, yield by(f, g)
    Fix: yield by().
  ```

- **A point the loop has not reached:**

  ```text
  UNPROVED compressed_taylor at table.py:7: the conclusion is cited where the loop has not reached.

    table.py:20    yield by(recurrence, compressed_taylor.conclusion[a + 1, b], pde)

    compressed_taylor.conclusion[a + 1, b] is not filled in yet when the loop is at (a, b)
    Fix: cite the conclusion at a point the loop has filled in, as compressed_taylor.conclusion[a - 1, b].
  ```

- **A part of the claim not addressed through its tree**, such as
  `compressed_taylor.domain`, `compressed_taylor[a, b]` or `.dom`:

  ```text
  UNPROVED compressed_taylor at table.py:7: the claim's tree is not used as lanky reads it.

    table.py:16    for a, b in compressed_taylor.domain:

    compressed_taylor.domain: a claim has no domain of its own; its conclusion has, addressed through the claim's tree as compressed_taylor.conclusion.domain
    Fix: compressed_taylor.conclusion.domain.
  ```

- **A claim that calls itself.** Recursion is not how lanky spells
  induction. Here `nicomachus` keeps `n` as a parameter, as lanky 0.5 had
  it, and calls itself at `n - 1`:

  ```text
  UNPROVED nicomachus at nicomachus.py:13: the claim calls itself in its own proof.

    nicomachus.py:19    return by(nicomachus(n - 1), gauss(n - 1))

    nicomachus(n - 1) at nicomachus.py:19 calls the claim in its own proof, and a claim does not call itself; to argue from an earlier case, put n in the conclusion's for, -> all(... for n in ...), and cite nicomachus.conclusion[n - 1]
    Fix: nicomachus.conclusion[n - 1].
  ```

  [A fact over a family](#a-fact-over-a-family) has the claim with `n` in
  its conclusion's `for`.

- **`return` in a proof that loops.** `return by(...)` would end the loop at
  its first point, so each case of a loop closes with `yield by(...)`.
- **A form of lanky 0.5**, each with the line to write: `@theorem` (*"write
  @claim"*), `@axiom`, a tuple returned as reasons, `x.equals(y, by=f)`, and a
  condition at a point in parentheses:

  ```text
  UNPROVED compressed_taylor at table.py:7: the proof is written in a form of lanky 0.5.

    table.py:20    yield by(recurrence(a - 2, b), compressed_taylor.conclusion[a - 2, b + 2], pde)

    recurrence(a - 2, b) is how lanky 0.5 cited a condition at a point; brackets give a point of its domain, and parentheses inputs to a claim
    Fix: recurrence[a - 2, b].
  ```

  The [CHANGELOG](../CHANGELOG.md) has the whole table, from 0.5 to 0.6.
- **A claim with no goal**, which is a condition: *"a claim needs a goal;
  write the proposition it claims as the return annotation, as in `-> n + 0
  == n`. A named set of assumptions with no goal is a @condition"*.

### What lanky knows

Some claims are one known fact away from a proof. sumpy evaluates the 2-D
Laplace kernel `log|alpha|` as half the log of `alpha` times its conjugate,
one logarithm and no square root, and `examples/log_of_the_modulus.py` says
why that is right:

```python
from lanky.known import log_of_a_power, modulus_squared


@claim
def log_of_the_modulus(alpha: Complex, nonzero: alpha != 0) -> (
    log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
):
    """log|alpha| with no square root: half the log of alpha times its conjugate."""
    assert log(abs(alpha)) == log(abs(alpha) ** 2) / 2, by(log_of_a_power)
    return by(modulus_squared)
```

Read aloud: "log|alpha| is half the log of |alpha| squared, by the log of a
power; the rest is the modulus squared." The step is known for the rest of
the proof, so `return by(modulus_squared)` is asked only for the rest of the
way, from where the step ended to the claim's other side. The claim has no
`for`, so it is proved without a loop, and closes with `return by(...)`. The
two facts come from `lanky.known`, under plain names. Each is a
claim stated in Python, like any other, with a docstring that cites the
Mathlib lemma it is:

```python
@claim
def log_of_a_power(x: Real, n: Nat) -> log(x**n) == n * log(x):
    """The log of a power is the exponent times the log (Mathlib: Real.log_pow)."""


@claim
def modulus_squared(z: Complex) -> real(z * conj(z)) == abs(z) ** 2:
    """z times its conjugate is |z| squared, a real number
    (Mathlib: Complex.mul_conj, Complex.normSq_eq_norm_sq)."""
```

Each fact's Lean proof is written once, against the statement lanky prints,
and kept in a table the Lean oracle reads (`lanky.oracles.known`), so the
library itself is checked like a file of yours, and with Mathlib every row is
proved:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check src/lanky/known.py
STATUS  EFFECTIVE  BY      WHERE         OWNER                         STATEMENT
------  ---------  ------  ------------  ----------------------------  ------------------------------------------
proved  tested     lean    known.py:96   log_of_a_power                x : Real, n : Nat |- log(x**n) == n*log(x)
tested  tested     python  known.py:96   log_of_a_power                the term computes what the annotations ...
...
proved  tested     lean    known.py:136  modulus_squared               z : Complex |- real(z*conj(z)) == abs(z)**2
...

40 facts: 20 proved, 20 tested
```

That is the command in a clone of the repository. Beside a lanky installed
from PyPI, a clone's `src/lanky/known.py` is refused, since the `lanky` it
sits in is not the `lanky` the command imported; check the installed file
instead:

```sh
lanky check "$(python -c 'import lanky.known; print(lanky.known.__file__)')"
```

`log_of_a_power` has no hypothesis that `x` is positive, because Lean's
logarithm is total and agrees with Python's wherever Python's has a value.
The claim keeps its own `nonzero`, which says where `log` means what its
reader thinks.

Lean's search alone does not prove `log_of_the_modulus`: no power is in
sight for the log of a power to apply to, which is why the proof asserts the
term where the two facts meet as a step. With the proof, and
Mathlib, the claim reads `proved`, and the two facts it cites are rows of the
file's ledger, marked with the module they come from, so that what the claim
rests on is in the ledger it is counted in:

```console
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/log_of_the_modulus.py
STATUS  EFFECTIVE  BY      WHERE                     OWNER               STATEMENT
------  ---------  ------  ------------------------  ------------------  -----------------------------------------------------------------------------------
proved  tested     lean    log_of_the_modulus.py:45  log_of_the_modulus  alpha : Complex | alpha != 0 |- log(abs(alpha)) == log(real(alpha*conj(alpha))) / 2
                                                                         by its proof, log_of_the_modulus.py:50-51: 2 steps, using log_of_a_power
                                                                           and modulus_squared from lanky.known
tested  tested     python  log_of_the_modulus.py:45  log_of_the_modulus  the term computes what the annotations compute
proved  tested     lean    lanky.known               log_of_a_power      x : Real, n : Nat |- log(x**n) == n*log(x)
tested  tested     python  lanky.known               log_of_a_power      the term computes what the annotations compute
proved  tested     lean    lanky.known               modulus_squared     z : Complex |- real(z*conj(z)) == abs(z)**2
tested  tested     python  lanky.known               modulus_squared     the term computes what the annotations compute

6 facts: 3 proved, 3 tested
```

A cited claim is restated in the citing proof's Lean by the text its own
command proved, `Lanky.log_of_a_power.as_cited`, byte for byte, never printed
again for the citation. Where a claim has no proof and Lean found none alone,
`lanky check` names the known facts whose shape occurs in the claim, the term
each fits, and its values there:

```text
NOT PROVED log_of_the_modulus at log_of_the_modulus.py:45: alpha : Complex | alpha != 0 |- log(abs(alpha)) == ...
  Lean found no proof alone. What lanky knows of its shape:
    modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha
  A proof cites them by name: from lanky.known import modulus_squared
```

### A fact over a family

A fact can be about any terms: `one_more_term` says that a sum to `n + 1` is
the sum to `n` plus its last term, whatever the terms are, as a fact over a
family `f`:

```python
@claim
def one_more_term(f: Fn[Nat, Real], n: Nat) -> (
    sum(f[k] for k in Fin[n + 1]) == sum(f[k] for k in Fin[n]) + f[n]
):
    """The sum to n + 1 is the sum to n plus its last term (Mathlib: Finset.sum_range_succ)."""
```

`examples/nicomachus.py` proves Nicomachus's theorem with it, by the
induction a textbook writes:

```python
from lanky.known import one_more_term


@claim
def nicomachus() -> all(
    sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2 for n in Nat
):
    """The sum of the first cubes is the square of the sum of the first numbers."""
    for n in nicomachus.conclusion.domain:
        if n == 0:
            yield by()
        else:
            assert (
                sum(i**3 for i in Fin[n + 1])
                == sum(i**3 for i in Fin[n]) + n**3
                == sum(i for i in Fin[n]) ** 2 + n**3
                == (sum(i for i in Fin[n]) + n) ** 2
                == sum(i for i in Fin[n + 1]) ** 2
            ), by(one_more_term, nicomachus.conclusion[n - 1], gauss(n - 1))
            yield by()
```

Read it aloud: "For each n, in order. At n = 0, it follows directly.
Otherwise, the cubes to n + 1 sum to the cubes to n plus n cubed; that is the
square of the sum to n, plus n cubed; that is the square of the sum to n plus
n; and that is the square of the sum to n + 1: by one more term, nicomachus
at n − 1, and Gauss for n − 1."

`n` is the variable of the conclusion's `for`, not a parameter, because the
proof argues from smaller `n`: that is where a variable you induct on
belongs. `gauss` keeps `n` as a parameter, and `gauss(n - 1)` is that claim
for the input `n - 1`. The calculation is one `assert` of Python's own
chained comparison; its two ends are the conclusion's two sides, so the case
closes with `yield by()`, nothing to add.

`one_more_term` is cited by its name alone, and lanky finds the family and the
point from the link each citation supports: `f` is `i ↦ i**3` at the first
link and `i ↦ i` at the last, both at `n`. The links name their sums' index
`i` and the fact names it `k`, which is the reader's choice and no
difference. At `n - 1` the fact's left side is a term of the first link too,
but only at `n` are both of its sides, so `n` is the point. To say the family
yourself, give it as an input, written as a `lambda`:
`one_more_term(lambda i: i**3, n)`.
`--steps` shows the points lanky found:

```text
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check --steps nicomachus examples/nicomachus.py
...
STEPS nicomachus at nicomachus.py:66, as its proof says them:
  the claim, induction on n, 2 cases, 4 steps, 1 routine, using one_more_term and gauss
  nicomachus.py:75  otherwise:  sum(i**3 for i in Fin(n + 1)) == sum(i**3 for i in Fin(n)) + n**3  by one_more_term at (lambda i: i**3, n), the claim at (n - 1), gauss at (n - 1) and one_more_term at (lambda i: i, n)
                                                              == sum(i for i in Fin(n))**2 + n**3
                                                              == (sum(i for i in Fin(n)) + n)**2
                                                              == sum(i for i in Fin(n + 1))**2
```

The sums of `lanky.known` are stated over the reals, and these are sums of
integers. An equation between integers holds where its cast into the reals
does, so lanky states the fact at its point over the integers, as the step
reads it, and Lean shows it from the fact over the reals through the cast:
`one_more_term`, `geometric_sum` and the other sums apply to sums of `Nat`s
and `Int`s as they are. With Mathlib all three claims of the file read
`proved`, `gauss` and `cubes` by lanky's own induction:

```text
$ LANKY_LEAN_MATHLIB=~/mathlib uv run lanky check examples/nicomachus.py
STATUS  EFFECTIVE  BY      WHERE             OWNER          STATEMENT
------  ---------  ------  ----------------  -------------  -----------------------------------------------------------------------------------------------
proved  tested     lean    nicomachus.py:61  gauss          n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)
tested  tested     python  nicomachus.py:61  gauss          the term computes what the annotations compute
proved  tested     lean    nicomachus.py:66  nicomachus     forall n in Nat. sum(i**3 for i in Fin(n + 1)) == sum(i for i in Fin(n + 1))**2
                                                            by its proof, nicomachus.py:71-82:
                                                              induction on n, 2 cases, 4 steps, 1 routine, using one_more_term and gauss
tested  tested     python  nicomachus.py:66  nicomachus     the term computes what the annotations compute
proved  tested     lean    nicomachus.py:85  cubes          n : Nat |- 4*sum(i**3 for i in Fin(n + 1)) == (n*(n + 1))**2
tested  tested     python  nicomachus.py:85  cubes          the term computes what the annotations compute
proved  tested     lean    lanky.known       one_more_term  f : Fn[Nat, Real], n : Nat |- sum(f[k] for k in Fin(n + 1)) == sum(f[k] for k in Fin(n)) + f[n]
tested  tested     python  lanky.known       one_more_term  the term computes what the annotations compute

8 facts: 4 proved, 4 tested
```

## What to try next

- Write a false claim and check it. The status is `refuted`, the
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
- Leave off a claim's return annotation. `@claim` raises `TypeError`
  where the function is defined, because a claim needs a goal, and names
  `@condition`, which is what a named set of assumptions with no goal is.
  `lanky check` reports the file as one that does not import.
- Call one of Python's builtins in a claim. At numbers it is Python's:
  `def half() -> round(0.5) == 1` is `0 == 1`, answered while the annotation
  is read, and the row reads `refuted`, as running the file would say. At a
  variable it is refused where the claim is defined, naming it:
  `def unit(x: Real) -> abs(complex(x, 1)) >= 1` raises `TypeError`,
  `complex(x, 1) applies Python's complex to a symbolic value`, since lanky
  has no term for it. (`max` and `min` of terms are lanky's own, and read as
  written.) `def wrong(x: int) -> x - 1 >= 0` is refused too, naming `Int` and
  `Nat`: `int` is Python's type, and not a sort. So is `f: Fn[Fin[n], float]`,
  naming `Real`.
- Look a point up in a dict: `def looked_up(n: Nat, f: Fn[Fin[n], Nat]) ->
  all(f(i) * 0 == {0: 1}.get(i, 0) for i in Fin[n])`. A dict finds a key by
  its hash, and a term's hash is its structure's, so the lookup would answer
  `0`, as if `i` were never `0`, and the claim would be `f(i)*0 == 0`. A term
  is unhashable to an annotation's own code instead, so the claim is
  refused where it is defined (`i was hashed by the annotation, as a dict or
  a set lookup or display there hashes its keys`), and so is `i in {0, 1}`.
  A table indexed by a point is a family, with hypotheses that give its
  values. Put the lookup in a function the claim calls, and the refusal does
  not see it; the reading's check does, as
  [Check the reading](#check-the-reading) shows.
- Misspell a name: `def typo(n: Nat) -> n + m >= n`. No parameter binds `m`,
  so no draw gives it a value, and the tester draws nothing; Lean is not
  handed it either. The row reads `assumed`, and the tester says why under
  the table:

  ```text
  DECLINED typo at typo.py:7: n : Nat |- n + m >= n
    property-test: the statement mentions m, which no parameter or binder of it binds, so no draw gives it a value and the statement cannot be tested; a name misspelt, not imported, or meant as a parameter is the usual cause
  ```

  A misspelt sort, `f: Fn[Fin[n], Flaot]`, is named the same way. Under
  `pytest` such a claim fails, naming the name.
- Choose a branch inside a quantifier: `all((f(i) if i < 3 else -1) >= 0 for
  i in Fin[n])`. The conditional asks `i < 3` for a truth value, which lanky
  has only where it records a guard, so it is refused where the claim is
  defined, as `not` in a body and a comparison of two tuples are. A
  condition on the points goes in the generator's `if` clause, written with
  `&`, `|` and `~`.
- Make two claims from one definition, with a function that decorates a
  nested `def` each time it is called. A fact id names a definition, so both
  claims have one id; the first is checked and stays in the table, and
  `lanky check` names the others in a `DUPLICATE` block under it, unchecked,
  and exits 1. A factory that wants several claims gives each function a
  `__qualname__` of its own before it decorates it.
- Write a claim whose hypotheses no sample can satisfy, such as
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
  is 0. Under `pytest` a claim with unsatisfiable hypotheses is reported as
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
  such a claim is skipped, with the guard in the reason.
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
| `@claim`, `@claim(cite=...)`, `Claim` and `CitedClaim`, and the refusals of lanky 0.5's `@theorem` and `@axiom` | `src/lanky/theory.py` |
| `@condition`, `with` in its three forms, `name.conditions` and `ConditionNotMet` | `src/lanky/conditions.py` |
| `by(...)`, the claim's tree (`name.conclusion`, `.domain`, a point) and the refusals of lanky 0.5's proof forms | `src/lanky/surface.py` |
| `@rewrite`, `Rewrite`, `RewriteTerm` and `rewrite_fact` | `src/lanky/rewrites.py` |
| samplers and the property tester | `src/lanky/testing.py` |
| a claim's reading, checked by running its annotations again at drawn values | `src/lanky/faithful.py` |
| where the readings still differ: division by zero, `log`, `sqrt` | `src/lanky/semantics.py` |
| the Lean printer, core Lean's dialect and Mathlib's | `src/lanky/lean.py` |
| Mathlib mode: the pinned project and its setup | `src/lanky/mathlib/`, `src/lanky/mathlib-project/` |
| induction over families: the search for a certificate, and the script Lean checks | `src/lanky/induction.py`, `src/lanky/oracles/lean.py` |
| exchanging finite sums: the order Python finds, and the script Lean checks | `src/lanky/sums.py`, `src/lanky/oracles/lean.py` |
| the proof lanky found, said back in Python: `--proofs` and `--steps` | `src/lanky/outline.py` |
| the oracles | `src/lanky/oracles/` |
| `check_path` and the CLI | `src/lanky/check.py`, `src/lanky/cli.py` |
| written proofs: the trace, the native run, the Lean they compile to, and the report at the Python line | `src/lanky/proofs/` |
| a family over the naturals filled in from its hypotheses, for the native run | `src/lanky/proofs/filled.py` |
| a written proof, lanky #140's `every_box` | `examples/every_box.py` |
| the CFL condition, named once, and what holds under it | `examples/upwind.py` |
| the pytential demonstration, and its rule engine | `examples/pytential_skie.py`, `examples/layer_potentials.py` |
| the bridge to sympy, and the CAS oracle | `src/lanky/cas.py`, `src/lanky/oracles/cas.py` |
| the sumpy demonstration, and its `mpmath` oracle | `examples/sumpy_recurrence.py` |
| sum factorization on hexahedra, grudge's tensor-product operators | `examples/sum_factorization.py` |
| the line-Taylor expansion pytential's QBX evaluates with | `examples/line_taylor.py` |
| what lanky knows: library facts under plain names, and their Lean proofs | `src/lanky/known.py`, `src/lanky/oracles/known.py` |
| the axiom audit, and the screen for Lean text lanky did not write | `src/lanky/audit.py` |
| the known facts that fit a claim, by shape | `src/lanky/suggest.py` |
| `log|alpha|` with no square root, by two known facts | `examples/log_of_the_modulus.py` |
| Nicomachus's theorem, by a known fact over a family, and the same taken on a citation | `examples/nicomachus.py`, `examples/citation.py` |
