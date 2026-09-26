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
[docs/quickstart.md](docs/quickstart.md) has the untrimmed table.)

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
  it can do.

## Status

This is `0.1.0.dev0`, a development release. The core works; the edges are
sharp.

**Works.**

- `lanky check FILE [--json OUT] [--verbose]`, exit code 1 on any refutation
  or vacuous claim. Each refuted fact is repeated under the table with its
  counterexample, its witness and its reason, the three standard provenance
  keys, read the same way whichever oracle or plugin refuted it; or with
  `no witness recorded` when it carries none of them.
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
  its own. `--json` carries `rests_on`, `effective` and `under`. An id no
  fact in the ledger has counts as an assumption, and `lanky check` names it
  under the table. `examples/nicomachus.py` is the worked case.
- The ledger: six statuses, provenance, JSON, a rendered table.
- The prelude: `Nat`, `Int`, `Real`, `Complex`, `Bool`, `Prop`, `Fin[n]`,
  `Fn[A, B]`, refinement by `T & prop`, exactness classes; and `lanky.exp`,
  `lanky.log` and `lanky.sqrt`, which build a term from a term and are
  `math`'s (or `cmath`'s) functions at a number.
- Property testing, including satisfying a definitional hypothesis by
  construction rather than rejection sampling, so a theorem about a scan is
  genuinely tested and not vacuously passed. A synthesized value has to land
  inside the family's codomain, so an unsatisfiable definition drops the draw
  rather than putting a point outside its sort into it. A pass over zero valid
  draws is never reported as `TESTED`: the fact stays `ASSUMED` and its
  provenance says `untested` and why.
- Refusing the ways a statement can silently mean something other than what was
  written: a guard joined with Python's `or`, an `and` or `or` used as a value,
  a `not` in a guard, and an `if` statement inside a function an annotation
  calls. The connectives are `&`, `|` and `~`.
- One reading of arithmetic for every oracle. `Nat` means an integer that is
  not negative, and the Lean printer says so: a natural is an `Int` with
  `0 ≤ n` as a hypothesis, and `//` and `%` are `Int.fdiv` and `Int.fmod`,
  which round the way Python's do. What Lean proves is what the property
  tester tests, so a claim is refuted, or not, whether or not Lean is
  installed: `n - 1 >= 0` over `Nat` is refuted everywhere, and `n - 1 <= n`
  is still proved where Lean is.
- Vacuous claims are caught. When no draw satisfies a fact's hypotheses, the
  stronger oracles are asked whether the hypotheses alone prove `False`. If one
  does, the row reads `proved (vacuous)` and `lanky check` exits 1: the claim
  is true and says nothing, which is usually a mistake in the hypotheses. If
  none can, a warning says the hypotheses were never satisfied.
- A statement the annotation already answered is a claim like any other:
  `-> 1 == 2` is `refuted`, `lanky check` prints why under the table, and it
  exits 1 on it.
- The Lean oracle over core Lean 4, with a tactic ladder and an induction
  strategy read off the term. No Mathlib is fetched or needed. CI runs the
  suite against Lean v4.29.1 as well as without Lean.
- Mathlib mode, opt-in: `LANKY_LEAN_MATHLIB` names a Lake project with
  Mathlib fetched, and `python -m lanky.mathlib DIR` sets one up from the
  project lanky ships, pinned to Mathlib v4.29.1 and every dependency at a
  commit. The oracle imports Mathlib once and prints statements over `Real`
  and `Complex` (`ℝ` and `ℂ`), sums (`∑` over `Finset.Ico`), absolute values,
  true division, floats as the rationals Python holds, and `exp`, `log` and
  `sqrt` (`Real.exp` and the rest). The ladder goes on to `norm_num`,
  `positivity`, `ring`, `field_simp`, `linarith` and `nlinarith`, and to an
  induction for a sum whose bound a natural parameter sets, so Gauss's sum in
  `examples/gauss.py` reads `proved lean`. With the variable unset, the oracle
  is the core one, exactly. [docs/quickstart.md](docs/quickstart.md#prove-it-with-mathlib)
  walks through it.
- Plugin discovery by entry point, and `lanky <verb>` from the registry.
- The pytest plugin.

**Partial.**

- The property tester satisfies hypotheses of the shape `f(i) == e` by
  assignment and rejection-samples everything else, so an awkward hypothesis can
  end with no valid draws. The fact is then `ASSUMED`, never falsely `TESTED`.
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
  its hypotheses.
- Python's `and` between two propositions in a generator's `if` clause happens
  to produce the conjunction that was written, because of how CPython compiles
  a comprehension filter, so it is not refused. It cannot be told apart from
  two `if` clauses in the bytecode. Write `&`.
- The Lean induction strategy is a shape matcher, not proof search. A statement
  needing a different induction or a lemma falls through to the tester;
  `lanky.oracles.lean.use_tactic` pins a script by hand.
- The Lean printer covers core Lean: `Sum`, `Abs`, `Real`, true division and
  an exponent that could be negative raise rather than emit source Lean would
  reject. In Mathlib mode all but the last are printed, and what is still
  declined is a sum over `Nat`, a `Fin` with a real bound, a floor division or
  a remainder of a real, an order between complex numbers and a complex
  logarithm or square root: each would be printed with a meaning Python does
  not give it.
- Over `Real` and `Complex` the readings are not one. The tester computes in
  floating point (with fractions for `Real.exact`) and Lean over `ℝ` and `ℂ`,
  so an identity that holds only up to rounding, such as
  `exp(x + y) == exp(x) * exp(y)`, is refuted without Mathlib and proved with
  it. Where Lean is total and Python raises (a division by zero, the logarithm
  of zero, the square root of a negative number), the fact carries a note in
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
  statement, the fact stays `ASSUMED` with the reason. Over `Fin` the domain is
  enumerated and both answers hold. A quantifier over a refined domain `T & p`,
  which a plugin building terms by hand can write, ranges over the points of
  `T` where `p` holds, as the Lean printer reads it: enumerated when `T` is,
  filtered draws when it is sampled.

**Not yet.**

- `CERTIFIED`. The Lean source and the tactic script are in provenance; nothing
  replays them under a checker yet.
- Real analysis beyond what the ladder finds: Mathlib mode states it, and the
  ladder is a fixed set of tactics, not proof search, so a statement that needs
  a lemma by name falls through to the tester (`use_tactic` pins a script).
- A proof scripting surface: today a proof is a tactic ladder lanky drives, not a
  Python program over a live goal.
- Anything on PyPI above the 0.0.1 placeholder.

## Install

```sh
uv add lanky
```

```sh
pip install lanky
```

The Lean oracle is an extra, because it pulls a sizable dependency tree and needs
a Lean toolchain on `PATH`:

```sh
uv add "lanky[lean]"
```

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
Mathlib fetched, about 7 GB on disk:

```sh
uv run python -m lanky.mathlib ~/mathlib    # writes the pinned project, runs `lake exe cache get`
export LANKY_LEAN_MATHLIB=~/mathlib
```

The command never builds Mathlib from source; it fetches the compiled files
Mathlib publishes, keeping the packed downloads in `MATHLIB_CACHE_DIR`
(default `~/.cache/mathlib`). The first session of a process imports Mathlib, which takes
seconds and about 1.5 GB of memory.

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
uv sync --group dev --extra lean
uv run pytest -q
uv run ruff check .
```

CI runs the suite twice. The main job, on Python 3.12 and 3.13, installs no
Lean and sets `LANKY_LEAN_DISABLE=1`, so it sees what a user without the extra
sees. The job named `test with Lean` installs elan, Lean v4.29.1 and the `lean`
extra, caches the toolchain and the built REPL between runs, and runs the same
suite with the oracle on and `LANKY_LEAN_TEST_REQUIRED=1`, under which a Lean
test that cannot get a Lean session fails instead of skipping. It then runs
`lanky check examples/gauss.py` and checks that the `proved lean` row at the top
of this page is a row the check printed. The suite compares the rest of that
table, and the quickstart's, with the real output in both jobs, reading the
row as `tested property-test` in the main one.

A third job, `test with Lean and Mathlib`, is optional: it may fail without
failing the run, since it depends on fetching Mathlib from outside GitHub. It
sets up the pinned project with `python -m lanky.mathlib`, caching Mathlib's
compiled files between runs, runs `tests/test_mathlib.py` with the project
required, and checks that `lanky check examples/gauss.py` proves both rows.
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
pymbolic subclasses, and comparison operators on them build propositions.

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
`decision-procedure` (isl) > `test` (property test). Each oracle answers
`can_establish(fact)`; `check_path` offers each fact to the strongest one that
says yes and stops at the first answer. A fact nobody establishes is `ASSUMED`,
which is not a failure. An oracle that cannot answer declines, so a timeout is
never read as a counterexample.

Decorators are inert and registering: `@theorem` returns a callable object that
runs natively and puts itself in the registry. `lanky check FILE` imports the
file and reads the registry, keeping the claims defined in that file and none
from the modules it imports; `lanky check a.py b.py` checks both, each for its
own. No environment variable changes what the code means.

## Name

- "Lean Annotations Natively Kernel-check Your math".
- LANK + y, where LANK = Lean Annotations, Native Kernel, and *lank* means long
  and thin, next to *lean*.

## Documentation

- [docs/quickstart.md](docs/quickstart.md): the worked file, end to end, with
  the output the commands actually print, and a second one with an axiom.
- [CHANGELOG.md](CHANGELOG.md).
- [loopty](https://github.com/xywei/loopty): the sister project and lanky's
  first plugin: a typed polyhedral layer over loopy, where the facts are about
  loop kernels and isl decides them.

## AI disclosure

This project is developed with substantial assistance from AI coding agents
(Anthropic's Claude, via Claude Code). Design, direction, and review are by Xiaoyu
Wei. Generated text and code are reviewed before release, but readers should assume
AI involvement throughout.

## License

MIT. See [LICENSE](LICENSE).
