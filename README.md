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
  them will tell you, for one file, which is which.
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

- `lanky check FILE [--json OUT] [--verbose]`, exit code 1 on any refutation.
- `@theorem`: statement from the signature, `.statement`, `.term`, `.fact()`,
  `.test()`, `.report()`, `.lean()`; callable on concrete values.
- The ledger: six statuses, provenance, JSON, a rendered table.
- The prelude: `Nat`, `Int`, `Real`, `Bool`, `Prop`, `Fin[n]`, `Fn[A, B]`,
  refinement by `T & prop`, exactness classes.
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
- A note in the provenance when Lean's reading of a statement and lanky's
  Python reading can differ (`Nat` subtraction, `Int` division, division by a
  divisor that may be zero), and, when a stronger oracle established such a
  fact, what the sampled reading found: the counterexample, or that it could
  not be run at all.
- A statement the annotation already answered is a claim like any other:
  `-> 1 == 2` is `refuted` with an empty counterexample and `lanky check` exits
  1 on it.
- The Lean oracle over core Lean 4, with a tactic ladder and an induction
  strategy read off the term. No Mathlib is fetched or needed. CI runs the
  suite against Lean v4.29.1 as well as without Lean.
- Plugin discovery by entry point, and `lanky <verb>` from the registry.
- The pytest plugin.

**Partial.**

- The property tester satisfies hypotheses of the shape `f(i) == e` by
  assignment and rejection-samples everything else, so an awkward hypothesis can
  end with no valid draws. The fact is then `ASSUMED`, never falsely `TESTED`.
- The two readings of a statement are detected and reported, not reconciled.
  A statement that subtracts over `Nat` can be `PROVED` in Lean and false when
  sampled, and one that divides by zero is a theorem in Lean and a
  `ZeroDivisionError` in Python; the ledger says both and the exit code stays
  0. See `src/lanky/semantics.py` for why truncating the evaluator instead
  would be wrong.
- Python's `and` between two propositions in a generator's `if` clause happens
  to produce the conjunction that was written, because of how CPython compiles
  a comprehension filter, so it is not refused. It cannot be told apart from
  two `if` clauses in the bytecode. Write `&`.
- The Lean induction strategy is a shape matcher, not proof search. A statement
  needing a different induction or a lemma falls through to the tester;
  `lanky.oracles.lean.use_tactic` pins a script by hand.
- The Lean printer covers core Lean: `Sum`, `Abs`, `Real` and true division
  raise rather than emit source Lean would reject.
- A family prints as a total function, so every application of one has to be
  shown in bounds before the statement can go to Lean. The check is affine
  arithmetic over the enclosing binders, not a solver, so an argument it cannot
  settle is declined rather than assumed: the statement falls through to the
  tester, which is a proof fewer and never a proof too many.
- Sampling quantifiers over `Nat` draws a handful of points. That is evidence of
  the weakest kind and the ledger says so. It is evidence in one direction only:
  a `forall` that a draw breaks is really refuted, but an `any` that no draw
  witnesses is undecided, not false, so the tester declines the draw and the
  fact stays `ASSUMED`. Over `Fin` the domain is enumerated and both answers
  hold.

**Not yet.**

- `CERTIFIED`. The Lean source and the tactic script are in provenance; nothing
  replays them under a checker yet.
- Mathlib, and with it reductions and real analysis in Lean.
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

Without the extra, every Lean test skips with a one-line reason and the weaker
oracles do the work. `lanky check --verbose` prints each oracle and whether it
is available. The first use builds a Lean REPL, which takes about a minute and
the network, and caches it in `$XDG_CACHE_HOME/lanky/lean-repl`
(`~/.cache/lanky` by default), outside the virtual environment so that a
reinstall does not throw it away. Useful environment variables:
`LANKY_LEAN_DISABLE=1` makes the oracle a declared no-op (the main CI job sets
it), `LANKY_LEAN_VERSION` pins a toolchain and skips the probe,
`LANKY_LEAN_CACHE_DIR` moves the cache, and `LANKY_LEAN_TIMEOUT` caps each
tactic attempt.

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

A file that carries statements needs `from __future__ import annotations` and a
ruff `F821` per-file ignore, because a size such as `n` is a symbolic variable
lanky invents while evaluating the annotation and has no binding a static checker
can see.

## Architecture

Four ideas, and everything else is one of them.

**Terms.** pymbolic is the expression language, the same one loopy uses, so a
statement and a generated kernel cannot drift apart in translation. lanky adds
`Forall`, `Exists`, `Sum` and `Abs` as pymbolic subclasses, and comparison
operators on them build propositions.

**Facts and the ledger.** A `Fact` is a statement, a term, a status, a decider,
a provenance and a source location. `Status` is `tested, decided, proved,
certified, assumed, refuted`. The ledger is the output of a check and the thing
a reviewer reads.

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
  the output the commands actually print.
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
