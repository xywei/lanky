# lanky

Python for math you can check.

lanky is a Python-hosted proof language with Lean 4 and Mathlib as the platform,
shaped like mypy: hints are inert, the body is executable Python, and an external
command does the checking. Theorems are typed Python functions (variables are
parameters, hypotheses are parameters annotated with propositions, the goal is the
return annotation); proofs are Python programs that drive Lean tactics over a live
goal; the recorded tactic script is the certificate; under plain `python` the
theorems run as property tests. Lean is the platform, lanky is a hosted language on
it (the Kotlin/JVM relationship), so all of Mathlib and every Lean tactic are
reachable. lanky itself is a thin plugin host: it defines a ledger of facts (each
with a status: tested, decided, proved, certified, assumed) and four plugin
interfaces (theories, oracles, executors, CLI verbs).

## Status

Work in progress. This is a placeholder release to reserve the name. The
architecture is prepared, not implemented: the ledger and the plugin protocols are
written down, and nothing behind them works yet.

The sister project [loopty](https://github.com/xywei/loopty) (loop + ty for types;
a typed polyhedral layer over loopy, with isl as an oracle and loopy as a code
generator) will be lanky's first plugin.

## Name

- "Lean Annotations Natively Kernel-check Your math".
- LANK + y, where LANK = Lean Annotations, Native Kernel — and *lank* means long
  and thin, next to *lean*.

## Planned architecture

- A ledger of facts, each carrying a status: tested, decided, proved, certified,
  assumed.
- Four plugin interfaces: theories (decorators that turn Python objects into
  facts), oracles (establish facts and report a trust class), executors (run a
  decorated object), and verbs (CLI subcommands).
- A live Lean session via PyPantograph as the Lean oracle.
- A property-test executor, so theorems run as tests under plain `python`.
- A generated Lean file plus a source map back to the Python program as the
  certificate.
- The command line: `lanky check | certify | watch | shell`.

## Install

```sh
uv add lanky
```

```sh
pip install lanky
```

Nothing works yet — installing this release gets you a `lanky` command that prints
its own version and this repository's URL.

## AI disclosure

This project is developed with substantial assistance from AI coding agents
(Anthropic's Claude, via Claude Code). Design, direction, and review are by Xiaoyu
Wei. Generated text and code are reviewed before release, but readers should assume
AI involvement throughout.

## License

MIT. See [LICENSE](LICENSE).
