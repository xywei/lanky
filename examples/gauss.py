"""Two worked theorems: what a lanky file looks like and what it does.

Run it three ways.

``python examples/gauss.py``
    The theorems run as property tests and the file prints what the draws
    found. Nothing but lanky and numpy is needed.

``uv run lanky check examples/gauss.py``
    The same file is imported, every claim becomes a fact, the oracles are
    tried strongest first, and the ledger is printed with the decider of each
    fact and its source location.

``uv run pytest examples/gauss.py``
    The theorems are collected as test items by lanky's pytest plugin.

``gauss`` is Gauss's schoolboy sum, and shows a reduction over an index type
whose bound is symbolic. ``scan_monotone`` is the theorem the sparse
matrix-vector demo needs: it says that the offsets an exclusive prefix scan
produces are monotone, and it is written the way a kernel presents its results,
with the output array as a parameter (``off``) and the recurrence as a
hypothesis rather than as a definition.
"""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Fn, Nat


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``.

    The body is a proof script for an oracle and is never executed by lanky.
    """


@theorem
def scan_monotone(
    n: Nat,
    cnt: Fn[Fin[n], Nat],
    off: Fn[Fin[n + 1], Nat],
    h0: off(0) == 0,
    hs: all(off(r + 1) == off(r) + cnt(r) for r in Fin[n]),
) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
    """The offsets of an exclusive scan over counts are monotone.

    ``cnt`` and ``off`` are families rather than arrays: a theorem talks about
    the data, and a kernel that writes ``off`` supplies the same hypotheses as
    its postcondition. Because the counts are naturals, nothing decreases.
    """


def main() -> int:
    """Run both theorems as property tests and report what the draws found."""
    print(f"gauss at n = 4: {gauss(n=4).holds}")
    # A family parameter takes a sequence: the scan of the counts [2, 1, 4].
    scanned = scan_monotone(n=3, cnt=[2, 1, 4], off=[0, 2, 3, 7])
    print(f"scan_monotone at n = 3: {scanned.holds} (hypotheses {scanned.hypotheses})")
    for statement in (gauss, scan_monotone):
        print()
        print(f"{statement.__name__}: {statement.statement}")
        report = statement.report(n=50)
        print(
            f"  {'ok' if report.ok else 'REFUTED'} "
            f"after {report.valid} valid draws of {report.samples}"
        )
        if report.counterexample:
            print(f"  counterexample: {report.counterexample}")
        if report.reason:
            print(f"  {report.reason}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
