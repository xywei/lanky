"""The ``lanky`` command: a host for verbs.

The design idea. The CLI owns argument parsing and plugin discovery and nothing
else. ``check`` is built in; every other verb arrives through the
``lanky.verbs`` entry-point group, which is how ``loopty run`` becomes a
subcommand of ``lanky`` without lanky knowing what loopty is.

``check`` exits 1 when any fact is ``REFUTED``, so it works in CI: a refuted
fact is a broken claim, while an assumed one is a claim nobody got to.

One more thing is printed under the table and does not change the exit code: a
statement whose Lean reading and whose Python reading disagree, or whose Python
reading could not be run at all (subtraction over ``Nat``, division over
``Int``, division by zero; see :mod:`lanky.semantics`). The fact keeps the
status its oracle gave it, because the oracle was right about the statement it
read; what is reported is that there are two readings and they are not the same
statement.
"""

from __future__ import annotations

import argparse
import traceback
from pathlib import Path
from typing import Any

from lanky.check import check_path, oracle_lines
from lanky.ledger import Status
from lanky.plugins import registry

__all__ = ["CheckVerb", "build_parser", "main"]


class CheckVerb:
    """``lanky check FILE``: print the ledger of everything the file claims."""

    name = "check"
    help = "check a file: print every obligation and who decided it"

    def add_arguments(self, parser: argparse.ArgumentParser, /) -> None:
        """Declare the arguments of ``check``."""
        parser.add_argument("file", help="the Python file to check")
        parser.add_argument("--json", metavar="OUT", help="also write the ledger as JSON")
        parser.add_argument(
            "--verbose",
            action="store_true",
            help="list the oracles and the facts as they are collected",
        )

    def run(self, args: argparse.Namespace, /) -> int:
        """Check the file, print the ledger, and report refutations.

        Exit code 1 on any refutation, and 1 with the traceback when the file
        itself cannot be imported, because a file that does not import is a
        broken claim too. Exit code 2 when there is no such file, which is a
        mistake in the command rather than in the file. A semantics
        disagreement is printed but does not fail the check: nothing was
        refuted, two readings differ.
        """
        if args.verbose:
            for line in oracle_lines():
                print(line)
            print()
        try:
            ledger = check_path(args.file, verbose=args.verbose)
        except FileNotFoundError:
            print(f"lanky check: no such file: {args.file}")
            return 2
        except Exception:  # noqa: BLE001 - the file is the user's, so show why
            print(f"lanky check: {args.file} could not be imported")
            print(traceback.format_exc().rstrip())
            return 1
        print(ledger.render())
        if args.json:
            Path(args.json).write_text(ledger.to_json(), encoding="utf-8")
        for fact in ledger:
            disagreement = fact.provenance.get(
                "semantics_disagreement"
            ) or fact.provenance.get("semantics_undecided")
            if not disagreement:
                continue
            print()
            print(f"SEMANTICS {fact.owner} at {fact.where}: {disagreement}")
            counterexample = fact.provenance.get("semantics_counterexample")
            if counterexample:
                print(f"  counterexample: {counterexample}")
            for note in fact.provenance.get("semantics", ()):
                print(f"  {note}")
        refuted = ledger.by_status(Status.REFUTED)
        if refuted:
            print()
            for fact in refuted:
                print(f"REFUTED {fact.owner} at {fact.where}: {fact.statement}")
                if "counterexample" not in fact.provenance:
                    continue
                witness = fact.provenance["counterexample"]
                print(f"  counterexample: {witness}")
                if not witness and fact.provenance.get("reason"):
                    # A closed statement such as ``-> 1 == 2`` is false at no
                    # assignment in particular. The empty witness is the honest
                    # one and says nothing on its own, so the reason follows it.
                    print(f"  {fact.provenance['reason']}")
            return 1
        return 0


def build_parser() -> tuple[argparse.ArgumentParser, dict[str, Any]]:
    """Build the parser from the built-in verb and every registered one."""
    from lanky import __version__

    registry.load_entry_points()
    parser = argparse.ArgumentParser(prog="lanky", description="Python for math you can check.")
    parser.add_argument("--version", action="version", version=f"lanky {__version__}")
    subparsers = parser.add_subparsers(dest="verb")
    verbs: dict[str, Any] = {}
    for verb in [CheckVerb(), *registry.verbs]:
        if verb.name in verbs:
            continue
        verbs[verb.name] = verb
        verb.add_arguments(subparsers.add_parser(verb.name, help=verb.help))
    return parser, verbs


def main(argv: Any = None) -> int:
    """Run a verb and return its exit code."""
    parser, verbs = build_parser()
    args = parser.parse_args(argv)
    if not args.verb:
        parser.print_help()
        return 0
    return verbs[args.verb].run(args)


if __name__ == "__main__":
    raise SystemExit(main())
