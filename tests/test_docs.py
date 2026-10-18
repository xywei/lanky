"""The quickstart's named conditions and written proof, as a reader writes them, are real runs.

The quickstart has a reader write five small files: ``upwind_step.py``, the
CFL story, red and then green; ``between.py``, the three things a ``with``
assumes; and ``table.py``, a written proof over tables of integers, which
core Lean checks. Each file is written here from the quickstart's own
snippets, and each block the quickstart shows under it is held to what
``lanky check`` prints: the table, the line that says what the native run
did without Lean, a step written wrong, and each refusal, at its line.

The CFL story, the forms and every refusal read the same with core Lean and
without it, so they run either way. The proof's ``proved`` row and the
report of a step that does not follow need Lean, and skip without it, or
fail where ``LANKY_LEAN_TEST_REQUIRED`` says Lean was promised.
"""

from __future__ import annotations

import os
from collections.abc import Iterator
from pathlib import Path

import pytest

from lanky import cli

ROOT = Path(__file__).resolve().parent.parent
QUICKSTART = ROOT / "docs" / "quickstart.md"


def _lines() -> list[str]:
    return QUICKSTART.read_text(encoding="utf-8").splitlines()


def _after(marker: str) -> int:
    """The index of the first line of the quickstart that contains ``marker``."""
    lines = _lines()
    at = next((index for index, line in enumerate(lines) if marker in line), None)
    assert at is not None, f"docs/quickstart.md no longer says {marker!r}"
    return at


def _fenced(fence: str, marker: str) -> list[str]:
    """The first ``fence`` block after ``marker``, its lines without the fence's indent."""
    lines = _lines()
    at = _after(marker)
    start = next(i for i in range(at, len(lines)) if lines[i].strip() == f"```{fence}")
    indent = len(lines[start]) - len(lines[start].lstrip())
    end = next(i for i in range(start + 1, len(lines)) if lines[i].strip() == "```")
    return [line[indent:].rstrip() for line in lines[start + 1 : end]]


def _python(marker: str) -> str:
    """The first python block after ``marker``, as source."""
    return "\n".join(_fenced("python", marker)) + "\n"


def _console(marker: str) -> list[str]:
    """What the first console block after ``marker`` shows its command printing."""
    block = _fenced("console", marker)
    assert block[0].startswith("$ "), block[0]
    return block[1:]


def _text(anchor: str) -> list[str]:
    """The text block of the quickstart that holds the line ``anchor``."""
    lines = _lines()
    at = next((i for i, line in enumerate(lines) if line.strip() == anchor.strip()), None)
    assert at is not None, f"docs/quickstart.md no longer shows {anchor!r}"
    start = max(i for i in range(at + 1) if lines[i].strip() == "```text")
    indent = len(lines[start]) - len(lines[start].lstrip())
    end = next(i for i in range(at, len(lines)) if lines[i].strip() == "```")
    return [line[indent:].rstrip() for line in lines[start + 1 : end]]


def _check(directory: Path, name: str, source: str, capsys, code: int) -> list[str]:
    """``lanky check`` on ``source`` written as ``directory/name``, as the lines it prints.

    Each file gets a directory of its own, so that no import of one is taken
    for another, and the check has to exit with ``code``.
    """
    directory.mkdir()
    path = directory / name
    path.write_text(source, encoding="utf-8")
    assert cli.main(["check", str(path)]) == code
    return [line.rstrip() for line in capsys.readouterr().out.splitlines()]


def _holds(shown: list[str], printed: list[str]) -> None:
    """``shown``, its ``...`` lines aside, is printed in order, each run of lines together."""
    runs: list[list[str]] = [[]]
    for line in shown:
        if line == "...":
            runs.append([])
        else:
            runs[-1].append(line)
    at = 0
    for run in (run for run in runs if run):
        found = next(
            (i for i in range(at, len(printed) - len(run) + 1) if printed[i : i + len(run)] == run),
            None,
        )
        assert found is not None, ("\n".join(run), "\n".join(printed))
        at = found + len(run)


@pytest.fixture(scope="module")
def lean() -> Iterator[object]:
    """Core Lean, or a skip saying why not: a failure where Lean was promised."""
    from lanky.oracles.lean import LeanOracle

    def without(reason: str) -> None:
        if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
            pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason}", pytrace=False)
        pytest.skip(reason)

    if os.environ.get("LANKY_LEAN_DISABLE"):
        without("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    oracle = LeanOracle(timeout=float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120")))
    available, reason = oracle.availability()
    if not available:
        without(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        without(f"the Lean REPL could not be built: {oracle.session.error}")
    yield oracle
    oracle.session.close()


# {{{ named conditions


def _red() -> str:
    return _python("this in `upwind_step.py`")


def _green() -> str:
    red = _red()
    at = red.index("@claim\ndef upwind_bounded")
    return red[:at] + _python("So put the claim under it")


def test_the_cfl_story_is_red_with_the_condition_named(tmp_path, capsys) -> None:
    """``upwind_bounded`` for every Courant number is refuted, and ``cfl`` named as the fix."""
    printed = _check(tmp_path / "red", "upwind_step.py", _red(), capsys, 1)
    assert printed == _console("That is false, and the check")


def test_the_cfl_story_is_green_under_the_condition(tmp_path, capsys) -> None:
    """Under ``with cfl as (nu, stable)`` the claim holds at every draw; the table is shown."""
    printed = _check(tmp_path / "green", "upwind_step.py", _green(), capsys, 0)
    shown = _console("So put the claim under it")
    assert printed[: len(shown)] == shown


def test_the_three_things_a_with_assumes(tmp_path, capsys) -> None:
    """A condition, another claim's conditions, and a whole claim, each in its row."""
    source = _python("Put this in `between.py`")
    printed = _check(tmp_path / "forms", "between.py", source, capsys, 0)
    shown = _console("Put this in `between.py`")
    assert printed[: len(shown)] == shown


def test_a_claim_with_no_goal_is_refused_naming_condition() -> None:
    """The quickstart quotes the refusal of a claim with no goal; it is the one raised."""
    from lanky import claim
    from lanky.prelude import Real

    def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):  # noqa: ANN202, F821 - a claim written wrong
        """The CFL condition: the Courant number is between 0 and 1."""

    with pytest.raises(TypeError) as raised:
        claim(cfl)
    message = " ".join(str(raised.value).split())
    quoted = message[message.index("a claim needs a goal") :]
    assert quoted.endswith("A named set of assumptions with no goal is a @condition")
    assert quoted in " ".join(QUICKSTART.read_text(encoding="utf-8").split())


# }}}


# {{{ a written proof


def _table() -> str:
    return _python("Put this in `table.py`")


#: The last case of ``table.py`` as the quickstart has it, which the variants replace.
LAST_CASE = (
    "        else:\n"
    "            yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)\n"
)


def _variant(old: str, new: str) -> str:
    source = _table()
    assert source.count(old) == 1, old
    return source.replace(old, new)


#: The line under the table that says what the native run did, without Lean.
NOT_CHECKED = (
    "NOT CHECKED compressed_taylor at table.py:7: without Lean, its proof was not checked by "
    "Lean; it was run at 8 drawn values instead, and every step held."
)


def test_without_lean_the_proof_is_run_at_draws_and_says_so(monkeypatch, tmp_path, capsys) -> None:
    """Without Lean the claim reads ``assumed``, and the ``NOT CHECKED`` line is the one shown."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    printed = _check(tmp_path / "table", "table.py", _table(), capsys, 0)
    row = next(line for line in printed if "compressed_taylor" in line)
    assert row.split()[:3] == ["assumed", "-", "table.py:7"]
    _holds(_text(NOT_CHECKED), printed)


def test_with_core_lean_the_proof_is_proved_as_shown(lean, tmp_path, capsys) -> None:
    """With core Lean the claim is ``proved``, by its proof, and the table is the one shown."""
    printed = _check(tmp_path / "table", "table.py", _table(), capsys, 0)
    assert printed == _console("With core Lean, the claim reads `proved`")


def test_a_sign_dropped_is_refuted_at_its_line_with_its_numbers(tmp_path, capsys) -> None:
    """The native run finds the calculation's dropped sign, with Lean or without."""
    source = _variant(LAST_CASE, _python("drop a sign in the middle"))
    printed = _check(tmp_path / "sign", "table.py", source, capsys, 1)
    _holds(_console("The native run finds it before Lean is asked"), printed)


def test_the_calculation_as_written_holds_at_every_draw(monkeypatch, tmp_path, capsys) -> None:
    """The calculation the quickstart shows with the sign right is no step written wrong."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    source = _variant(LAST_CASE, _python("Python's own chained"))
    printed = _check(tmp_path / "calculation", "table.py", source, capsys, 0)
    assert any(line.startswith("NOT CHECKED compressed_taylor") for line in printed)
    assert "every step held" in printed[-1]


def test_a_point_one_cell_off_is_named_with_its_fix(lean, tmp_path, capsys) -> None:
    """Every step holds at the draws; Lean says the step does not follow, and the fix is checked."""
    old = "            yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)\n"
    source = _variant(old, _python("one cell off"))
    printed = _check(tmp_path / "off", "table.py", source, capsys, 1)
    _holds(_console("Every step holds at the draws"), printed)


#: Each refusal the quickstart shows: the line it changes in ``table.py``, what it
#: writes there, and a line of the block it shows, which finds the block.
REFUSALS = {
    "no closing line": (
        "            yield by(stored)\n",
        "            continue\n",
        "UNPROVED compressed_taylor at table.py:7: a case of the proof has no closing line.",
    ),
    "a point not reached": (
        "compressed_taylor.conclusion[a - 2, b + 2], pde)",
        "compressed_taylor.conclusion[a + 1, b], pde)",
        "UNPROVED compressed_taylor at table.py:7: the conclusion is cited where the loop has "
        "not reached.",
    ),
    "not through the tree": (
        "compressed_taylor.conclusion.domain",
        "compressed_taylor.domain",
        "UNPROVED compressed_taylor at table.py:7: the claim's tree is not used as lanky reads it.",
    ),
    "a form of 0.5": (
        "yield by(recurrence, ",
        "yield by(recurrence(a - 2, b), ",
        "UNPROVED compressed_taylor at table.py:7: the proof is written in a form of lanky 0.5.",
    ),
}

#: The reports the quickstart shows of a citation the proof makes wrong, which
#: lanky finds as it compiles the proof for Lean, where Lean is installed.
WITH_LEAN = {
    "a condition not met": (
        "            yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)\n",
        "            yield by(stored[a, b], recurrence[a - 2, b], "
        "compressed_taylor.conclusion[a - 2, b + 2], pde[a - 2, b])\n",
        "stored[a, b] needs a < 2, and this case has a >= 2.",
    ),
    "below zero": (
        "        if a < 2:\n",
        "        if a < 1:\n",
        "compressed_taylor.conclusion[a - 2, b + 2] is at a negative a when a = 1: "
        "split off a < 2 first.",
    ),
}


@pytest.mark.parametrize("name", sorted(REFUSALS))
def test_each_refusal_is_what_check_prints(name, tmp_path, capsys) -> None:
    """Each refusal is reported at its line, with Lean or without, with the line to write."""
    old, new, anchor = REFUSALS[name]
    printed = _check(tmp_path / "refused", "table.py", _variant(old, new), capsys, 1)
    _holds(_text(anchor), printed)


@pytest.mark.parametrize("name", sorted(WITH_LEAN))
def test_each_wrong_citation_is_named_where_lean_is(name, lean, tmp_path, capsys) -> None:
    """A cited fact whose condition fails, or the conclusion below zero, is named at its line."""
    old, new, anchor = WITH_LEAN[name]
    printed = _check(tmp_path / "cited", "table.py", _variant(old, new), capsys, 1)
    _holds(_text(anchor), printed)


#: Nicomachus's theorem as lanky 0.5 had it: ``n`` a parameter, and the claim at
#: ``n - 1`` a call of itself.
NICOMACHUS_05 = '''\
from __future__ import annotations

from lanky import by, claim
from lanky.known import one_more_term
from lanky.prelude import Fin, Nat


@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of 0 .. n is n * (n + 1)."""


@claim
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""
    if n == 0:
        return by()
    assert sum(i**3 for i in Fin[n + 1]) == sum(i**3 for i in Fin[n]) + n**3, by(one_more_term)
    return by(nicomachus(n - 1), gauss(n - 1))
'''


def test_a_claim_that_calls_itself_is_refused_with_n_moved_into_the_for(tmp_path, capsys) -> None:
    """lanky 0.5's ``nicomachus(n - 1)`` is refused, with the conclusion's point as the fix."""
    printed = _check(tmp_path / "nicomachus", "nicomachus.py", NICOMACHUS_05, capsys, 1)
    _holds(
        _text("UNPROVED nicomachus at nicomachus.py:13: the claim calls itself in its own proof."),
        printed,
    )


# }}}
