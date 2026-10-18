"""The words of the proof interface: what lanky says where a proof, a script or a check falls short.

Each message is read as a person would read it aloud, and tested as text:

- a script ``use_tactic`` gives that the screen refuses is a ``REFUSED`` line
  under the table, with the fix, and not a traceback at import;
- a step of a written proof that does not follow says which fact it also
  needs, or which facts of :mod:`lanky.known` fit its shape;
- the outline names each case as the body reads, ``if a < 2:`` after ``if a
  + b == 0:``, not ``when a + b != 0 and a < 2:``;
- a proof not checked for want of Lean says so in a clause;
- a row whose Lean trusts the printer for a citation says so in words;
- the multipliers a step was closed with are kept, so a warm check runs no
  search;
- a hypothesis named like a name lanky's scripts use keeps its meaning.

Everything here runs without Lean but for the last test, which skips where
there is none.
"""

# A lanky statement names its variables in the annotations (see pyproject.toml).
# ruff: noqa: F821

from __future__ import annotations

import json
import os
import textwrap
from fractions import Fraction
from pathlib import Path

import pytest

from conftest import claims
from lanky import conj, real, theorem
from lanky.audit import refusal, screen
from lanky.check import check_path, import_path
from lanky.cli import main as lanky_main
from lanky.cli import report_written
from lanky.ledger import Fact, Ledger, Status
from lanky.oracles.lean import LeanOracle, LeanSession, ProofCache, use_tactic
from lanky.prelude import Complex, Nat
from lanky.proofs import compile_proof, hints, trace_proof
from lanky.proofs.report import read
from lanky.terms import Var, render

# {{{ a script the screen refuses


@pytest.mark.parametrize(
    ("script", "found", "fix"),
    [
        ("omega\n#exit", "it has #exit, a Lean command", "take #exit out; lanky writes every"),
        ("native_decide", "it has native_decide, which trusts", "prove it with decide"),
        ("set_option maxRecDepth 9 in omega", "it has set_option", "set LANKY_LEAN_BUDGET"),
        ("theorem t : True := trivial\nexact t", "it has theorem", "with have inside the script"),
        ("open Finset in simp", "it has open", "write each name in full, as Finset.sum_comm"),
        ("omega\n/- the rest", "block comment", "close the comment with -/"),
        ("macro_rules | `(tactic| x) => `(tactic| omega)", "macro_rules", "in tactics"),
        ("exact Lean.ofReduceBool _ _ rfl", "ofReduceBool", "rests on the kernel alone"),
    ],
)
def test_a_refused_script_is_said_with_what_to_write_instead(script, found, fix) -> None:
    reason, said = refusal(script)
    assert found in reason and fix in said, (reason, said)
    assert screen(script) == reason
    assert refusal("omega") is None


@theorem
def nonneg_square(n: Nat) -> n * n >= 0:
    """A claim a test pins a refused script to."""


def test_use_tactic_takes_a_refused_script_and_raises_nothing() -> None:
    from lanky.oracles.lean import _lean_oracles

    use_tactic(nonneg_square, "native_decide\n#exit")
    try:
        assert all(
            oracle.tactics[nonneg_square.fact_id] == "native_decide\n#exit"
            for oracle in _lean_oracles()
        )
    finally:
        for oracle in _lean_oracles():
            oracle.tactics.pop(nonneg_square.fact_id, None)


def _no_lean(monkeypatch: pytest.MonkeyPatch, tmp_path) -> LeanOracle:
    """An oracle whose session cannot start, with a proof cache of its own."""
    monkeypatch.setenv("LANKY_LEAN_VERSION", "v0.0.0-test")
    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)

    def start(session: LeanSession) -> bool:
        session.error = "no Lean in this test"
        return False

    monkeypatch.setattr(LeanSession, "start", start)
    oracle = LeanOracle()
    monkeypatch.setattr(oracle, "availability", lambda: (True, ""))
    oracle.proofs = ProofCache(str(tmp_path / "proofs"))
    return oracle


def test_the_oracle_records_a_refused_script_with_its_fix(monkeypatch, tmp_path) -> None:
    oracle = _no_lean(monkeypatch, tmp_path)
    fact = nonneg_square.fact()
    oracle.tactics[fact.id] = "native_decide\n#exit"
    result = oracle.establish(fact)
    assert result.status is Status.ASSUMED
    refused = result.provenance["tactic_refused"]
    assert refused["reason"] == (
        "the script use_tactic gives it is not sent to Lean, since it has #exit, a Lean command"
    )
    assert refused["fix"].startswith("take #exit out; lanky writes every command")


REFUSED_FILE = '''\
"""A pinned script the screen refuses."""

from __future__ import annotations

from lanky import theorem
from lanky.oracles.lean import use_tactic
from lanky.prelude import Nat


@theorem
def square(n: Nat) -> n * n >= 0:
    """A square is not negative."""


use_tactic(square, "omega\\n#exit")
'''


def test_lanky_check_names_a_refused_script_under_the_table_and_fails(
    tmp_path, monkeypatch, capsys
) -> None:
    """With no Lean at all: the script is screened where it is reported."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "pinned.py"
    path.write_text(REFUSED_FILE, encoding="utf-8")
    assert lanky_main(["check", str(path)]) == 1
    out = capsys.readouterr().out
    line = REFUSED_FILE.splitlines().index("@theorem") + 1
    assert (
        f"REFUSED square at pinned.py:{line}: the script use_tactic gives it is not sent to "
        "Lean, since it has #exit, a Lean command." in out
    )
    assert "  Fix: take #exit out; lanky writes every command around the script" in out
    assert "Traceback" not in out


def test_a_refused_script_lasts_only_the_check_of_the_file_that_gave_it(
    tmp_path, monkeypatch
) -> None:
    """Codex on #179: a script taken out of the file is not refused when it is checked again."""
    from lanky.oracles.lean import _lean_oracles

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "pinned_again.py"
    path.write_text(REFUSED_FILE, encoding="utf-8")
    (fact,) = claims(check_path(path))
    assert fact.provenance["tactic_refused"]["fix"].startswith("take #exit out")
    assert all(fact.id not in oracle.tactics for oracle in _lean_oracles())
    path.write_text(REFUSED_FILE.split("\n\nuse_tactic(")[0] + "\n", encoding="utf-8")
    (again,) = claims(check_path(path))
    assert "tactic_refused" not in again.provenance


def test_a_refused_script_does_not_outlast_an_import_that_raises(tmp_path, monkeypatch) -> None:
    """Codex on #179: the file raises after its use_tactic; checked again, it is not refused."""
    from lanky.oracles.lean import refused_scripts

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "pinned_then_raises.py"
    path.write_text(REFUSED_FILE + '\nraise RuntimeError("after use_tactic")\n', encoding="utf-8")
    with pytest.raises(RuntimeError, match="after use_tactic"):
        check_path(path)
    assert refused_scripts() == {}
    path.write_text(REFUSED_FILE.split("\n\nuse_tactic(")[0] + "\n", encoding="utf-8")
    (again,) = claims(check_path(path))
    assert "tactic_refused" not in again.provenance


# }}}


# {{{ a step that does not follow

#: Written proofs a step of which leaves out a fact, or cites none at all.
STEPS = '''\
"""Written proofs a step of which does not follow."""

from __future__ import annotations

from lanky import conj, log, real, theorem
from lanky.prelude import Complex, Fn, Nat, Real


@theorem
def without_pde(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    def claim(a, b):
        if a + b == 0:
            return stored
        if a < 2:
            return stored
        return recurrence(a - 2, b), claim(a - 2, b + 2)

    return claim


@theorem
def nested(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    def claim(a, b):
        if a < 2:
            if b < 2:
                return stored
            return stored
        return recurrence(a - 2, b), claim(a - 2, b + 2), pde(a - 2, b)

    return claim


@theorem
def bare_modulus(alpha: Complex, nonzero: alpha != 0) -> (
    log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
):
    return (
        log(abs(alpha))
        .equals(log(abs(alpha) ** 2) / 2)
        .equals(log(real(alpha * conj(alpha))) / 2)
    )
'''


@pytest.fixture(scope="module")
def steps(tmp_path_factory) -> object:
    """The proofs above, imported."""
    path = tmp_path_factory.mktemp("steps") / "steps.py"
    path.write_text(STEPS, encoding="utf-8")
    return import_path(path)


def _at_step(command, line: int) -> tuple[int, int]:
    """The Lean line (from 1) and column of the step from Python ``line``."""
    for number, emitted in enumerate(command.lines, 1):
        for start, _end, origin in emitted.spans:
            if origin.kind == "step" and origin.line == line:
                return number, start + 4
        if emitted.origin is not None and emitted.origin.kind == "step":
            if emitted.origin.line == line:
                return number, 0
    raise AssertionError(f"no step from line {line}")


def _failure_at(proof, command, line: int):
    error = {"severity": "error", "line": 0, "column": 0, "data": "made up here"}
    error["line"], error["column"] = _at_step(command, line)
    closed, failures = read(proof, command, {"messages": [error], "sorries": []})
    assert not closed
    return next(failure for failure in failures if failure.line == line)


def test_a_step_short_of_a_fact_says_which_it_also_needs(steps) -> None:
    pytest.importorskip("sympy")
    proof = trace_proof(steps.without_pde)
    command = compile_proof(proof, mathlib=True)
    leaf = proof.leaves[-1]
    failure = _failure_at(proof, command, leaf.line)
    assert "It also needs pde(a - 2, b), which says D[a, b] + D[a - 2, b + 2] == 0." in (
        failure.lines
    )
    assert failure.fix == "return recurrence(a - 2, b), claim(a - 2, b + 2), pde(a - 2, b)"
    assert failure.repair[0] == "add"


def test_a_step_no_fact_gets_to_names_the_known_facts_of_its_shape(steps) -> None:
    pytest.importorskip("sympy")
    proof = trace_proof(steps.bare_modulus)
    command = compile_proof(proof, mathlib=True)
    second = proof.leaves[0].chain.links[1].line
    failure = _failure_at(proof, command, second)
    assert "No fact the proof cites gets there. What lanky knows of its shape:" in failure.lines
    assert any(
        line.startswith("  log_of_a_power rewrites log(x**n); here log(abs(alpha)**2)")
        for line in failure.lines
    ), failure.lines
    assert failure.fix == (
        "cite one of them, after from lanky.known import log_of_a_power, modulus_squared; "
        "or split the step in two"
    )


# }}}


# {{{ the outline's cases


def test_the_outline_names_each_case_as_the_body_reads(steps) -> None:
    proof = trace_proof(steps.without_pde)
    rows = compile_proof(proof, mathlib=True).outline
    assert [row[1] for row in rows] == ["if a + b == 0:", "if a < 2:", "otherwise:"]


def test_a_nested_case_says_the_split_it_did_not_take_the_other_way_round(steps) -> None:
    proof = trace_proof(steps.nested)
    rows = compile_proof(proof, mathlib=True).outline
    assert [row[1] for row in rows] == ["if a < 2 and b < 2:", "if a < 2 and b >= 2:", "otherwise:"]


# }}}


# {{{ a proof not checked, and a citation the printer restated


def _fact(proof: dict | None = None, **provenance) -> Fact:
    return Fact(
        id="theorem:m.t@3",
        kind="theorem",
        statement="n : Nat |- n + 0 == n",
        status=Status.TESTED,
        decided_by="property-test",
        provenance={**({"proof": proof} if proof else {}), "path": "/x/m.py", **provenance},
        where="m.py:3",
        owner="t",
    )


def test_without_lean_the_line_says_so_in_a_clause(tmp_path, monkeypatch, capsys) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "doubled.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import theorem
            from lanky.prelude import Real


            @theorem
            def doubled(x: Real) -> 2 * x == x + x:
                return (2 * x).equals(x + x)
            """
        ),
        encoding="utf-8",
    )
    (fact,) = claims(check_path(path))
    proof = fact.provenance["proof"]
    assert proof["closed"] is None
    line = path.read_text(encoding="utf-8").splitlines().index("    return (2 * x).equals(x + x)")
    assert proof["said"] == (
        f"without Lean, each step of its proof was tested at drawn points instead (line {line + 1})"
    )
    # the long form stays, for --verbose and --json
    assert proof["reason"].startswith("Lean is not available here")
    assert not report_written(Ledger([fact]))
    out = capsys.readouterr().out
    assert f"NOT CHECKED doubled at {fact.where}: without Lean, each step of its proof" in out
    assert "not checked by Lean" not in out


def test_a_row_whose_citation_the_printer_restated_says_so_in_words() -> None:
    one = Ledger([_fact(lean_restated_by_printer=["line_taylor"])]).render()
    assert "trusts how lanky prints line_taylor, which Lean did not prove in this check" in one
    two = Ledger([_fact(lean_restated_by_printer=["line_taylor", "harmonic"])]).render()
    assert "trusts how lanky prints line_taylor and harmonic, which Lean did not" in two
    assert "lean_restated_by_printer" not in two
    assert "trusts" not in Ledger([_fact()]).render()


# }}}


# {{{ the multipliers kept


def test_a_multiplier_is_kept_and_read_back_as_the_same_term() -> None:
    n, alpha, beta = Var("n"), Var("alpha"), Var("beta")
    terms = ((n - 1) / n * (-beta / alpha), Fraction(1, 3), -1, 2.5, alpha**2 * beta)
    again = hints.decode(json.loads(json.dumps(hints.encode(terms))))
    assert [render(item) if hasattr(item, "mapper_method") else item for item in again] == [
        render(item) if hasattr(item, "mapper_method") else item for item in terms
    ]
    with pytest.raises(ValueError):
        hints.decode({"n": "os:system", "a": {"t": []}})


def test_the_hint_cache_keeps_a_step_and_misses_what_it_cannot_read(tmp_path) -> None:
    cache = hints.HintCache(str(tmp_path))
    n = Var("n")
    key = hints.hint_key(n == 1, [n == 2], {"n": Nat})
    assert cache.get(key) is hints.MISSING
    cache.put(key, [n + 1, Fraction(1, 2)])
    kept = cache.get(key)
    assert render(kept[0]) == "n + 1" and kept[1] == Fraction(1, 2)
    cache.put(key, None)
    assert cache.get(key) is None
    path = next(Path(tmp_path).rglob("*.json"))
    path.write_text("{not json", encoding="utf-8")
    assert cache.get(key) is hints.MISSING
    assert hints.HintCache(None).get(key) is hints.MISSING


def test_a_warm_compile_runs_no_search_and_writes_the_same_lean(
    steps, tmp_path, monkeypatch
) -> None:
    pytest.importorskip("sympy")
    import lanky.proofs.report as report

    monkeypatch.setenv("LANKY_LEAN_PROOF_CACHE", str(tmp_path / "proofs"))
    calls: list[int] = []
    search = report.combination

    def counted(*args, **kwargs):
        calls.append(1)
        return search(*args, **kwargs)

    monkeypatch.setattr(report, "combination", counted)
    proof = trace_proof(steps.nested)
    cold = compile_proof(proof, mathlib=True)
    assert calls
    calls.clear()
    warm = compile_proof(proof, mathlib=True)
    assert not calls
    assert warm.source == cold.source
    assert any((tmp_path / "proofs" / "hints").rglob("*.json"))


# }}}


# {{{ names


NAMES = '''\
"""Hypotheses named like the names lanky's scripts introduce."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fn, Int, Nat


@theorem
def count_ih(
    f: Fn[Nat, Int],
    ih: f[0] == 0,
    hk: all(f[n + 1] == f[n] + 1 for n in Nat),
) -> all(f[n] == n for n in Nat):
    def claim(n):
        if n == 0:
            return ih
        return hk(n - 1), claim(n - 1)

    return claim


@theorem
def count_hn(
    f: Fn[Nat, Int],
    hn: f[0] == 0,
    case_1: all(f[n + 1] == f[n] + 1 for n in Nat),
) -> all(f[n] == n for n in Nat):
    def claim(n):
        if n == 0:
            return hn
        return case_1(n - 1), claim(n - 1)

    return claim


@theorem
def count_pin(
    f: Fn[Nat, Int],
    pin_1: f[0] == 0,
    hstep: all(f[n + 1] == f[n] + 1 for n in Nat),
) -> all(f[n] == n for n in Nat):
    def claim(n):
        if n == 0:
            return pin_1
        return hstep(n - 1), claim(n - 1)

    return claim
'''


def test_a_hypothesis_named_like_a_script_name_keeps_its_name(tmp_path) -> None:
    path = tmp_path / "names.py"
    path.write_text(NAMES, encoding="utf-8")
    module = import_path(path)
    for name, given in (("count_ih", "ih"), ("count_hn", "hn"), ("count_pin", "pin_1")):
        source = compile_proof(trace_proof(getattr(module, name)), mathlib=False).source
        claim = source.split("\n\n")[0]
        # the hypothesis is bound once, under its own name, and lanky's names are others
        assert claim.count(f"({given} :") == 1, claim
        assert f"have {given} " not in claim and f"by_cases {given} " not in claim, claim


@theorem
def conjugate_form(x: Complex, alpha: Complex, hz0: alpha != 0) -> x / alpha == x * conj(alpha) * (
    1 / real(alpha * conj(alpha))
):
    """Division through the conjugate, its hypothesis named like the script's fact."""


def test_a_part_script_names_its_facts_apart_from_the_hypotheses() -> None:
    from lanky.oracles.lean import claim_statement, part_scripts

    statement = claim_statement(conjugate_form.fact(), True)
    first = str(part_scripts(statement)[0])
    assert "try have hz0_1 :" in first and "try have hz0 :" not in first


def test_lean_proves_what_hypotheses_named_like_script_names_say(tmp_path) -> None:
    from lanky.oracles.lean import LeanOracle

    if os.environ.get("LANKY_LEAN_DISABLE") or not LeanOracle().availability()[0]:
        pytest.skip("no Lean here")
    path = tmp_path / "names.py"
    path.write_text(NAMES, encoding="utf-8")
    for fact in claims(check_path(path)):
        assert fact.provenance["proof"]["closed"] is True, fact.provenance["proof"]


# }}}
