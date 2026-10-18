"""The soundness reproductions of 0.6's proof surface: each fails the check, natively and with Lean.

The design (2026-10-18, sections 3.7 and 3.8) keeps the soundness work of
0.5 and adds the forms of 0.6. Each case below is a claim that is false, so
that a check passing it would be unsound, with a written proof that has one
of the faults the surface makes possible:

- a false ``assert`` step;
- a citation of the claim's own conclusion at a later point, which would be
  circular;
- a ``yield`` whose reasons do not give the case;
- a case with no closing line (``continue``, or a path that ends);
- a condition a claim drops: a claim held under a ``with`` block cited from
  outside it, a claim in the block that declares a bound name as its own,
  and a claim after the block that reads a bound name.

Each is checked three ways: without Lean, where the native run and the
refusals have to catch it; with Lean and the native run set aside, so that
Lean's side refuses it on its own; and with both. ``lanky check`` exits 1
every time, and the claim never reads ``proved``. The controls beside them,
the same proofs written right, are proved by Lean, so that no case passes
for refused only because nothing could be proved.
"""

from __future__ import annotations

import os
import textwrap

import pytest

from conftest import claims
from lanky.check import check_path
from lanky.cli import main as lanky_main
from lanky.ledger import Status

HEAD = """\
from __future__ import annotations

from lanky import by, claim, condition
from lanky.prelude import Fn, Int, Nat
"""

#: A false step: f[n] == f[n - 1] where the table climbs by one.
FALSE_STEP = '''
@claim
def flat(
    f: Fn[Nat, Int], start: f[0] == 0, step: all(f[n + 1] == f[n] + 1 for n in Nat)
) -> all(f[n] == 0 for n in Nat):
    for n in flat.conclusion.domain:
        if n == 0:
            yield by(start)
        else:
            assert f[n] == f[n - 1], by(step[n - 1])
            yield by(flat.conclusion[n - 1])
'''

#: The same claim and proof, written right: the control.
CLIMBS = '''
@claim
def climbs(
    f: Fn[Nat, Int], start: f[0] == 0, step: all(f[n + 1] == f[n] + 1 for n in Nat)
) -> all(f[n] == n for n in Nat):
    for n in climbs.conclusion.domain:
        if n == 0:
            yield by(start)
        else:
            assert f[n] == f[n - 1] + 1, by(step[n - 1])
            yield by(climbs.conclusion[n - 1])
'''

#: A later point: the conclusion at n + 1, not yet filled in at n.
LATER_POINT = '''
@claim
def held(f: Fn[Nat, Int], step: all(f[n] == f[n + 1] for n in Nat)) -> all(
    f[n] == 0 for n in Nat
):
    for n in held.conclusion.domain:
        assert f[n] == f[n + 1], by(step[n])
        yield by(held.conclusion[n + 1])
'''

#: A wrong yield: the first term is 0, and the case says the conclusion, 1.
WRONG_YIELD = '''
@claim
def ones(
    f: Fn[Nat, Int], start: f[0] == 0, step: all(f[n + 1] == f[n] for n in Nat)
) -> all(f[n] == 1 for n in Nat):
    for n in ones.conclusion.domain:
        if n == 0:
            yield by(start)
        else:
            yield by(step[n - 1], ones.conclusion[n - 1])
'''

#: A case with no closing line: the first point skipped, with nothing to start from.
SKIPPED_CASE = '''
@claim
def zeros(f: Fn[Nat, Int], step: all(f[n + 1] == f[n] for n in Nat)) -> all(
    f[n] == 0 for n in Nat
):
    for n in zeros.conclusion.domain:
        if n == 0:
            continue
        yield by(step[n - 1], zeros.conclusion[n - 1])
'''

#: A case that ends: the path for n == 0 runs off the end of the loop's body.
ENDED_CASE = '''
@claim
def zeros_again(f: Fn[Nat, Int], step: all(f[n + 1] == f[n] for n in Nat)) -> all(
    f[n] == 0 for n in Nat
):
    for n in zeros_again.conclusion.domain:
        if n >= 1:
            yield by(step[n - 1], zeros_again.conclusion[n - 1])
'''

#: A condition, and a claim under it, cited from outside the block for any table.
DROPPED_BY_A_CITATION = '''
@condition
def starts_at_zero(f: Fn[Nat, Int], zero: f[0] == 0):
    """The table starts at zero."""


with starts_at_zero as (f, zero):

    @claim
    def first_is_zero() -> f[0] == 0:
        return by(zero)


@claim
def any_table_starts_at_zero(g: Fn[Nat, Int]) -> g[0] == 0:
    return by(first_is_zero(g))
'''


def _lean_or_skip() -> None:
    """Skip a test that needs Lean, or fail it where Lean was promised."""
    from lanky.oracles.lean import LeanOracle

    reason = None
    if os.environ.get("LANKY_LEAN_DISABLE"):
        reason = "the Lean oracle is disabled by LANKY_LEAN_DISABLE"
    else:
        available, why = LeanOracle().availability()
        if not available:
            reason = f"no Lean oracle here: {why}"
    if reason is None:
        return
    if os.environ.get("LANKY_LEAN_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


def _lean_side_only(monkeypatch) -> None:
    """Set the native run aside, so that Lean's side has to refuse the proof on its own."""
    import lanky.proofs.native as native

    monkeypatch.setattr(native, "native_run", lambda theorem, *args, **kwargs: (None, 0))


def _file(tmp_path, name: str, body: str):
    path = tmp_path / f"{name}.py"
    path.write_text(HEAD + textwrap.dedent(body), encoding="utf-8")
    return path


def _failed(path, owner: str, capsys) -> tuple[dict, str]:
    """Check ``path``: ``lanky check`` exits 1, ``owner`` is not proved; its proof's account."""
    code = lanky_main(["check", str(path)])
    out = capsys.readouterr().out
    assert code == 1, out
    fact = {fact.owner: fact for fact in claims(check_path(path))}[owner]
    assert fact.status is not Status.PROVED, (owner, fact.provenance)
    assert fact.provenance.get("tactic") != "its written proof", owner
    return fact.provenance.get("proof") or {}, out


#: Each case: its source, the claim, and what the report's failure is, natively and in Lean.
CASES = {
    "false_step": (FALSE_STEP, "flat", {"false"}, {"step"}),
    "later_point": (LATER_POINT, "held", {"later"}, {"later"}),
    "wrong_yield": (WRONG_YIELD, "ones", {"false"}, {"step"}),
    "skipped_case": (SKIPPED_CASE, "zeros", {"close"}, {"close"}),
    "ended_case": (ENDED_CASE, "zeros_again", {"close"}, {"close"}),
    "dropped_by_a_citation": (
        DROPPED_BY_A_CITATION, "any_table_starts_at_zero", {"false"}, {"condition"}
    ),
}


@pytest.mark.parametrize("case", sorted(CASES))
def test_a_faulty_proof_of_a_false_claim_fails_natively(case, tmp_path, monkeypatch, capsys):
    """Without Lean: the native run, or a refusal before it, fails the check."""
    source, owner, kinds, _lean = CASES[case]
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    account, out = _failed(_file(tmp_path, case, source), owner, capsys)
    assert account.get("closed") is False, (case, account)
    assert {failure["kind"] for failure in account["failures"]} <= kinds, (case, account)
    assert f"UNPROVED {owner} at " in out


@pytest.mark.parametrize("case", sorted(CASES))
def test_a_faulty_proof_of_a_false_claim_fails_in_lean(case, tmp_path, monkeypatch, capsys):
    """With Lean and the native run set aside: Lean's side refuses it alone."""
    _lean_or_skip()
    source, owner, _native, kinds = CASES[case]
    _lean_side_only(monkeypatch)
    account, out = _failed(_file(tmp_path, case, source), owner, capsys)
    assert account.get("closed") is False, (case, account)
    assert {failure["kind"] for failure in account["failures"]} <= kinds, (case, account)
    if case == "dropped_by_a_citation":
        # the citation brings its condition, which nothing in the case shows
        (failure,) = account["failures"]
        assert failure["lines"][0] == (
            "first_is_zero(g) needs g[0] == 0, and this case has nothing that shows it."
        )


@pytest.mark.parametrize("case", sorted(CASES))
def test_a_faulty_proof_of_a_false_claim_fails_with_lean_and_the_native_run(
    case, tmp_path, capsys
):
    _lean_or_skip()
    source, owner, _native, _lean = CASES[case]
    account, _out = _failed(_file(tmp_path, case, source), owner, capsys)
    assert account.get("closed") is False, (case, account)


def test_the_controls_are_proved_by_lean(tmp_path) -> None:
    """The climbing table written right, and the claim under its condition: both proved."""
    _lean_or_skip()
    path = _file(tmp_path, "controls", CLIMBS + DROPPED_BY_A_CITATION)
    facts = {fact.owner: fact for fact in claims(check_path(path))}
    for owner in ("climbs", "first_is_zero"):
        fact = facts[owner]
        assert fact.status is Status.PROVED and fact.decided_by == "lean", fact.provenance
        assert fact.provenance["proof"]["closed"] is True, owner
    under = facts["first_is_zero"]
    assert under.statement.startswith("under starts_at_zero (zero): ")
    # the condition is in what Lean proved, and so in what a citation restates
    assert "(zero : f 0 = 0)" in under.provenance["proof"]["lean_source"]
    assert "f 0 = 0 →" in under.provenance["lean_as_cited"]


#: A claim in the block that declares a bound name as its own, so its condition is
#: about another f: refused where it is defined.
SHADOWED = '''
@condition
def starts_at_zero(f: Fn[Nat, Int], zero: f[0] == 0):
    """The table starts at zero."""


with starts_at_zero as (f, zero):

    @claim
    def any_table(f: Fn[Nat, Int]) -> f[0] == 0:
        return by(zero)
'''

#: A claim after the block that reads a name it bound, without holding under it.
READ_AFTER = '''
@condition
def starts_at_zero(f: Fn[Nat, Int], zero: f[0] == 0):
    """The table starts at zero."""


with starts_at_zero as (f, zero):

    @claim
    def first_is_zero() -> f[0] == 0:
        return by(zero)


@claim
def outside() -> f[0] == 0:
    return by(first_is_zero)
'''


@pytest.mark.parametrize(
    ("case", "said"),
    [
        (
            SHADOWED,
            "f is starts_at_zero's, which with starts_at_zero as (f, zero) assumes for every "
            "claim in the block; drop the parameter f",
        ),
        (
            READ_AFTER,
            "f belongs to starts_at_zero; use it inside with starts_at_zero as (f, zero):",
        ),
    ],
    ids=["shadowed", "read_after"],
)
@pytest.mark.parametrize("lean", [False, True], ids=["natively", "with_lean"])
def test_a_claim_that_would_drop_its_condition_is_refused(
    case, said, lean, tmp_path, monkeypatch, capsys
) -> None:
    """Refused where it is defined, so the file does not import, and the check exits 1."""
    if lean:
        _lean_or_skip()
    else:
        monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = _file(tmp_path, "dropped", case)
    code = lanky_main(["check", str(path)])
    captured = capsys.readouterr()
    assert code == 1
    assert said in captured.out + captured.err
