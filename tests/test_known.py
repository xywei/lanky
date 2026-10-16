"""What lanky knows: the library facts, their Lean proofs, the screen, and suggestions by shape.

Most of this needs no Lean: the facts are theorems like any other, their
proofs a table of text, the screen a reading of words, and the suggestions a
matcher over terms. The tests that need Lean with Mathlib, that each fact is
proved by its table proof under the current printer, skip unless
``LANKY_LEAN_MATHLIB`` names a project, and fail instead where CI promised
one (``LANKY_LEAN_MATHLIB_TEST_REQUIRED``): that job is what keeps the table
and the printer in step.
"""

from __future__ import annotations

import os
import subprocess
import sys
from collections.abc import Iterator
from pathlib import Path
from typing import NoReturn

import pytest

import lanky.known as known
from conftest import claims
from lanky import conj, log, real, theorem
from lanky.check import check_path
from lanky.cli import report_known
from lanky.lean import render_term, statement_of
from lanky.ledger import Status
from lanky.oracles import known as table
from lanky.oracles.lean import LeanOracle, LeanSession
from lanky.oracles.screen import REFUSED_WORDS, screen
from lanky.prelude import Complex, Fin, Fn, Nat, Real
from lanky.suggest import suggestions
from lanky.terms import Var
from lanky.theory import Theorem

ROOT = Path(__file__).resolve().parent.parent
DEMO = ROOT / "examples" / "log_of_the_modulus.py"
ENTRIES = [getattr(known, name) for name in known.__all__]


# {{{ the library


def test_every_fact_is_a_theorem_named_in_all_with_a_proof_in_the_table() -> None:
    assert list(known.__all__) == sorted(known.__all__)
    assert all(isinstance(entry, Theorem) for entry in ENTRIES)
    assert set(known.__all__) == set(table.PROOFS)
    # what the module defines and does not name would be a fact with no proof
    defined = {name for name, value in vars(known).items() if isinstance(value, Theorem)}
    assert defined == set(known.__all__)


@pytest.mark.parametrize("entry", ENTRIES, ids=known.__all__)
def test_every_fact_cites_its_mathlib_name_and_states_it_in_words(entry: Theorem) -> None:
    doc = entry.__doc__ or ""
    assert "(Mathlib: " in doc, doc
    first = doc.strip().splitlines()[0]
    assert first[0].isupper() or first[0] in "nz", first
    # the module is lanky.known wherever the package is installed
    assert entry.fact_id.startswith(f"theorem:lanky.known.{entry.__name__}@")


@pytest.mark.parametrize("entry", ENTRIES, ids=known.__all__)
def test_every_fact_prints_for_lean_with_mathlib(entry: Theorem) -> None:
    """The printer states each fact, with no branch cut to keep it off: the proof is about it."""
    statement = statement_of(entry.term, entry.__name__, mathlib=True)
    assert statement.declared_name == f"Lanky.{entry.__name__}"
    assert not statement.side_conditions


@pytest.mark.parametrize("entry", ENTRIES, ids=known.__all__)
def test_no_draw_refutes_a_fact(entry: Theorem) -> None:
    report = entry.report(n=60, seed=1)
    assert report.ok, report.counterexample


def test_importing_the_library_pins_nothing_and_starts_no_lean() -> None:
    """``from lanky.known import ...`` builds theorems and nothing more."""
    program = (
        "import sys, lanky\n"
        "from lanky.oracles.lean import _lean_oracles\n"
        "before = set(sys.modules)\n"
        "import lanky.known\n"
        "new = sorted(set(sys.modules) - before)\n"
        "assert new == ['lanky.known'], new\n"
        "assert all(not oracle.tactics for oracle in _lean_oracles())\n"
        "assert 'lean_interact' not in sys.modules\n"
        "print('ok')\n"
    )
    done = subprocess.run(
        [sys.executable, "-c", program], capture_output=True, text=True, check=False
    )
    assert done.returncode == 0, done.stderr
    assert done.stdout.strip() == "ok"


def test_the_table_does_not_import_the_library() -> None:
    """The oracle reads the table, and the table reads no theorem of the library."""
    program = (
        "import sys, lanky.oracles.known\nassert 'lanky.known' not in sys.modules\nprint('ok')\n"
    )
    done = subprocess.run(
        [sys.executable, "-c", program], capture_output=True, text=True, check=False
    )
    assert done.returncode == 0, done.stderr


@theorem
def log_of_a_power(x: Real, n: Nat) -> log(x**n) == n * log(x):
    """A user's own theorem, named like a fact of the library."""


# kept under a private name, so that the pytest plugin does not collect it
_users_own = log_of_a_power
del log_of_a_power


def test_a_theorem_named_like_a_fact_is_not_one() -> None:
    assert _users_own.__name__ == "log_of_a_power"
    assert table.entry_name(known.log_of_a_power.fact()) == "log_of_a_power"
    assert table.entry_name(_users_own.fact()) is None
    assert table.proof_of(_users_own.fact()) is None
    assert table.proof_of(known.log_of_a_power.fact()) == table.PROOFS["log_of_a_power"]


@pytest.mark.parametrize("name", sorted(table.PROOFS))
def test_every_proof_of_the_table_passes_the_screen(name: str) -> None:
    assert screen(table.PROOFS[name], library=True) is None


def test_a_table_proof_the_screen_refuses_is_not_sent(monkeypatch) -> None:
    monkeypatch.setitem(table.PROOFS, "modulus_squared", "native_decide")
    with pytest.raises(ValueError, match="modulus_squared is refused: it uses native_decide"):
        table.proof_of(known.modulus_squared.fact())


# }}}


# {{{ the screen


@pytest.mark.parametrize(
    ("text", "said"),
    [
        ("simp\n  #exit", "runs the command #exit"),
        ("#print axioms Lanky.t", "runs the command #print"),
        ("exact h --#eval 1", "runs the command #eval"),
        ("set_option debug.skipKernelTC true in\nsimp", "sets an option of Lean's"),
        ("native_decide", "uses native_decide"),
        ("exact absurd (axiom_x) h\naxiom x : False", "uses axiom"),
        ("open Real in simp", "uses open"),
        ("simp\nend", "uses end"),
        ("theorem t : True := trivial", "uses theorem"),
        ("run_tac pure ()", "uses run_tac"),
        ("elab \"x\" : tactic => pure ()", "uses elab"),
        ("attribute [simp] foo", "uses attribute"),
        ("instance : Inhabited Nat := ⟨0⟩", "uses instance"),
        ("import Mathlib", "uses import"),
        ("macro \"x\" : tactic => `(tactic| rfl)", "uses macro"),
    ],
)
def test_the_screen_refuses_what_a_proof_does_not_need(text: str, said: str) -> None:
    for library in (False, True):
        reason = screen(text, library=library)
        assert reason is not None and said in reason, (library, reason)


def test_the_screen_reads_words_not_parts_of_names() -> None:
    assert screen("rw [Finset.sum_def, Foo.end, Real.open_ball]\nsimp [Nat.instance_x]") is None
    assert screen("exact sum_insert_def") is None


def test_a_library_proof_may_give_a_step_more_time_and_may_not_leave_a_hole() -> None:
    timed = "set_option maxHeartbeats 400000 in\nnlinarith [sq_nonneg x]"
    assert screen(timed, library=True) is None
    assert "sets an option" in screen(timed)
    assert "leaves a hole (sorry)" in screen("sorry", library=True)
    assert "leaves a hole (admit)" in screen("admit", library=True)
    assert screen("sorry") is None  # Lean's answer reports a hole as a failure already
    assert "block comment" in screen("simp /- and the rest", library=True)
    assert "a proof is Lean text" in screen(None)  # type: ignore[arg-type]


def test_the_refused_words_are_the_designs() -> None:
    assert REFUSED_WORDS >= {
        "set_option",
        "run_tac",
        "elab",
        "elab_rules",
        "macro",
        "macro_rules",
        "syntax",
        "notation",
        "axiom",
        "unsafe",
        "native_decide",
        "namespace",
        "section",
        "end",
        "open",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "attribute",
        "import",
        "initialize",
    }


# }}}


# {{{ the oracle reads the table


class _Session:
    """A Mathlib session that answers yes to every attempt, and keeps what it was asked."""

    mathlib = "/a/mathlib/project"
    mathlib_revision = "a revision"
    version = "v4.29.1"
    error = None
    timeout = 60.0

    def ready(self) -> bool:
        return True


@pytest.fixture
def asked(monkeypatch) -> Iterator[tuple[LeanOracle, list[str]]]:
    """An oracle whose Lean says yes to everything, with the sources it was sent."""
    monkeypatch.setenv("LANKY_LEAN_PROOF_CACHE", "off")
    oracle = LeanOracle(session=_Session())  # type: ignore[arg-type]
    sent: list[str] = []

    def ask(session, source, until=None):
        sent.append(source)
        return True, "", False, True

    monkeypatch.setattr(oracle, "availability", lambda: (True, ""))
    monkeypatch.setattr(oracle, "_ask", ask)
    monkeypatch.setattr(oracle, "_cache_version", lambda: None)
    yield oracle, sent


def test_a_fact_of_the_library_is_proved_by_its_table_proof_alone(asked) -> None:
    oracle, sent = asked
    proved = oracle.establish(known.one_more_term.fact())
    assert proved.status is Status.PROVED
    assert proved.provenance["tactic"] == table.PROOFS["one_more_term"]
    assert len(sent) == 1
    assert sent[0].startswith("set_option autoImplicit false in\ntheorem Lanky.one_more_term")
    assert "  rw [last, Finset.sum_insert (by simp)]" in sent[0]


def test_a_theorem_named_like_a_fact_gets_the_ladder(asked) -> None:
    oracle, sent = asked
    proved = oracle.establish(_users_own.fact())
    assert proved.status is Status.PROVED
    assert table.PROOFS["log_of_a_power"] not in sent[0]


def test_a_refused_table_proof_declines_the_fact(asked, monkeypatch) -> None:
    oracle, sent = asked
    monkeypatch.setitem(table.PROOFS, "exp_of_a_sum", "simp\n#exit")
    declined = oracle.establish(known.exp_of_a_sum.fact())
    assert declined.status is Status.ASSUMED
    assert "exp_of_a_sum is refused: it runs the command #exit" in declined.provenance[
        "lean_declined"
    ]
    assert not sent


def test_a_pinned_tactic_still_comes_first(asked) -> None:
    oracle, sent = asked
    fact = known.abs_of_positive.fact()
    oracle.tactics[fact.id] = "exact abs_of_pos (by assumption)"
    oracle.establish(fact)
    assert sent and "exact abs_of_pos (by assumption)" in sent[0]


# }}}


# {{{ suggestions by shape


@theorem
def log_of_the_modulus(alpha: Complex, nonzero: alpha != 0) -> (
    log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
):
    """The design's example 1.3, with no proof: Lean's search alone does not prove it."""


def test_the_modulus_squared_fits_the_log_of_the_modulus() -> None:
    (only,) = suggestions(log_of_the_modulus.term)
    assert only.name == "modulus_squared"
    assert only.text == (
        "modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha"
    )


def test_a_fact_fits_only_terms_of_its_types() -> None:
    """``modulus_squared``'s ``z`` is complex, so the real ``x * conj(x)`` is not its shape."""

    @theorem
    def real_square(x: Real) -> real(x * conj(x)) == x**2:
        """x times itself."""

    assert [s.name for s in suggestions(real_square.term)] == []


def test_a_family_fits_what_the_claim_sums() -> None:
    @theorem
    def powers(r: Real, n: Nat) -> sum(r**k for k in Fin[n + 1]) >= 0:
        """Not a theorem; only its shape matters here."""

    texts = [s.text for s in suggestions(powers.term)]
    assert (
        "one_more_term rewrites sum(f[k] for k in Fin(n + 1)); "
        "here sum(r**k for k in Fin(n + 1)), at f = k -> r**k"
    ) in texts
    # a sum of anything fits fiber_exchange's right side, which is not said
    assert not any(text.startswith("fiber_exchange") for text in texts)


def test_a_factor_fits_what_the_others_leave() -> None:
    @theorem
    def scaled(x: Real, a: Fn[Nat, Real], n: Nat) -> (
        2 * x * sum(a[k] for k in Fin[n]) == sum(2 * x * a[k] for k in Fin[n])
    ):
        """distribute, at c = 2 * x."""

    texts = [s.text for s in suggestions(scaled.term)]
    assert texts[0] == (
        "distribute rewrites c*sum(f[k] for k in Fin(n)); "
        "here 2*x*sum(a[k] for k in Fin(n)), at c = 2*x, f = a"
    )


def test_an_inequality_bounds_the_side_it_fits() -> None:
    @theorem
    def bounded(z: Complex, w: Complex) -> abs(z + 2 * w) <= 3 * abs(w) + abs(z):
        """Only its shape matters here."""

    texts = [s.text for s in suggestions(bounded.term)]
    assert texts == [
        "complex_triangle_inequality bounds abs(z + w) from above; "
        "here abs(z + 2*w), at w = 2*w"
    ]


def test_a_sum_over_a_triangle_and_a_regrouped_sum_fit_their_exchanges() -> None:
    @theorem
    def triangle(q: Nat, D: Fn[Fin[q], Fin[q], Real]) -> (
        sum(D[a, b] for a in Fin[q] for b in Fin[q - a]) >= 0
    ):
        """Only its shape matters here."""

    @theorem
    def regrouped(
        nc: Nat, nv: Nat, cell: Fn[Fin[nc], Fin[nv]], h: Fn[Fin[nc], Real]
    ) -> sum(sum(h[p] for p in Fin[nc] if cell[p] == i) for i in Fin[nv]) >= 0:
        """Only its shape matters here."""

    assert suggestions(triangle.term)[0].text == (
        "triangle_exchange rewrites sum(f[a, b] for a in Fin(q), b in Fin(q - a)); "
        "here sum(D[a, b] for a in Fin(q), b in Fin(q - a)), at f = D"
    )
    assert suggestions(regrouped.term)[0].text.startswith(
        "fiber_exchange rewrites sum(sum(y[i] for i in Fin(n) if c[i] == j) for j in Fin(m)); "
        "here sum(sum(h[p] for p in Fin(nc) if cell[p] == i) for i in Fin(nv)), "
        "at n = nc, m = nv, c = cell, y = h"
    )


def test_a_step_with_its_types_given_gets_suggestions_too() -> None:
    """What a written proof's step report asks: a step is a comparison, its scope apart."""
    alpha = Var("alpha")
    step = log(abs(alpha) ** 2) / 2 == log(abs(alpha))
    texts = [s.text for s in suggestions(step, {"alpha": Complex})]
    # the two facts the demonstration's chain cites, each where it applies
    assert texts == [
        "log_of_a_power rewrites log(x**n); here log(abs(alpha)**2), at x = abs(alpha), n = 2",
        "modulus_squared, right to left, rewrites abs(z)**2; here abs(alpha)**2, at z = alpha",
    ]
    others = suggestions(step, {"alpha": Complex}, exclude=["log_of_a_power"])
    assert [s.name for s in others] == ["modulus_squared"]


def test_lanky_check_names_the_facts_that_fit_a_claim_lean_did_not_prove(capsys) -> None:
    fact = log_of_the_modulus.fact().with_status(
        Status.TESTED, "property-test", lean_tried=31, lean_reason="linarith failed"
    )
    untried = fact.with_status(Status.TESTED, "property-test", lean_tried=0)
    report_known([untried])  # type: ignore[arg-type]
    assert capsys.readouterr().out == ""
    report_known([fact])  # type: ignore[arg-type]
    printed = capsys.readouterr().out.splitlines()
    assert printed[1].startswith("NOT PROVED log_of_the_modulus at test_known.py:")
    assert printed[2:] == [
        "  Lean found no proof alone. What lanky knows of its shape:",
        "    modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha",
        "  A proof cites them by name: from lanky.known import modulus_squared",
    ]


def test_a_fact_of_the_library_is_not_suggested_for_itself(capsys) -> None:
    fact = known.modulus_squared.fact().with_status(
        Status.TESTED, "property-test", lean_tried=1, lean_reason="the proof failed"
    )
    report_known([fact])  # type: ignore[arg-type]
    assert "modulus_squared rewrites" not in capsys.readouterr().out


# }}}


# {{{ the demonstration


def test_the_demonstration_runs_as_a_program() -> None:
    done = subprocess.run(
        [sys.executable, str(DEMO)], capture_output=True, text=True, check=False
    )
    assert done.returncode == 0, done.stderr
    lines = done.stdout.splitlines()
    assert lines[0].split() == ["alpha", "log|alpha|", "log(alpha", "*", "conj(alpha))", "/", "2"]
    assert lines[1].startswith("(3+4j)")


def test_without_lean_the_demonstration_reads_tested(monkeypatch) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    (claim,) = [fact for fact in claims(check_path(DEMO)) if fact.owner == "log_of_the_modulus"]
    assert claim.status is Status.TESTED


# }}}


# {{{ with Lean and Mathlib


def _without_mathlib(reason: str) -> NoReturn:
    """Skip a test that needs Mathlib, or fail it where Mathlib was promised."""
    if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
        pytest.fail(f"LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but {reason}", pytrace=False)
    pytest.skip(reason)


@pytest.fixture(scope="module")
def mathlib_oracle(mathlib_project: str | None) -> Iterator[LeanOracle]:
    """One Mathlib session for the module, or a skip that says why not."""
    pytest.importorskip("lean_interact", reason="the Lean oracle needs lean-interact")
    if mathlib_project is None:
        _without_mathlib("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        _without_mathlib("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    timeout = float(os.environ.get("LANKY_LEAN_TEST_TIMEOUT", "120"))
    oracle = LeanOracle(session=LeanSession(timeout, mathlib=mathlib_project))
    available, reason = oracle.availability()
    if not available:
        _without_mathlib(f"no Lean oracle here: {reason}")
    if not oracle.session.start():
        _without_mathlib(f"the Mathlib session did not open: {oracle.session.error}")
    yield oracle
    oracle.session.close()


@pytest.mark.parametrize("entry", ENTRIES, ids=known.__all__)
def test_with_mathlib_every_fact_is_proved_by_its_table_proof(
    mathlib_oracle: LeanOracle, entry: Theorem, monkeypatch
) -> None:
    """The CI job's point: the table's proofs hold under the printer as it is."""
    monkeypatch.setenv("LANKY_LEAN_PROOF_CACHE", "off")
    proved = mathlib_oracle.establish(entry.fact())
    assert proved.status is Status.PROVED, proved.provenance.get("lean_reason")
    assert proved.decided_by == "lean"
    assert proved.provenance["tactic"] == table.PROOFS[entry.__name__]


def test_with_mathlib_the_two_facts_as_cited_prove_the_log_of_the_modulus(
    mathlib_oracle: LeanOracle,
) -> None:
    """The demonstration's proof as a written proof compiles it: the facts restated, a calc.

    The seam with the proof compiler: each fact is restated byte for byte
    from the proposition lanky prints for it, which its own command proved,
    and the chain's two links are closed as a link is, by the restated fact
    at the point lanky matched (``x := ‖alpha‖, n := 2`` and ``z := alpha``),
    with the literal exponent rewritten to ``2`` by ``rfl``.
    """
    claim = statement_of(log_of_the_modulus.term, "log_of_the_modulus", mathlib=True)
    cited = {
        entry.__name__: statement_of(entry.term, entry.__name__, mathlib=True).proposition
        for entry in (known.log_of_a_power, known.modulus_squared)
    }
    middle = render_term(log(abs(Var("alpha")) ** 2) / 2, claim.types, mathlib=True)
    left = render_term(log(abs(Var("alpha"))), claim.types, mathlib=True)
    right = render_term(
        log(real(Var("alpha") * conj(Var("alpha")))) / 2, claim.types, mathlib=True
    )
    restated = " ".join(f"({name} : {text})" for name, text in cited.items())
    source = (
        "set_option autoImplicit false in\n"
        f"theorem Lanky.log_of_the_modulus (alpha : ℂ) {restated} (nonzero : alpha ≠ 0) :\n"
        f"    {claim.goal} := by\n"
        f"  calc {left}\n"
        f"      = {middle} := by\n"
        "        have step := log_of_a_power ‖alpha‖ 2 (by norm_num)\n"
        "        rw [show Int.toNat 2 = 2 from rfl] at step\n"
        "        push_cast at step\n"
        "        linear_combination (-1 / 2 : ℝ) * step\n"
        f"    _ = {right} := by\n"
        "        rw [modulus_squared alpha]\n"
        "#print axioms Lanky.log_of_the_modulus\n"
    )
    closed, detail = mathlib_oracle.session.run(source)
    assert closed, f"{detail}\n{source}"


def test_with_mathlib_lean_alone_does_not_prove_the_demonstration_and_says_what_fits(
    mathlib_project: str | None, monkeypatch, capsys
) -> None:
    """Today's search fails on the claim, and the check names modulus_squared.

    Once proof bodies are read (the chains of written proofs), the
    demonstration's own proof proves it, citing the two facts; the test
    then checks that instead.
    """
    pytest.importorskip("lean_interact", reason="the Lean oracle needs lean-interact")
    if mathlib_project is None:
        _without_mathlib("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    if os.environ.get("LANKY_LEAN_DISABLE"):
        _without_mathlib("the Lean oracle is disabled by LANKY_LEAN_DISABLE")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    from lanky import cli

    (claim,) = [fact for fact in claims(check_path(DEMO)) if fact.owner == "log_of_the_modulus"]
    if hasattr(Var("alpha"), "equals"):
        # written proofs are read: the proof cites the two facts, and Lean checks it
        assert claim.status is Status.PROVED, claim.provenance
        return
    assert claim.status is Status.TESTED
    assert claim.provenance["lean_tried"] > 0
    cli.main(["check", str(DEMO)])
    printed = capsys.readouterr().out
    assert (
        "    modulus_squared rewrites real(z*conj(z)); here real(alpha*conj(alpha)), at z = alpha"
    ) in printed
    assert "  A proof cites them by name: from lanky.known import modulus_squared" in printed


# }}}
