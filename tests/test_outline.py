"""The proof lanky found, said back in Python: ``lanky check --proofs`` and ``--steps``.

Nothing here needs Lean. The plans are what the ladder's search finds
(:mod:`lanky.induction` and :mod:`lanky.sums`), which is Python, sympy's
for an induction, so those tests skip without sympy; the record is built from
the script that would close the claim, as the Lean oracle builds it when
Lean says the script closes it (``tests/test_mathlib.py`` runs that).
"""

from __future__ import annotations

from fractions import Fraction

import pytest

from lanky import claim, cli
from lanky.lean import statement_of
from lanky.ledger import Fact, Ledger, Status
from lanky.oracles.lean import tactic_ladder
from lanky.outline import (
    FamilyPlan,
    Script,
    SumPlan,
    found_proof,
    hypothesis_names,
    proof_lines,
    python_source,
    step_lines,
)
from lanky.prelude import Complex, Fin, Fn, Nat, Real
from lanky.terms import Elementary, Var

# {{{ claims


@claim
def compressed_taylor(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """What sumpy stores of a harmonic table, reconstructed, is the table (loopty's l2p.py)."""


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


@claim
def telescoping(
    f: Fn[Nat, Real],
    start: f(0) == 0,
    step: all(f(n + 1) == f(n) + 1 / ((n + 1) * (n + 2)) for n in Nat),
) -> all(f(n) == n / (n + 1) for n in Nat):
    """A sum of ``1 / ((n + 1)(n + 2))``, its base taken at ``n == 0``."""


@claim
def shifting(
    f: Fn[Nat, Fn[Nat, Real]],
    start: all(f(a)(0) == a for a in Nat),
    step: all(f(a)(n + 1) == f(a + 1)(n) for a in Nat for n in Nat),
) -> all(f(a)(n) == a + n for a in Nat for n in Nat):
    """Induced on ``n``, the second of the claim's variables."""


@claim
def helmholtz(
    k: Real,
    D: Fn[Nat, Fn[Nat, Real]],
    R: Fn[Nat, Fn[Nat, Real]],
    pde: all(D(a + 2)(b) + D(a)(b + 2) + k**2 * D(a)(b) == 0 for a in Nat for b in Nat),
    stored: all(R(a)(b) == D(a)(b) for a in Nat for b in Nat if a < 2),
    recurrence: all(R(a + 2)(b) == -R(a)(b + 2) - k**2 * R(a)(b) for a in Nat for b in Nat),
) -> all(R(a)(b) == D(a)(b) for a in Nat for b in Nat):
    """Helmholtz's PDE, whose step takes the claim at ``(a - 2, b)`` times ``-k**2``."""


@claim
def on_every_triangle(
    n: Nat,
    p: Nat,
    c: Fn[Nat, Nat, Nat, Real],
    D: Fn[Nat, Nat, Nat, Real],
    R: Fn[Nat, Nat, Nat, Real],
    pde: all(D[i, a + 2, b] + D[i, a, b + 2] == 0 for i in Fin[n] for a in Nat for b in Nat),
    stored: all(
        c[i, a, b] == D[i, a, b]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a < 2
        if a + b <= p
    ),
    copies: all(
        R[i, a, b] == c[i, a, b]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a < 2
        if a + b <= p
    ),
    recurrence: all(
        R[i, a + 2, b] == -R[i, a, b + 2]
        for i in Fin[n]
        for a in Nat
        for b in Nat
        if a + b + 2 <= p
    ),
) -> all(R[i, a, b] == D[i, a, b] for i in Fin[n] for a in Nat for b in Nat if a + b <= p):
    """The reconstruction on every box, through the copies of what is stored (loopty's l2p.py)."""


@claim
def stored_and_followed(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    table: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2)
    & all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """The reconstruction, with what is stored and the recurrence as one hypothesis."""


@claim
def exchange(
    n: Nat, m: Nat, f: Fn[Fin[n], Fin[m], Real]
) -> sum(sum(f[i, j] for j in Fin[m]) for i in Fin[n]) == sum(
    sum(f[i, j] for i in Fin[n]) for j in Fin[m]
):
    """Two finite sums exchange."""


@claim
def scaled(n: Nat, s: Real, f: Fn[Fin[n], Real]) -> sum(s * f[i] for i in Fin[n]) == s * sum(
    f[i] for i in Fin[n]
):
    """A factor comes out of a sum: no exchange, only the product distributed."""


@claim
def split_hypothesis(
    x: Nat,
    y: Nat,
    both: (x >= 1) & (y >= 1),
    sum_of: x + y == 3,
) -> x * y >= 2:
    """A hypothesis written ``p & q``, which is two conjuncts of the guard."""


@pytest.fixture
def searching():
    """sympy, which the search needs; skipped without it."""
    return pytest.importorskip("sympy")


def _found(claim) -> tuple[Fact, Script]:
    """The claim's fact as Lean would leave it proved by its first planned script."""
    fact = claim.fact()
    statement = statement_of(fact.term, claim.__name__, mathlib=True)
    ladder = tactic_ladder(statement)
    (script, *_) = [tactic for tactic in ladder if getattr(tactic, "plan", None) is not None]
    record = found_proof(fact, statement, script)
    return fact.with_status(Status.PROVED, "lean", found_proof=record), script


def _where(claim) -> str:
    return claim.fact().where


# }}}


# {{{ the induction


def test_the_reconstruction_is_printed_in_hint_form_as_the_design_shows(searching) -> None:
    """``lanky check --proofs`` on l2p.py: the body ready to paste, in the claim's names."""
    proved, script = _found(compressed_taylor)
    assert isinstance(script.plan, FamilyPlan)
    assert proof_lines(proved) == [
        f"PROOF compressed_taylor at {_where(compressed_taylor)}, "
        "by induction on a, two at a time:",
        "",
        "    for a, b in claim.dom:",
        "        if a < 2:",
        "            yield by(stored)",
        "        else:",
        "            yield by(recurrence(a - 2, b), claim[a - 2, b + 2], pde(a - 2, b))",
    ]


def test_its_steps_are_a_chain_from_one_side_to_the_other(searching) -> None:
    """``--steps``: each case a displayed calculation, with the point of every link."""
    proved, _ = _found(compressed_taylor)
    assert step_lines(proved) == [
        f"STEPS compressed_taylor at {_where(compressed_taylor)}, as lanky found them:",
        "  the claim at (a, b), for every a, b in Nat, by induction on a, two at a time",
        "    if a < 2:   R[a, b] == D[a, b]           by stored, at (a, b)",
        "    otherwise:  R[a, b] == -R[a - 2, b + 2]  by recurrence, at (a - 2, b)",
        "                        == -D[a - 2, b + 2]  by the claim at (a - 2, b + 2)",
        "                        == D[a, b]           by pde, at (a - 2, b)",
    ]


def test_without_the_terms_between_a_case_is_one_line(searching, monkeypatch) -> None:
    """Where sympy cannot write a chain, each case is its claim and the facts it rests on."""
    from lanky import outline

    def unwritten(*args):
        raise ValueError("no chain")

    monkeypatch.setattr(outline, "_sympy_chain", unwritten)
    proved, _ = _found(compressed_taylor)
    assert proved.provenance["found_proof"]["steps"][1:] == [
        "  if a < 2:   R[a, b] == D[a, b]  by stored, at (a, b)",
        "  otherwise:  R[a, b] == D[a, b]  from recurrence at (a - 2, b), "
        "the claim at (a - 2, b + 2) and pde at (a - 2, b)",
    ]


def test_a_base_the_guard_pins_to_one_order_reads_as_that_order(searching) -> None:
    """``n >= 1`` and a step of two leave the base ``n == 1``, where ``first_term`` is cited."""
    proved, _ = _found(line_taylor)
    record = proved.provenance["found_proof"]
    assert record["body"] == [
        "for n in claim.dom:",
        "    if n == 1:",
        "        yield by(first_term)",
        "    else:",
        "        yield by(ode(n - 1), claim[n - 1])",
    ]
    steps = record["steps"]
    assert steps[0] == (
        "the claim at n, for every n in Nat with n >= 1, by induction on n, two at a time"
    )
    # the claim at n == 1, with the power and the division by 1 that pinning leaves gone
    assert steps[1].startswith("  if n == 1:  a[1] == -(-beta / alpha)  ")
    assert steps[1].endswith("by first_term, times 1 / alpha")
    # the multiplier is named where it is not 1 or -1
    assert "by ode, at n - 1, times 1 / (alpha * n)" in steps[2]


def test_a_base_taken_one_order_at_a_time(searching) -> None:
    """``f(0) == 0`` says nothing below the step until the order is 0: ``if n == 0``."""
    proved, _ = _found(telescoping)
    assert proved.provenance["found_proof"]["body"] == [
        "for n in claim.dom:",
        "    if n == 0:",
        "        yield by(start)",
        "    else:",
        "        yield by(step(n - 1), claim[n - 1])",
    ]
    assert "if n == 0:  f[0] == 0  " in proved.provenance["found_proof"]["steps"][1]


def test_the_claim_takes_its_variables_in_order_whichever_is_induced_on(searching) -> None:
    """Induced on ``n``, the second variable; the hypothesis there is at ``a + 1``."""
    proved, _ = _found(shifting)
    assert proved.provenance["found_proof"]["body"] == [
        "for a, n in claim.dom:",
        "    if n == 0:",
        "        yield by(start)",
        "    else:",
        "        yield by(step(a, n - 1), claim[a + 1, n - 1])",
    ]


def test_a_multiplier_that_is_an_expression_is_said_in_the_steps(searching) -> None:
    """Helmholtz's step takes the claim at ``(a - 2, b)`` too, times ``-k**2``."""
    proved, _ = _found(helmholtz)
    record = proved.provenance["found_proof"]
    assert record["body"][4] == (
        "        yield by(recurrence(a - 2, b), claim[a - 2, b + 2], pde(a - 2, b), "
        "claim[a - 2, b])"
    )
    last = record["steps"][-1].strip()
    assert last.startswith("== D[a, b]  ")
    assert last.endswith("  by the claim at (a - 2, b), times -k**2")
    # a coefficient is written before the application it multiplies
    assert "-R[a - 2, b + 2] - k**2 * R[a - 2, b]" in record["steps"][2]


def test_a_fact_that_fits_the_claim_at_one_point_is_cited_by_name(searching) -> None:
    """``copies`` fits ``R[i, a, b]`` and ``stored`` fits ``D[i, a, b]``, each at one point.

    The step's facts fit the claim at two points each (``pde`` at ``(i, a -
    2, b)`` and ``(i, a, b - 2)``), so they keep theirs, as does the claim at
    a smaller point, which is the induction.
    """
    proved, _ = _found(on_every_triangle)
    record = proved.provenance["found_proof"]
    assert record["body"] == [
        "for i, a, b in claim.dom:",
        "    if a < 2:",
        "        yield by(copies, stored)",
        "    else:",
        "        yield by(recurrence(i, a - 2, b), claim[i, a - 2, b + 2], pde(i, a - 2, b))",
    ]
    assert record["steps"][0] == (
        "the claim at (i, a, b), for every i in Fin[n] and a, b in Nat with a + b <= p, "
        "by induction on a, two at a time"
    )
    assert record["steps"][1:3] == [
        "  if a < 2:   R[i, a, b] == c[i, a, b]           by copies, at (i, a, b)",
        "                         == D[i, a, b]           by stored, at (i, a, b)",
    ]


def test_both_parts_of_a_hypothesis_written_p_and_q_answer_to_its_name(searching) -> None:
    """``table`` is two conjuncts in Lean; the body cites it by its name in both cases."""
    proved, _ = _found(stored_and_followed)
    record = proved.provenance["found_proof"]
    assert record["body"][1:5] == [
        "    if a < 2:",
        "        yield by(table)",
        "    else:",
        "        yield by(table(a - 2, b), claim[a - 2, b + 2], pde(a - 2, b))",
    ]
    assert "by table, at (a - 2, b)" in record["steps"][2]


# }}}


# {{{ the sums


def test_an_exchange_of_sums_is_a_chain_through_the_order_found(searching) -> None:
    proved, script = _found(exchange)
    assert isinstance(script.plan, SumPlan)
    record = proved.provenance["found_proof"]
    assert record["how"] == "by putting the sums in one order"
    assert record["body"] == [
        "assert (",
        "    sum(sum(f[i, j] for j in Fin[m]) for i in Fin[n])",
        "    == sum(f[i, j] for j in Fin[m] for i in Fin[n])",
        "    == sum(sum(f[i, j] for i in Fin[n]) for j in Fin[m])",
        ")",
    ]
    assert record["steps"][0].endswith("the sums in the order j, i")
    assert record["steps"][1].endswith("the products distributed into the sums")


def test_sums_in_one_order_already_have_no_body() -> None:
    """Nothing is exchanged, so a body would say no more than the claim."""
    proved, _ = _found(scaled)
    record = proved.provenance["found_proof"]
    assert "body" not in record
    assert record["how"] == (
        "by distributing the products into the sums, which are in one order already"
    )
    assert proof_lines(proved) == [
        f"PROOF scaled at {_where(scaled)}, by distributing the products into the sums, "
        "which are in one order already"
    ]


# }}}


# {{{ the rest of the ladder


def test_a_whole_goal_tactic_is_named_in_words() -> None:
    fact = split_hypothesis.fact()
    statement = statement_of(fact.term, "split_hypothesis")
    assert found_proof(fact, statement, "omega") == {"how": "by integer arithmetic"}
    assert found_proof(fact, statement, "nlinarith")["how"] == (
        "by nonlinear arithmetic from its hypotheses"
    )
    assert found_proof(fact, statement, "intro x\nfirst | omega")["how"] == (
        "under its quantifiers, by arithmetic and simplification"
    )
    assert found_proof(fact, statement, "omega", given=True) == {
        "how": "by the Lean script use_tactic gives it"
    }
    # a rung the ladder named
    named = Script("induction ...", "by induction on n, taking the last term off the sum")
    assert found_proof(fact, statement, named)["how"] == (
        "by induction on n, taking the last term off the sum"
    )


def test_a_plan_that_cannot_be_said_leaves_the_rung() -> None:
    """The record is a view: a plan it cannot read costs the body, never the proof."""
    fact = split_hypothesis.fact()
    statement = statement_of(fact.term, "split_hypothesis")
    broken = Script("script", "by induction on n", plan=FamilyPlan(*(None,) * 10))
    assert found_proof(fact, statement, broken) == {"how": "by induction on n"}


def test_a_script_is_its_text() -> None:
    script = Script("omega", "by integer arithmetic")
    assert script == "omega"
    assert f"by {script}" == "by omega"
    assert str(script).__class__ is str


def test_the_lean_names_of_the_hypotheses_are_paired_with_the_python_ones() -> None:
    """``both`` is two conjuncts, ``x >= 1`` and ``y >= 1``, and both answer to its name."""
    fact = split_hypothesis.fact()
    statement = statement_of(fact.term, "split_hypothesis")
    names = hypothesis_names(fact, statement)
    lean = [name for (name, _), term in zip(
        statement.hypotheses, statement.hypothesis_terms, strict=True
    ) if term is not None]
    assert [names[name] for name in lean] == ["both", "both", "sum_of"]


def test_python_source_reads_as_ruff_writes_it() -> None:
    r, k, n, x, y = Var("r"), Var("k"), Var("n"), Var("x"), Var("y")
    R = Var("R")
    assert python_source(r**k) == "r**k"
    assert python_source(R[x, y] ** 2) == "R[x, y] ** 2"
    assert python_source(R(x)(y)) == "R[x, y]"
    assert python_source((n - 1) / n * r) == "(n - 1) / n * r"
    assert python_source(-(x * y)) == "-x * y"
    assert python_source(Fraction(1, 3) * x) == "1 / 3 * x"
    assert python_source(x - 2) == "x - 2"
    assert python_source(Elementary("log", x) / 2) == "log(x) / 2"


# }}}


# {{{ the command


def _ledger(found: dict | None, status: Status = Status.PROVED, kind: str = "claim") -> Ledger:
    ledger = Ledger()
    provenance = {} if found is None else {"found_proof": found}
    ledger.add(
        Fact(
            id="claim:claims.gauss@3",
            kind=kind,
            statement="n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)",
            status=status,
            decided_by="lean",
            provenance=provenance,
            where="claims.py:3",
            owner="gauss",
        )
    )
    return ledger


def test_proofs_prints_the_body_and_steps_the_outline(capsys) -> None:
    found = {
        "how": "by induction on n",
        "body": ["for n in claim.dom:", "    yield by(step(n - 1), claim[n - 1])"],
        "steps": ["the claim at n, for every n in Nat, by induction on n", "  ..."],
    }
    cli.report_proofs(_ledger(found))
    cli.report_steps(_ledger(found), "gauss")
    assert capsys.readouterr().out.splitlines() == [
        "",
        "PROOF gauss at claims.py:3, by induction on n:",
        "",
        "    for n in claim.dom:",
        "        yield by(step(n - 1), claim[n - 1])",
        "",
        "STEPS gauss at claims.py:3, as lanky found them:",
        "  the claim at n, for every n in Nat, by induction on n",
        "    ...",
    ]


def test_proofs_names_the_rung_where_python_cannot_say_more(capsys) -> None:
    cli.report_proofs(_ledger({"how": "by integer arithmetic"}))
    cli.report_steps(_ledger({"how": "by integer arithmetic"}))
    assert capsys.readouterr().out.splitlines() == [
        "",
        "PROOF gauss at claims.py:3, by integer arithmetic",
        "",
        "STEPS gauss at claims.py:3, as lanky found them:",
        "  the claim, by integer arithmetic",
    ]


def test_proofs_leaves_out_what_was_not_proved_and_what_is_not_a_theorem(capsys) -> None:
    cli.report_proofs(_ledger({"how": "by algebra"}, status=Status.TESTED))
    cli.report_proofs(_ledger({"how": "by algebra"}, kind="in-bounds"))
    cli.report_steps(_ledger({"how": "by algebra"}), "nothing like it")
    assert capsys.readouterr().out.splitlines() == [
        "",
        "PROOF no claim was proved",
        "",
        "PROOF no claim was proved",
        "",
        "STEPS no claim was proved among those matching 'nothing like it'",
    ]


def test_a_file_given_to_proofs_is_checked(tmp_path, capsys) -> None:
    """``lanky check --proofs FILE`` hands the option the file, which is taken back as one."""
    path = tmp_path / "claims.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import claim\n"
        "from lanky.prelude import Nat\n\n\n"
        "@claim\n"
        "def plus_zero(n: Nat) -> n + 0 == n:\n"
        '    """Adding nothing."""\n',
        encoding="utf-8",
    )
    assert cli.main(["check", "--proofs", str(path)]) == 0
    printed = capsys.readouterr().out
    assert "plus_zero" in printed
    assert "PROOF " in printed


def test_files_are_checked_in_the_order_the_command_names_them(tmp_path, capsys) -> None:
    """``--proofs a.py b.py`` takes ``a.py`` as its text, and checks it first (Codex, #171)."""
    names = []
    for name in ("first", "second"):
        path = tmp_path / f"{name}.py"
        path.write_text(
            "from __future__ import annotations\n\n"
            "from lanky import claim\n"
            "from lanky.prelude import Nat\n\n\n"
            "@claim\n"
            f"def {name}_plus_zero(n: Nat) -> n + 0 == n:\n"
            '    """Adding nothing."""\n',
            encoding="utf-8",
        )
        names.append(str(path))
    assert cli.main(["check", "--proofs", *names]) == 0
    printed = capsys.readouterr().out
    assert printed.index(f"==> {names[0]} <==") < printed.index(f"==> {names[1]} <==")
    # and with the value attached to the option
    assert cli.main(["check", f"--proofs={names[0]}", names[1]]) == 0
    printed = capsys.readouterr().out
    assert printed.index(f"==> {names[0]} <==") < printed.index(f"==> {names[1]} <==")


def test_check_with_no_file_says_so(capsys) -> None:
    assert cli.main(["check"]) == 2
    assert "name a file to check" in capsys.readouterr().out


# }}}
