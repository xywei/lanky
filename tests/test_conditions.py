"""Named conditions: ``@condition``, and the theorems of a ``with`` block holding under one.

A condition is read off a typed function with no conclusion and no body. It
says natively whether it holds, it is a hypothesis of any theorem, and ``with
segment as (alpha, beta, nonzero):`` puts every theorem defined in the block
under it. Most of that is Python, and is tested without Lean: the reading, the
refusals, the statements, the property tester's draws, the faithfulness check
and the trace of a written proof. Lean checks a written proof under a
condition over the integers where Lean is, and the line-Taylor theorems under
``segment`` where Mathlib is.
"""

from __future__ import annotations

import os
import subprocess
import sys
import textwrap
from fractions import Fraction
from pathlib import Path

import pytest

from conftest import claims
from lanky import Condition, condition, theorem
from lanky.check import check_path, import_path
from lanky.ledger import Status, statement_lines
from lanky.prelude import Int, Real
from lanky.proofs import compile_proof, trace_proof
from lanky.terms import LogicalAnd, Var, render

ROOT = Path(__file__).resolve().parent.parent


def _module(tmp_path, source: str, name: str = "conditions_case"):
    """``source`` written to a file of its own and imported, as ``lanky check`` imports it."""
    path = tmp_path / f"{name}.py"
    path.write_text(textwrap.dedent(source), encoding="utf-8")
    return import_path(path)


def _refused(tmp_path, source: str) -> str:
    """What importing ``source`` is refused with."""
    with pytest.raises(TypeError) as refused:
        _module(tmp_path, source, "refused")
    return str(refused.value)


HEAD = """\
from __future__ import annotations

from lanky import by, claim, condition, theorem
from lanky.prelude import Complex, Fn, Int, Nat, Real
"""

#: The CFL condition of an explicit upwind scheme, and theorems that hold under it.
CFL = (
    HEAD
    + '''

@condition
def cfl(c: Real, dt: Real, h: Real, positive: h > 0, stable: c * dt <= h):
    """The CFL condition of an explicit upwind scheme for u_t + c u_x = 0."""


@theorem
def courant(c: Real, dt: Real, h: Real, ok: cfl(c, dt, h)) -> c * dt / h <= 1:
    """Under the CFL condition the Courant number is at most one."""


with cfl as (c, dt, h, positive, stable):

    @theorem
    def courant_in_block(k: Real, small: k >= 0) -> c * dt / h <= 1 + k:
        """The Courant number, under with cfl, is at most one plus anything not negative."""

    @theorem
    def step_fits(dx: Real, inside: dx <= c * dt) -> dx <= h:
        """What the scheme moves in a step is at most a cell."""
'''
)

#: The two line-Taylor theorems of loopty's layer potential, under one segment.
SEGMENT = (
    HEAD
    + '''

def coefficient(ratio, k):
    """The k-th Taylor coefficient of log(alpha + tau * beta), k >= 1."""
    return -(ratio**k) / k


@condition
def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
    """A source segment alpha + tau * beta that does not pass through zero."""


with segment as (alpha, beta, nonzero):

    @theorem
    def line_taylor(
        a: Fn[Nat, Complex],
        first_term: alpha * a[1] == beta,
        ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
    ) -> all(a[n] == coefficient(-beta / alpha, n) for n in Nat if n >= 1):
        """The line-Taylor coefficients of log(alpha + tau * beta), at every order."""
        for n in claim.dom:
            if n == 1:
                yield by(first_term)
            else:
                assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode)
                yield by(claim[n - 1])

    @theorem
    def reciprocal_taylor(
        b: Fn[Nat, Complex],
        first_term: b[0] == 1,
        ode: all(alpha * b[n + 1] + beta * b[n] == 0 for n in Nat),
    ) -> all(b[n] == (-beta / alpha) ** n for n in Nat):
        """The line-Taylor coefficients of alpha / (alpha + tau * beta), at every order."""
        for n in claim.dom:
            if n == 0:
                yield by(first_term)
            else:
                assert b[n] == (-beta / alpha) * b[n - 1], by(ode)
                yield by(claim[n - 1])
'''
)

#: A written proof over the integers under a condition, which core Lean checks.
TABLE = (
    HEAD
    + '''

@condition
def harmonic_table(
    D: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
):
    """The derivatives of a harmonic function, as a table: D[a + 2, b] == -D[a, b + 2]."""


with harmonic_table as (D, pde):

    @theorem
    def ct(
        R: Fn[Nat, Nat, Int],
        stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
        recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
    ) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
        """What sumpy stores of a harmonic table, rebuilt by the recurrence, is the table."""
        for a, b in claim.dom:
            if a < 2:
                yield by(stored)
            else:
                yield by(recurrence(a - 2, b), claim[a - 2, b + 2], pde(a - 2, b))

    @theorem
    def ct_wrong(
        R: Fn[Nat, Nat, Int],
        stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
        recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
    ) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
        """The same, citing the claim at a point that does not make the step follow."""
        for a, b in claim.dom:
            if a < 2:
                yield by(stored)
            else:
                yield by(recurrence(a - 2, b), claim[a - 2, b + 3], pde(a - 2, b))
'''
)


@pytest.fixture(scope="module")
def cfl(tmp_path_factory):
    """The CFL module, imported."""
    return _module(tmp_path_factory.mktemp("cfl"), CFL, "cfl_case")


@pytest.fixture(scope="module")
def segment(tmp_path_factory):
    """The segment module, imported."""
    return _module(tmp_path_factory.mktemp("segment"), SEGMENT, "segment_case")


# {{{ a condition


def test_a_condition_reads_its_variables_and_named_conditions(cfl) -> None:
    assert isinstance(cfl.cfl, Condition)
    assert [name for name, _ in cfl.cfl.variables] == ["c", "dt", "h"]
    assert [name for name, _ in cfl.cfl.hypotheses] == ["positive", "stable"]
    assert cfl.cfl.names == ("c", "dt", "h", "positive", "stable")
    assert cfl.cfl.label == "cfl (positive, stable)"
    assert cfl.cfl.signature == (
        "cfl(c: Real, dt: Real, h: Real, positive: h > 0, stable: c * dt <= h)"
    )
    assert repr(cfl.cfl) == f"<condition {cfl.cfl.signature}>"
    assert cfl.cfl.__doc__.startswith("The CFL condition")
    assert render(cfl.cfl.term) == "h > 0 and c*dt <= h"


def test_a_condition_called_at_values_says_whether_it_holds(cfl, segment) -> None:
    assert cfl.cfl(c=1, dt=Fraction(1, 10), h=Fraction(1, 5)) is True
    assert cfl.cfl(1, Fraction(1, 10), Fraction(1, 5)) is True
    assert cfl.cfl(c=3, dt=1, h=1) is False
    assert cfl.cfl(c=1, dt=1, h=0) is False
    assert segment.segment(alpha=2, beta=1) is True
    assert segment.segment(alpha=0, beta=1) is False


def test_a_condition_call_says_what_to_give_it(cfl) -> None:
    with pytest.raises(TypeError, match="cfl needs values for h"):
        cfl.cfl(c=1, dt=1)
    with pytest.raises(TypeError, match="stable is a condition of cfl, which the call answers"):
        cfl.cfl(c=1, dt=1, h=1, stable=True)
    with pytest.raises(TypeError, match="cfl has no variable dx: its variables are c, dt, h"):
        cfl.cfl(c=1, dt=1, dx=1)
    with pytest.raises(TypeError, match="cfl is given c twice"):
        cfl.cfl(1, 1, 1, c=1)
    with pytest.raises(TypeError, match="takes the values of its variables, c, dt, h"):
        cfl.cfl(1, 1, 1, 1)


def test_a_condition_called_at_symbolic_values_is_the_proposition(cfl) -> None:
    applied = cfl.cfl(Var("u"), Var("k"), 2)
    assert isinstance(applied, LogicalAnd)
    assert render(applied) == "2 > 0 and u*k <= 2"


def test_a_condition_is_a_hypothesis_of_any_theorem(cfl) -> None:
    courant = cfl.courant
    assert [name for name, _ in courant.hypotheses] == ["ok"]
    assert courant.statement == (
        "c : Real, dt : Real, h : Real | h > 0 and c*dt <= h |- c*dt / h <= 1"
    )
    assert courant.hypothesis_names == ("ok_1", "ok_2")
    assert courant.under == () and courant.cited_under == ""
    assert courant(c=1, dt=Fraction(1, 10), h=Fraction(1, 5)).holds
    report = courant.report()
    assert report.ok and report.valid > 0
    reading = courant.faithful_fact()
    assert reading.status is Status.TESTED, reading.provenance


def test_a_condition_has_no_conclusion_and_no_body(tmp_path) -> None:
    concluded = _refused(
        tmp_path,
        HEAD
        + """
        @condition
        def positive(h: Real) -> h > 0:
            '''A conclusion.'''
        """.replace("\n        ", "\n"),
    )
    assert "a condition has no conclusion" in concluded and "@theorem" in concluded
    bodied = _refused(
        tmp_path,
        HEAD
        + """
        @condition
        def positive(h: Real, ok: h > 0):
            '''A body.'''
            return ok
        """.replace("\n        ", "\n"),
    )
    assert "a condition has no body" in bodied
    defaulted = _refused(
        tmp_path,
        HEAD
        + """
        @condition
        def positive(h: Real = 1, ok: h > 0 = True):
            '''Defaults.'''
        """.replace("\n        ", "\n"),
    )
    assert "each a plain name with an annotation" in defaulted
    with pytest.raises(TypeError, match="@condition decorates a typed function"):
        condition("cfl")


# }}}


# {{{ a with block


def test_theorems_in_a_with_block_hold_under_the_condition(segment) -> None:
    for claim, own in ((segment.line_taylor, "a"), (segment.reciprocal_taylor, "b")):
        assert [name for name, _ in claim.variables] == ["alpha", "beta", own]
        assert [name for name, _ in claim.hypotheses] == ["nonzero", "first_term", "ode"]
        assert claim.hypothesis_names == ("nonzero", "first_term", "ode")
        assert claim.conditions == (segment.segment,)
        assert claim.bound == ("alpha", "beta", "nonzero")
        assert [name for name, _ in claim.own_variables] == [own]
        assert claim.under_label == "segment (nonzero)"
        assert claim.cited_under == "under segment"
        binders = [var.name for var, _ in claim.term.binders]
        assert binders == ["alpha", "beta", own]
        assert claim.statement.startswith(f"under segment (nonzero): {own} : Fn[Nat, Complex] | ")
    assert segment.line_taylor.statement == (
        "under segment (nonzero): a : Fn[Nat, Complex] | alpha*a[1] == beta, forall n in Nat "
        "where n >= 1. (n + 1)*alpha*a[n + 1] + n*beta*a[n] == 0 |- forall n in Nat where "
        "n >= 1. a[n] == -(-beta / alpha)**n / n"
    )


def test_the_ledger_names_the_condition_before_the_theorems_own_parts(segment) -> None:
    fact = segment.line_taylor.fact()
    sequent = fact.provenance["sequent"]
    assert sequent["under"] == "segment (nonzero)"
    assert [name for name, _ in sequent["hypotheses"]] == ["nonzero", "first_term", "ode"]
    assert [name for name, _ in sequent["own"]["hypotheses"]] == ["first_term", "ode"]
    assert statement_lines(fact, width=60) == [
        "under segment (nonzero): a : Fn[Nat, Complex]",
        "| first_term: alpha*a[1] == beta",
        "| ode: forall n in Nat where n >= 1.",
        "    (n + 1)*alpha*a[n + 1] + n*beta*a[n] == 0",
        "|- forall n in Nat where n >= 1.",
        "    a[n] == -(-beta / alpha)**n / n",
    ]


def test_a_theorem_under_a_condition_takes_the_conditions_variables_natively(cfl) -> None:
    verdict = cfl.courant_in_block(c=1, dt=Fraction(1, 10), h=Fraction(1, 5), k=0)
    assert verdict.hypotheses == {"positive": True, "stable": True, "small": True}
    assert verdict.holds
    # where the condition fails, the statement is not violated: its hypotheses are not met
    verdict = cfl.courant_in_block(c=3, dt=1, h=1, k=0)
    assert verdict.hypotheses["stable"] is False and verdict.holds
    with pytest.raises(TypeError, match="courant_in_block needs values for h"):
        cfl.courant_in_block(c=1, dt=1, k=0)


def test_the_property_tester_draws_the_conditions_variables_satisfying_its_conditions(
    cfl,
) -> None:
    """``dx <= h`` follows only from ``stable``: a draw that ignored it would refute the claim."""
    for claim in (cfl.courant_in_block, cfl.step_fits):
        report = claim.report()
        assert report.ok and report.valid > 0, report


def test_the_faithfulness_check_runs_the_conditions_annotations_too(segment, cfl) -> None:
    for claim, count in (
        (segment.line_taylor, 7),
        (segment.reciprocal_taylor, 7),
        (cfl.courant_in_block, 8),
    ):
        reading = claim.faithful_fact()
        assert reading.status is Status.TESTED, reading.provenance
        assert reading.provenance["compared"] == reading.provenance["draws"] * count


UNFAITHFUL = (
    HEAD
    + '''

def shifted(x):
    """x + 1 at a number, and x itself at a term: a reading that says something else."""
    return x + 1 if isinstance(x, int) else x


@condition
def above(x: Int, ok: shifted(x) >= 1):
    """x is at least one, as the helper has it."""


with above as (x, ok):

    @theorem
    def under_above(y: Int, same: y == x) -> y >= 1:
        """Under the misread condition."""


@theorem
def cites_above(z: Int, h: above(z)) -> z >= 1:
    """With the misread condition as a hypothesis."""
'''
)


def test_a_misread_condition_is_refuted_under_a_block_and_as_a_hypothesis(tmp_path) -> None:
    module = _module(tmp_path, UNFAITHFUL, "unfaithful_case")
    under = module.under_above.faithful_fact()
    assert under.status is Status.REFUTED, under.provenance
    assert "ok of above" in under.provenance["reason"]
    cited = module.cites_above.faithful_fact()
    assert cited.status is Status.REFUTED, cited.provenance
    assert "the hypothesis h" in cited.provenance["reason"]


def test_the_lean_statement_has_the_conditions_variables_and_hypotheses(segment, cfl) -> None:
    from lanky.lean import statement_of

    printed = segment.line_taylor.lean(mathlib=True)
    assert printed.startswith("∀ alpha : ℂ, ∀ beta : ℂ, ∀ a : Int → ℂ, alpha ≠ 0 → ")
    claim = cfl.step_fits
    statement = statement_of(
        claim.term, "step_fits", mathlib=True, hypotheses=claim.hypothesis_names
    )
    assert [name for name, _ in statement.binders] == ["c", "dt", "h", "dx"]
    assert [name for name, _ in statement.hypotheses] == ["positive", "stable", "inside"]


def test_the_body_reads_the_conditions_names_from_its_namespace(segment, cfl) -> None:
    from lanky.proofs.trace import body_arguments

    theorem = segment.line_taylor
    values = {name: Var(name) for name in ("alpha", "beta", "a", "nonzero", "first_term", "ode")}
    positional, named, outer = body_arguments(theorem.fn, values)
    assert positional == () and sorted(named) == ["a", "first_term", "ode"]
    assert sorted(outer) == sorted(theorem.bound) == ["alpha", "beta", "nonzero"]
    positional, named, outer = body_arguments(cfl.courant.fn, {"c": 1, "dt": 1, "h": 1, "ok": True})
    assert sorted(named) == ["c", "dt", "h", "ok"] and outer == {}


# }}}


# {{{ what a with statement is refused for


def test_a_with_statement_with_other_names_is_refused_with_the_signature(tmp_path) -> None:
    head = HEAD + textwrap.dedent(
        '''

        @condition
        def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
            """A segment."""

        '''
    )
    signature = "segment(alpha: Complex, beta: Complex, nonzero: alpha != 0)"
    line = "write with segment as (alpha, beta, nonzero):"
    fewer = _refused(tmp_path, head + "with segment as (alpha, beta):\n    pass\n")
    assert fewer == (
        f"with segment as (alpha, beta): binds 2 names, and segment has 3 variables and "
        f"conditions, {signature}; {line}"
    )
    renamed = _refused(tmp_path, head + "with segment as (alpha, b, nonzero):\n    pass\n")
    assert renamed == (
        f"with segment as (alpha, b, nonzero): names them otherwise than {signature} does "
        "(b for beta): a theorem under segment reads its variables and conditions by their "
        f"names; {line}"
    )
    swapped = _refused(tmp_path, head + "with segment as (beta, alpha, nonzero):\n    pass\n")
    assert "(beta for alpha, alpha for beta)" in swapped
    single = _refused(tmp_path, head + "with segment as s:\n    pass\n")
    assert single.startswith("with segment as s: binds one name") and line in single
    bare = _refused(tmp_path, head + "with segment:\n    pass\n")
    assert bare.startswith("with segment: binds nothing") and line in bare


def test_a_theorem_in_the_block_that_declares_a_bound_name_is_refused(tmp_path) -> None:
    refused = _refused(
        tmp_path,
        HEAD
        + textwrap.dedent(
            '''

            @condition
            def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
                """A segment."""


            with segment as (alpha, beta, nonzero):

                @theorem
                def again(alpha: Complex, x: Complex) -> x * alpha == alpha * x:
                    """alpha twice."""
            '''
        ),
    )
    assert refused.startswith("again at refused.py:")
    assert refused.endswith(
        "alpha is segment's, which with segment as (alpha, beta, nonzero) binds for every "
        "theorem in the block; drop the parameter alpha, or define again outside the block"
    )


def test_a_bound_name_used_after_the_block_is_refused(tmp_path) -> None:
    head = HEAD + textwrap.dedent(
        '''

        @condition
        def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
            """A segment."""


        with segment as (alpha, beta, nonzero):

            @theorem
            def inside(x: Complex) -> x * alpha == alpha * x:
                """Inside."""

        '''
    )
    in_annotation = _refused(
        tmp_path,
        head
        + textwrap.dedent(
            '''
            @theorem
            def outside(x: Complex) -> x * alpha == alpha * x:
                """Outside."""
            '''
        ),
    )
    assert in_annotation.endswith(
        "alpha belongs to segment; use it inside with segment as (alpha, beta, nonzero):"
    )
    assert in_annotation.startswith("outside at refused.py:")
    in_body = _refused(
        tmp_path,
        head
        + textwrap.dedent(
            '''
            @theorem
            def outside(x: Complex, h: x != 0) -> x / x == 1:
                """Outside, its body reading beta."""
                return beta
            '''
        ),
    )
    assert "beta belongs to segment" in in_body


def test_a_condition_in_force_twice_or_a_name_two_conditions_bind_is_refused(tmp_path) -> None:
    head = HEAD + textwrap.dedent(
        '''

        @condition
        def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
            """A segment."""


        @condition
        def ratio(alpha: Real, small: alpha < 1):
            """Another alpha, a real one."""

        '''
    )
    twice = _refused(
        tmp_path,
        head
        + "with segment as (alpha, beta, nonzero):\n"
        + "    with segment as (alpha, beta, nonzero):\n        pass\n",
    )
    assert "is inside a with block of segment already" in twice
    clash = _refused(
        tmp_path,
        head + "with segment as (alpha, beta, nonzero), ratio as (alpha, small):\n    pass\n",
    )
    assert clash.startswith("with ratio as (alpha, small): binds alpha, which with segment")


def test_a_condition_is_defined_outside_every_with_block(tmp_path) -> None:
    refused = _refused(
        tmp_path,
        HEAD
        + textwrap.dedent(
            '''

            @condition
            def positive(h: Real, ok: h > 0):
                """h is positive."""


            with positive as (h, ok):

                @condition
                def smaller(k: Real, below: k < h):
                    """k is below h."""
            '''
        ),
    )
    assert "a condition is defined outside every with block" in refused


# }}}


# {{{ composing conditions


COMPOSED = (
    HEAD
    + '''

@condition
def mesh(h: Real, positive: h > 0):
    """A uniform mesh of width h."""


@condition
def cfl(c: Real, dt: Real, h: Real, stable: c * dt <= h):
    """The CFL condition."""


@condition
def speed(c: Real, forward: c >= 0):
    """A wave that moves to the right."""


with mesh as (h, positive), speed as (c, forward):

    @theorem
    def in_one_statement(x: Real, inside: x >= 0) -> x + h * c >= 0:
        """Under mesh and speed, in one with statement."""


with (
    mesh as (h, positive),
    cfl as (c, dt, h, stable),
):

    @theorem
    def parenthesized(dx: Real, moves: dx <= c * dt) -> dx <= h:
        """Under mesh and cfl, which share h."""


with mesh as (h, positive):
    with speed as (c, forward):

        @theorem
        def nested(x: Real, inside: x >= 0) -> x + h * c >= 0:
            """Under mesh and speed, nested."""

    @theorem
    def outer_only(x: Real, inside: x >= 0) -> x * h >= 0:
        """Under mesh alone, after the inner block."""
'''
)


def test_conditions_compose_in_one_with_statement_and_by_nesting(tmp_path) -> None:
    module = _module(tmp_path, COMPOSED, "composed_case")
    for claim in (module.in_one_statement, module.nested):
        assert claim.conditions == (module.mesh, module.speed)
        assert [name for name, _ in claim.variables] == ["h", "c", "x"]
        assert [name for name, _ in claim.hypotheses] == ["positive", "forward", "inside"]
        assert claim.statement.startswith("under mesh (positive), speed (forward): x : Real | ")
        assert claim.cited_under == "under mesh, speed"
        assert claim.report().ok
        assert claim.faithful_fact().status is Status.TESTED
    shared = module.parenthesized
    assert shared.conditions == (module.mesh, module.cfl)
    assert [name for name, _ in shared.variables] == ["h", "c", "dt", "dx"]
    assert [name for name, _ in shared.hypotheses] == ["positive", "stable", "moves"]
    assert shared.report().ok
    assert shared.faithful_fact().status is Status.TESTED
    assert module.outer_only.conditions == (module.mesh,)
    assert module.outer_only.under_label == "mesh (positive)"


# }}}


# {{{ written proofs under a condition


def test_a_written_proof_under_a_condition_reads_the_bound_names(tmp_path) -> None:
    module = _module(tmp_path, TABLE, "table_case")
    proof = trace_proof(module.ct)
    cited = {citation.name for leaf in proof.leaves for citation in leaf.facts or ()}
    assert {"stored", "recurrence", "pde", "claim"} <= cited
    command = compile_proof(proof, mathlib=False)
    assert "(pde :" in command.source and "theorem Lanky.ct" in command.source


def test_the_line_taylor_theorems_under_segment_trace_and_read_faithfully(segment) -> None:
    for claim in (segment.line_taylor, segment.reciprocal_taylor):
        proof = trace_proof(claim)
        assert proof.claim is not None and proof.claim.params == ("n",)
        assert claim.faithful_fact().status is Status.TESTED


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


def test_lean_checks_a_written_proof_under_a_condition(tmp_path) -> None:
    _lean_or_skip()
    path = tmp_path / "table_core.py"
    path.write_text(TABLE, encoding="utf-8")
    checked = {fact.owner: fact for fact in claims(check_path(path))}
    proved = checked["ct"]
    assert proved.status is Status.PROVED and proved.decided_by == "lean"
    assert proved.provenance["proof"]["closed"] is True, proved.provenance["proof"]
    assert proved.statement.startswith("under harmonic_table (pde): R : Fn[Nat, Nat, Int] | ")
    (failure,) = checked["ct_wrong"].provenance["proof"]["failures"]
    assert failure["kind"] == "step"
    assert failure["source"].startswith("yield by(recurrence(a - 2, b), claim[a - 2, b + 3]")


def test_mathlib_proves_line_taylor_and_reciprocal_taylor_under_segment(
    mathlib_project, monkeypatch, tmp_path
) -> None:
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but no project is named")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    path = tmp_path / "segment_mathlib.py"
    path.write_text(SEGMENT, encoding="utf-8")
    checked = {fact.owner: fact for fact in claims(check_path(path))}
    for owner in ("line_taylor", "reciprocal_taylor"):
        fact = checked[owner]
        assert fact.status is Status.PROVED and fact.decided_by == "lean", fact.provenance
        assert fact.provenance["proof"]["closed"] is True


# }}}


# {{{ the quickstart's example


def _shown(command: str) -> list[str]:
    """The lines the quickstart shows under ``$ command``, up to the end of its block."""
    lines = (ROOT / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    start = lines.index(f"$ {command}")
    shown = []
    for line in lines[start + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line.rstrip())
    return shown


def test_the_quickstart_shows_what_the_upwind_example_prints() -> None:
    printed = subprocess.run(
        [sys.executable, str(ROOT / "examples" / "upwind.py")],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    assert _shown("uv run python examples/upwind.py") == printed


def test_the_quickstart_shows_the_ledger_of_the_upwind_example(capsys, monkeypatch) -> None:
    """The table and its summary, which read the same with core Lean and without Lean."""
    from lanky import cli

    monkeypatch.delenv("LANKY_LEAN_MATHLIB", raising=False)
    assert cli.main(["check", str(ROOT / "examples" / "upwind.py")]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    shown = _shown("uv run lanky check examples/upwind.py")
    assert printed[: len(shown)] == shown


# }}}


def test_lanky_exports_condition() -> None:
    import lanky

    assert lanky.condition is condition and lanky.Condition is Condition
    assert theorem is lanky.theorem and Int is lanky.Int and Real is lanky.Real
