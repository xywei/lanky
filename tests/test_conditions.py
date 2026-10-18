"""Named conditions, ``@condition``, and ``with``: the claims of a block hold under what it assumes.

A condition is read off a typed function with no goal and no body. It says
natively whether it holds, it is a hypothesis of any claim, and ``with
segment as (alpha, beta, nonzero):`` puts every claim defined in the block
under it. A ``with`` statement assumes a claim's conditions, or a whole
claim, the same way. Most of that is Python, and is tested without Lean: the reading, the
refusals, the statements, the property tester's draws, the faithfulness check
and the trace of a written proof. Lean checks a written proof under a
condition over the integers where Lean is, and the line-Taylor claims under
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
from lanky import Condition, ConditionNotMet, Conditions, claim, condition
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

from lanky import by, claim, condition
from lanky.prelude import Complex, Fn, Int, Nat, Real
"""

#: The CFL condition of an explicit upwind scheme, and claims that hold under it.
CFL = (
    HEAD
    + '''

@condition
def cfl(c: Real, dt: Real, h: Real, positive: h > 0, stable: c * dt <= h):
    """The CFL condition of an explicit upwind scheme for u_t + c u_x = 0."""


@claim
def courant(c: Real, dt: Real, h: Real, ok: cfl(c, dt, h)) -> c * dt / h <= 1:
    """Under the CFL condition the Courant number is at most one."""


with cfl as (c, dt, h, positive, stable):

    @claim
    def courant_in_block(k: Real, small: k >= 0) -> c * dt / h <= 1 + k:
        """The Courant number, under with cfl, is at most one plus anything not negative."""

    @claim
    def step_fits(dx: Real, inside: dx <= c * dt) -> dx <= h:
        """What the scheme moves in a step is at most a cell."""
'''
)

#: The two line-Taylor claims of loopty's layer potential, under one segment.
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

    @claim
    def line_taylor(
        a: Fn[Nat, Complex],
        first_term: alpha * a[1] == beta,
        ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
    ) -> all(a[n] == coefficient(-beta / alpha, n) for n in Nat if n >= 1):
        """The line-Taylor coefficients of log(alpha + tau * beta), at every order."""
        for n in line_taylor.conclusion.domain:
            if n == 1:
                yield by(first_term)
            else:
                assert a[n] == (n - 1) / n * (-beta / alpha) * a[n - 1], by(ode[n - 1])
                yield by(line_taylor.conclusion[n - 1])

    @claim
    def reciprocal_taylor(
        b: Fn[Nat, Complex],
        first_term: b[0] == 1,
        ode: all(alpha * b[n + 1] + beta * b[n] == 0 for n in Nat),
    ) -> all(b[n] == (-beta / alpha) ** n for n in Nat):
        """The line-Taylor coefficients of alpha / (alpha + tau * beta), at every order."""
        for n in reciprocal_taylor.conclusion.domain:
            if n == 0:
                yield by(first_term)
            else:
                assert b[n] == (-beta / alpha) * b[n - 1], by(ode[n - 1])
                yield by(reciprocal_taylor.conclusion[n - 1])
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

    @claim
    def ct(
        R: Fn[Nat, Nat, Int],
        stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
        recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
    ) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
        """What sumpy stores of a harmonic table, rebuilt by the recurrence, is the table."""
        for a, b in ct.conclusion.domain:
            if a < 2:
                yield by(stored)
            else:
                yield by(recurrence[a - 2, b], ct.conclusion[a - 2, b + 2], pde[a - 2, b])

    @claim
    def ct_wrong(
        R: Fn[Nat, Nat, Int],
        stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
        recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
    ) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
        """The same, citing the conclusion at a point that does not make the step follow."""
        for a, b in ct_wrong.conclusion.domain:
            if a < 2:
                yield by(stored)
            else:
                yield by(recurrence[a - 2, b], ct_wrong.conclusion[a - 2, b + 3], pde[a - 2, b])
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


def test_a_condition_is_a_hypothesis_of_any_claim(cfl) -> None:
    courant = cfl.courant
    assert [name for name, _ in courant.hypotheses] == ["ok"]
    # printed as it is written
    assert courant.statement == "c : Real, dt : Real, h : Real | cfl(c, dt, h) |- c*dt / h <= 1"
    assert render(courant.hypotheses[0][1]) == "h > 0 and c*dt <= h"
    assert courant.hypothesis_names == ("ok_1", "ok_2")
    assert courant.under == () and courant.cited_under == ""
    assert courant(c=1, dt=Fraction(1, 10), h=Fraction(1, 5))
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
    assert "a condition has no goal" in concluded and "@claim" in concluded
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


def test_claims_in_a_with_block_hold_under_the_condition(segment) -> None:
    for stated, own in ((segment.line_taylor, "a"), (segment.reciprocal_taylor, "b")):
        assert [name for name, _ in stated.variables] == ["alpha", "beta", own]
        assert [name for name, _ in stated.hypotheses] == ["nonzero", "first_term", "ode"]
        assert stated.hypothesis_names == ("nonzero", "first_term", "ode")
        assert stated.held_under == (segment.segment,)
        assert isinstance(stated.conditions, Conditions)
        assert stated.bound == ("alpha", "beta", "nonzero")
        assert [name for name, _ in stated.own_variables] == [own]
        assert stated.under_label == "segment (nonzero)"
        assert stated.cited_under == "under segment"
        binders = [var.name for var, _ in stated.term.binders]
        assert binders == ["alpha", "beta", own]
        assert stated.statement.startswith(f"under segment (nonzero): {own} : Fn[Nat, Complex] | ")
    assert segment.line_taylor.statement == (
        "under segment (nonzero): a : Fn[Nat, Complex] | alpha*a[1] == beta, forall n in Nat "
        "where n >= 1. (n + 1)*alpha*a[n + 1] + n*beta*a[n] == 0 |- forall n in Nat where "
        "n >= 1. a[n] == -(-beta / alpha)**n / n"
    )


def test_the_ledger_names_the_condition_before_the_claims_own_parts(segment) -> None:
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


def test_a_claim_under_a_condition_takes_the_conditions_variables_natively(cfl) -> None:
    assert cfl.courant_in_block(c=1, dt=Fraction(1, 10), h=Fraction(1, 5), k=0) is True
    assert cfl.courant_in_block(1, Fraction(1, 10), Fraction(1, 5), 0) is True
    # where the condition fails, the question does not apply, and the error says why
    with pytest.raises(ConditionNotMet) as refused:
        cfl.courant_in_block(c=3, dt=1, h=1, k=0)
    assert str(refused.value) == (
        "courant_in_block does not apply at these values: its condition stable of cfl, "
        "c*dt <= h, fails there"
    )
    with pytest.raises(TypeError, match="courant_in_block needs values for h"):
        cfl.courant_in_block(c=1, dt=1, k=0)


def test_the_property_tester_draws_the_conditions_variables_satisfying_its_conditions(
    cfl,
) -> None:
    """``dx <= h`` follows only from ``stable``: a draw that ignored it would refute the claim."""
    for stated in (cfl.courant_in_block, cfl.step_fits):
        report = stated.report()
        assert report.ok and report.valid > 0, report


def test_the_faithfulness_check_runs_the_conditions_annotations_too(segment, cfl) -> None:
    for stated, count in (
        (segment.line_taylor, 7),
        (segment.reciprocal_taylor, 7),
        (cfl.courant_in_block, 8),
    ):
        reading = stated.faithful_fact()
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

    @claim
    def under_above(y: Int, same: y == x) -> y >= 1:
        """Under the misread condition."""


@claim
def cites_above(z: Int, h: above(z)) -> z >= 1:
    """With the misread condition as a hypothesis."""


@claim
def base(x: Int, ok: shifted(x) >= 1) -> x + 1 >= 2:
    """A claim whose condition the helper misreads."""


@claim
def cites_base(z: Int, h: base.conditions(z)) -> z >= 1:
    """With the misread claim's conditions as a hypothesis."""
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
    # a claim's conditions used as a hypothesis are run again as Python too
    through_a_claim = module.cites_base.faithful_fact()
    assert through_a_claim.status is Status.REFUTED, through_a_claim.provenance
    assert "the hypothesis h" in through_a_claim.provenance["reason"]


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
        "(b for beta): a claim under segment reads its variables and conditions by their "
        f"names; {line}"
    )
    swapped = _refused(tmp_path, head + "with segment as (beta, alpha, nonzero):\n    pass\n")
    assert "(beta for alpha, alpha for beta)" in swapped
    single = _refused(tmp_path, head + "with segment as s:\n    pass\n")
    assert single.startswith("with segment as s: binds one name") and line in single
    bare = _refused(tmp_path, head + "with segment:\n    pass\n")
    assert bare.startswith("with segment: binds nothing") and line in bare


def test_a_claim_in_the_block_that_declares_a_bound_name_is_refused(tmp_path) -> None:
    refused = _refused(
        tmp_path,
        HEAD
        + textwrap.dedent(
            '''

            @condition
            def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
                """A segment."""


            with segment as (alpha, beta, nonzero):

                @claim
                def again(alpha: Complex, x: Complex) -> x * alpha == alpha * x:
                    """alpha twice."""
            '''
        ),
    )
    assert refused.startswith("again at refused.py:")
    assert refused.endswith(
        "alpha is segment's, which with segment as (alpha, beta, nonzero) assumes for every "
        "claim in the block; drop the parameter alpha, or define again outside the block"
    )


def test_a_bound_name_used_after_the_block_is_refused(tmp_path) -> None:
    head = HEAD + textwrap.dedent(
        '''

        @condition
        def segment(alpha: Complex, beta: Complex, nonzero: alpha != 0):
            """A segment."""


        with segment as (alpha, beta, nonzero):

            @claim
            def inside(x: Complex) -> x * alpha == alpha * x:
                """Inside."""

        '''
    )
    in_annotation = _refused(
        tmp_path,
        head
        + textwrap.dedent(
            '''
            @claim
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
            @claim
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

    @claim
    def in_one_statement(x: Real, inside: x >= 0) -> x + h * c >= 0:
        """Under mesh and speed, in one with statement."""


with (
    mesh as (h, positive),
    cfl as (c, dt, h, stable),
):

    @claim
    def parenthesized(dx: Real, moves: dx <= c * dt) -> dx <= h:
        """Under mesh and cfl, which share h."""


with mesh as (h, positive):
    with speed as (c, forward):

        @claim
        def nested(x: Real, inside: x >= 0) -> x + h * c >= 0:
            """Under mesh and speed, nested."""

    @claim
    def outer_only(x: Real, inside: x >= 0) -> x * h >= 0:
        """Under mesh alone, after the inner block."""
'''
)


def test_conditions_compose_in_one_with_statement_and_by_nesting(tmp_path) -> None:
    module = _module(tmp_path, COMPOSED, "composed_case")
    for stated in (module.in_one_statement, module.nested):
        assert stated.held_under == (module.mesh, module.speed)
        assert [name for name, _ in stated.variables] == ["h", "c", "x"]
        assert [name for name, _ in stated.hypotheses] == ["positive", "forward", "inside"]
        assert stated.statement.startswith("under mesh (positive), speed (forward): x : Real | ")
        assert stated.cited_under == "under mesh, speed"
        assert stated.report().ok
        assert stated.faithful_fact().status is Status.TESTED
    shared = module.parenthesized
    assert shared.held_under == (module.mesh, module.cfl)
    assert [name for name, _ in shared.variables] == ["h", "c", "dt", "dx"]
    assert [name for name, _ in shared.hypotheses] == ["positive", "stable", "moves"]
    assert shared.report().ok
    assert shared.faithful_fact().status is Status.TESTED
    assert module.outer_only.held_under == (module.mesh,)
    assert module.outer_only.under_label == "mesh (positive)"


# }}}


# {{{ written proofs under a condition


def test_a_written_proof_under_a_condition_reads_the_bound_names(tmp_path) -> None:
    module = _module(tmp_path, TABLE, "table_case")
    proof = trace_proof(module.ct)
    cited = {citation.name for leaf in proof.leaves for citation in leaf.facts or ()}
    assert {"stored", "recurrence", "pde", "ct.conclusion"} <= cited
    command = compile_proof(proof, mathlib=False)
    assert "(pde :" in command.source and "theorem Lanky.ct" in command.source


def test_the_line_taylor_theorems_under_segment_trace_and_read_faithfully(segment) -> None:
    for stated in (segment.line_taylor, segment.reciprocal_taylor):
        proof = trace_proof(stated)
        assert proof.claim is not None and proof.claim.params == ("n",)
        assert stated.faithful_fact().status is Status.TESTED


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
    assert failure["source"].startswith(
        "yield by(recurrence[a - 2, b], ct_wrong.conclusion[a - 2, b + 3]"
    )


def test_lean_proves_claims_under_a_claim_and_under_its_conditions(tmp_path) -> None:
    """The whole claim's goal is a hypothesis under its name; its conditions are hypotheses."""
    _lean_or_skip()
    path = tmp_path / "steps_core.py"
    path.write_text(STEPS, encoding="utf-8")
    ledger = check_path(path)
    checked = {fact.owner: fact for fact in claims(ledger)}
    for owner in ("moves", "twice", "below"):
        fact = checked[owner]
        assert fact.status is Status.PROVED and fact.decided_by == "lean", fact.provenance
    assert checked["twice"].rests_on[0] == checked["moves"].id
    assert ledger.support(checked["twice"]).under == ()


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


# {{{ the three forms of with


#: A condition over the integers, a claim under it, and the claims of the
#: two other forms of with: under the claim's conditions, and under the claim.
STEPS = (
    HEAD
    + '''

@condition
def forward(h: Int, positive: h > 0):
    """A step that moves forward."""


with forward as (h, positive):

    @claim
    def moves(x: Int, small: x <= 3) -> x + h > x:
        """A step moves x forward."""

    stated = moves(5)

    with moves as (x, small):

        @claim
        def twice() -> x + 2 * h > x:
            """Two steps move further than one."""

    with moves.conditions as (x, small):

        @claim
        def below() -> x - h < 3:
            """Under moves' conditions alone: a step back stays below 3."""
'''
)


@pytest.fixture(scope="module")
def steps(tmp_path_factory):
    """The steps module, imported."""
    return _module(tmp_path_factory.mktemp("steps"), STEPS, "steps_case")


def test_a_claims_conditions_are_one_object(steps, segment) -> None:
    conditions = steps.moves.conditions
    assert isinstance(conditions, Conditions)
    assert conditions is steps.moves.conditions
    assert conditions.__name__ == "moves.conditions"
    assert conditions.names == ("x", "small")
    assert conditions.label == "moves.conditions (small)"
    assert conditions.signature == "moves.conditions(x: Int, small: x <= 3)"
    assert render(conditions.small) == "x <= 3"
    assert conditions(x=2) is True and conditions(x=4) is False
    # the conditions of what the claim holds under are that one's
    with pytest.raises(AttributeError) as refused:
        _ = conditions.positive
    assert str(refused.value) == (
        "positive is a condition of forward, which moves holds under; the conditions of "
        "moves itself are small"
    )
    with pytest.raises(AttributeError, match="x is a variable of moves, not one of its"):
        _ = conditions.x
    with pytest.raises(AttributeError, match="moves has no condition big: its conditions are"):
        _ = conditions.big
    ode = segment.line_taylor.conditions.ode
    assert render(ode).startswith("forall n in Nat where n >= 1.")


def test_with_a_claims_conditions_assumes_them_and_not_its_goal(steps) -> None:
    below = steps.below
    assert below.statement == "under forward (positive), moves.conditions (small): x - h < 3"
    assert [name for name, _ in below.variables] == ["h", "x"]
    assert [name for name, _ in below.hypotheses] == ["positive", "small"]
    assert below.held_under == (steps.forward, steps.moves.conditions)
    assert below.uses == ()
    assert below.cited_under == "under forward, moves.conditions"
    assert below.report().ok
    assert below.faithful_fact().status is Status.TESTED


def test_with_a_whole_claim_assumes_its_goal_under_its_name(steps) -> None:
    twice = steps.twice
    assert twice.statement == "under forward (positive), moves: x + 2*h > x"
    assert [name for name, _ in twice.hypotheses] == ["positive", "small", "moves"]
    assert render(dict(twice.hypotheses)["moves"]) == "x + h > x"
    assert twice.held_under == (steps.forward, steps.moves)
    # a claim built on another rests on it
    assert twice.uses == (steps.moves.fact_id,)
    assert twice.fact().rests_on == (steps.moves.fact_id,)
    assert twice.report().ok
    assert twice.faithful_fact().status is Status.TESTED


def test_a_claim_built_on_a_cited_claim_reads_under_it(tmp_path, capsys) -> None:
    from lanky import cli

    source = STEPS.replace(
        "    @claim\n    def moves(",
        '    @claim(cite="a step, as a textbook has it")\n    def moves(',
    )
    path = tmp_path / "steps_cited.py"
    path.write_text(source, encoding="utf-8")
    ledger = check_path(path)
    rows = {fact.owner: fact for fact in claims(ledger)}
    assert rows["moves"].is_cited
    assert ledger.support(rows["twice"]).under == (rows["moves"].id,)
    assert ledger.support(rows["below"]).under == ()
    cli.main(["check", str(path)])
    printed = capsys.readouterr().out
    assert "under moves" in next(line for line in printed.splitlines() if " twice " in line)


def test_a_claim_asked_inside_its_block_takes_the_blocks_names(steps) -> None:
    from lanky.terms import Forall

    stated = steps.stated
    assert isinstance(stated, Forall) and stated.binders == ()
    assert render(stated.guard) == "h > 0 and 5 <= 3"
    assert render(stated.body) == "5 + h > 5"
    # outside the block, a call gives every input, the condition's first
    assert steps.moves(2, 1) is True
    assert steps.moves(h=2, x=1) is True
    with pytest.raises(ConditionNotMet, match="its condition positive of forward, h > 0"):
        steps.moves(h=0, x=1)


def test_with_a_claim_outside_its_conditions_is_refused(tmp_path) -> None:
    head = STEPS + "\n\n"
    whole = _refused(tmp_path, head + "with moves as (x, small):\n    pass\n")
    assert whole == (
        "with moves as (x, small): assumes moves, which holds under forward, and forward "
        "is not in force here; write with forward as (h, positive), moves as (x, small):"
    )
    half = _refused(tmp_path, head + "with moves.conditions as (x, small):\n    pass\n")
    assert half.startswith("with moves.conditions as (x, small): assumes moves, which holds")
    assert half.endswith("write with forward as (h, positive), moves.conditions as (x, small):")


def test_with_a_claim_binds_every_name_of_its_signature(tmp_path) -> None:
    head = STEPS + "\n\nwith forward as (h, positive):\n"
    fewer = _refused(tmp_path, head + "    with moves as (x,):\n        pass\n")
    assert fewer == (
        "with moves as (x): binds 1 name, and moves has 2 variables and conditions, "
        "moves(x: Int, small: x <= 3); write with moves as (x, small):"
    )
    renamed = _refused(tmp_path, head + "    with moves as (y, small):\n        pass\n")
    assert "(y for x)" in renamed


# }}}


# {{{ citing a sibling inside the block


class _Runner:
    """A run in progress, as a trace or a native run is: it proves ``theorem``, and records."""

    def __init__(self, theorem) -> None:
        self.theorem = theorem
        self.cited: list = []

    def cite_theorem(self, theorem, values, named, frame):
        self.cited.append((theorem.__name__, values, dict(named)))
        return "cited"


#: Two claims under one condition, and one outside it, over the integers.
SIBLINGS = (
    HEAD
    + '''

@condition
def offset(k: Int, m: Int, gap: m == k + 2):
    """Two numbers two apart."""


with offset as (k, m, gap):

    @claim
    def apart(x: Int) -> x + m == x + k + 2:
        """x moves the same under both."""

    @claim
    def apart_twice(y: Int) -> y + 2 * m == y + 2 * k + 4:
        """Twice as far."""


@claim
def outside(z: Int) -> z == z:
    """Not under offset."""
'''
)


def test_a_sibling_cited_inside_the_block_takes_only_its_own_inputs(tmp_path) -> None:
    from lanky.proofs.trace import running

    module = _module(tmp_path, SIBLINGS, "siblings_case")
    runner = _Runner(module.apart_twice)
    namespace = {"apart": module.apart, "k": Var("k"), "m": Var("m"), "y": Var("y")}
    with running(runner):
        exec("cited = apart(y)", namespace)
        exec("cited = apart(x=y)", namespace)
    (name, values, named), (_, named_values, named_named) = runner.cited
    assert name == "apart" and named == {}
    assert values == (namespace["k"], namespace["m"], namespace["y"])
    assert named_values == (namespace["k"], namespace["m"]) and named_named == {"x": namespace["y"]}
    # the block's names are the block's: giving them too is refused, with what to write
    with running(runner), pytest.raises(TypeError) as refused:
        exec("cited = apart(k, m, y)", namespace)
    assert str(refused.value) == (
        "inside with offset, apart takes its own inputs, x; k, m are the block's, and come "
        "from it: give apart its own inputs only"
    )
    with running(runner), pytest.raises(TypeError, match="takes its own inputs, x"):
        exec("cited = apart(y, k=k)", namespace)
    # a proof that does not hold under offset gives every input
    other = _Runner(module.outside)
    with running(other):
        exec("cited = apart(k, m, y)", namespace)
    assert other.cited[0][1] == (namespace["k"], namespace["m"], namespace["y"])


def test_a_traced_sibling_citation_gets_the_blocks_names(tmp_path) -> None:
    source = SIBLINGS.replace(
        '''        """Twice as far."""''',
        '''        """Twice as far."""
        assert y + 2 * m == y + m + m, by(apart(y))
        return by()''',
    )
    module = _module(tmp_path, source, "siblings_traced")
    proof = trace_proof(module.apart_twice)
    cited = [
        citation.text()
        for leaf in proof.leaves
        for citation in leaf.citations
        if citation.source is module.apart
    ]
    assert cited == ["apart(k, m, y)"]


# }}}


# {{{ a condition as a hypothesis, and its row


#: A condition used as a hypothesis, the variables it names declared nowhere else.
BROUGHT = (
    HEAD
    + '''

@condition
def cfl(c: Real, dt: Real, h: Real, positive: h > 0, stable: c * dt <= h):
    """The CFL condition of an explicit upwind scheme for u_t + c u_x = 0."""


with cfl as (c, dt, h, positive, stable):

    @claim
    def courant() -> c * dt / h <= 1:
        """Under the CFL condition, the Courant number is at most one."""


@claim
def courant_number(ok: cfl(c, dt, h)) -> c * dt / h <= 1:
    """Wherever the CFL condition holds, the Courant number is at most one."""
'''
)


def test_a_condition_used_as_a_hypothesis_brings_its_variables_sorts(tmp_path) -> None:
    module = _module(tmp_path, BROUGHT, "brought_case")
    claim_ = module.courant_number
    assert claim_.variables == (("c", Real), ("dt", Real), ("h", Real))
    assert claim_.brought == (("c", Real), ("dt", Real), ("h", Real))
    assert claim_.statement == "c : Real, dt : Real, h : Real | cfl(c, dt, h) |- c*dt / h <= 1"
    assert claim_.fact().provenance["sequent"]["hypotheses"] == [["ok", "cfl(c, dt, h)"]]
    assert claim_.report().ok
    assert claim_.faithful_fact().status is Status.TESTED
    assert claim_(c=1, dt=Fraction(1, 10), h=Fraction(1, 5)) is True


def test_a_condition_has_a_row_that_checks_it_can_hold(tmp_path) -> None:
    path = tmp_path / "brought_row.py"
    path.write_text(BROUGHT, encoding="utf-8")
    ledger = check_path(path)
    (row,) = [fact for fact in ledger if fact.is_condition]
    assert row.owner == "cfl" and row.kind == "condition"
    assert row.id == f"condition:brought_row.cfl@{row.provenance['line']}"
    assert row.status is Status.TESTED and row.decided_by == "property-test"
    assert row.statement == "can hold: c : Real, dt : Real, h : Real | h > 0, c*dt <= h"
    assert statement_lines(row, width=40) == [
        "can hold: c : Real, dt : Real, h : Real",
        "| positive: h > 0",
        "| stable: c*dt <= h",
    ]
    assert row not in claims(ledger)


def test_a_condition_that_can_never_hold_is_not_passed_over(tmp_path) -> None:
    path = tmp_path / "never.py"
    path.write_text(
        HEAD
        + '''

@condition
def never(x: Int, low: x < 0, high: x > 0):
    """Below zero and above it."""
''',
        encoding="utf-8",
    )
    (row,) = [fact for fact in check_path(path) if fact.is_condition]
    assert row.status is Status.ASSUMED
    assert row.provenance.get("unsatisfied") or row.is_vacuous


def test_a_conditions_names_are_not_read_off_it(cfl) -> None:
    with pytest.raises(AttributeError) as refused:
        _ = cfl.cfl.dt
    assert str(refused.value) == (
        "cfl.dt names nothing: dt is bound by with cfl as (c, dt, h, positive, stable):, and "
        "a claim outside the block ranges over dt in its own for, or takes it as a parameter"
    )
    assert not hasattr(cfl.cfl, "stable")


# }}}


# {{{ a condition for a refuted claim


#: The CFL story of the design: a claim red at draws, and the condition that makes it green.
UPWIND = (
    HEAD
    + '''

@condition
def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
    """The CFL condition: the Courant number is between 0 and 1."""


@condition
def positive(nu: Real, above: nu > 0):
    """A Courant number above zero, which leaves the failing draws above one."""


@claim
def upwind_between() -> all(
    (u0 - nu * (u0 - u1) - u0) * (u0 - nu * (u0 - u1) - u1) <= 0
    for nu in Real
    for u0 in Real
    for u1 in Real
):
    """One upwind step lands between the two values it mixes."""
'''
)


def test_a_refuted_claim_names_the_condition_that_excludes_its_failing_draws(
    tmp_path, capsys
) -> None:
    from lanky import cli

    path = tmp_path / "upwind_red.py"
    path.write_text(UPWIND, encoding="utf-8")
    (fact,) = claims(check_path(path))
    assert fact.status is Status.REFUTED
    line = (
        "The condition cfl in this file excludes every failing draw: put the claim under "
        "with cfl as (nu, stable)."
    )
    assert fact.provenance["suggestion"] == [line]
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out.splitlines()
    at = next(index for index, text in enumerate(printed) if text.startswith("REFUTED"))
    assert f"  {line}" in printed[at:]


def test_the_claim_under_the_suggested_condition_holds(tmp_path) -> None:
    green = UPWIND.replace(
        '''@claim
def upwind_between() -> all(
    (u0 - nu * (u0 - u1) - u0) * (u0 - nu * (u0 - u1) - u1) <= 0
    for nu in Real
    for u0 in Real
    for u1 in Real
):
    """One upwind step lands between the two values it mixes."""''',
        '''with cfl as (nu, stable):

    @claim
    def upwind_between() -> all(
        (u0 - nu * (u0 - u1) - u0) * (u0 - nu * (u0 - u1) - u1) <= 0
        for u0 in Real
        for u1 in Real
    ):
        """One upwind step lands between the two values it mixes."""''',
    )
    path = tmp_path / "upwind_green.py"
    path.write_text(green, encoding="utf-8")
    (fact,) = claims(check_path(path))
    assert fact.status is not Status.REFUTED
    assert fact.statement.startswith("under cfl (stable): ")
    assert "suggestion" not in fact.provenance


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
    assert lanky.Conditions is Conditions and lanky.ConditionNotMet is ConditionNotMet
    assert claim is lanky.claim and Int is lanky.Int and Real is lanky.Real
