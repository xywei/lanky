"""The examples of the 0.6 design (proofs read as engineers write checks), as it writes them.

The design writes each kind of proof once:

- a closed form from a recurrence, two claims under one named condition
  (``line_taylor`` and ``reciprocal_taylor`` under ``with away_from_zero``);
- strong induction on two variables, and the same step as a calculation
  (``compressed_taylor``);
- a proof beside the kernel it proves, with its conclusion flat and nested
  (``every_box``);
- induction over the conclusion's ``for``, citing another claim for an
  input (``nicomachus`` and ``gauss(n - 1)``);
- two known facts and no loop (``log_of_the_modulus``), and algebra alone
  (``harmonic``);
- the CFL story: a claim red at its draws, the condition lanky names, and
  the claim green under it.

Each runs natively, at drawn values, where a step written wrong is refuted
with its numbers before Lean is asked; a family over the naturals is filled
in from the hypotheses that define it (:mod:`lanky.proofs.filled`). Each is
traced, to the Lean proof its summary names, and Lean with Mathlib proves
them where Mathlib is.
"""

from __future__ import annotations

import os
import re
import textwrap
from fractions import Fraction

import pytest

from conftest import claims
from lanky.check import check_path, import_path
from lanky.ledger import Status
from lanky.proofs import compile_proof, trace_proof
from lanky.proofs.trace import ProofError

HEAD = """\
from __future__ import annotations

from lanky import by, claim, condition, conj, log, real
from lanky.known import log_of_a_power, modulus_squared, one_more_term
from lanky.prelude import Complex, Fin, Fn, Int, Nat, Real
"""

#: The design's examples, as it writes them; ``every_box``'s conditions,
#: which it leaves out, are ``examples/every_box.py``'s.
EXAMPLES = (
    HEAD
    + '''

def coefficient(ratio, k):
    """The k-th Taylor coefficient of log(alpha + tau * beta), k >= 1."""
    return -(ratio**k) / k


@condition
def away_from_zero(alpha: Complex, beta: Complex, nonzero: alpha != 0):
    """The expansion point alpha is not zero."""


with away_from_zero as (alpha, beta, nonzero):

    @claim
    def line_taylor(
        a: Fn[Nat, Complex],
        first_term: alpha * a[1] == beta,
        ode: all((n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0 for n in Nat if n >= 1),
    ) -> all(a[n] == coefficient(-beta / alpha, n) for n in Nat if n >= 1):
        """The Taylor coefficients of log(alpha + tau * beta), from the ODE they satisfy."""
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
        """The Taylor coefficients of alpha / (alpha + tau * beta)."""
        for n in reciprocal_taylor.conclusion.domain:
            if n == 0:
                yield by(first_term)
            else:
                assert b[n] == (-beta / alpha) * b[n - 1], by(ode[n - 1])
                yield by(reciprocal_taylor.conclusion[n - 1])


@claim
def compressed_taylor(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """What sumpy stores of a harmonic table, reconstructed, is the table."""
    for a, b in compressed_taylor.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence, compressed_taylor.conclusion[a - 2, b + 2], pde)


@claim
def compressed_calculation(
    D: Fn[Nat, Nat, Real],
    R: Fn[Nat, Nat, Real],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    """The same, its step a calculation."""
    for a, b in compressed_calculation.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            assert R[a, b] == -R[a - 2, b + 2] == -D[a - 2, b + 2] == D[a, b], by(
                recurrence[a - 2, b], compressed_calculation.conclusion[a - 2, b + 2], pde[a - 2, b]
            )
            yield by()


@claim
def every_box(
    n: Nat,
    p: Nat,
    c: Fn[Nat, Int, Real],
    D: Fn[Nat, Nat, Nat, Real],
    R: Fn[Nat, Nat, Nat, Real],
    pde: all(D[i, a + 2, b] + D[i, a, b + 2] == 0 for i in Fin[n] for a in Nat for b in Nat),
    centre: all(c[i, 0] == D[i, 0, 0] for i in Fin[n]),
    stored: all(
        c[i, 2 * (a + b) - 1 + a] == D[i, a, b]
        for i in Fin[n] for a in Nat for b in Nat if a < 2 if a + b >= 1 if a + b <= p
    ),
    centre_copy: all(R[i, 0, 0] == c[i, 0] for i in Fin[n]),
    copies: all(
        R[i, a, b] == c[i, 2 * (a + b) - 1 + a]
        for i in Fin[n] for a in Nat for b in Nat if a < 2 if a + b >= 1 if a + b <= p
    ),
    recurrence: all(
        R[i, a + 2, b] == -R[i, a, b + 2]
        for i in Fin[n] for a in Nat for b in Nat if a + b + 2 <= p
    ),
) -> all(R[i, a, b] == D[i, a, b] for i in Fin[n] for a in Nat for b in Nat if a + b <= p):
    """Every derivative a box's table reconstructs is the derivative it stands for."""
    for i, a, b in every_box.conclusion.domain:
        if a + b == 0:
            yield by(centre_copy, centre)
        elif a < 2:
            yield by(copies, stored)
        else:
            yield by(recurrence, every_box.conclusion[i, a - 2, b + 2], pde)


@claim
def every_box_nested(
    n: Nat,
    p: Nat,
    c: Fn[Nat, Int, Real],
    D: Fn[Nat, Nat, Nat, Real],
    R: Fn[Nat, Nat, Nat, Real],
    pde: all(D[i, a + 2, b] + D[i, a, b + 2] == 0 for i in Fin[n] for a in Nat for b in Nat),
    centre: all(c[i, 0] == D[i, 0, 0] for i in Fin[n]),
    stored: all(
        c[i, 2 * (a + b) - 1 + a] == D[i, a, b]
        for i in Fin[n] for a in Nat for b in Nat if a < 2 if a + b >= 1 if a + b <= p
    ),
    centre_copy: all(R[i, 0, 0] == c[i, 0] for i in Fin[n]),
    copies: all(
        R[i, a, b] == c[i, 2 * (a + b) - 1 + a]
        for i in Fin[n] for a in Nat for b in Nat if a < 2 if a + b >= 1 if a + b <= p
    ),
    recurrence: all(
        R[i, a + 2, b] == -R[i, a, b + 2]
        for i in Fin[n] for a in Nat for b in Nat if a + b + 2 <= p
    ),
) -> all(
    all(R[i, a, b] == D[i, a, b] for a in Nat for b in Nat if a + b <= p) for i in Fin[n]
):
    """The same, the conclusion a for over boxes of a for over orders."""
    for i in every_box_nested.conclusion.domain:
        for a, b in every_box_nested.conclusion[i].domain:
            if a + b == 0:
                yield by(centre_copy, centre)
            elif a < 2:
                yield by(copies, stored)
            else:
                yield by(recurrence, every_box_nested.conclusion[i][a - 2, b + 2], pde)


@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of 0 .. n is n * (n + 1)."""


@claim
def nicomachus() -> all(
    sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2 for n in Nat
):
    """The sum of the first cubes is the square of the sum of the first numbers."""
    for n in nicomachus.conclusion.domain:
        if n == 0:
            yield by()
        else:
            assert (
                sum(i**3 for i in Fin[n + 1])
                == sum(i**3 for i in Fin[n]) + n**3
                == sum(i for i in Fin[n]) ** 2 + n**3
                == (sum(i for i in Fin[n]) + n) ** 2
                == sum(i for i in Fin[n + 1]) ** 2
            ), by(one_more_term, nicomachus.conclusion[n - 1], gauss(n - 1))
            yield by()


@claim
def log_of_the_modulus(alpha: Complex, nonzero: alpha != 0) -> (
    log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
):
    """log|alpha| with no square root: half the log of alpha times its conjugate."""
    assert log(abs(alpha)) == log(abs(alpha) ** 2) / 2, by(log_of_a_power)
    return by(modulus_squared)
'''
)

#: Each example with a step written wrong, a sign or a power, by the text that changes.
TYPOS = {
    "line_taylor": (
        "(n - 1) / n * (-beta / alpha) * a[n - 1], by(ode[n - 1])",
        "(n - 1) / n * (beta / alpha) * a[n - 1], by(ode[n - 1])",
    ),
    "reciprocal_taylor": (
        "assert b[n] == (-beta / alpha) * b[n - 1]",
        "assert b[n] == (beta / alpha) * b[n - 1]",
    ),
    "compressed_calculation": (
        "assert R[a, b] == -R[a - 2, b + 2] == -D[a - 2, b + 2] == D[a, b]",
        "assert R[a, b] == -R[a - 2, b + 2] == D[a - 2, b + 2] == D[a, b]",
    ),
    "nicomachus": (
        "== sum(i**3 for i in Fin[n]) + n**3\n",
        "== sum(i**3 for i in Fin[n]) + n**2\n",
    ),
}

#: ``harmonic``, algebra alone, which reads sympy's Laplacian of the kernel.
HARMONIC = '''\
from __future__ import annotations

from lanky import by, claim
from lanky.cas import from_sympy
from lanky.prelude import Real


def log_r(x, y, functions):
    """The 2-D Laplace kernel without its constant factor: log r."""
    return functions.log(functions.sqrt(x**2 + y**2))


def laplacian(kernel, x, y):
    """G_xx + G_yy of kernel, as sympy differentiates it, over lanky's x and y."""
    import sympy

    sx, sy = sympy.symbols("x y", real=True)
    term = kernel(sx, sy, sympy)
    return from_sympy(term.diff(sx, 2) + term.diff(sy, 2), {"x": x, "y": y})


@claim
def harmonic(x: Real, y: Real, away: x**2 + y**2 > 0) -> laplacian(log_r, x, y) == 0:
    """The 2-D Laplace kernel is harmonic away from the origin."""
    r2 = x**2 + y**2
    assert laplacian(log_r, x, y) == 2 / r2 - 2 * (x**2 + y**2) / r2**2 == 0
    return by()
'''

#: The CFL story, red: a claim over every Courant number, and a condition in the file.
UPWIND_RED = '''\
from __future__ import annotations

from lanky import claim, condition
from lanky.prelude import Real


@condition
def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
    """The CFL condition: the Courant number is between 0 and 1."""


@claim
def upwind_bounded() -> all(
    abs(u0 - nu * (u0 - u1)) <= max(abs(u0), abs(u1))
    for nu in Real for u0 in Real for u1 in Real
):
    """One upwind step does not grow the solution."""
'''

#: The CFL story, green: the claim under the condition, nu out of its for.
UPWIND_GREEN = '''\
from __future__ import annotations

from lanky import claim, condition
from lanky.prelude import Real


@condition
def cfl(nu: Real, stable: (0 <= nu) & (nu <= 1)):
    """The CFL condition: the Courant number is between 0 and 1."""


with cfl as (nu, stable):

    @claim
    def upwind_bounded() -> all(
        abs(u0 - nu * (u0 - u1)) <= max(abs(u0), abs(u1)) for u0 in Real for u1 in Real
    ):
        """One upwind step does not grow the solution."""
'''


def _module(tmp_path_factory, source: str, name: str):
    """``source`` in a file of its own, imported as ``lanky check`` imports it."""
    path = tmp_path_factory.mktemp(name) / f"{name}.py"
    path.write_text(textwrap.dedent(source), encoding="utf-8")
    return import_path(path)


def _typo_source() -> str:
    source = EXAMPLES
    for old, new in TYPOS.values():
        assert source.count(old) == 1, old
        source = source.replace(old, new)
    return source


def _line(source: str, text: str) -> int:
    """The line of ``source`` that holds ``text``; in a chain, the line its ``assert`` is on."""
    lines = source.splitlines()
    at = next(number for number, line in enumerate(lines, 1) if text in line)
    while "assert" not in lines[at - 1]:
        at -= 1
    return at


@pytest.fixture(scope="module")
def examples(tmp_path_factory):
    return _module(tmp_path_factory, EXAMPLES, "design_examples")


@pytest.fixture(scope="module")
def typos(tmp_path_factory):
    return _module(tmp_path_factory, _typo_source(), "design_typos")


# {{{ traced


#: What each written proof traces to: the conclusion's points it loops over,
#: and the summary of the Lean proof it compiles to.
TRACED = {
    "line_taylor": (("n",), "induction on n, 2 cases, 3 steps"),
    "reciprocal_taylor": (("n",), "induction on n, 2 cases, 3 steps"),
    "compressed_taylor": (("a", "b"), "induction on a, 2 cases, 2 steps"),
    "compressed_calculation": (("a", "b"), "induction on a, 2 cases, 4 steps"),
    "every_box": (("i", "a", "b"), "induction on a, 3 cases, 3 steps"),
    "every_box_nested": (("i", "a", "b"), "induction on a, 3 cases, 3 steps"),
    "nicomachus": (
        ("n",),
        "induction on n, 2 cases, 4 steps, 1 routine, using one_more_term and gauss",
    ),
    "log_of_the_modulus": (
        None,
        "2 steps, using log_of_a_power and modulus_squared from lanky.known",
    ),
}


@pytest.mark.parametrize("name", sorted(TRACED))
def test_each_example_traces_to_the_lean_proof_its_summary_names(examples, name) -> None:
    proof = trace_proof(getattr(examples, name))
    params, summary = TRACED[name]
    assert (proof.claim.params if proof.claim is not None else None) == params
    assert compile_proof(proof, mathlib=True).summary == summary


def test_line_taylor_and_reciprocal_taylor_hold_under_away_from_zero(examples) -> None:
    for stated, own in ((examples.line_taylor, "a"), (examples.reciprocal_taylor, "b")):
        assert stated.held_under == (examples.away_from_zero,)
        assert stated.under_label == "away_from_zero (nonzero)"
        assert stated.statement.startswith(
            f"under away_from_zero (nonzero): {own} : Fn[Nat, Complex] | "
        )
        assert [name for name, _ in stated.variables] == ["alpha", "beta", own]


def test_nicomachus_cites_gauss_for_an_input_and_itself_at_an_earlier_point(examples) -> None:
    proof = trace_proof(examples.nicomachus)
    cited = {citation.text() for leaf in proof.leaves for citation in leaf.citations}
    assert {"gauss(n - 1)", "nicomachus.conclusion[n - 1]", "one_more_term"} <= cited


def test_nicomachus_by_a_parameter_is_refused_with_n_moved_into_the_for(tmp_path) -> None:
    """lanky 0.5's nicomachus took n as a parameter and called itself at n - 1."""
    module = _module_at(
        tmp_path,
        HEAD
        + '''

@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of 0 .. n is n * (n + 1)."""


@claim
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""
    if n == 0:
        return by()
    return by(one_more_term, nicomachus(n - 1), gauss(n - 1))
''',
    )
    with pytest.raises(ProofError) as refused:
        trace_proof(module.nicomachus)
    assert refused.value.message.endswith(
        "a claim does not call itself; to argue from an earlier case, put n in the "
        "conclusion's for, -> all(... for n in ...), and cite nicomachus.conclusion[n - 1]"
    )


def _module_at(tmp_path, source: str, name: str = "design_case"):
    path = tmp_path / f"{name}.py"
    path.write_text(source, encoding="utf-8")
    return import_path(path)


# }}}


# {{{ natively


@pytest.mark.parametrize("name", sorted(TRACED))
def test_each_example_holds_at_every_draw_of_its_native_run(examples, name) -> None:
    from lanky.proofs.native import native_failure

    assert native_failure(getattr(examples, name)) is None


@pytest.mark.parametrize("name", sorted(TYPOS))
def test_a_step_written_wrong_is_refuted_natively_with_its_numbers(typos, name) -> None:
    from lanky.proofs.native import native_failure

    failure = native_failure(getattr(typos, name))
    assert failure is not None and failure.kind == "false"
    assert failure.headline == "a step of its proof is false"
    assert failure.line == _line(_typo_source(), TYPOS[name][1].strip())
    (said,) = failure.lines
    assert re.fullmatch(r"At .+: the left side is .+, the right side .+\.", said), said


def test_nicomachus_written_wrong_fails_at_two(typos) -> None:
    from lanky.proofs.native import native_failure

    (said,) = native_failure(typos.nicomachus).lines
    assert said == "At n = 2: the left side is 9, the right side 5."


def test_line_taylor_written_wrong_names_the_point_and_the_condition_values(typos) -> None:
    from lanky.proofs.native import native_failure

    (said,) = native_failure(typos.line_taylor).lines
    assert re.match(r"At n = \d+, alpha = .+, beta = .+: the left side is ", said), said


def test_a_conclusion_written_wrong_is_false_at_a_point_the_walk_reaches(tmp_path) -> None:
    """every_box's walk fills its boxes' tables, and checks the conclusion at each point."""
    from lanky.proofs.native import native_failure

    source = EXAMPLES.replace(
        "-> all(R[i, a, b] == D[i, a, b] for i in Fin[n]",
        "-> all(R[i, a, b] == -D[i, a, b] for i in Fin[n]",
    )
    failure = native_failure(_module_at(tmp_path, source).every_box)
    assert failure is not None
    assert failure.headline == "its conclusion is false at a point its proof reaches"


def test_harmonic_holds_natively_and_written_wrong_is_refuted(tmp_path) -> None:
    pytest.importorskip("sympy")
    from lanky.proofs.native import native_failure

    module = _module_at(tmp_path, HARMONIC, "harmonic_case")
    assert native_failure(module.harmonic) is None
    proof = trace_proof(module.harmonic)
    assert compile_proof(proof, mathlib=True).summary == "2 steps"
    wrong = HARMONIC.replace("- 2 * (x**2 + y**2) / r2**2 == 0", "- 2 * (x**2 + y**2) / r2 == 0")
    failure = native_failure(_module_at(tmp_path, wrong, "harmonic_wrong").harmonic)
    assert failure is not None and failure.kind == "false"
    (said,) = failure.lines
    assert said.startswith("At x = ") and "the left side is 0, the right side " in said


# }}}


# {{{ families over the naturals, filled in


def test_a_family_over_the_naturals_is_filled_in_from_its_hypotheses(examples) -> None:
    from lanky.proofs.filled import FILLED_DRAWS, filled_draws

    draws = filled_draws(examples.line_taylor)
    assert len(draws) == FILLED_DRAWS
    for draw in draws:
        alpha, beta, a = draw["alpha"], draw["beta"], draw["a"]
        assert alpha * a[1] == beta
        for n in range(1, 8):
            assert (n + 1) * alpha * a[n + 1] + n * beta * a[n] == 0
            assert a[n] == -((-beta / alpha) ** n) / n


def test_tables_over_two_naturals_are_filled_along_their_recurrence(examples) -> None:
    from lanky.proofs.filled import filled_draws

    (draw, *_) = filled_draws(examples.compressed_taylor)
    D, R = draw["D"], draw["R"]
    for a in range(6):
        for b in range(6):
            assert D[a + 2, b] + D[a, b + 2] == 0
            assert R[a + 2, b] == -R[a, b + 2]
            assert R[a, b] == D[a, b]


#: A table of integers under a condition, and a calculation with a sign written wrong.
INTEGER_TABLES = (
    HEAD
    + '''

@condition
def harmonic_table(
    D: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
):
    """The derivatives of a harmonic function, as a table."""


with harmonic_table as (D, pde):

    @claim
    def calculation(
        R: Fn[Nat, Nat, Int],
        stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
        recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
    ) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
        """A calculation with a sign written wrong."""
        for a, b in calculation.conclusion.domain:
            if a < 2:
                yield by(stored)
            else:
                assert R[a, b] == -R[a - 2, b + 2] == D[a - 2, b + 2] == D[a, b], by(
                    recurrence[a - 2, b], calculation.conclusion[a - 2, b + 2], pde[a - 2, b]
                )
                yield by()
'''
)

#: The line of that calculation's ``assert``.
CALCULATION_LINE = _line(INTEGER_TABLES, "D[a - 2, b + 2] == D[a, b], by(")


def test_tables_of_integers_under_a_condition_are_filled_with_integers(tmp_path) -> None:
    """``D`` bound by ``with harmonic_table``, ``R`` the claim's own, both of integers."""
    from lanky.proofs.filled import filled_draws
    from lanky.proofs.native import native_failure

    module = _module_at(tmp_path, INTEGER_TABLES, "integer_tables")
    (draw, *_) = filled_draws(module.calculation)
    assert all(isinstance(draw["R"][a, b], int) for a in range(6) for b in range(6))
    failure = native_failure(module.calculation)
    assert failure is not None and failure.line == CALCULATION_LINE
    (said,) = failure.lines
    numbers = r"At a = \d+, b = \d+: the left side is -?\d+, the right side -?\d+\."
    assert re.fullmatch(numbers, said), said


def test_lean_names_the_false_step_and_not_the_measure(tmp_path, monkeypatch) -> None:
    """With the native run set aside, Lean's report is of the step, at its line.

    Lean leaves the recursion's measure unproved after a step it could not
    show, and the report used to say "the conclusion is not cited at earlier
    points" of this proof, whose citations are all earlier.
    """
    _lean_or_skip()
    import lanky.proofs.native as native

    monkeypatch.setattr(native, "native_run", lambda theorem, *args, **kwargs: (None, 0))
    path = tmp_path / "integer_tables_lean.py"
    path.write_text(INTEGER_TABLES, encoding="utf-8")
    fact = {fact.owner: fact for fact in claims(check_path(path))}["calculation"]
    failures = fact.provenance["proof"]["failures"]
    assert failures and {failure["kind"] for failure in failures} == {"step"}, failures
    assert failures[0]["line"] == CALCULATION_LINE


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


def test_a_family_its_hypotheses_do_not_reach_is_not_filled(tmp_path) -> None:
    """A quantifier over the reals, or hypotheses that contradict: the run tests nothing."""
    from lanky.proofs.filled import filled_draws
    from lanky.proofs.native import native_failure

    module = _module_at(
        tmp_path,
        HEAD
        + '''

@claim
def over_the_reals(
    f: Fn[Nat, Real], h: all(f[0] * x == 0 for x in Real)
) -> all(f[n] == 0 for n in Nat):
    for n in over_the_reals.conclusion.domain:
        assert f[n] == 1, by(h)
        yield by(h)


@claim
def contradicts(f: Fn[Nat, Real], one: f[0] == 1, two: f[0] == 2) -> all(f[n] == 0 for n in Nat):
    for n in contradicts.conclusion.domain:
        assert f[n] == 7, by(one, two)
        yield by(one, two)
''',
    )
    for stated in (module.over_the_reals, module.contradicts):
        assert filled_draws(stated) == []
        assert native_failure(stated) is None


def test_a_reversed_loop_starts_at_the_top_of_a_long_domain(tmp_path) -> None:
    """``reversed(...)`` over more points than one walk takes starts at the top, not below it."""
    from lanky.proofs.native import PointFalse

    module = _module_at(
        tmp_path,
        HEAD
        + '''

@claim
def from_the_top(m: Nat, f: Fn[Fin[m], Int]) -> all(f[k] == 0 for k in Fin[m]):
    for k in reversed(from_the_top.conclusion.domain):
        yield by()
''',
    )
    with pytest.raises(PointFalse):
        module.from_the_top.run_proof(m=300, f=[0] * 299 + [1])
    # the walk takes the top points, so a point far below them is not reached
    module.from_the_top.run_proof(m=300, f=[1] + [0] * 299)


# }}}


# {{{ the CFL story


def test_the_cfl_story_red_names_the_condition_and_green_holds_under_it(tmp_path, capsys) -> None:
    from lanky import cli

    red = tmp_path / "upwind_red.py"
    red.write_text(UPWIND_RED, encoding="utf-8")
    (fact,) = claims(check_path(red))
    assert fact.status is Status.REFUTED
    assert fact.statement == (
        "forall nu in Real, u0 in Real, u1 in Real. "
        "abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))"
    )
    suggestion = (
        "The condition cfl in this file excludes every failing draw: put the claim under "
        "with cfl as (nu, stable)."
    )
    assert fact.provenance["suggestion"] == [suggestion]
    assert cli.main(["check", str(red)]) == 1
    printed = capsys.readouterr().out.splitlines()
    at = next(index for index, text in enumerate(printed) if text.startswith("REFUTED"))
    assert f"  {suggestion}" in printed[at:]

    green = tmp_path / "upwind_green.py"
    green.write_text(UPWIND_GREEN, encoding="utf-8")
    (fact,) = claims(check_path(green))
    assert fact.status is not Status.REFUTED
    assert fact.statement == (
        "under cfl (stable): forall u0 in Real, u1 in Real. "
        "abs(u0 - nu*(u0 - u1)) <= max(abs(u0), abs(u1))"
    )
    assert "suggestion" not in fact.provenance


def test_the_cfl_condition_and_the_green_claim_at_numbers(tmp_path) -> None:
    from lanky import ConditionNotMet

    module = _module_at(tmp_path, UPWIND_GREEN, "upwind_numbers")
    assert module.cfl(nu=Fraction(1, 2)) is True
    assert module.cfl(nu=2) is False
    with pytest.raises(ConditionNotMet, match="its condition stable"):
        module.upwind_bounded(nu=2)


# }}}


# {{{ Lean with Mathlib


def test_mathlib_proves_the_design_examples(mathlib_project, monkeypatch, tmp_path) -> None:
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but no project is named")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    path = tmp_path / "design_mathlib.py"
    path.write_text(EXAMPLES, encoding="utf-8")
    checked = {fact.owner: fact for fact in claims(check_path(path))}
    for owner in TRACED:
        fact = checked[owner]
        assert fact.status is Status.PROVED and fact.decided_by == "lean", (owner, fact.provenance)
        assert fact.provenance["proof"]["closed"] is True, owner
    assert checked["line_taylor"].statement.startswith("under away_from_zero (nonzero): ")


# }}}
