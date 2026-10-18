"""A known fact over a family, cited at a function of the step: Nicomachus's sum (#172, #173).

``examples/nicomachus.py`` proves Nicomachus's theorem by a chain through
``one_more_term``, a fact of :mod:`lanky.known` over a family of reals,
cited by its name alone at sums of integers. What that takes, each a test
here: the matcher compares two values of a family as functions and two sums
up to the names of their binders, and prefers the point at which both sides
of the fact are the step's; a family's value prints in Lean, as a ``fun``;
the fact over the reals is restated over the integers and shown through the
cast; a step's multipliers see its sums. And the ladder tries ``field_simp``
followed by ``ring``, which proves sumpy's Laplacian of ``log r`` with no
body (#173).

The Python half needs no Lean. The examples are checked by Lean with Mathlib
where ``LANKY_LEAN_MATHLIB`` names a project, and skip where it does not.
"""

from __future__ import annotations

import os
import re
from pathlib import Path

import pytest

from conftest import claims
from lanky.check import check_path, import_path
from lanky.induction import Lemma
from lanky.ledger import Status
from lanky.matching import (
    FamilyValue,
    _same_sigma,
    candidate_points,
    kind_fits,
    same,
    same_function,
    single_point,
)
from lanky.oracles import lean as lean_module
from lanky.outline import _rung_of_text
from lanky.prelude import Complex, Fin, Fn, Nat, Real
from lanky.proofs import compile_proof, trace_proof
from lanky.proofs.report import combination
from lanky.terms import Comparison, Sum, Var, render

ROOT = Path(__file__).resolve().parent.parent
EXAMPLE = ROOT / "examples" / "nicomachus.py"

i, k, n, m, f = Var("i"), Var("k"), Var("n"), Var("m"), Var("f")


def one_more_term() -> Lemma:
    """``one_more_term`` as the matcher reads it: a family of reals, and ``m``."""
    return Lemma(
        "one_more_term",
        ((f, Fn[Nat, Real]), (m, Nat)),
        (("value", "f"), ("value", "m"), ("proof", Comparison(0, "<=", m))),
        Comparison(Sum(((k, Fin[m + 1]),), f[k]), "==", Sum(((k, Fin[m]),), f[k]) + f[m]),
    )


def cubes(bound: object) -> Sum:
    """``sum(i**3 for i in Fin[bound])``."""
    return Sum(((i, Fin[bound]),), i**3)


# {{{ the matcher


def test_two_sums_are_the_same_up_to_the_names_of_their_binders() -> None:
    """``sum(k**3 for k in Fin(n - 1 + 1))`` is ``sum(i**3 for i in Fin(n))``.

    A binder's name is the reader's choice, and a bound is the integer it is.
    """
    assert same(Sum(((k, Fin[n - 1 + 1]),), k**3), cubes(n))
    assert not same(Sum(((k, Fin[n]),), k**2), cubes(n))
    assert not same(cubes(n + 1), cubes(n))
    # no capture: the binder of one is not a free name of the other
    assert not same(Sum(((k, Fin[n]),), k + i), Sum(((i, Fin[n]),), i + i))


def test_domains_refined_by_their_own_binders_are_compared_renamed() -> None:
    """``k in Nat & (k > 0)`` is ``i in Nat & (i > 0)`` (Codex, #176).

    The refinements were compared before the binders were renamed, as ``k >
    0`` against ``i > 0``, and two sums the same up to their binders' names
    read as different.
    """
    from lanky.prelude import Refined

    def positive(var: Var) -> Refined:
        return Refined(Nat, (Comparison(var, ">", 0),))

    assert same(Sum(((k, positive(k)),), k**3), Sum(((i, positive(i)),), i**3))
    assert not same(Sum(((k, positive(k)),), k**3), Sum(((i, positive(n)),), i**3))


def test_two_values_of_a_family_are_compared_as_functions() -> None:
    """``k ↦ k**3`` is ``i ↦ i**3``; comparing their parameters with ``==`` raised."""
    first, second = FamilyValue((k,), k**3), FamilyValue((i,), i**3)
    assert same_function(first, second)
    assert not same_function(first, FamilyValue((i,), i**2))
    assert _same_sigma({"f": first, "m": n}, {"f": second, "m": n})
    assert not _same_sigma({"f": first, "m": n}, {"f": second, "m": n - 1})


def test_one_more_term_fits_the_first_link_at_n() -> None:
    """Two points fit, ``n`` and ``n - 1``; at ``n`` both sides of the fact are the link's."""
    link = [cubes(n + 1), cubes(n) + n**3]
    types = {"n": Nat}
    points = candidate_points(one_more_term(), link, types)
    assert sorted(render(at) for _, at in points) == ["n", "n - 1"]
    family, at = single_point(one_more_term(), link, types, (), "one_more_term")
    assert isinstance(family, FamilyValue) and family.shown() == "lambda i: i**3"
    assert render(at) == "n"


def test_one_more_term_fits_the_last_link_at_n() -> None:
    """``(sum(i for i in Fin(n)) + n)**2 == sum(i for i in Fin(n + 1))**2``: ``i ↦ i`` at ``n``."""
    whole = Sum(((i, Fin[n + 1]),), i)
    part = Sum(((i, Fin[n]),), i)
    family, at = single_point(
        one_more_term(), [(part + n) ** 2, whole**2], {"n": Nat}, (), "one_more_term"
    )
    assert family.shown() == "lambda i: i" and render(at) == "n"


def test_a_family_of_reals_takes_integers_and_reals_and_not_complex_numbers() -> None:
    """The values of a family's value have to fit the family's, as a number does."""
    types = {"z": Complex, "r": Real}
    assert kind_fits(Fn[Nat, Real], FamilyValue((i,), i**3), types)
    assert kind_fits(Fn[Nat, Real], FamilyValue((i,), Var("r") ** i), types)
    assert not kind_fits(Fn[Nat, Real], FamilyValue((i,), Var("z") ** i), types)
    assert kind_fits(Fn[Nat, Complex], FamilyValue((i,), Var("z") ** i), types)


# }}}


# {{{ the proof, traced and compiled

#: The example's proof, with the family written as a lambda, and a geometric sum.
CASES = '''\
"""Facts over a family, cited at a function of the step."""

from __future__ import annotations

from lanky import by, claim
from lanky.known import one_more_term
from lanky.prelude import Fin, Nat, Real


@claim
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of ``0 .. n`` is ``n * (n + 1)``."""


@claim
def written() -> all(
    sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2 for n in Nat
):
    """Nicomachus's theorem, the family written as a lambda."""
    for n in written.conclusion.domain:
        if n == 0:
            yield by()
        else:
            assert (
                sum(i**3 for i in Fin[n + 1])
                == sum(i**3 for i in Fin[n]) + n**3
                == sum(i for i in Fin[n]) ** 2 + n**3
                == (sum(i for i in Fin[n]) + n) ** 2
                == sum(i for i in Fin[n + 1]) ** 2
            ), by(
                one_more_term(lambda i: i**3, n),
                written.conclusion[n - 1],
                gauss(n - 1),
                one_more_term(lambda k: k, n),
            )
            yield by()


@claim
def geometric(r: Real) -> all((r - 1) * sum(r**k for k in Fin[n]) == r**n - 1 for n in Nat):
    """The design's geometric sum: one more term, and the conclusion at n - 1."""
    for n in geometric.conclusion.domain:
        if n == 0:
            yield by()
        else:
            yield by(one_more_term, geometric.conclusion[n - 1])
'''


@pytest.fixture(scope="module")
def cases(tmp_path_factory) -> object:
    """The cases, imported."""
    path = tmp_path_factory.mktemp("family") / "family_cases.py"
    path.write_text(CASES, encoding="utf-8")
    return import_path(path)


@pytest.fixture(scope="module")
def example() -> object:
    """``examples/nicomachus.py``, imported."""
    return import_path(EXAMPLE)


def test_a_lambda_at_a_familys_place_is_the_familys_value(cases) -> None:
    """``one_more_term(lambda i: i**3, n)`` cites the fact with ``f`` at ``i ↦ i**3``."""
    proof = trace_proof(cases.written)
    (asserted,) = proof.leaves[-1].steps
    first, last = asserted.facts[0], asserted.facts[-1]
    assert first.text() == "one_more_term(lambda i: i**3, n)"
    assert last.text() == "one_more_term(lambda k: k, n)"
    assert isinstance(first.values[0], FamilyValue)


def test_the_fact_over_the_reals_is_restated_over_the_integers(example) -> None:
    """The family is a ``fun`` ascribed the reals, and the fact is shown through the cast."""
    pytest.importorskip("sympy")  # the multipliers are found by sympy
    command = compile_proof(trace_proof(example.nicomachus), mathlib=True)
    source = command.source
    assert "one_more_term (fun i => (i ^ 3 : ℝ)) n (by omega)" in source
    assert "one_more_term (fun i => (i : ℝ)) n (by omega)" in source
    assert (
        " : ∑ k ∈ Finset.Ico (0 : ℤ) (n + 1), k ^ 3 = "
        "(∑ k ∈ Finset.Ico (0 : ℤ) n, k ^ 3) + n ^ 3 := by"
    ) in source
    assert "(apply (Int.cast_injective (α := ℝ)); push_cast at cast ⊢; exact cast)" in source
    # the theorem at n - 1 is one of the step's facts up to algebra, and Gauss's
    # multiplier pairs its sum with the step's
    assert re.search(r"\) f_\d+\n", source)
    assert re.search(r"\(\(-1\) \* n : Int\) \* f_\d+", source)
    assert "exact step_1\n" in source
    assert command.summary == (
        "induction on n, 2 cases, 4 steps, 1 routine, using one_more_term and gauss"
    )
    # one row for the assert, its links under it, and the facts each link fits
    reasons = [row[-1] for row in command.outline]
    assert reasons == [
        "by one_more_term at (lambda i: i**3, n), the claim at (n - 1), gauss at (n - 1) "
        "and one_more_term at (lambda i: i, n)",
        "",
        "",
        "",
    ]


def test_a_real_family_needs_no_cast(cases) -> None:
    """``geometric``'s ``k ↦ r**k`` is a family of reals already: the fact is applied as it is."""
    source = compile_proof(trace_proof(cases.geometric), mathlib=True).source
    assert "one_more_term (fun k => r ^ k.toNat)" in source
    assert "Int.cast_injective" not in source


def test_a_steps_multipliers_see_its_sums() -> None:
    """``gauss(n - 1)`` at a step about ``sum(i for i in Fin(n))`` has the multiplier ``-n``."""
    pytest.importorskip("sympy")  # the multipliers are found by sympy
    part = Sum(((i, Fin[n]),), i)
    step = Comparison(part**2 + n**3, "==", (part + n) ** 2)
    fact = Comparison(2 * Sum(((i, Fin[n - 1 + 1]),), i), "==", (n - 1) * (n - 1 + 1))
    (multiplier,) = combination(step, [fact], {"n": Nat})
    assert render(multiplier) in ("-n", "-1*n", "(-1)*n")
    # a fact the step is, with a sum squared on both sides
    same_step = Comparison(cubes(n) + n**3, "==", part**2 + n**3)
    claim = Comparison(Sum(((i, Fin[n - 1 + 1]),), i**3), "==", Sum(((i, Fin[n - 1 + 1]),), i) ** 2)
    assert [render(value) for value in combination(same_step, [claim], {"n": Nat})] == ["1"]


# }}}


# {{{ the ladder


def test_the_ladder_tries_field_simp_then_ring() -> None:
    """After the attempts that prove a claim without it; never for a question of vacuity."""
    tactics = lean_module.MATHLIB_TACTICS
    assert tactics.index("(field_simp; ring)") == tactics.index("(push_cast; ring)") + 1
    assert tactics.index("field_simp") < tactics.index("linarith")
    assert "(field_simp; ring)" not in lean_module._mathlib_tactics((), refuting=True)
    assert _rung_of_text("(field_simp; ring)") == "by algebra, clearing its denominators"


# }}}


# {{{ with Lean and Mathlib

#: sumpy's Laplacian of ``log r``, as ``harmonic`` states it, with no body.
HARMONIC = '''\
"""The Laplacian of log r, with no body."""

from __future__ import annotations

from lanky import claim
from lanky.prelude import Real


@claim
def harmonic(x: Real, y: Real, away: x**2 + y**2 > 0) -> (
    (1 - 2 * x**2 / (x**2 + y**2)) / (x**2 + y**2)
    + (1 - 2 * y**2 / (x**2 + y**2)) / (x**2 + y**2)
    == 0
):
    """The Laplacian of log r, as sympy writes it, is zero away from the origin."""
'''


def _with_mathlib(mathlib_project: str | None, monkeypatch) -> None:
    """Point the Lean oracle at Mathlib, or skip, or fail where Mathlib was promised."""
    reason = None
    if mathlib_project is None:
        reason = "LANKY_LEAN_MATHLIB names no Lake project with Mathlib"
    elif os.environ.get("LANKY_LEAN_DISABLE"):
        reason = "the Lean oracle is disabled by LANKY_LEAN_DISABLE"
    else:
        from lanky.oracles.lean import LeanOracle

        available, why = LeanOracle().availability()
        if not available:
            reason = f"no Lean oracle here: {why}"
    if reason is not None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail(f"LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but {reason}", pytrace=False)
        pytest.skip(reason)
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)


def test_with_mathlib_the_example_is_proved_by_its_written_proof(
    mathlib_project, monkeypatch
) -> None:
    """All three theorems read proved; ``nicomachus`` by its proof, through ``one_more_term``."""
    _with_mathlib(mathlib_project, monkeypatch)
    facts = {fact.owner: fact for fact in claims(check_path(EXAMPLE))}
    assert {owner: fact.status for owner, fact in facts.items()} == {
        "gauss": Status.PROVED,
        "nicomachus": Status.PROVED,
        "cubes": Status.PROVED,
        "one_more_term": Status.PROVED,
    }
    account = facts["nicomachus"].provenance["proof"]
    assert account["closed"] is True, account
    assert account["summary"] == (
        "induction on n, 2 cases, 4 steps, 1 routine, using one_more_term and gauss"
    )
    assert facts["one_more_term"].id in facts["nicomachus"].rests_on


def test_with_mathlib_the_laplacian_of_log_r_needs_no_body(
    mathlib_project, monkeypatch, tmp_path
) -> None:
    """``field_simp`` clears the denominators, and ``ring`` closes what is left (#173)."""
    _with_mathlib(mathlib_project, monkeypatch)
    monkeypatch.setenv("LANKY_LEAN_PROOF_CACHE", "off")
    path = tmp_path / "harmonic_alone.py"
    path.write_text(HARMONIC, encoding="utf-8")
    (fact,) = claims(check_path(path))
    assert fact.status is Status.PROVED
    assert fact.provenance["tactic"] == "(field_simp; ring)"
    assert fact.provenance["found_proof"]["how"] == "by algebra, clearing its denominators"


# }}}
