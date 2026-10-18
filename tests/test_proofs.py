"""Written proofs: a claim's body traced in Python, compiled to Lean, and reported at its lines.

Most of what lanky does with a written proof is Python, and is tested without
Lean: whether a body is a proof, the trace (case splits, citations, the claim
and its stub), the matching of a fact cited by its name, the measure, the Lean
the proof compiles to, and the reading of Lean's answer back to the Python
lines, from messages made up here at the positions Lean gives them. The
Lean-checked half runs where Lean is, and skips cleanly where it is not; the
demonstration, lanky #140's ``every_box``, runs where Mathlib is.
"""

from __future__ import annotations

import os
import textwrap
from pathlib import Path

import pytest

from conftest import claims
from lanky.check import check_path, import_path
from lanky.citations import Citation
from lanky.cli import main as lanky_main
from lanky.cli import report_written
from lanky.induction import Lemma
from lanky.ledger import Fact, Ledger, Status
from lanky.matching import NoSinglePoint, single_point
from lanky.prelude import Fn, Int, Nat
from lanky.proofs import ProofError, compile_proof, trace_proof, written_lines
from lanky.proofs.cases import affine, from_affine, pins
from lanky.proofs.compile import measure
from lanky.proofs.report import audit, case_text, read
from lanky.proofs.trace import ClaimDef
from lanky.terms import Comparison, Var, render

#: Written proofs over the integers, which core Lean checks.
CASES = '''\
"""Written proofs over the integers."""

from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fin, Fn, Int, Nat


@claim
def ct(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence[a - 2, b], ct.conclusion[a - 2, b + 2], pde[a - 2, b])


@claim
def ct_wrong(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct_wrong.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence[a - 2, b], ct_wrong.conclusion[a - 2, b + 3], pde[a - 2, b])


@claim
def ct_negative(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct_negative.conclusion.domain:
        yield by(recurrence[a - 2, b], ct_negative.conclusion[a - 2, b + 2], pde[a - 2, b])


@claim
def ct_condition(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct_condition.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(stored)


@claim
def every_box(
    n: Nat,
    p: Nat,
    c: Fn[Nat, Int, Int],
    D: Fn[Nat, Nat, Nat, Int],
    R: Fn[Nat, Nat, Nat, Int],
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
    for i, a, b in every_box.conclusion.domain:
        if a + b == 0:
            yield by(centre_copy, centre)
        elif a < 2:
            yield by(copies, stored)
        else:
            yield by(recurrence, every_box.conclusion[i, a - 2, b + 2], pde)


@claim
def each_box(
    n: Nat,
    D: Fn[Nat, Nat, Nat, Int],
    R: Fn[Nat, Nat, Nat, Int],
    pde: all(D[i, a + 2, b] + D[i, a, b + 2] == 0 for i in Fin[n] for a in Nat for b in Nat),
    stored: all(R[i, a, b] == D[i, a, b] for i in Fin[n] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[i, a + 2, b] == -R[i, a, b + 2] for i in Fin[n] for a in Nat for b in Nat),
) -> all(all(R[i, a, b] == D[i, a, b] for a in Nat for b in Nat) for i in Fin[n]):
    for i in each_box.conclusion.domain:
        for a, b in each_box.conclusion[i].domain:
            if a < 2:
                yield by(stored)
            else:
                yield by(recurrence, each_box.conclusion[i][a - 2, b + 2], pde)


@claim
def sum_to(
    S: Fn[Nat, Int], base: S[0] == 0, step: all(S[k + 1] == S[k] + 1 for k in Nat)
) -> all(S[n] == n for n in Nat):
    for n in sum_to.conclusion.domain:
        if n == 0:
            yield by(base)
        else:
            yield by(step[n - 1], sum_to.conclusion[n - 1])


@claim
def stepped(
    S: Fn[Nat, Int], base: S[0] == 0, step: all(S[k + 1] == S[k] + 1 for k in Nat)
) -> all(S[n] == n for n in Nat):
    for n in stepped.conclusion.domain:
        if n == 0:
            yield by(base)
        else:
            assert S[n] == S[n - 1] + 1, by(step)
            yield by(stepped.conclusion[n - 1])


@claim
def climb(
    p: Nat,
    H: Fn[Nat, Int],
    top: H[p] == 0,
    step: all(H[k] == H[k + 1] for k in Nat if k < p),
) -> all(H[k] == 0 for k in Nat if k <= p):
    for k in reversed(climb.conclusion.domain):
        if k == p:
            yield by(top)
        else:
            yield by(step[k], climb.conclusion[k + 1])


@claim
def lex(
    R: Fn[Nat, Nat, Int],
    base: R[0, 0] == 0,
    down_b: all(R[a, b + 1] == R[a, b] for a in Nat for b in Nat),
    down_a: all(R[a + 1, 0] == R[a, 7] for a in Nat),
) -> all(R[a, b] == 0 for a in Nat for b in Nat):
    for a, b in lex.conclusion.domain:
        if b >= 1:
            yield by(down_b[a, b - 1], lex.conclusion[a, b - 1])
        elif a >= 1:
            yield by(down_a[a - 1], lex.conclusion[a - 1, 7])
        else:
            yield by(base)


@claim
def routine(n: Nat, m: Nat, h: m == n + 1) -> m - n == 1:
    if n == 0:
        return by()
    return by(h)


@claim
def zero_times(f: Fn[Nat, Int], h: all(f[k] == 2 * k for k in Nat if k >= 1)) -> f[0] * 0 == 0:
    return by(h[0])


@claim
def both_parts(
    S: Fn[Nat, Int], T: Fn[Nat, Int], starts: (S[0] == 1) & (T[0] == 2)
) -> S[0] + T[0] == 3:
    return by(starts)


@claim
def cites_later(f: Fn[Nat, Int], h: all(f[k] == k for k in Nat)) -> f[3] == 3:
    return by(identity_at(f, 3))


@claim
def identity_at(f: Fn[Nat, Int], h: all(f[k] == k for k in Nat), m: Nat) -> f[m] == m:
    """Proved by lanky alone; cited by the claim above, which is written before it."""


@claim
def by_its_conditions(
    S: Fn[Nat, Int], base: S[0] == 0, step: all(S[k + 1] == S[k] + 1 for k in Nat)
) -> all(S[n] == n for n in Nat):
    for n in by_its_conditions.conclusion.domain:
        if n == 0:
            yield by(by_its_conditions.conditions.base)
        else:
            yield by(by_its_conditions.conditions.step, by_its_conditions.conclusion[n - 1])
'''

#: Bodies lanky refuses before Lean is asked, each with the kind of refusal.
REFUSED = '''\
"""Written proofs lanky refuses before Lean is asked."""

from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fn, Int, Nat


def small(x):
    if x < 2:
        return True
    return False


@claim
def ct_later(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct_later.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence[a - 2, b], ct_later.conclusion[a, b + 2], pde[a - 2, b])


@claim
def out_of_order(
    R: Fn[Nat, Nat, Int], h: all(R[a, b] == 0 for a in Nat for b in Nat)
) -> all(R[a, b] == 0 for a in Nat for b in Nat):
    for a, b in out_of_order.conclusion.domain:
        yield by(h, out_of_order.conclusion[a + 1, b - 1])


@claim
def ct_self(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    pde: all(D[a + 2, b] + D[a, b + 2] == 0 for a in Nat for b in Nat),
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    recurrence: all(R[a + 2, b] == -R[a, b + 2] for a in Nat for b in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat):
    for a, b in ct_self.conclusion.domain:
        if a < 2:
            yield by(stored)
        else:
            yield by(recurrence[a - 2, b], ct_self(a - 2, b + 2), pde[a - 2, b])


@claim
def smaller_input(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] == 0:
    if n == 0:
        return by(h)
    return by(smaller_input(n - 1))


@claim
def ct_nopoint(
    D: Fn[Nat, Nat, Int],
    R: Fn[Nat, Nat, Int],
    E: Fn[Nat, Int],
    stored: all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2),
    apart: all(E[a] == 0 for a in Nat),
) -> all(R[a, b] == D[a, b] for a in Nat for b in Nat if a < 2):
    for a, b in ct_nopoint.conclusion.domain:
        yield by(stored, apart)


@claim
def foreign_if(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in foreign_if.conclusion.domain:
        if small(a):
            yield by(h)
        else:
            yield by(h)


@claim
def and_as_a_value(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in and_as_a_value.conclusion.domain:
        either = (a < 2) or (a > 5)
        yield by(h)


@claim
def returns_a_number(n: Nat) -> n + 0 == n:
    return 3


@claim
def asked_twice(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in asked_twice.conclusion.domain:
        if a < 2:
            if a < 2:
                yield by(h)
        else:
            yield by(h)


@claim
def old_claim(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    def claim(a):
        return h

    return claim


@claim
def old_induction(
    n: Nat, S: Fn[Nat, Int], base: S[0] == 0, step: all(S[k + 1] == S[k] + 1 for k in Nat)
) -> S[n] == n:
    def claim(n):
        if n == 0:
            return base
        return step(n - 1), claim(n - 1)

    return claim


@claim
def old_return(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] == 0:
    return h, h


@claim
def old_chain(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] == 0:
    return S[n].equals(0, by=h)


@claim
def old_at_most(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] <= 0:
    return S[n].at_most(0, by=h)


@claim
def old_point(
    R: Fn[Nat, Int], h: all(R[a + 1] == R[a] for a in Nat)
) -> all(R[a] == R[0] for a in Nat):
    for a in old_point.conclusion.domain:
        if a == 0:
            yield by()
        else:
            yield by(h(a - 1), old_point.conclusion[a - 1])


@claim
def same_point(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in same_point.conclusion.domain:
        yield by(same_point.conclusion[a])


@claim
def climbs_forward(
    p: Nat, H: Fn[Nat, Int], top: H[p] == 0, step: all(H[k] == H[k + 1] for k in Nat if k < p)
) -> all(H[k] == 0 for k in Nat if k <= p):
    for k in climbs_forward.conclusion.domain:
        if k == p:
            yield by(top)
        else:
            yield by(step[k], climbs_forward.conclusion[k + 1])


@claim
def unbounded(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in reversed(unbounded.conclusion.domain):
        yield by(h)


@claim
def own_domain(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in own_domain.domain:
        yield by(h)


@claim
def own_point(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in own_point.conclusion.domain:
        yield by(h, own_point[a - 1])


@claim
def short_dom(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in short_dom.dom:
        yield by(h)


@claim
def flat_point(
    R: Fn[Nat, Nat, Int], h: all(all(R[i, a] == 0 for a in Nat) for i in Nat)
) -> all(all(R[i, a] == 0 for a in Nat) for i in Nat):
    for i in flat_point.conclusion.domain:
        for a in flat_point.conclusion[i].domain:
            yield by(h, flat_point.conclusion[i - 1, a])


@claim
def yield_outside(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] == 0:
    yield by(h)


@claim
def return_in_the_loop(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in return_in_the_loop.conclusion.domain:
        return by(h)


@claim
def two_yields(
    R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)
) -> all(R[a] == 0 for a in Nat):
    for a in two_yields.conclusion.domain:
        yield by(h)
        yield by(h)


@claim
def no_variables(n: Nat) -> n + 0 == n:
    for k in no_variables.conclusion.domain:
        yield by()


@claim
def bare_return(n: Nat, m: Nat, h: m == n + 1) -> m - n == 1:
    if n == 0:
        return
    return by(h)


@claim
def falls_off(n: Nat, m: Nat, h: m == n + 1) -> m - n == 1:
    assert m == n + 1, by(h)


@claim
def continues(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in continues.conclusion.domain:
        if a < 2:
            continue
        yield by(h)


@claim
def path_ends(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in path_ends.conclusion.domain:
        if a < 2:
            yield by(h)
        else:
            assert R[a] == 0, by(h)


@claim
def bare_yield(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in bare_yield.conclusion.domain:
        yield


@claim
def mixes(R: Fn[Nat, Int], h: all(R[a] == 0 for a in Nat)) -> all(R[a] == 0 for a in Nat):
    for a in mixes.conclusion.domain:
        yield by(h)
    return by(h)


@claim
def a_message(n: Nat, S: Fn[Nat, Int], h: all(S[k] == 0 for k in Nat)) -> S[n] == 0:
    assert S[n] == 0, "it is zero"
    return by()


@claim
def false_as_written(n: Nat) -> n + 0 == n:
    assert 1 == 2
    return by()
'''


@pytest.fixture(scope="module")
def cases(tmp_path_factory) -> object:
    """The integer cases, imported."""
    path = tmp_path_factory.mktemp("proofs") / "cases_core.py"
    path.write_text(CASES, encoding="utf-8")
    return import_path(path)


@pytest.fixture(scope="module")
def refused(tmp_path_factory) -> object:
    """The refused cases, imported."""
    path = tmp_path_factory.mktemp("refused") / "refused.py"
    path.write_text(REFUSED, encoding="utf-8")
    return import_path(path)


def _line(module: object, text: str) -> int:
    """The line of the module's file that holds ``text``, the first one."""
    source = Path(module.__file__).read_text(encoding="utf-8").splitlines()
    return next(number for number, line in enumerate(source, 1) if text in line)


# {{{ whether there is a proof


def _no_proof(fn) -> bool:
    return written_lines(fn) is None


def test_a_body_of_a_docstring_dots_or_pass_is_no_proof() -> None:
    def docstring(n):
        """Only a docstring."""

    def dots(n): ...

    def passes(n):
        pass

    def both(n):
        """A docstring, then dots."""
        ...

    def written(n):
        """A docstring, then a proof."""
        return n

    assert _no_proof(docstring) and _no_proof(dots) and _no_proof(passes) and _no_proof(both)
    first, last = written_lines(written)
    assert first == last == written.__code__.co_firstlineno + 2


def test_running_the_file_never_runs_a_proof(tmp_path) -> None:
    """``python file.py`` calls no body: evaluating and sampling the claim read the annotations."""
    path = tmp_path / "loud.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import by, claim
            from lanky.prelude import Nat

            RAN = []


            @claim
            def loud(n: Nat) -> n + 0 == n:
                RAN.append("the body ran")
                return by()
            """
        ),
        encoding="utf-8",
    )
    module = import_path(path)
    assert module.loud(n=3)
    assert module.loud.test()[0]
    assert module.RAN == []


def test_outside_a_proof_a_theorem_is_evaluated_at_values_given_by_name(cases) -> None:
    assert cases.both_parts(S=[1], T=[2])
    with pytest.raises(TypeError, match=r"given by name, as both_parts\(S=\.\.\., T=\.\.\.\)"):
        cases.both_parts([1], [2])


# }}}


# {{{ the trace


def test_the_trace_splits_the_cases_and_records_what_each_yield_cites(cases) -> None:
    proof = trace_proof(cases.every_box)
    assert proof.claim.params == ("i", "a", "b") and proof.claim.generalized == ()
    paths = [
        (
            [(str(question.prop), question.answer) for question in leaf.questions],
            [citation.text() for citation in leaf.facts],
        )
        for leaf in proof.leaves
    ]
    assert paths == [
        ([("a + b == 0", True)], ["centre_copy", "centre"]),
        ([("a + b == 0", False), ("a < 2", True)], ["copies", "stored"]),
        (
            [("a + b == 0", False), ("a < 2", False)],
            ["recurrence", "every_box.conclusion[i, a - 2, b + 2]", "pde"],
        ),
    ]
    assert [leaf.line for leaf in proof.leaves] == [
        _line(cases, "yield by(centre_copy, centre)"),
        _line(cases, "yield by(copies, stored)"),
        _line(cases, "yield by(recurrence, every_box.conclusion[i, a - 2, b + 2], pde)"),
    ]
    assert all(leaf.point for leaf in proof.leaves)
    assert proof.calls[0].is_claim and proof.calls[0].line == proof.leaves[2].line
    loop = _line(cases, "for i, a, b in every_box.conclusion.domain:")
    assert proof.claim.line == loop
    assert proof.where.startswith(f"cases_core.py:{loop}-")


def test_a_nested_domain_is_a_loop_inside_the_loop(cases) -> None:
    """The design's 2.4b: ``each_box.conclusion[i].domain``, a yield closing ``(i, a, b)``."""
    proof = trace_proof(cases.each_box)
    assert proof.claim.params == ("i", "a", "b") and proof.claim.levels == (1, 2)
    cited = [citation.text() for citation in proof.leaves[1].facts]
    assert cited == ["recurrence", "each_box.conclusion[i][a - 2, b + 2]", "pde"]
    # the conclusion as the proof closes it: the two levels of for as one
    assert [var.name for var, _ in proof.conclusion.binders] == ["i", "a", "b"]
    source = compile_proof(proof, mathlib=False).source
    assert "theorem Lanky.each_box.claim (n : Int) (hn : 0 ≤ n)" in source
    assert "(i : Int) (hi : 0 ≤ i) (hi_1 : i < n) (a : Int) (ha : 0 ≤ a) (b : Int)" in source
    assert "termination_by a.toNat" in source
    # the theorem states the levels nested, and the claim takes them flat
    assert "  intro i hd hd_1\n  intro a hd_2 b hd_3\n" in source


def test_an_assert_is_a_step_read_by_running_the_body_again(cases) -> None:
    """The first run answers the assert "false" and reads ``by(...)``; the next answers "true"."""
    proof = trace_proof(cases.stepped)
    base, step = proof.leaves
    assert base.steps == () and [c.text() for c in base.facts] == ["base"]
    (asserted,) = step.steps
    assert asserted.line == _line(cases, "assert S[n] == S[n - 1] + 1, by(step)")
    assert [render(prop) for prop in asserted.props] == ["S[n] == S[n - 1] + 1"]
    assert [citation.text() for citation in asserted.facts] == ["step"]
    assert [citation.text() for citation in step.facts] == ["stepped.conclusion[n - 1]"]
    assert proof.claim.params == ("n",) and proof.claim.generalized == ()


def test_a_condition_is_cited_through_the_claims_tree(cases) -> None:
    """``by_its_conditions.conditions.step`` is the condition ``step`` names in the proof."""
    proof = trace_proof(cases.by_its_conditions)
    assert [[c.text() for c in leaf.facts] for leaf in proof.leaves] == [
        ["base"],
        ["step", "by_its_conditions.conclusion[n - 1]"],
    ]


def test_a_question_asked_twice_on_a_path_is_answered_alike(refused) -> None:
    proof = trace_proof(refused.asked_twice)
    # the second if a < 2 is answered as the first was, and splits nothing
    assert len(proof.leaves) == 2
    assert [[q.answer for q in leaf.questions] for leaf in proof.leaves] == [[True], [False]]


def test_an_if_outside_the_proofs_own_code_is_refused(refused) -> None:
    with pytest.raises(ProofError, match="outside the proof's own code") as raised:
        trace_proof(refused.foreign_if)
    assert raised.value.kind == "question"


def test_or_used_as_a_value_is_refused(refused) -> None:
    with pytest.raises(ProofError, match="not by an if") as raised:
        trace_proof(refused.and_as_a_value)
    assert raised.value.line == _line(refused, "either = (a < 2) or (a > 5)")


def test_a_claim_that_calls_itself_is_refused_with_its_conclusion_as_the_fix(refused) -> None:
    """The design's 3.4: a claim never calls itself; the earlier case is a point."""
    with pytest.raises(ProofError) as raised:
        trace_proof(refused.ct_self)
    error = raised.value
    assert error.kind == "self-reference"
    line = _line(refused, "ct_self(a - 2, b + 2)")
    assert error.message == (
        f"ct_self(a - 2, b + 2) at refused.py:{line} calls the claim in its own proof, and a "
        "claim does not call itself; an earlier case is the conclusion at an earlier point of "
        "its domain, in brackets"
    )
    assert error.fix == "ct_self.conclusion[a - 2, b + 2]"
    with pytest.raises(ProofError) as raised:
        trace_proof(refused.smaller_input)
    assert raised.value.kind == "self-reference"
    assert (
        "a claim does not call itself; to argue from an earlier case, put n in the "
        "conclusion's for, -> all(... for n in ...), and cite smaller_input.conclusion[n - 1]"
    ) in raised.value.message
    assert raised.value.fix == "smaller_input.conclusion[n - 1]"


def test_a_return_of_something_that_is_no_reason_is_refused(refused) -> None:
    with pytest.raises(ProofError, match="this return gives a int") as raised:
        trace_proof(refused.returns_a_number)
    assert raised.value.kind == "return"


def test_the_forms_of_lanky_0_5_are_refused_with_the_line_to_write(refused) -> None:
    """``def claim``, ``return f, g``, ``.equals`` and ``h(p)``: each refused with the 0.6 line."""
    cases = {
        "old_claim": (
            "removed",
            "def claim(a) is how lanky 0.5 wrote a proof",
            "for a in old_claim.conclusion.domain:",
        ),
        "old_induction": (
            "removed",
            "def claim(n) is how lanky 0.5 wrote an induction on the claim's parameters",
            "for n in old_induction.conclusion.domain:",
        ),
        "old_return": ("removed", "return h, h is how lanky 0.5", "return by(h, h)"),
        "old_chain": (
            "removed",
            ".equals(...) is how lanky 0.5 wrote a step",
            "assert S[n] == 0, by(h)",
        ),
        "old_at_most": ("removed", ".at_most(...) is how lanky 0.5", "assert S[n] <= 0, by(h)"),
        "old_point": ("removed", "h(a - 1) is how lanky 0.5 cited a condition", "h[a - 1]"),
    }
    for name, (kind, said, fix) in cases.items():
        with pytest.raises(ProofError) as raised:
            trace_proof(getattr(refused, name))
        assert raised.value.kind == kind, name
        assert said in raised.value.message, (name, raised.value.message)
        assert raised.value.fix == fix, (name, raised.value.fix)


def test_the_tree_is_spelled_out_and_its_other_spellings_refused(refused) -> None:
    """The design's 3.4: ``name.domain``, ``name[p]`` and ``.dom`` refused, the tree's spelled."""
    cases = {
        "own_domain": "own_domain.conclusion.domain",
        "own_point": "own_point.conclusion[a - 1]",
        "short_dom": "short_dom.conclusion.domain",
        "flat_point": "flat_point.conclusion[i - 1][a]",
    }
    for name, fix in cases.items():
        with pytest.raises(ProofError) as raised:
            trace_proof(getattr(refused, name))
        assert raised.value.fix == fix, (name, raised.value.message)
    with pytest.raises(ProofError, match="a claim has no domain of its own"):
        trace_proof(refused.own_domain)


def test_a_point_the_loop_has_not_filled_in_is_refused_before_lean(refused) -> None:
    """The design's 3.5: an earlier point is earlier in the loop, lexicographic and strict."""
    with pytest.raises(ProofError) as raised:
        trace_proof(refused.ct_later)
    assert raised.value.kind == "later"
    assert raised.value.message == (
        "ct_later.conclusion[a, b + 2] is not filled in yet when the loop is at (a, b)"
    )
    assert raised.value.line == _line(refused, "ct_later.conclusion[a, b + 2]")
    # smaller in b, but larger in a, which the loop walks first
    with pytest.raises(ProofError, match=r"\[a \+ 1, b - 1\] is not filled in yet") as raised:
        trace_proof(refused.out_of_order)
    assert raised.value.fix == (
        "cite the conclusion at a point the loop has filled in, as "
        "out_of_order.conclusion[a - 1, b]"
    )
    with pytest.raises(ProofError, match=r"same_point.conclusion\[a\] is the point the loop is"):
        trace_proof(refused.same_point)


def test_an_argument_from_above_walks_a_bounded_domain_reversed(cases, refused) -> None:
    """0.5's climb: the conclusion at ``k + 1`` comes earlier in a reversed loop."""
    proof = trace_proof(cases.climb)
    assert proof.claim.directions == (-1,)
    assert [citation.text() for citation in proof.leaves[1].facts] == [
        "step[k]",
        "climb.conclusion[k + 1]",
    ]
    source = compile_proof(proof, mathlib=False).source
    assert "termination_by (p - k).toNat\ndecreasing_by omega" in source
    assert "have pin_1 : k = p := by omega\n" in source
    with pytest.raises(ProofError) as raised:
        trace_proof(refused.climbs_forward)
    assert raised.value.fix == "for k in reversed(climbs_forward.conclusion.domain):"
    with pytest.raises(ProofError, match="a in Nat has no top") as raised:
        trace_proof(refused.unbounded)


def test_yield_closes_the_point_the_loop_is_at_once(refused) -> None:
    with pytest.raises(ProofError, match="outside a loop over yield_outside.conclusion.domain"):
        trace_proof(refused.yield_outside)
    first = "leaves the loop over return_in_the_loop.conclusion.domain at its first point"
    with pytest.raises(ProofError, match=first) as raised:
        trace_proof(refused.return_in_the_loop)
    assert raised.value.fix == "yield by(h)"
    with pytest.raises(ProofError, match="the point was closed already at line"):
        trace_proof(refused.two_yields)
    with pytest.raises(ProofError, match="no_variables's conclusion has no for") as raised:
        trace_proof(refused.no_variables)
    assert raised.value.fix == "return by(...)"


def test_every_case_ends_with_a_closing_line(refused) -> None:
    """The design's closing rule: a bare return, continue, or a path that ends, refused."""
    cases = {
        "bare_return": ("a bare return at line", "return by()", "return"),
        "falls_off": ("the case ends at line", "return by()", 'assert m == n + 1, by(h)'),
        "continues": ("continue at line", "yield by()", "continue"),
        "path_ends": ("the case ends at line", "yield by()", "assert R[a] == 0, by(h)"),
        "bare_yield": ("a bare yield closes the case", "yield by()", "yield"),
    }
    for name, (said, fix, at) in cases.items():
        with pytest.raises(ProofError) as raised:
            trace_proof(getattr(refused, name))
        error = raised.value
        assert error.kind == "close", name
        assert said in error.message, (name, error.message)
        assert error.fix == fix, name
        source = Path(refused.__file__).read_text(encoding="utf-8").splitlines()
        assert source[error.line - 1].strip().startswith(at), (name, error.line)
    with pytest.raises(ProofError) as raised:
        trace_proof(refused.continues)
    assert raised.value.message.startswith("when a < 2 (refused.py:")
    with pytest.raises(ProofError, match="one proof does not mix the two") as raised:
        trace_proof(refused.mixes)
    assert raised.value.kind == "return"


def test_an_assert_gives_its_reason_as_by(refused) -> None:
    with pytest.raises(ProofError, match="this one gives the text 'it is zero'") as raised:
        trace_proof(refused.a_message)
    assert raised.value.kind == "assert"
    assert raised.value.line == _line(refused, 'assert S[n] == 0, "it is zero"')
    with pytest.raises(ProofError, match="false as Python evaluates it") as raised:
        trace_proof(refused.false_as_written)
    assert raised.value.kind == "false"


def test_the_conclusion_is_cited_at_the_variables_of_its_for(cases) -> None:
    proof = trace_proof(cases.sum_to)
    assert proof.claim.params == ("n",) and proof.claim.generalized == ()
    assert [str(question.prop) for question in proof.leaves[0].questions] == ["n == 0"]
    cited = [citation.text() for citation in proof.leaves[1].facts]
    assert cited == ["step[n - 1]", "sum_to.conclusion[n - 1]"]


def test_a_later_claim_is_cited_from_the_live_globals(cases) -> None:
    proof = trace_proof(cases.cites_later)
    (citation,) = proof.leaves[0].facts
    assert citation.source is cases.identity_at and citation.text() == "identity_at(f, 3)"
    assert proof.cited == [cases.identity_at]


def test_the_tree_outside_a_proof_says_what_it_is(cases) -> None:
    from lanky import by
    from lanky.surface import FormError, OutsideAProof

    with pytest.raises(OutsideAProof, match="walked inside that proof"):
        iter(cases.sum_to.conclusion.domain)
    assert repr(cases.sum_to.conclusion) == "<sum_to.conclusion: all(S[n] == n for n in Nat)>"
    assert repr(cases.sum_to.conclusion.domain) == "<sum_to.conclusion.domain: n in Nat>"
    assert repr(cases.sum_to.conditions) == "<sum_to.conditions: base, step>"
    assert repr(cases.sum_to.conditions.base) == "<sum_to.conditions.base: S[0] == 0>"
    with pytest.raises(AttributeError, match="S is an input of sum_to, not a condition"):
        cases.sum_to.conditions.S  # noqa: B018 - the refusal is what is tested
    with pytest.raises(FormError, match="a claim has no domain of its own"):
        cases.sum_to.domain  # noqa: B018 - the refusal is what is tested
    with pytest.raises(FormError, match=r"write sum_to.conclusion\[3\]"):
        cases.sum_to[3]
    with pytest.raises(FormError, match=r"write each_box.conclusion\[1\]\[2, 3\]"):
        cases.each_box.conclusion[1, 2, 3]
    assert repr(by(...)) == "by(...)"
    with pytest.raises(TypeError, match="names no fact"):
        by("pde")
    with pytest.raises(TypeError, match="takes no facts beside it"):
        by(cases.sum_to, ...)
    with pytest.raises(TypeError, match="not a condition"):
        bool(by())


# }}}


# {{{ matching, pins and the measure


def test_affine_forms_read_and_write_offsets() -> None:
    a, b = Var("a"), Var("b")
    assert affine(a - 2 + 2) == {"a": 1}
    assert render(from_affine(affine(2 * (a + b) - 1 + a), ["a", "b"])) == "3*a + 2*b - 1"


def test_a_fact_is_matched_at_the_point_its_offsets_solve() -> None:
    """A fact that gives one side of the claim is at the point that lines that side up."""
    a, b, x, y = Var("a"), Var("b"), Var("x"), Var("y")
    R, C, D = Var("R"), Var("C"), Var("D")
    types = {"R": Fn[Nat, Nat, Int], "C": Fn[Nat, Nat, Int], "D": Fn[Nat, Nat, Int]}
    types.update(a=Nat, b=Nat)
    claim = [R[a, b], D[a, b]]
    copies = Lemma(
        "copies",
        ((x, Nat), (y, Nat)),
        (("value", "x"), ("value", "y")),
        Comparison(R[x + 2, y], "==", C[x, y]),
    )
    point = single_point(copies, claim, types, (), "copies")
    assert [render(value) for value in point] == ["a - 2", "b"]
    stuck = Lemma("stuck", ((x, Nat),), (("value", "x"),), Comparison(R[x, 0], "==", C[x, 0]))
    with pytest.raises(NoSinglePoint):
        single_point(stuck, claim, types, (), "stuck")


def test_naturals_that_sum_to_nothing_are_each_nothing() -> None:
    a, b, k, p = Var("a"), Var("b"), Var("k"), Var("p")
    types = {"a": Nat, "b": Nat, "k": Nat, "p": Nat}
    assert pins(a + b == 0, types) == [("a", 0), ("b", 0)]
    assert pins(a == 1, types) == [("a", 1)]
    assert pins(a + b == 2, types) == []
    assert pins(b < 1, types) == [("b", 0)] and pins(b <= 0, types) == [("b", 0)]
    assert pins(b < 2, types) == []
    assert [(name, render(value)) for name, value in pins(k == p, types, ["k"])] == [("k", "p")]


def _calls(*values: tuple) -> list[Citation]:
    claim = ClaimDef("claim", ("a", "b"), (Nat, Nat), (), 1)
    return [Citation(claim, value, 10, bracket=True) for value in values]


def test_the_measure_is_down_up_or_a_pair() -> None:
    a, b, p = Var("a"), Var("b"), Var("p")
    claim = ClaimDef("claim", ("a", "b"), (Nat, Nat), (), 1)
    assert measure(claim, _calls((a - 2, b + 2)), []).said == "induction on a"
    up = measure(claim, _calls((a + 1, b)), [a <= p])
    assert up.kind == "up" and render(up.bound) == "p"
    lex = measure(claim, _calls((a, b - 1), (a - 1, b + 7)), [])
    assert lex.kind == "lex" and lex.names == ("a", "b")
    with pytest.raises(ProofError) as raised:
        measure(claim, _calls((a, b + 2)), [])
    assert raised.value.kind == "measure"
    assert raised.value.message == (
        "claim[a, b + 2] is not at smaller values: neither a nor b is smaller than at (a, b)"
    )


def test_a_fact_cited_by_name_is_applied_at_the_point_of_the_case(cases) -> None:
    command = compile_proof(trace_proof(cases.every_box), mathlib=False)
    source = command.source
    assert "have pin_1 : a = 0 := by omega\n" in source and "subst a\n" in source
    assert "have f_1 := centre_copy i (by omega) (by omega)" in source
    assert "have f_3 := copies i (by omega) (by omega) a (by omega) b (by omega)" in source
    assert command.summary == "induction on a, 3 cases, 3 steps"


def test_no_single_point_asks_for_the_point(refused) -> None:
    with pytest.raises(ProofError) as raised:
        compile_proof(trace_proof(refused.ct_nopoint), mathlib=False)
    assert raised.value.kind == "no-point" and raised.value.fix == "apart[a]"
    assert "no point of apart fits a term of this case's claim" in raised.value.message


def test_a_fact_by_name_is_matched_against_the_terms_of_the_steps_other_facts(cases) -> None:
    """``by(recurrence, claim[i, a - 2, b + 2], pde)``: each fits at ``(i, a - 2, b)``.

    Against the claim's cells alone, ``pde`` touches ``D[i, a, b]`` at two
    points; with the cells of the claim at the earlier point, one of them
    is about those cells and nothing else.
    """
    command = compile_proof(trace_proof(cases.every_box), mathlib=False)
    source = command.source
    assert "recurrence i (by omega) (by omega) (a - 2) (by omega) b (by omega)" in source
    assert "pde i (by omega) (by omega) (a - 2) (by omega) b (by omega)" in source


# }}}


# {{{ the Lean a proof compiles to


def test_the_claim_is_a_recursive_theorem_with_the_python_names(cases) -> None:
    command = compile_proof(trace_proof(cases.ct), mathlib=False)
    source = command.source
    assert source.startswith("set_option autoImplicit false in\ntheorem Lanky.ct.claim (D : ")
    assert "(pde : ∀ a : Int, 0 ≤ a → ∀ b : Int, 0 ≤ b → D (a + 2) b + D a (b + 2) = 0)" in source
    assert "  by_cases case_1 : a < 2\n" in source
    assert "termination_by a.toNat\ndecreasing_by omega\n" in source
    assert (
        "have f_3 := Lanky.ct.claim D R (a - 2) (by omega) (b + 2) (by omega) pde stored" in source
    )
    assert "exact Lanky.ct.claim D R a (by assumption) b (by assumption) pde stored recurrence" in (
        source
    )
    assert source.endswith("#print axioms _root_.Lanky.ct\n")


def test_the_conclusions_variable_is_a_parameter_of_the_claim(cases) -> None:
    source = compile_proof(trace_proof(cases.sum_to), mathlib=False).source
    assert "theorem Lanky.sum_to.claim (S : Int → Int) (n : Int) (hn : 0 ≤ n)" in source
    assert "Lanky.sum_to.claim S (n - 1) (by omega) base step" in source
    assert "subst n" in source


def test_an_asserted_step_is_a_have_the_rest_of_its_case_uses(cases) -> None:
    """``assert S[n] == S[n - 1] + 1``, then ``yield by(stepped.conclusion[n - 1])``."""
    command = compile_proof(trace_proof(cases.stepped), mathlib=False)
    source = command.source
    assert "have step_1 : S n = S (n - 1) + 1 := by" in source
    assert "have rest_1 : S (n - 1) + 1 = n := by" in source
    assert "exact step_1.trans rest_1" in source
    assert "Lanky.stepped.claim S (n - 1) (by omega) base step" in source
    assert command.summary == "induction on n, 2 cases, 3 steps"


def test_a_pair_that_gets_smaller_is_measured_as_a_pair(cases) -> None:
    source = compile_proof(trace_proof(cases.lex), mathlib=False).source
    assert "termination_by (a.toNat, b.toNat)\n\n" in source
    # b >= 1 false keeps the natural b at 0, which the branch substitutes
    assert "  · have pin_1 : b = 0 := by omega\n    subst b\n" in source


def test_a_case_closed_with_by_nothing_is_lankys_to_close(cases) -> None:
    source = compile_proof(trace_proof(cases.routine), mathlib=False).source
    assert "    first\n      | omega\n      | (simp_all; done)" in source
    assert compile_proof(trace_proof(cases.routine), mathlib=False).summary == (
        "2 cases, 1 step, 1 routine"
    )


def test_a_conjunction_is_cited_as_both_parts(cases) -> None:
    source = compile_proof(trace_proof(cases.both_parts), mathlib=False).source
    assert "(starts_1 : S 0 = 1) (starts_2 : T 0 = 2)" in source
    assert "have f_1 := starts_1\n" in source and "have f_2 := starts_2\n" in source


def test_a_cited_theorem_is_restated_as_a_hypothesis(cases) -> None:
    command = compile_proof(trace_proof(cases.cites_later), mathlib=False)
    assert (
        "(identity_at : ∀ f : Int → Int, ∀ m : Int, 0 ≤ m → (∀ k : Int, 0 ≤ k → f k = k) → "
        "f m = m)" in command.source
    )
    assert "have f_1 := identity_at f 3 (by omega) (by first | assumption | omega)" in (
        command.source
    )
    assert command.cited == [cases.identity_at]
    assert command.summary == "1 step, using identity_at"


def test_a_hypothesis_named_like_a_lean_word_keeps_meaning_one_thing(tmp_path) -> None:
    path = tmp_path / "names.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import by, claim
            from lanky.prelude import Nat


            @claim
            def odd_names(n: Nat, fun: n >= 1, Real: n <= 5) -> n >= 1:
                return by(fun, Real)
            """
        ),
        encoding="utf-8",
    )
    module = import_path(path)
    source = compile_proof(trace_proof(module.odd_names), mathlib=False).source
    assert "(«fun» : n ≥ 1) (Real_ : n ≤ 5)" in source
    assert "have f_1 := «fun»\n" in source


# }}}


# {{{ Lean's answer, read back to the Python lines


def _span(command, kind: str, line: int, condition: str | None = None) -> tuple[int, int]:
    """The Lean line (from 1) and column of the first piece of ``kind`` from Python ``line``.

    ``condition`` picks the condition a span discharges, by its text.
    """
    for number, emitted in enumerate(command.lines, 1):
        for start, _end, origin in emitted.spans:
            said = origin.detail.get("condition")
            if condition is not None and (said is None or render(said) != condition):
                continue
            if origin.kind == kind and origin.line == line:
                return number, start + 4
        if (
            emitted.origin is not None
            and emitted.origin.kind == kind
            and emitted.origin.line == line
        ):
            return number, 0
    raise AssertionError(f"no {kind} from line {line}")


def _error(line: int, column: int) -> dict:
    return {"severity": "error", "line": line, "column": column, "data": "made up here"}


AXIOMS = {
    "severity": "info",
    "line": 1,
    "column": 0,
    "data": "'Lanky.ct_condition' depends on axioms: [propext]",
}


def test_an_error_at_a_condition_reads_as_the_condition_not_met(cases) -> None:
    proof = trace_proof(cases.ct_condition)
    command = compile_proof(proof, mathlib=False)
    line = proof.leaves[1].line
    at = _span(command, "condition", line, "a < 2")
    closed, failures = read(proof, command, {"messages": [_error(*at), AXIOMS], "sorries": []})
    assert not closed
    (failure,) = failures
    assert failure.kind == "condition" and failure.line == line
    assert failure.lines == ("stored, at (a, b) needs a < 2, and this case has a >= 2.",)


def test_an_error_at_a_call_below_zero_reads_as_a_negative_argument(cases) -> None:
    proof = trace_proof(cases.ct_negative)
    command = compile_proof(proof, mathlib=False)
    at = next(
        (number, start + 4)
        for number, emitted in enumerate(command.lines, 1)
        for start, _end, origin in emitted.spans
        if origin.detail.get("negative") == "a"
    )
    measure_line = next(
        number
        for number, emitted in enumerate(command.lines, 1)
        if emitted.text.startswith("decreasing_by")
    )
    messages = [_error(*at), _error(measure_line, 0)]
    closed, failures = read(proof, command, {"messages": messages, "sorries": []})
    (failure,) = failures
    assert failure.kind == "negative"
    assert failure.lines == (
        "ct_negative.conclusion[a - 2, b + 2] is at a negative a when a = 1: split off a < 2 "
        "first.",
    )


def test_a_step_that_does_not_follow_says_what_is_left_and_the_fix(cases) -> None:
    pytest.importorskip("sympy")
    proof = trace_proof(cases.ct_wrong)
    command = compile_proof(proof, mathlib=False)
    leaf = proof.leaves[1]
    at = _span(command, "step", leaf.line)
    closed, failures = read(proof, command, {"messages": [_error(*at)], "sorries": []})
    (failure,) = failures
    assert failure.kind == "step" and failure.headline == "a step of its proof does not follow"
    split = leaf.questions[0].line
    assert failure.lines[0] == (
        f"When a >= 2 (cases_core.py:{split}), the step needs   R[a, b] == D[a, b]"
    )
    assert failure.lines[2] == (
        "  ct_wrong.conclusion[a - 2, b + 3] says   R[a - 2, b + 3] == D[a - 2, b + 3]"
    )
    assert failure.lines[3] == (
        "  pde[a - 2, b]                     says   D[a, b] + D[a - 2, b + 2] == 0"
    )
    assert failure.lines[4] == "Left over:"
    left = failure.lines[5]
    for term in ("R[a - 2, b + 3]", "- R[a - 2, b + 2]", "D[a - 2, b + 2]", "- D[a - 2, b + 3]"):
        assert term in left
    assert failure.fix == "ct_wrong.conclusion[a - 2, b + 2] makes the step follow"


def test_the_axiom_audit_is_read_positively() -> None:
    def said(text: str) -> list[dict]:
        return [{"severity": "info", "data": text}]

    assert audit(said("'Lanky.t' depends on axioms: [propext, Quot.sound]"), "Lanky.t") is None
    assert audit(said("'Lanky.t' does not depend on any axioms"), "Lanky.t") is None
    assert "sorryAx" in audit(said("'Lanky.t' depends on axioms: [sorryAx]"), "Lanky.t")
    assert "did not answer the axiom audit of Lanky.t" in audit([], "Lanky.t")
    holed = said("'Lanky.t' depends on axioms: [propext, sorryAx]")
    assert audit(holed, "Lanky.t", holes=True) is None
    assert audit(holed, "Lanky.t") is not None
    both = [
        *said("'Lanky.t' does not depend on any axioms"),
        *said("'Lanky.t.as_cited' does not depend on any axioms"),
    ]
    assert audit(both, ("Lanky.t", "Lanky.t.as_cited")) is None
    assert audit(said("'Lanky.t' does not depend on any axioms"), ("Lanky.t", "Lanky.t.as_cited"))
    decoy = said("'Decoy.Lanky.t' does not depend on any axioms")
    assert audit(decoy, "Lanky.t") is not None
    assert audit(said("'Lanky.«t»' does not depend on any axioms"), "Lanky.«t»") is None


def test_a_case_is_said_with_the_lines_of_its_ifs() -> None:
    a, b = Var("a"), Var("b")
    text = case_text([(a + b != 0, 48), (a >= 2, 50)], "/x/every_box.py")
    assert text == "When a + b != 0 and a >= 2 (every_box.py:48, 50)"


# }}}


# {{{ the native run


#: Proofs whose steps can be run as plain Python at drawn values.
NATIVE = '''\
from __future__ import annotations

from lanky import by, claim
from lanky.prelude import Fin, Fn, Int, Nat


@claim
def doubling(
    n: Nat,
    f: Fn[Fin[n + 1], Int],
    start: f[0] == 0,
    step: all(f[k + 1] == f[k] + 2 for k in Fin[n]),
) -> all(f[k] == 2 * k for k in Fin[n + 1]):
    for k in doubling.conclusion.domain:
        if k == 0:
            yield by(start)
        else:
            assert f[k] == f[k - 1] + 2, by(step[k - 1])
            yield by(doubling.conclusion[k - 1])


@claim
def doubling_wrong(
    n: Nat,
    f: Fn[Fin[n + 1], Int],
    start: f[0] == 0,
    step: all(f[k + 1] == f[k] + 2 for k in Fin[n]),
) -> all(f[k] == 2 * k for k in Fin[n + 1]):
    for k in doubling_wrong.conclusion.domain:
        if k == 0:
            yield by(start)
        else:
            assert f[k] == f[k - 1] + 3, by(step)
            yield by(doubling_wrong.conclusion[k - 1])


@claim
def capped(
    n: Nat,
    f: Fn[Fin[n + 1], Int],
    start: f[0] == 0,
    step: all(f[k + 1] == f[k] + 2 for k in Fin[n]),
) -> all(f[k] <= 3 for k in Fin[n + 1]):
    for k in capped.conclusion.domain:
        yield by(step)


@claim
def from_the_top(
    n: Nat,
    f: Fn[Fin[n + 1], Int],
    top: f[n] == 0,
    step: all(f[k] == f[k + 1] for k in Fin[n]),
) -> all(f[k] == 0 for k in Fin[n + 1]):
    for k in reversed(from_the_top.conclusion.domain):
        if k == n:
            yield by(top)
        else:
            assert f[k] == f[k + 1], by(step[k])
            yield by(from_the_top.conclusion[k + 1])


@claim
def table(n: Nat, f: Fn[Fin[n], Fin[n], Int]) -> all(
    all(f[i, j] + i * j <= f[i, j] + i for j in Fin[n]) for i in Fin[n]
):
    for i in table.conclusion.domain:
        for j in table.conclusion[i].domain:
            yield by()


@claim
def halves(n: Nat, k: Nat, h: k >= 1) -> (n + k) / k == n / k + 1:
    assert (n + k) / k == n / k + k / k == n / k + 1
    return by()
'''


@pytest.fixture(scope="module")
def native(tmp_path_factory) -> object:
    """The native cases, imported."""
    path = tmp_path_factory.mktemp("native") / "native_cases.py"
    path.write_text(NATIVE, encoding="utf-8")
    return import_path(path)


def test_the_native_run_finds_a_false_step_at_its_line_with_its_values(native) -> None:
    """The design's 3.6: a counterexample at the step's line, with the numbers there."""
    from lanky.proofs.native import native_failure

    assert native_failure(native.doubling) is None
    failure = native_failure(native.doubling_wrong)
    assert failure.kind == "false" and failure.headline == "a step of its proof is false"
    assert failure.line == _line(native, "assert f[k] == f[k - 1] + 3, by(step)")
    (said,) = failure.lines
    assert said.startswith("At k = 1, n = ")
    assert said.endswith(": the left side is 2, the right side 3.")


def test_the_native_run_checks_each_point_as_the_loop_moves_on(native) -> None:
    from lanky.proofs.native import native_failure

    failure = native_failure(native.capped)
    assert failure.kind == "false"
    assert failure.line == _line(native, "yield by(step)")
    (said,) = failure.lines
    assert said.startswith("At k = 2, n = ") and said.endswith(
        ": the conclusion there, f[k] <= 3, is false."
    )


def test_the_native_run_walks_reversed_and_nested_domains(native) -> None:
    """A reversed loop from the top down, and a nested one at each point of the outer."""
    from lanky.proofs.native import native_failure

    assert native_failure(native.from_the_top) is None
    native.from_the_top.run_proof(n=2, f=[0, 0, 0])
    failure = native_failure(native.table)
    assert failure.kind == "false"
    assert failure.line == _line(native, "            yield by()")
    (said,) = failure.lines
    assert said.startswith("At i = 1, j = 2, n = ") and said.endswith(
        ": the conclusion there, f[i, j] + i*j <= f[i, j] + i, is false."
    )


def test_the_native_run_divides_exactly(native) -> None:
    """``n / k`` of two drawn naturals is a ``Fraction`` there, so no step fails on rounding."""
    from lanky.proofs.native import native_failure

    assert native_failure(native.halves) is None


def test_a_proof_can_be_run_by_hand_at_values_of_ones_own(native) -> None:
    native.doubling.run_proof(n=2, f=[0, 2, 4])
    with pytest.raises(AssertionError) as raised:
        native.doubling_wrong.run_proof(n=2, f=[0, 2, 4])
    assert repr(raised.value.args[0]) == "by(step)"


def test_without_lean_a_false_step_fails_the_proof(native, monkeypatch) -> None:
    from lanky.proofs import prove

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    fact = prove(native.doubling_wrong, native.doubling_wrong.fact())
    account = fact.provenance["proof"]
    assert account["closed"] is False
    (failure,) = account["failures"]
    assert failure["kind"] == "false" and failure["source"] == (
        "assert f[k] == f[k - 1] + 3, by(step)"
    )


# }}}


# {{{ the ledger and the command


def _fact(status: Status, proof: dict) -> Fact:
    return Fact(
        id="theorem:m.t@3",
        kind="theorem",
        statement="n : Nat |- n + 0 == n",
        status=status,
        decided_by="lean" if status is Status.PROVED else None,
        provenance={"proof": proof, "path": "/x/m.py"},
        where="m.py:3",
        owner="t",
    )


def test_the_ledger_says_a_claim_is_proved_by_its_proof() -> None:
    proof = {"where": "m.py:5-9", "summary": "induction on a, 2 cases, 2 steps", "closed": True}
    rendered = Ledger([_fact(Status.PROVED, proof)]).render()
    assert "by its proof, m.py:5-9: induction on a, 2 cases, 2 steps" in rendered


FAILURE = {
    "kind": "condition",
    "line": 7,
    "headline": "a condition of a cited fact is not met",
    "lines": ["stored, at (a, b) needs a < 2, and this case has a >= 2."],
    "fix": "cite stored in a case where a < 2, or split that case off first",
    "source": "return stored",
    "where": "m.py:7",
}


def test_a_broken_proof_fails_the_check(capsys) -> None:
    proof = {"where": "m.py:5-9", "summary": "", "closed": False, "failures": [FAILURE]}
    assert report_written(Ledger([_fact(Status.TESTED, proof)]))
    out = capsys.readouterr().out
    assert "UNPROVED t at m.py:3: a condition of a cited fact is not met." in out
    assert "  m.py:7    return stored" in out
    assert "  Fix: cite stored in a case where a < 2, or split that case off first." in out


def test_a_broken_proof_of_a_claim_lanky_proves_alone_warns_and_fails(capsys) -> None:
    """Question 4: the row reads proved, by lanky's own proof, and the check fails."""
    proof = {"where": "m.py:5-9", "summary": "", "closed": False, "failures": [FAILURE]}
    assert report_written(Ledger([_fact(Status.PROVED, proof)]))
    out = capsys.readouterr().out
    assert (
        "WARNING t at m.py:3: your proof fails at m.py:7; lanky proved the claim without it" in out
    )


def test_a_proof_not_checked_says_why_and_fails_nothing(capsys) -> None:
    proof = {"where": "m.py:5-9", "closed": None, "reason": "Lean is not available here"}
    assert not report_written(Ledger([_fact(Status.TESTED, proof)]))
    assert "NOT CHECKED t at m.py:3: its proof, m.py:5-9, was not checked: Lean is not" in (
        capsys.readouterr().out
    )


def test_without_lean_a_proof_is_not_checked_and_the_check_passes(
    tmp_path, monkeypatch, capsys
) -> None:
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "plain.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import by, claim
            from lanky.prelude import Fn, Int, Nat


            @claim
            def sum_to(
                S: Fn[Nat, Int], base: S[0] == 0, step: all(S[k + 1] == S[k] + 1 for k in Nat),
            ) -> all(S[n] == n for n in Nat):
                for n in sum_to.conclusion.domain:
                    if n == 0:
                        yield by(base)
                    else:
                        yield by(step[n - 1], sum_to.conclusion[n - 1])
            """
        ),
        encoding="utf-8",
    )
    (fact,) = claims(check_path(path))
    assert fact.provenance["proof"]["closed"] is None
    assert fact.provenance["proof"]["reason"].startswith("Lean is not available here")
    assert lanky_main(["check", str(path)]) == 0
    assert "NOT CHECKED sum_to" in capsys.readouterr().out


def test_a_body_is_traced_after_every_run_and_draw_of_the_check(tmp_path, monkeypatch) -> None:
    import lanky.check as check_module

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    order: list[str] = []
    establish = check_module.establish

    def recording(fact, verbose=False):
        order.append(f"establish {fact.kind}")
        return establish(fact, verbose=verbose)

    monkeypatch.setattr(check_module, "establish", recording)
    path = tmp_path / "order.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import by, claim
            from lanky.prelude import Nat

            ORDER = None


            @claim
            def first(n: Nat, h: n >= 1) -> n >= 1:
                ORDER.append("traced first")
                return by(h)


            @claim
            def second(n: Nat) -> n + 0 == n:
                ...
            """
        ),
        encoding="utf-8",
    )
    import builtins

    monkeypatch.setattr(builtins, "lanky_test_order", order, raising=False)
    text = path.read_text(encoding="utf-8").replace("ORDER = None", "ORDER = lanky_test_order")
    path.write_text(text, encoding="utf-8")
    check_path(path)
    assert order[-1] == "traced first"
    assert order.count("establish theorem") == 2


# }}}


# {{{ with Lean


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


@pytest.fixture(scope="module")
def checked(tmp_path_factory) -> dict[str, Fact]:
    """The integer cases checked with core Lean, by owner."""
    _lean_or_skip()
    path = tmp_path_factory.mktemp("lean") / "cases_core.py"
    path.write_text(CASES, encoding="utf-8")
    return {fact.owner: fact for fact in claims(check_path(path))}


@pytest.mark.parametrize(
    "owner",
    [
        "ct",
        "every_box",
        "each_box",
        "sum_to",
        "stepped",
        "climb",
        "lex",
        "routine",
        "both_parts",
        "cites_later",
        "by_its_conditions",
    ],
)
def test_lean_accepts_the_written_proofs(checked, owner) -> None:
    fact = checked[owner]
    assert fact.provenance["proof"]["closed"] is True, fact.provenance["proof"]
    assert fact.status is Status.PROVED and fact.decided_by == "lean"


def test_a_proof_rests_on_the_theorems_it_cites(checked) -> None:
    assert checked["identity_at"].id in checked["cites_later"].rests_on


def test_a_proof_lean_accepts_proves_a_claim_lanky_does_not_alone(checked) -> None:
    fact = checked["every_box"]
    assert fact.provenance["tactic"] == "its written proof"
    assert fact.provenance["proof"]["summary"] == "induction on a, 3 cases, 3 steps"
    assert "theorem Lanky.every_box.claim" in fact.provenance["lean_source"]


def test_lean_finds_the_step_that_does_not_follow_and_checks_the_fix(checked) -> None:
    pytest.importorskip("sympy")
    (failure,) = checked["ct_wrong"].provenance["proof"]["failures"]
    assert failure["kind"] == "step"
    assert failure["fix"] == "ct_wrong.conclusion[a - 2, b + 2] makes the step follow (checked)"
    assert failure["source"].startswith(
        "yield by(recurrence[a - 2, b], ct_wrong.conclusion[a - 2, b + 3]"
    )


def test_lean_finds_the_call_below_zero_and_the_condition_not_met(checked) -> None:
    (negative,) = checked["ct_negative"].provenance["proof"]["failures"]
    assert negative["kind"] == "negative"
    (condition,) = checked["ct_condition"].provenance["proof"]["failures"]
    assert condition["lines"] == ["stored, at (a, b) needs a < 2, and this case has a >= 2."]


def test_a_broken_proof_of_a_claim_lanky_proves_alone_keeps_the_row_and_fails(
    checked, tmp_path, capsys
) -> None:
    fact = checked["zero_times"]
    assert fact.status is Status.PROVED and fact.provenance["tactic"] != "its written proof"
    assert fact.provenance["proof"]["closed"] is False


def test_lanky_check_exits_nonzero_on_a_broken_proof(tmp_path, capsys) -> None:
    _lean_or_skip()
    path = tmp_path / "broken.py"
    path.write_text(
        textwrap.dedent(
            """
            from __future__ import annotations

            from lanky import by, claim
            from lanky.prelude import Fn, Int, Nat


            @claim
            def zero_times(
                f: Fn[Nat, Int], h: all(f[k] == 2 * k for k in Nat if k >= 1)
            ) -> f[0] * 0 == 0:
                return by(h[0])
            """
        ),
        encoding="utf-8",
    )
    assert lanky_main(["check", str(path)]) == 1
    out = capsys.readouterr().out
    lines = path.read_text(encoding="utf-8").splitlines()
    claim = next(number for number, line in enumerate(lines, 1) if line == "@claim")
    body = next(number for number, line in enumerate(lines, 1) if "return by(h[0])" in line)
    assert f"WARNING zero_times at broken.py:{claim}: your proof fails at broken.py:{body};" in out
    assert "  h[0] needs 0 >= 1, and this case has nothing that shows it." in out


def test_the_demonstration_is_proved_by_its_written_proof(mathlib_project, monkeypatch) -> None:
    """lanky #140's ``every_box``, which read assumed, proved by the design's body."""
    if mathlib_project is None:
        if os.environ.get("LANKY_LEAN_MATHLIB_TEST_REQUIRED"):
            pytest.fail("LANKY_LEAN_MATHLIB_TEST_REQUIRED is set, but there is no Mathlib")
        pytest.skip("LANKY_LEAN_MATHLIB names no Lake project with Mathlib")
    _lean_or_skip()
    monkeypatch.setenv("LANKY_LEAN_MATHLIB", mathlib_project)
    example = Path(__file__).resolve().parent.parent / "examples" / "every_box.py"
    (fact,) = claims(check_path(example))
    assert fact.status is Status.PROVED
    assert fact.provenance["proof"]["closed"] is True
    assert fact.provenance["proof"]["summary"] == "induction on a, 3 cases, 3 steps"


# }}}
