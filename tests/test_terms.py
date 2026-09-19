"""Terms: the scope, the operators that build propositions, and binder tracing."""

from __future__ import annotations

import random

import pytest

from lanky.prelude import Fin, Fn, Nat
from lanky.terms import (
    Comparison,
    Forall,
    Scope,
    Sum,
    SymbolicBoolError,
    Undecided,
    Var,
    abs_,
    binders,
    evaluate,
    evaluate_annotations,
    exists,
    forall,
    render,
    structurally_equal,
    sum_,
)
from lanky.testing import sort_sampler


def test_scope_invents_variables() -> None:
    scope = Scope()
    assert isinstance(scope["n"], Var)
    assert scope["n"].name == "n"
    # the same name is the same variable on the next lookup
    assert scope["n"] is scope["n"]


def test_scope_leaves_dunders_alone() -> None:
    with pytest.raises(KeyError):
        Scope()["__builtins__"]


def test_comparison_is_a_term_not_a_bool() -> None:
    n = Var("n")
    claim = n + 1 == 2 * n
    assert isinstance(claim, Comparison)
    assert render(claim) == "n + 1 == 2*n"
    assert evaluate(claim, {"n": 1}) is True
    assert evaluate(claim, {"n": 3}) is False


def test_truth_value_of_a_proposition_is_refused() -> None:
    with pytest.raises(SymbolicBoolError):
        bool(Var("n") == 0)


def test_symbolic_iteration_binds_one_variable() -> None:
    n = Var("n")
    bound = binders(i for i in Fin[n])
    assert len(bound) == 1
    var, domain = bound[0]
    assert var.name == "i"
    assert domain == Fin[n]


def test_sum_is_a_term_over_a_symbolic_domain() -> None:
    n = Var("n")
    total = sum_(i for i in Fin[n + 1])
    assert isinstance(total, Sum)
    assert render(total) == "sum(i for i in Fin(n + 1))"
    assert evaluate(total, {"n": 4}) == 10


def test_sum_is_a_number_over_a_concrete_domain() -> None:
    assert sum_(i for i in Fin[5]) == 10
    assert forall(i >= 0 for i in Fin[5]) is True


def test_generator_filter_becomes_a_guard() -> None:
    n = Var("n")
    claim = forall(a <= b for a in Fin[n] for b in Fin[n] if a <= b)
    assert isinstance(claim, Forall)
    assert [var.name for var, _ in claim.binders] == ["a", "b"]
    assert render(claim.guard) == "a <= b"
    assert evaluate(claim, {"n": 3}) is True


def test_evaluate_annotations_reads_a_theorem_signature() -> None:
    def scan_monotone(
        n: Nat,
        off: Fn[Fin[n + 1], Nat],
        h0: off(0) == 0,
        hs: all(off(r + 1) >= off(r) for r in Fin[n]),
    ) -> all(off(a) <= off(b) for a in Fin[n + 1] for b in Fin[n + 1] if a <= b):
        """A signature is a statement; the body is never run."""

    annotations = evaluate_annotations(scan_monotone)
    assert list(annotations) == ["n", "off", "h0", "hs", "return"]
    assert annotations["n"] is Nat
    assert annotations["off"] == Fn[Fin[Var("n") + 1], Nat]
    assert render(annotations["h0"]) == "off(0) == 0"
    assert render(annotations["hs"]) == "forall r in Fin(n). off(r + 1) >= off(r)"
    assert isinstance(annotations["return"], Forall)


def test_evaluate_annotations_handles_evaluated_annotations() -> None:
    # Without "from __future__ import annotations" the annotation is an object
    # already; both forms have to work.
    #
    # Two details make this fixture an honest test of the eager path.
    # ``dont_inherit=True``, because compile() otherwise inherits the future
    # statements of *this* module, which has "from __future__ import
    # annotations" at the top, and the fixture would quietly test the string
    # path a second time. And a binding for ``n`` in the namespace, because an
    # eager annotation is evaluated at definition time, where a name lanky
    # would have invented does not exist yet: giving it a Var is what the
    # defaulting Scope does for the string path, done by hand.
    source = "def f(n: Nat) -> n >= 0:\n    pass\n"
    namespace: dict = {"Nat": Nat, "n": Var("n")}
    exec(compile(source, "<eager>", "exec", dont_inherit=True), namespace)
    function = namespace["f"]
    # the annotations really are objects here, not the strings the other path
    # hands over, which is the whole point of the fixture
    assert not isinstance(function.__annotations__["return"], str)
    assert isinstance(function.__annotations__["return"], Comparison)
    annotations = evaluate_annotations(function)
    assert annotations["n"] is Nat
    assert render(annotations["return"]) == "n >= 0"


def test_any_and_abs_are_replaced_too() -> None:
    n = Var("n")
    annotations = evaluate_annotations(_any_and_abs)
    goal = annotations["return"]
    assert render(goal) == "exists i in Fin(n). abs(i - n) == 1"
    assert evaluate(goal, {"n": 2}) is True
    assert evaluate(goal, {"n": 0}) is False
    assert abs_(-3) == 3
    assert render(abs_(n)) == "abs(n)"


def _any_and_abs(n: Nat) -> any(abs(i - n) == 1 for i in Fin[n]):
    """A signature using the two remaining replaced builtins."""


def test_a_quantifier_over_a_sort_is_sampled_not_enumerated() -> None:
    claim = forall(x >= 0 for x in Nat)
    assert render(claim) == "forall x in Nat. x >= 0"
    with pytest.raises(ValueError, match="cannot enumerate"):
        evaluate(claim, {})
    assert evaluate(claim, {}, sort_sampler(random.Random(0), {})) is True


def test_structural_equality_ignores_the_proposition_operators() -> None:
    n = Var("n")
    assert structurally_equal(2 * n, 2 * n)
    assert not structurally_equal(2 * n, 3 * n)


# {{{ how a guard may be written


def test_a_generator_if_clause_becomes_the_guard() -> None:
    """The one place Python may ask for the truth value of a proposition."""
    n = Var("n")
    claim = forall(a <= b for a in Fin[n] for b in Fin[n] if a <= b)
    assert render(claim) == "forall a in Fin(n), b in Fin(n) where a <= b. a <= b"


def test_the_connectives_build_a_compound_guard() -> None:
    n = Var("n")
    both = forall(a <= b for a in Fin[n] for b in Fin[n] if (a <= b) & (b < n))
    assert render(both) == "forall a in Fin(n), b in Fin(n) where a <= b and b < n. a <= b"
    either = forall(a <= b for a in Fin[n] for b in Fin[n] if (a <= b) | (b < n))
    assert render(either) == "forall a in Fin(n), b in Fin(n) where a <= b or b < n. a <= b"
    negated = forall(a <= b for a in Fin[n] for b in Fin[n] if ~(a <= b))
    assert render(negated) == "forall a in Fin(n), b in Fin(n) where not (a <= b). a <= b"


def test_python_or_between_propositions_is_refused() -> None:
    """``or`` short-circuits on the answer lanky gives while capturing a guard.

    Answering the first test truthfully is what records it, and that skips the
    second operand entirely, so the disjunction would silently narrow to its
    left half. There is no answer that both records the guard and keeps the
    right operand, so the only honest thing is to refuse.
    """
    n = Var("n")
    with pytest.raises(SymbolicBoolError, match="short-circuits"):
        forall(a <= b for a in Fin[n] for b in Fin[n] if a <= b or b < n)


def test_python_and_or_as_a_value_is_refused() -> None:
    """In the body of a generator, ``and`` would drop its left operand."""
    n = Var("n")
    p = Var("p")
    q = Var("q")
    with pytest.raises(SymbolicBoolError, match="short-circuits"):
        forall((p(i) < 1) and (q(i) < 1) for i in Fin[n])
    with pytest.raises(SymbolicBoolError, match="short-circuits"):
        forall((p(i) < 1) or (q(i) < 1) for i in Fin[n])


def test_python_not_in_a_guard_is_refused() -> None:
    """``not`` inverts the answer that captures the guard, emptying the range."""
    n = Var("n")
    with pytest.raises(SymbolicBoolError, match="``~"):
        forall(a <= b for a in Fin[n] for b in Fin[n] if not (a <= b))


def test_an_if_statement_inside_a_traced_call_is_refused() -> None:
    """A guard recorded from another frame would belong to the wrong generator."""
    n = Var("n")

    def helper(x):
        if x < 3:  # the mistake: a proposition is not a bool
            return 1
        return 0

    with pytest.raises(SymbolicBoolError, match="outside the ``if`` clause"):
        forall(helper(i) for i in Fin[n])


def test_python_and_between_propositions_still_works() -> None:
    """Documented, because it survives by an accident of CPython's compiler.

    A conjunction in a comprehension filter compiles to two successive tests,
    exactly as two ``if`` clauses do, so both halves are captured and the guard
    is the conjunction that was written. It cannot be told apart from ``if a if
    b`` in the bytecode, so it is not refused; ``&`` is still what to write.
    """
    n = Var("n")
    claim = forall(a <= b for a in Fin[n] for b in Fin[n] if a <= b and b < n)
    assert render(claim) == "forall a in Fin(n), b in Fin(n) where a <= b and b < n. a <= b"


def test_a_concrete_comprehension_is_left_alone() -> None:
    """Nothing symbolic, nothing to refuse: plain Python keeps working."""
    assert forall(x > 0 for x in [1, 2, 3] if x > 0 and x < 3) is True
    assert forall(x > 0 for x in [1, 2, 3] if x > 5 or x < 3) is True


def test_a_proposition_is_not_a_bool_outside_tracing() -> None:
    n = Var("n")
    with pytest.raises(SymbolicBoolError, match="undefined"):
        bool(n < 1)


# }}}


def test_a_nested_quantifier_keeps_its_binder_names() -> None:
    """A target a nested comprehension closes over is a cell, not a local.

    ``co_varnames`` has only ``.0`` in it for the outer generator here, so the
    names come off the bytecode instead; without that the statement prints
    ``_i0`` and the reader has to guess.
    """
    n = Var("n")
    f = Var("f")
    claim = forall(forall(f(i)(j) >= 0 for j in Fin[n]) for i in Fin[n])
    assert render(claim) == "forall i in Fin(n). forall j in Fin(n). f(i)(j) >= 0"


def test_two_for_clauses_keep_both_names() -> None:
    """CPython fuses the second store with a load; the target is still there."""
    n = Var("n")
    p = Var("p")
    claim = forall(p(a) <= p(b) for a in Fin[n] for b in Fin[n] if a <= b)
    assert render(claim) == "forall a in Fin(n), b in Fin(n) where a <= b. p(a) <= p(b)"


def test_a_sampled_existential_declines_rather_than_answering_false() -> None:
    """``any`` over a sampled sort has no ``False`` to give.

    The draws are four points of an infinite domain, so finding no witness is
    not finding that there is none. The evaluator says so by raising rather
    than by answering, and the property tester drops the draw.
    """
    claim = exists(x == 100 for x in Nat)
    assert render(claim) == "exists x in Nat. x == 100"
    with pytest.raises(Undecided, match="undecided"):
        evaluate(claim, {}, sort_sampler(random.Random(0), {}))
    # a witness among the draws is still an answer
    assert evaluate(exists(x == 0 for x in Nat), {}, sort_sampler(random.Random(0), {}))


def test_an_existential_over_an_index_type_answers_both_ways() -> None:
    """``Fin`` is enumerated, so nothing is held back over it."""
    assert evaluate(exists(i == 2 for i in Fin[4]), {}) is True
    assert evaluate(exists(i == 9 for i in Fin[4]), {}) is False


def test_a_sampled_universal_is_still_refutable() -> None:
    """A failing draw of a ``forall`` is a real counterexample, sampled or not."""
    assert evaluate(forall(x < 3 for x in Nat), {}, sort_sampler(random.Random(1), {})) is False
    assert evaluate(forall(x >= 0 for x in Nat), {}, sort_sampler(random.Random(1), {})) is True


def test_a_binderless_quantifier_renders_as_a_sequent() -> None:
    """A closed statement with hypotheses and no variables is not "forall nothing"."""
    body = Var("p") > 0
    guard = Var("p") > 1
    assert render(Forall((), body, guard)) == "p > 1 |- p > 0"
    assert render(Forall((), body, None)) == "p > 0"
