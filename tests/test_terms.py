"""Terms: the scope, the operators that build propositions, and binder tracing."""

from __future__ import annotations

import random
from contextlib import closing

import pytest

from lanky.prelude import Fin, Fn, Nat, Refined
from lanky.terms import (
    Comparison,
    Exists,
    Forall,
    LankyEvaluationMapper,
    Polarity,
    Scope,
    Sum,
    SymbolicBoolError,
    Undecided,
    Var,
    abs_,
    binder_assignments,
    binders,
    evaluate,
    evaluate_annotations,
    exists,
    forall,
    free_variables,
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


def test_a_symbolic_guard_over_a_concrete_domain_is_refused() -> None:
    """A concrete domain is walked, and a symbolic guard over it used to be dropped (#24).

    Capturing the guard answers ``True``, so every point was yielded and the
    builtin answered over all of them: ``sum(1 for i in Fin[3] if n > 100)``
    was ``3``, and ``all`` and ``any`` with a concrete body lost the guard
    the same way. Each is refused now, naming a way to keep the condition.
    """
    f, n = Var("f"), Var("n")
    with pytest.raises(SymbolicBoolError, match="give the domain a symbolic bound"):
        sum_(1 for i in Fin[3] if n > 100)
    with pytest.raises(SymbolicBoolError, match=r"as in ~\(condition\) \| all\(body for"):
        forall(i >= 0 for i in Fin[3] if n > 100)
    with pytest.raises(SymbolicBoolError, match=r"as in \(condition\) & any\(body for"):
        exists(i >= 0 for i in Fin[3] if n > 100)
    # a sum of symbolic values is added up without asking any of them for a
    # truth value, so nothing else noticed the guard go
    with pytest.raises(SymbolicBoolError, match="its guard 'n > 1' is symbolic"):
        sum_(f(i) for i in Fin[2] if n > 1)
    # a guard that mentions the point is named as each point recorded it
    with pytest.raises(SymbolicBoolError, match="its guard 'n > 0 and n > 1'"):
        sum_(1 for i in Fin[2] if i < n)
    # a guard written with `not` held at no point, and the message says why
    with pytest.raises(SymbolicBoolError, match="Python's `not`"):
        forall(i >= 0 for i in Fin[3] if not (n > 100))


def test_the_ways_the_refusal_names_keep_the_condition() -> None:
    """A concrete guard is Python's, and the two spellings the refusal suggests work.

    A condition that does not mention the loop variable stands outside the
    quantifier, and a domain with a symbolic bound keeps its guard in the term.
    """
    m, n = Var("m"), Var("n")
    assert sum_(1 for i in Fin[3] if i > 0) == 2
    assert forall(i >= 1 for i in Fin[3] if i > 0) is True
    outside = ~(n > 100) | forall(i > 0 for i in Fin[3])
    assert evaluate(outside, {"n": 3}) is True
    assert evaluate(outside, {"n": 101}) is False
    kept = sum_(1 for i in Fin[m] if n > 100)
    assert render(kept) == "sum(1 for i in Fin(m) if n > 100)"
    assert evaluate(kept, {"m": 3, "n": 3}) == 0
    assert evaluate(kept, {"m": 3, "n": 101}) == 3


# }}}


# {{{ three-valued connectives


def _undecided() -> bool:
    raise Undecided("open")


def test_conjoin_and_disjoin_are_kleenes_strong_connectives() -> None:
    """The settling answer wins wherever it stands, and the walk stops there.

    A false operand settles a conjunction and a true one a disjunction,
    whatever an operand before it could not answer; with nothing to settle
    it, the first open answer is raised again. An operand after the settling
    one is never asked.
    """
    from lanky.terms import conjoin, disjoin

    asked: list[bool] = []

    def ask(value: bool):
        def operand() -> bool:
            asked.append(value)
            return value

        return operand

    assert conjoin([_undecided, ask(False), ask(False)]) is False
    assert asked == [False]
    assert disjoin([_undecided, ask(True), ask(True)]) is True
    assert conjoin([ask(True), ask(True)]) is True
    assert disjoin([ask(False), ask(False)]) is False
    with pytest.raises(Undecided, match="open"):
        conjoin([_undecided, ask(True)])
    with pytest.raises(Undecided, match="open"):
        disjoin([ask(False), _undecided])
    with pytest.raises(ZeroDivisionError):
        conjoin([lambda: 1 // 0 > 0, _undecided, ask(True)])
    assert conjoin([]) is True
    assert disjoin([]) is False


def test_a_connective_goes_on_past_an_undecided_operand() -> None:
    """``p | q`` and ``q | p`` agree, and so do ``p & q`` and ``q & p`` (#25).

    ``~all(k < 100 for k in Nat)`` is undecided: the universal held at every
    draw, and under ``~`` that would be used as a certainty. A disjunction
    with a true operand is true, and a conjunction with a false one false,
    whatever that operand is, and the walk used to stop at the undecided
    operand and give the answer up when it came first.
    """
    k, n = Var("k"), Var("n")
    undecided = ~Forall(((k, Nat),), k < 100)
    for claim in (undecided | (n >= 0), (n >= 0) | undecided):
        assert evaluate(claim, {"n": 3}, _sampler()) is True
    for claim in (undecided & (n < 0), (n < 0) & undecided):
        assert evaluate(claim, {"n": 3}, _sampler()) is False
    for claim in (
        undecided | (n < 0),
        (n < 0) | undecided,
        undecided & (n >= 0),
        (n >= 0) & undecided,
    ):
        with pytest.raises(Undecided, match="assumes or denies it"):
            evaluate(claim, {"n": 3}, _sampler())
    # an operand after an undecided one is asked now, and one that is not a
    # proposition is refused, where the undecided operand used to hide it
    with pytest.raises(TypeError, match="not a proposition"):
        evaluate(undecided | (n + 1), {"n": 3}, _sampler())


def test_a_division_by_zero_is_an_operand_with_no_answer() -> None:
    """Python raises where Lean's division is total, and another operand can still settle it.

    ``(10 // n > 1) | (n == 0)`` is true at ``n = 0`` under every reading of
    the division, and it raised ``ZeroDivisionError``; a false operand before
    the division still keeps it from being evaluated at all.
    """
    n = Var("n")
    assert evaluate((10 // n > 1) | (n == 0), {"n": 0}) is True
    assert evaluate((10 // n > 1) & (n != 0), {"n": 0}) is False
    assert evaluate((n > 0) & (10 // n > 1), {"n": 0}) is False
    with pytest.raises(ZeroDivisionError):
        evaluate((10 // n > 1) | (n > 0), {"n": 0})


def test_a_refinement_is_one_conjunction_read_three_valued() -> None:
    """``T & p & q`` rejects a point ``q`` rejects, whatever ``p`` could not answer there.

    As a parameter's sort and as a binder's domain alike: at ``i = 0`` the
    first proposition divides by zero, and the second rejects the point.
    """
    i, n = Var("i"), Var("n")
    assert (Nat & (10 // n > 1) & (n > 5)).holds({"n": 0}) is False
    claim = Forall(((i, Fin[3] & (10 // i > 1) & (i > 5)),), i < 0)
    assert evaluate(claim, {}) is True
    with pytest.raises(ZeroDivisionError):
        (Nat & (10 // n > 1) & (n < 5)).holds({"n": 0})


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


def test_a_short_circuiting_quantifier_restores_the_binder_it_shadowed() -> None:
    """A witness ends the walk early, and the binding has to go back anyway.

    ``all(any(i == 0 for i in Fin[1]) & (i < 2) for i in Fin[3])`` is false at
    the outer ``i = 2``. The inner existential finds its witness at ``i = 0``
    and returns there, so the restoration that used to sit after the loop was
    never reached and the outer ``i < 2`` was answered at the inner ``0``: a
    false statement passed.
    """
    i = Var("i")
    j = Var("j")
    shadowing = Forall(((i, Fin[3]),), Exists(((i, Fin[1]),), i == 0) & (i < 2))
    assert render(shadowing) == "forall i in Fin(3). (exists i in Fin(1). i == 0) and i < 2"
    assert evaluate(shadowing, {}) is False
    # the same shape with nothing shadowed is unchanged
    nested = Forall(((i, Fin[3]),), Exists(((j, Fin[3]),), j == i) & (i < 3))
    assert evaluate(nested, {}) is True
    assert evaluate(Forall(((i, Fin[3]),), Exists(((j, Fin[3]),), j == i) & (i < 2)), {}) is False


def test_an_abandoned_walk_restores_the_binding_it_replaced() -> None:
    """The restoration is in a ``finally``, so leaving the walk early is safe."""
    context = {"i": 7}
    with closing(binder_assignments(((Var("i"), Fin[3]),), context)) as walk:
        for _ in walk:
            break
    assert context["i"] == 7
    fresh: dict[str, object] = {}
    with closing(binder_assignments(((Var("k"), Fin[3]),), fresh)) as walk:
        for _ in walk:
            break
    assert "k" not in fresh


def test_a_binderless_quantifier_renders_as_a_sequent() -> None:
    """A closed statement with hypotheses and no variables is not "forall nothing"."""
    body = Var("p") > 0
    guard = Var("p") > 1
    assert render(Forall((), body, guard)) == "p > 1 |- p > 0"
    assert render(Forall((), body, None)) == "p > 0"


# {{{ a quantifier over a refined domain


def test_a_refined_domain_is_its_base_filtered_by_the_refinement() -> None:
    """``Fin[4] & (k > 0)`` is ``{1, 2, 3}``, and both quantifiers see exactly that.

    The evaluator used to read the domain as if the refinement were not there:
    it had no ``points``, so it was handed to the sampler (and without one it
    could not be walked at all), and the sampler drew from ``Fin[4]`` unfiltered.
    """
    k = Var("k")
    domain = Fin[4] & (k > 0)
    assert evaluate(Forall(((k, domain),), k > 0), {}) is True
    assert evaluate(Exists(((k, domain),), k == 0), {}) is False
    assert evaluate(Exists(((k, domain),), k == 3), {}) is True
    assert evaluate(Sum(((k, domain),), k), {}) == 6
    # a refinement of a refinement keeps both, the inner one read first
    nested = Refined(Refined(Fin[6], (k > 0,)), (6 // k > 1,))
    assert evaluate(Sum(((k, nested),), k), {}) == 1 + 2 + 3
    # the refinement may name other variables in scope, read where it is bound
    n = Var("n")
    assert evaluate(Sum(((k, Fin[5] & (k < n)),), k), {"n": 3}) == 0 + 1 + 2


def test_a_refined_domain_is_enumerated_when_its_base_is() -> None:
    k, n = Var("k"), Var("n")
    assert LankyEvaluationMapper.is_exhaustive(Fin[n] & (k > 0))
    assert LankyEvaluationMapper.is_exhaustive(Refined(Fin[n] & (k > 0), (k < 5,)))
    assert not LankyEvaluationMapper.is_exhaustive(Nat & (k > 0))


def test_a_sampled_refined_domain_keeps_only_the_draws_it_admits() -> None:
    """``Nat & (k > 0)`` is sampled from ``Nat`` and filtered, never read as ``Nat``."""
    k = Var("k")
    claim = Forall(((k, Nat & (k > 0)),), k > 0)
    for seed in range(20):
        assert evaluate(claim, {}, sort_sampler(random.Random(seed), {})) is True
    seen: list[int] = []
    context: dict[str, object] = {}
    walk = binder_assignments(((k, Nat & (k > 0)),), context, sort_sampler(random.Random(0), {}))
    with closing(walk):
        for _ in walk:
            seen.append(context["k"])
    assert seen
    assert all(point > 0 for point in seen)


def test_a_forall_no_draw_of_a_refinement_reaches_is_undecided() -> None:
    """A ``forall`` that looked at no point has not been shown to hold anywhere.

    ``Nat & (k == 1000)`` rejects every draw, so answering ``True`` would be a
    vacuous pass. Over an enumerated base an empty domain is really empty, and
    the vacuous answer is the right one.
    """
    k = Var("k")
    sampler = sort_sampler(random.Random(0), {})
    with pytest.raises(Undecided, match="satisfied its refinement"):
        evaluate(Forall(((k, Nat & (k == 1000)),), k == 1000), {}, sampler)
    with pytest.raises(Undecided, match="undecided"):
        evaluate(Exists(((k, Nat & (k == 1000)),), k == 1000), {}, sampler)
    assert evaluate(Forall(((k, Fin[3] & (k > 5)),), k == 1000), {}) is True
    assert evaluate(Exists(((k, Fin[3] & (k > 5)),), k == k), {}) is False


def test_a_refinement_that_cannot_be_answered_raises_as_a_guard_does() -> None:
    """``Fin[3] & (6 // k > 1)`` has no answer at ``k = 0``, and says so."""
    k = Var("k")
    with pytest.raises(ZeroDivisionError):
        evaluate(Forall(((k, Fin[3] & (6 // k > 1)),), k >= 0), {})
    with pytest.raises(TypeError, match="not a truth value"):
        evaluate(Forall(((k, Fin[3] & (k + 1)),), k >= 0), {})


def test_a_filtered_walk_restores_the_binding_it_replaced() -> None:
    """A rejected point is bound to be judged; the old binding still comes back."""
    k = Var("k")
    context = {"k": 7}
    with closing(binder_assignments(((k, Fin[3] & (k > 5)),), context)) as walk:
        assert list(walk) == []
    assert context["k"] == 7
    shadowing = Forall(((k, Fin[3]),), Exists(((k, Fin[3] & (k > 1)),), k == 2) & (k < 2))
    assert evaluate(shadowing, {}) is False


def test_free_variables_see_inside_a_refined_binder_domain() -> None:
    """``Fin[n] & (k < m)`` for the binder ``k`` mentions ``n`` and ``m``.

    The domain was read through ``bound``, which a refinement does not have, so
    neither name was found.
    """
    k, n, m = Var("k"), Var("n"), Var("m")
    assert free_variables(Forall(((k, Fin[n] & (k < m)),), k >= 0)) == {"n", "m"}
    assert free_variables(Exists(((k, Nat & (k > 0)),), k == 1)) == frozenset()


def test_a_fraction_literal_is_a_constant() -> None:
    """A term built node by node may carry a ``Fraction``, and it evaluates as one.

    pymbolic's operators refuse a ``Fraction`` operand, so only a plugin puts
    one into a term, and pymbolic's evaluator refused it as an invalid foreign
    object: the tester could not run such a statement at all, where it should
    refute ``1 - Fraction(2, 1) ** n >= 0`` at ``n = 1``.
    """
    from fractions import Fraction

    import pymbolic.primitives as prim

    from lanky.testing import check

    n = Var("n")
    below = prim.Comparison(
        prim.Sum((1, prim.Product((-1, prim.Power(Fraction(2, 1), n))))), ">=", 0
    )
    assert evaluate(below, {"n": 0}) is True
    assert evaluate(below, {"n": 1}) is False
    assert evaluate(prim.Sum((n, Fraction(1, 2))), {"n": 1}) == Fraction(3, 2)
    report = check([("n", Nat)], [], below)
    assert not report.ok
    assert report.counterexample["n"] >= 1


def test_free_variables_read_a_later_domain_with_the_earlier_binders_bound() -> None:
    """``Fin[i]`` after ``i in Fin[n]`` is the binder ``i``, and not a free name.

    The generator ``all(j < n for i in Fin[n] for j in Fin[i])`` evaluates
    ``Fin[i]`` once the outer ``i`` is bound. The domains used to be collected
    without subtracting the binders before them, so ``i`` came back free. A
    binder's own domain is read before it exists, and keeps its free name.
    """
    i, j, k, n, m = Var("i"), Var("j"), Var("k"), Var("n"), Var("m")
    assert free_variables(Forall(((i, Fin[n]), (j, Fin[i])), j < n)) == {"n"}
    assert free_variables(Sum(((i, Fin[n]), (j, Fin[i + m])), j)) == {"n", "m"}
    # a refinement of a later binder may name an earlier one
    assert free_variables(Exists(((i, Fin[n]), (j, Nat & (j < i))), j == 0)) == {"n"}
    # a binder's own domain is evaluated before the binder is bound
    assert free_variables(Forall(((i, Fin[i]),), i > 0)) == {"i"}
    assert free_variables(Forall(((i, Fin[n]), (j, Fin[j])), j < n)) == {"n", "j"}
    # a binder that shadows an earlier one reads its domain with the earlier one
    # bound, ``all(i < n for i in Fin[n] for i in Fin[i])``, whether the two sit
    # in one quantifier or in nested ones
    assert free_variables(Forall(((i, Fin[n]), (i, Fin[i])), i < n)) == {"n"}
    assert free_variables(Exists(((i, Fin[n]),), Forall(((i, Fin[i]),), i < n))) == {"n"}
    assert free_variables(Forall(((i, Fin[i]), (i, Fin[i])), i < n)) == {"i", "n"}
    # a later domain inside a nested quantifier sees the outer binders as well
    inner = Exists(((j, Fin[i]), (k, Fin[j + m])), k < n)
    assert free_variables(Forall(((i, Fin[n]),), inner)) == {"n", "m"}


# }}}


# {{{ where a sampled quantifier stands


def _sampler(seed: int = 0):
    """A sampler of the tester's own, drawing naturals up to five."""
    return sort_sampler(random.Random(seed), {})


def test_a_sampled_forall_is_confirmed_only_where_it_is_asserted() -> None:
    """``all(k < 100 for k in Nat)`` holds at every draw, and is false.

    Standing where the statement asserts it, that is evidence, the ``TESTED``
    kind; standing anywhere else the ``True`` would be used as a certainty,
    and evaluation declines. A draw that breaks it is a counterexample
    wherever it stands, so ``k < 3`` is ``False`` in every position.
    """
    k = Var("k")
    held = Forall(((k, Nat),), k < 100)
    broken = Forall(((k, Nat),), k < 3)
    assert evaluate(held, {}, _sampler()) is True
    assert evaluate(held, {}, _sampler(), Polarity.POSITIVE) is True
    for polarity in (Polarity.NEGATIVE, Polarity.MIXED):
        with pytest.raises(Undecided, match="evidence that it holds and not proof"):
            evaluate(held, {}, _sampler(), polarity)
        assert evaluate(broken, {}, _sampler(), polarity) is False
    # under a negation, and on either side of a comparison between propositions
    with pytest.raises(Undecided, match="assumes or denies it"):
        evaluate(~held, {}, _sampler())
    with pytest.raises(Undecided, match="used as a value"):
        evaluate(held == True, {}, _sampler())  # noqa: E712 - a proposition, not a bool
    assert evaluate(~broken, {}, _sampler()) is True
    # two negations put it back where it is asserted
    assert evaluate(~~held, {}, _sampler()) is True
    assert evaluate(~~broken, {}, _sampler()) is False


def test_a_universal_reads_its_guard_and_refinements_as_its_antecedent() -> None:
    """A universal's guard and refinements stand opposite to it; an existential's with it.

    ``all(i < 0 for i in Fin[3] if all(k < 100 for k in Nat))`` is true,
    because the guard is false, and it used to be refuted at ``i = 0`` on the
    strength of four draws of ``k``. As a refinement of the binder domain the
    same guard reads the same way. An existential's guard is a conjunct of
    what it claims, so where the existential is asserted a pass is evidence
    for it.
    """
    i, k = Var("i"), Var("k")
    held = Forall(((k, Nat),), k < 100)
    guarded = Forall(((i, Fin[3]),), i < 0, held)
    refined = Forall(((i, Fin[3] & held),), i < 0)
    for claim in (guarded, refined):
        with pytest.raises(Undecided, match="assumes or denies it"):
            evaluate(claim, {}, _sampler())
    assert evaluate(Exists(((i, Fin[3]),), i == 0, held), {}, _sampler()) is True
    assert evaluate(Exists(((i, Fin[3] & held),), i == 0), {}, _sampler()) is True
    # a guard a draw refutes is false for certain, and the universal is vacuous
    broken = Forall(((k, Nat),), k < 3)
    assert evaluate(Forall(((i, Fin[3]),), i < 0, broken), {}, _sampler()) is True


def test_a_sum_over_a_sampled_domain_is_undecided() -> None:
    """Four draws of ``Nat`` are not ``Nat``, and their sum is not the sum.

    A sampled universal inside a sum is used as a value, so it declines too,
    and a sum over an enumerated domain is still added up.
    """
    i, k = Var("i"), Var("k")
    with pytest.raises(Undecided, match="sum over draws is not the sum"):
        evaluate(Sum(((k, Nat),), 1), {}, _sampler())
    with pytest.raises(Undecided, match="sum over draws is not the sum"):
        evaluate(Sum(((i, Fin[3]), (k, Nat)), k), {}, _sampler())
    with pytest.raises(Undecided, match="used as a value"):
        evaluate(Sum(((i, Fin[3]),), 1, Forall(((k, Nat),), k < 100)), {}, _sampler())
    assert evaluate(Sum(((i, Fin[3]),), 1, Forall(((k, Nat),), k < 3)), {}, _sampler()) == 0
    assert evaluate(Sum(((i, Fin[4]),), i), {}, _sampler()) == 6


def test_a_guard_that_rejects_every_draw_leaves_a_universal_undecided() -> None:
    """``all(k < 0 for k in Nat if k > 100)`` held at no draw, because none passed the guard.

    It used to answer ``True``, a vacuous pass over draws that says nothing
    about the guarded domain; the refinement spelling of the same statement
    was already declined. Over an enumerated domain the guarded domain really
    is empty, and the vacuous ``True`` stands.
    """
    k, n = Var("k"), Var("n")
    with pytest.raises(Undecided, match="no draw of Nat passed the guard k > 100"):
        evaluate(Forall(((k, Nat),), k < 0, k > 100), {}, _sampler())
    with pytest.raises(Undecided, match="satisfied its refinement"):
        evaluate(Forall(((k, Nat & (k > 100)),), k < 0), {}, _sampler())
    assert evaluate(Forall(((k, Fin[n]),), k < 0, k > 100), {"n": 5}, _sampler()) is True


def test_a_walk_that_never_draws_is_exhaustive() -> None:
    """Over ``i in Fin[n], k in Nat`` at ``n = 0`` nothing is drawn, and the answer is exact.

    The first binder has no point, so the domain is empty whatever ``Nat``
    would have given: the universal is vacuously true, the existential false,
    and the sum zero. A walk that drew from ``Nat`` is still the sampled kind.
    """
    i, k, n = Var("i"), Var("k"), Var("n")
    binders_ = ((i, Fin[n]), (k, Nat & (k > 100)))
    assert evaluate(Forall(binders_, k < 0), {"n": 0}, _sampler()) is True
    assert evaluate(~Forall(((i, Fin[n]), (k, Nat)), k < 100), {"n": 0}, _sampler()) is False
    assert evaluate(Exists(((i, Fin[n]), (k, Nat)), k >= 0), {"n": 0}, _sampler()) is False
    assert evaluate(Sum(((i, Fin[n]), (k, Nat)), k), {"n": 0}, _sampler()) == 0
    with pytest.raises(Undecided, match="satisfied its refinement"):
        evaluate(Forall(binders_, k < 0), {"n": 2}, _sampler())
    with pytest.raises(Undecided, match="no witness"):
        evaluate(Exists(((i, Fin[n]), (k, Nat)), k > 100), {"n": 2}, _sampler())


def _atoms(inner: bool) -> list:
    """Propositions whose truth is known, paired with it, as functions of the point.

    The sampled ones are the point: their draws say something else, or
    nothing. ``all(k < 100 for k in Nat)`` is false and holds at every draw,
    ``all(k >= 0 for k in Nat)`` is true and holds at every draw, ``all(k < 3
    for k in Nat)`` is false and usually broken, ``any(k > 1000 for k in
    Nat)`` is true and never witnessed, and a guard above every draw leaves a
    false universal with no point. ``inner`` adds the ones that mention the
    binder ``i`` of an enclosing quantifier.
    """
    i, k, n = Var("i"), Var("k"), Var("n")
    atoms = [
        (Forall(((k, Nat),), k < 100), lambda p: False),
        (Forall(((k, Nat),), k >= 0), lambda p: True),
        (Forall(((k, Nat),), k < 3), lambda p: False),
        (Forall(((k, Nat),), k < 0, k > 100), lambda p: False),
        (Exists(((k, Nat),), k > 1000), lambda p: True),
        (Exists(((k, Nat),), k == 0), lambda p: True),
        (n < 2, lambda p: p["n"] < 2),
        (n < 0, lambda p: False),
    ]
    if inner:
        atoms += [
            (i == n, lambda p: p["i"] == p["n"]),
            (Forall(((k, Nat),), k < 100 + i), lambda p: False),
            (Forall(((k, Nat),), k + i >= i), lambda p: True),
        ]
    return atoms


def _statement(rng: random.Random, depth: int, inner: bool = False) -> tuple:
    """A random statement over :func:`_atoms`, with its truth as a function of the point."""
    i, n = Var("i"), Var("n")
    shape = rng.randrange(9) if depth else 0
    if shape == 0 or (inner and shape >= 5):
        return rng.choice(_atoms(inner))
    left, true_left = _statement(rng, depth - 1, inner)
    right, true_right = _statement(rng, depth - 1, inner)
    if shape == 1:
        return ~left, lambda p: not true_left(p)
    if shape == 2:
        return left & right, lambda p: true_left(p) and true_right(p)
    if shape == 3:
        return left | right, lambda p: true_left(p) or true_right(p)
    if shape == 4:
        return left == right, lambda p: true_left(p) == true_right(p)
    # a quantifier over Fin[n + 1], with a guard or a refinement read from a
    # statement about its binder, or a sum counting the points of one
    body, true_body = _statement(rng, depth - 1, inner=True)
    guard, true_guard = _statement(rng, depth - 1, inner=True)

    def points(p):
        return [{**p, "i": value} for value in range(p["n"] + 1)]

    if shape == 5:
        return Forall(((i, Fin[n + 1]),), body, guard), lambda p: all(
            true_body(q) for q in points(p) if true_guard(q)
        )
    if shape == 6:
        return Forall(((i, Fin[n + 1] & guard),), body), lambda p: all(
            true_body(q) for q in points(p) if true_guard(q)
        )
    if shape == 7:
        return Exists(((i, Fin[n + 1]),), body, guard), lambda p: any(
            true_body(q) for q in points(p) if true_guard(q)
        )
    count = rng.randrange(3)
    return Sum(((i, Fin[n + 1]),), 1, body) == count, lambda p: count == sum(
        1 for q in points(p) if true_body(q)
    )


def test_every_answer_is_one_its_position_allows() -> None:
    """Random statements over propositions whose truth is known, at every polarity.

    Standing ``POSITIVE`` a ``False`` has to be false, which is what makes a
    refutation real; standing ``NEGATIVE`` a ``True`` has to be true, which is
    what lets a hypothesis admit a draw; standing ``MIXED`` every answer has
    to be right. ``Undecided`` is always allowed. The statements combine the
    atoms with the connectives, comparisons between propositions, guarded and
    refined quantifiers over ``Fin[n + 1]`` and sums, and the rule the pieces
    are tested for one by one above has to hold for every combination.
    """
    rng = random.Random(0)
    decided = 0
    for trial in range(200):
        term, truth = _statement(rng, 4)
        for n in range(4):
            for polarity in Polarity:
                try:
                    answer = evaluate(term, {"n": n}, _sampler(trial), polarity)
                except Undecided:
                    continue
                decided += 1
                expected = truth({"n": n})
                if polarity is Polarity.POSITIVE:
                    allowed = answer or not expected
                elif polarity is Polarity.NEGATIVE:
                    allowed = expected or not answer
                else:
                    allowed = answer is expected
                assert allowed, (render(term), n, polarity, answer)
    # the check is only worth something if a fair share of answers were given
    assert decided > 500


# }}}
