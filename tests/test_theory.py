"""The @theorem theory: statements, native calls, and property tests."""

from __future__ import annotations

import functools

import pytest

from lanky import axiom, theorem
from lanky.ledger import Fact, Status
from lanky.oracles.test import TestOracle
from lanky.plugins import registry
from lanky.prelude import Fin, Fn, Int, Nat
from lanky.terms import Var
from lanky.theory import Axiom, Theorem


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Twice the sum of 0 .. n is n * (n + 1)."""


def false_theorem() -> Theorem:
    """A deliberately false theorem, built inside a function.

    It lives here rather than at module level so that lanky's pytest plugin,
    which collects module-level theorems as test items, does not collect a
    statement this suite means to refute.
    """

    @theorem
    def wrong(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
        """False as soon as n is at least two."""

    return wrong


@theorem
def bounded(n: Nat, k: Int, h: k >= n) -> k + 1 > n:
    """A hypothesis restricts which draws count."""


def test_the_signature_is_the_statement() -> None:
    assert isinstance(gauss, Theorem)
    assert gauss.variables == (("n", Nat),)
    assert gauss.hypotheses == ()
    assert gauss.statement == "n : Nat |- 2*sum(i for i in Fin(n + 1)) == n*(n + 1)"
    assert bounded.statement == "n : Nat, k : Int | k >= n |- k + 1 > n"


def test_the_decorator_registers_in_import_order() -> None:
    names = [obj.__name__ for obj in registry.objects if isinstance(obj, Theorem)]
    assert "gauss" in names
    assert names.index("gauss") < names.index("bounded")


def test_calling_a_theorem_evaluates_it_at_concrete_values() -> None:
    verdict = gauss(n=4)
    assert verdict.goal is True
    assert verdict.holds is True
    assert bool(verdict)
    assert false_theorem()(n=3).goal is False
    # a failed hypothesis means the statement is not violated
    verdict = bounded(n=3, k=0)
    assert verdict.hypotheses == {"h": False}
    assert verdict.hypotheses_hold is False
    assert verdict.holds is True
    with pytest.raises(TypeError, match="needs values for n"):
        gauss()


def test_a_true_theorem_passes_the_property_test() -> None:
    ok, counterexample = gauss.test(n=30)
    assert ok
    assert counterexample is None
    report = gauss.report(n=30)
    assert report.valid == 30


def test_a_false_theorem_returns_a_counterexample() -> None:
    ok, counterexample = false_theorem().test(n=30)
    assert not ok
    assert counterexample is not None
    assert counterexample["n"] not in (0, 1)


def test_hypotheses_filter_the_draws() -> None:
    report = bounded.report(n=20)
    assert report.ok
    assert 0 < report.valid <= 20
    assert report.samples > report.valid


def test_a_theorem_becomes_an_assumed_fact_until_an_oracle_speaks() -> None:
    fact = gauss.fact()
    # the id names the definition, not only the qualified name: module, name
    # and line, which is what keeps two same-named theorems apart in one ledger;
    # the module is the one this file's path gives it, tests/ being no package
    assert fact.id == f"theorem:test_theory.gauss@{gauss.line}"
    assert fact.id == gauss.fact_id
    assert fact.kind == "theorem"
    assert fact.status is Status.ASSUMED
    assert fact.owner == "gauss"
    assert fact.where.startswith("test_theory.py:")
    assert fact.statement == gauss.statement


def test_the_closed_term_carries_binders_and_guard() -> None:
    term = bounded.term
    assert [var.name for var, _ in term.binders] == ["n", "k"]
    assert term.guard is not None


def test_families_are_sampled_as_tables() -> None:
    @theorem
    def head_is_smallest(
        n: Nat,
        f: Fn[Fin[n + 1], Nat],
        h0: f(0) == 0,
    ) -> f(0) <= f(n):
        """The sampler satisfies a definitional hypothesis rather than rejecting."""

    report = head_is_smallest.report(n=20)
    assert report.ok
    assert report.valid == 20


def test_the_lean_printer_is_not_here_yet() -> None:
    with pytest.raises(NotImplementedError):
        gauss.lean()


# {{{ axioms, and what a theorem uses


def cited() -> Axiom:
    """An axiom, built inside a function so that pytest does not collect it."""

    @axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
    def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
        """The sum of the first cubes is the square of the sum of the first numbers."""

    return nicomachus


def test_an_axiom_is_a_statement_taken_on_a_citation() -> None:
    nicomachus = cited()
    assert isinstance(nicomachus, Axiom)
    assert isinstance(nicomachus, Theorem)
    assert nicomachus.cite == "Nicomachus of Gerasa, Introduction to Arithmetic"
    assert nicomachus.variables == (("n", Nat),)
    fact = nicomachus.fact()
    assert fact.id == f"axiom:{__name__}.cited.<locals>.nicomachus@{nicomachus.line}"
    assert fact.id == nicomachus.fact_id
    assert fact.kind == "axiom"
    assert fact.is_axiom
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.provenance["cite"] == nicomachus.cite
    assert fact.rests_on == ()
    assert repr(nicomachus).startswith("<axiom nicomachus: n : Nat |- ")
    # it is still a statement: it can be called and sampled
    assert nicomachus(n=4).holds
    assert nicomachus.report(n=20).ok
    assert nicomachus in registry.objects


def test_an_axiom_needs_a_citation() -> None:
    """Without one it is a claim with nothing behind it, which ``assumed`` already says."""

    def statement(n: Nat) -> n + 0 == n:
        """Addition of zero."""

    with pytest.raises(TypeError, match=r'needs a citation.*@axiom\(cite="..."\)'):
        axiom(statement)
    with pytest.raises(TypeError, match="needs a citation"):
        axiom()
    with pytest.raises(TypeError, match="needs a citation"):
        axiom(cite=None)
    with pytest.raises(TypeError, match="citation is empty"):
        axiom(cite="  ")
    with pytest.raises(TypeError, match="citation is a string"):
        axiom(cite=("Kress", 1989))
    with pytest.raises(TypeError, match="an axiom needs a goal"):

        @axiom(cite="a textbook")
        def no_goal(n: Nat):
            """No return annotation."""


def test_a_theorem_names_what_it_uses() -> None:
    """``uses=`` takes theorems, axioms, facts and ids; they become ``rests_on``."""
    nicomachus = cited()
    plugin_fact = Fact(id="scan:postcondition", kind="postcondition", statement="...")

    @theorem(uses=[nicomachus, gauss, plugin_fact, "kernel:spmv:traced", nicomachus])
    def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
        """The sum of the cubes, in closed form."""

    assert isinstance(cubes, Theorem)
    assert cubes.uses == (
        nicomachus.fact_id,
        gauss.fact_id,
        "scan:postcondition",
        "kernel:spmv:traced",
    )
    assert cubes.fact().rests_on == cubes.uses
    assert cubes.fact().kind == "theorem"
    assert cubes in registry.objects

    # one entry need not be wrapped, and none is said with an empty list
    @theorem(uses=nicomachus)
    def single(n: Nat) -> n + 0 == n:
        """Uses one fact."""

    @theorem(uses=[])
    def none(n: Nat) -> n + 0 == n:
        """Uses nothing."""

    @theorem()
    def bare(n: Nat) -> n + 0 == n:
        """Called with no arguments at all."""

    assert single.fact().rests_on == (nicomachus.fact_id,)
    assert none.fact().rests_on == ()
    assert bare.fact().rests_on == ()
    assert gauss.fact().rests_on == ()


def test_uses_refuses_what_does_not_name_one_fact() -> None:
    """Refused where the decorator is written, not when the file is checked."""
    with pytest.raises(TypeError, match="is none of them"):

        @theorem(uses=[object()])
        def claim(n: Nat) -> n + 0 == n:
            """Uses something that is not a fact."""

    with pytest.raises(TypeError, match="or a list of them"):
        theorem(uses=3)


def test_uses_none_is_refused_rather_than_read_as_nothing() -> None:
    """``uses=lemma`` with ``lemma`` bound to ``None`` by mistake names no fact.

    Read as "uses nothing", the theorem would be worth its own status with
    nothing to say that what it was meant to rest on went missing.
    """
    with pytest.raises(TypeError, match="uses=None names no fact"):

        @theorem(uses=None)
        def claim(n: Nat) -> n + 0 == n:
            """Meant to rest on something."""

    with pytest.raises(TypeError, match="uses=None names no fact"):
        axiom(cite="a textbook", uses=None)
    with pytest.raises(TypeError, match="is none of them"):
        theorem(uses=[None])


def test_a_decorator_refuses_what_is_not_the_function_it_decorates() -> None:
    """``@theorem(gauss)`` is ``uses=`` without its keyword, ``@axiom("...")`` is ``cite=``.

    Read as the function to decorate, the first failed on a theorem having no
    code object and the second on a missing citation, neither saying why.
    """
    with pytest.raises(TypeError, match=r"@theorem decorates a typed function.*uses=\[\.\.\.\]"):

        @theorem(gauss)
        def claim(n: Nat) -> n + 0 == n:
            """Meant to use gauss."""

    with pytest.raises(TypeError, match="@theorem decorates a typed function"):
        theorem([gauss])
    with pytest.raises(TypeError, match=r'@axiom decorates a typed function.*cite="\.\.\."'):

        @axiom("Kress, Linear Integral Equations")
        def kress(n: Nat) -> n + 0 == n:
            """Meant to be cited."""

    with pytest.raises(TypeError, match="@axiom decorates a typed function"):
        axiom(cited(), cite="a textbook")


def test_an_axiom_can_rest_on_facts_too() -> None:
    @axiom(cite="a textbook", uses=[gauss])
    def restated(n: Nat) -> n + 0 == n:
        """A cited result stated in terms of another."""

    assert restated.fact().rests_on == (gauss.fact_id,)
    assert restated.fact().provenance["cite"] == "a textbook"


# }}}


def test_a_builtin_answered_at_concrete_values_is_refuted() -> None:
    """``round(0.5) == 1`` is Python's ``0 == 1``, and the tester refutes it (#63).

    ``round`` was a free name, so the statement applied a variable nobody
    binds: the tester could not run it, and Mathlib proved it about its own
    ``round``, which rounds half up (#64).
    """

    @theorem
    def rounds_half_up() -> round(0.5) == 1:
        """False in Python, where round(0.5) is 0."""

    assert rounds_half_up.term is False
    assert TestOracle().establish(rounds_half_up.fact()).status is Status.REFUTED


def test_an_annotation_that_is_a_builtin_is_refused() -> None:
    """``x: int`` made ``int`` a hypothesis and ``x`` a free name (#63).

    Lean then bound ``x`` implicitly, as a natural, and proved ``x - 1 >= 0``,
    which is false at ``x = 0`` (#64). The theorem is refused where it is
    written, naming the sort meant, with ``from __future__ import
    annotations`` and without it.
    """

    def as_int(x: int) -> x - 1 >= 0:
        """False at x = 0."""

    with pytest.raises(
        TypeError,
        match=r"as_int at test_theory.py:\d+: the parameter x is annotated with int, "
        r"which is Python's int and not a lanky sort or a proposition; write Int "
        r"from lanky.prelude, or Nat for a natural",
    ):
        theorem(as_int)

    def as_float(n: Nat, x: float) -> x * n >= 0:
        """A real number, written as Python's type."""

    with pytest.raises(TypeError, match="the parameter x is annotated with float.*write Real"):
        theorem(as_float)

    def a_bool(n: Nat) -> bool:
        """A goal that is a type, and no proposition."""

    with pytest.raises(TypeError, match="the goal is annotated with bool"):
        theorem(a_bool)

    # without the future import the annotation is the type itself, refused alike
    namespace: dict = {"x": Var("x")}
    source = "def eager(x: int) -> x >= 0:\n    pass\n"
    exec(compile(source, "<eager>", "exec", dont_inherit=True), namespace)
    with pytest.raises(TypeError, match="the parameter x is annotated with int"):
        theorem(namespace["eager"])


def test_a_builtin_named_inside_an_annotation_is_refused() -> None:
    """A builtin named and not called anywhere in an annotation is refused too.

    ``f: Fn[Fin[n], float]`` made ``float``, a free name, the sort of the
    family's values: the tester could draw no value of it, passed the claim
    on the draws where ``n`` is ``0`` and the family empty, and so read
    ``all(f(i) >= 0 for i in Fin[n])`` as tested, which is false for a
    family of floats. Lean could not print the type. The same holds for a
    builtin as a family's index, inside a refinement, as a ``Fin`` bound or
    as a value in a proposition.
    """

    def floats(n: Nat, f: Fn[Fin[n], float]) -> all(f(i) >= 0 for i in Fin[n]):
        """False for a family of floats."""

    with pytest.raises(
        TypeError,
        match=r"the parameter f is annotated with Fn\[Fin\(n\), float\], which names "
        r"Python's float without calling it, .*; write Real from lanky.prelude",
    ):
        theorem(floats)

    def nested(n: Nat, f: Fn[Fin[n], Fn[Int, int]]) -> all(f(i)(0) >= 0 for i in Fin[n]):
        """A builtin in a family of families."""

    with pytest.raises(TypeError, match=r"the parameter f is annotated .*Python's int"):
        theorem(nested)

    def refined(x: int & (x > 0)) -> x >= 1:
        """A refinement of a builtin, which read as the proposition ``int and x > 0``."""

    with pytest.raises(TypeError, match=r"the parameter x is annotated with int and x > 0"):
        theorem(refined)

    def bounded(i: Fin[len]) -> i >= 0:
        """A builtin as a size."""

    with pytest.raises(TypeError, match=r"Python's len without calling it.*bind len as a"):
        theorem(bounded)

    def compared(n: Nat) -> n >= int:
        """A builtin as a value."""

    # Python asks the subclass first, BuiltinName, so the comparison is reflected
    with pytest.raises(TypeError, match=r"the goal is annotated with int <= n, which names"):
        theorem(compared)

    # without the future import the type is what the family is built of
    namespace: dict = {"Fn": Fn, "Fin": Fin}
    source = "def eager(f: Fn[Fin[3], float]) -> True:\n    pass\n"
    exec(compile(source, "<eager>", "exec", dont_inherit=True), namespace)
    with pytest.raises(TypeError, match=r"parameter f is annotated with .*, which names Python's"):
        theorem(namespace["eager"])

    # a builtin called at concrete values leaves nothing behind, and a name
    # bound by the theorem is the theorem's
    @theorem
    def concrete(n: Nat, min: Fn[Fin[n], Nat]) -> all(min(i) >= round(0.4) for i in Fin[n]):
        """True: round(0.4) is 0, and min is the family."""

    assert concrete.report().ok


def test_a_term_is_no_key_of_a_dict_or_a_set_in_an_annotation() -> None:
    """#73: a lookup keyed by a term answered from its hash, as if the key were absent.

    A dict or a set finds a key by its hash before it compares anything, and
    a term's hash is its structure's, so ``{0: 1}.get(i, 0)`` was ``0``
    while the annotation was read, and the statement became ``f(i)*0 ==
    0``, which Lean proved with ``omega``, false at ``i = 0``. ``i in {0, 1}``
    was ``False`` the same way, and nothing asked a term for a truth value
    lanky could refuse. A term is unhashable to the annotation's own code
    now, as a list is, and the theorem is refused where it is written.
    """
    refused = r"i was hashed by the annotation, as a dict or a set lookup or display"

    def looked_up(n: Nat, f: Fn[Fin[n], Nat]) -> all(
        f(i) * 0 == {0: 1}.get(i, 0) for i in Fin[n]
    ):
        """False in Python at i = 0, where the lookup gives 1."""

    with pytest.raises(TypeError, match=refused):
        theorem(looked_up)

    def member(n: Nat) -> all(i in {0, 1} for i in Fin[n]):
        """False wherever n > 2; read as False everywhere."""

    with pytest.raises(TypeError, match=refused):
        theorem(member)

    def displayed(n: Nat) -> all({i: 1}[0] == 1 for i in Fin[n]):
        """A dict display keyed by a term."""

    with pytest.raises(TypeError, match=refused):
        theorem(displayed)

    def subscripted(n: Nat) -> all({0: 1}[i] == 1 for i in Fin[n]):
        """This one raised KeyError, and is refused with the reason now."""

    with pytest.raises(TypeError, match=refused):
        theorem(subscripted)

    def quantified(n: Nat) -> {all(i >= 0 for i in Fin[n]): 1}.get(True, 0) == 1:
        """A quantifier as a key, whose hash pymbolic generates."""

    with pytest.raises(TypeError, match=r"forall i in Fin\(n\)\. i >= 0 was hashed"):
        theorem(quantified)

    # concrete keys, and a term as a value, are no business of the hash
    @theorem
    def concrete(n: Nat) -> {0: n, 1: 1}.get(0) == n:
        """A lookup by a concrete key."""

    assert concrete.statement == "n : Nat |- n == n"
    # outside an annotation a term hashes as pymbolic's node does
    x = Var("x")
    assert hash(x) == hash(Var("x"))
    assert {x: 1}[x] == 1


def test_a_builtin_the_annotation_calls_hashes_no_term() -> None:
    """#73: a builtin called by name in an annotation hashed a term in lanky's frame.

    A builtin an annotation names runs in :class:`lanky.terms.BuiltinName`,
    so a hash it asked for was asked in lanky's frame and not refused: ``set(i
    for k in range(1))`` held ``i``, and ``0 not in`` it read ``True``;
    ``dict((i, 1) for k in range(1)).get(0, 0)`` read ``0``; and ``max`` with
    a key that looks ``i`` up read as if ``i`` were never ``0``. Lean proved
    each statement, and each is false at ``i = 0``. A hash a builtin asks for
    is refused as the annotation's own is.
    """

    def set_of(n: Nat, f: Fn[Fin[n], Nat]) -> all(
        (f(i) * 0 == 1) | (0 not in set(i for k in range(1))) for i in Fin[n]
    ):
        """False at i = 0, where the set holds 0."""

    with pytest.raises(TypeError, match=r"Python's set raised .*i was hashed by the annotation"):
        theorem(set_of)

    def dict_of(n: Nat, f: Fn[Fin[n], Nat]) -> all(
        f(i) * 0 == dict((i, 1) for k in range(1)).get(0, 0) for i in Fin[n]
    ):
        """False at i = 0, where the lookup gives 1."""

    with pytest.raises(TypeError, match=r"Python's dict raised .*i was hashed by the annotation"):
        theorem(dict_of)

    def keyed(n: Nat, f: Fn[Fin[n], Nat]) -> all(
        f(i) * 0 + max([0, 1], key=functools.partial({0: 5}.get, i)) == 1 for i in Fin[n]
    ):
        """False at i = 0, where both keys are 5 and max gives 0."""

    with pytest.raises(TypeError, match=r"Python's max raised .*i was hashed by the annotation"):
        theorem(keyed)

    def ordered(n: Nat, f: Fn[Fin[n], Nat]) -> all(
        f(i) * 0 + sorted([1, 0], key=functools.partial({0: 5}.get, i))[0] == 0 for i in Fin[n]
    ):
        """False at i = 0, where both keys are 5 and sorted keeps 1 first."""

    with pytest.raises(TypeError, match=r"Python's sorted raised .*i was hashed by the"):
        theorem(ordered)

    # at concrete values a builtin is Python's, a generator and a key included
    @theorem
    def concrete(n: Nat) -> len(set(k % 2 for k in range(4))) + max(
        [0, 1, 2], key=functools.partial({0: 5}.get, 0)
    ) + n >= 2:
        """True: two residues, and every key is 5, so max gives the first, 0."""

    assert concrete.statement == "n : Nat |- 2 + n >= 2"
