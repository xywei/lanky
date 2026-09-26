"""The rewrite shape: a source, a target, and the obligation between them."""

from __future__ import annotations

import json

import pytest

import lanky
from lanky import cli
from lanky.check import check_path
from lanky.ledger import Fact, Status
from lanky.plugins import registry
from lanky.rewrites import Rewrite, RewriteTerm, rewrite, rewrite_fact
from lanky.terms import Var, render

n = Var("n")


def test_a_rewrite_is_the_pair_its_function_returns() -> None:
    with registry.collecting() as decorated:

        @rewrite
        def doubled():
            """Twice n, as a sum."""
            return 2 * n, n + n

    assert decorated == [doubled]
    assert isinstance(doubled, Rewrite)
    assert render(doubled.source) == "2*n"
    assert render(doubled.target) == "n + n"
    assert doubled.obligation == "equal"
    assert doubled.statement == "2*n ~> n + n (equal)"
    assert doubled() is doubled.target
    assert doubled.__doc__ == "Twice n, as a sum."
    assert repr(doubled) == "<rewrite doubled: 2*n ~> n + n (equal)>"


def test_a_rewrite_is_one_fact_of_one_shape() -> None:
    with registry.collecting():

        @rewrite(obligation="unrolled", uses=["theorem:elsewhere.lemma@3"])
        def unrolled():
            return "for i in range(2): x += a[i]", "x += a[0]; x += a[1]"

    fact = unrolled.fact()
    assert [claimed.id for claimed in unrolled.facts()] == [fact.id]
    assert fact.kind == "rewrite"
    assert fact.id == unrolled.fact_id
    assert fact.id == (
        f"rewrite:{__name__}.test_a_rewrite_is_one_fact_of_one_shape.<locals>.unrolled"
        f"@{unrolled.line}"
    )
    assert isinstance(fact.term, RewriteTerm)
    assert fact.term.source == "for i in range(2): x += a[i]"
    assert fact.term.target == "x += a[0]; x += a[1]"
    assert fact.term.obligation == "unrolled"
    assert fact.status is Status.ASSUMED
    assert fact.decided_by is None
    assert fact.rests_on == ("theorem:elsewhere.lemma@3",)
    assert fact.provenance == {"path": __file__, "line": unrolled.line}
    assert fact.where == f"test_rewrites.py:{unrolled.line}"
    assert fact.owner.endswith("unrolled")
    statement = "for i in range(2): x += a[i] ~> x += a[0]; x += a[1] (unrolled)"
    assert fact.statement == statement
    # the JSON carries the claim as text, since the term is not a lanky term
    assert fact.to_dict()["term"] == statement
    json.dumps(fact.to_dict())


def test_a_plugin_builds_the_same_shape_without_a_decorator() -> None:
    """What loopty's schedule steps are: a rewrite fact built, and decided, in place."""
    term = RewriteTerm("S0[i]", "S0[i_outer, i_inner]", "legal reindexing")
    fact = rewrite_fact(
        term,
        owner="scan",
        module="kernels",
        line=12,
        path="/work/kernels.py",
        where="kernels.py:12",
        detail="split",
        rests_on=["in-bounds:kernels.scan@12"],
    )
    assert fact.id == "rewrite:kernels.scan@12:split"
    assert fact.kind == "rewrite"
    assert fact.term is term
    assert fact.statement == "S0[i] ~> S0[i_outer, i_inner] (legal reindexing)"
    assert fact.provenance == {"path": "/work/kernels.py", "line": 12}
    assert fact.rests_on == ("in-bounds:kernels.scan@12",)
    decided = fact.with_status(Status.DECIDED, "isl", detail="bijective and monotone")
    assert decided.status is Status.DECIDED and decided.term is term
    with pytest.raises(TypeError, match="RewriteTerm"):
        rewrite_fact(("S0[i]", "S0[j]"), owner="scan")


def test_a_rewrite_term_compares_by_identity() -> None:
    """A side may be a lanky term, whose ``==`` builds a proposition."""
    left, right = RewriteTerm(n, n + 0), RewriteTerm(n, n + 0)
    assert left == left
    assert left != right
    assert str(left) == "n ~> n + 0 (equal)"


def test_the_rewrite_theory_is_built_in() -> None:
    theories = {theory.name: theory for theory in registry.theories}
    assert list(theories)[:2] == ["theorem", "rewrite"]
    assert theories["rewrite"].facts(object()) == ()
    assert lanky.rewrite is rewrite
    assert lanky.Rewrite is Rewrite
    assert lanky.RewriteTerm is RewriteTerm


def test_a_subclass_claims_more_than_the_rewrite() -> None:
    """The extension point a plugin uses to add a claim about the target."""

    class Checked(Rewrite):
        noun = "checked rewrite"

        def facts(self):
            fact = self.fact()
            about = Fact(
                id=f"{fact.id}:target",
                kind="about-the-target",
                statement="n + n is a sum",
                owner=fact.owner,
                rests_on=(fact.id,),
            )
            return (fact, about)

    def claimed():
        return 2 * n, n + n

    with registry.collecting():
        obj = registry.register_object(Checked(claimed))
    theory = next(theory for theory in registry.theories if theory.name == "rewrite")
    rewrite_row, target_row = theory.facts(obj)
    assert rewrite_row.kind == "rewrite"
    assert target_row.kind == "about-the-target"
    assert target_row.rests_on == (rewrite_row.id,)
    # what the subclass is called in messages does not change the fact's shape
    assert rewrite_row.id == obj.fact_id
    assert repr(obj).startswith("<checked rewrite claimed: ")


def test_a_malformed_rewrite_is_refused_where_it_is_written() -> None:
    with registry.collecting():
        with pytest.raises(TypeError, match=r"returns the pair \(source, target\)"):

            @rewrite
            def single():
                return n

        with pytest.raises(TypeError, match="takes no arguments.*asks for x"):

            @rewrite
            def needs(x):
                return x, x

        with pytest.raises(TypeError, match="obligation is a short name"):
            rewrite(obligation="")
        with pytest.raises(TypeError, match="obligation is a short name"):
            rewrite(obligation=None)
        with pytest.raises(TypeError, match="obligation='...'"):
            rewrite("equal")
        with pytest.raises(TypeError, match="uses= names facts"):
            rewrite(uses=[object()])
        with pytest.raises(TypeError, match="uses=None"):
            rewrite(uses=None)


# {{{ checking a file with rewrites in it

REWRITES = '''
"""Three rewrites of strings, and an oracle that decides one obligation."""

from __future__ import annotations

from lanky import rewrite


@rewrite(obligation="reversed")
def reversal():
    return "abc", "cba"


@rewrite(obligation="reversed")
def mistaken():
    return "abc", "abc"


@rewrite(obligation="sorted")
def unknown():
    return "cab", "abc"
'''


class Reverser:
    """Decides the obligation "reversed" between strings, and nothing else."""

    name = "reverser"

    def trust_class(self) -> str:
        return "decision-procedure"

    def can_establish(self, fact, /) -> bool:
        return isinstance(fact.term, RewriteTerm) and fact.term.obligation == "reversed"

    def establish(self, fact, /):
        source, target = fact.term.source, fact.term.target
        if source[::-1] == target:
            return fact.with_status(Status.DECIDED, self.name)
        return fact.with_status(
            Status.REFUTED, self.name, reason=f"{source!r} reversed is {source[::-1]!r}"
        )


def test_lanky_check_offers_each_rewrite_to_the_oracles(tmp_path, monkeypatch, capsys) -> None:
    """An oracle that knows the obligation decides it; nobody takes the other one."""
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, Reverser()])
    path = tmp_path / "rewrites.py"
    path.write_text(REWRITES, encoding="utf-8")
    reversal, mistaken, unknown = check_path(path)
    assert (reversal.status, reversal.decided_by) == (Status.DECIDED, "reverser")
    assert reversal.provenance["trust_class"] == "decision-procedure"
    assert (mistaken.status, mistaken.decided_by) == (Status.REFUTED, "reverser")
    # the property tester and Lean do not take a term that is not a lanky term
    assert unknown.status is Status.ASSUMED
    assert unknown.decided_by is None

    out = tmp_path / "out.json"
    assert cli.main(["check", str(path), "--json", str(out)]) == 1
    printed = capsys.readouterr().out
    assert "decided  reverser" in printed
    assert "REFUTED mistaken at rewrites.py:" in printed
    assert "'abc' reversed is 'cba'" in printed
    rows = json.loads(out.read_text(encoding="utf-8"))
    assert [row["kind"] for row in rows] == ["rewrite"] * 3
    assert rows[0]["term"] == "abc ~> cba (reversed)"


# }}}
