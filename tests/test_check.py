"""Checking a file: import it, collect facts, run oracles, exit on a refutation."""

from __future__ import annotations

import json

import pytest

from lanky import cli
from lanky.check import check_path, oracle_lines
from lanky.ledger import Fact, Ledger, Status
from lanky.terms import Var

FILE = '''
"""Two claims, one of them false."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Fin, Nat


@theorem
def true_claim(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Gauss."""


@theorem
def false_claim(n: Nat) -> sum(i for i in Fin[n + 1]) == n:
    """False as soon as n is at least two."""
'''


def write_file(tmp_path, text: str = FILE) -> str:
    path = tmp_path / "claims.py"
    path.write_text(text, encoding="utf-8")
    return str(path)


def test_check_path_yields_a_ledger(tmp_path) -> None:
    ledger = check_path(write_file(tmp_path))
    assert [fact.owner for fact in ledger] == ["true_claim", "false_claim"]

    tested = ledger.by_status(Status.TESTED)
    assert [fact.owner for fact in tested] == ["true_claim"]
    assert tested[0].decided_by == "property-test"
    assert tested[0].provenance["valid"] > 0

    refuted = ledger.by_status(Status.REFUTED)
    assert [fact.owner for fact in refuted] == ["false_claim"]
    assert refuted[0].decided_by == "property-test"
    assert "n" in refuted[0].provenance["counterexample"]
    assert refuted[0].where.startswith("claims.py:")


def test_checking_twice_keeps_the_ledgers_apart(tmp_path) -> None:
    path = write_file(tmp_path)
    assert len(check_path(path)) == 2
    assert len(check_path(path)) == 2


def test_oracle_lines_name_the_trust_classes() -> None:
    lines = oracle_lines()
    assert any(line.startswith("lean (kernel):") for line in lines)
    assert any(line.startswith("property-test (test): available") for line in lines)


def test_cli_exits_one_on_a_refutation(tmp_path, capsys) -> None:
    out_json = tmp_path / "ledger.json"
    code = cli.main(["check", write_file(tmp_path), "--json", str(out_json)])
    assert code == 1
    printed = capsys.readouterr().out
    assert "REFUTED false_claim" in printed
    assert "counterexample" in printed
    # the reason follows the counterexample
    assert "  the goal is false at this assignment" in printed
    data = json.loads(out_json.read_text(encoding="utf-8"))
    assert {entry["status"] for entry in data} == {"tested", "refuted"}


def test_cli_exits_zero_when_nothing_is_refuted(tmp_path, capsys) -> None:
    text = FILE.split("@theorem\ndef false_claim")[0]
    code = cli.main(["check", write_file(tmp_path, text), "--verbose"])
    assert code == 0
    printed = capsys.readouterr().out
    assert "property-test (test): available" in printed
    assert "1 facts: 1 tested" in printed


def test_cli_without_a_verb_prints_help(capsys) -> None:
    assert cli.main([]) == 0
    assert "check" in capsys.readouterr().out


def test_checking_a_file_does_not_accumulate_its_objects(tmp_path) -> None:
    """A process that checks many files must not keep every one of them.

    The decorators register into one process-wide registry, so a check has to
    scope itself to the objects its own import made and then let them go.
    """
    from lanky.plugins import registry

    path = write_file(tmp_path)
    check_path(path)
    after_one = len(registry.objects)
    check_path(path)
    assert len(registry.objects) == after_one


def test_an_imported_file_does_not_stay_in_sys_modules(tmp_path) -> None:
    """Two files with one basename would otherwise share a module entry."""
    import sys

    check_path(write_file(tmp_path))
    assert not [name for name in sys.modules if name.startswith("lanky_checked_")]


@pytest.mark.parametrize("lean", ["as installed", "disabled"])
def test_subtraction_over_nat_is_refuted_with_or_without_lean(
    tmp_path, monkeypatch, capsys, lean
) -> None:
    """#6: ``n - 1 >= 0`` has one verdict and one exit code on every machine.

    Lean used to prove it, because its ``Nat`` subtraction truncates, while
    the property tester refuted it at ``n = 0``; the check exited 0 where Lean
    was installed and 1 where it was not, and this test accepted either. Every
    oracle reads the statement over the integers now, so there is no semantics
    note, the fact is refuted, and ``lanky check`` exits 1, with Lean and
    without it. On a machine with Lean both parameters run.
    """
    if lean == "disabled":
        monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "truncated.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def truncated(n: Nat) -> n - 1 >= 0:\n"
        '    """True where Nat subtraction truncates; false at n = 0 in integers."""\n',
        encoding="utf-8",
    )
    (fact,) = list(check_path(path))
    assert "semantics" not in fact.provenance
    assert fact.status is Status.REFUTED
    assert fact.decided_by == "property-test"
    assert fact.provenance["counterexample"] == {"n": 0}
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "REFUTED truncated" in printed
    assert "SEMANTICS" not in printed


CLOSED = '''
"""Two claims Python answers on its own."""

from __future__ import annotations

from lanky import theorem


@theorem
def certainly() -> 1 == 1:
    """True, with no variable to draw and no hypothesis to satisfy."""


@theorem
def impossible() -> 1 == 2:
    """False, and nothing in the file says otherwise."""
'''


def test_cli_exits_one_on_a_false_closed_claim(tmp_path, capsys) -> None:
    """The shortest false theorem there is used to leave the check green.

    ``1 == 2`` is answered by Python while the annotation is evaluated, so the
    term is a ``bool``. The property oracle declined anything that was not a
    pymbolic node and Lean has no proof of a false statement, so the row read
    ``assumed`` and ``lanky check`` exited 0.
    """
    path = tmp_path / "closed.py"
    path.write_text(CLOSED, encoding="utf-8")
    out_json = tmp_path / "ledger.json"
    code = cli.main(["check", str(path), "--json", str(out_json)])
    printed = capsys.readouterr().out
    assert code == 1
    assert "REFUTED impossible" in printed
    # the reason is what explains it; the empty witness said nothing, and is
    # left out of the terminal while the JSON keeps it
    block = printed.split("REFUTED impossible", 1)[1].splitlines()[1:]
    assert block == [
        "  the statement is the constant False: it binds no variable and assumes "
        "nothing, so there is no assignment to blame and nothing that could make "
        "it true"
    ]
    assert "counterexample" not in printed
    (entry,) = [
        entry for entry in json.loads(out_json.read_text(encoding="utf-8"))
        if entry["owner"] == "impossible"
    ]
    assert entry["provenance"]["counterexample"] == {}
    assert "constant False" in entry["provenance"]["reason"]


def test_a_true_closed_claim_is_tested_rather_than_assumed(tmp_path, monkeypatch) -> None:
    """The other side of it, with Lean out of the way so the decider is fixed."""
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    path = tmp_path / "closed.py"
    path.write_text(CLOSED.split("@theorem\ndef impossible")[0], encoding="utf-8")
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert fact.status is Status.TESTED
    assert fact.decided_by == "property-test"


def test_a_division_by_zero_is_a_gap_the_ledger_records(tmp_path) -> None:
    """``n // 0 == 0`` is a Lean theorem and a Python ZeroDivisionError.

    Whatever establishes it, the note has to be in the provenance and the
    sampled reading has to have been tried: with Lean the fact is proved and
    the cross-check records that the Python reading could not be run, without
    Lean the tester declines the draws and the row stays assumed.
    """
    from lanky.semantics import DIVISION_BY_ZERO

    path = tmp_path / "divzero.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def div_zero(n: Nat) -> n // 0 == 0:\n"
        '    """Total in Lean, undefined in Python."""\n',
        encoding="utf-8",
    )
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert DIVISION_BY_ZERO in fact.provenance["semantics"]
    assert fact.status is not Status.REFUTED
    if fact.status is Status.ASSUMED:
        assert "zero" in fact.provenance["untested"]
    else:
        assert fact.status is Status.PROVED
        assert "zero" in fact.provenance["semantics_undecided"]


def test_an_axiom_records_its_division_by_zero_gap_too(tmp_path, capsys) -> None:
    """An axiom is sampled for a counterexample, and the gap is where sampling is blind.

    It used to skip the note: an axiom went to its own examination before the
    gaps were read, so ``n // m`` with ``m`` possibly zero left nothing in the
    provenance, and a reader could not tell that some draws were never
    answered. The note is in the provenance and the verbose output, and the
    axiom stays ``assumed``.
    """
    from lanky.semantics import DIVISION_BY_ZERO

    path = tmp_path / "divaxiom.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import axiom\n"
        "from lanky.prelude import Nat\n\n\n"
        '@axiom(cite="the division algorithm")\n'
        "def divides(n: Nat, m: Nat) -> (n // m) * m + n % m == n:\n"
        '    """Floor division and remainder put a number back together."""\n',
        encoding="utf-8",
    )
    (fact,) = list(check_path(path, verbose=True))
    assert fact.status is Status.ASSUMED
    assert fact.provenance["semantics"] == [DIVISION_BY_ZERO]
    assert f"  semantics: {DIVISION_BY_ZERO}" in capsys.readouterr().out.splitlines()


def test_an_application_outside_its_domain_is_never_proved(tmp_path, capsys) -> None:
    """A family applied past its own domain must not come back ``proved``.

    Lean sees a total ``Nat -> Nat`` once the family is erased, so the claim is
    a tautology there; the statement lanky wrote has no value at that point at
    all. The printer declines it, the tester cannot answer it either, and the
    ledger says assumed and why rather than proved.
    """
    path = tmp_path / "outside.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Fin, Fn, Nat\n\n\n"
        "@theorem\n"
        "def outside(n: Nat, f: Fn[Fin[n], Nat]) -> f(n) == f(n):\n"
        '    """One point past the domain f declares."""\n',
        encoding="utf-8",
    )
    assert cli.main(["check", str(path)]) == 0
    assert "assumed" in capsys.readouterr().out
    (fact,) = list(check_path(path))
    assert fact.status is Status.ASSUMED
    assert fact.status is not Status.PROVED
    assert "outside the domain" in fact.provenance["untested"]


def test_a_file_that_does_not_exist_is_a_mistake_in_the_command(capsys) -> None:
    assert cli.main(["check", "/no/such/file.py"]) == 2
    assert "no such file" in capsys.readouterr().out


def test_a_missing_file_the_checked_file_opens_is_the_file_failing(tmp_path, capsys) -> None:
    """A ``FileNotFoundError`` raised inside the file is the file's, not the command's.

    The command-error branch used to catch every ``FileNotFoundError`` out of
    ``check_path``, so a file that exists and opens a data file that does not
    was reported as missing itself, with exit code 2 and no traceback.
    """
    path = tmp_path / "reads_data.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from pathlib import Path\n\n"
        "DATA = (Path(__file__).parent / 'missing-data.json').read_text()\n",
        encoding="utf-8",
    )
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "no such file" not in printed
    assert "could not be imported" in printed
    assert "FileNotFoundError" in printed
    assert "missing-data.json" in printed


def test_a_file_that_raises_on_import_fails_the_check(tmp_path, capsys) -> None:
    """A file that does not import is a broken claim, not a clean ledger."""
    from lanky.plugins import registry

    path = tmp_path / "boom.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def fine(n: Nat) -> n + 0 == n:\n"
        '    """Registered before the file blows up."""\n\n\n'
        "raise RuntimeError('boom')\n",
        encoding="utf-8",
    )
    before = len(registry.objects)
    assert cli.main(["check", str(path)]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" in printed
    assert "RuntimeError: boom" in printed
    # whatever the file managed to register is released again
    assert len(registry.objects) == before


def test_an_oracle_whose_availability_probe_raises_does_not_stop_the_check(
    tmp_path, monkeypatch, capsys
) -> None:
    """One broken optional oracle costs itself, not the check.

    The probe used to raise straight out of ``establish`` and ``oracle_lines``,
    so ``lanky check`` reported the checked file as unimportable and the
    weaker oracles never ran.
    """
    from lanky.plugins import registry

    class BrokenProbe:
        name = "broken-probe"

        def trust_class(self) -> str:
            return "decision-procedure"

        def availability(self) -> tuple[bool, str]:
            raise ImportError("libdemo.so: cannot open shared object file")

        def can_establish(self, fact, /) -> bool:
            return True

        def establish(self, fact, /):
            raise AssertionError("an unavailable oracle is never asked")

    # load everything first, so that nothing registered during the test is
    # lost when the patched list is put back
    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, BrokenProbe()])

    ledger = check_path(write_file(tmp_path))
    assert [fact.status for fact in ledger] == [Status.TESTED, Status.REFUTED]
    (line,) = [line for line in oracle_lines() if line.startswith("broken-probe ")]
    assert line.startswith(
        "broken-probe (decision-procedure): unavailable: its availability check raised "
        "ImportError: libdemo.so"
    )

    assert cli.main(["check", write_file(tmp_path), "--verbose"]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" not in printed
    assert "REFUTED false_claim" in printed


HELPER = '''
"""A claim that lives in a module the checked file imports."""

from __future__ import annotations

from lanky import theorem
from lanky.prelude import Nat


@theorem
def helper_claim(n: Nat) -> n + 0 == n:
    """Collected when the file that imports this module is checked."""
'''


def _neighbourhood(tmp_path, neighbour: str) -> tuple:
    """A project holding FILE, importing a claim from a module next to it."""
    project = tmp_path / "project"
    project.mkdir()
    helper = project / f"{neighbour}.py"
    helper.write_text(HELPER, encoding="utf-8")
    main = project / "main_claims.py"
    main.write_text(
        FILE.replace(
            "from lanky.prelude import Fin, Nat\n",
            f"from lanky.prelude import Fin, Nat\nfrom {neighbour} import helper_claim\n",
        ),
        encoding="utf-8",
    )
    return main, helper


def test_a_claim_imported_from_a_neighbour_is_not_collected(tmp_path) -> None:
    """A check collects the claims the file defines, and none that it imports.

    Python imports a module once per process, so collecting whatever an
    import happened to register made the neighbour's theorem part of the
    first check of the file and missing from the second. Ownership is now
    read off where each object was defined, so every check of the file agrees,
    and the neighbour is left imported like any other module. Its claim is
    checked by checking its file, which finds it even though the module is
    cached.
    """
    import sys

    neighbour = "lanky_test_neighbour_claims"
    main, helper = _neighbourhood(tmp_path, neighbour)
    try:
        first = [fact.owner for fact in check_path(main)]
        cached = sys.modules[neighbour]
        second = [fact.owner for fact in check_path(main)]
        assert first == ["true_claim", "false_claim"]
        assert second == first
        assert sys.modules[neighbour] is cached
        assert [fact.owner for fact in check_path(helper)] == ["helper_claim"]
    finally:
        sys.modules.pop(neighbour, None)


def test_a_neighbour_imported_before_the_check_changes_nothing(tmp_path, monkeypatch) -> None:
    """Import order is not ownership: a neighbour that runs nothing now is no different."""
    import importlib
    import sys

    from lanky.plugins import registry

    neighbour = "lanky_test_early_neighbour"
    main, _helper = _neighbourhood(tmp_path, neighbour)
    monkeypatch.syspath_prepend(str(main.parent))
    try:
        with registry.collecting():
            importlib.import_module(neighbour)
        assert [fact.owner for fact in check_path(main)] == ["true_claim", "false_claim"]
    finally:
        sys.modules.pop(neighbour, None)


def test_the_cli_checks_a_neighbour_when_it_is_listed(tmp_path, monkeypatch, capsys) -> None:
    """``lanky check main.py helper.py`` is how two files are checked together.

    Each file gets its own ledger under a heading, since a fact id is unique
    within one file's ledger and not across files, and each claim is checked
    once: the helper's theorem under the helper, whichever order the files
    are listed in. ``--json`` writes one list of both files' facts.
    """
    import sys

    # Lean proves the helper's claim where it is installed; which oracle takes
    # it is not what this is about, and the counts below are the tester's.
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    neighbour = "lanky_test_listed_neighbour"
    main, helper = _neighbourhood(tmp_path, neighbour)
    out_json = tmp_path / "ledger.json"
    try:
        for files in ([main, helper], [helper, main]):
            code = cli.main(["check", *map(str, files), "--json", str(out_json)])
            printed = capsys.readouterr().out
            assert code == 1  # false_claim
            assert printed.startswith(f"==> {files[0]} <==\n")
            assert f"\n\n==> {files[1]} <==\n" in printed
            assert printed.count("helper_claim") == 1
            assert "2 facts: 1 refuted, 1 tested" in printed
            assert "1 facts: 1 tested" in printed
            data = json.loads(out_json.read_text(encoding="utf-8"))
            assert sorted(entry["owner"] for entry in data) == [
                "false_claim",
                "helper_claim",
                "true_claim",
            ]
    finally:
        sys.modules.pop(neighbour, None)


def test_the_cli_checks_nothing_when_one_of_several_files_is_missing(tmp_path, capsys) -> None:
    path = write_file(tmp_path)
    assert cli.main(["check", path, str(tmp_path / "absent.py")]) == 2
    printed = capsys.readouterr().out
    assert printed == f"lanky check: no such file: {tmp_path / 'absent.py'}\n"


def test_a_file_that_does_not_import_does_not_stop_the_others(tmp_path, capsys) -> None:
    broken = tmp_path / "broken.py"
    broken.write_text("raise RuntimeError('boom')\n", encoding="utf-8")
    assert cli.main(["check", str(broken), write_file(tmp_path)]) == 1
    printed = capsys.readouterr().out
    assert "could not be imported" in printed
    assert "REFUTED false_claim" in printed


def test_the_check_verb_reads_a_namespace_with_one_file(tmp_path, capsys) -> None:
    """``loopty check`` builds a namespace with ``file`` and hands it to the verb."""
    import argparse

    text = FILE.split("@theorem\ndef false_claim")[0]
    namespace = argparse.Namespace(file=write_file(tmp_path, text), json=None, verbose=False)
    assert cli.CheckVerb().run(namespace) == 0
    printed = capsys.readouterr().out
    assert "==>" not in printed
    assert "1 facts: 1 tested" in printed


PLAIN = """
from lanky.plugins import registry


class Plain:
    def __init__(self, label, path=None):
        self.label = label
        self.path = path
        registry.register_object(self)


Plain("here", __file__)
Plain("elsewhere", "/nowhere/else.py")
Plain("unrecorded")
"""


def test_an_object_with_no_function_is_placed_by_the_path_its_fact_records(
    tmp_path, monkeypatch
) -> None:
    """A plugin's object that wraps no function is placed by its facts.

    A fact recording another file is not this file's claim; one recording no
    path at all is kept, because nothing says it was written anywhere else and
    a claim the ledger drops is a claim nobody sees.
    """
    from lanky.ledger import Fact
    from lanky.plugins import registry

    class PlainTheory:
        name = "plain"

        def facts(self, obj, /):
            if type(obj).__name__ != "Plain":
                return ()
            provenance = {"path": obj.path} if obj.path else {}
            return (
                Fact(
                    id=f"plain:{obj.label}",
                    kind="plain",
                    statement=obj.label,
                    provenance=provenance,
                    owner=obj.label,
                ),
            )

    registry.load_entry_points()
    monkeypatch.setattr(registry, "theories", [*registry.theories, PlainTheory()])
    path = tmp_path / "plain.py"
    path.write_text(PLAIN, encoding="utf-8")
    assert [fact.owner for fact in check_path(path)] == ["here", "unrecorded"]


def _package(tmp_path, name: str, init: str = "") -> tuple:
    """``project/<name>/`` with a helper, a module using it, and a subpackage."""
    root = tmp_path / "project" / name
    (root / "sub").mkdir(parents=True)
    (root / "__init__.py").write_text(init, encoding="utf-8")
    (root / "helpers.py").write_text(HELPER + "\nVALUE = 2\n", encoding="utf-8")
    (root / "sub" / "__init__.py").write_text("", encoding="utf-8")
    header = (
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n"
    )
    mod = root / "mod.py"
    mod.write_text(
        header
        + "\nfrom . import helpers\nfrom .helpers import VALUE, helper_claim  # noqa: F401\n\n\n"
        "@theorem\ndef mod_claim(n: Nat) -> n * helpers.VALUE == n + n:\n"
        '    """Uses what a relative import brought in."""\n',
        encoding="utf-8",
    )
    deep = root / "sub" / "deep.py"
    deep.write_text(
        header + "\nfrom ..helpers import VALUE\n\n\n"
        "@theorem\ndef deep_claim(n: Nat) -> n + VALUE > n:\n"
        '    """Two levels down."""\n',
        encoding="utf-8",
    )
    return mod, deep


def test_a_file_inside_a_package_can_import_relatively(tmp_path) -> None:
    """``from .helpers import ...`` in ``pkg/mod.py`` works under ``lanky check``.

    The file was loaded as a top-level module with an empty ``__package__``,
    so a relative import failed with "attempted relative import with no known
    parent package" and the check reported an import failure. The module
    keeps its own name and is given its package; ``__spec__.parent`` agrees
    with ``__package__``, so the import system does not warn about the pair.
    """
    import sys
    import warnings

    from lanky.check import import_path
    from lanky.plugins import registry

    name = "lanky_test_pkg"
    mod, deep = _package(tmp_path, name)
    path_before = list(sys.path)
    try:
        with warnings.catch_warnings():
            warnings.filterwarnings("error", message="__package__ != __spec__")
            assert [fact.owner for fact in check_path(mod)] == ["mod_claim"]
            assert [fact.owner for fact in check_path(deep)] == ["deep_claim"]
            with registry.collecting():
                module = import_path(mod)
                deeper = import_path(deep)
        assert module.__name__ == "lanky_checked_mod"
        assert module.__package__ == module.__spec__.parent == name
        assert deeper.__package__ == deeper.__spec__.parent == f"{name}.sub"
        assert sys.path == path_before
        assert f"{name}.helpers" in sys.modules
    finally:
        for key in [key for key in sys.modules if key.split(".")[0] == name]:
            sys.modules.pop(key, None)


def test_a_package_that_imports_the_checked_file_does_not_double_its_claims(tmp_path) -> None:
    """The package's own copy of the checked file is not this check's.

    When ``pkg/__init__.py`` imports ``pkg.mod`` and the checked ``pkg/mod.py``
    imports relatively, the first check runs the file twice, once as the
    package's submodule and once under the check's own name, and both copies
    register the same theorem from the same file. Only the copy the check
    executed is collected, so the first ledger is the second one.
    """
    import sys

    name = "lanky_test_pkg_imports_mod"
    mod, _deep = _package(tmp_path, name, init="from . import mod  # noqa: F401\n")
    try:
        first = [fact.owner for fact in check_path(mod)]
        assert f"{name}.mod" in sys.modules
        second = [fact.owner for fact in check_path(mod)]
        assert first == second == ["mod_claim"]
    finally:
        for key in [key for key in sys.modules if key.split(".")[0] == name]:
            sys.modules.pop(key, None)


def test_a_package_init_is_checked_in_its_own_package(tmp_path) -> None:
    """``pkg/__init__.py`` resolves ``.helpers`` in ``pkg``, and its claim is collected once.

    Its relative import imports ``pkg``, which runs the same ``__init__.py``
    again under the package's name; that copy's theorem is not this check's.
    """
    import sys

    name = "lanky_test_pkg_init"
    init = (
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n"
        "from .helpers import VALUE\n\n\n"
        "@theorem\n"
        "def init_claim(n: Nat) -> n + VALUE > n:\n"
        '    """Written in the package itself."""\n'
    )
    mod, _deep = _package(tmp_path, name, init=init)
    try:
        first = [fact.owner for fact in check_path(mod.parent / "__init__.py")]
        assert name in sys.modules
        second = [fact.owner for fact in check_path(mod.parent / "__init__.py")]
        assert first == second == ["init_claim"]
    finally:
        for key in [key for key in sys.modules if key.split(".")[0] == name]:
            sys.modules.pop(key, None)


def test_a_package_of_the_same_name_from_another_tree_is_refused(tmp_path) -> None:
    """``check_path`` must not check ``b/pkg/mod.py`` with ``a/pkg/mod.py``'s modules.

    The first file's relative import leaves ``pkg`` and ``pkg.helpers`` in
    ``sys.modules``, and a relative import resolves through that cache before
    it looks at ``sys.path``, so the second file's ``from . import helpers``
    was answered by the first tree. In one process the second file is refused
    instead, with the reason, and the first tree's package can still be
    checked again.
    """
    import sys

    name = "lanky_test_twin"
    first, _deep = _package(tmp_path / "a", name)
    second, _deep = _package(tmp_path / "b", name)
    try:
        assert [fact.owner for fact in check_path(first)] == ["mod_claim"]
        with pytest.raises(ImportError) as refusal:
            check_path(second)
        assert str(refusal.value).startswith(
            f"{second.resolve()} sits in the package {name!r}, but "
            f"{name!r} is already imported from {first.parent.resolve()} in this process"
        )
        assert [fact.owner for fact in check_path(first)] == ["mod_claim"]
    finally:
        for key in [key for key in sys.modules if key.split(".")[0] == name]:
            sys.modules.pop(key, None)


def test_the_cli_checks_twin_packages_in_processes_of_their_own(
    tmp_path, monkeypatch, capsys
) -> None:
    """``lanky check b/pkg/mod.py a/pkg/mod.py`` checks each file in its own tree.

    The command used to check both in one process, where the second was
    refused (see above) and the check failed on a file that is fine. The two
    have different source roots, so each is now checked in a child process of
    its own, and neither sees the other's package, nor the one this process
    imported before the command ran.
    """
    import sys

    # The two ledgers are found by their summaries, which read "1 proved"
    # rather than "1 tested" where Lean is installed.
    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    name = "lanky_test_twin_cli"
    first, _deep = _package(tmp_path / "a", name)
    second, _deep = _package(tmp_path / "b", name)
    try:
        assert [fact.owner for fact in check_path(first)] == ["mod_claim"]
        assert cli.main(["check", str(second), str(first)]) == 0
        printed = capsys.readouterr().out
        assert "could not be imported" not in printed
        assert printed.startswith(f"==> {second} <==\n")
        assert f"\n\n==> {first} <==\n" in printed
        assert printed.count("1 facts: 1 tested") == 2
    finally:
        for key in [key for key in sys.modules if key.split(".")[0] == name]:
            sys.modules.pop(key, None)


# {{{ files from several source roots

ROOTS_HELPER = "lanky_test_roots_helpers"

ROOTED = f'''
"""A claim about the helper module in this file's directory."""

from __future__ import annotations

import os
import sys

import {ROOTS_HELPER} as helpers

from lanky import theorem
from lanky.prelude import Nat

print("imported in process", os.getpid())
print("a line on stderr", file=sys.stderr)


@theorem
def own_helper(n: Nat) -> n * helpers.VALUE == VALUE * n:
    """True of the helper next to this file, and of no other."""
'''


def _rooted(directory, value: int, name: str = "claims"):
    """``directory/<name>.py``, claiming that the helper beside it holds ``value``.

    Every directory's helper has the one module name, so a file checked with
    another directory's helper has its claim refuted at ``n = 1``.
    """
    directory.mkdir(parents=True, exist_ok=True)
    (directory / f"{ROOTS_HELPER}.py").write_text(f"VALUE = {value}\n", encoding="utf-8")
    path = directory / f"{name}.py"
    path.write_text(ROOTED.replace("== VALUE * n", f"== {value} * n"), encoding="utf-8")
    return path


def _pids(printed: str) -> list[int]:
    """The process ids the checked files printed, in the order they printed them."""
    return [
        int(line.rsplit(" ", 1)[1])
        for line in printed.splitlines()
        if line.startswith("imported in process ")
    ]


def test_source_roots_are_the_directories_a_check_puts_on_sys_path(tmp_path) -> None:
    from lanky.check import source_roots

    plain = _rooted(tmp_path / "plain", 1)
    mod, deep = _package(tmp_path, "lanky_test_roots_pkg")
    project = (tmp_path / "project").resolve()
    assert source_roots(plain) == (plain.parent.resolve(),)
    assert source_roots(mod) == (mod.parent.resolve(), project)
    assert source_roots(deep) == (deep.parent.resolve(), project)
    assert source_roots(mod.parent / "helpers.py") == source_roots(mod)


def test_files_from_two_roots_are_checked_against_their_own_helpers(
    tmp_path, monkeypatch, capsys
) -> None:
    """The reproduction of #9: each directory's ``claims.py`` imports its own ``helpers``.

    Checked one after another in one process, the second file's import found
    the first directory's module in ``sys.modules``, and its claim was
    refuted against code it does not contain, whichever order the files were
    listed in. Each root is now checked in a process of its own, so both
    claims are tested, and ``--json`` holds both files' facts, in the order
    their ledgers were printed.
    """
    import sys
    from pathlib import Path

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    first = _rooted(tmp_path / "a", 1)
    second = _rooted(tmp_path / "b", 2)
    out_json = tmp_path / "ledger.json"
    try:
        for files in ([first, second], [second, first]):
            code = cli.main(["check", *map(str, files), "--json", str(out_json)])
            captured = capsys.readouterr()
            assert "REFUTED" not in captured.out
            assert code == 0
            assert captured.out.startswith(f"==> {files[0]} <==\n")
            assert f"\n\n==> {files[1]} <==\n" in captured.out
            assert captured.out.count("1 facts: 1 tested") == 2
            assert captured.err.count("a line on stderr\n") == 2
            data = json.loads(out_json.read_text(encoding="utf-8"))
            assert [(entry["owner"], entry["status"]) for entry in data] == [
                ("own_helper", "tested"),
                ("own_helper", "tested"),
            ]
            assert [Path(entry["provenance"]["path"]) for entry in data] == [
                files[0].resolve(),
                files[1].resolve(),
            ]
        assert ROOTS_HELPER not in sys.modules
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_each_root_is_checked_in_one_process_of_its_own(tmp_path, monkeypatch, capsys) -> None:
    """One child process per distinct source root, and the ledgers printed root by root.

    ``a/x.py b/y.py a/z.py`` starts two processes, one for ``a`` and one for
    ``b``, neither of them this one; ``a``'s files share theirs and are
    printed first, in the order they were listed. The oracles are listed once,
    by this process, and each child prints its facts as it collects them.
    """
    import os
    import sys

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    x = _rooted(tmp_path / "a", 1, "x")
    y = _rooted(tmp_path / "b", 2, "y")
    z = _rooted(tmp_path / "a", 1, "z")
    try:
        assert cli.main(["check", str(x), str(y), str(z), "--verbose"]) == 0
        printed = capsys.readouterr().out
        headings = [line for line in printed.splitlines() if line.startswith("==> ")]
        assert headings == [f"==> {x} <==", f"==> {z} <==", f"==> {y} <=="]
        pids = _pids(printed)
        assert len(pids) == 3
        assert pids[0] == pids[1] != pids[2]
        assert os.getpid() not in pids
        assert printed.count("property-test (test): available") == 1
        assert printed.count(" own_helper: n : Nat |- ") == 3
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_files_of_one_root_are_checked_in_this_process(tmp_path, monkeypatch, capsys) -> None:
    """Files that share their roots are checked as they always were: here, one after another."""
    import os
    import sys

    def refuse(_spec_path):
        raise AssertionError("no child process is started for a single root")

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    monkeypatch.setattr(cli, "_start_child", refuse)
    x = _rooted(tmp_path / "a", 1, "x")
    z = _rooted(tmp_path / "a", 1, "z")
    try:
        assert cli.main(["check", str(x), str(z)]) == 0
        printed = capsys.readouterr().out
        assert _pids(printed) == [os.getpid(), os.getpid()]
        assert printed.count("1 facts: 1 tested") == 2
        assert sys.modules[ROOTS_HELPER].VALUE == 1  # imported here, and still imported
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_a_root_whose_process_stops_is_reported_and_the_others_checked(
    tmp_path, monkeypatch, capsys
) -> None:
    """A checked file that ends its process fails the check, with a line, and stops nothing else.

    ``sys.exit`` while the file is imported used to end ``lanky check`` itself,
    with the file's exit code and without the files after it. With several
    roots it ends the child checking its root, before that child reports, and
    the command says so and goes on to the next root.
    """
    import sys

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    stops = tmp_path / "a" / "stops.py"
    stops.parent.mkdir()
    stops.write_text("raise SystemExit(3)\n", encoding="utf-8")
    good = _rooted(tmp_path / "b", 2)
    try:
        assert cli.main(["check", str(stops), str(good)]) == 1
        printed = capsys.readouterr().out
        assert (
            f"lanky check: the process checking {stops} stopped with exit code 3 "
            "before it reported\n"
        ) in printed
        assert printed.count("1 facts: 1 tested") == 1
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_a_root_whose_process_cannot_start_is_reported(tmp_path, monkeypatch, capsys) -> None:
    """A child that cannot be started fails the check with a line, and the next root is tried."""
    import sys

    started = []
    start = cli._start_child

    def start_all_but_the_first(spec_path):
        started.append(spec_path)
        if len(started) == 1:
            raise OSError("no processes left")
        return start(spec_path)

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    monkeypatch.setattr(cli, "_start_child", start_all_but_the_first)
    first = _rooted(tmp_path / "a", 1)
    second = _rooted(tmp_path / "b", 2)
    try:
        assert cli.main(["check", str(first), str(second)]) == 1
        printed = capsys.readouterr().out
        assert printed.startswith(
            f"lanky check: could not start a process to check {first}: no processes left\n\n"
            f"==> {second} <==\n"
        )
        assert printed.count("1 facts: 1 tested") == 1
        assert len(started) == 2
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_a_childs_output_is_copied_as_text_whatever_its_bytes() -> None:
    """A byte that is not UTF-8 is copied as its escape, and line endings as they came."""
    import io

    sink = io.StringIO()
    cli._copy_lines(io.BytesIO(b"caf\xc3\xa9\n\xff\r\nlast"), sink)
    assert sink.getvalue() == "café\n\\xff\r\nlast"
    cli._copy_lines(io.BytesIO(b"nowhere\n"), None)  # drained, not written

    # A character the sink cannot encode is escaped too, rather than failing the write.
    ascii_sink = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
    cli._copy_lines(io.BytesIO(b"caf\xc3\xa9\nplain\n"), ascii_sink)
    ascii_sink.flush()
    assert ascii_sink.buffer.getvalue() == b"caf\\xe9\nplain\n"


def test_exit_codes_and_json_merge_across_roots(tmp_path, monkeypatch, capsys) -> None:
    """Each root's verdict and facts come back to the one command, in the order printed.

    A refutation in one child fails the check as it would in one process, and
    so does a file another child could not import; a root that passes changes
    neither. ``--json`` holds the facts of the files that imported, and each
    is what a check of that file alone writes.
    """
    import sys

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    good = _rooted(tmp_path / "good", 1)
    bad = _rooted(tmp_path / "bad", 1)
    (bad.parent / f"{ROOTS_HELPER}.py").write_text("VALUE = 3\n", encoding="utf-8")
    broken = tmp_path / "broken" / "claims.py"
    broken.parent.mkdir()
    broken.write_text("def broken(:\n", encoding="utf-8")
    out_json = tmp_path / "ledger.json"
    alone = tmp_path / "alone.json"
    try:
        assert cli.main(["check", str(good), str(bad), str(broken), "--json", str(out_json)]) == 1
        printed = capsys.readouterr().out
        assert printed.count("1 facts: 1 tested") == 1
        assert printed.count("1 facts: 1 refuted") == 1
        assert "REFUTED own_helper at claims.py:" in printed
        assert f"lanky check: {broken} could not be imported" in printed
        assert "SyntaxError" in printed
        data = json.loads(out_json.read_text(encoding="utf-8"))
        assert [(entry["owner"], entry["status"]) for entry in data] == [
            ("own_helper", "tested"),
            ("own_helper", "refuted"),
        ]
        for file, entry in zip((good, bad), data, strict=True):
            sys.modules.pop(ROOTS_HELPER, None)
            cli.main(["check", str(file), "--json", str(alone)])
            assert json.loads(alone.read_text(encoding="utf-8")) == [entry]

        assert cli.main(["check", str(broken), str(good)]) == 1
        other = _rooted(tmp_path / "other", 2)
        assert cli.main(["check", str(good), str(other)]) == 0
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def test_a_child_may_print_what_this_process_cannot_encode(tmp_path, monkeypatch) -> None:
    """A checked file that prints a character this process's output refuses stops nothing.

    The child writes UTF-8 whatever the locale, and this process's output may
    be ASCII (``PYTHONIOENCODING=ascii``, say). Writing the line as it came
    raised ``UnicodeEncodeError`` here, which ended the whole command and left
    the next root unchecked; the character is escaped instead.
    """
    import io
    import sys

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    accented = tmp_path / "a" / "accented.py"
    accented.parent.mkdir()
    accented.write_text("print('caf\\u00e9')\n", encoding="utf-8")
    good = _rooted(tmp_path / "b", 2)
    out = io.TextIOWrapper(io.BytesIO(), encoding="ascii", newline="")
    monkeypatch.setattr(sys, "stdout", out)
    try:
        assert cli.main(["check", str(accented), str(good)]) == 0
        out.flush()
        printed = out.buffer.getvalue().decode("ascii")
        assert "caf\\xe9\n" in printed
        assert printed.count("1 facts: 1 tested") == 1
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


def _sleeper(script: str):
    """A Python child running ``script``, with both output streams piped here."""
    import subprocess
    import sys

    return subprocess.Popen(
        [sys.executable, "-c", script], stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )


def test_a_failing_stderr_does_not_stall_a_child(monkeypatch) -> None:
    """The thread copying standard error keeps reading when ``sys.stderr`` fails.

    It died at the first failed write, and a child writing more than a pipe
    holds to its standard error then blocked for good, while this process
    waited for its standard output to end.
    """
    import errno
    import io
    import sys
    import threading

    class Closed:
        encoding = "utf-8"

        def write(self, text):
            raise OSError(errno.EPIPE, "Broken pipe")

    out = io.StringIO()
    monkeypatch.setattr(sys, "stdout", out)
    monkeypatch.setattr(sys, "stderr", Closed())
    child = _sleeper(
        "import sys\n"
        "for i in range(20000):\n"
        "    print('e' * 60, file=sys.stderr)\n"
        "print('done')\n"
    )
    returned = []
    follow = threading.Thread(target=lambda: returned.append(cli._follow(child)), daemon=True)
    follow.start()
    follow.join(timeout=30)
    if follow.is_alive():
        child.kill()
        follow.join(timeout=10)
        pytest.fail("the child blocked on its standard error")
    assert returned == [0]
    assert out.getvalue() == "done\n"


def test_a_copy_that_fails_kills_the_child(monkeypatch) -> None:
    """When this process cannot copy a child's output, the child is killed and reaped.

    It used to be left checking for no one, with this process waiting on it at
    the end of ``with``, whose closing of the standard error pipe blocks until
    the thread reading it sees the child's last line.
    """
    import sys
    import time

    class Closed:
        encoding = "utf-8"

        def write(self, text):
            raise BrokenPipeError(32, "Broken pipe")

    monkeypatch.setattr(sys, "stdout", Closed())
    child = _sleeper("import time\nprint('ready', flush=True)\ntime.sleep(30)\n")
    started = time.monotonic()
    with pytest.raises(BrokenPipeError):
        cli._follow(child)
    assert time.monotonic() - started < 20
    assert child.returncode is not None and child.returncode != 0


def test_check_path_imports_into_the_calling_process(tmp_path, monkeypatch) -> None:
    """The API keeps one process, as documented: the command is what keeps roots apart.

    After ``check_path`` of the first directory's file, the second file's
    ``import helpers`` finds the first directory's module, and its claim is
    refuted against it.
    """
    import sys

    monkeypatch.setenv("LANKY_LEAN_DISABLE", "1")
    first = _rooted(tmp_path / "a", 1)
    second = _rooted(tmp_path / "b", 2)
    try:
        assert [fact.status for fact in check_path(first)] == [Status.TESTED]
        assert [fact.status for fact in check_path(second)] == [Status.REFUTED]
        assert sys.modules[ROOTS_HELPER].VALUE == 1
    finally:
        sys.modules.pop(ROOTS_HELPER, None)


# }}}


# {{{ what is printed under a REFUTED line


def _refuted(**provenance) -> Fact:
    """A refuted fact carrying exactly this provenance."""
    return Fact(
        id="theorem:claim",
        kind="theorem",
        statement="n : Nat |- n == n + 1",
        status=Status.REFUTED,
        decided_by="an-oracle",
        where="claims.py:7",
        owner="claim",
        provenance=provenance,
    )


def _block(capsys, fact: Fact) -> list[str]:
    """The lines ``lanky check`` prints under the fact's ``REFUTED`` line."""
    assert cli.CheckVerb._report(Ledger([fact])) is True
    printed = capsys.readouterr().out
    head = "REFUTED claim at claims.py:7: n : Nat |- n == n + 1"
    assert head in printed
    return printed.split(head, 1)[1].splitlines()[1:]


def test_a_refutation_with_a_reason_and_no_counterexample_prints_the_reason(
    capsys,
) -> None:
    """loopty's trace fact is refuted with a reason and no assignment to show.

    Only a fact with a ``counterexample`` got anything under its line, so the
    reason, which names the fix, was in the JSON alone, and loopty put an empty
    counterexample into the fact to have it printed.
    """
    fact = _refuted(reason="TraceError: the body branches on a loop index")
    assert _block(capsys, fact) == ["  TraceError: the body branches on a loop index"]
    assert cli.refutation_lines(fact) == ["TraceError: the body branches on a loop index"]
    # a reason of several lines is indented line by line under the REFUTED line
    fact = _refuted(reason="TraceError: the body branches\nwrite 'with when(...):' instead")
    assert _block(capsys, fact) == [
        "  TraceError: the body branches",
        "  write 'with when(...):' instead",
    ]


def test_a_refutation_prints_its_counterexample_and_then_its_reason(capsys) -> None:
    """The counterexample is printed as before, and the reason follows it."""
    fact = _refuted(
        counterexample={"n": 0},
        reason="the goal is false at this assignment",
    )
    assert _block(capsys, fact) == [
        "  counterexample: {'n': 0}",
        "  the goal is false at this assignment",
    ]


def test_a_refutation_with_only_a_counterexample_is_printed_as_before(capsys) -> None:
    assert _block(capsys, _refuted(counterexample={"n": 0})) == [
        "  counterexample: {'n': 0}"
    ]


def test_an_empty_counterexample_is_not_printed(capsys) -> None:
    """``{}`` names nothing; the reason beside it is what explains the fact."""
    fact = _refuted(counterexample={}, reason="false at no assignment in particular")
    assert _block(capsys, fact) == ["  false at no assignment in particular"]


def test_a_refutation_that_records_nothing_says_so(capsys) -> None:
    """A bare REFUTED line must not read as explained somewhere below it."""
    assert _block(capsys, _refuted()) == ["  no witness recorded"]
    assert _block(capsys, _refuted(counterexample={}, reason="")) == [
        "  no witness recorded"
    ]


def test_a_witness_is_printed_whichever_plugin_recorded_it(capsys) -> None:
    """``witness`` is a standard key, and printed like the counterexample (#20).

    loopty's isl oracle records one, and it counted against "no witness
    recorded" without being printed, so a refuted in-bounds fact came out with
    an empty block and the cell that escapes was in the JSON alone. A plugin's
    own keys, such as ``witness_text``, are still not lanky's to print.
    """
    fact = _refuted(witness=((0, 8), (1, 7)), witness_text="[t=0, i=8] -> [t=1, i=7]")
    assert _block(capsys, fact) == ["  witness: ((0, 8), (1, 7))"]
    # a term in the provenance is printed, and not asked for its truth value
    assert cli.refutation_lines(_refuted(witness=Var("n"))) == ["witness: n"]


def test_the_standard_keys_are_printed_in_one_order(capsys) -> None:
    """The counterexample and the witness, then the reason that talks about them."""
    fact = _refuted(
        reason="S0[t=0, i=8] runs before S0[t=1, i=7], which reads what it writes",
        witness="S0[t=0, i=8] -> S0[t=1, i=7]",
        counterexample={"n": 16},
    )
    assert _block(capsys, fact) == [
        "  counterexample: {'n': 16}",
        "  witness: S0[t=0, i=8] -> S0[t=1, i=7]",
        "  S0[t=0, i=8] runs before S0[t=1, i=7], which reads what it writes",
    ]


def test_a_witness_of_several_lines_is_indented_line_by_line(capsys) -> None:
    fact = _refuted(witness="S0[t=0, i=8]\nS0[t=1, i=7]")
    assert _block(capsys, fact) == ["  witness: S0[t=0, i=8]", "  S0[t=1, i=7]"]


def test_an_empty_witness_is_not_printed(capsys) -> None:
    """An empty witness names nothing, as an empty counterexample does not."""
    assert _block(capsys, _refuted(witness=(), reason="the pair was not kept")) == [
        "  the pair was not kept"
    ]
    assert _block(capsys, _refuted(witness="", counterexample={})) == [
        "  no witness recorded"
    ]


# }}}


# {{{ facts rest on facts

CITED = '''
"""An axiom, and a theorem that rests on it."""

from __future__ import annotations

from lanky import axiom, theorem
from lanky.prelude import Fin, Nat


@theorem
def gauss(n: Nat) -> 2 * sum(i for i in Fin[n + 1]) == n * (n + 1):
    """Gauss."""


@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")
def nicomachus(n: Nat) -> sum(i**3 for i in Fin[n + 1]) == sum(i for i in Fin[n + 1]) ** 2:
    """The sum of the first cubes is the square of the sum of the first numbers."""


@theorem(uses=[nicomachus, gauss])
def cubes(n: Nat) -> 4 * sum(i**3 for i in Fin[n + 1]) == (n * (n + 1)) ** 2:
    """The sum of the cubes, in closed form."""
'''


def test_a_theorem_resting_on_an_axiom_is_worth_the_axiom(tmp_path, capsys) -> None:
    """The axiom is ``assumed`` on its citation; the theorem is tested under it.

    Every statement here has a sum in it, which core Lean cannot print, so the
    ledger is the same with Lean and without it.
    """
    path = write_file(tmp_path, CITED)
    ledger = check_path(path)
    gauss, nicomachus, cubes = ledger
    assert nicomachus.kind == "axiom"
    assert nicomachus.status is Status.ASSUMED
    assert nicomachus.decided_by is None
    assert nicomachus.provenance["cite"] == "Nicomachus of Gerasa, Introduction to Arithmetic"
    # sampled for a counterexample, and nothing of a pass is kept
    assert "valid" not in nicomachus.provenance
    assert cubes.status is Status.TESTED
    assert cubes.rests_on == (nicomachus.id, gauss.id)
    assert ledger.support(cubes).effective is Status.ASSUMED
    assert ledger.support(cubes).under == (nicomachus.id,)
    assert ledger.support(gauss).effective is Status.TESTED

    out = tmp_path / "out.json"
    assert cli.main(["check", path, "--json", str(out)]) == 0
    lines = capsys.readouterr().out.splitlines()
    assert lines[0].split()[:3] == ["STATUS", "EFFECTIVE", "BY"]
    assert lines[2].startswith("tested                   tested     property-test")
    assert lines[3].startswith("assumed (axiom)          assumed    -")
    assert lines[4].startswith("tested under nicomachus  assumed    property-test")
    assert lines[6] == "3 facts: 1 assumed, 2 tested"
    assert lines[7:] == [
        "",
        f"CITED nicomachus at {nicomachus.where}: "
        "Nicomachus of Gerasa, Introduction to Arithmetic",
    ]
    data = json.loads(out.read_text(encoding="utf-8"))
    assert [(row["owner"], row["status"], row["effective"], row["under"]) for row in data] == [
        ("gauss", "tested", "tested", []),
        ("nicomachus", "assumed", "assumed", []),
        ("cubes", "tested", "assumed", [nicomachus.id]),
    ]
    assert data[2]["rests_on"] == [nicomachus.id, gauss.id]
    assert data[1]["provenance"]["cite"] == "Nicomachus of Gerasa, Introduction to Arithmetic"


def test_an_axiom_false_as_written_is_refuted(tmp_path, capsys) -> None:
    """A citation copied down wrong is caught, and fails the check.

    The cube became a square on one side. The reference says nothing of the
    sort, and the property tester's counterexample is definite whatever the
    citation says; what rests on the axiom is worth a refutation.
    """
    cube = "sum(i**3 for i in Fin[n + 1]) =="
    path = write_file(tmp_path, CITED.replace(cube, cube.replace("**3", "**2"), 1))
    ledger = check_path(path)
    _gauss, nicomachus, cubes = ledger
    assert nicomachus.status is Status.REFUTED
    assert nicomachus.decided_by == "property-test"
    assert nicomachus.provenance["cite"] == "Nicomachus of Gerasa, Introduction to Arithmetic"
    assert nicomachus.provenance["counterexample"]
    assert ledger.support(cubes).effective is Status.REFUTED

    assert cli.main(["check", path]) == 1
    printed = capsys.readouterr().out
    assert "\nrefuted (axiom)  " in printed
    assert "tested under nicomachus  refuted    property-test" in printed
    assert "REFUTED nicomachus at claims.py:" in printed
    assert "  counterexample: {'n': " in printed
    # the reference is where to look for what was copied down wrong
    assert "\nCITED nicomachus at claims.py:" in printed


def test_an_axiom_is_never_offered_to_a_stronger_oracle(tmp_path, monkeypatch) -> None:
    """Whatever a prover would say of an axiom, it is not asked.

    An oracle stronger than a test that establishes everything it is shown
    would make the axiom ``proved``; it proves the theorem, and never sees the
    axiom.
    """
    from lanky.plugins import registry

    shown: list[str] = []

    class ProvesEverything:
        name = "proves-everything"

        def trust_class(self) -> str:
            return "kernel"

        def can_establish(self, fact, /) -> bool:
            return True

        def establish(self, fact, /):
            shown.append(fact.kind)
            return fact.with_status(Status.PROVED, self.name)

    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, ProvesEverything()])
    _gauss, nicomachus, cubes = check_path(write_file(tmp_path, CITED))
    assert nicomachus.status is Status.ASSUMED
    assert cubes.status is Status.PROVED
    assert "axiom" not in shown
    assert shown.count("theorem") >= 2


def test_a_plugin_fact_rests_on_another_facts_id(tmp_path) -> None:
    """``rests_on`` is set by whoever builds the fact, and read off the ledger."""
    post = Fact(id="scan:postcondition", kind="postcondition", statement="...", owner="scan")
    restated = Fact(
        id="program:solve:scan:postcondition",
        kind="postcondition-in-scope",
        statement="after scan(...) in solve: ...",
        owner="solve",
        rests_on=(post.id,),
    )
    bounds = Fact(
        id="scan:bounds", kind="in-bounds", statement="...", status=Status.DECIDED, owner="scan"
    )
    ledger = Ledger([post, restated, bounds])
    assert ledger.support(restated).under == ("scan:postcondition",)
    row = ledger.render().splitlines()[3]
    # the kernel owns many facts, so the one meant is named by its id
    assert row.startswith("assumed under scan:postcondition  -")


SPELLED = (
    CITED
    + '''

@theorem(uses=[cubes, "theorem:helpers.lemma@12", "theorem:helpers.lemma@12"])
def spelled(n: Nat) -> n + 0 == n:
    """Rests on a fact of this file, and on an id no fact here has."""
'''
)


def test_an_id_no_fact_in_the_ledger_has_is_named_under_the_table(tmp_path, capsys) -> None:
    """A ``uses=`` string that names nothing is an assumption, and is said to be one.

    It is sound to count it as ``assumed``, and the row does, but in the row
    it reads like any other assumption, and a misspelt id would pass for one.
    So the check names it under the table, once, under the fact that rests on
    it, and the exit code stays 0, because an id of another file's fact is
    this case too and is not a mistake.
    """
    path = write_file(tmp_path, SPELLED)
    out = tmp_path / "out.json"
    assert cli.main(["check", path, "--json", str(out)]) == 0
    printed = capsys.readouterr().out.splitlines()
    (index,) = [i for i, line in enumerate(printed) if line.startswith("UNRESOLVED")]
    assert printed[index].startswith("UNRESOLVED spelled at claims.py:")
    assert printed[index].endswith(
        ": rests on theorem:helpers.lemma@12, which this ledger does not hold"
    )
    assert printed[index + 1] == (
        "  counted as an assumption; a fact of another file is in that file's ledger, "
        "not this one"
    )
    rows = json.loads(out.read_text(encoding="utf-8"))
    nicomachus = rows[1]["id"]
    assert rows[-1]["rests_on"] == [rows[2]["id"], "theorem:helpers.lemma@12"]
    assert rows[-1]["under"] == [nicomachus, "theorem:helpers.lemma@12"]
    assert rows[-1]["effective"] == "assumed"
    # a file whose facts rest on facts it holds prints no such line
    assert cli.main(["check", write_file(tmp_path, CITED)]) == 0
    assert "UNRESOLVED" not in capsys.readouterr().out


def test_the_quickstart_shows_the_ledger_nicomachus_prints(capsys) -> None:
    """The quickstart's table for ``examples/nicomachus.py`` is the real one.

    Every statement in the file has a sum in it, which core Lean cannot print,
    so the table is the same with Lean and without it, and both CI jobs hold
    the document to it.
    """
    from pathlib import Path

    root = Path(__file__).resolve().parent.parent
    lines = (root / "docs" / "quickstart.md").read_text(encoding="utf-8").splitlines()
    start = lines.index("$ uv run lanky check examples/nicomachus.py")
    shown = []
    for line in lines[start + 1 :]:
        if line.startswith(("$ ", "```")):
            break
        shown.append(line)
    assert cli.main(["check", str(root / "examples" / "nicomachus.py")]) == 0
    printed = [line.rstrip() for line in capsys.readouterr().out.splitlines()]
    assert shown == printed


# }}}


# {{{ what stands behind a decision: a citation, a trust class


def test_lanky_check_prints_each_axioms_citation_under_the_table(tmp_path, capsys) -> None:
    """The citation is what stands behind an ``assumed (axiom)`` row, so it is shown.

    It used to be in the JSON alone. A citation of several lines is indented
    under its first, and a file with no axiom prints no ``CITED`` line.
    """
    text = CITED.replace(
        '@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic")',
        '@axiom(cite="Nicomachus of Gerasa, Introduction to Arithmetic,\\nbook II, ch. 20")',
    )
    path = write_file(tmp_path, text)
    _gauss, nicomachus, _cubes = check_path(path)
    assert cli.main(["check", path]) == 0
    lines = capsys.readouterr().out.splitlines()
    summary = lines.index("3 facts: 1 assumed, 2 tested")
    assert lines[summary + 1 :] == [
        "",
        f"CITED nicomachus at {nicomachus.where}: "
        "Nicomachus of Gerasa, Introduction to Arithmetic,",
        "  book II, ch. 20",
    ]

    assert cli.main(["check", write_file(tmp_path)]) == 1
    assert "CITED" not in capsys.readouterr().out


def test_the_oracle_that_settles_a_fact_leaves_its_trust_class(tmp_path) -> None:
    """The status says what kind of evidence; ``trust_class`` says how far to trust its decider."""
    true_claim, false_claim = check_path(write_file(tmp_path))
    assert true_claim.provenance["trust_class"] == "test"
    assert false_claim.provenance["trust_class"] == "test"


class Simplifier:
    """A heuristic that decides every theorem it is shown, as a careless simplifier might."""

    name = "simplifier"

    def trust_class(self) -> str:
        return "heuristic"

    def can_establish(self, fact, /) -> bool:
        return fact.kind == "theorem"

    def establish(self, fact, /):
        return fact.with_status(Status.DECIDED, self.name)


def test_a_fact_a_heuristic_decides_is_marked_in_the_table_and_the_json(
    tmp_path, monkeypatch, capsys
) -> None:
    """A heuristic is asked before the property tester, and its ``decided`` says what it is.

    Before the ``heuristic`` class existed, an oracle naming it ranked below
    the tester, which refuted ``false_claim`` before the simplifier was asked.
    Now the simplifier is asked first, and the tester still refutes
    ``false_claim``: a counterexample overrules a heuristic's answer, which is
    not guaranteed, and the provenance says whose answer it overruled.
    """
    from lanky.plugins import registry

    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, Simplifier()])
    path = write_file(tmp_path)
    true_claim, false_claim = check_path(path)
    assert (true_claim.status, true_claim.decided_by) == (Status.DECIDED, "simplifier")
    assert true_claim.provenance["trust_class"] == "heuristic"
    assert true_claim.is_heuristic
    assert (false_claim.status, false_claim.decided_by) == (Status.REFUTED, "property-test")
    assert false_claim.provenance["trust_class"] == "test"
    assert not false_claim.is_heuristic
    assert false_claim.provenance["overruled"] == "simplifier, a heuristic, decided it"
    assert "n" in false_claim.provenance["counterexample"]
    out = tmp_path / "out.json"
    assert cli.main(["check", path, "--json", str(out)]) == 1
    printed = capsys.readouterr().out
    lines = printed.splitlines()
    assert lines[2].startswith("decided (heuristic)  simplifier")
    assert lines[3].startswith("refuted              property-test")
    heading = f"REFUTED false_claim at {false_claim.where}: {false_claim.statement}"
    block = lines[lines.index(heading) :]
    assert block[1:4] == [
        f"  counterexample: {false_claim.provenance['counterexample']}",
        "  the goal is false at this assignment",
        "  simplifier, a heuristic, decided it, and this draw overrules it",
    ]
    data = json.loads(out.read_text(encoding="utf-8"))
    assert [row["provenance"]["trust_class"] for row in data] == ["heuristic", "test"]


class Hasty:
    """A heuristic that decides every theorem it is shown, the false ones too."""

    name = "hasty"

    def trust_class(self) -> str:
        return "heuristic"

    def can_establish(self, fact, /) -> bool:
        return fact.kind == "theorem"

    def establish(self, fact, /):
        return fact.with_status(Status.DECIDED, self.name)


CLOSED_FACTS = '''
from __future__ import annotations

import pymbolic.primitives as prim

from lanky.ledger import Fact
from lanky.plugins import registry
from lanky.rewrites import Rewrite


class Closed(Rewrite):
    """Two statements with no variable and no hypothesis in them, one false."""

    def facts(self):
        return (
            Fact(id="closed:true", kind="theorem", statement="1 - 2 < 0",
                 term=prim.Comparison(prim.Sum((1, -2)), "<", 0), owner="true_closed"),
            Fact(id="closed:false", kind="theorem", statement="1 - 2 >= 0",
                 term=prim.Comparison(prim.Sum((1, -2)), ">=", 0), owner="false_closed"),
        )


def nothing():
    return None, None


claims = registry.register_object(Closed(nothing))
'''


def test_a_counterexample_overrules_a_heuristic_where_nothing_else_would_look(
    tmp_path, monkeypatch
) -> None:
    """A statement with no hypotheses and no semantics gap is sampled after a heuristic too.

    Only such facts are cross-checked after a decision procedure or a kernel,
    and there a counterexample is only recorded. After a heuristic every fact
    is sampled, and a counterexample stands in place of its answer.
    """
    from lanky.plugins import registry

    registry.load_entry_points()
    # Lean, where it is installed, proves the true statement before the
    # heuristic is asked, which is right and beside the point here.
    tester = [oracle for oracle in registry.oracles if oracle.trust_class() == "test"]
    monkeypatch.setattr(registry, "oracles", [*tester, Hasty()])
    true_closed, false_closed = check_path(write_file(tmp_path, CLOSED_FACTS))
    assert (true_closed.status, true_closed.decided_by) == (Status.DECIDED, "hasty")
    assert "overruled" not in true_closed.provenance
    assert (false_closed.status, false_closed.decided_by) == (Status.REFUTED, "property-test")
    assert false_closed.provenance["overruled"] == "hasty, a heuristic, decided it"


class Flaky:
    """A tester whose draws pass the first time it is asked, and refute every time after."""

    name = "flaky-test"

    def __init__(self) -> None:
        self.asked = 0

    def trust_class(self) -> str:
        return "test"

    def can_establish(self, fact, /) -> bool:
        return fact.kind == "theorem"

    def establish(self, fact, /):
        self.asked += 1
        if self.asked == 1:
            return fact.with_status(Status.TESTED, self.name, samples=1, valid=1)
        return fact.with_status(
            Status.REFUTED, self.name, counterexample={"n": 0}, reason="drawn again"
        )


GUARDED = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Nat


@theorem
def guarded(n: Nat, h: n >= 1) -> n + 0 == n:
    """Its hypothesis holds at almost every draw."""
'''


def test_a_heuristics_answer_is_sampled_once(tmp_path, monkeypatch) -> None:
    """One sample both looks for a counterexample and says what is recorded.

    A fact with hypotheses that a heuristic established used to be sampled
    for a counterexample, and then sampled again to record what sampling
    says about the hypotheses. A tester seeded afresh, or one that keeps
    state, can pass the first time and refute the second, and that
    refutation was only recorded, leaving the heuristic's answer standing
    and the check passing.
    """
    from lanky.plugins import registry

    flaky = Flaky()
    monkeypatch.setattr(registry, "oracles", [flaky, Hasty()])
    (fact,) = check_path(write_file(tmp_path, GUARDED))
    assert flaky.asked == 1
    assert (fact.status, fact.decided_by) == (Status.DECIDED, "hasty")
    assert "semantics_disagreement" not in fact.provenance


class Leaning:
    """A heuristic that decides every theorem, on a lemma it names and a reason it gives."""

    name = "leaning"

    def trust_class(self) -> str:
        return "heuristic"

    def can_establish(self, fact, /) -> bool:
        return fact.kind == "theorem"

    def establish(self, fact, /):
        from dataclasses import replace

        leaning = replace(fact, rests_on=(*fact.rests_on, "lemma"))
        return leaning.with_status(Status.DECIDED, self.name, detail="by the lemma")


def test_what_a_heuristic_added_goes_with_its_overruled_answer(tmp_path, monkeypatch) -> None:
    """The refutation is the tester's, of the fact as it was handed over.

    A heuristic's answer can come with what it rests on and why; once a
    counterexample overrules it, neither is what the refuted fact rests on,
    and only ``overruled`` says what the heuristic had answered.
    """
    from lanky.plugins import registry

    registry.load_entry_points()
    tester = [oracle for oracle in registry.oracles if oracle.trust_class() == "test"]
    monkeypatch.setattr(registry, "oracles", [*tester, Leaning()])
    true_claim, false_claim = check_path(write_file(tmp_path))
    assert (true_claim.status, true_claim.rests_on) == (Status.DECIDED, ("lemma",))
    assert true_claim.provenance["detail"] == "by the lemma"
    assert (false_claim.status, false_claim.decided_by) == (Status.REFUTED, "property-test")
    assert false_claim.rests_on == ()
    assert "detail" not in false_claim.provenance
    assert false_claim.provenance["overruled"] == "leaning, a heuristic, decided it"


class RashSimplifier:
    """A heuristic that says every set of hypotheses is inconsistent."""

    name = "rash-simplifier"

    def trust_class(self) -> str:
        return "heuristic"

    def can_establish(self, fact, /) -> bool:
        return fact.kind == "hypotheses"

    def establish(self, fact, /):
        return fact.with_status(Status.PROVED, self.name)


RARE = '''
from __future__ import annotations

from lanky import theorem
from lanky.prelude import Nat


@theorem
def rare(n: Nat, h: n == 1000) -> n + 0 == n:
    """Its hypothesis holds only where the sampler does not look."""
'''


def test_a_heuristic_is_not_enough_to_make_a_fact_vacuous(tmp_path, monkeypatch, capsys) -> None:
    """A vacuous fact fails the check, and a heuristic's answer is not guaranteed.

    A counterexample overrules a heuristic elsewhere, and where no draw
    satisfies the hypotheses there is none to be had. So only a decision
    procedure or a kernel is asked whether the hypotheses are inconsistent,
    and here the fact keeps its warning.
    """
    from lanky.plugins import registry

    registry.load_entry_points()
    monkeypatch.setattr(registry, "oracles", [*registry.oracles, RashSimplifier()])
    path = write_file(tmp_path, RARE)
    (fact,) = check_path(path)
    assert not fact.is_vacuous
    assert fact.provenance["unsatisfied"]
    assert cli.main(["check", path]) == 0
    assert "WARNING rare at claims.py:" in capsys.readouterr().out


# }}}
