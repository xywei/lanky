"""Checking a file: import it, collect facts, run oracles, exit on a refutation."""

from __future__ import annotations

import json

from lanky import cli
from lanky.check import check_path, oracle_lines
from lanky.ledger import Status

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


def test_a_semantics_gap_is_recorded_and_cross_checked(tmp_path, monkeypatch) -> None:
    """``n - 1 >= 0`` is true in Lean and false in Python at ``n = 0``.

    Whatever establishes it, the ledger has to say that the statement has two
    readings. With no Lean here the property tester refutes it outright; with
    Lean it is proved and the disagreement is recorded instead. Both are
    honest, and neither is silent.
    """
    from lanky.semantics import NAT_SUBTRACTION

    path = tmp_path / "gap.py"
    path.write_text(
        "from __future__ import annotations\n\n"
        "from __future__ import annotations\n\n"
        "from lanky import theorem\n"
        "from lanky.prelude import Nat\n\n\n"
        "@theorem\n"
        "def truncated(n: Nat) -> n - 1 >= 0:\n"
        '    """Nat subtraction truncates in Lean and goes negative in Python."""\n',
        encoding="utf-8",
    )
    ledger = check_path(path)
    (fact,) = list(ledger)
    assert NAT_SUBTRACTION in fact.provenance["semantics"]
    if fact.status is Status.REFUTED:
        assert fact.provenance["counterexample"] == {"n": 0}
    else:
        assert fact.status is Status.PROVED
        assert fact.provenance["semantics_counterexample"] == {"n": 0}


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
    code = cli.main(["check", str(path)])
    printed = capsys.readouterr().out
    assert code == 1
    assert "REFUTED impossible" in printed
    # empty on purpose, and printed rather than dropped: no assignment is what
    # makes this statement false
    assert "counterexample: {}" in printed
    assert "constant False" in printed


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


def test_the_cli_checks_a_neighbour_when_it_is_listed(tmp_path, capsys) -> None:
    """``lanky check main.py helper.py`` is how two files are checked together.

    Each file gets its own ledger under a heading, since a fact id is unique
    within one file's ledger and not across files, and each claim is checked
    once: the helper's theorem under the helper, whichever order the files
    are listed in. ``--json`` writes one list of both files' facts.
    """
    import sys

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
