"""Mathlib mode: the Lake project the Lean oracle runs in when it may import Mathlib.

The design idea. Core Lean is the default because it costs nothing: the oracle
builds a small REPL once and needs no project at all. Mathlib is several
gigabytes of compiled files and a Lake project to find them in, so it is opt-in,
and the switch names the project: ``LANKY_LEAN_MATHLIB=DIR``. When it is unset,
nothing here is consulted and the oracle behaves exactly as it does without
this module. When it is set, the oracle starts its REPL with ``lake env`` in
``DIR``, imports Mathlib once, elaborates every attempt in that environment,
and prints statements in the Mathlib dialect (see :mod:`lanky.lean`), which
takes ``Real``, ``Complex``, reductions, absolute values, true division and
``exp``, ``log`` and ``sqrt``.

The project is pinned, and lanky ships it. ``lakefile.toml`` requires Mathlib at
the release tag for one Lean toolchain, ``lean-toolchain`` names that
toolchain, and ``lake-manifest.json`` pins Mathlib and every one of its
dependencies to a commit, so two machines that set the project up get the same
Mathlib. The toolchain has to be one the REPL lean-interact drives has a build
for, which rules out the newest Lean releases; :data:`MATHLIB_REVISION` is the
one lanky's CI uses for core Lean as well.

Setting it up is one command, :func:`main`, and then the variable::

    python -m lanky.mathlib ~/.cache/lanky/mathlib
    export LANKY_LEAN_MATHLIB=~/.cache/lanky/mathlib

The command writes the three files and runs ``lake exe cache get``, which clones
Mathlib and fetches its compiled files (about 7 GB on disk, a few minutes). It
never builds Mathlib from source, which would take hours: a project whose cache
fetch failed is reported as not ready (:func:`problem`) rather than built.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
from pathlib import Path

__all__ = [
    "ENVIRONMENT_VARIABLE",
    "MATHLIB_REVISION",
    "PROJECT_FILES",
    "TEMPLATE",
    "TOOLCHAIN",
    "fetch_cache",
    "main",
    "problem",
    "project_directory",
    "revision",
    "write_project",
]

#: The environment variable that turns Mathlib mode on, by naming the project.
ENVIRONMENT_VARIABLE = "LANKY_LEAN_MATHLIB"

#: The directory the pinned project's files are shipped in.
TEMPLATE = Path(__file__).resolve().parent / "mathlib-project"

#: The files that make up the pinned project.
PROJECT_FILES = ("lakefile.toml", "lean-toolchain", "lake-manifest.json")

#: The Mathlib release the project requires, which is the tag of the Lean
#: release it is built for.
MATHLIB_REVISION = "v4.29.1"

#: The Lean toolchain the project, and so the REPL, runs on.
TOOLCHAIN = f"leanprover/lean4:{MATHLIB_REVISION}"


def project_directory() -> str | None:
    """The project Mathlib mode is to run in, or ``None`` when the mode is off.

    Read from :data:`ENVIRONMENT_VARIABLE` when asked, not when lanky is
    imported, so a process that sets it before its first Lean fact gets Mathlib
    mode. An empty value is off, as an unset one is.
    """
    return os.environ.get(ENVIRONMENT_VARIABLE) or None


def problem(directory: str | os.PathLike[str]) -> str | None:
    """Why ``directory`` is not a Lake project Mathlib mode can run in, or ``None``.

    Cheap, and asked before a REPL is started: a directory that does not exist,
    a project without a toolchain, and one whose Mathlib was never fetched are
    each named, with what to run. That the compiled files are really there is
    not checked file by file; importing Mathlib is the check, and its failure
    is reported by the session.
    """
    path = Path(directory).expanduser()
    fix = f"run `python -m lanky.mathlib {directory}` to set it up"
    if not path.is_dir():
        return f"{ENVIRONMENT_VARIABLE} names {directory}, which is not a directory; {fix}"
    if not (path / "lean-toolchain").is_file():
        return f"{directory} has no lean-toolchain, so it is not a Lake project; {fix}"
    if not (path / ".lake" / "packages" / "mathlib").is_dir():
        return f"{directory} has no Mathlib under .lake/packages; {fix}"
    return None


def revision(directory: str | os.PathLike[str]) -> str | None:
    """The Mathlib revision a project's manifest pins, as ``tag (commit)``.

    This is what a proof found in Mathlib mode records in its provenance, so
    that it can be replayed against the same library. ``None`` when the
    manifest cannot be read or does not mention Mathlib.
    """
    manifest = Path(directory).expanduser() / "lake-manifest.json"
    try:
        packages = json.loads(manifest.read_text(encoding="utf-8")).get("packages", ())
    except (OSError, ValueError, AttributeError):
        return None
    for package in packages:
        if isinstance(package, dict) and package.get("name") == "mathlib":
            tag, commit = package.get("inputRev"), package.get("rev")
            if tag and commit:
                return f"{tag} ({commit})"
            return tag or commit
    return None


def write_project(directory: str | os.PathLike[str]) -> Path:
    """Write the pinned project into ``directory``, creating it if need be.

    The three files are copied as lanky ships them. A file already there with
    other contents is overwritten: the point of the project is to be the
    pinned one, and a hand-edited manifest would silently be another Mathlib.
    What Lake keeps under ``.lake`` is left alone, so running this again on a
    fetched project costs nothing.
    """
    path = Path(directory).expanduser()
    path.mkdir(parents=True, exist_ok=True)
    for name in PROJECT_FILES:
        shutil.copyfile(TEMPLATE / name, path / name)
    return path


def fetch_cache(directory: str | os.PathLike[str], lake: str = "lake") -> int:
    """Fetch Mathlib's compiled files into a project with ``lake exe cache get``.

    Lake clones Mathlib and its dependencies at the commits the manifest pins
    first, which is the network part; then the cache tool downloads and unpacks
    the compiled files. Its output goes to the terminal, since it is a long
    command and says how far it has got. Returns its exit code.
    """
    try:
        return subprocess.run(
            [lake, "exe", "cache", "get"], cwd=Path(directory).expanduser(), check=False
        ).returncode
    except FileNotFoundError:
        print(f"{lake} is not on PATH: install elan and the {TOOLCHAIN} toolchain first")
        return 127


def main(argv: list[str] | None = None) -> int:
    """``python -m lanky.mathlib DIR``: write the pinned project, fetch the cache.

    Exit code 0 when the project is ready, with the line that turns Mathlib
    mode on; otherwise the cache tool's exit code, or 1 when the project is
    still not ready after it ran.
    """
    parser = argparse.ArgumentParser(
        prog="python -m lanky.mathlib",
        description=(
            "Set up the Lake project lanky's Lean oracle imports Mathlib from: "
            f"Mathlib {MATHLIB_REVISION} on {TOOLCHAIN}, pinned."
        ),
    )
    parser.add_argument("directory", help="where to put the project (created if missing)")
    parser.add_argument(
        "--no-fetch",
        action="store_true",
        help="only write the project files; do not run `lake exe cache get`",
    )
    parser.add_argument("--lake", default="lake", help="the lake executable to run")
    args = parser.parse_args(argv)
    path = write_project(args.directory)
    print(f"wrote the pinned Mathlib project ({MATHLIB_REVISION}) to {path}", flush=True)
    if args.no_fetch:
        return 0
    code = fetch_cache(path, args.lake)
    if code != 0:
        print(f"`lake exe cache get` exited with {code}")
        return code
    reason = problem(path)
    if reason is not None:
        print(reason)
        return 1
    print(f"ready: export {ENVIRONMENT_VARIABLE}={path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
