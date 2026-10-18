"""The multipliers a step was closed with, kept so that a warm check runs no sympy.

The design idea. A step of a written proof, ``return f, g``, is closed by
``linear_combination`` with multipliers that Python finds: sympy's linear
algebra over the step's terms (:func:`lanky.proofs.report.combination`). The
search is the slow part of compiling a proof, and the multipliers are part of
the Lean source, which is the proof cache's key. So the multipliers found for
each step are kept here, keyed by the step: its claim, the facts at their
points, and the sorts of its names, as text. A check of a file that has not
changed finds every step's multipliers here, runs no sympy, and writes the
same Lean source as the check that found them, which Lean's answer is then
read back for.

Nothing rests on a hint. Lean checks the combination the multipliers make,
so a hint that is wrong, stale or tampered with costs a failed step and never
a wrong proof; a hint the cache cannot read is a miss. A step for which the
search found no multipliers is kept too, as ``None``, so that it is not
searched again either; the key carries lanky's version, so a search that
improves in a later version is asked again.

The cache is a directory beside the proof cache, ``hints`` in it
(:func:`lanky.oracles.lean.default_proof_cache_dir`), and is off when the
proof cache is (``LANKY_LEAN_PROOF_CACHE=off``). A multiplier is a lanky
term, kept as JSON: numbers, names, and the nodes of :mod:`lanky.terms` and
:mod:`pymbolic.primitives`, each by its class and its constructor's
arguments. Only classes of those two modules are read back.
"""

from __future__ import annotations

import hashlib
import json
import os
from collections.abc import Mapping, Sequence
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

__all__ = ["HintCache", "default_hint_dir", "hint_key", "decode", "encode"]

#: The format the hints are kept in; a change makes every kept hint a miss.
FORMAT = 1

#: The modules a kept node's class may come from.
_MODULES = ("lanky.terms", "pymbolic.primitives")


class Unencodable(ValueError):
    """A multiplier the cache cannot keep, which is then searched for again next time."""


def encode(value: Any) -> Any:
    """``value`` as JSON: a number, a name, a tuple, or a node of a term by class and arguments."""
    if value is None or isinstance(value, bool):
        if isinstance(value, bool):
            return {"b": value}
        return None
    if isinstance(value, int):
        return value
    if isinstance(value, float):
        return {"f": value.hex()}
    if isinstance(value, Fraction):
        return {"q": [value.numerator, value.denominator]}
    if isinstance(value, complex):
        return {"c": [value.real.hex(), value.imag.hex()]}
    if isinstance(value, str):
        return {"s": value}
    if isinstance(value, tuple):
        return {"t": [encode(item) for item in value]}
    if isinstance(value, prim.ExpressionNode):
        from lanky.terms import init_args

        cls = type(value)
        if cls.__module__ not in _MODULES:
            raise Unencodable(f"a {cls.__module__}.{cls.__qualname__} is not kept")
        return {"n": f"{cls.__module__}:{cls.__qualname__}", "a": encode(tuple(init_args(value)))}
    raise Unencodable(f"a {type(value).__name__} is not kept")


def decode(data: Any) -> Any:
    """The value :func:`encode` gave ``data`` for; ``ValueError`` for anything else."""
    if data is None or isinstance(data, int) and not isinstance(data, bool):
        return data
    if not isinstance(data, dict) or len(data) not in (1, 2):
        raise ValueError("not a kept value")
    if "b" in data:
        return bool(data["b"])
    if "f" in data:
        return float.fromhex(data["f"])
    if "q" in data:
        numerator, denominator = data["q"]
        return Fraction(int(numerator), int(denominator))
    if "c" in data:
        real, imag = data["c"]
        return complex(float.fromhex(real), float.fromhex(imag))
    if "s" in data:
        if not isinstance(data["s"], str):
            raise ValueError("not a name")
        return data["s"]
    if "t" in data:
        return tuple(decode(item) for item in data["t"])
    if "n" in data:
        module, _, qualname = str(data["n"]).partition(":")
        if module not in _MODULES or not qualname.isidentifier():
            raise ValueError(f"{data['n']} is not a class a hint may name")
        import importlib

        cls = getattr(importlib.import_module(module), qualname, None)
        if not (isinstance(cls, type) and issubclass(cls, prim.ExpressionNode)):
            raise ValueError(f"{data['n']} is not a node of a term")
        arguments = decode(data.get("a", {"t": []}))
        if not isinstance(arguments, tuple):
            raise ValueError("a node's arguments are a tuple")
        return cls(*arguments)
    raise ValueError("not a kept value")


def hint_key(claim: Any, bodies: Sequence[Any], types: Mapping[str, Any]) -> str:
    """The key of one step's multipliers: its claim, its facts and its names' sorts, as text."""
    from lanky import __version__
    from lanky.terms import render

    text = json.dumps(
        {
            "format": FORMAT,
            "lanky": __version__,
            "claim": render(claim),
            "facts": [render(body) for body in bodies],
            "types": sorted((str(name), str(sort)) for name, sort in types.items()),
        },
        sort_keys=True,
    )
    return hashlib.sha256(text.encode()).hexdigest()


#: What :meth:`HintCache.get` returns for a step it keeps nothing of.
MISSING = object()


class HintCache:
    """The multipliers found for each step, kept in a directory (see the module)."""

    def __init__(self, directory: str | None) -> None:
        self.directory = directory

    def _path(self, key: str) -> str | None:
        if not self.directory:
            return None
        return os.path.join(self.directory, key[:2], f"{key}.json")

    def get(self, key: str) -> Any:
        """The multipliers kept for ``key``, a tuple or ``None``; :data:`MISSING` for none kept."""
        path = self._path(key)
        if path is None:
            return MISSING
        try:
            with open(path, encoding="utf-8") as handle:
                record = json.load(handle)
            if not isinstance(record, dict) or record.get("key") != key:
                return MISSING
            found = decode(record.get("multipliers"))
        except (OSError, ValueError, TypeError, KeyError):
            return MISSING
        if found is not None and not isinstance(found, tuple):
            return MISSING
        return found

    def put(self, key: str, multipliers: Sequence[Any] | None) -> None:
        """Keep ``multipliers`` for ``key``; nothing where they cannot be kept, or written."""
        path = self._path(key)
        if path is None:
            return
        try:
            data = encode(None if multipliers is None else tuple(multipliers))
            if multipliers is not None and not _reads_back(data, multipliers):
                return
            os.makedirs(os.path.dirname(path), exist_ok=True)
            temporary = f"{path}.{os.getpid()}.tmp"
            with open(temporary, "w", encoding="utf-8") as handle:
                json.dump({"key": key, "multipliers": data}, handle)
            os.replace(temporary, path)
        except (OSError, Unencodable, ValueError, TypeError):
            return


def _reads_back(data: Any, multipliers: Sequence[Any]) -> bool:
    """Whether the kept form of ``multipliers`` reads back as terms that print the same."""
    from lanky.terms import render

    try:
        again = decode(data)
    except (ValueError, TypeError):
        return False
    if not isinstance(again, tuple) or len(again) != len(multipliers):
        return False
    return all(
        _text(render, first) == _text(render, second)
        for first, second in zip(again, multipliers, strict=True)
    )


def _text(render: Any, value: Any) -> str:
    """A multiplier as text: a term rendered, a number as Python writes it."""
    return render(value) if isinstance(value, prim.ExpressionNode) else repr(value)


def default_hint_dir() -> str | None:
    """Where the hints are kept: ``hints`` in the proof cache's directory; ``None`` when off."""
    from lanky.oracles.lean import default_proof_cache_dir

    directory = default_proof_cache_dir()
    return None if directory is None else os.path.join(directory, "hints")
