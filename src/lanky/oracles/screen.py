"""The screen for Lean text lanky did not write itself.

The design idea. Almost all the Lean the oracle sends is printed by lanky,
from a statement and a script lanky built. Two kinds of text are not: a
script a user pins with :func:`lanky.oracles.lean.use_tactic`, and the Lean
proofs of :mod:`lanky.known`, which are written by hand once and kept in a
table (:mod:`lanky.oracles.known`). Either is pasted after ``:= by`` in the
theorem lanky prints, and either could, by accident or not, say something
other than a proof of that theorem: end the file early with ``#exit``, so
that a later check never runs; turn the kernel's checking off with an
option; declare an axiom; or prove the goal with ``native_decide``, which
trusts the compiler rather than the kernel.

So the text is screened before Lean sees it, by the words it uses
(:func:`screen`). What it refuses:

- any ``#`` command (``#exit``, ``#print``, ``#eval``), anywhere in the text;
- ``set_option``, except ``set_option maxHeartbeats N in`` in a library proof,
  which only gives one step more time;
- the words that extend Lean or the environment: ``run_tac``, ``elab``,
  ``elab_rules``, ``macro``, ``macro_rules``, ``syntax``, ``notation``,
  ``axiom``, ``unsafe``, ``native_decide``;
- the words that open or close a scope or declare something: ``namespace``,
  ``section``, ``end``, ``open``, ``theorem``, ``lemma``, ``def``,
  ``abbrev``, ``instance``, ``attribute``, ``import``, ``initialize``.

A library proof is held to more: it may not leave a hole (``sorry``,
``admit``), and it may not open a block comment, which left open would hide
everything after it.

The screen reads words, not Lean's grammar, so it refuses some text Lean
would read harmlessly, a ``#`` inside a comment, say. That costs a rewording
at worst. It cannot see everything a metaprogram could do, which is why the
oracle's positive axiom audit stays the backstop.
"""

from __future__ import annotations

import re

__all__ = ["REFUSED_WORDS", "screen"]

#: The words a screened text may not use, each a token on its own: ``end`` is
#: refused, ``Finset.sum_def`` and ``Foo.end`` are not.
REFUSED_WORDS = frozenset(
    {
        "set_option",
        "run_tac",
        "elab",
        "elab_rules",
        "macro",
        "macro_rules",
        "syntax",
        "notation",
        "axiom",
        "unsafe",
        "native_decide",
        "namespace",
        "section",
        "end",
        "open",
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "attribute",
        "import",
        "initialize",
    }
)

#: The holes a library proof may not leave.
_HOLES = frozenset({"sorry", "admit"})

#: A word as Lean reads one: a name, dotted or not, with its primes and marks.
_WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*")

#: A ``#`` command: a ``#`` followed by a letter, anywhere.
_COMMAND = re.compile(r"#[A-Za-z_]")

#: The one option a library proof may set, for the step that follows it.
_HEARTBEATS = re.compile(r"\bset_option\s+maxHeartbeats\s+\d+\s+in\b")


def screen(text: str, *, library: bool = False) -> str | None:
    """Why ``text`` may not be sent to Lean as a proof; ``None`` if it may.

    ``library=True`` screens a proof of :mod:`lanky.known`, which may set
    ``maxHeartbeats`` for a step and may not leave a hole or open a block
    comment. The reason names the first word refused, in the user's terms.
    """
    if not isinstance(text, str):
        return f"a proof is Lean text, not {type(text).__name__}"
    command = _COMMAND.search(text)
    if command is not None:
        word = _WORD.match(text, command.start() + 1)
        name = f"#{word.group(0)}" if word else command.group(0)
        return f"it runs the command {name}, and a proof runs no command"
    if library:
        if "/-" in text:
            return "it opens a block comment, which left open would hide what follows"
        text = _HEARTBEATS.sub(" ", text)
    for word in _WORD.findall(text):
        if word in REFUSED_WORDS:
            if word == "set_option":
                allowed = (
                    "; a library proof may only give a step more time, with "
                    "set_option maxHeartbeats N in"
                    if library
                    else ""
                )
                return f"it sets an option of Lean's{allowed}"
            return f"it uses {word}, which a proof does not need and may not use"
        if library and word in _HOLES:
            return f"it leaves a hole ({word}), and a library proof leaves none"
    return None
