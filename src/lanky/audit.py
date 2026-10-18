"""What a Lean command has to answer before lanky takes it as a proof, and what it may hold.

The design idea. Lean's kernel checks every declaration it accepts, but it
accepts more than proofs. A declaration closed by ``sorry`` is accepted with
a warning, one closed by ``native_decide`` rests on an axiom that trusts the
compiler, and a command can stop Lean before anything after it runs, or
declare the theorem lanky asked for in another namespace. Lean reports no
error in any of these, so "no error" is not enough to call a claim proved.

So every command lanky sends ends with an *axiom audit*, one ``#print axioms``
per theorem the command declares (:func:`audit_lines`), named from the root,
``#print axioms _root_.Lanky.compressed_taylor``, so that no namespace the
command opened can make the name mean another theorem. lanky takes the
command as a proof only on a positive answer (:func:`audit_failure`): for each
name, exactly one message, about exactly that theorem, that says either that
it depends on axioms among :data:`TRUSTED_AXIOMS` or that it depends on none.

- A missing answer is a failure. A command that stops Lean before the audit,
  ``#exit`` or a block comment left open, has none; nor has a command whose
  theorem was declared in another namespace, whose audit Lean answers about
  ``'Decoy.Lanky.t'`` or not at all.
- ``sorryAx``, and the axiom ``native_decide`` adds for each use (in Lean
  v4.29.1 named like ``Lanky.t._native.native_decide.ax_1_1``), are not
  trusted, so a theorem resting on either fails the audit.
- The audit does not see a kernel check turned off, ``set_option
  debug.skipKernelTC``, or a metaprogram that adds declarations the kernel
  never checks. That is why the raw text a user hands Lean is screened
  first (:func:`screen`).

The audit is what lanky writes after the theorem, at the start of a line,
and a proof's tactics never start a line there (each line of a script is
indented under ``:= by``). So :func:`audited` reads which theorems a command
audits from the command itself, and a session asks for the positive answer
of every command it sends (:meth:`lanky.oracles.lean.LeanSession.answer`).

*The screen.* ``use_tactic`` hands Lean a script as it was written, and so
will the Lean proofs of lanky's library of known facts. A script is the proof
that follows ``:= by``; lanky writes every command around it. The screen
refuses what a proof never needs and a command around it could use to say
something else: any ``#`` command, ``set_option`` (except ``set_option
maxHeartbeats ... in`` in the library's proofs), the words that define syntax
or run metaprograms, ``axiom``, ``unsafe``, ``native_decide`` and the other
ways to ask the compiler, the words that open, close or declare in a
namespace, and a block comment left open. The positive audit is the backstop
for anything the list misses.
"""

from __future__ import annotations

import re
from collections.abc import Collection, Sequence

__all__ = [
    "REFUSED_WORDS",
    "TRUSTED_AXIOMS",
    "audit_failure",
    "audit_lines",
    "audited",
    "refusal",
    "screen",
]

#: The axioms a proof may rest on: Lean's own, which Mathlib rests on too.
TRUSTED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})

#: How lanky's audit of a theorem starts a line (see :func:`audit_lines`).
_AUDIT = "#print axioms _root_."

#: Lean's answer to ``#print axioms``: the theorem, then its axioms or none.
_ANSWER = re.compile(
    r"\A'(?P<name>.*)' (?:depends on axioms: \[(?P<axioms>[^\]]*)\]"
    r"|does not depend on any axioms)\s*\Z",
    re.DOTALL,
)


def audit_lines(names: Sequence[str]) -> str:
    """The audit lanky ends a command with: ``#print axioms _root_.<name>``, a line each.

    ``names`` are the theorems the command declares, as the command declares
    them (``Lanky.compressed_taylor``, ``Lanky.«fun»``), in the order they
    are declared.
    """
    return "\n".join(f"{_AUDIT}{name}" for name in names)


def audited(source: str) -> tuple[str, ...]:
    """The theorems the audit at the end of ``source`` asks about, in order; ``()`` for none.

    The audit is the lines at the end of the command that start with
    ``#print axioms _root_.``, which only lanky writes there: every line of a
    tactic script is indented under ``:= by`` (:meth:`lanky.lean.LeanStatement.source`).
    """
    names: list[str] = []
    for line in reversed(source.rstrip().splitlines()):
        if not line.strip():
            continue
        if not line.startswith(_AUDIT):
            break
        names.append(line[len(_AUDIT) :].strip())
    return tuple(reversed(names))


def declares(source: str) -> bool:
    """Whether ``source`` declares a theorem at the start of a line, as lanky's commands do."""
    return re.search(r"^theorem\s", source, re.MULTILINE) is not None


def _plain(name: str) -> str:
    """A Lean name without its quotation marks: ``Lanky.«fun»`` is ``Lanky.fun``.

    Lean prints a name in a message with or without them as it pleases, and
    no name lanky declares has a component with a dot in it, which is the one
    thing the quotation marks could have told apart.
    """
    return name.replace("«", "").replace("»", "")


def audit_failure(
    messages: Sequence[str], names: Sequence[str], allowed: Collection[str] = TRUSTED_AXIOMS
) -> str | None:
    """Why Lean's answers do not pass the audit of ``names``; ``None`` when they do.

    ``messages`` are the texts of every message Lean gave the command. Each
    name needs exactly one answer about exactly that theorem (see the module
    docstring), resting on nothing beyond :data:`TRUSTED_AXIOMS`, or beyond
    ``allowed``: a written proof with steps left open, ``by(...)``, which
    closes "with holes", may rest on ``sorryAx`` as well, and reads assumed
    (:mod:`lanky.proofs`).
    """
    answers: dict[str, list[tuple[str, ...]]] = {}
    for message in messages:
        found = _ANSWER.match(str(message).strip())
        if found is None:
            continue
        said = found.group("axioms")
        axioms = tuple(
            part.strip() for part in (said or "").replace("\n", " ").split(",") if part.strip()
        )
        answers.setdefault(_plain(found.group("name")), []).append(axioms)
    for name in names:
        got = answers.get(_plain(name), [])
        if not got:
            return (
                f"Lean did not answer the axiom audit of {name}: something in the "
                "command stopped Lean before it, or declared the theorem under "
                "another name"
            )
        if len(got) > 1:
            return (
                f"Lean answered the axiom audit of {name} {len(got)} times, where lanky asked once"
            )
        untrusted = [axiom for axiom in got[0] if axiom not in allowed]
        if untrusted:
            listing = ", ".join(untrusted)
            return (
                f"{name} rests on {listing}, which lanky does not take as proof: a "
                "proof rests on propext, Classical.choice and Quot.sound at most"
            )
    return None


# {{{ the screen

#: The words a proof never needs and a command around it could use (see the
#: module docstring). ``native`` covers ``decide +native``, and
#: ``ofReduceBool`` and ``trustCompiler`` the axioms the compiler's answers
#: rest on.
_REFUSED_WORDS = (
    "run_tac",
    "run_cmd",
    "run_elab",
    "run_meta",
    "elab",
    "elab_rules",
    "macro",
    "macro_rules",
    "syntax",
    "notation",
    "infix",
    "infixl",
    "infixr",
    "prefix",
    "postfix",
    "axiom",
    "unsafe",
    "native_decide",
    "native",
    "ofReduceBool",
    "trustCompiler",
    "implemented_by",
    "extern",
    "namespace",
    "section",
    "end",
    "open",
    "export",
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "instance",
    "example",
    "structure",
    "inductive",
    "class",
    "opaque",
    "attribute",
    "import",
    "initialize",
    "builtin_initialize",
    "set_option",
)

#: A character a Lean name can have, which a refused word must not touch on
#: either side: ``update_def`` and ``Nat.end`` are names, not the words.
_NAME_CHARACTER = r"[A-Za-z0-9_.'!?«»]"

_WORD = re.compile(
    rf"(?<!{_NAME_CHARACTER})(?P<word>{'|'.join(sorted(_REFUSED_WORDS, key=len, reverse=True))})"
    rf"(?!{_NAME_CHARACTER})"
)

#: The words a screened script may not use, each a token on its own: ``end``
#: is refused, ``Finset.sum_def`` and ``Foo.end`` are not.
REFUSED_WORDS = frozenset(_REFUSED_WORDS)

#: The holes a library proof may not leave: its claim reads proved on its
#: proof alone, and a hole would make that a failure on every check.
_HOLE = re.compile(rf"(?<!{_NAME_CHARACTER})(?P<word>sorry|admit)(?!{_NAME_CHARACTER})")

#: ``set_option maxHeartbeats N in``, which a library proof may use to give a
#: slow step its time, and nothing else may.
_HEARTBEATS = re.compile(
    rf"(?<!{_NAME_CHARACTER})set_option\s+maxHeartbeats\s+\d+\s+in(?!{_NAME_CHARACTER})"
)

#: The names whose axioms trust the compiler, refused wherever they stand, a
#: component of a longer name included: ``Lean.ofReduceBool``.
_COMPILER = re.compile(r"ofReduceBool|ofReduceNat|trustCompiler|native_decide|implemented_by")

#: A ``#`` command, ``#exit``, ``#print``, ``#eval``: a ``#`` and a name.
_COMMAND = re.compile(r"#\s*[A-Za-z_]")


def _without_comments(script: str) -> tuple[str, bool]:
    """``script`` with its comments blanked, and whether a block comment is left open.

    A line comment runs to the end of its line, and a block comment, ``/-
    ... -/``, nests, as Lean reads them. What a comment says is not read by
    Lean, so it is not screened; a block comment left open swallows
    everything after it, the audit included, so it is refused.
    """
    out: list[str] = []
    depth = 0
    index = 0
    while index < len(script):
        if script.startswith("/-", index):
            depth += 1
            index += 2
            continue
        if depth and script.startswith("-/", index):
            depth -= 1
            index += 2
            continue
        if depth:
            out.append("\n" if script[index] == "\n" else " ")
            index += 1
            continue
        if script.startswith("--", index):
            end = script.find("\n", index)
            end = len(script) if end < 0 else end
            out.append(" " * (end - index))
            index = end
            continue
        out.append(script[index])
        index += 1
    return "".join(out), depth > 0


def screen(script: str, library: bool = False) -> str | None:
    """Why ``script`` cannot be handed to Lean as a proof; ``None`` when it can.

    ``library`` is for the Lean proofs of lanky's library of known facts,
    :mod:`lanky.known`, which may give a slow step its time with ``set_option
    maxHeartbeats N in``, and may not leave a hole (``sorry``, ``admit``).
    The reason names what was found, in the words of the script; what to
    write instead is :func:`refusal`'s.
    """
    refused = refusal(script, library)
    return None if refused is None else refused[0]


#: What to write instead of a word the screen refuses, by what the word does.
_DECLARING = frozenset(
    {
        "theorem",
        "lemma",
        "def",
        "abbrev",
        "instance",
        "example",
        "structure",
        "inductive",
        "class",
        "opaque",
    }
)
_SCOPING = frozenset({"namespace", "section", "end", "export"})
_SYNTAX = frozenset(
    {
        "run_tac",
        "run_cmd",
        "run_elab",
        "run_meta",
        "elab",
        "elab_rules",
        "macro",
        "macro_rules",
        "syntax",
        "notation",
        "infix",
        "infixl",
        "infixr",
        "prefix",
        "postfix",
    }
)
_TRUSTING = frozenset({"axiom", "unsafe", "native", "extern", "implemented_by"})


def _fix_for_word(word: str) -> str:
    """What to write instead of a refused word, in a clause that follows ``Fix:``."""
    if word == "set_option":
        return (
            "take set_option out; to give the claim more time, set LANKY_LEAN_BUDGET "
            "to the seconds it needs"
        )
    if word in _DECLARING:
        return (
            f"take {word} out; state what the proof needs with have inside the "
            "script, or as a @theorem of its own"
        )
    if word == "open":
        return "take open out, and write each name in full, as Finset.sum_comm"
    if word == "import":
        return "take import out; lanky imports Mathlib itself where the claim needs it"
    if word in _SCOPING:
        return f"take {word} out; the script is one proof, and lanky writes the command around it"
    if word in _SYNTAX:
        return f"take {word} out, and write the proof in tactics"
    if word in _TRUSTING:
        return f"take {word} out; a proof rests on the kernel and Lean's three axioms alone"
    return f"take {word} out; a proof changes nothing outside itself"


def refusal(script: str, library: bool = False) -> tuple[str, str] | None:
    """Why the screen refuses ``script``, and what to write instead; ``None`` when it passes.

    The reason is :func:`screen`'s (``it has #exit, a Lean command``), and
    the fix a clause that can follow ``Fix:`` (``take #exit out; lanky writes
    every command around the script, and --show-lean prints them``), so that
    ``lanky check`` names both where it says the script was not sent.
    """
    if not isinstance(script, str):
        return (
            f"a proof is Lean text, not {type(script).__name__}",
            "give the script as a string, the tactics that follow := by",
        )
    text, unclosed = _without_comments(script)
    if unclosed:
        return (
            "it opens a block comment, /-, and does not close it, which hides "
            "everything after it from Lean",
            "close the comment with -/",
        )
    command = _COMMAND.search(text)
    if command is not None:
        word = re.match(r"#\s*[A-Za-z_][A-Za-z0-9_]*", text[command.start() :])
        shown = word.group(0) if word else "#"
        return (
            f"it has {shown}, a Lean command",
            f"take {shown} out; lanky writes every command around the script, and "
            "lanky check --show-lean prints them",
        )
    compiler = _COMPILER.search(text)
    if compiler is not None:
        found = compiler.group(0)
        fix = (
            "prove it with decide, which the kernel checks"
            if found == "native_decide"
            else f"take {found} out; a proof rests on the kernel alone"
        )
        return f"it has {found}, which trusts the compiler and not the kernel", fix
    if library:
        text = _HEARTBEATS.sub(" ", text)
    found = _WORD.search(text)
    if found is not None:
        word = found.group("word")
        return f"it has {word}, which a proof never needs", _fix_for_word(word)
    if library:
        hole = _HOLE.search(text)
        if hole is not None:
            return (
                f"it leaves a hole ({hole.group('word')}), and a library proof leaves none",
                "finish the proof where the hole is",
            )
    return None


# }}}
