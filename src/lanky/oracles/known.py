"""The Lean proofs of :mod:`lanky.known`, one per fact, written once.

The design idea. :mod:`lanky.known` states each library fact in Python and
cites the Mathlib lemma it is, and nothing in it is Lean: a user who reads it
reads Python. The proofs live here, in a table keyed by each fact's Python
name, and the Lean oracle reads the table for a fact of that module where it
would otherwise build its ladder (:func:`proof_of`). A user never writes or
sees this text; ``--show-lean`` shows it.

Each proof is the tactic block after ``:= by`` in the theorem lanky prints
for the fact, so it is written against the integer reading of
:mod:`lanky.lean`: a ``Nat`` is an ``Int`` with ``0 ≤ n`` among the
hypotheses, a family over ``Nat`` is a function from ``Int``, and a sum over
``Fin[n]`` is over ``Finset.Ico (0 : ℤ) n``. A proof names no hypothesis:
the names the printer gives them are its own to change, so a proof reaches
one by its statement (``‹0 ≤ n›``) or through a tactic that looks
(``assumption``, ``omega``, ``simp_all``). Nor does it rely on the order of
the parameters beyond what the statement fixes.

Every proof is screened before it is sent (:func:`lanky.audit.screen`,
as a library proof), so the table cannot end a file early, set an option
other than a step's heartbeats, declare anything, or leave a hole. And CI
proves every entry with Mathlib under the current printer
(``tests/test_known.py``), so a change to the printer that a proof does not
survive fails CI, rather than turning the library into ``tested`` without a
word.
"""

from __future__ import annotations

from typing import Any

from lanky.audit import screen

__all__ = ["MODULE", "PROOFS", "entry_name", "proof_of"]

#: The module whose facts this table proves.
MODULE = "lanky.known"

#: The Lean proof of each fact of :mod:`lanky.known`, by its Python name.
PROOFS: dict[str, str] = {
    # {{{ logarithms, exponentials and roots
    "log_of_a_power": ("obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ‹0 ≤ n›\nsimp [Real.log_pow]"),
    "log_of_a_product": "exact Real.log_mul (ne_of_gt ‹x > 0›) (ne_of_gt ‹y > 0›)",
    "exp_of_a_sum": "exact Real.exp_add x y",
    "square_root_squared": "exact Real.sq_sqrt ‹x ≥ 0›",
    # }}}
    # {{{ absolute values and moduli
    "abs_of_positive": "exact abs_of_pos ‹x > 0›",
    "abs_of_negative": "rw [abs_of_neg ‹x < 0›]\nring",
    "modulus_squared": "rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]\nnorm_cast",
    "modulus_of_a_product": "exact norm_mul z w",
    "triangle_inequality": "exact abs_add_le x y",
    "complex_triangle_inequality": "exact norm_add_le z w",
    # }}}
    # {{{ finite sums
    "one_more_term": (
        "have last : Finset.Ico (0 : ℤ) (n + 1) = insert n (Finset.Ico (0 : ℤ) n) := by\n"
        "  ext k\n"
        "  simp only [Finset.mem_Ico, Finset.mem_insert]\n"
        "  omega\n"
        "rw [last, Finset.sum_insert (by simp)]\n"
        "ring"
    ),
    "shifted_sum": (
        "symm\n"
        "refine Finset.sum_nbij' (fun k => k + m) (fun k => k - m) ?_ ?_ ?_ ?_ ?_\n"
        "all_goals intro k held\n"
        "all_goals simp only [Finset.mem_Ico, Finset.mem_filter] at held ⊢\n"
        "all_goals omega"
    ),
    "geometric_sum": (
        "obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ‹0 ≤ n›\n"
        "induction n with\n"
        "| zero => simp\n"
        "| succ m step =>\n"
        "  have last : Finset.Ico (0 : ℤ) ((m + 1 : ℕ) : ℤ)\n"
        "      = insert (m : ℤ) (Finset.Ico (0 : ℤ) (m : ℤ)) := by\n"
        "    ext k\n"
        "    simp only [Finset.mem_Ico, Finset.mem_insert]\n"
        "    omega\n"
        "  rw [last, Finset.sum_insert (by simp), mul_add, step (by omega)]\n"
        "  simp only [Int.toNat_natCast]\n"
        "  ring"
    ),
    "sum_of_a_constant": (
        "obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ‹0 ≤ n›\nsimp [Finset.sum_const, Int.card_Ico]"
    ),
    "distribute": "rw [Finset.mul_sum]",
    "sum_of_sums": "exact Finset.sum_add_distrib",
    "triangle_inequality_for_sums": "exact Finset.abs_sum_le_sum_abs _ _",
    "sum_exchange": "exact Finset.sum_comm",
    "triangle_exchange": (
        "refine Finset.sum_comm' fun a b => ?_\nsimp only [Finset.mem_Ico]\nomega"
    ),
    "fiber_exchange": (
        "refine Finset.sum_fiberwise_of_maps_to (fun i held => ?_) _\n"
        "rw [Finset.mem_Ico] at held ⊢\n"
        "exact ⟨by omega, by simp_all⟩"
    ),
    # }}}
}


def entry_name(fact: Any) -> str | None:
    """The Python name of the :mod:`lanky.known` fact ``fact`` is the claim of; ``None`` otherwise.

    A theorem's fact id is ``theorem:<module>.<name>@<line>``, with the module
    its file's path gives it (:func:`lanky.check.module_name`), so a theorem
    of a user's own named like an entry, ``log_of_a_power`` in ``mine.py``,
    is not one, and gets the ladder.
    """
    if getattr(fact, "kind", None) != "theorem":
        return None
    owner = getattr(fact, "owner", None)
    identifier = getattr(fact, "id", None)
    if not isinstance(owner, str) or not isinstance(identifier, str):
        return None
    if not identifier.startswith(f"theorem:{MODULE}.{owner}@"):
        return None
    return owner if owner in PROOFS else None


def proof_of(fact: Any) -> str | None:
    """The table's Lean proof of ``fact``, if it is a fact of :mod:`lanky.known`.

    Raises:
        ValueError: If the table's proof does not pass the screen, which a
            change to the table, never a user, can cause; the oracle declines
            the fact with the reason.
    """
    name = entry_name(fact)
    if name is None:
        return None
    proof = PROOFS[name]
    refused = screen(proof, library=True)
    if refused is not None:
        raise ValueError(f"lanky.known's Lean proof of {name} is refused: {refused}")
    return proof
