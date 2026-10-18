"""log|alpha| with no square root: a claim that needs two facts lanky knows.

Run it as ``gauss.py`` is run.

``python examples/log_of_the_modulus.py``
    The claim runs at a few complex numbers, as Python computes both sides,
    and the file prints them.

``uv run lanky check examples/log_of_the_modulus.py``
    The ledger. Where Mathlib is installed (see :mod:`lanky.mathlib`), Lean
    checks the proof below, which cites two facts of :mod:`lanky.known`; the
    two facts are proved once, in the library, by their own Lean proofs.

The mathematics. sumpy and pytential evaluate the 2-D Laplace kernel
``log|alpha|`` as half the log of ``alpha`` times its conjugate, which is
``|alpha|**2`` and a real number: one logarithm, no square root. That is the
``log(r2) / 2`` of a QBX kernel. The claim says so for every nonzero complex
``alpha``, and the proof is the calculation a textbook displays: ``log|alpha|``
is half the log of ``|alpha|**2``, by the log of a power, and ``|alpha|**2``
is ``alpha`` times its conjugate, by the modulus squared.

Neither step is lanky's own algebra. Lean's search tries every whole-goal
tactic of its ladder on the claim, and none closes it: no power is in sight
for the log of a power to apply to, which is why the proof asserts the term
where the two facts meet, ``log(abs(alpha) ** 2) / 2``, as a step. Read
aloud: "log|alpha| is half the log of |alpha| squared, by the log of a power;
the rest is the modulus squared." The ``return by(...)`` gives the reason for
the rest of the way, from where the step ended to the claim's other side.
The two facts come from ``lanky.known`` under plain names; their Mathlib
names (``Real.log_pow``, ``Complex.mul_conj``) are in their docstrings, and
never in this file.

``nonzero`` is not cited. Lean does not need it, since Mathlib's logarithm is
total, with ``log 0 = 0``; it keeps the claim to where ``log`` means what its
reader thinks, as Python's ``math.log`` has no value at ``0``.
"""

from __future__ import annotations

from lanky import by, conj, log, real, theorem
from lanky.known import log_of_a_power, modulus_squared
from lanky.prelude import Complex


@theorem
def log_of_the_modulus(alpha: Complex, nonzero: alpha != 0) -> (
    log(abs(alpha)) == log(real(alpha * conj(alpha))) / 2
):
    """log|alpha| with no square root: half the log of alpha times its conjugate."""
    assert log(abs(alpha)) == log(abs(alpha) ** 2) / 2, by(log_of_a_power)
    return by(modulus_squared)


#: The points the program prints the two sides at.
POINTS = (3 + 4j, -0.5 + 0.25j, 1e-3 - 2j)


def main() -> int:
    """Print both sides of the claim at a few complex numbers, as Python computes them.

    The two sides are two roundings of one number, so they agree to the last
    bit or two; the claim is about the numbers, which Lean checks, and the
    property tester draws them exactly.
    """
    import math

    print("alpha               log|alpha|          log(alpha * conj(alpha)) / 2")
    for alpha in POINTS:
        left = math.log(abs(alpha))
        right = math.log((alpha * alpha.conjugate()).real) / 2
        print(f"{alpha!s:<19} {left:<19.15g} {right:.15g}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
