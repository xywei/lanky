"""Five integral representations, and whether each gives a second-kind equation.

Run it three ways, as ``gauss.py`` is run.

``python examples/pytential_skie.py``
    Prints each representation, the boundary equation it gives on a smooth
    closed boundary, and the verdict, with the two refusals explained. Where
    pytential imports, the five are built again with ``pytential.sym`` and
    translated, and two of pytential's own ``DirichletOperator`` pairs are
    checked as well.

``uv run lanky check examples/pytential_skie.py``
    The ledger. The eight facts the argument rests on are axioms, taken on a
    citation that is printed under the table. Each representation claims
    three things: a rewrite, from its trace to the boundary operator it is
    said to give, which the jump relations have to justify; for a
    second-kind claim, that the operator's identity coefficient is not zero,
    which is arithmetic and the one part Lean touches; and a verdict about
    the operator, decided by the rule engine in ``layer_potentials.py``
    under the axioms it applied.

``uv run pytest examples/pytential_skie.py``
    The axioms are collected and skipped: they quantify over boundaries,
    which the property tester has no way to draw.

The mathematics. A representation ``u`` of the solution by layer potentials is
taken to the boundary from one side, and the equation it gives there is of
the second kind when its operator is ``c*I`` plus a compact operator with
``c`` not zero: Fredholm theory then applies, and a discretization of it is
well conditioned. The normal points to the exterior, ``INTERIOR`` is -1 and
``EXTERIOR`` is +1, and the operators are normalized as in Kress: the
double-layer potential jumps by half the density, ``trace(D, s) = D + s/2 * I``
from the side ``s``. pytential's ``DirichletOperator`` has the same
convention, and where pytential imports its operators are checked against the
same rules.

The combined field representation belongs to the exterior problem (Brakhage
and Werner, Leis, Panich), and its limit from the exterior is ``(1/2 I + D - i
eta S) sigma = f``. Written with ``-1/2 I``, as it sometimes is, it is the
limit from the interior; the verdict is the same from either side, and the
claim made here is the exterior one. The fifth row, Neumann data for the same
representation, has the shape of the Burton-Miller formulation: its operator
has ``D'`` in it, which is hypersingular, and it is not of the second kind
without a regularization.
"""

from __future__ import annotations

import warnings

from layer_potentials import (
    EXTERIOR,
    INTERIOR,
    OBLIGATION,
    C2Boundary,
    D,
    Dp,
    I,
    JumpRewrite,
    Operator,
    OutsideFragment,
    RuleSet,
    S,
    Side,
    Sp,
    classify,
    compact,
    decide,
    from_pytential,
    normal_derivative,
    resolve,
    same,
    scalar_plus_compact,
    trace,
)

from lanky import Var, axiom

KRESS = "R. Kress, Linear Integral Equations, 3rd ed., Springer, 2014, ch. 6"
COLTON_KRESS = (
    "D. Colton and R. Kress, Inverse Acoustic and Electromagnetic Scattering Theory, "
    "4th ed., Springer, 2019, ch. 3"
)
#: The Laplace case is Kress's, and the Helmholtz case is Colton and Kress's.
BOTH = f"{KRESS} (Laplace); {COLTON_KRESS} (Helmholtz)"

#: The coupling parameter of the combined field representation.
eta = Var("eta")


# {{{ what the argument rests on


@axiom(cite=BOTH)
def jump_S(gamma: C2Boundary, s: Side) -> trace(S, s) == S:
    """The single-layer potential is continuous across the boundary."""


@axiom(cite=BOTH)
def jump_D(gamma: C2Boundary, s: Side) -> trace(D, s) == D + s / 2 * I:
    """The double-layer potential jumps by the density: ``u± = D σ ± σ/2``."""


@axiom(cite=BOTH)
def jump_Sp(gamma: C2Boundary, s: Side) -> normal_derivative(S, s) == Sp - s / 2 * I:
    """The normal derivative of the single-layer potential jumps: ``∂u±/∂ν = S' σ ∓ σ/2``."""


@axiom(cite=BOTH)
def jump_Dp(gamma: C2Boundary, s: Side) -> normal_derivative(D, s) == Dp:
    """The normal derivative of the double-layer potential is continuous, for a C^{1,α} density."""


@axiom(cite=BOTH)
def compact_S(gamma: C2Boundary) -> compact(S):
    """``S`` has a weakly singular kernel, and is compact on ``C(Γ)`` and ``L²(Γ)``."""


@axiom(cite=BOTH)
def compact_D(gamma: C2Boundary) -> compact(D):
    """``D`` has a weakly singular kernel on a boundary of class C², and is compact."""


@axiom(cite=BOTH)
def compact_Sp(gamma: C2Boundary) -> compact(Sp):
    """``S'`` is the adjoint of ``D``, and is compact."""


@axiom(cite=COLTON_KRESS)
def hypersingular_Dp(gamma: C2Boundary) -> ~scalar_plus_compact(Dp):
    """``D'`` is hypersingular: of order one, and bounded on neither ``C(Γ)`` nor ``L²(Γ)``.

    A multiple of the identity plus a compact operator is bounded, so ``D'`` is
    not one, and that is why an equation with ``D'`` in it needs a
    regularization before it is of the second kind.
    """


#: The rules the verdicts are decided by: exactly the eight statements above.
rules = RuleSet(
    jump_S, jump_D, jump_Sp, jump_Dp, compact_S, compact_D, compact_Sp, hypersingular_Dp
)


# }}}


# {{{ the five representations


@rules.second_kind
def laplace_dirichlet_dlp():
    """Laplace, interior Dirichlet."""
    return trace(D, INTERIOR), -I / 2 + D


@rules.first_kind
def laplace_dirichlet_slp():
    """Laplace, interior Dirichlet."""
    return trace(S, INTERIOR), S


@rules.second_kind
def laplace_neumann_slp():
    """Laplace, interior Neumann."""
    return normal_derivative(S, INTERIOR), I / 2 + Sp


@rules.second_kind
def helmholtz_combined_field():
    """Helmholtz, exterior Dirichlet (combined field)."""
    return trace(D - 1j * eta * S, EXTERIOR), I / 2 + D - 1j * eta * S


@rules.not_second_kind(Dp)
def helmholtz_burton_miller():
    """Helmholtz, exterior Neumann (Burton-Miller)."""
    return normal_derivative(D - 1j * eta * S, EXTERIOR), 1j * eta / 2 * I + Dp - 1j * eta * Sp


CLAIMS = (
    laplace_dirichlet_dlp,
    laplace_dirichlet_slp,
    laplace_neumann_slp,
    helmholtz_combined_field,
    helmholtz_burton_miller,
)


# }}}


# {{{ running it


def _applied(operator: Operator) -> str:
    """``D sigma``, or ``(D - 1j*eta*S) sigma``."""
    text = str(operator)
    return f"({text}) sigma" if len(operator.terms) > 1 else f"{text} sigma"


def _verdict_text(claim) -> str:
    kind = claim.verdict.kind
    if kind == "second kind":
        return "second kind"
    if kind == "first kind":
        return "refused: no identity term"
    return f"refused: {', '.join(claim.verdict.offending)} is not c*I + compact"


def _table(rows: list[tuple[str, ...]]) -> list[str]:
    widths = [max(len(row[i]) for row in rows) for i in range(len(rows[0]))]
    lines = [
        "  ".join(cell.ljust(width) for cell, width in zip(row, widths, strict=True)).rstrip()
        for row in rows
    ]
    lines.insert(1, "  ".join("-" * width for width in widths))
    return lines


def pytential_lines() -> tuple[bool, list[str]]:
    """Build the five with ``pytential.sym``, and check two of pytential's own pairs.

    Returns whether everything agreed, and lines saying what was found.
    pytential is imported here and nowhere else.
    """
    try:
        from pytential import sym
        from pytential.symbolic.pde.scalar import DirichletOperator
        from sumpy.kernel import HelmholtzKernel, LaplaceKernel
    except ImportError:
        return True, [
            "pytential is not importable here, so the rows were built with this file's "
            "operators alone."
        ]
    sigma, k, coupling = sym.var("sigma"), sym.var("k"), sym.var("eta")
    laplace, helmholtz = LaplaceKernel(2), HelmholtzKernel(2)

    def lap(name, limit):
        return getattr(sym, name)(laplace, sigma, qbx_forced_limit=limit)

    def helm(name, limit):
        return getattr(sym, name)(helmholtz, sigma, k=k, qbx_forced_limit=limit)

    combined = helm("D", None) - 1j * coupling * helm("S", None)
    built = {
        laplace_dirichlet_dlp: (lap("D", None), -0.5 * sigma + lap("D", "avg")),
        laplace_dirichlet_slp: (lap("S", None), lap("S", "avg")),
        laplace_neumann_slp: (lap("S", None), 0.5 * sigma + lap("Sp", "avg")),
        helmholtz_combined_field: (
            combined,
            0.5 * sigma + helm("D", "avg") - 1j * coupling * helm("S", "avg"),
        ),
        helmholtz_burton_miller: (
            combined,
            0.5j * coupling * sigma + helm("Dp", "avg") - 1j * coupling * helm("Sp", "avg"),
        ),
    }
    ok, lines = True, []
    for claim, (representation, operator) in built.items():
        try:
            agrees = same(from_pytential(representation), claim.representation) and same(
                resolve(from_pytential(operator), rules).operator,
                resolve(claim.target, rules).operator,
            )
        except OutsideFragment as exc:
            agrees, why = False, str(exc)
        else:
            why = "a different representation or operator"
        if not agrees:
            ok = False
            lines.append(f"pytential: {claim.__name__} translates to {why}")
    if ok:
        lines.append(
            "pytential: the five representations and operators, built with pytential.sym, "
            "translate to the rows above."
        )
    with warnings.catch_warnings():
        # It recommends L2 weighting, which changes the discretization and not
        # the operator the rules see.
        warnings.simplefilter("ignore")
        interior = DirichletOperator(laplace, loc_sign=INTERIOR)
        exterior = DirichletOperator(
            helmholtz, loc_sign=EXTERIOR, alpha=1j, kernel_arguments={"k": k}
        )
    pairs = (
        ("DirichletOperator(LaplaceKernel(2), loc_sign=-1)", INTERIOR, interior),
        ("DirichletOperator(HelmholtzKernel(2), loc_sign=+1, alpha=1j)", EXTERIOR, exterior),
    )
    for name, side, pde in pairs:
        try:
            target = from_pytential(pde.operator(sigma))
            source = trace(from_pytential(pde.representation(sigma)), side)
            rewrite = decide(JumpRewrite(source, target, OBLIGATION, rules))
            kind = classify(target, rules).kind
        except OutsideFragment as exc:
            ok = False
            lines.append(f"pytential's {name}: outside what the rules read: {exc}")
            continue
        ok = ok and rewrite.holds and kind == "second kind"
        lines.append(
            f"pytential's {name}: operator {target}, "
            f"{'which is' if rewrite.holds else 'which is NOT'} the {OBLIGATION} image of "
            f"{source}; {kind}"
        )
    return ok, lines


def main() -> int:
    """Print the five verdicts; exit 1 if any claim is not what the rules decide."""
    ok = True
    rows = [("problem", "representation", "boundary equation", "verdict")]
    why = []
    for claim in CLAIMS:
        rewrite, verdict = claim.decide_rewrite(), claim.decide_verdict()
        ok = ok and rewrite.holds and verdict.holds
        rows.append(
            (
                claim.problem,
                f"u = {_applied(claim.representation)}",
                f"{_applied(claim.target)} = {claim.data}",
                _verdict_text(claim) if rewrite.holds and verdict.holds else "WRONG, see below",
            )
        )
        axioms = ", ".join(a.__name__ for a in (*rewrite.applied, *verdict.applied))
        why.append(f"{claim.__name__}: {verdict.reason}. Under {axioms}.")
        if not rewrite.holds:
            why.append(f"  the rewrite is wrong: {rewrite.reason}")
        if not verdict.holds:
            why.append(f"  the verdict is wrong: {verdict.reason}")
    print("On a closed boundary of class C2, each representation gives, from the side shown:")
    print()
    print("\n".join(_table(rows)))
    print()
    print("\n".join(why))
    print()
    agreed, lines = pytential_lines()
    print("\n".join(lines))
    print()
    print(
        "The axioms are taken on a citation: `lanky check examples/pytential_skie.py` "
        "lists them, and what each verdict is decided under."
    )
    return 0 if ok and agreed else 1


if __name__ == "__main__":
    raise SystemExit(main())

# }}}
