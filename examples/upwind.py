"""The CFL condition, named once, and what holds under it.

The upwind scheme for ``u_t + c u_x = 0`` with ``c >= 0`` moves a value on a
mesh of width ``h`` by a step of ``dt``::

    u_new = u - c * dt / h * (u - u_left)

It is stable under the CFL condition, ``c * dt <= h``: the Courant number
``c * dt / h`` is at most one, and a step then makes no new extremum, since
the new value is a weighted mean of the old one and its upwind neighbour.

The condition is stated once, with ``@condition``, and named, as engineers
name it. The claims that hold under it are written in a ``with`` block, and
each one's statement is the condition's variables and conditions, then its
own. ``cfl`` is also a hypothesis like any other, as in ``courant_number``,
where ``cfl(c, dt, h)`` gives ``c``, ``dt`` and ``h`` their sorts.

Run it three ways::

    python examples/upwind.py           # the condition and the claims, at numbers
    pytest examples/upwind.py           # the claims, as property tests
    lanky check examples/upwind.py      # the ledger
"""

from __future__ import annotations

from fractions import Fraction

from lanky import claim, condition
from lanky.prelude import Real


@condition
def cfl(
    c: Real,
    dt: Real,
    h: Real,
    forward: c >= 0,
    positive: (dt > 0) & (h > 0),
    stable: c * dt <= h,
):
    """The CFL condition of the upwind scheme for u_t + c u_x = 0, with c >= 0."""


with cfl as (c, dt, h, forward, positive, stable):

    @claim
    def courant() -> c * dt / h <= 1:
        """Under the CFL condition, the Courant number is at most one."""

    @claim
    def no_new_extremum(u_left: Real, u: Real, rising: u_left <= u) -> (
        (u_left <= u - c * dt / h * (u - u_left)) & (u - c * dt / h * (u - u_left) <= u)
    ):
        """An upwind step keeps each value between its old value and its upwind neighbour."""


@claim
def courant_number(ok: cfl(c, dt, h)) -> 0 <= c * dt / h:
    """Wherever the CFL condition holds, the Courant number is not negative either."""


def main() -> int:
    """The condition and the claims at numbers, as Python computes them."""
    c, dt, h = 1, Fraction(1, 10), Fraction(1, 5)
    print(f"cfl(c={c}, dt={dt}, h={h}) = {cfl(c=c, dt=dt, h=h)}")
    print(f"cfl(c=3, dt={dt}, h={h}) = {cfl(c=3, dt=dt, h=h)}")
    print(f"courant at them: {courant(c=c, dt=dt, h=h)}")
    step = no_new_extremum(c=c, dt=dt, h=h, u_left=0, u=1)
    print(f"no_new_extremum at u_left = 0, u = 1: {step}")
    return 0 if step else 1


if __name__ == "__main__":
    raise SystemExit(main())
