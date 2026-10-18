"""Families over the naturals for a native run, filled in from the hypotheses that define them.

The property tester draws a family over a ``Fin`` as a table, and a family
over ``Nat`` not at all: there is no table of every natural. A written
proof's native run (:mod:`lanky.proofs.native`) needs one anyway.
``line_taylor`` is about any table ``a`` with ``alpha * a[1] == beta`` and
the ODE at every ``n``, and its steps are only worth checking at a table
that satisfies them. Drawn at random, almost none would.

So the native run fills such a family in, over the first naturals (and
integers, for an ``Int`` index), from its hypotheses:

- each hypothesis is taken at each point of its domain there, one equation
  or proposition per point;
- an equation that leaves one cell unknown, and is linear in it, gives that
  cell its value, and the cells it fills may leave other equations one
  unknown short in turn;
- where no equation is left so, the first unknown cell (in the order of the
  claim's variables, then of the cell's indices) is drawn, and the filling
  goes on;
- a cell no hypothesis speaks of is drawn when the proof first reads it.

A point of a hypothesis that reads a cell past the filled extent is left
out. The run walks the first :data:`lanky.testing.MAX_NAT` points of a
domain, well inside the extent, so the points it reaches rest on points
that are inside too. A filling that contradicts a hypothesis at a point,
leaves a point of one with no answer in Python (Lean's reading may give it
one: a division by zero is zero there), or puts a value outside the
family's sort, is dropped; and a family the
hypotheses do not reach this way (a quantifier over the reals, a hypothesis
whose guard reads the family) is not filled at all, so the run tests
nothing there, as before, rather than report a step false at values its
hypotheses exclude.
"""

from __future__ import annotations

import heapq
import random
from collections import defaultdict, deque
from collections.abc import Iterator, Mapping
from fractions import Fraction
from typing import Any

import pymbolic.primitives as prim

__all__ = ["EXTENT", "FILLED_DRAWS", "Grid", "filled_draws", "over_the_naturals"]

#: How many naturals each ``Nat`` index of a filled family runs over (and how
#: far each way an ``Int`` index does): twice the native run's walk and a
#: margin, so that a step's reads a few points past the walk are inside.
EXTENT = 14

#: How many draws a native run makes when it fills families: filling is
#: slower than drawing a table, and a step false at all is false at most.
FILLED_DRAWS = 8


class _Unknown(BaseException):  # noqa: N818 - a signal, not an error a user sees
    """A cell of a family being filled read before it has a value.

    A ``BaseException``, so that no handler of the evaluator's own takes it
    for an answer; only the filling catches it, and once filling is done no
    cell raises it (:attr:`Grid.lazy`).
    """

    def __init__(self, cell: tuple[Grid, tuple[int, ...]]) -> None:
        super().__init__(cell[1])
        self.cell = cell


class Unfillable(Exception):  # noqa: N818 - a reason, raised and caught here
    """A family, or a hypothesis about one, that this filling does not reach."""


class _Row:
    """A family with some of its indices given: ``F[i]`` of an ``F[i, j]``."""

    def __init__(self, grid: Grid, given: tuple[Any, ...]) -> None:
        self.grid = grid
        self.given = given

    def __getitem__(self, index: Any) -> Any:
        more = index if isinstance(index, tuple) else (index,)
        return self.grid[(*self.given, *more)]

    def __call__(self, *indices: Any) -> Any:
        return self[indices]

    def __repr__(self) -> str:
        return f"{self.grid.name}[{', '.join(map(str, self.given))}]"


class Grid:
    """A family over the first naturals (and integers), filled in a cell at a time.

    Read at a cell with no value yet, it raises :class:`_Unknown` while it is
    being filled, and draws the cell once filling is done (:attr:`lazy`).
    Read past its extent, it is :class:`~lanky.terms.Undecided`, as a table
    read outside its domain is: there is no value to compare there.

    Attributes:
        name: The family's name, the parameter's.
        axes: The points of each index, in order.
        entries: What the family holds at a cell, its sort.
        cells: The cells with a value, by their indices.
        lazy: Whether a cell with no value is drawn when read.
    """

    def __init__(
        self,
        name: str,
        axes: tuple[range, ...],
        entries: Any,
        rng: random.Random,
        context: Mapping[str, Any],
    ) -> None:
        self.name = name
        self.axes = axes
        self.entries = entries
        self.cells: dict[tuple[int, ...], Any] = {}
        self.probe: dict[tuple[int, ...], Any] = {}
        self.lazy = False
        self.rng = rng
        self.context = context

    def draw(self) -> Any:
        """A value of the family's entries, as the property tester draws one."""
        from lanky.proofs.native import exact
        from lanky.testing import sample_value

        return exact(sample_value(self.entries, self.rng, dict(self.context)))

    def _key(self, indices: tuple[Any, ...]) -> tuple[int, ...]:
        from lanky.terms import Undecided

        key = tuple(int(index) for index in indices)
        for index, axis in zip(key, self.axes, strict=True):
            if index not in axis:
                raise Undecided(
                    f"{self.name} is read at {', '.join(map(str, key))}, past the cells "
                    "the native run fills"
                )
        return key

    def value(self, indices: tuple[Any, ...]) -> Any:
        """The value at a cell, every index given."""
        key = self._key(indices)
        if key in self.probe:
            return self.probe[key]
        if key in self.cells:
            return self.cells[key]
        if self.lazy:
            self.cells[key] = self.draw()
            return self.cells[key]
        raise _Unknown((self, key))

    def __getitem__(self, index: Any) -> Any:
        indices = index if isinstance(index, tuple) else (index,)
        if len(indices) < len(self.axes):
            return _Row(self, indices)
        if len(indices) > len(self.axes):
            raise TypeError(
                f"{self.name} is applied at {len(indices)} indices and has {len(self.axes)}"
            )
        return self.value(indices)

    def __call__(self, *indices: Any) -> Any:
        return self[indices]

    def __repr__(self) -> str:
        return f"<{self.name}, filled over {len(self.cells)} cells>"


def over_the_naturals(sort: Any) -> bool:
    """Whether ``sort`` is a family with an index over ``Nat`` or ``Int``: one to fill in."""
    from lanky.prelude import FnType, Sort

    return isinstance(sort, FnType) and any(
        isinstance(domain, Sort) and domain.name in ("Nat", "Int") for domain in sort.indices
    )


def _axes(sort: Any, context: Mapping[str, Any]) -> tuple[range, ...]:
    """The points of each index of a family to fill, or :class:`Unfillable`."""
    from lanky.prelude import FinType, Refined, Sort
    from lanky.terms import evaluate

    if sort._chain(through_refinements=False) != sort._chain(through_refinements=True):
        raise Unfillable(f"a row of {sort} is refined")
    axes: list[range] = []
    for domain in sort.indices:
        if isinstance(domain, Sort) and domain.name == "Nat":
            axes.append(range(EXTENT))
        elif isinstance(domain, Sort) and domain.name == "Int":
            axes.append(range(-EXTENT, EXTENT))
        elif isinstance(domain, FinType):
            size = domain.bound
            if hasattr(size, "mapper_method"):
                size = evaluate(size, dict(context))
            axes.append(range(int(size)))
        else:
            what = "a refined index" if isinstance(domain, Refined) else f"an index over {domain}"
            raise Unfillable(f"{sort} has {what}")
    return tuple(axes)


def _points(binders: tuple[tuple[Any, Any], ...], scope: dict[str, Any]) -> Iterator[dict]:
    """The points of a hypothesis's binders inside the extent, each binder bound in turn."""
    from lanky.prelude import FinType, Refined, Sort
    from lanky.proofs.native import ExactInt
    from lanky.terms import evaluate

    if not binders:
        yield scope
        return
    (var, domain), rest = binders[0], binders[1:]
    props: tuple[Any, ...] = ()
    while isinstance(domain, Refined):
        props += domain.props
        domain = domain.base
    if isinstance(domain, Sort) and domain.name == "Nat":
        values: Any = range(EXTENT)
    elif isinstance(domain, Sort) and domain.name == "Int":
        values = range(-EXTENT, EXTENT)
    elif isinstance(domain, FinType):
        size = domain.bound
        if hasattr(size, "mapper_method"):
            size = evaluate(size, scope)
        values = range(int(size))
    else:
        raise Unfillable(f"a hypothesis quantifies over {domain}")
    for value in values:
        point = {**scope, var.name: ExactInt(value)}
        if props and not all(_holds(prop, point) for prop in props):
            continue
        yield from _points(rest, point)


def _holds(prop: Any, scope: Mapping[str, Any]) -> bool:
    """Whether a guard or refinement holds at a point; one that reads a cell is not reached."""
    from lanky.terms import evaluate

    try:
        return evaluate(prop, dict(scope)) is True
    except _Unknown as exc:
        raise Unfillable("a guard reads a family being filled") from exc
    except Exception:  # noqa: BLE001 - a point whose guard has no answer is left out
        return False


def _instances(prop: Any, scope: dict[str, Any]) -> Iterator[tuple[Any, dict[str, Any]]]:
    """A hypothesis at each point of its domain inside the extent: ``(proposition, scope)``."""
    from lanky.terms import Forall

    if isinstance(prop, prim.LogicalAnd):
        for child in prop.children:
            yield from _instances(child, scope)
    elif isinstance(prop, Forall):
        for point in _points(prop.binders, scope):
            if prop.guard is not None and not _holds(prop.guard, point):
                continue
            yield from _instances(prop.body, point)
    else:
        yield prop, scope


#: A point of a hypothesis that has no answer at the values filled (a
#: division by zero, a value Python cannot compute). The filling is dropped:
#: Lean's reading may answer it (``f[0] % 0 == 0`` forces ``f[0] == 0``
#: there), and a draw that breaks that answer could report a valid step false.
_NO_ANSWER = object()


class _Filling:
    """One filling of the families of a draw: the equations at each point, and the cells."""

    def __init__(self, instances: list[tuple[Any, dict[str, Any]]], order: dict[Grid, int]):
        self.instances = instances
        self.order = order
        self.done = [False] * len(instances)
        self.waiting: dict[tuple[Grid, tuple[int, ...]], list[int]] = defaultdict(list)
        self.heap: list[tuple[int, tuple[int, ...], int]] = []
        self.grids = {index: grid for grid, index in order.items()}
        self.queue: deque[int] = deque(range(len(instances)))

    def run(self) -> bool:
        """Fill every cell an equation reaches; whether every point of every hypothesis holds."""
        while True:
            while self.queue:
                k = self.queue.popleft()
                if not self.done[k] and not self._examine(k):
                    return False
            cell = self._next_open_cell()
            if cell is None:
                return True
            grid, key = cell
            self._set(grid, key, grid.draw())

    def _next_open_cell(self) -> tuple[Grid, tuple[int, ...]] | None:
        """The first cell in order that a point still waits on, and has no value."""
        while self.heap:
            index, key, _ = heapq.heappop(self.heap)
            grid = self.grids[index]
            if key in grid.cells:
                continue
            if any(not self.done[k] for k in self.waiting.get((grid, key), ())):
                return grid, key
        return None

    def _wait(self, cell: tuple[Grid, tuple[int, ...]], k: int) -> None:
        if cell not in self.waiting:
            grid, key = cell
            heapq.heappush(self.heap, (self.order[grid], key, len(self.heap)))
        self.waiting[cell].append(k)

    def _set(self, grid: Grid, key: tuple[int, ...], value: Any) -> None:
        grid.cells[key] = value
        self.queue.extend(self.waiting.pop((grid, key), ()))

    def _unknown_cells(self, k: int) -> tuple[list[tuple[Grid, tuple[int, ...]]], Any]:
        """The cells point ``k`` reads that have no value, and its truth where it has one.

        Raises:
            lanky.terms.Undecided: Where the point reads past the extent.
        """
        from lanky.terms import Undecided, evaluate

        prop, scope = self.instances[k]
        found: list[tuple[Grid, tuple[int, ...]]] = []
        try:
            while True:
                try:
                    return found, evaluate(prop, scope)
                except _Unknown as unknown:
                    grid, key = unknown.cell
                    found.append(unknown.cell)
                    grid.probe[key] = 1
                except Undecided:
                    raise
                except Exception:  # noqa: BLE001 - a point with no answer at these values
                    return found, _NO_ANSWER
        finally:
            for grid, key in found:
                grid.probe.pop(key, None)

    def _examine(self, k: int) -> bool:
        """Settle point ``k`` if it can be: check it, or solve it for its one unknown cell."""
        from lanky.terms import Undecided

        try:
            found, truth = self._unknown_cells(k)
        except Undecided:
            self.done[k] = True  # it reads past the extent: left out
            return True
        if not found:
            self.done[k] = True
            return truth is True
        if len(found) == 1:
            solved = self._solve(k, found[0])
            if solved is not None:
                grid, key = found[0]
                if not _in_sort(solved, grid):
                    return False
                self._set(grid, key, solved)
                self.queue.append(k)
                return True
        for cell in found:
            self._wait(cell, k)
        return True

    def _solve(self, k: int, cell: tuple[Grid, tuple[int, ...]]) -> Any:
        """The value of ``cell`` that makes the equation at point ``k`` hold, where linear in it."""
        from lanky.proofs.native import ExactInt
        from lanky.terms import evaluate

        prop, scope = self.instances[k]
        if not isinstance(prop, prim.Comparison) or prop.operator != "==":
            return None
        grid, key = cell

        def at(x: Any, term: Any) -> Any:
            grid.probe[key] = x
            try:
                return evaluate(term, scope)
            finally:
                grid.probe.pop(key, None)

        try:
            # exact probes: with plain ints, f[0] == 0 would give 1 - 1 / 1, a float
            probes = (ExactInt(1), ExactInt(2), ExactInt(3))
            f1, f2, f3 = (at(x, prop.left) - at(x, prop.right) for x in probes)
            slope = f2 - f1
            if (f3 - f2 == slope) is not True or (slope == 0) is not False:
                return None
            value = 1 - f1 / slope
            if isinstance(value, Fraction) and value.denominator == 1:
                # an integer, as a family of integers holds one
                value = ExactInt(value.numerator)
            holds = at(value, prop)
        except Exception:  # noqa: BLE001 - an equation that cannot be solved here is checked later
            return None
        return value if holds is True else None


def _in_sort(value: Any, grid: Grid) -> bool:
    from lanky.testing import in_sort

    try:
        return in_sort(value, grid.entries, dict(grid.context)) is True
    except Exception:  # noqa: BLE001 - a value whose sort cannot be told is not kept
        return False


def _fill(
    families: list[tuple[str, Any]],
    defining: list[Any],
    context: dict[str, Any],
    rng: random.Random,
) -> dict[str, Grid] | None:
    """The families of one draw, filled in, or ``None`` where a hypothesis contradicts them."""
    grids = {
        name: Grid(name, _axes(sort, context), sort.entries, rng, context)
        for name, sort in families
    }
    scope = {**context, **grids}
    instances = [found for prop in defining for found in _instances(prop, scope)]
    filling = _Filling(instances, {grid: index for index, grid in enumerate(grids.values())})
    if not filling.run():
        return None
    for grid in grids.values():
        grid.lazy = True
    return grids


def filled_draws(theorem: Any, samples: int = FILLED_DRAWS, seed: int = 0) -> list[dict]:
    """Draws of ``theorem``'s variables with its families over the naturals filled in.

    The other variables are drawn as the property tester draws them, at the
    hypotheses that do not read a family to fill; each family is then
    filled in from the rest (see the module docstring). Empty where the
    claim has no such family, or one this does not reach.
    """
    from lanky.terms import exact_reading, free_names
    from lanky.testing import valid_draws

    families = [(name, sort) for name, sort in theorem.variables if over_the_naturals(sort)]
    if not families:
        return []
    names = {name for name, _ in families}
    others = [(name, sort) for name, sort in theorem.variables if name not in names]
    props = [prop for _name, prop in theorem.hypotheses]
    plain = [prop for prop in props if not free_names(prop) & names]
    defining = [prop for prop in props if free_names(prop) & names]
    rng = random.Random(seed)
    out: list[dict] = []
    try:
        with exact_reading():
            for context in valid_draws(others, plain, samples * 4, seed):
                grids = _fill(families, defining, dict(context), rng)
                if grids is not None:
                    out.append({**context, **grids})
                if len(out) >= samples:
                    break
    except Unfillable:
        return []
    except Exception:  # noqa: BLE001 - a statement the filling cannot read runs no proof
        return []
    return out
