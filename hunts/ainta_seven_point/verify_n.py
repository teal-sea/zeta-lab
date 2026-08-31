"""Computer-assisted certificate for the n-point pressure inequality.

Generalisation of ``verify_seven.py`` to n points, i.e. n-1 nonnegative gaps:

    F_{n-1}(g) = (1/p) sum_i g_i
               + sum_{s=1}^{n-1} (2/(n-s)) sum_{i=0}^{n-1-s} w(g_i + ... + g_{i+s-1}),

    w(x) = k(x)^2,  k = K(x)/K(0),  K(x) = int_{-1/2}^{1/2} cos(sqrt2 t) cos(2 pi x t) dt.

The soundness structure of ``verify_seven.py`` is kept exactly:

* Arb lower enclosures of w on a fixed 1/grid grid (``kernel.build_kernel_table``),
  widened to binary64 lower bounds;
* every binary64 operation in the search phase rounds outward (``rounding.py``);
* O(1) range minima over cell ranges (``kernel.RangeMinimum``);
* exhaustive bisection of (n-1)-dimensional cell boxes on the widest dimension;
* the interval prune (box lower bound >= target_upper);
* the pressure prune, whose cutoff is now DERIVED from the target,
  ``cutoff_cells = ceil(grid * p * target) + grid // 10``, so that every box it
  removes has sum(g) >= cutoff/grid >= p * target and hence F >= target by the
  linear term alone. ``verify_seven.py`` hard-codes 45600, which encodes only the
  original 19/5000 target (45600 / (4000 * 3000) = 0.0038) and is unsound for any
  larger target;
* the convex tangent prune, carried over with the dimension parameterised. Its
  argument is dimension-free: Hess F = sum_{i,s} c_s w''(sigma_{i,s}) u u^T with
  u the 0/1 indicator of the gaps a span covers, so a lower bound L on w'' over the
  span's cell range gives Hess F >= sum c_s L u u^T; Arb LDL proves that matrix
  positive definite, and then the tangent plane at the box centre minus
  |gradient| * radius is a lower bound for F on the box.

Differences from ``verify_seven.py`` that are not soundness-relevant: a terminal
single-cell box below target returns outcome REFUSED with the cell instead of
raising; an optional node cap and time cap return UNDECIDED; the initial box list
can be partitioned deterministically across shards.

Nothing here is a statement about zeta zeros: it decides the finite inequality
F_{n-1} >= target on nonnegative gaps, at one grid, and nothing else.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import time
from dataclasses import dataclass, field
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from flint import arb, fmpq

from .kernel import (
    RangeMinimum,
    build_kernel_table,
    build_second_derivative_lower_table,
    kernel_constants,
    squared_kernel_derivatives,
    table_sha256,
)
from .rounding import down_add, down_mul, down_ratio, up_ratio


ACCEPTED = "ACCEPTED"
REFUSED = "REFUSED"
UNDECIDED = "UNDECIDED"

CellRange = Tuple[int, int]
Box = Tuple[CellRange, ...]


def derived_cutoff_cells(grid: int, pressure: int, numerator: int, denominator: int) -> int:
    """ceil(grid * pressure * target) + grid // 10, in exact integer arithmetic.

    Any box whose gap-sum lower end is at least this many cells has
    sum(g) >= cutoff/grid >= pressure * target, so the linear term alone gives
    F >= target. The extra grid // 10 cells (0.1 in gap-sum units) are margin.
    """

    if grid <= 0 or pressure <= 0 or numerator <= 0 or denominator <= 0:
        raise ValueError("grid, pressure, numerator and denominator must be positive")
    exact = grid * pressure * numerator
    return -(-exact // denominator) + grid // 10


def _coefficient_bounds(n_points: int, span: int) -> Tuple[float, float, fmpq]:
    """(lower, upper, exact) for c_s = 2/(n-s); exact binary64 when integral.

    For n = 7 this reproduces verify_seven.py's tables bit for bit:
    down_ratio(1,3), down_ratio(2,5), down_ratio(1,2), down_ratio(2,3), 1.0, 2.0.
    """

    numerator, denominator = 2, n_points - span
    common = math.gcd(numerator, denominator)
    numerator //= common
    denominator //= common
    if denominator == 1:
        return float(numerator), float(numerator), fmpq(numerator)
    return (
        down_ratio(numerator, denominator),
        up_ratio(numerator, denominator),
        fmpq(numerator, denominator),
    )


def _components(indices: Iterable[int]) -> List[CellRange]:
    result: List[List[int]] = []
    for index in indices:
        if not result or index > result[-1][1] + 1:
            result.append([index, index])
        else:
            result[-1][1] = index
    return [(left, right) for left, right in result]


@dataclass
class Prepared:
    """Everything the search phase needs; built once, reusable across shards."""

    n_points: int
    numerator: int
    denominator: int
    grid: int
    pressure: int
    precision_bits: int
    cutoff_cells: int
    table: List[float]
    ranges: RangeMinimum
    second_table: List[float]
    second_ranges: RangeMinimum
    second_start: int
    target_upper: float
    coefficients: Dict[int, float]
    coefficients_up: Dict[int, float]
    coefficient_rationals: Dict[int, fmpq]
    components: List[CellRange]
    boxes: List[Box]
    root_boxes: int
    presplit_depth: int
    prepare_seconds: float
    constants: Any = field(repr=False, default=None)


def prepare(
    n_points: int,
    numerator: int,
    denominator: int,
    grid: int = 4_000,
    pressure: int = 3_000,
    precision_bits: int = 128,
    cutoff_cells: Optional[int] = None,
    presplit_depth: int = 0,
) -> Prepared:
    """Build the Arb tables, the surviving gap cells and the initial box list."""

    started = time.perf_counter()
    if n_points < 2:
        raise ValueError("n_points must be at least 2 (one gap)")
    gaps = n_points - 1
    derived = derived_cutoff_cells(grid, pressure, numerator, denominator)
    if cutoff_cells is None:
        cutoff_cells = derived
    # Soundness of the pressure prune, checked exactly: cutoff/(grid*p) >= target.
    if cutoff_cells * denominator < grid * pressure * numerator:
        raise ValueError(
            f"cutoff_cells={cutoff_cells} is below grid*pressure*target="
            f"{grid * pressure * numerator}/{denominator}; the pressure prune would be unsound"
        )

    cell_count = cutoff_cells + 8
    table = build_kernel_table(grid, cell_count, precision_bits)
    ranges = RangeMinimum(table)
    constants = kernel_constants()
    target_upper = up_ratio(numerator, denominator)

    coefficients: Dict[int, float] = {}
    coefficients_up: Dict[int, float] = {}
    coefficient_rationals: Dict[int, fmpq] = {}
    for span in range(1, n_points):
        low, high, exact = _coefficient_bounds(n_points, span)
        coefficients[span] = low
        coefficients_up[span] = high
        coefficient_rationals[span] = exact

    # U(g) = g/p + c_1 w(g) is a term of F (the rest is nonnegative). Any cell on
    # which U already exceeds the target cannot hold a gap of a counterexample.
    surviving_cells: List[int] = []
    for index in range(cutoff_cells):
        one_body = down_ratio(index, grid * pressure)
        one_body = down_add(one_body, down_mul(coefficients[1], table[index]))
        if one_body < target_upper:
            surviving_cells.append(index)
    components = _components(surviving_cells)

    # The w'' table feeds only the tangent prune; cells below second_start hold
    # -inf there, which simply disables that prune on boxes touching them. The
    # closed form divides by (pi x - 1/sqrt2)^3, zero at x ~ 0.225, so the table
    # never starts below 0.4. For n = 7 at grid 4000 this is the published 3800.
    published_start = (95 * grid) // 100
    first_cell = components[0][0] if components else published_start
    second_start = max(min(first_cell, published_start), -(-(2 * grid) // 5))
    second_table = build_second_derivative_lower_table(
        grid, cell_count, start_index=second_start, precision=precision_bits
    )
    # A NaN could only arise from a ball containing the pole; it never does with
    # the floor above, but a NaN must never pass as a finite lower bound.
    second_table = [value if value == value else -math.inf for value in second_table]
    second_ranges = RangeMinimum(second_table)

    boxes: List[Box] = [tuple(parts) for parts in itertools.product(components, repeat=gaps)]
    root_boxes = len(boxes)
    if presplit_depth < 0:
        raise ValueError("presplit_depth must be nonnegative")
    if presplit_depth:
        boxes = presplit(boxes, presplit_depth)

    return Prepared(
        n_points=n_points,
        numerator=numerator,
        denominator=denominator,
        grid=grid,
        pressure=pressure,
        precision_bits=precision_bits,
        cutoff_cells=cutoff_cells,
        table=table,
        ranges=ranges,
        second_table=second_table,
        second_ranges=second_ranges,
        second_start=second_start,
        target_upper=target_upper,
        coefficients=coefficients,
        coefficients_up=coefficients_up,
        coefficient_rationals=coefficient_rationals,
        components=components,
        boxes=boxes,
        root_boxes=root_boxes,
        presplit_depth=presplit_depth,
        prepare_seconds=time.perf_counter() - started,
        constants=constants,
    )


def shard_boxes(boxes: Sequence[Box], shard_index: int, shard_count: int) -> List[Box]:
    """Deterministic round-robin slice of the initial box list."""

    if shard_count < 1 or not 0 <= shard_index < shard_count:
        raise ValueError(f"bad shard ({shard_index}, {shard_count})")
    return list(boxes[shard_index::shard_count])


def presplit(boxes: Sequence[Box], depth: int) -> List[Box]:
    """Bisect every box `depth` times on its widest dimension (the search's own rule).

    The halves partition the box, so exhaustiveness is preserved; the only effect
    is a finer, better balanced unit of work for sharding. Single-cell boxes are
    kept as they are.
    """

    current = list(boxes)
    for _ in range(depth):
        following: List[Box] = []
        for box in current:
            widths = [right - left for left, right in box]
            if max(widths) == 0:
                following.append(box)
                continue
            coordinate = max(range(len(box)), key=widths.__getitem__)
            left, right = box[coordinate]
            midpoint = (left + right) // 2
            lower_half = list(box)
            upper_half = list(box)
            lower_half[coordinate] = (left, midpoint)
            upper_half[coordinate] = (midpoint + 1, right)
            following.append(tuple(lower_half))
            following.append(tuple(upper_half))
        current = following
    return current


def search(
    prepared: Prepared,
    shard_index: int = 0,
    shard_count: int = 1,
    node_cap: int = 0,
    time_cap_seconds: float = 0.0,
    use_tangent_prune: bool = True,
    progress_every: int = 0,
) -> Dict[str, Any]:
    """Exhaustive branch-and-bound over one shard of the initial boxes."""

    started = time.perf_counter()
    P = prepared
    gaps = P.n_points - 1
    grid = P.grid
    pressure = P.pressure
    cutoff_cells = P.cutoff_cells
    target_upper = P.target_upper
    coefficients = P.coefficients
    coefficients_up = P.coefficients_up
    coefficient_rationals = P.coefficient_rationals
    ranges = P.ranges
    second_ranges = P.second_ranges
    constants = P.constants
    table = P.table
    target_arb = arb(fmpq(P.numerator, P.denominator))

    def kernel_min(left: int, right: int) -> float:
        # Past the table, zero is still a rigorous lower bound for w = k^2 >= 0.
        if right >= ranges.length:
            return 0.0
        return ranges.query(left, right)

    def second_derivative_min(left: int, right: int) -> float:
        if right >= second_ranges.length:
            return float("-inf")
        return second_ranges.query(left, right)

    def box_lower(box: Box) -> float:
        low_prefix = [0]
        high_prefix = [0]
        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        result = down_ratio(low_prefix[-1], grid * pressure)
        for span in range(1, gaps + 1):
            coefficient = coefficients[span]
            for start in range(gaps + 1 - span):
                left = low_prefix[start + span] - low_prefix[start]
                # A sum of `span` closed cells has this inclusive cell range.
                right = high_prefix[start + span] - high_prefix[start] + span - 1
                result = down_add(result, down_mul(coefficient, kernel_min(left, right)))
        return result

    def coefficient_times_signed_lower(span: int, lower: float) -> float:
        if lower == float("-inf") or lower != lower:
            return float("-inf")
        coefficient = coefficients[span] if lower >= 0.0 else coefficients_up[span]
        # Multiplication is rounded to nearest first, then widened down.
        return math.nextafter(coefficient * lower, -math.inf)

    def float_ldl_is_positive(matrix: List[List[float]]) -> bool:
        """Cheap heuristic; success is rechecked with Arb below."""

        lower = [[0.0] * gaps for _ in range(gaps)]
        diagonal = [0.0] * gaps
        for column in range(gaps):
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= lower[column][previous] * lower[column][previous] * diagonal[previous]
            if not pivot > 1e-12:
                return False
            diagonal[column] = pivot
            lower[column][column] = 1.0
            for row in range(column + 1, gaps):
                value = matrix[row][column]
                for previous in range(column):
                    value -= lower[row][previous] * lower[column][previous] * diagonal[previous]
                lower[row][column] = value / pivot
        return True

    def exact_float(value: float) -> arb:
        numerator, denominator = value.as_integer_ratio()
        return arb(fmpq(numerator, denominator))

    def arb_ldl_is_positive(terms: Sequence[Tuple[int, int, float]]) -> bool:
        """Prove the rational lower-Hessian matrix positive definite."""

        matrix = [[arb(0) for _ in range(gaps)] for _ in range(gaps)]
        for start, span, coefficient in terms:
            exact = exact_float(coefficient)
            for row in range(start, start + span):
                for column in range(start, start + span):
                    matrix[row][column] += exact

        lower = [[arb(0) for _ in range(gaps)] for _ in range(gaps)]
        diagonal = [arb(0) for _ in range(gaps)]
        for column in range(gaps):
            lower[column][column] = arb(1)
            pivot = matrix[column][column]
            for previous in range(column):
                pivot -= lower[column][previous] * lower[column][previous] * diagonal[previous]
            if not (pivot > 0):
                return False
            diagonal[column] = pivot
            for row in range(column + 1, gaps):
                value = matrix[row][column]
                for previous in range(column):
                    value -= lower[row][previous] * lower[column][previous] * diagonal[previous]
                lower[row][column] = value / pivot
        return True

    def convex_tangent_lower(box: Box) -> Optional[arb]:
        """Return a rigorous tangent lower bound when convexity is proved."""

        low_prefix = [0]
        high_prefix = [0]
        for low, high in box:
            low_prefix.append(low_prefix[-1] + low)
            high_prefix.append(high_prefix[-1] + high)

        terms: List[Tuple[int, int, float]] = []
        heuristic = [[0.0] * gaps for _ in range(gaps)]
        for span in range(1, gaps + 1):
            for start in range(gaps + 1 - span):
                left = low_prefix[start + span] - low_prefix[start]
                right = high_prefix[start + span] - high_prefix[start] + span - 1
                second_lower = second_derivative_min(left, right)
                scalar = coefficient_times_signed_lower(span, second_lower)
                if scalar == float("-inf"):
                    return None
                terms.append((start, span, scalar))
                for row in range(start, start + span):
                    for column in range(start, start + span):
                        heuristic[row][column] += scalar

        if not float_ldl_is_positive(heuristic):
            return None
        if not arb_ldl_is_positive(terms):
            return None

        midpoints = [fmpq(low + high + 1, 2 * grid) for low, high in box]
        radii = [fmpq(high - low + 1, 2 * grid) for low, high in box]
        value = sum((arb(point) for point in midpoints), arb(0)) / pressure
        gradient = [arb(fmpq(1, pressure)) for _ in range(gaps)]

        for span in range(1, gaps + 1):
            coefficient = arb(coefficient_rationals[span])
            for start in range(gaps + 1 - span):
                point = sum(midpoints[start : start + span], fmpq(0))
                potential, derivative, _ = squared_kernel_derivatives(arb(point), constants)
                value += coefficient * potential
                for coordinate in range(start, start + span):
                    gradient[coordinate] += coefficient * derivative

        lower = value
        for derivative, radius in zip(gradient, radii):
            lower -= derivative.abs_upper() * arb(radius)
        return lower

    my_boxes = shard_boxes(P.boxes, shard_index, shard_count)
    stack: List[Tuple[Box, int]] = [(box, P.presplit_depth) for box in my_boxes]
    nodes = pruned = splits = maximum_depth = 0
    pressure_pruned = interval_pruned = tangent_pruned = 0
    outcome = ACCEPTED
    stop_reason: Optional[str] = None
    refuting_cell: Optional[List[int]] = None
    refuting_lower: Optional[float] = None

    while stack:
        if node_cap and nodes >= node_cap:
            outcome, stop_reason = UNDECIDED, "node_cap"
            break
        if time_cap_seconds and time.perf_counter() - started >= time_cap_seconds:
            outcome, stop_reason = UNDECIDED, "time_cap"
            break

        box, depth = stack.pop()
        nodes += 1
        maximum_depth = max(maximum_depth, depth)

        if sum(part[0] for part in box) >= cutoff_cells:
            pruned += 1
            pressure_pruned += 1
            continue

        lower = box_lower(box)
        if lower >= target_upper:
            pruned += 1
            interval_pruned += 1
            continue

        if use_tangent_prune:
            tangent_lower = convex_tangent_lower(box)
            if tangent_lower is not None and tangent_lower >= target_arb:
                pruned += 1
                tangent_pruned += 1
                continue

        widths = [right - left for left, right in box]
        if max(widths) == 0:
            outcome = REFUSED
            refuting_cell = [left for left, _ in box]
            refuting_lower = lower
            break

        splits += 1
        coordinate = max(range(gaps), key=widths.__getitem__)
        left, right = box[coordinate]
        midpoint = (left + right) // 2
        lower_half = list(box)
        upper_half = list(box)
        lower_half[coordinate] = (left, midpoint)
        upper_half[coordinate] = (midpoint + 1, right)
        stack.append((tuple(lower_half), depth + 1))
        stack.append((tuple(upper_half), depth + 1))

        if progress_every and nodes % progress_every == 0:
            print(
                f"n{P.n_points} shard {shard_index}/{shard_count}: nodes={nodes} "
                f"pending={len(stack)} depth={maximum_depth}",
                flush=True,
            )

    elapsed = time.perf_counter() - started
    result: Dict[str, Any] = {
        "outcome": outcome,
        "n_points": P.n_points,
        "gaps": gaps,
        "target": f"{P.numerator}/{P.denominator}",
        "target_float": P.numerator / P.denominator,
        "grid": grid,
        "pressure": pressure,
        "precision_bits": P.precision_bits,
        "cutoff_cells": cutoff_cells,
        "cutoff_derived": derived_cutoff_cells(grid, pressure, P.numerator, P.denominator),
        "tangent_prune": use_tangent_prune,
        "second_derivative_start_cell": P.second_start,
        "kernel_table_sha256": table_sha256(table),
        "second_derivative_table_sha256": table_sha256(P.second_table),
        "surviving_gap_components_cells": ";".join(f"[{a},{b}]" for a, b in P.components),
        "surviving_gap_components_count": len(P.components),
        "root_boxes": P.root_boxes,
        "presplit_depth": P.presplit_depth,
        "initial_boxes_total": len(P.boxes),
        "initial_boxes_shard": len(my_boxes),
        "shard_index": shard_index,
        "shard_count": shard_count,
        "nodes": nodes,
        "pruned": pruned,
        "splits": splits,
        "maximum_depth": maximum_depth,
        "pressure_pruned": pressure_pruned,
        "interval_pruned": interval_pruned,
        "tangent_pruned": tangent_pruned,
        "pending_boxes": len(stack),
        "node_cap": node_cap,
        "time_cap_seconds": time_cap_seconds,
        "stop_reason": stop_reason,
        "refuting_cell": refuting_cell,
        "refuting_cell_gaps": (
            [cell / grid for cell in refuting_cell] if refuting_cell is not None else None
        ),
        "refuting_lower_hex": refuting_lower.hex() if refuting_lower is not None else None,
        "refuting_lower": refuting_lower,
        "prepare_seconds": P.prepare_seconds,
        "search_seconds": elapsed,
        "seconds_per_node": (elapsed / nodes) if nodes else None,
    }
    return result


def verify_n(
    n_points: int,
    numerator: int,
    denominator: int,
    grid: int = 4_000,
    pressure: int = 3_000,
    precision_bits: int = 128,
    shard_index: int = 0,
    shard_count: int = 1,
    node_cap: int = 0,
    time_cap_seconds: float = 0.0,
    cutoff_cells: Optional[int] = None,
    use_tangent_prune: bool = True,
    progress_every: int = 0,
    presplit_depth: int = 0,
) -> Dict[str, Any]:
    """Decide F_{n-1} >= numerator/denominator on one shard of the initial boxes.

    Returns a dict with ``outcome`` in {ACCEPTED, REFUSED, UNDECIDED}. ACCEPTED
    for a shard means every box of that shard was exhausted; the full inequality is
    accepted only when every shard of the same (n, target, grid, pressure,
    cutoff, presplit_depth) is ACCEPTED. ``cutoff_cells`` defaults to the derived
    value and may only be raised above it; ``time_cap_seconds`` counts from the
    start of the table build; ``presplit_depth`` bisects every initial box that
    many times before sharding, for load balance when there are few initial boxes.
    """

    started = time.perf_counter()
    prepared = prepare(
        n_points, numerator, denominator, grid, pressure, precision_bits, cutoff_cells,
        presplit_depth=presplit_depth,
    )
    remaining = 0.0
    if time_cap_seconds:
        remaining = max(1e-9, time_cap_seconds - (time.perf_counter() - started))
    result = search(
        prepared,
        shard_index=shard_index,
        shard_count=shard_count,
        node_cap=node_cap,
        time_cap_seconds=remaining,
        use_tangent_prune=use_tangent_prune,
        progress_every=progress_every,
    )
    result["time_cap_seconds"] = time_cap_seconds
    result["elapsed_seconds"] = time.perf_counter() - started
    return result


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="verify_n",
        description="Decide the n-point pressure inequality F_{n-1} >= num/den at one grid.",
    )
    parser.add_argument("--n", type=int, required=True, help="number of points (n-1 gaps)")
    parser.add_argument("--num", type=int, required=True)
    parser.add_argument("--den", type=int, required=True)
    parser.add_argument("--grid", type=int, default=4_000)
    parser.add_argument("--pressure", type=int, default=3_000)
    parser.add_argument("--precision", type=int, default=128)
    parser.add_argument("--shard-index", type=int, default=0)
    parser.add_argument("--shard-count", type=int, default=1)
    parser.add_argument("--node-cap", type=int, default=0)
    parser.add_argument("--time-cap", type=float, default=0.0)
    parser.add_argument("--cutoff-cells", type=int, default=None, help="override (may only raise)")
    parser.add_argument("--no-tangent", action="store_true", help="disable the convex tangent prune")
    parser.add_argument("--progress-every", type=int, default=0)
    parser.add_argument("--presplit-depth", type=int, default=0,
                        help="bisect every initial box this many times before sharding")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    args = build_parser().parse_args(argv)
    result = verify_n(
        args.n,
        args.num,
        args.den,
        grid=args.grid,
        pressure=args.pressure,
        precision_bits=args.precision,
        shard_index=args.shard_index,
        shard_count=args.shard_count,
        node_cap=args.node_cap,
        time_cap_seconds=args.time_cap,
        cutoff_cells=args.cutoff_cells,
        use_tangent_prune=not args.no_tangent,
        progress_every=args.progress_every,
        presplit_depth=args.presplit_depth,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
