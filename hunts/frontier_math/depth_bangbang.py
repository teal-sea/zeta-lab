"""ROAD B: does the depth quantifier in `k >= 2` collapse to the corners?

The `k >= 2` statement quantifies over `k` depths `y_p` ranging over a
continuum, `[0, 1/2]^k`, on top of the atoms and the centres.  This module
tests one structural claim that would remove that continuum:

    (BB)  with atoms, centres and the other depths held fixed, the relative
          margin  slack_k / sum_p Shq(y_p)/2  attains its minimum over a
          single `y_p` at an ENDPOINT of the allowed range.

If (BB) holds, the worst case over depths lives on the `2^k` corners of
`[y_min, 1/2]^k`, and since the pairs are interchangeable that is `k + 1`
cases: `j` pairs shallow and `k - j` pairs at `1/2`.  A continuum quantifier
becomes a finite one.

## Why it was worth testing

The binding configurations the joint search returns are visibly bang-bang:
at `k = 4` the extremum came back with depths `[0.01, 0.025, 0.5, 0.5]`, and
re-running under depth floors from `0.001` to `0.30` the extremum sat on the
floor and the ceiling every time, never in between (worst relative margin
stayed in `0.335 .. 0.399` throughout, so the floor is also not an artifact
of the degenerate `y -> 0` corner — a corner an earlier search in this hunt
did collapse into, which is why the objective is the relative one).

## The control, and why the first one was worthless

A scan that reports "no interior minimum" is worth nothing unless it can be
shown to *find* one.  The first control here planted a fixed-height bump and
fired on 3 of 60 cases — the bump was simply smaller than the variation it
was competing with, so it tested nothing.  Scaling the planted bump to each
scan's own range makes the planted minimum genuinely global, and the detector
then fires 60/60.  Only against that does `0 / 540` mean anything.

## Status

Measured, one instrument, float grade.  (BB) is **not** proved, and a proof
would need `slack_k` to be shown quasi-concave in each `y_p` separately.
Nothing here is a proof of `k >= 2` and nothing here moves the constant.  Nothing
here is evidence about RH.
"""

from __future__ import annotations

import math
import random

import kpair_identity as K

__all__ = [
    "Y_LO",
    "Y_HI",
    "GRID",
    "scan_depth",
    "has_interior_minimum",
    "sweep",
    "planted_fault_control",
    "report",
]

#: The depth range.  `Y_LO` is a floor, not `0`: at `y = 0` the pair
#: degenerates (gain and damage vanish together) and the relative margin is
#: a `0/0`.
Y_LO, Y_HI = 0.01, 0.5

#: 61 points is enough to separate an endpoint minimum from an interior one
#: at the scale the bump control operates on; `sweep` re-checks at 241.
GRID = [Y_LO + (Y_HI - Y_LO) * j / 60 for j in range(61)]


def _peaks() -> list:
    return K._ALL_PEAKS


def scan_depth(xs, ts, ys, i: int, grid=None) -> list:
    """The relative margin as `y_i` runs over `grid`, everything else fixed."""
    g = grid or GRID
    out = []
    for v in g:
        yy = list(ys)
        yy[i] = v
        out.append(K.slack_k(xs, list(zip(yy, ts)), 1.0, True))
    return out


def has_interior_minimum(vals, tol: float = 1e-12) -> bool:
    """True if the minimum beats both endpoints strictly."""
    m = min(vals)
    am = vals.index(m)
    if am in (0, len(vals) - 1):
        return False
    return min(vals[0], vals[-1]) - m > tol


def _random_config(rng, structured: bool = False):
    k = rng.randint(2, 4)
    n = rng.randint(1, 10)
    if structured:
        L = rng.choice([6.283185307, 6.5, 12.7, 13.03, 19.0, 25.5])
        x0, t0 = rng.uniform(-3, 3), rng.uniform(-3, 3)
        xs = [x0 + j * L for j in range(n)]
        ts = [t0 + j * L for j in range(k)]
    else:
        P = _peaks()
        xs = [rng.choice(P) + rng.gauss(0, 0.4) for _ in range(n)]
        ts = [rng.choice(P) + rng.gauss(0, 0.6) for _ in range(k)]
    ys = [rng.uniform(Y_LO, Y_HI) for _ in range(k)]
    return xs, ts, ys, k


def sweep(trials: int = 120, seed: int = 99, structured: bool = False,
          fine: bool = False) -> dict:
    """Count interior minima over random or lattice configurations."""
    rng = random.Random(seed)
    grid = (
        [Y_LO + (Y_HI - Y_LO) * j / 240 for j in range(241)] if fine else GRID
    )
    interior = 0
    for _ in range(trials):
        xs, ts, ys, k = _random_config(rng, structured)
        vals = scan_depth(xs, ts, ys, rng.randrange(k), grid)
        if has_interior_minimum(vals):
            interior += 1
    return {"trials": trials, "interior": interior, "structured": structured}


def planted_fault_control(trials: int = 60, seed: int = 99,
                          centre: float = 0.25, width: float = 0.04) -> dict:
    """Plant an interior minimum and check the scan finds it.

    The bump is scaled to each scan's own range, so the planted point really
    is the global minimum.  A fixed-height bump does not do this and produced
    a 3/60 detection rate, which would have made the clean result meaningless.
    """
    rng = random.Random(seed)
    fired = 0
    for _ in range(trials):
        xs, ts, ys, k = _random_config(rng)
        vals = scan_depth(xs, ts, ys, rng.randrange(k))
        amp = (max(vals) - min(vals)) or 1.0
        bumped = [
            vals[j] - 2.0 * amp * math.exp(-((GRID[j] - centre) / width) ** 2)
            for j in range(len(GRID))
        ]
        if has_interior_minimum(bumped):
            fired += 1
    return {"trials": trials, "fired": fired}


def report() -> dict:
    print("=" * 70)
    print("Depth bang-bang: is the worst case over depths on the corners?")
    print("=" * 70)
    ctrl = planted_fault_control()
    print(f"\n  planted-fault control   {ctrl['fired']}/{ctrl['trials']} fired")
    rnd = sweep()
    print(f"  random configurations   {rnd['interior']}/{rnd['trials']} interior minima")
    lat = sweep(structured=True, seed=7)
    print(f"  lattice configurations  {lat['interior']}/{lat['trials']} interior minima")
    return {"control": ctrl, "random": rnd, "lattice": lat}


if __name__ == "__main__":
    report()
