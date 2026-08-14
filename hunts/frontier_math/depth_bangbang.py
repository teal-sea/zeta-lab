"""ROAD B: does the depth quantifier in `k >= 2` collapse to the corners?

**NO. (BB) IS FALSE, see `COUNTEREXAMPLE` below.  This module is kept as
the record of a claim that a sampling sweep supported and a targeted search
destroyed within the hour.**

The `k >= 2` statement quantifies over `k` depths `y_p` ranging over a
continuum, `[0, 1/2]^k`, on top of the atoms and the centres.  This module
tested one structural claim that would have removed that continuum:

    (BB)  with atoms, centres and the other depths held fixed, the relative
          margin  slack_k / sum_p Shq(y_p)/2  attains its minimum over a
          single `y_p` at an ENDPOINT of the allowed range.

Had (BB) held, the worst case over depths would live on the `2^k` corners of
`[y_min, 1/2]^k`, i.e. `k + 1` cases once the pairs are identified, a
continuum quantifier made finite.  **It does not hold, so that reduction is
not available and the depth quantifier stays continuous.**

## How it died, and the methodological point

Random sampling said `0 / 540`: no interior minimum in 540 configurations,
random peak-seeded and lattice, at grid 61 and 241, against a planted-fault
control firing 60/60.  That is a real measurement and it is **worthless as
evidence for (BB)**, because sampling looks where the measure is, not where
the adversary is.

An annealer pointed at the quantity the claim forbids (maximise
`min(endpoints) - min(all)` over atoms, centres and the other depths) found
a violation at the **smallest case it was given**, `k = 2, n = 2`, in
minutes.  The lesson is the one this hunt keeps relearning: a sweep that
does not optimise against its own claim measures the sweep, not the claim.

## Why it was worth testing

The binding configurations the joint search returns are visibly bang-bang:
at `k = 4` the extremum came back with depths `[0.01, 0.025, 0.5, 0.5]`, and
re-running under depth floors from `0.001` to `0.30` the extremum sat on the
floor and the ceiling every time, never in between (worst relative margin
stayed in `0.335 .. 0.399` throughout, so the floor is also not an artifact
of the degenerate `y -> 0` corner, a corner an earlier search in this hunt
did collapse into, which is why the objective is the relative one).

## The control, and why the first one was worthless

A scan that reports "no interior minimum" is worth nothing unless it can be
shown to *find* one.  The first control here planted a fixed-height bump and
fired on 3 of 60 cases, the bump was simply smaller than the variation it
was competing with, so it tested nothing.  Scaling the planted bump to each
scan's own range makes the planted minimum genuinely global, and the detector
then fires 60/60.  Only against that does `0 / 540` mean anything.

## What survives

Only this: the *binding* configurations the joint search returns still look
bang-bang (at `k = 12` ten of twelve depths sit within `0.02` of an end).  So
(BB) may well hold near the infimum while failing in general, the
counterexample sits at relative margin `0.7475`, three times the binding
`~0.23`, i.e. nowhere near where the question is decided.  That is a much
weaker and much harder statement: it needs the region where it holds to be
characterised first, and no such characterisation is in hand.  It is not a
route.

## Status

(BB) is **refuted** as a universal claim.  The corner reduction is not
available.  Nothing here is a proof of `k >= 2` and nothing here moves the
constant.
"""

from __future__ import annotations

import math
import random

import kpair_identity as K

__all__ = [
    "Y_LO",
    "Y_HI",
    "GRID",
    "COUNTEREXAMPLE",
    "counterexample_advantage",
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

#: The configuration that refutes (BB).  Scanning `y_0` over `[0.01, 0.5]`:
#: endpoints give `3.233353` and `0.749598`, and the minimum is `0.747516`
#: at `y_0 = 0.35104`, interior, by `2.0823e-03`.  Coarse (61 points) and
#: fine (2001 points) agree to `5e-07`, so it is not a grid artifact.
COUNTEREXAMPLE = {
    "xs": [-48.71286266, -42.68243098],
    "ts": [26.80790727, 20.19203376],
    "ys": [0.46269921, 0.01],
    "index": 0,
    "advantage": 2.082294e-03,
    "argmin": 0.35104,
}


def counterexample_advantage(fine: bool = True) -> float:
    """How far the interior minimum beats the better endpoint.  Positive."""
    c = COUNTEREXAMPLE
    grid = (
        [Y_LO + (Y_HI - Y_LO) * j / 2000 for j in range(2001)]
        if fine else GRID
    )
    vals = scan_depth(c["xs"], c["ts"], c["ys"], c["index"], grid)
    return min(vals[0], vals[-1]) - min(vals)


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
