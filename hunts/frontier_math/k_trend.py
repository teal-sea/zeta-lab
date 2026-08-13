"""ROAD B step 0: does the `k >= 2` margin survive large `k`?

`kpair_identity.joint_search` stops at `k = 6` and reports a worst relative
margin of `+0.3430`, read in `PROOF-LEDGER.md` as "no downward trend in `k`".
That reading is the one thing that would make the whole `k >= 2` programme
safe to invest in, so it is the first thing to attack.

## What the documented table is, and is not

It reproduces **exactly**: re-running `joint_search(ks=(1,2,3,4,6),
restarts=60, n_max=24, seed=20260813)` returns `0.4915 / 0.3719 / 0.3908 /
0.3430 / 0.3618`, delta `0.0000` at every `k`.  The record is sound.

Two caveats it does not carry:

1. **It stops at `k = 6`.**  The trend is read off five points, four of which
   are `k <= 4`.
2. **It is a search, so every entry is an UPPER bound on the true infimum.**
   A stronger search can only push the numbers down, never up.

Also worth knowing before quoting it: `joint_search` threads one RNG through
all requested `k`, so `ks=(4,6)` does not reproduce the `k = 4` entry of a run
made with `ks=(1,2,3,4,6)`.  The numbers are seed-stable only for the exact
`ks` tuple used.

## What a better-resourced search finds

The stock annealer varies `n` by add/remove moves, and past `k >= 12` it
collapses to `n = 1` — it strips the atoms rather than finding a bad
configuration, and then reports a *high* margin because damage has nowhere to
act.  Holding `n` fixed, seeding depths on the corners and raising the
iteration count from 6 000 to 25 000 removes that failure mode:

| k | 4 | 6 | 8 | 12 | 16 | 24 |
|---|---|---|---|---|---|---|
| stock, `n` free | — | — | — | `n=1`, junk | `n=1`, junk | `n=1`, junk |
| fixed `n`, 25k iters | +0.3959 | **+0.2973** | +0.2840 | **+0.2305** | +0.2365 | +0.2533 |

Neither search dominates: at `k = 4` the stock search finds `+0.3430` and this
one only `+0.3959`, because fixing `n` costs it a degree of freedom.  The
best-known worst at each `k` is the minimum over both.

## The finding

**"No downward trend in `k`" does not survive extension past `k = 6`.**
Best-known worst falls from `+0.3430` at `k = 4` to `+0.2305` at `k = 12`,
then flattens around `0.23 .. 0.25` through `k = 24`.  The flattening is not
established — it is equally consistent with the search weakening as `k` grows.

**The margin has not crossed zero anywhere tested**, so `k >= 2` is not
falsified.  What changes is the headline: the number to quote is not `+0.343`
but `+0.2305`, and it is an upper bound rather than a floor.

`WITNESS_K12` below is a saved configuration re-evaluating to `+0.265409`; it
is embedded so the revised figure can be checked in milliseconds instead of
re-run.  (`+0.2305` was observed in a sweep whose RNG stream this standalone
run does not reproduce, and was not saved; `0.2654` is what is pinnable.)

Measured, one instrument, float grade.  Nothing here is a proof of anything.
"""

from __future__ import annotations

import math
import random

import kpair_identity as K

__all__ = [
    "DOCUMENTED",
    "WITNESS_K12",
    "witness_margin",
    "anneal_fixed_n",
    "trend",
    "report",
]

#: `joint_search(ks=(1,2,3,4,6), restarts=60, n_max=24, seed=20260813)`.
DOCUMENTED = {1: 0.4915, 2: 0.3719, 3: 0.3908, 4: 0.3430, 6: 0.3618}

#: A saved `k = 12` configuration: (atoms, centres, depths).
WITNESS_K12 = {
    "xs": [
        40.729292, -28.629452, -9.831523, 40.680692, 40.621102, 78.664993,
        -35.146074, -41.375711, 40.752315, 15.294527, 15.34823, 15.240676,
        -22.657045, 15.292747, 40.734969, 40.701081, 15.359661, -35.090559,
        -91.501993, -22.724899, 53.526619, -9.821708, 109.818249, -47.500028,
    ],
    "ts": [
        27.958514, -3.539941, -192.13351, 8.920615, 65.889751, 34.19648,
        2.68505, -229.686818, 47.100488, 21.72317, -60.215696, -16.172423,
    ],
    "ys": [
        0.5, 0.5, 0.01, 0.5, 0.01, 0.5, 0.5, 0.014345, 0.5, 0.5, 0.01,
        0.483445,
    ],
}


def witness_margin(w=None) -> float:
    """Relative margin of a saved configuration.  Deterministic."""
    w = w or WITNESS_K12
    return K.slack_k(
        w["xs"], list(zip(w["ys"], w["ts"])), 1.0, True
    )


def anneal_fixed_n(k: int, n: int, rng, iters: int = 25000):
    """The annealer with `n` held fixed, which is what stops the `n -> 1` collapse."""
    P = K._ALL_PEAKS
    xs = [rng.choice(P) + rng.gauss(0, 0.3) for _ in range(n)]
    ts = [rng.choice(P) + rng.gauss(0, 0.5) for _ in range(k)]
    ys = [rng.choice([0.01, 0.5]) for _ in range(k)]
    cur = K.slack_k(xs, list(zip(ys, ts)), 1.0, True)
    best, bs = cur, (list(xs), list(ts), list(ys))
    for it in range(iters):
        T = 0.05 * (1 - it / iters) + 1e-5
        nxs, nts, nys = list(xs), list(ts), list(ys)
        r = rng.random()
        if r < 0.45:
            nxs[rng.randrange(n)] += rng.gauss(
                0, 0.8 if rng.random() < 0.7 else 4.0)
        elif r < 0.85:
            nts[rng.randrange(k)] += rng.gauss(
                0, 1.0 if rng.random() < 0.7 else 5.0)
        else:
            i = rng.randrange(k)
            nys[i] = min(0.5, max(0.01, nys[i] + rng.gauss(0, 0.10)))
        new = K.slack_k(nxs, list(zip(nys, nts)), 1.0, True)
        if new < cur or rng.random() < math.exp(-(new - cur) / T):
            xs, ts, ys, cur = nxs, nts, nys, new
            if cur < best:
                best, bs = cur, (list(xs), list(ts), list(ys))
    return best, bs


def trend(ks=(4, 6, 8, 12), ns=(8, 16, 24), restarts: int = 3,
          seed: int = 2718, iters: int = 25000) -> dict:
    rng = random.Random(seed)
    out = {}
    for k in ks:
        b = None
        for n in ns:
            for _ in range(restarts):
                s, _st = anneal_fixed_n(k, n, rng, iters)
                if b is None or s < b:
                    b = s
        out[k] = b
    return out


def report() -> dict:
    print("=" * 68)
    print("k-trend: does the k >= 2 margin survive large k?")
    print("=" * 68)
    print(f"\n  saved k=12 witness margin  {witness_margin():+.6f}")
    print(f"  documented worst (k <= 6)  {min(DOCUMENTED.values()):+.4f}")
    return {"witness_k12": witness_margin(), "documented": DOCUMENTED}


if __name__ == "__main__":
    report()
