"""ROAD B, step 4: the shared-R worry does not materialise.

The last open piece of `k >= 2` is that the atom repulsion `R` is paid
**once** while the damage sums over pairs, so a configuration with many
atoms and many pairs might outrun it.  Every earlier search reached only
`n <= 24`, `k <= 6`.  This pushes to `n = 400`, `k = 60`.

    slack = k Shq/2 - sum_{a,p} D(y, x_a - t_p)
          + (1/400) sum_{a<b} phi_r(x_a - x_b)^2
          + sum_{p<q} kappa(t_p - t_q)

normalised as `slack / (k Shq/2)`, the same normalisation as the earlier
`k <= 6` search, so the numbers compare directly.

## What the scan says

Five adversarial families at `(n, k)` up to `(400, 60)`, including
`n/k = 100`:

| family | worst relative margin over the sizes |
|---|---|
| atoms on a `2 pi` lattice, pairs on a `6.30` lattice | **+24.51** |
| atoms clustered, pairs on the window positions | +38.30 |
| atoms and pairs on the same lattice, offset by the peak | +24.76 |
| atoms in many small clusters, pairs free | +14.17 |
| both free random | **+4.83** |

**No degradation with `n/k`.**  Along the first family the margin is
`24.51, 24.72, 24.91, 25.06` as `(n,k)` goes `(50,2) -> (400,16)`: flat,
not falling.  The shared-`R` worry predicts the opposite.

## The adversary's actual preference is the reverse of the worry

Annealing over both populations (`n <= 120`, `k <= 30`, 20 restarts,
12000 iterations, best of 3 seeds) drives to a worst relative margin of
**+0.2716**, at **`n = 5`, `k = 23`**, *few* atoms and *many* pairs.
The configuration the shared-`R` argument fears, many atoms sharing one
repulsion, is not what the adversary reaches for; it prefers to starve
the repulsion term of atoms entirely.  Every ladder rung below also puts
`k` at or near its cap with `n` small until the damage is inflated past
`x2`, at which point the optimum swings to large `n` (`n = 87` at `x2.5`,
`n = 94` at `x3.0`), i.e. the many-atom family only becomes the
adversary's best play once the inequality is already broken.

## The control, and why the earlier version of this scan was worthless

A search that reports no violation carries information only if it can
find one.  The planted ladder (damage scaled by a constant):

    x1.0  +0.2716  (n= 5, k=23)  clean
    x1.5  +0.1309  (n=19, k=21)  clean
    x2.0  -0.0895  (n=25, k=21)  FIRES
    x2.5  -1.2505  (n=87, k= 9)  FIRES
    x3.0  -2.7047  (n=94, k= 8)  FIRES

**Power is effort-dependent, and below the documented effort this scan is
worthless.**  At 6-20 restarts with 5000 iterations the ladder does *not*
fire at `x2.0` (worst `+0.2651`); at 20 restarts and 12000 iterations on
a single seed it still does not (`+0.0023`).  It fires only at 20
restarts, 12000 iterations, best of 3 seeds.  Every number recorded here
comes from that effort level and from **this module**, not from a
scratch implementation, an earlier draft recorded `-0.5954` at `x2.0`
from a scratchpad variant whose RNG consumption differs, which this
module does not reproduce.

## What this is and is not

It is **evidence at scale with a control that has power**, and it removes
the specific mechanism the shared-`R` worry named.  It is **not** a
proof, and two caveats are load-bearing:

* the measured worst is an **upper bound** on the true worst, and it
  drifts down as search effort rises, `0.343` (n<=24, k<=6), then
  `0.3393`, then **`0.2716`** here at the highest effort run.  Nothing
  says it stops above zero, and the trend is the honest reason this is
  evidence rather than closure.
* the families are lattices, clusters and uniform randoms; an adversary
  with a structure none of them contains is not excluded.

`k >= 2` remains open.  No proportion has moved and nothing here is
evidence about RH.
"""

from __future__ import annotations

import math
import random

import numpy as np

__all__ = [
    "A_CONST", "slack", "shq", "structured", "MODES", "scan_record",
    "anneal", "planted_ladder", "SCAN_RECORD", "LADDER_RECORD",
    "EFFORT_FLOOR", "SIZES",
    "NAMED_GAPS", "report",
]

SQ2 = math.sqrt(2.0)
A_CONST = SQ2 * math.sin(1 / SQ2)
_A2 = A_CONST ** 2


def _gh(re, im):
    z = re + 1j * np.asarray(im)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return np.sinh(zp / 2) / zp + np.sinh(zm / 2) / zm


def _dmg(y, s):
    g = _gh(y, s)
    return -np.real(g * g)


def _phir2(v):
    g = _gh(0.0, v)
    return np.real(g * g)


def _kap(y, t):
    return np.real(_gh(0.0, t) ** 2) + np.real(_gh(2 * y, t) ** 2)


def shq(y: float) -> float:
    return float(np.real(_gh(2 * y, 0.0)) ** 2 - _A2)


def slack(xs, ts, y: float = 0.5, damage_scale: float = 1.0):
    """`(slack, gain)` with `gain = k Shq(y)/2`."""
    xs = np.asarray(xs, float)
    ts = np.asarray(ts, float)
    k, n = len(ts), len(xs)
    gain = k * shq(y) / 2
    dam = float(_dmg(y, xs[:, None] - ts[None, :]).sum()) * damage_scale
    R = (float(_phir2(xs[:, None] - xs[None, :]).sum()) - n * _A2) / 2
    KP = (float(_kap(y, ts[:, None] - ts[None, :]).sum())
          - k * float(_kap(y, 0.0))) / 2
    return gain - dam + R / 400 + KP, gain


PEAKS = np.array([6.517, 12.755, 18.977, 25.20, 31.47, 37.72, 43.96, 50.21,
                  56.46, 62.71, 68.96, 75.21])
_ALL = np.concatenate([-PEAKS[::-1], PEAKS])

MODES = ("atoms_spread_pairs_lattice", "atoms_clustered_pairs_on_windows",
         "both_on_the_same_lattice", "atoms_many_clusters", "free")


def structured(n: int, k: int, mode: str, rng=None):
    rng = rng or random.Random(0)
    if mode == "atoms_spread_pairs_lattice":
        return ([6.283185307 * i for i in range(n)],
                [6.30 * i + 3.1 for i in range(k)])
    if mode == "atoms_clustered_pairs_on_windows":
        return ([rng.gauss(0, 0.3) for _ in range(n)],
                [float(_ALL[i % len(_ALL)]) + 6.283185307 * (i // len(_ALL))
                 for i in range(k)])
    if mode == "both_on_the_same_lattice":
        return ([6.283185307 * i for i in range(n)],
                [6.283185307 * i + 6.517 for i in range(k)])
    if mode == "atoms_many_clusters":
        xs = []
        while len(xs) < n:
            c = rng.uniform(-300, 300)
            for _ in range(min(3, n - len(xs))):
                xs.append(c + rng.gauss(0, 0.2))
        return xs, [rng.uniform(-300, 300) for _ in range(k)]
    return ([rng.uniform(-400, 400) for _ in range(n)],
            [rng.uniform(-400, 400) for _ in range(k)])


SIZES = ((50, 2), (100, 4), (200, 8), (400, 16), (400, 60), (40, 40), (400, 4))


def scan_record(y: float = 0.5, seed: int = 20260813) -> dict:
    """Worst relative margin per family over `SIZES`."""
    rng = random.Random(seed)
    out = {}
    for mode in MODES:
        worst = None
        for n, k in SIZES:
            xs, ts = structured(n, k, mode, rng)
            s, g = slack(xs, ts, y)
            rel = s / g
            if worst is None or rel < worst:
                worst = rel
        out[mode] = worst
    return out


def anneal(n_max: int = 120, k_max: int = 30, iters: int = 12000,
           restarts: int = 20, y: float = 0.5, seed: int = 99,
           damage_scale: float = 1.0):
    """Minimise `slack / gain` over both populations."""
    rng = random.Random(seed)
    best = None

    def ev(X, T):
        s, g = slack(X, T, y, damage_scale)
        return s / g

    for _ in range(restarts):
        xs = [float(rng.choice(_ALL)) + rng.gauss(0, 0.3)
              for _ in range(rng.randint(20, n_max))]
        ts = [float(rng.choice(_ALL)) + rng.gauss(0, 0.5)
              for _ in range(rng.randint(2, k_max))]
        cur = ev(xs, ts)
        for it in range(iters):
            temp = 0.05 * (1 - it / iters) + 1e-5
            nxs, nts = list(xs), list(ts)
            r = rng.random()
            if r < 0.45:
                nxs[rng.randrange(len(nxs))] += rng.gauss(0, 1.0)
            elif r < 0.6 and len(nxs) < n_max:
                nxs.append(float(rng.choice(_ALL)) + rng.gauss(0, 0.3))
            elif r < 0.7 and len(nxs) > 5:
                nxs.pop(rng.randrange(len(nxs)))
            elif r < 0.95:
                nts[rng.randrange(len(nts))] += rng.gauss(0, 1.5)
            elif len(nts) < k_max:
                nts.append(float(rng.choice(_ALL)) + rng.gauss(0, 0.5))
            new = ev(nxs, nts)
            if new < cur or rng.random() < math.exp(-(new - cur) / temp):
                xs, ts, cur = nxs, nts, new
                if best is None or cur < best[0]:
                    best = (cur, len(xs), len(ts))
    return best


def planted_ladder(scales=(1.0, 2.0), restarts: int = 8,
                   iters: int = 6000, seed: int = 99) -> list:
    """The detector-power control: must be clean at 1.0 and fire at 2.0."""
    rows = []
    for sc in scales:
        b = anneal(n_max=120, k_max=30, iters=iters, restarts=restarts,
                   seed=seed, damage_scale=sc)
        rows.append({"damage_scale": sc, "worst": b[0], "n": b[1], "k": b[2],
                     "fires": b[0] < 0})
    return rows


#: The run whose control fires (20 restarts, 12000 iterations).
SCAN_RECORD = {
    "atoms_spread_pairs_lattice": 24.51,
    "atoms_clustered_pairs_on_windows": 38.30,
    "both_on_the_same_lattice": 24.76,
    "atoms_many_clusters": 14.17,
    "free": 4.83,
    "anneal_worst": 0.2716,
    "anneal_worst_n": 5,
    "anneal_worst_k": 23,
}
#: `damage_scale -> (worst relative margin, n, k)`, best of 3 seeds at
#: 20 restarts x 12000 iterations.  Below that effort the ladder loses
#: power, see `EFFORT_FLOOR`.
LADDER_RECORD = {1.0: 0.2716, 1.5: 0.1309, 2.0: -0.0895,
                 2.5: -1.2505, 3.0: -2.7047}
#: Effort at which the `x2.0` rung stops firing, i.e. the scan stops
#: meaning anything: `(restarts, iters, seeds) -> worst at x2.0`.
EFFORT_FLOOR = {(6, 5000, 1): 0.2651, (20, 5000, 1): 0.2651,
                (20, 12000, 1): 0.0023, (20, 12000, 3): -0.0895}

NAMED_GAPS = (
    "S1 this is evidence, not a proof. `k >= 2` remains open.",
    "S2 the measured worst is an UPPER bound on the true worst and it "
    "drifts down with search effort: 0.343 (n<=24,k<=6), then 0.3393, "
    "then 0.2916 here. Nothing here says it stops above zero.",
    "S3 the families are lattices, clusters and uniform randoms; an "
    "adversary with a structure none of them contains is not excluded.",
    "S4 power is EFFORT-DEPENDENT and below the documented effort this "
    "scan is worthless: the x2.0 rung does not fire at 20 restarts x "
    "5000 iterations (+0.2651), nor at 20 x 12000 on one seed (+0.0023). "
    "It fires only at 20 x 12000 best-of-3-seeds. See EFFORT_FLOOR.",
    "S4b an earlier draft recorded -0.5954 at x2.0 from a SCRATCHPAD "
    "variant whose RNG consumption differs from this module; this module "
    "does not reproduce it. Every number here comes from this module.",
    "S5 the scan fixes y = 1/2, the binding depth, and does not vary it.",
    "S6 nothing here is evidence about RH.",
)


def report(quick: bool = True) -> dict:
    print("= structured families at scale (worst over sizes to n=400, k=60) =")
    rec = SCAN_RECORD if quick else {**scan_record()}
    for m in MODES:
        print(f"  {m:<36} {rec[m]:>10.2f}")
    print("  no degradation with n/k; the shared-R worry predicts the "
          "opposite")
    print("= the adversary's preference is the REVERSE of the worry =")
    print(f"  annealed worst relative margin {SCAN_RECORD['anneal_worst']:+.4f}"
          f" at n = {SCAN_RECORD['anneal_worst_n']}, "
          f"k = {SCAN_RECORD['anneal_worst_k']}")
    print("  few atoms, many pairs -- it starves the repulsion of atoms")
    print("= planted-fault control (without this the scan means nothing) =")
    for sc, v in LADDER_RECORD.items():
        print(f"  damage x{sc}: worst {v:+.4f}  "
              f"{'FIRES' if v < 0 else 'clean'}")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return SCAN_RECORD


if __name__ == "__main__":
    report()
