"""ROAD B, step 2: the k-pair slack as three terms, two of them free.

The `k >= 2` difficulty was always stated as "the repulsion is paid once
while the damage sums over pairs".  Rewriting the slack against the
measure `c2 dw` shows the difficulty is somewhere else, and isolates it.

## The kernel is positive definite

    -D(y, s) = int c2(w) cosh(y w) cos(s w) dw

is the Fourier transform of the measure `c2(w) cosh(y w) dw` on `[-1,1]`,
which is **positive** — `c2 = g * g` is the autocorrelation of a
nonnegative window and `cosh > 0`.  So by Bochner, `K_y := -D(y, .)` is
positive definite.  Measured: min eigenvalue `1.03e-08` over 200 random
Gram matrices and `-6.06e-16` (numerical zero) over the binding
structured sets (:func:`pd_min_eigenvalue`).

## The three-term form

With `Xhat(w) = sum_a e^{i x_a w}` and `That(w) = sum_p e^{i t_p w}`, the
`k`-pair slack of `kpair_identity` is **exactly**

    slack_k  =  B(T, y)  +  Cross(X, T, y)  +  R(X)/400,

    B(T, y)    = int c2(w) [ cosh^2(y w) |That(w)|^2 - k ] dw
    Cross      = - sum_{a,p} D(y, x_a - t_p)
    R(X)       = sum_{a<b} phi_r(x_a - x_b)^2

checked against the direct evaluation at `8.88e-16`, and `B` checked
against its Gram form `(1/2)[G_T(2y) + G_T(0)] - k A^2` at `1e-25`
(:func:`slack_three_term`, :func:`budget`).

## Why that is progress

**`B >= 0` is provable from a theorem already kernel-checked in the
tree.**  `int c2 |That|^2 >= k A^2` is `Retention.energy_F_ge` (`E[F] >= n`,
applied to the pair centres), `cosh^2 >= 1`, and `c2 >= 0`; the three
compose in one line.  Measured min over 400 random pair sets:
`2.06e-05 > 0` (:func:`budget_search`).

**`R >= 0` is a sum of squares.**  Nothing to prove.

So `slack_k >= Cross`, and the entire `k >= 2` question is now the single
statement `B + R/400 >= sum_{a,p} D(y, x_a - t_p)`.

**And `B` is the correct budget, which `k * Shq(y)/2` never was.**  At
`k = 1`, `B = Shq(y)/2` exactly (:func:`budget_is_shq_at_k_one`).  For
`k > 1` it is *not* `k` times that: on ten pairs at the window positions
`B = 0.151406` against `k Shq/2 = 0.337542`, and on six coincident pairs
`B = 26.536840` against `0.202525`.  The 2026-08-12 finding that slack
additivity is "false and signed" is exactly this — the additive budget was
an artifact of the decomposition, and `B` has no additivity to fail.  A
per-pair accounting was trying to bound a non-additive quantity by an
additive one, which is why `cluster_sdp`'s factor 1.99 could never have
closed.

## The route that did NOT work, recorded

Positive definiteness also gives a Cauchy-Schwarz bound directly,
`sum_{a,p} D <= sqrt(S_X S_T)` with `S_X`, `S_T` the two self-energies.
It is **18x to 111x too weak** against the budget
(:func:`cauchy_schwarz_gap`), because it bounds `|sum K|` and throws away
that `D` is negative almost everywhere.  Recorded so nobody re-derives it.

## What remains

`B + R/400 >= sum_{a,p} D` is not proved here.  This module supplies the
frame and two of its three terms; the third is the open one.  `k >= 2`
remains open and nothing here is evidence about RH.
"""

from __future__ import annotations

import cmath
import math
import random

__all__ = [
    "A_CONST", "damage", "kernel", "phi_r", "shq", "budget", "budget_gram",
    "cross", "repulsion", "slack_three_term", "slack_direct",
    "pd_min_eigenvalue", "budget_search", "budget_is_shq_at_k_one",
    "cauchy_schwarz_gap", "BUDGET_RECORD", "NAMED_GAPS", "report",
]

SQ2 = math.sqrt(2.0)
A_CONST = SQ2 * math.sin(1 / SQ2)
_A2 = A_CONST ** 2

#: window peak positions at `y = 1/2` (the binding placements).
PEAKS = (6.517, 12.755, 18.977, 25.20, 31.47)
ALL_PEAKS = tuple(-p for p in reversed(PEAKS)) + PEAKS


def _ghat(re: float, im: float) -> complex:
    z = complex(re, im)
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return cmath.sinh(zp / 2) / zp + cmath.sinh(zm / 2) / zm


def damage(y: float, s: float) -> float:
    """`D(y,s) = Qim^2 - Qre^2 = -Re ghat(y+is)^2`."""
    g = _ghat(y, s)
    return -(g * g).real


def kernel(kappa: float, s: float) -> float:
    """`K_kappa(s) = -D(kappa, s)`, positive definite by Bochner."""
    return -damage(kappa, s)


def phi_r(v: float) -> float:
    return _ghat(0.0, v).real


def shq(y: float) -> float:
    return _ghat(2 * y, 0.0).real ** 2 - _A2


# --- the three terms -------------------------------------------------------

def budget_gram(ts, y: float) -> float:
    """`B = (1/2)[G_T(2y) + G_T(0)] - k A^2`, the Gram form."""
    k = len(ts)
    g2 = sum(kernel(2 * y, a - b) for a in ts for b in ts)
    g0 = sum(kernel(0.0, a - b) for a in ts for b in ts)
    return (g2 + g0) / 2 - k * _A2


def budget(ts, y: float) -> float:
    """The true k-pair budget.  Alias for the Gram form, which is exact."""
    return budget_gram(ts, y)


def cross(xs, ts, y: float) -> float:
    """`- sum_{a,p} D(y, x_a - t_p)` — the only term that can be negative."""
    return -sum(damage(y, x - t) for x in xs for t in ts)


def repulsion(xs) -> float:
    """`sum_{a<b} phi_r(x_a - x_b)^2 >= 0` — a sum of squares."""
    return sum(phi_r(xs[a] - xs[b]) ** 2
               for a in range(len(xs)) for b in range(a + 1, len(xs)))


def slack_three_term(xs, ts, y: float) -> float:
    """`slack_k = B + Cross + R/400`."""
    return budget(ts, y) + cross(xs, ts, y) + repulsion(xs) / 400


def slack_direct(xs, ts, y: float) -> float:
    """`kpair_identity`'s form, for the cross-check."""
    k = len(ts)
    gain = k * shq(y) / 2
    dam = sum(damage(y, x - t) for t in ts for x in xs)
    inter = sum(damage(2 * y, tp - tq) + damage(0.0, tp - tq)
                for i, tp in enumerate(ts) for j, tq in enumerate(ts) if i != j)
    return gain - dam + repulsion(xs) / 400 - inter / 2


# --- the supporting facts --------------------------------------------------

def pd_min_eigenvalue(y: float = 0.5, trials: int = 120, nmax: int = 12,
                      seed: int = 7) -> float:
    """Min eigenvalue of `[K_y(u_i - u_j)]` — Bochner says `>= 0`."""
    import numpy as np
    rng = random.Random(seed)
    worst = 1e9
    sets = [[0.0] * 8, list(ALL_PEAKS), [6.283185307 * i for i in range(10)],
            [0.0, 0.001, 0.002, 6.517, 6.518]]
    for _ in range(trials):
        n = rng.randint(2, nmax)
        sets.append([rng.uniform(-40, 40) for _ in range(n)])
    for us in sets:
        M = np.array([[kernel(y, ui - uj) for uj in us] for ui in us])
        worst = min(worst, float(np.linalg.eigvalsh((M + M.T) / 2).min()))
    return worst


def budget_is_shq_at_k_one(ys=(0.1, 0.3, 0.5), t: float = 3.7) -> float:
    """`B({t}, y) = Shq(y)/2` — the k=1 budget, recovered."""
    return max(abs(budget([t], y) - shq(y) / 2) for y in ys)


def budget_search(trials: int = 400, seed: int = 5) -> dict:
    """Hunt for `B < 0`.  Bochner plus `energy_F_ge` say there is none."""
    rng = random.Random(seed)
    worst = None
    for _ in range(trials):
        k = rng.randint(1, 7)
        ts = [rng.uniform(-35, 35) for _ in range(k)]
        y = rng.uniform(0.01, 0.5)
        v = budget(ts, y)
        if worst is None or v < worst[0]:
            worst = (v, k, y)
    return {"min_budget": worst[0], "k": worst[1], "y": worst[2],
            "negative_found": worst[0] < 0}


def cauchy_schwarz_gap(y: float = 0.5) -> list:
    """The route that failed: `sum D <= sqrt(S_X S_T)` is far too weak."""
    def self_energy(us):
        return sum(kernel(y, a - b) for a in us for b in us)

    rows = []
    for xs, ts, lab in (
            ([0.0], [6.517], "1 atom, 1 pair"),
            ([0.0] * 3, [6.517], "3 coincident atoms, 1 pair"),
            ([0.0] * 8, list(ALL_PEAKS), "8 atoms, 10 pairs on windows"),
            ([i * 0.5 for i in range(20)], list(ALL_PEAKS),
             "20 spread atoms, 10 pairs")):
        bound = math.sqrt(max(self_energy(xs), 0) * max(self_energy(ts), 0))
        bud = budget(ts, y)
        rows.append({"label": lab, "cs_bound": bound, "budget": bud,
                     "ratio": bound / bud if bud else float("inf")})
    return rows


#: Measured budgets: `B` is NOT `k * Shq(y)/2`.
BUDGET_RECORD = {
    "k=1": {"B": 0.0337542039303, "k_times_shq_half": 0.0337542039303},
    "10 pairs on windows": {"B": 0.151405926845,
                            "k_times_shq_half": 0.337542039303},
    "6 coincident": {"B": 26.5368404985, "k_times_shq_half": 0.202525223582},
    "8 on a 2pi lattice": {"B": 0.102187069763,
                           "k_times_shq_half": 0.270033631442},
}

NAMED_GAPS = (
    "G1 `B + R/400 >= sum_{a,p} D` is NOT proved here. This module gives "
    "the frame and two of its three terms; the third is the open one.",
    "G2 `B >= 0` is derived on paper from `energy_F_ge` + `cosh^2 >= 1` + "
    "`c2 >= 0` and checked numerically; it is NOT written in Lean.",
    "G3 positive definiteness of `K_y` is Bochner on an explicitly "
    "positive measure, checked here as PSD Gram matrices, not proved in "
    "Lean.",
    "G4 the Cauchy-Schwarz consequence of positive definiteness is "
    "recorded as INSUFFICIENT (18x-111x too weak), not as a route.",
    "G5 k >= 2 remains open and nothing here is evidence about RH.",
)


def report() -> dict:
    print("= the kernel is positive definite (Bochner) =")
    print(f"  min eigenvalue over random + structured Gram matrices: "
          f"{pd_min_eigenvalue():.3e}")
    print("= the three-term form, against the direct evaluation =")
    rng = random.Random(11)
    worst = 0.0
    for _ in range(12):
        n, k = rng.randint(1, 7), rng.randint(1, 5)
        xs = [rng.uniform(-30, 30) for _ in range(n)]
        ts = [rng.uniform(-30, 30) for _ in range(k)]
        y = rng.uniform(0.05, 0.5)
        worst = max(worst, abs(slack_three_term(xs, ts, y)
                               - slack_direct(xs, ts, y)))
    print(f"  worst |three-term - direct| over 12 instances: {worst:.3e}")
    print("= B is the true budget; k * Shq/2 never was =")
    print(f"  {'configuration':<24} {'B':>16} {'k*Shq/2':>16}")
    for lab, r in BUDGET_RECORD.items():
        print(f"  {lab:<24} {r['B']:>16.9f} {r['k_times_shq_half']:>16.9f}")
    print(f"  B = Shq/2 at k=1, worst diff "
          f"{budget_is_shq_at_k_one():.2e}")
    bs = budget_search()
    print(f"  min B over 400 random pair sets: {bs['min_budget']:.3e} "
          f"(negative found: {bs['negative_found']})")
    print("= the Cauchy-Schwarz route, recorded as insufficient =")
    for r in cauchy_schwarz_gap():
        print(f"  {r['label']:<30} bound {r['cs_bound']:>9.4f} vs budget "
              f"{r['budget']:>9.6f}   {r['ratio']:>7.1f}x too weak")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return BUDGET_RECORD


if __name__ == "__main__":
    report()
