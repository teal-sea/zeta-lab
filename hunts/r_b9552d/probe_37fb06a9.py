"""Blocker 2, `k >= 3`: measuring where the two-species centre-gas term T1 resists.

Reads `hunts/frontier_math/K2-TWO-SPECIES.md` section 5 and
`hunts/frontier_math/two_species.py`.  Nothing here is proved; nothing here
is evidence about RH; the reserved certification word is not used.

## What T1 is

`K2-TWO-SPECIES.md` section 5 splits blocker 2 into a centre-gas obligation
and an atom obligation.  The gas obligation, in the `x2` normalisation the
identity uses, is

    (T1)   2*sum_{p!=q} [ Dam(2y, tau_pq) - Kpair(tau_pq) ]
             <=  2*k*Shq(y) * (1 - rho)          for some atom reserve rho > 0.

Write `GAS(T,y) := sum_{p!=q} [Dam(2y,tau_pq) - Kpair(tau_pq)]`, so T1 reads
`GAS <= k*Shq(y)*(1-rho)`.

## The one identity this probe adds

`gram_form.budget_gram` computes the true `k`-pair budget
`B = (1/2)[G_T(2y) + G_T(0)] - k A^2`, and `B >= 0` is the ONE part of the
`k >= 2` frame that is already a consequence of a kernel-checked theorem
(`Retention.energy_F_ge` plus `cosh^2 >= 1` plus `c2 >= 0`).  Expanding the
Gram sums into diagonal and off-diagonal parts gives, exactly,

    2*B  =  k*Shq(y)  +  sum_{p!=q} [ Kpair(tau_pq) - D(2y, tau_pq) ]

and since `Dam = max(0, D) = D + [-D]^+`,

    (*)   GAS(T,y)  =  k*Shq(y)  -  2*B(T,y)  +  P(T,y),
          P(T,y) := sum_{p!=q} [ -D(2y, tau_pq) ]^+  >=  0.

`P` is exactly the credit thrown away by the `D <= Dam` step.  Two
consequences, and they are the reason this probe exists:

1. **T1 with the SIGNED damage and `rho = 0` is already implied by a
   kernel-checked theorem.**  Drop `P` (i.e. use `D` in place of `Dam`) and
   T1 becomes `2B >= 0`.  So the whole content of T1 is (a) the strict
   positivity of `rho` and (b) the positive-part loss `P`.
2. **An exact ceiling on the atom reserve.**  Rearranging (*), T1 holds with
   reserve `rho` if and only if `rho * k * Shq(y) <= 2B - P`, hence

       rho  <=  (2B - P) / (k Shq(y))   <=   2B / (k Shq(y)).

   On the critical `2*pi` lattice `B/k -> c2(0) - A^2` EXACTLY (defect #24,
   Poisson summation, `counting_lemma.CRITICAL_LATTICE_LIMIT`), so

       rho  <=  2 (c2(0) - A^2) / Shq(1/2)  =  0.1532...

   whatever the atom argument turns out to be.  That is a closed-form
   ceiling replacing the measured "87.8% of the per-centre budget".

## What is measured

* (A) the reduction (*) as a residual over random configurations;
* (B) the exact ceiling, and the finite-`k` lattice ladder approaching it,
      plus `P` on the critical lattice (where the window drift restores
      credit);
* (C) the gas extremum over PERIODIC OCCUPANCY patterns: for every period
      `p <= P_MAX` and every occupancy subset of `Z_p`, the exact `k -> inf`
      per-centre row, with the base spacing `lam` optimised.  This is the
      search `K2-TWO-SPECIES.md` G4 says is an optimisation obligation;
* (D) free-position local search at finite `k` (no lattice assumed);
* (E) a **linear-programming assessment of the natural proof route** for T1.
      A Cohn-Elkies-style certificate for T1 is a function `G` with
      `G >= f := Dam(2y,.) - Kpair(.)` pointwise and `Ghat <= 0`, since then
      `sum_{p,q} G(tau_pq) = int Ghat |That|^2 <= 0` gives
      `GAS <= -k G(0)`.  Truncating the pointwise constraint to `s <= S_MAX`
      only RELAXES the program, so the truncated optimum is a LOWER bound on
      any such certificate's value: if it already exceeds `Shq(1/2)`, no
      certificate of this form can prove T1 at all.
* (F) controls: a planted-fault ladder on (C), a weak-duality check tying
      (E) to (C)/(D), and the identity residual of (A) as the null.

Run: `.venv/bin/python hunts/r_b9552d/probe.py [--quick]`
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

_FM = Path(__file__).resolve().parents[1] / "frontier_math"
sys.path.insert(0, str(_FM))

import gram_form as gf  # noqa: E402

SQ2 = math.sqrt(2.0)
A2 = gf.A_CONST ** 2
#: `c2(0) = 1/2 + sin(sqrt2)/(2 sqrt2)` (`mean_damage.c2_zero`).
C2_ZERO = 0.5 + math.sin(SQ2) / (2 * SQ2)
#: `lim_k B/k` on the critical `2*pi` lattice (defect #24, exact).
CRIT = C2_ZERO - A2
#: the Lean-proved floor `2 Shq y >= 0.51944 y^2`, at `y = 1/2`.
LEAN_FLOOR = 0.12986

TWO_PI = 2.0 * math.pi


def dam(y: float, s: float) -> float:
    return max(0.0, gf.damage(y, s))


def kpair(u: float) -> float:
    return gf.phi_r(u) ** 2


def f_gas(s: float, twoy: float = 1.0) -> float:
    """`f(s) = Dam(2y, s) - Kpair(s)`, the per-pair gas charge."""
    return dam(twoy, s) - kpair(s)


def _ghat_vec(a: float, b: np.ndarray) -> np.ndarray:
    z = a + 1j * b
    zp, zm = z + 1j * SQ2, z - 1j * SQ2
    return np.sinh(zp / 2) / zp + np.sinh(zm / 2) / zm


def f_gas_vec(s: np.ndarray, twoy: float = 1.0,
              damage_scale: float = 1.0) -> np.ndarray:
    """Vectorized `damage_scale * Dam(2y, s) - Kpair(s)`.

    Agrees with the scalar `gram_form` path to double-precision rounding
    (checked by :func:`vector_path_residual`, control F).
    """
    s = np.asarray(s, dtype=float)
    g = _ghat_vec(twoy, s)
    d = -(g * g).real
    g0 = _ghat_vec(0.0, s)
    return damage_scale * np.maximum(0.0, d) - g0.real ** 2


def vector_path_residual(n: int = 4000, twoy: float = 1.0) -> float:
    """Control: the numpy kernel against `gram_form`'s scalar `cmath` one."""
    s = np.linspace(1e-3, 400.0, n)
    fast = f_gas_vec(s, twoy)
    slow = np.array([f_gas(float(x), twoy) for x in s])
    return float(np.max(np.abs(fast - slow)))


# -- (A) the reduction ------------------------------------------------------

def reduction_residual(trials: int = 300, seed: int = 20260818) -> dict:
    """Worst `|GAS - (k Shq - 2B + P)|` over random centre sets and depths."""
    import random
    rng = random.Random(seed)
    worst, worst_rel = 0.0, 0.0
    for _ in range(trials):
        k = rng.randint(1, 7)
        T = [rng.uniform(-45, 45) for _ in range(k)]
        y = rng.uniform(0.01, 0.5)
        pairs = [(a, b) for i, a in enumerate(T) for j, b in enumerate(T) if i != j]
        gas = sum(dam(2 * y, a - b) - kpair(a - b) for a, b in pairs)
        pp = sum(max(0.0, -gf.damage(2 * y, a - b)) for a, b in pairs)
        rhs = k * gf.shq(y) - 2 * gf.budget_gram(T, y) + pp
        d = abs(gas - rhs)
        worst = max(worst, d)
        worst_rel = max(worst_rel, d / max(1e-12, abs(gas) + abs(rhs)))
    return {"trials": trials, "worst_abs": worst, "worst_rel": worst_rel}


# -- (B) the exact ceiling and the lattice ladder ---------------------------

def lattice_ladder(ks=(64, 256, 1024, 4096, 16384)) -> list:
    """`B/k` on the `2*pi` lattice, against the exact limit."""
    rows = []
    for k in ks:
        T = np.arange(k) * TWO_PI
        # B = (k/2) Shq + (1/2) sum_{p!=q} [Kpair - D(2y,tau)] ; use the
        # translation-invariant form to keep it O(k) rather than O(k^2).
        d = np.arange(1, k)
        mult = (k - d)  # number of ordered pairs at separation d, one sign
        s = d * TWO_PI
        vals = np.array([kpair(x) - gf.damage(1.0, x) for x in s])
        off = 2.0 * float(np.dot(mult, vals))
        B = 0.5 * k * gf.shq(0.5) + 0.5 * off
        rows.append({"k": k, "B_over_k": B / k})
    return rows


def critical_lattice_credit(dmax: int = 4000) -> dict:
    """`P` per centre on the `2*pi` lattice: where the window drift pays.

    `P/k = 2 sum_{d>=1} [-D(1, 2 pi d)]^+`.  Zero while every lattice point
    sits inside a depth-1 damage window; positive once the window ladder
    (spacing ~6.23) has drifted a full width away from `2 pi`.
    """
    first_positive, tot = None, 0.0
    for d in range(1, dmax + 1):
        v = -gf.damage(1.0, TWO_PI * d)
        if v > 0:
            if first_positive is None:
                first_positive = d
            tot += v
    return {"P_per_centre": 2.0 * tot, "first_credit_multiple": first_positive,
            "dmax": dmax}


def exact_ceiling() -> dict:
    """The closed-form ceiling on the atom reserve `rho`.

    `rho <= (2B - P)/(k Shq)`, and on the critical `2*pi` lattice `P = 0`
    (measured, :func:`critical_lattice_credit`) and `B/k -> c2(0) - A^2`
    exactly, so `rho <= 2(c2(0) - A^2)/Shq(1/2)`.

    A proof may only use the Lean-proved floor `2 Shq y >= 0.51944 y^2`
    rather than the true `Shq`.  Replacing `Shq` by `F/2 = 0.06493` in the
    RIGHT side of T1 only (the left side is the honest `GAS`) tightens the
    ceiling to `[(2B - P)/k - (Shq - F/2)] / (F/2)`.
    """
    shq = gf.shq(0.5)
    half_floor = LEAN_FLOOR / 2
    return {
        "c2_zero": C2_ZERO, "A_squared": A2,
        "critical_lattice_limit_B_over_k": CRIT,
        "Shq_half": shq, "two_Shq_half": 2 * shq,
        "lean_proved_floor_2Shq": LEAN_FLOOR,
        "rho_ceiling_true_Shq": 2 * CRIT / shq,
        "rho_ceiling_with_lean_floor": (2 * CRIT - (shq - half_floor)) / half_floor,
    }


# -- (C) the periodic occupancy search --------------------------------------

def _F_vector(p: int, lam: float, twoy: float, dmax: int,
              damage_scale: float = 1.0) -> np.ndarray:
    """`F[r] = sum_{n in Z} f((r + n p) lam)`, truncated to `|.| <= dmax`.

    `damage_scale != 1` inflates only the damage half of `f` (the planted
    fault of control F).
    """
    F = np.zeros(p)
    for r in range(p):
        n = np.arange(-(dmax // p) - 1, dmax // p + 2)
        d = r + n * p
        d = d[np.abs(d) <= dmax]
        F[r] = float(np.sum(f_gas_vec(np.abs(d) * lam, twoy, damage_scale)))
    return F


def _all_subsets(p: int) -> np.ndarray:
    """Indicator matrix of every subset of `Z_p` containing 0 (2^(p-1) rows)."""
    m = 1 << (p - 1)
    idx = np.arange(m, dtype=np.int64)
    bits = ((idx[:, None] >> np.arange(p - 1)[None, :]) & 1).astype(np.float64)
    return np.hstack([np.ones((m, 1)), bits])


def periodic_rows(p: int, lam: float, twoy: float = 1.0,
                  dmax: int = 3000, damage_scale: float = 1.0):
    """Per-centre `GAS/k` in the `k -> inf` limit, for every occupancy of `Z_p`.

    For a periodic set (occupied residues `S`, base spacing `lam`, period
    `p*lam`) the per-centre row is exactly

        (1/|S|) * sum_r  m_S(r) * F(r)   +   A^2,

    with `m_S` the cyclic autocorrelation of the indicator, `F` as above,
    and `+A^2` removing the `|S|` self-pairs (`f(0) = -Kpair(0) = -A^2`).
    """
    ind = _all_subsets(p)
    F = _F_vector(p, lam, twoy, dmax, damage_scale)
    corr = np.zeros((ind.shape[0], p))
    for r in range(p):
        corr[:, r] = np.sum(ind * np.roll(ind, r, axis=1), axis=1)
    size = ind[:, 0] * 0 + np.sum(ind, axis=1)
    rows = (corr @ F) / size + A2
    return rows, ind


def periodic_search(p_max: int = 14, lam_grid=None, twoy: float = 1.0,
                    dmax: int = 3000, damage_scale: float = 1.0) -> dict:
    """Best per-centre gas row over periods `<= p_max` and base spacings."""
    if lam_grid is None:
        lam_grid = np.concatenate([np.arange(5.30, 6.60, 0.01),
                                   np.arange(6.60, 13.0, 0.05)])
    best = {"row": -1e9}
    per_period = []
    for p in range(1, p_max + 1):
        bp = {"row": -1e9, "p": p}
        for lam in lam_grid:
            rows, ind = periodic_rows(p, float(lam), twoy, dmax, damage_scale)
            i = int(np.argmax(rows))
            if rows[i] > bp["row"]:
                bp = {"row": float(rows[i]), "p": p, "lam": float(lam),
                      "pattern": [int(v) for v in ind[i]]}
        bp["gaps"] = _gaps_of(bp["pattern"])
        per_period.append(bp)
        if bp["row"] > best["row"]:
            best = dict(bp)
    # golden-section refinement of lam at the winning pattern
    pat = np.array(best["pattern"], dtype=float)[None, :]
    p = best["p"]

    def row_at(lam: float) -> float:
        F = _F_vector(p, lam, twoy, dmax, damage_scale)
        corr = np.array([np.sum(pat * np.roll(pat, r, axis=1)) for r in range(p)])
        return float(corr @ F) / float(pat.sum()) + A2

    a, b = best["lam"] - 0.02, best["lam"] + 0.02
    gr = (math.sqrt(5) - 1) / 2
    c, d = b - gr * (b - a), a + gr * (b - a)
    for _ in range(45):
        if row_at(c) < row_at(d):
            a, c = c, d
            d = a + gr * (b - a)
        else:
            b, d = d, c
            c = b - gr * (b - a)
    best["lam"] = (a + b) / 2
    best["row"] = row_at(best["lam"])
    best["gaps"] = _gaps_of(best["pattern"])
    best["per_period"] = per_period
    return best


def _gaps_of(pattern) -> list:
    occ = [i for i, v in enumerate(pattern) if v]
    p = len(pattern)
    return [occ[(i + 1) % len(occ)] - occ[i] + (p if i == len(occ) - 1 else 0)
            for i in range(len(occ))]


# -- (D) free-position local search at finite k ------------------------------

def _periodic_row_free(t: np.ndarray, L: float, twoy: float = 1.0,
                       s_max: float = 3000.0) -> float:
    """Per-centre `GAS/k` for the infinite periodic set `{t_i + nL}`.

    No lattice is assumed: the `m` positions inside the period and the
    period itself are free.  This strictly contains the occupancy search.
    """
    m = len(t)
    if L <= 1e-6:
        return -1e9
    n = np.arange(-int(s_max / L) - 1, int(s_max / L) + 2)
    tot = 0.0
    for i in range(m):
        d = (t[i] - t[:, None] + n[None, :] * L).ravel()
        d = d[np.abs(d) > 1e-12]
        d = d[np.abs(d) <= s_max]
        tot += float(np.sum(f_gas_vec(np.abs(d), twoy)))
    return tot / m


def free_periodic_search(ms=(1, 2, 3, 4, 5, 6, 7, 8), restarts: int = 8,
                         twoy: float = 1.0, s_max: float = 3000.0,
                         seed: int = 3) -> dict:
    """Maximise the `k -> inf` per-centre row over FREE periodic configurations.

    Seeded from the occupancy winners (integer gap patterns at step `2*pi`)
    and from random cells, then refined with Powell on `(t_1..t_{m-1}, L)`.
    """
    from scipy.optimize import minimize
    rng = np.random.default_rng(seed)
    best = {"row": -1e9}
    per_m = []
    for m in ms:
        bm = {"row": -1e9, "m": m}
        seeds = []
        seeds.append((np.arange(m) * TWO_PI, m * TWO_PI))
        if m >= 3:
            g = ([1, 1, 2, 1, 1, 2, 3] * 3)[:m]
            cum = np.concatenate([[0], np.cumsum(g)])[:m]
            seeds.append((cum * TWO_PI, float(np.sum(g)) * TWO_PI))
        for _ in range(restarts):
            gaps = rng.uniform(5.0, 9.0, m)
            seeds.append((np.concatenate([[0.0], np.cumsum(gaps[:-1])]),
                          float(np.sum(gaps))))
        for t0, L0 in seeds:
            x0 = np.concatenate([np.asarray(t0, dtype=float)[1:], [L0]])

            def neg(x):
                L = x[-1]
                t = np.concatenate([[0.0], x[:-1]])
                if L <= 2.0 or np.any(np.abs(t) > 5 * L + 50):
                    return 1e9
                return -_periodic_row_free(t, L, twoy, s_max)

            r = minimize(neg, x0, method="Powell",
                         options={"maxiter": 4000, "xtol": 1e-7, "ftol": 1e-11})
            if -r.fun > bm["row"]:
                L = float(r.x[-1])
                t = np.sort(np.concatenate([[0.0], r.x[:-1]]) % L)
                bm = {"row": float(-r.fun), "m": m, "L": L,
                      "positions": [round(float(v), 5) for v in t],
                      "gaps": [round(float(v), 5) for v in
                               np.diff(np.concatenate([t, [t[0] + L]]))]}
        per_m.append(bm)
        if bm["row"] > best["row"]:
            best = dict(bm)
    best["per_m"] = per_m
    return best


def free_search(ks=(6, 10, 16, 24), restarts: int = 12, twoy: float = 1.0,
                seed: int = 11) -> list:
    """Maximise the finite-`k` per-centre row `GAS/k` with free positions."""
    from scipy.optimize import minimize
    rng = np.random.default_rng(seed)
    out = []
    for k in ks:
        best = {"row": -1e9}
        for r in range(restarts):
            if r == 0:
                t0 = np.arange(k) * TWO_PI
            elif r == 1:
                base = [0, 1, 2, 4, 5, 6, 8, 9, 11, 12, 13, 15]
                t0 = np.array([base[i % len(base)] + 16 * (i // len(base))
                               for i in range(k)], dtype=float) * TWO_PI
            else:
                t0 = np.sort(np.cumsum(rng.uniform(3.0, 9.0, k)))

            def neg(t):
                tot = 0.0
                for i in range(k):
                    for j in range(k):
                        if i != j:
                            tot += f_gas(abs(t[i] - t[j]), twoy)
                return -tot / k

            res = minimize(neg, t0, method="Powell",
                           options={"maxiter": 6000, "xtol": 1e-6, "ftol": 1e-9})
            if -res.fun > best["row"]:
                t = np.sort(res.x)
                best = {"row": float(-res.fun),
                        "gaps": [round(float(v), 4) for v in np.diff(t)]}
        best["k"] = k
        out.append(best)
    return out


# -- (E) the LP assessment of the certificate route -------------------------

def lp_horizon_ladder(horizons=((60.0, 1500), (120.0, 2000), (200.0, 3000),
                                (400.0, 5000), (600.0, 7000)),
                      n_w: int = 200) -> list:
    """The LP value as the truncation horizon grows.

    The value must increase toward the untruncated optimum.  Until it
    exceeds the best achievable row it carries no upper-bound content; a
    solver failure is reported as such rather than read as a bound.
    """
    out = []
    for s_max, n_s in horizons:
        r = lp_route(s_max=s_max, n_s=n_s, n_w=n_w)
        out.append({"s_max": s_max, "n_s": n_s, "status": r["status"],
                    "value": r.get("lp_value_lower_bound"),
                    "ratio_vs_Shq": r.get("ratio_value_over_budget")})
    return out


def lp_route(s_max: float = 200.0, n_s: int = 3000, w_max: float = 2.4,
             n_w: int = 200, twoy: float = 1.0) -> dict:
    """Truncated Cohn-Elkies-style LP for T1, and what its value forbids.

    Certificate sought: `G(s) = - int_0^{w_max} mu(w) cos(sw) dw` with
    `mu >= 0` piecewise constant, so `Ghat <= 0` by construction and
    `sum_{p,q} G(tau_pq) = - int mu |That|^2 <= 0`, whence
    `GAS <= -k G(0) = k * int mu`.  Minimise `int mu` subject to
    `G(s) >= f(s)` on a grid of `(0, s_max]`.

    Truncating the constraint set can only DECREASE the optimum, so the
    value returned is a LOWER bound on the value of the untruncated program.
    """
    from scipy.optimize import linprog
    edges = np.linspace(0.0, w_max, n_w + 1)
    dw = np.diff(edges)
    s = np.linspace(s_max / n_s, s_max, n_s)
    # psi[i, j] = int_{cell j} cos(s_i w) dw = (sin(s_i w_{j+1}) - sin(s_i w_j))/s_i
    psi = (np.sin(np.outer(s, edges[1:])) - np.sin(np.outer(s, edges[:-1]))) / s[:, None]
    fv = np.array([f_gas(float(x), twoy) for x in s])
    # constraint  -psi @ mu >= f   <=>   psi @ mu <= -f
    res = linprog(c=dw, A_ub=psi, b_ub=-fv, bounds=(0, None), method="highs")
    shq = gf.shq(0.5)
    out = {"status": res.status, "message": str(res.message),
           "s_max": s_max, "n_s": n_s, "w_max": w_max, "n_w": n_w,
           "Shq_half": shq}
    if res.status == 0:
        val = float(np.dot(dw, res.x))
        out.update({"lp_value_lower_bound": val,
                    "budget_Shq_half": shq,
                    "ratio_value_over_budget": val / shq,
                    "route_dead_if_ratio_ge_1": val >= shq})
    return out


# -- (F) controls ------------------------------------------------------------

def planted_ladder(scales=(1.0, 1.05, 1.10, 1.15, 1.20, 1.30, 1.5),
                   p_max: int = 8, dmax: int = 1500) -> list:
    """Inflate the damage half of `f` and record when the search reports a
    violation of T1 (`row >= Shq(1/2)`).  A search that never fires has no
    demonstrated power (EFFORT_FLOOR)."""
    shq = gf.shq(0.5)
    lam_grid = np.arange(5.6, 7.4, 0.02)
    out = []
    for c in scales:
        b = periodic_search(p_max=p_max, lam_grid=lam_grid, dmax=dmax,
                            damage_scale=c)
        out.append({"damage_scale": c, "best_row": b["row"],
                    "ratio_vs_Shq": b["row"] / shq,
                    "violates_T1": b["row"] >= shq,
                    "p": b["p"], "lam": b["lam"], "gaps": b["gaps"]})
    return out


def recorded_pattern_recheck(s_max: float = 6000.0) -> dict:
    """The `1,1,2,1,1,2,3` pattern of `two_species.NAMED_GAPS` G4, three ways.

    G4 records that this irregular occupancy at step `2*pi` "reaches 0.1200
    against 0.1140", i.e. that it BEATS the uniform lattice, the one
    recorded reason to believe the gas extremum is not the lattice.  The
    pattern's reading is not stated, so all three natural ones are evaluated
    here, in the `x2` normalisation `two_species.centre_gas_row` prints.
    """
    g = [1, 1, 2, 1, 1, 2, 3]
    cum = np.concatenate([[0], np.cumsum(g)])[:7] * TWO_PI
    L = float(np.sum(g)) * TWO_PI
    n = np.arange(-int(s_max / L) - 2, int(s_max / L) + 3)
    rows = []
    for i in range(7):
        d = (cum[i] - cum[:, None] + n[None, :] * L).ravel()
        d = d[(np.abs(d) > 1e-12) & (np.abs(d) <= s_max)]
        rows.append(float(np.sum(f_gas_vec(np.abs(d)))))
    # reading 3: the entries are site MULTIPLICITIES on the 2*pi lattice
    M = np.array(g, dtype=float)
    Lm = 7 * TWO_PI
    nm = np.arange(-int(s_max / Lm) - 2, int(s_max / Lm) + 3)
    tot = 0.0
    for i in range(7):
        for j in range(7):
            d = (i - j) * TWO_PI + nm * Lm
            dd = d[(np.abs(d) > 1e-12) & (np.abs(d) <= s_max)]
            tot += M[i] * M[j] * float(np.sum(f_gas_vec(np.abs(dd))))
        tot += M[i] * (M[i] - 1) * (-A2)
    uni = _periodic_row_free(np.array([0.0]), TWO_PI, 1.0, s_max)
    return {
        "recorded_claim_x2": 0.1200, "recorded_uniform_x2": 0.1140,
        "as_gaps_mean_x2": 2 * float(np.mean(rows)),
        "as_gaps_max_over_centres_x2": 2 * float(np.max(rows)),
        "as_multiplicities_mean_x2": float(2 * tot / float(M.sum())),
        "uniform_2pi_x2": 2 * uni,
        "reproduces_under_any_reading": bool(
            max(2 * np.mean(rows), 2 * np.max(rows), 2 * tot / M.sum())
            > 2 * uni),
    }


def main(quick: bool = False) -> dict:
    t0 = time.time()
    res = {"quick": quick}
    print("== (A) the reduction GAS = k*Shq - 2B + P ==")
    res["reduction"] = reduction_residual(60 if quick else 300)
    print("   worst abs residual: %.3e" % res["reduction"]["worst_abs"])

    print("== (B) the exact reserve ceiling ==")
    res["ceiling"] = exact_ceiling()
    for k, v in res["ceiling"].items():
        print(f"   {k:34s} {v!r}")
    res["lattice_ladder"] = lattice_ladder((64, 256, 1024) if quick
                                           else (64, 256, 1024, 4096, 16384))
    for r in res["lattice_ladder"]:
        print("   B/k at k=%6d : %.12f" % (r["k"], r["B_over_k"]))
    res["critical_credit"] = critical_lattice_credit(600 if quick else 4000)
    print("   P per centre on the 2pi lattice: %.6e (first credit at d=%s)"
          % (res["critical_credit"]["P_per_centre"],
             res["critical_credit"]["first_credit_multiple"]))

    print("== (C) the periodic occupancy extremum ==")
    res["periodic"] = periodic_search(p_max=8 if quick else 14,
                                      dmax=800 if quick else 3000)
    shq = gf.shq(0.5)
    res["periodic"]["Shq_half"] = shq
    res["periodic"]["ratio_vs_Shq"] = res["periodic"]["row"] / shq
    res["periodic"]["ratio_vs_lean_floor"] = 2 * res["periodic"]["row"] / LEAN_FLOOR
    res["periodic"]["rho_implied"] = 1.0 - res["periodic"]["row"] / shq
    print("   best row %.7f  p=%d lam=%.6f gaps=%s  ratio %.4f  rho %.4f"
          % (res["periodic"]["row"], res["periodic"]["p"],
             res["periodic"]["lam"], res["periodic"]["gaps"],
             res["periodic"]["ratio_vs_Shq"], res["periodic"]["rho_implied"]))

    print("== (C2) the recorded irregular-occupancy pattern, rechecked ==")
    res["recorded_pattern"] = recorded_pattern_recheck(
        800.0 if quick else 6000.0)
    for k, v in res["recorded_pattern"].items():
        print(f"   {k:34s} {v!r}")

    print("== (D) free-position search ==")
    res["free_periodic"] = free_periodic_search(
        ms=(1, 2, 3, 4) if quick else (1, 2, 3, 4, 5, 6, 7, 8),
        restarts=3 if quick else 8, s_max=800.0 if quick else 3000.0)
    fp = res["free_periodic"]
    fp["ratio_vs_Shq"] = fp["row"] / shq
    fp["rho_implied"] = 1.0 - fp["row"] / shq
    for r in fp["per_m"]:
        print("   m=%d  row %.7f  ratio %.4f  gaps=%s"
              % (r["m"], r["row"], r["row"] / shq, r.get("gaps")))
    res["free_finite_k"] = free_search((6, 10) if quick else (6, 10, 16, 24),
                                       restarts=4 if quick else 12)
    for r in res["free_finite_k"]:
        print("   k=%3d  row %.7f  ratio %.4f" % (r["k"], r["row"], r["row"] / shq))

    print("== (E) the LP certificate route ==")
    res["lp"] = lp_route(s_max=120.0, n_s=2000) if quick else lp_route()
    print("   ", {k: v for k, v in res["lp"].items()
                  if k in ("status", "lp_value_lower_bound",
                           "ratio_value_over_budget", "route_dead_if_ratio_ge_1")})
    if not quick:
        res["lp_horizon"] = lp_horizon_ladder()
        for r in res["lp_horizon"]:
            print("   s_max %6.0f  status %d  value %s" %
                  (r["s_max"], r["status"], r["value"]))

    print("== (F) controls ==")
    res["vector_path_residual"] = vector_path_residual()
    print("   numpy-vs-cmath kernel residual: %.3e" % res["vector_path_residual"])
    res["planted"] = planted_ladder(
        scales=(1.0, 1.2, 1.5) if quick else (1.0, 1.05, 1.10, 1.15, 1.20, 1.30, 1.5),
        p_max=6 if quick else 8, dmax=600 if quick else 1500)
    for r in res["planted"]:
        print("   scale %.2f -> row %.6f ratio %.4f  violates=%s"
              % (r["damage_scale"], r["best_row"], r["ratio_vs_Shq"],
                 r["violates_T1"]))
    # Truncation adequacy, not weak duality: the UNtruncated LP value must
    # exceed every achievable row.  If the truncated value sits below the
    # best measured row, the truncation is provably biting and the LP number
    # is only a lower bound with no upper-bound content.
    res["lp_truncation_adequate"] = (
        res["lp"].get("lp_value_lower_bound", -1) >= res["periodic"]["row"] - 1e-9)
    print("   LP truncation adequate (value >= best measured row):",
          res["lp_truncation_adequate"])
    res["elapsed_s"] = time.time() - t0
    print("elapsed %.1f s" % res["elapsed_s"])
    return res


if __name__ == "__main__":
    quick = "--quick" in sys.argv
    out = main(quick)
    dest = Path(__file__).resolve().parent / "results.json"
    dest.write_text(json.dumps(out, indent=2, sort_keys=True,
                               default=float) + "\n")
    print("wrote", dest)
