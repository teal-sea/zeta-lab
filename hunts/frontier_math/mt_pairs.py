"""The pair layer rebuilt at the Montgomery-Taylor window (LAW L and budgets).

This is `pair_energy.py` / `pair_density.py`'s layer re-run at the window
`mt_chain.py` works in: phi(t) = cos(sqrt2 t) on the width-1 box.  Nothing
here is evidence about RH, and nothing here moves a proportion; it is a
measured comparison of one algebraic layer across two windows.

WHAT IS MEASURED (all numbers reproduced by ``audit()``)

1. **LAW L holds at MT.**  For pairs at z_r = t_r + i y_r,

       T(dt, y1, y2) = W(dt, y1 - y2) + W(dt, y1 + y2),

   the same identity as at the hunt window, for the same reason (LAW D's
   complex Poisson identity, which `mt_chain` measures to be exact here).
   Against the *independent* route -- build the real grid vectors
   u_r(tau) = phihat_mt(z_r - tau) over an integer tau grid, form the pair
   blocks M_r = 2(x_r x_r^T - y_r y_r^T) and take the Frobenius cross
   tr(M_r M_s) -- the measured defect is pure grid truncation: it scales
   like 1/K (0.01757 -> 0.00111 over K = 200 -> 3200, ratio 15.9 against a
   16x range; worst relative defect 1.8e-3 at K = 3200, dominated by the
   sample at dt = 6.9 where T itself is near zero).  No alias term
   appears, exactly as LAW D's own truncation control says.  The
   planted-wrong routes (``law_l_lesion``) sit at 2.7e-2 (sqrt2 modulation
   mis-set to 1.4), 7.6e-2 (sum layer used twice) and 2.04 (difference
   layer dropped) -- 1.5 to 3 orders of magnitude above the truncation
   defect, so the check has power.

2. **The difference layer is nonnegative here too, and for a stronger
   reason.**  W(g, 0) = 2 Phi2(g)^2 / a^2 with Phi2 real on the real axis,
   so W(., 0) >= 0 identically -- an algebraic sign, not a measured one.
   Its minimum over dt in (0, 60] is 0 to working precision, attained at
   the real zeros of Phi2 (g = 7.042, 12.950, 19.106, ... grid units).
   So T(dt, y, y) = W(dt, 0) + W(dt, 2y) can only be dragged negative by
   the 2y layer, whose depth of negativity is sigma^2-scaled and tiny at
   this window (min W(., 0.98) = -0.036).

3. **The stacking floor is enormous at MT in mean-gap units.**  One-sided
   (grid + Lipschitz margin) over all depth pairs on the probe grid, T
   stays positive out to

       delta_p = 6.15 grid units = 0.979 mean gaps

   (ladder: step 0.01 -> 5.93, 0.005 -> 6.05, 0.0025 -> 6.11, 0.001 ->
   6.15 grid units; the limit is the depth-(0.49, 0.49) sign change just
   below Phi2's first real zero at 7.042).  The floor VALUE at the hunt
   window's own delta_p, transported by the census, is +3.31, and at
   dt = 0 it is 4 + O(sigma^2).  The hunt window's floor lived to
   delta_p = 0.2 of ITS units; with the census below that is 0.255 mean
   gaps, so **the MT stacking floor is ~3.8x wider in mean gaps**.

   CENSUS USED (stated because the comparison depends on it): one zero per
   critical Gabor cell, mean gap = 2 pi / (window support width).  MT: the
   box has width 1, mean gap = 2 pi grid units (`mt_chain.MEAN_GAP`).
   Hunt: L = 8, mean gap = 2 pi / 8 = 0.7854 of its units.  The
   corroboration is that the damage band lands near one mean gap in both:
   6.78-7.04 grid units = 1.08-1.12 mean gaps at MT, g* ~ 0.7 = 0.89 mean
   gaps at the hunt window.  A different census would rescale every
   "mean gaps" figure here and none of the grid-unit ones.

4. **Dipole negativity is comfortably covered.**  Over depth pairs on the
   0.02-0.49 grid the worst min-over-dt T is -0.0322 at y = (0.49, 0.49),
   at dt = 6.78 = 1.079 mean gaps, against a two-pair slack of 0.2847:
   cover factor 8.84.  The cover factor is remarkably flat across the
   depth grid (8.84 to 9.91, shallowest pairs best), because both minT
   and slack are O(sigma^2) here.  The hunt window's worst dipole was
   covered by 2.8-6.7, so MT is ~1.3-3x safer on this axis.

5. **The lattice budget is stacking-dominant almost everywhere, with one
   narrow dangerous window.**  Signed total sum_{r != s} T over
   equal-depth lattices of density nu_p (pairs per mean gap), divided by
   sum slack:

       nu_p       0.50    0.75    1.00    1.25    1.50    2.00    3.00
       y = 0.49  -0.077  +1.07   -0.241  +5.79   +12.6   +26.2   +53.7

   For nu_p >= 1.02 every nearest-neighbour spacing sits INSIDE the
   stacking floor of item 3, so the totals are large and positive: the
   pair layer pays far more than it takes.  On a fine sweep (y = 0.49,
   nu_p from 0.3 to 3.0 in steps of 0.01) only 18 of 271 densities are
   negative at all: the main band nu_p in [0.90, 1.01], worst at
   nu_p = 0.97 with T/slack = -0.381 (spacing 6.48 grid units, on the
   damage band), plus weak echoes at nu_p in [0.48, 0.51] (-0.081) and
   [0.33, 0.34] (-0.029) where the SECOND and THIRD neighbours hit that
   band.  Every row survives (T/slack > -1).  So "dangerous" at MT means
   a ~10%-wide density window near one pair per mean gap, not a broad
   deep-dense regime.

6. **The collective battery is stacking-dominated.**  The six named
   shapes rebuilt in MT units give cross/slack of +275 (stacked column),
   +0.43 / +59.6 (alternating dipoles at nu_p = 1 / 2), +51.9 / +158.7
   (staggered), +57.3 / +162.3 (sandwich), -0.241 / +26.2 (strip-edge
   cluster), +0.750 (periodic pair word at the critical spacing, which at
   this window IS 2 pi = one mean gap).  Every shape survives; the only
   negative row in the battery is the strip-edge cluster at nu_p = 1,
   i.e. item 5's dangerous density seen again.

THE STRUCTURAL DIFFERENCE FROM THE OTHER WINDOW.  At the hunt window the
stacking floor (0.255 mean gaps) is much narrower than the mean gap, so
pair lattices of any density from 0.5 to 3 sit outside it and the
pair-pair interaction can be broadly negative -- which is why level 6b
needed the mutual-exclusion argument (dense clusters blind the on-line
attack) to clear a +0.07 pinch at nu_p ~ 1.25-1.5.  At MT the floor is
0.98 mean gaps: it very nearly fills the mean gap, so density itself
pushes pairs into their own positive stacking region.  The pair layer
here is not the constraint; there is no dense-deep pinch at all, and the
single residual soft spot is the ~10%-wide density band at nu_p ~ 1
where the nearest-neighbour spacing coincides with the damage band.

WHAT THIS IS NOT.  These are measured families (probe depth grids,
equal-depth lattices, six named shapes), not a configuration-free
statement; the configuration-free closure of the pair layer at MT is the
same named gap as at the hunt window -- a counting dual on the T kernel
at mixed depths -- and, per `mt_chain`, at this window the chain DP that
would supply it is itself structurally inadequate (its interval charge
floors straddle the kernel zeros).  The stacking floor is one-sided
(grid minimum minus a Lipschitz margin) and its delta_p is reported with
its step ladder, not as an enclosure.

Run ``.venv/bin/python hunts/frontier_math/mt_pairs.py`` (~1 min).
"""

from __future__ import annotations

import math
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from mt_chain import MEAN_GAP, S2, A, MTChain  # noqa: E402

MT = MTChain()

#: probe depths for the stacking floor (same shape as the other window's)
DEPTH_GRID = (0.01, 0.1, 0.2, 0.3, 0.4, 0.49)
#: depth grid for the dipole scan
DIPOLE_GRID = (0.02, 0.1, 0.2, 0.3, 0.4, 0.45, 0.49)
#: the hunt window's stacking floor width, in ITS units, and its mean gap
HUNT_DELTA_P = 0.2
HUNT_MEAN_GAP = 2 * math.pi / 8.0


# ---------------------------------------------------------------------------
# LAW L at the MT window
# ---------------------------------------------------------------------------


def T(dt, y1: float, y2: float):
    """LAW L: the pair-pair Frobenius cross via the two W layers."""
    dt = np.asarray(dt, float)
    return MT.W(dt, abs(y1 - y2)) + MT.W(dt, y1 + y2)


def _phihat_mt(w):
    """phihat for cos(sqrt2 t) on the width-1 box, vectorized (complex)."""
    w = np.asarray(w, complex)

    def s(u):
        small = np.abs(u) < 1e-12
        us = np.where(small, 1.0, u)
        return np.where(small, 0.5 + 0j, np.sin(us / 2) / us)

    return s(w + S2) + s(w - S2)


def _grid_vectors(dt: float, y1: float, y2: float, K: int):
    """The two normalised grid vectors u_r(tau) = phihat(z_r - tau)."""
    tau = np.arange(-K, K + 1, 1.0)
    norm = math.sqrt(2 * math.pi * A)
    u1 = _phihat_mt(complex(dt, y1) - tau) / norm
    u2 = _phihat_mt(complex(0.0, y2) - tau) / norm
    return u1, u2


def grid_pair_cross(dt: float, y1: float, y2: float, K: int = 3200) -> float:
    """tr(M_r M_s) built from the actual grid vectors -- independent route.

    M = 2(x x^T - y y^T) with x = Re u, y = Im u, so
    tr(M_r M_s) = 4[(x_r.x_s)^2 - (x_r.y_s)^2 - (y_r.x_s)^2 + (y_r.y_s)^2].
    """
    u1, u2 = _grid_vectors(dt, y1, y2, K)
    x1, w1 = u1.real, u1.imag
    x2, w2 = u2.real, u2.imag
    return 4 * ((x1 @ x2) ** 2 - (x1 @ w2) ** 2 - (w1 @ x2) ** 2 + (w1 @ w2) ** 2)


LAW_L_SAMPLES = ((0.7, 0.3, 0.2), (2.1, 0.45, 0.1), (0.0, 0.25, 0.25),
                 (5.5, 0.49, 0.49), (6.9, 0.49, 0.49))


def law_l_check(Ks=(200, 800, 3200), samples=LAW_L_SAMPLES):
    """Defect of LAW L against the grid route, along a truncation ladder."""
    out = []
    for K in Ks:
        worst, rel = 0.0, 0.0
        for dt, y1, y2 in samples:
            lhs = float(T(np.array([dt]), y1, y2)[0])
            rhs = grid_pair_cross(dt, y1, y2, K)
            worst = max(worst, abs(lhs - rhs))
            rel = max(rel, abs(lhs - rhs) / max(abs(lhs), 1e-12))
        out.append((K, worst, rel))
    return out


def law_l_lesion(K: int = 3200, samples=LAW_L_SAMPLES) -> dict:
    """Planted-wrong LAW L variants: the grid route must reject each.

    ``sum layer twice`` is the weakest of the three (the two layers nearly
    coincide at shallow depth), ``difference layer only`` drops half the
    identity, ``modulation 1.4`` mis-sets Taylor's sqrt2 -- the one
    constant `transplant_lemma` identifies as carrying the whole window.
    """
    out = {}
    for name in ("sum layer twice", "difference layer only", "modulation 1.4"):
        worst = 0.0
        for dt, y1, y2 in samples:
            ref = grid_pair_cross(dt, y1, y2, K)
            if name == "sum layer twice":
                wrong = float(2 * MT.W(np.array([dt]), y1 + y2)[0])
            elif name == "difference layer only":
                wrong = float(MT.W(np.array([dt]), abs(y1 - y2))[0])
            else:
                z1 = np.asarray([complex(dt, abs(y1 - y2))])
                z2 = np.asarray([complex(dt, y1 + y2)])
                wrong = float(sum(
                    2 * (v.real**2 - v.imag**2) / A**2
                    for v in (_phihat_bad(z1)[0], _phihat_bad(z2)[0])))
            worst = max(worst, abs(wrong - ref))
        out[name] = worst
    return out


def _phihat_bad(z, mod: float = 1.4):
    """Phi2 with Taylor's sqrt2 mis-set -- the lesion's planted fault."""
    z = np.asarray(z, complex)

    def sc(u):
        small = np.abs(u) < 1e-12
        us = np.where(small, 1.0, u)
        return np.where(small, 1.0, 2 * np.sin(us / 2) / us)

    return 0.5 * sc(z) + 0.25 * (sc(z + 2 * mod) + sc(z - 2 * mod))


# ---------------------------------------------------------------------------
# the difference layer
# ---------------------------------------------------------------------------


def difference_layer(g_max: float = 60.0, step: float = 0.001) -> dict:
    """min W(., 0) over dt in (0, g_max], plus the equal-depth T minima.

    W(g, 0) = 2 Phi2(g)^2 / a^2 is a square of a real quantity on the real
    axis, so nonnegativity is algebraic here; the scan reports where it
    touches zero (the real zeros of Phi2) and how deep the 2y layer digs.
    """
    gs = np.arange(step, g_max + step, step)
    w0 = MT.W(gs, 0.0)
    rows = {}
    for y in (0.02, 0.1, 0.3, 0.45, 0.49):
        t = T(gs, y, y)
        rows[y] = {"min_T": float(t.min()), "at": float(gs[t.argmin()]),
                   "min_W_2y": float(MT.W(gs, 2 * y).min()),
                   "slack": MT.slack(y)}
    return {"min_W0": float(w0.min()), "at": float(gs[w0.argmin()]),
            "equal_depth": rows}


# ---------------------------------------------------------------------------
# the stacking floor
# ---------------------------------------------------------------------------


def stacking_floor(delta_p: float, depth_grid=DEPTH_GRID,
                   step: float = 0.001) -> dict:
    """One-sided min of T over |dt| <= delta_p and all depth pairs.

    Grid minimum minus a Lipschitz margin; |dT/d(dt)| <= lip_W(|y1-y2|) +
    lip_W(y1+y2) with `mt_chain`'s exact-L1 Lipschitz constant.
    """
    dts = np.arange(0.0, delta_p + step, step)
    worst, arg = math.inf, None
    for i, y1 in enumerate(depth_grid):
        for y2 in depth_grid[i:]:
            lip = MT.lip_W(abs(y1 - y2)) + MT.lip_W(y1 + y2)
            local = float(T(dts, y1, y2).min()) - lip * step
            if local < worst:
                worst, arg = local, (y1, y2)
    return {"floor": worst, "at_depths": arg, "delta_p": delta_p,
            "delta_p_mean_gaps": delta_p / MEAN_GAP, "positive": worst > 0}


def largest_delta_p(step: float = 0.001, lo: float = 0.2, hi: float = 6.6,
                    iters: int = 26) -> dict:
    """Bisect for the largest delta_p whose one-sided floor stays positive."""
    for _ in range(iters):
        mid = (lo + hi) / 2
        if stacking_floor(mid, step=step)["floor"] > 0:
            lo = mid
        else:
            hi = mid
    return {"delta_p": lo, "mean_gaps": lo / MEAN_GAP, "step": step,
            "floor": stacking_floor(lo, step=step)["floor"]}


# ---------------------------------------------------------------------------
# dipole negativity and its cover
# ---------------------------------------------------------------------------


def dipole_worst(y1: float, y2: float, dtmax: float = 60.0,
                 step: float = 0.002) -> dict:
    """Worst pair-pair interaction against the two pairs' slacks."""
    dts = np.arange(0.0, dtmax, step)
    t = T(dts, y1, y2)
    m = float(t.min())
    budget = MT.slack(y1) + MT.slack(y2)
    return {"worst_T": m, "at_dt": float(dts[t.argmin()]),
            "at_mean_gaps": float(dts[t.argmin()]) / MEAN_GAP,
            "two_pair_slack": budget, "covered": budget + m >= 0,
            "cover_factor": budget / (-m) if m < 0 else math.inf}


def dipole_table(depth_grid=DIPOLE_GRID):
    """All depth pairs on the grid, sorted worst cover factor first."""
    rows = []
    for i, y1 in enumerate(depth_grid):
        for y2 in depth_grid[i:]:
            rec = dipole_worst(y1, y2)
            rows.append(((y1, y2), rec))
    rows.sort(key=lambda r: r[1]["cover_factor"])
    return rows


# ---------------------------------------------------------------------------
# lattice budgets
# ---------------------------------------------------------------------------


def lattice_budget(nu_p: float, y: float, span_gaps: float = 10.0) -> dict:
    """Signed total sum_{r != s} T over an equal-depth lattice vs sum slack.

    Density nu_p is in pairs per mean gap; spacing = MEAN_GAP / nu_p.
    Both signs of T are kept -- the adversary's own stacking payments
    count against it, which the negative-parts-only eta accounting of the
    other window's level 5-6a deliberately ignored.
    """
    n = max(2, int(round(span_gaps * nu_p)))
    spacing = MEAN_GAP / nu_p
    k = np.arange(1, n)
    total = float((2 * (n - k) * T(k * spacing, y, y)).sum())
    slack_total = n * MT.slack(y)
    return {"nu_p": nu_p, "y": y, "n": n, "spacing": spacing,
            "t_signed": total, "slack_total": slack_total,
            "t_over_slack": total / slack_total,
            "stacking_dominant": total > 0, "survives": slack_total + total > 0}


def lattice_table(nu_values=(0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0),
                  depths=(0.3, 0.45, 0.49)):
    return [lattice_budget(nu, y) for nu in nu_values for y in depths]


def danger_band(y: float = 0.49, lo: float = 0.3, hi: float = 3.0,
                step: float = 0.01):
    """Fine density sweep: where the signed lattice total is negative."""
    rows = [lattice_budget(float(nu), y)
            for nu in np.arange(lo, hi + step / 2, step)]
    neg = [r for r in rows if r["t_over_slack"] < 0]
    worst = min(rows, key=lambda r: r["t_over_slack"])
    return {"worst": worst,
            "negative_nu": (min(r["nu_p"] for r in neg),
                            max(r["nu_p"] for r in neg)) if neg else None,
            "n_negative": len(neg), "n_total": len(rows)}


# ---------------------------------------------------------------------------
# the collective battery, at MT units
# ---------------------------------------------------------------------------


def total_energy(pairs) -> dict:
    """(sum slack, signed cross sum over ordered r != s) for [(t, y), ...]."""
    slack_total = sum(MT.slack(y) for _, y in pairs)
    ts = np.array([t for t, _ in pairs])
    ys = [y for _, y in pairs]
    cross = 0.0
    for i, y1 in enumerate(ys):
        for j, y2 in enumerate(ys):
            if i != j:
                cross += float(T(np.array([ts[i] - ts[j]]), y1, y2)[0])
    return {"slack_total": slack_total, "cross_total": cross,
            "survives": slack_total + cross > 0}


def battery_configs(nu_p: float = 1.0, span_gaps: float = 10.0):
    """The other window's six named shapes, in MT units."""
    spacing = MEAN_GAP / nu_p
    span = span_gaps * MEAN_GAP
    n = max(1, int(span / spacing))
    cfg = {}
    cfg["stacked column"] = [(0.0, y) for y in (0.1, 0.2, 0.3, 0.4, 0.45)]
    cfg["alternating dipoles"] = [(k * spacing, 0.45 if k % 2 else 0.15)
                                  for k in range(2 * n)]
    cfg["staggered lattices"] = (
        [(k * spacing, 0.3) for k in range(n)]
        + [(k * spacing + spacing / 2, 0.4) for k in range(n)])
    cfg["shallow/deep sandwich"] = (
        [(k * spacing, 0.05) for k in range(n)]
        + [(k * spacing, 0.49) for k in range(n)])
    cfg["strip-edge cluster"] = [(k * spacing, 0.49) for k in range(n)]
    # critical spacing: 2 pi / (window support width) = 2 pi here, which at
    # this window IS the mean gap (at the hunt window it was 2 pi / L)
    h = MEAN_GAP
    cfg["periodic pair word"] = [(k * h, 0.3) for k in range(int(span / h))]
    return cfg


def collective_battery(nu_p: float = 1.0):
    rows = {}
    for name, pairs in battery_configs(nu_p).items():
        rec = total_energy(pairs)
        rows[name] = {"pairs": len(pairs),
                      "cross_over_slack": rec["cross_total"] / rec["slack_total"],
                      "survives": rec["survives"]}
    return rows


# ---------------------------------------------------------------------------


def audit():
    print("= LAW L at the MT window vs the independent grid route =")
    for K, dabs, drel in law_l_check():
        print(f"  K={K:5d}: defect {dabs:.3e} abs, {drel:.3e} rel")
    rows = law_l_check()
    print(f"  ratio across 16x truncation range: "
          f"{rows[0][1] / rows[-1][1]:.1f} (~16 = pure 1/K truncation, no alias)")
    for name, d in law_l_lesion().items():
        print(f"  lesion [{name:22s}]: defect {d:.3e} (rejected)")

    print("= the difference layer =")
    d = difference_layer()
    print(f"  min W(dt, 0) over dt in (0, 60]: {d['min_W0']:+.3e} at "
          f"dt={d['at']:.3f} (a real zero of Phi2; W(.,0) = 2 Phi2^2/a^2 "
          ">= 0 algebraically)")
    for y, r in d["equal_depth"].items():
        print(f"  y={y}: min T(dt,y,y) {r['min_T']:+.6f} at {r['at']:.3f}  "
              f"(min W(.,2y) {r['min_W_2y']:+.6f}, slack {r['slack']:.5f})")

    print("= the stacking floor (one-sided, grid + Lipschitz) =")
    for dp in (0.2, HUNT_DELTA_P * MEAN_GAP / HUNT_MEAN_GAP, 3.0, 6.0, 7.0):
        rec = stacking_floor(dp)
        print(f"  delta_p={dp:5.3f} ({rec['delta_p_mean_gaps']:.3f} mean gaps): "
              f"floor {rec['floor']:+8.4f} at depths {rec['at_depths']}  "
              f"positive={rec['positive']}")
    print("  step ladder for the largest positive delta_p:")
    for st in (0.01, 0.005, 0.0025, 0.001):
        rec = largest_delta_p(step=st)
        print(f"    step {st:.4f}: delta_p {rec['delta_p']:.3f} grid units "
              f"= {rec['mean_gaps']:.4f} mean gaps")
    print(f"  the other window: delta_p = {HUNT_DELTA_P} of its units = "
          f"{HUNT_DELTA_P / HUNT_MEAN_GAP:.3f} mean gaps "
          "(census: mean gap = 2 pi / window support width)")

    print("= pair-pair negativity and its cover =")
    rows = dipole_table()
    for (y1, y2), r in rows[:4] + rows[-2:]:
        print(f"  y=({y1:.2f},{y2:.2f}): min T {r['worst_T']:+.6f} at "
              f"dt={r['at_dt']:.3f} ({r['at_mean_gaps']:.3f} mean gaps)  "
              f"two-pair slack {r['two_pair_slack']:.5f}  "
              f"cover x{r['cover_factor']:.2f}")
    print(f"  worst cover factor over the grid: "
          f"x{rows[0][1]['cover_factor']:.2f} "
          "(other window: x2.8-6.7)")

    print("= lattice budgets (signed, both signs of T) =")
    for r in lattice_table():
        tag = "stacking-dominant" if r["stacking_dominant"] else "NEGATIVE"
        print(f"  nu_p={r['nu_p']:.2f} y={r['y']:.2f} n={r['n']:2d} "
              f"spacing {r['spacing']:6.3f}: T/slack {r['t_over_slack']:+9.4f}"
              f"  {tag}  survives={r['survives']}")
    db = danger_band()
    w = db["worst"]
    print(f"  fine sweep at y=0.49: {db['n_negative']}/{db['n_total']} "
          f"densities negative, band nu_p in {db['negative_nu']}")
    print(f"  worst: nu_p={w['nu_p']:.2f} (spacing {w['spacing']:.3f} = "
          f"{w['spacing'] / MEAN_GAP:.3f} mean gaps, on the damage band) "
          f"T/slack {w['t_over_slack']:+.4f}, survives={w['survives']}")

    print("= the collective battery, MT units =")
    for nu_p in (1.0, 2.0):
        print(f"  -- nu_p = {nu_p} --")
        for name, row in collective_battery(nu_p).items():
            print(f"  {name:24s}: pairs {row['pairs']:3d}  cross/slack "
                  f"{row['cross_over_slack']:+10.4f}  "
                  f"survives={row['survives']}")


if __name__ == "__main__":
    audit()
