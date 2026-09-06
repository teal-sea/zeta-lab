"""ARM C: depth generality of the centre-gas extremum (support run 17a0f787).

Answers the bounded question put by run `872d7dce` (hunt `r_c7f779`), which
is loose thread 4 of `hunts/r_b9552d/RESULTS-37fb06a9.md`: re-run search (C)
of `hunts/r_b9552d/probe_37fb06a9.py` at several depths `2y` and ask whether
the ratio `row(y)/Shq(y)` is maximised at `y = 1/2`, whether the maximiser is
still the uniform `2*pi` lattice, and where the optimal base spacing sits.

Nothing here is proved, nothing here is evidence about RH, and the reserved
certification word is not used.

## What is measured

* **(C-fine)** the same periodic-occupancy family as search (C), every
  occupancy subset of `Z_p` containing 0, for `p <= P_MAX`, at base spacing
  `lam`: but on a `lam` grid roughly 40x finer than the recorded run's, and
  extended down to `lam = 3.0`.  The refinement is not cosmetic: at shallow
  depth the row is a **very** sharp function of `lam` (§ RESULTS), and the
  recorded 0.01/0.05 grid steps step straight over the peak.
* **(L)** the pure uniform lattice `{n L}` on a dense `L` grid out to
  `L = 400`, which reaches spacings the occupancy family cannot express and
  is an independent code path for the same numbers.
* **(X)** an independent scalar recomputation of each winning row through
  `gram_form`'s `cmath` path rather than the numpy kernel.
* **(F)** the planted-fault control the brief asks for: the damage half of
  `f` inflated by `damage_scale > 1` until the search reports T1 violated,
  run at every depth, so that a "no violation" verdict at `scale = 1` comes
  from a search with demonstrated power at that depth.

## Method note: why a new evaluator

`probe_37fb06a9.periodic_rows` recomputes the subset-indicator matrix and its
cyclic autocorrelation for every `(p, lam)`.  Neither depends on `lam`, so
hoisting them out of the spacing loop makes a ~40x finer grid cost less than
the recorded coarse one.  The evaluator is otherwise the recorded formula and
:func:`evaluator_agreement` pins it against `periodic_rows` to 1e-14.

Run: `.venv/bin/python hunts/support_17a0f787/probe.py [--quick]`
"""

from __future__ import annotations

import json
import math
import sys
import time
from pathlib import Path

import numpy as np

_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(_ROOT / "hunts" / "r_b9552d"))
sys.path.insert(0, str(_ROOT / "hunts" / "frontier_math"))

import gram_form as gf  # noqa: E402
import probe_37fb06a9 as P  # noqa: E402

TWO_PI = 2.0 * math.pi
A2 = P.A2

#: depths `2y` asked for by the brief.  `2y > 1` is `y > 1/2` and therefore
#: OUTSIDE the range T1 has to hold on; it is measured for the trend only.
DEPTHS = (0.2, 0.5, 1.0, 1.5, 2.0)
EXTRA_DEPTHS = (0.1, 0.3, 0.4, 0.6, 0.7, 0.8, 0.9)

P_MAX = 14
DMAX = 3000


# -- the fast occupancy evaluator -------------------------------------------

def _corr_tables(p_max: int):
    """Cyclic autocorrelations `m_S` of every subset of `Z_p` containing 0.

    `corr[p][i, r] = #{(a, b) in S_i x S_i : a - b = r mod p}`.  Independent
    of the spacing, so it is built once.
    """
    out = {}
    for p in range(1, p_max + 1):
        ind = P._all_subsets(p)
        corr = np.empty((ind.shape[0], p))
        for r in range(p):
            corr[:, r] = np.sum(ind * np.roll(ind, r, axis=1), axis=1)
        out[p] = (ind, corr, np.sum(ind, axis=1))
    return out


def _fold(fv: np.ndarray, p: int) -> np.ndarray:
    """`G[r] = sum_{|d| <= dmax, d = r mod p} f(|d| lam)`, from `fv[d] = f(d lam)`."""
    dmax = len(fv) - 1
    d = np.arange(dmax + 1)
    w = np.where(d == 0, 1.0, 2.0)          # +d and -d, except d = 0
    return np.bincount(d % p, weights=w * fv, minlength=p)


def rows_all_patterns(p: int, lam: float, twoy: float, tables,
                      dmax: int = DMAX, damage_scale: float = 1.0,
                      fv: np.ndarray = None):
    """Per-centre `GAS/k` in the `k -> inf` limit, every occupancy of `Z_p`.

    `fv[d] = f(d lam)` may be passed in when several periods share a spacing.
    """
    if fv is None:
        fv = P.f_gas_vec(np.arange(dmax + 1) * lam, twoy, damage_scale)
    ind, corr, size = tables[p]
    return (corr @ _fold(fv, p)) / size + A2


def row_of_pattern(pattern, lam: float, twoy: float, dmax: int = DMAX,
                   damage_scale: float = 1.0) -> float:
    """The same row for one occupancy pattern (no subset enumeration)."""
    pat = np.asarray(pattern, dtype=float)
    p = len(pat)
    m = np.array([float(np.sum(pat * np.roll(pat, r))) for r in range(p)])
    d = np.arange(dmax + 1)
    fv = P.f_gas_vec(d * lam, twoy, damage_scale)
    return float(m @ _fold(fv, p)) / float(pat.sum()) + A2


def evaluator_agreement(twoy: float = 1.0, dmax: int = 800) -> dict:
    """Control: the fast evaluator against `probe_37fb06a9.periodic_rows`."""
    tables = _corr_tables(6)
    worst = 0.0
    for p in range(1, 7):
        for lam in (5.4, 6.283185307179586, 9.1, 12.7):
            a = rows_all_patterns(p, lam, twoy, tables, dmax)
            b, _ = P.periodic_rows(p, lam, twoy, dmax)
            worst = max(worst, float(np.max(np.abs(a - b))))
    return {"worst_abs_diff_vs_recorded_periodic_rows": worst, "dmax": dmax}


# -- (C-fine) the occupancy search on a resolved spacing grid ----------------

def _golden(fn, a: float, b: float, iters: int = 60) -> tuple:
    gr = (math.sqrt(5) - 1) / 2
    c, d = b - gr * (b - a), a + gr * (b - a)
    fc, fd = fn(c), fn(d)
    for _ in range(iters):
        if fc < fd:
            a, c, fc = c, d, fd
            d = a + gr * (b - a)
            fd = fn(d)
        else:
            b, d, fd = d, c, fc
            c = b - gr * (b - a)
            fc = fn(c)
    x = (a + b) / 2
    return x, fn(x)


def occupancy_search(twoy: float, p_max: int = P_MAX, dmax: int = DMAX,
                     lam_lo: float = 3.0, lam_hi: float = 13.0,
                     step: float = 5e-4, damage_scale: float = 1.0,
                     tables=None) -> dict:
    """Search (C) with the spacing grid resolved.

    Returns the best row over all `(p, occupancy, lam)`, plus the best row
    for each period so the period dependence is visible.
    """
    if tables is None:
        tables = _corr_tables(p_max)
    lams = np.arange(lam_lo, lam_hi + 0.5 * step, step)
    d = np.arange(dmax + 1)
    # spacing is the outer loop so `f(d lam)` is evaluated once per spacing
    # rather than once per (period, spacing).
    coarse = [{"row": -1e18, "p": p} for p in range(1, p_max + 1)]
    for lam in lams:
        fv = P.f_gas_vec(d * float(lam), twoy, damage_scale)
        for p in range(1, p_max + 1):
            r = rows_all_patterns(p, float(lam), twoy, tables, dmax,
                                  damage_scale, fv=fv)
            i = int(np.argmax(r))
            if r[i] > coarse[p - 1]["row"]:
                coarse[p - 1] = {"row": float(r[i]), "p": p,
                                 "lam": float(lam), "i": i}
    best = {"row": -1e18}
    per_period = []
    for p in range(1, p_max + 1):
        ind, corr, size = tables[p]
        bp = dict(coarse[p - 1])
        bp["pattern"] = [int(v) for v in ind[bp.pop("i")]]
        # refine lam for the winning pattern of this period
        pat = bp["pattern"]
        lo, hi = bp["lam"] - step, bp["lam"] + step
        lam_star, row_star = _golden(
            lambda L: row_of_pattern(pat, L, twoy, dmax, damage_scale), lo, hi)
        if row_star > bp["row"]:
            bp["lam"], bp["row"] = float(lam_star), float(row_star)
        bp["gaps"] = P._gaps_of(bp["pattern"])
        bp["spacing_over_2pi"] = [g * bp["lam"] / TWO_PI for g in bp["gaps"]]
        per_period.append(bp)
        if bp["row"] > best["row"]:
            best = dict(bp)
    best["per_period"] = per_period
    best["lam_grid"] = {"lo": lam_lo, "hi": lam_hi, "step": step,
                        "n": int(len(lams))}
    best["p_max"] = p_max
    best["dmax"] = dmax
    return best


# -- (L) the pure lattice, densely --------------------------------------------

def lattice_row(L: float, twoy: float, s_max: float = 20000.0,
                damage_scale: float = 1.0) -> float:
    """Per-centre row of the uniform lattice `{n L}`: `2 sum_{n>=1} f(n L)`."""
    n = np.arange(1, int(s_max / L) + 1)
    return 2.0 * float(np.sum(P.f_gas_vec(n * L, twoy, damage_scale)))


def lattice_scan(twoy: float, lo: float = 4.0, hi: float = 400.0,
                 step: float = 2e-3, s_max: float = 20000.0) -> dict:
    """Dense scan of the uniform-lattice family, plus its top few peaks."""
    Ls = np.arange(lo, hi, step)
    v = np.array([lattice_row(float(L), twoy, s_max) for L in Ls])
    order = np.argsort(v)[::-1]
    peaks, seen = [], []
    for i in order:
        L = float(Ls[i])
        if any(abs(L - q) < 1.0 for q in seen):
            continue
        seen.append(L)
        Ls_, row_ = _golden(lambda x: lattice_row(x, twoy, s_max),
                            L - step, L + step)
        peaks.append({"L": Ls_, "L_over_2pi": Ls_ / TWO_PI, "row": row_})
        if len(peaks) >= 5:
            break
    return {"best": peaks[0], "peaks": peaks,
            "grid": {"lo": lo, "hi": hi, "step": step, "s_max": s_max}}


def peak_sharpness(twoy: float, L: float, half_width: float = 0.05,
                   n: int = 201) -> dict:
    """Width in `L` of the peak at `L`: how fine a `lam` grid it demands."""
    xs = np.linspace(L - half_width, L + half_width, n)
    v = np.array([lattice_row(float(x), twoy) for x in xs])
    top = v.max()
    half = 0.5 * top
    above = xs[v >= half] if top > 0 else np.array([])
    return {"L": L, "peak_row": float(top),
            "fwhm_in_L": float(above.max() - above.min()) if above.size else None,
            "row_at_L_minus_0p01": float(lattice_row(L - 0.01, twoy)),
            "row_at_L_plus_0p01": float(lattice_row(L + 0.01, twoy))}


# -- (X) the independent scalar recheck ---------------------------------------

def scalar_row_recheck(pattern, lam: float, twoy: float,
                       dmax: int = DMAX) -> float:
    """The winner's row through `gram_form`'s scalar `cmath` path.

    Shares no line of arithmetic with `f_gas_vec`: `gram_form.damage` and
    `gram_form.phi_r` build `ghat` with `cmath.sinh` on python complex.
    """
    pat = list(pattern)
    p = len(pat)
    m = [sum(pat[i] * pat[(i - r) % p] for i in range(p)) for r in range(p)]
    tot = m[0] * P.f_gas(0.0, twoy)
    for d in range(1, dmax + 1):
        tot += 2.0 * m[d % p] * P.f_gas(d * lam, twoy)
    return tot / float(sum(pat)) + A2


# -- (F) the planted-fault control --------------------------------------------

def planted_ladder(twoy: float, scales, p_max: int = 8, dmax: int = 1200,
                   step: float = 2e-3, tables=None) -> list:
    """Inflate only the damage half and record when the search says T1 fails.

    A search that never fires has no demonstrated power, so the ladder is run
    at every depth rather than only at `y = 1/2`.
    """
    shq = gf.shq(twoy / 2)
    if tables is None:
        tables = _corr_tables(p_max)
    out = []
    for c in scales:
        b = occupancy_search(twoy, p_max=p_max, dmax=dmax, step=step,
                             damage_scale=c, tables=tables)
        out.append({"damage_scale": float(c), "best_row": b["row"],
                    "ratio_vs_Shq": b["row"] / shq,
                    "violates_T1": bool(b["row"] >= shq),
                    "p": b["p"], "lam": b["lam"], "gaps": b["gaps"]})
    return out


def first_firing_scale(twoy: float, p_max: int = 8, dmax: int = 1200,
                       step: float = 2e-3, lo: float = 1.0, hi: float = 4096.0,
                       tol: float = 0.02, tables=None) -> dict:
    """Bisect the damage inflation at which the search first reports T1 failed."""
    shq = gf.shq(twoy / 2)
    if tables is None:
        tables = _corr_tables(p_max)

    def fires(c):
        b = occupancy_search(twoy, p_max=p_max, dmax=dmax, step=step,
                             damage_scale=c, tables=tables)
        return b["row"] >= shq, b

    ok, b_lo = fires(lo)
    if ok:
        return {"fires_at_scale_1": True, "detail": b_lo}
    ok_hi, b_hi = fires(hi)
    if not ok_hi:
        return {"fires_at_scale_1": False, "never_fired_below": hi}
    a, b = lo, hi
    while b / a > 1.0 + tol:
        mid = math.sqrt(a * b)
        ok, _ = fires(mid)
        if ok:
            b = mid
        else:
            a = mid
    return {"fires_at_scale_1": False, "first_firing_scale_lo": a,
            "first_firing_scale_hi": b}


# -- the run -------------------------------------------------------------------

def main(quick: bool = False) -> dict:
    t0 = time.time()
    res = {"quick": quick,
           "note": "2y > 1 is y > 1/2 and outside the range T1 must hold on"}

    print("== controls: the evaluator against the recorded one ==")
    res["evaluator_agreement"] = evaluator_agreement()
    print("   worst |fast - periodic_rows| = %.3e"
          % res["evaluator_agreement"]["worst_abs_diff_vs_recorded_periodic_rows"])
    res["vector_path_residual"] = P.vector_path_residual(1500)
    print("   numpy-vs-cmath kernel residual = %.3e" % res["vector_path_residual"])

    depths = list(DEPTHS) if quick else sorted(set(DEPTHS) | set(EXTRA_DEPTHS))
    p_max = 10 if quick else P_MAX
    dmax = 1200 if quick else DMAX
    step = 2e-3 if quick else 5e-4
    tables = _corr_tables(p_max)

    print("== (C-fine) the occupancy search, resolved spacing grid ==")
    rows = []
    for twoy in depths:
        t1 = time.time()
        b = occupancy_search(twoy, p_max=p_max, dmax=dmax, step=step,
                             tables=tables)
        shq = gf.shq(twoy / 2)
        rec = P.periodic_search(p_max=min(p_max, 12), twoy=twoy,
                                dmax=min(dmax, 1500))
        L_eff = sorted(set(round(g * b["lam"], 6) for g in b["gaps"]))
        entry = {
            "two_y": twoy, "y": twoy / 2, "in_T1_range": twoy <= 1.0,
            "row": b["row"], "Shq_y": shq, "ratio": b["row"] / shq,
            "rho_implied": 1.0 - b["row"] / shq,
            "p": b["p"], "lam": b["lam"], "pattern": b["pattern"],
            "gaps": b["gaps"],
            "gap_spacings": L_eff,
            "gap_spacings_over_2pi": [g / TWO_PI for g in L_eff],
            "is_uniform_lattice": len(set(b["gaps"])) == 1,
            "recorded_grid_row": rec["row"],
            "recorded_grid_ratio": rec["row"] / shq,
            "recorded_grid_lam": rec["lam"],
            "recorded_grid_gaps": rec["gaps"],
            "seconds": time.time() - t1,
        }
        entry["scalar_recheck_row"] = scalar_row_recheck(
            b["pattern"], b["lam"], twoy, min(dmax, 1500))
        entry["scalar_recheck_abs_diff"] = abs(
            entry["scalar_recheck_row"] - row_of_pattern(
                b["pattern"], b["lam"], twoy, min(dmax, 1500)))
        rows.append(entry)
        print("   2y=%.2f row=%.9f Shq=%.9f ratio=%.5f  p=%d lam=%.6f "
              "gaps=%s  spacing/2pi=%s  [recorded grid: ratio %.5f] (%.0fs)"
              % (twoy, entry["row"], shq, entry["ratio"], entry["p"],
                 entry["lam"], entry["gaps"],
                 ["%.4f" % v for v in entry["gap_spacings_over_2pi"]],
                 entry["recorded_grid_ratio"], entry["seconds"]))
    res["occupancy"] = rows

    print("== (L) the pure lattice, densely ==")
    lat = []
    for twoy in depths:
        s = lattice_scan(twoy, step=5e-3 if quick else 2e-3,
                         hi=200.0 if quick else 400.0)
        shq = gf.shq(twoy / 2)
        s["two_y"] = twoy
        s["ratio"] = s["best"]["row"] / shq
        s["sharpness"] = peak_sharpness(twoy, s["best"]["L"])
        lat.append(s)
        print("   2y=%.2f  best L=%.5f (=%.4f x 2pi)  row=%.9f ratio=%.5f  "
              "peak FWHM in L = %s"
              % (twoy, s["best"]["L"], s["best"]["L_over_2pi"],
                 s["best"]["row"], s["ratio"], s["sharpness"]["fwhm_in_L"]))
    res["lattice"] = lat

    print("== (F) the planted-fault control, at every depth ==")
    ctl = []
    ladder_depths = (0.2, 0.5, 1.0) if quick else DEPTHS
    for twoy in ladder_depths:
        shq = gf.shq(twoy / 2)
        fire = first_firing_scale(twoy, p_max=6 if quick else 8,
                                  dmax=800 if quick else 1200,
                                  step=5e-3 if quick else 2e-3)
        lo = fire.get("first_firing_scale_lo", 1.0)
        scales = sorted({1.0, round(lo * 0.9, 4), round(lo, 4),
                         round(lo * 1.1, 4), round(lo * 1.5, 4)})
        lad = planted_ladder(twoy, scales, p_max=6 if quick else 8,
                             dmax=800 if quick else 1200,
                             step=5e-3 if quick else 2e-3)
        ctl.append({"two_y": twoy, "Shq_y": shq, "firing": fire,
                    "ladder": lad})
        print("   2y=%.2f  first firing damage_scale in [%s, %s]"
              % (twoy, fire.get("first_firing_scale_lo"),
                 fire.get("first_firing_scale_hi")))
        for r in lad:
            print("      scale %8.3f -> row %.6f ratio %.4f violates=%s"
                  % (r["damage_scale"], r["best_row"], r["ratio_vs_Shq"],
                     r["violates_T1"]))
    res["control_planted"] = ctl

    # the two questions the brief asks, answered from the measurement
    in_range = [r for r in res["occupancy"] if r["in_T1_range"]]
    best_in_range = max(in_range, key=lambda r: r["ratio"])
    res["verdict"] = {
        "ratio_maximised_at_y_half_within_T1_range":
            bool(abs(best_in_range["two_y"] - 1.0) < 1e-12),
        "ratio_monotone_increasing_in_depth": bool(all(
            a["ratio"] < b["ratio"] for a, b in
            zip(sorted(res["occupancy"], key=lambda r: r["two_y"]),
                sorted(res["occupancy"], key=lambda r: r["two_y"])[1:]))),
        "maximiser_is_uniform_2pi_lattice_at_every_depth": bool(all(
            r["is_uniform_lattice"] and
            abs(r["gap_spacings_over_2pi"][0] - 1.0) < 1e-3
            for r in res["occupancy"])),
        "optimal_spacing_over_2pi_by_depth": {
            str(r["two_y"]): r["gap_spacings_over_2pi"] for r in res["occupancy"]},
        "max_ratio_in_T1_range": best_in_range["ratio"],
        "at_two_y": best_in_range["two_y"],
        "no_violation_anywhere_measured": bool(
            all(r["ratio"] < 1.0 for r in res["occupancy"])),
    }
    res["elapsed_s"] = time.time() - t0
    print("elapsed %.1f s" % res["elapsed_s"])
    return res


if __name__ == "__main__":
    q = "--quick" in sys.argv
    out = main(q)
    dest = Path(__file__).resolve().parent / (
        "results_quick.json" if q else "results.json")
    dest.write_text(json.dumps(out, indent=2, sort_keys=True, default=float)
                    + "\n")
    print("wrote", dest)
