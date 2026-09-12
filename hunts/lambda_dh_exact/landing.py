"""Hunt #52, phase 2: landing times measured, the shave law fitted, the
extrapolation to the strip edge.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_exact/landing.py pde --pairs 1,2 --out landing_A.json
    .venv/bin/python hunts/lambda_dh_exact/landing.py census --pairs 1,2,3
    .venv/bin/python hunts/lambda_dh_exact/landing.py fit
    .venv/bin/python hunts/lambda_dh_exact/landing.py merge

Everything here is float grade in the sense of the probe discipline: mpmath
floats with measured cross-route defects. The strongest words used are
*measured* and *observed*. No enclosure claims are made anywhere.

What the three stages do.

``pde``  re-measures the landing time t* of an off-line Davenport-Heilbronn
quadruple by the contour-moment route of hunt #4 (hunts/flow_repair/probe.py):
t* is the root of the pair discriminant Delta(t) = 2 q_2 - q_1^2, which is
analytic through the collision. It is run here with deliberately perturbed
instrument settings (different contour radius rule, different node count M,
different working precision, tighter bracket tolerance) so that agreement with
the nine published numbers is an instrument check and not a replay.

``census`` measures the local zero geometry at each site: the real zeros of
Xi_DH in a window, the nearest-neighbour distance d, the local mean gap, and
the neighbour sum S_0 = sum_a 1/(x-a)^2 that the phase-1 theory says controls
the shave.

``fit``  tests the phase-1 law

    t* = int_0^{y0} y dy / (1 + 2 y^2 S(y)),   S(y) = sum_a 1/((x-a)^2 + y^2)

against the measured landings, in three forms with zero, one and one free
parameters, then extrapolates to y0 -> Delta = 0.62036249819.
"""
from __future__ import annotations

import argparse
import glob
import json
import math
import os
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))
_FLOW = os.path.join(_ROOT, "hunts", "flow_repair")
for _p in (_ROOT, _FLOW):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from mpmath import mp  # noqa: E402

import probe  # noqa: E402  (hunts/flow_repair/probe.py: the hunt #4 instrument)

RESULTS = os.path.join(_HERE, "landing.json")

# inherited, decided in hunts/lambda_dh_bounds/STRIP2.md
DELTA = 0.62036249819
UPPER = DELTA ** 2 / 2  # 0.19242481458...

# hunts/flow_repair/NOTES.md section 1: the nine published landings
PUBLISHED = {
    1: (85.6993, 0.3085172, 0.04412634450),
    2: (114.1633, 0.1508270, 0.01112958794),
    3: (166.4793, 0.0743505, 0.00274784849),
    4: (176.7025, 0.2242763, 0.02366473172),
    5: (240.4046, 0.3695261, 0.05765184035),
    6: (320.8765, 0.3195496, 0.04468146893),
    7: (331.0503, 0.2682231, 0.03217819397),
    8: (366.6409, 0.1285081, 0.00803041920),
    9: (411.7967, 0.3158737, 0.04265328332),
}


def mean_gap(gamma: float) -> float:
    """2 pi / log(5 gamma / 2 pi), the conductor-5 mean spacing."""
    return float(2 * math.pi / math.log(5 * float(gamma) / (2 * math.pi)))


# ---------------------------------------------------------------------------
# stage pde
# ---------------------------------------------------------------------------


def perturbed_radius(y0: float) -> float:
    """A different radius rule from hunt #4's min(0.9, max(0.35, 2.6 y0)):
    the contour must enclose both members at +-y0 with margin and stay well
    inside the nearest real neighbour, which sits about one mean gap away."""
    return float(min(0.95, max(0.32, 2.15 * y0)))


def stage_pde(pairs: list[int], out: str, M: int = 120, extra_dps: int = 30) -> None:
    res: dict = {}
    for k in pairs:
        tk = time.time()
        gamma_seed = float(mp.mpf(probe.LIT_PAIRS[k][1]))
        pol = probe.polish_pair(k, dps=probe.site_dps(gamma_seed, 20))
        y0 = float(mp.mpf(pol["y0"]))
        site = probe.make_site(k, pol, extra_dps=extra_dps,
                               radius=perturbed_radius(y0))
        tst = probe.find_tstar(site, tol=1e-9, M=M)
        tst["polished"] = pol
        tst["seconds"] = round(time.time() - tk, 2)
        pub = PUBLISHED[k][2]
        tst["published"] = pub
        tst["rel_diff_vs_published"] = tst["tstar"] / pub - 1.0
        res[f"pair{k}"] = tst
        print(f"pair {k} (gamma~{gamma_seed:.2f}): t* = {tst['tstar']:.11f} "
              f"published {pub:.11f} rel diff {tst['rel_diff_vs_published']:+.2e} "
              f"shave {tst['shave_percent']:.3f}% [{tst['seconds']}s dps={tst['dps']} "
              f"M={M} r={site['radius']:.3f}]", flush=True)
    save_results({f"pde_{'_'.join(map(str, pairs))}": res}, out)


# ---------------------------------------------------------------------------
# stage census: the local zero geometry
# ---------------------------------------------------------------------------


def stage_census(pairs: list[int], out: str, half: float = 25.0,
                 dps: int = 25) -> None:
    res: dict = {}
    for k in pairs:
        tk = time.time()
        gamma, y0, _ = PUBLISHED[k]
        reals = probe.line_zeros_near(gamma, half, step_frac=10.0, dps=dps)
        d = sorted(abs(w - gamma) for w in reals)
        gaps = [b - a for a, b in zip(reals, reals[1:])]
        entry = {
            "gamma": gamma,
            "y0": y0,
            "half_window": half,
            "n_line_zeros": len(reals),
            "line_zeros": reals,
            "d_nearest": d[0] if d else None,
            "d_second": d[1] if len(d) > 1 else None,
            "local_gap_median": sorted(gaps)[len(gaps) // 2] if gaps else None,
            "density_measured": len(reals) / (2.0 * half),
            "mean_gap_formula": mean_gap(gamma),
            "seconds": round(time.time() - tk, 2),
        }
        res[f"pair{k}"] = entry
        print(f"pair {k}: {len(reals)} line zeros in +-{half}, d_nn = "
              f"{entry['d_nearest']:.5f}, measured gap "
              f"{1.0/entry['density_measured']:.5f} vs formula "
              f"{entry['mean_gap_formula']:.5f} [{entry['seconds']}s]", flush=True)
    save_results({f"census_{'_'.join(map(str, pairs))}": res}, out)


# ---------------------------------------------------------------------------
# the neighbour sum and the landing integral
# ---------------------------------------------------------------------------


def neighbour_sum_builder(gamma: float, reals: list[float], others: list[dict],
                          half: float, K: int = 20000):
    """S(y) = sum_a 1/((x-a)^2 + y^2) at x = gamma, over

      * every measured real zero in the window,
      * every other known off-line quadruple in the window (both members,
        summed in complex arithmetic, real part taken),
      * a lattice continuation beyond the window at the formula mean gap,
        both sides, K terms,
      * the mirror cluster near -gamma, as a density integral.

    The lattice tail matters at the 1e-3 level for S_0 and is included rather
    than dropped.
    """
    h = mean_gap(gamma)
    tail = []
    edge_hi = max(reals) if reals else gamma + half
    edge_lo = min(reals) if reals else gamma - half
    for j in range(1, K + 1):
        tail.append(edge_hi + j * h)
        lo = edge_lo - j * h
        if lo > 1.0:
            tail.append(lo)
    finite = [float(a) for a in reals] + tail
    pairs_c = [(complex(p["x"], p["y"]), complex(p["x"], -p["y"])) for p in others]

    def S(y: float) -> float:
        y2 = float(y) ** 2
        s = 0.0
        for a in finite:
            dx = gamma - a
            s += 1.0 / (dx * dx + y2)
        for a1, a2 in pairs_c:
            for a in (a1, a2):
                dz = complex(gamma, 0.0) - a
                s += (1.0 / (dz * dz + y2)).real
        # mirror cluster near -gamma: density 1/h out to the far edge
        s += 2.0 * (1.0 / h) * (1.0 / (2.0 * gamma - 1.0))
        return s

    return S


def landing_integral(y0: float, S, n: int = 4000) -> float:
    """t* = int_0^{y0} y dy / (1 + 2 y^2 S(y)) by composite Simpson."""
    n = n if n % 2 == 0 else n + 1
    hstep = y0 / n
    total = 0.0
    for i in range(n + 1):
        y = i * hstep
        w = 1 if i in (0, n) else (4 if i % 2 else 2)
        total += w * y / (1.0 + 2.0 * y * y * S(y))
    return total * hstep / 3.0


def lattice_S(h: float, dfac: float, K: int = 2000000):
    """S for a local gap of half-width dfac*h with a lattice beyond, the
    calibrated model of phase 1 (theory.py t_star_gap): neighbours sit at
    x +- (dfac + j) h for j = 0, 1, 2, ...  Direct truncated sum, used only
    to check the closed form below."""
    import numpy as np

    a = (dfac + np.arange(K)) * h

    def S(y: float) -> float:
        y2 = float(y) ** 2
        return float(np.sum(2.0 / (a * a + y2)))

    return S


def lattice_S_fast(h: float, dfac: float):
    """Closed form of the same sum, derived here rather than recalled.

    With theta = dfac and u = y/h,

        sum_{j>=0} 1/((j+theta)^2 + u^2) = Im psi(theta + i u) / u,

    from psi(z+1) - psi(z) = 1/z summed telescopically, so

        S(y) = (2/h^2) sum_{j>=0} 1/((j+theta)^2 + u^2) = (2/(h y)) Im psi(theta + i y/h),

    and at y = 0 the limit is (2/h^2) psi'(theta).  Checked against the direct
    truncated sum in stage ``fit`` (key ``lattice_closed_form_check``).
    """
    from scipy.special import digamma, polygamma

    def S(y: float) -> float:
        y = float(y)
        if y <= 0.0:
            return float(2.0 / h ** 2 * polygamma(1, dfac))
        return float(2.0 / (h * y) * complex(digamma(complex(dfac, y / h))).imag)

    return S


# ---------------------------------------------------------------------------
# stage fit
# ---------------------------------------------------------------------------


def _linfit_through_origin(xs, ys):
    sxx = sum(x * x for x in xs)
    sxy = sum(x * y for x, y in zip(xs, ys))
    slope = sxy / sxx
    resid = [y - slope * x for x, y in zip(xs, ys)]
    ss_res = sum(r * r for r in resid)
    ybar = sum(ys) / len(ys)
    ss_tot = sum((y - ybar) ** 2 for y in ys)
    return slope, resid, 1.0 - ss_res / ss_tot


def stage_fit(out: str, fallback_published: bool = False) -> None:
    data = load_results()
    # gather measurements
    meas: dict[int, dict] = {}
    for key, blob in data.items():
        if key.startswith("pde_"):
            for pk, v in blob.items():
                if pk.startswith("pair"):
                    v = dict(v)
                    v["source"] = "measured here (contour moments, perturbed settings)"
                    meas[int(pk[4:])] = v
    if fallback_published:
        for k, (g, y0, t) in PUBLISHED.items():
            if k not in meas:
                meas[k] = {"tstar": t, "source": "hunt #4 published value, not re-measured here",
                           "polished": {"y0": repr(y0), "gamma": repr(g)}}
    cens: dict[int, dict] = {}
    for key, blob in data.items():
        if key.startswith("census_"):
            for pk, v in blob.items():
                if pk.startswith("pair"):
                    cens[int(pk[4:])] = v
    ks = sorted(set(meas) & set(cens))
    print(f"pairs with both a landing and a census: {ks}")

    # polished y0 from the pde stage where available
    def y0_of(k):
        if k in meas and "polished" in meas[k]:
            return float(mp.mpf(meas[k]["polished"]["y0"]))
        return PUBLISHED[k][1]

    def gamma_of(k):
        if k in meas and "polished" in meas[k]:
            return float(mp.mpf(meas[k]["polished"]["gamma"]))
        return PUBLISHED[k][0]

    rows = []
    for k in ks:
        gamma, y0 = gamma_of(k), y0_of(k)
        c = cens[k]
        others = [{"x": gamma_of(j), "y": y0_of(j)} for j in ks
                  if j != k and abs(gamma_of(j) - gamma) < c["half_window"]]
        S = neighbour_sum_builder(gamma, c["line_zeros"], others, c["half_window"])
        S0 = S(0.0)
        t_meas = meas[k]["tstar"]
        naive = 0.5 * y0 * y0
        shave = 1.0 - t_meas / naive
        t_model = landing_integral(y0, S)
        d = c["d_nearest"]
        rows.append({
            "pair": k, "gamma": gamma, "y0": y0,
            "tstar_measured": t_meas, "tstar_naive": naive,
            "shave": shave,
            "S0": S0, "S0_y0sq": S0 * y0 * y0,
            "d_nearest": d, "y0_over_d_sq": (y0 / d) ** 2,
            "tstar_frozen_model": t_model,
            "model_over_measured": t_model / t_meas,
            "shave_frozen_model": 1.0 - t_model / naive,
            "mean_gap_formula": c["mean_gap_formula"],
            "gap_measured": 1.0 / c["density_measured"],
            "d_over_h_measured": d / c["mean_gap_formula"],
            "tstar_source": meas[k].get("source", "unknown"),
        })
        print(f"pair {k}: shave {100*shave:7.3f}%  S0*y0^2 {S0*y0*y0:7.4f}  "
              f"2(y0/d)^2 {2*(y0/d)**2:7.4f}  frozen model t* {t_model:.8f} "
              f"(ratio {t_model/t_meas:.4f})", flush=True)

    fits: dict = {}
    xs = [r["S0_y0sq"] for r in rows]
    ys = [r["shave"] for r in rows]
    slope, resid, r2 = _linfit_through_origin(xs, ys)
    fits["shave_vs_S0y0sq"] = {
        "predicted_slope": 1.0, "fitted_slope": slope, "r2": r2,
        "residuals": dict(zip([r["pair"] for r in rows], resid)),
        "max_abs_residual": max(abs(v) for v in resid),
        "rms_relative": math.sqrt(sum((r / y) ** 2 for r, y in zip(resid, ys)) / len(ys)),
    }
    xs2 = [r["y0_over_d_sq"] for r in rows]
    slope2, resid2, r22 = _linfit_through_origin(xs2, ys)
    fits["shave_vs_y0_over_d_sq"] = {
        "predicted_slope_two_neighbours": 2.0, "fitted_slope": slope2, "r2": r22,
        "residuals": dict(zip([r["pair"] for r in rows], resid2)),
        "rms_relative": math.sqrt(sum((r / y) ** 2 for r, y in zip(resid2, ys)) / len(ys)),
    }
    # is the exponent really 1?  log-log fit shave = A (S0 y0^2)^p
    lx = [math.log(x) for x in xs]
    ly = [math.log(y) for y in ys]
    n = len(lx)
    mx, my = sum(lx) / n, sum(ly) / n
    sxx = sum((a - mx) ** 2 for a in lx)
    p = sum((a - mx) * (b - my) for a, b in zip(lx, ly)) / sxx
    logA = my - p * mx
    pred = [logA + p * a for a in lx]
    ss_res = sum((b - c) ** 2 for b, c in zip(ly, pred))
    sd_p = math.sqrt(ss_res / (n - 2) / sxx)
    fits["shave_power_law"] = {"exponent": p, "exponent_sd": sd_p,
                               "amplitude": math.exp(logA),
                               "predicted_exponent": 1.0,
                               "predicted_amplitude": 1.0}
    # can nine points separate the two candidate regressors?
    def _corr(u, v):
        mu, mv = sum(u) / len(u), sum(v) / len(v)
        num = sum((a - mu) * (b - mv) for a, b in zip(u, v))
        den = math.sqrt(sum((a - mu) ** 2 for a in u) * sum((b - mv) ** 2 for b in v))
        return num / den
    fits["regressor_collinearity"] = {
        "corr_S0y0sq_vs_y0_over_d_sq": _corr(xs, xs2),
        "note": "two regressors this collinear cannot be told apart by nine points",
        "y0_range": [min(r["y0"] for r in rows), max(r["y0"] for r in rows)],
        "S0y0sq_range": [min(xs), max(xs)],
    }

    ratios = [r["model_over_measured"] for r in rows]
    fits["frozen_neighbour_integral"] = {
        "free_parameters": 0,
        "ratio_model_over_measured": dict(zip([r["pair"] for r in rows], ratios)),
        "mean": sum(ratios) / len(ratios),
        "sd": math.sqrt(sum((x - sum(ratios) / len(ratios)) ** 2 for x in ratios)
                        / (len(ratios) - 1)),
        "worst": max(abs(x - 1.0) for x in ratios),
    }

    # one-parameter lattice calibration: d/h per pair such that the lattice
    # model reproduces the measured landing exactly
    from scipy.optimize import brentq
    dfacs = []
    for r in rows:
        h = r["mean_gap_formula"]

        def f(dfac):
            return landing_integral(r["y0"], lattice_S_fast(h, dfac)) - r["tstar_measured"]
        try:
            dfac = brentq(f, 0.2, 12.0, xtol=1e-8)
        except ValueError:
            dfac = float("nan")
        dfacs.append(dfac)
        r["dfac_calibrated"] = dfac
    good = [d for d in dfacs if d == d]
    mean_d = sum(good) / len(good)
    sd_d = math.sqrt(sum((d - mean_d) ** 2 for d in good) / (len(good) - 1))
    fits["lattice_calibration"] = {
        "free_parameters": 1,
        "dfac_per_pair": dict(zip([r["pair"] for r in rows], dfacs)),
        "mean": mean_d, "sd": sd_d, "cv": sd_d / mean_d,
    }
    # leave-one-out on the one-parameter model
    loo = []
    for i, r in enumerate(rows):
        rest = [d for j, d in enumerate(good) if j != i]
        dm = sum(rest) / len(rest)
        pred = landing_integral(r["y0"], lattice_S_fast(r["mean_gap_formula"], dm))
        loo.append(pred / r["tstar_measured"])
    fits["lattice_calibration"]["leave_one_out_ratio"] = dict(
        zip([r["pair"] for r in rows], loo))
    fits["lattice_calibration"]["loo_rms_percent"] = 100.0 * math.sqrt(
        sum((x - 1.0) ** 2 for x in loo) / len(loo))

    # closed form vs direct lattice sum, as a check on lattice_S_fast
    chk = []
    for h, dfac, y in ((1.5, 1.4, 0.3), (1.0, 1.43, 0.6), (0.8, 2.0, 0.1),
                       (2.2, 1.43, 0.62)):
        a = lattice_S(h, dfac)(y)
        b = lattice_S_fast(h, dfac)(y)
        chk.append({"h": h, "dfac": dfac, "y": y, "direct": a, "closed": b,
                    "rel": abs(a - b) / b})
    fits["lattice_closed_form_check"] = chk

    # ------------------------------------------------------------------
    # the extrapolation
    # ------------------------------------------------------------------
    dbar = mean_d
    extrap = {"dfac_used": dbar, "Delta": DELTA, "upper_bound": UPPER}
    grid = []
    for y0 in (0.60, 0.61, 0.62, DELTA):
        for gamma in (85.7, 240.4, 411.8, 1e3, 1e4, 1e5, 1e6, 1e8, 1e12):
            h = mean_gap(gamma)
            t = landing_integral(y0, lattice_S_fast(h, dbar), n=8000)
            lin = 0.5 * y0 * y0 * (1.0 - lattice_S_fast(h, dbar)(0.0) * y0 * y0)
            grid.append({
                "y0": y0, "gamma": gamma, "mean_gap": h,
                "tstar_model": t,
                "tstar_naive": 0.5 * y0 * y0,
                "shave_percent": 100.0 * (1.0 - t / (0.5 * y0 * y0)),
                "fraction_of_upper_bound": t / UPPER,
                "tstar_linear_law": lin,
                "linear_law_valid": abs(lin - t) / t < 0.05,
            })
        # isolated: d -> infinity
        grid.append({"y0": y0, "gamma": None, "mean_gap": None,
                     "tstar_model": 0.5 * y0 * y0, "tstar_naive": 0.5 * y0 * y0,
                     "shave_percent": 0.0,
                     "fraction_of_upper_bound": (0.5 * y0 * y0) / UPPER,
                     "tstar_linear_law": 0.5 * y0 * y0, "linear_law_valid": True})
    extrap["grid"] = grid
    # the central number: the best a pair at the strip edge can do, over height
    at_edge = [g for g in grid if g["y0"] == DELTA and g["gamma"] is not None]
    best = max(at_edge, key=lambda g: g["tstar_model"])
    extrap["best_at_strip_edge"] = best
    # sensitivity of that number to the calibration parameter
    sens = []
    for f in (dbar - 2 * sd_d, dbar - sd_d, dbar, dbar + sd_d, dbar + 2 * sd_d):
        h = mean_gap(best["gamma"])
        sens.append({"dfac": f,
                     "tstar": landing_integral(DELTA, lattice_S_fast(h, f), n=8000)})
    extrap["sensitivity_to_dfac"] = sens
    # sanity: the model can never exceed the theorem's ceiling
    extrap["max_model_value_over_grid"] = max(g["tstar_model"] for g in grid)
    extrap["exceeds_upper_bound"] = bool(
        extrap["max_model_value_over_grid"] > UPPER + 1e-12)
    # honest error envelope: the frozen-neighbour integral is known from the
    # phase-1 polynomial toys to run low, by a factor that grows with y0/h
    # (1.011 at y0/h = 0.15, 1.13 at 0.6, 1.16 at 0.86).  The lattice
    # calibration absorbs the average of that bias over the fitted range;
    # what is left at the extrapolation point is the growth of the bias.
    env = {}
    for f in (1.0, 1.05, 1.10, 1.16, 1.25):
        env[f"bias_factor_{f}"] = {
            "tstar": best["tstar_model"] * f,
            "fraction_of_upper_bound": best["tstar_model"] * f / UPPER,
            "still_below_upper_bound": bool(best["tstar_model"] * f < UPPER),
        }
    extrap["bias_envelope_at_best"] = env
    # non-parametric extrapolation: take each measured neighbour configuration
    # exactly as it is and ask what a pair of depth y0 would do sitting in it.
    # No lattice, no fitted parameter, just the measured zeros of Xi_DH.
    npx = []
    for r in rows:
        k = r["pair"]
        c = cens[k]
        others = [{"x": gamma_of(j), "y": y0_of(j)} for j in ks
                  if j != k and abs(gamma_of(j) - r["gamma"]) < c["half_window"]]
        S = neighbour_sum_builder(r["gamma"], c["line_zeros"], others,
                                  c["half_window"])
        row = {"pair": k, "gamma": r["gamma"]}
        for yv in (0.60, DELTA):
            row[f"tstar_at_y0_{yv:.4f}"] = landing_integral(yv, S, n=4000)
        row["fraction_of_upper_bound_at_Delta"] = row[f"tstar_at_y0_{DELTA:.4f}"] / UPPER
        npx.append(row)
    extrap["nonparametric_by_configuration"] = npx
    extrap["nonparametric_best_at_Delta"] = max(
        r[f"tstar_at_y0_{DELTA:.4f}"] for r in npx)

    # a holdout the model never saw: the gamma = 531 quadruple measured in
    # hunts/lambda_dh_bounds (ODE route, census_results.json)
    hy0, hg, hmeas = 0.34695380309204904, 531.27972689652, 0.05033975468118168
    hpred = landing_integral(hy0, lattice_S_fast(mean_gap(hg), dbar), n=8000)
    extrap["holdout_gamma531"] = {"gamma": hg, "y0": hy0, "measured_ode": hmeas,
                                  "model": hpred, "ratio": hpred / hmeas}

    payload = {"rows": rows, "fits": fits, "extrapolation": extrap}
    save_results({"fit": payload}, out)
    print(json.dumps({"fits": fits, "best_at_strip_edge": best,
                      "exceeds_upper_bound": extrap["exceeds_upper_bound"]},
                     indent=2)[:4000])


# ---------------------------------------------------------------------------
# plumbing
# ---------------------------------------------------------------------------


def load_results(path: str = RESULTS) -> dict:
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    return {}


def save_results(update: dict, path: str = RESULTS) -> None:
    data = load_results(path)
    data.update(update)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")


def stage_harvest(log_glob: str, out: str) -> None:
    """Recover landings from worker stdout when a worker is still mid-list.

    ``stage_pde`` writes its JSON only after finishing every pair it was given,
    so a worker interrupted on its second pair would lose the first.  The
    printed line carries the same numbers; this parses them back.  Rows
    harvested this way are marked, because they carry fewer digits than the
    JSON would.
    """
    import re
    pat = re.compile(r"^pair (\d+) \(gamma~([\d.]+)\): t\* = ([\d.]+) published "
                     r"([\d.]+) rel diff ([-+0-9.e]+) shave ([\d.]+)% "
                     r"\[([\d.]+)s dps=(\d+) M=(\d+) r=([\d.]+)\]")
    res: dict = {}
    for path in sorted(glob.glob(log_glob)):
        with open(path, "r", encoding="utf-8") as f:
            for line in f:
                m = pat.match(line.strip())
                if not m:
                    continue
                k = int(m.group(1))
                res[f"pair{k}"] = {
                    "tstar": float(m.group(3)),
                    "published": float(m.group(4)),
                    "rel_diff_vs_published": float(m.group(5)),
                    "shave_percent": float(m.group(6)),
                    "seconds": float(m.group(7)),
                    "dps": int(m.group(8)),
                    "M": int(m.group(9)),
                    "radius": float(m.group(10)),
                    "harvested_from_log": True,
                }
                print("harvested", f"pair{k}", res[f"pair{k}"]["tstar"])
    if res:
        save_results({"pde_harvested": res}, out)


def stage_merge() -> None:
    for path in sorted(glob.glob(os.path.join(_HERE, "landing_*.json"))):
        with open(path, "r", encoding="utf-8") as f:
            save_results(json.load(f))
        os.remove(path)
        print("merged", os.path.basename(path))


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("stage", choices=["pde", "census", "fit", "merge", "harvest"])
    ap.add_argument("--logs", default="", help="glob of worker logs for harvest")
    ap.add_argument("--pairs", default="1,2,3,4,5,6,7,8,9")
    ap.add_argument("--out", default=RESULTS)
    ap.add_argument("--M", type=int, default=120)
    ap.add_argument("--extra-dps", type=int, default=30)
    ap.add_argument("--fallback-published", action="store_true",
                    help="use hunt #4's published t* for any pair not re-measured "
                         "here, labelled as such in the output rows")
    args = ap.parse_args()
    out = args.out if os.path.isabs(args.out) else os.path.join(_HERE, args.out)
    pairs = [int(s) for s in args.pairs.split(",") if s.strip()]
    if args.stage == "pde":
        stage_pde(pairs, out, M=args.M, extra_dps=args.extra_dps)
    elif args.stage == "census":
        stage_census(pairs, out)
    elif args.stage == "fit":
        stage_fit(out, fallback_published=args.fallback_published)
    elif args.stage == "merge":
        stage_merge()
    elif args.stage == "harvest":
        stage_harvest(args.logs, out)


if __name__ == "__main__":
    main()
