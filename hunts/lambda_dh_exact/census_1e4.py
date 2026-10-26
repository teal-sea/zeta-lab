"""Landing census below height 10^4: ODE landing times of the deepest pairs.

Hunt #119, resumption of 2026-10-26, step 3 (coordinator-approved for 10^4
only; 10^5 deferred).  Prediction P4 asks what a complete census to height
10^4 does to the best measured landing 0.05765184035; P5, P6 and P8 ask where
the maximum sits, what the local gap ratio is, and whether any pair lands
later than its own y0^2/2.

Candidates are the 21 zeros with beta > 0.85 below 10^4 (`decide_low_zeros.json`:
positions decided on both backends; that they are *all* such zeros rests on
the float screen and is measured).  A pair with y0 <= 0.35 needs
y0^2/2 <= 0.06125 and so beats the floor only with a shave under 5.9 percent,
against 12.5 to 16 percent measured at this depth in `hunts/lambda_dh_bounds`;
they are not run, and that gap is stated rather than closed.

Per candidate, deepest first, in the window [gamma - 40, gamma + 40]:

1. line zeros: sign changes of the Hardy-style Z of f on a grid of 1/60 of
   the mean gap, bisected 30 times (`deep_zeros.f_vline`, float64);
2. N_right, the zeros with beta > 0.505, and N_strip, all zeros with
   -1.05 < beta < 2.05, each by a float argument-principle count on the
   rectangle (same evaluator); the accounting N_strip = N_line + 2 N_right
   must close, else the window is recorded as unaccounted and not landed;
3. the N_right off-line zeros located (grid minimum of |f| from beta = 0.51,
   Newton), required distinct and equal in number to N_right;
4. the landing: `hunts/flow_repair/probe.ode_null_control`, the N-body ODE
   that `hunts/lambda_dh_bounds` matched to the Xi-plane contour measurement
   within 0.04 percent on flow_repair pairs 1 to 5, with the same half-window
   40 and 800 RK4 steps to t_end = 1.25 y0^2/2.

Grade: every landing is *measured* (float route, one instrument).  The
control is the floor pair itself (gamma = 240.4047): its ODE landing must
reproduce the recorded 0.05765184035 to within the instrument's 0.04 percent
band, or the census is not read.

Run:  .venv/bin/python hunts/lambda_dh_exact/census_1e4.py [--only K] [--validate]
"""
from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

import numpy as np

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(os.path.dirname(_HERE))
_FLOW = os.path.join(_ROOT, "hunts", "flow_repair")
for _p in (_HERE, _ROOT, _FLOW):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import deep_zeros as dz  # noqa: E402
import probe  # noqa: E402  (hunts/flow_repair/probe.py, read-only)

SRC = os.path.join(_HERE, "decide_low_zeros.json")
OUT = os.path.join(_HERE, "census_1e4.json")
HALF = 40.0
SIG_IN = 0.505
SIG_ALL = -1.05
FLOOR = 0.05765184034869543


def _theta(t):
    from scipy.special import loggamma
    return np.imag(loggamma(0.75 + 0.5j * t)) - 0.5 * t * math.log(math.pi / 5)


def line_zeros(a: float, b: float, per_gap: int = 60):
    gap = probe.mean_gap(0.5 * (a + b))
    npts = int(math.ceil((b - a) / gap * per_gap)) + 1
    dt = (b - a) / (npts - 1)
    ts = a + dt * np.arange(npts)
    zz = np.real(np.exp(1j * _theta(ts)) * dz.f_vline(0.5, a, dt, npts))

    def zed(t):
        v = dz.f_one(complex(0.5, t))
        th = float(_theta(np.array([t]))[0])
        return math.cos(th) * v.real - math.sin(th) * v.imag

    out = []
    for i in range(npts - 1):
        if (zz[i] > 0) != (zz[i + 1] > 0):
            lo, hi, flo = ts[i], ts[i + 1], zz[i]
            for _ in range(30):
                m = 0.5 * (lo + hi)
                fm = zed(m)
                if (flo > 0) != (fm > 0):
                    hi = m
                else:
                    lo, flo = m, fm
            out.append(0.5 * (lo + hi))
    return out


def count_float(sig_c: float, a: float, b: float, pts_per_unit: int = 32):
    """Measured argument-principle count on [sig_c, 2.05] x [a, b]."""
    bottom = dz.hvariation(a, sa=sig_c, sb=dz.SIGMA_R, n=200)
    top = dz.hvariation(b, sa=sig_c, sb=dz.SIGMA_R, n=200)
    left, _ = dz.vline_variation(sig_c, a, b, pts_per_unit=pts_per_unit)
    right, _ = dz.vline_variation(dz.SIGMA_R, a, b, pts_per_unit=pts_per_unit)
    raw = (bottom + right - top - left) / (2 * math.pi)
    n = int(round(raw))
    return n, abs(raw - n)


def _newton(seed: complex, a: float, b: float, iters: int = 60):
    """Newton on the fast evaluator, abandoned as soon as it leaves the box."""
    z = complex(seed)
    h = 1e-6
    for _ in range(iters):
        if not (0.3 < z.real < 1.4 and a - 1 <= z.imag <= b + 1):
            return None
        fz = dz.f_one(z)
        if abs(fz) < 1e-15:
            return z
        d = (dz.f_one(z + h) - dz.f_one(z - h)) / (2 * h)
        if d == 0 or not np.isfinite(abs(d)):
            return None
        step = fz / d
        if abs(step) > 0.5:
            step *= 0.5 / abs(step)
        z = z - step
        if abs(step) < 1e-15:
            return z
    return z


def offline_zeros(a: float, b: float, want: int):
    """Locate zeros with beta > SIG_IN in [a, b]: grid minima, Newton, dedupe."""
    found = []
    xs = np.linspace(SIG_IN + 0.005, 1.15, 24)
    step = 0.05
    npts = int((b - a) / step) + 1
    grid = np.array([np.abs(dz.f_vline(float(x), a, step, npts)) for x in xs])
    # local minima of |f| over the 2-D grid, best first
    cand = []
    for i in range(len(xs)):
        for j in range(1, npts - 1):
            v = grid[i, j]
            lo_i, hi_i = max(0, i - 1), min(len(xs), i + 2)
            if v <= grid[lo_i:hi_i, j - 1:j + 2].min():
                cand.append((v, complex(xs[i], a + step * j)))
    cand.sort(key=lambda c: c[0])
    for _, seed in cand:
        z = _newton(seed, a, b)
        if z is None or not (SIG_IN < z.real < 1.2 and a <= z.imag <= b):
            continue
        if abs(dz.f_one(z)) > 1e-9:
            continue
        if any(abs(z - w) < 1e-6 for w in found):
            continue
        found.append(z)
        if len(found) >= want + 3:
            break
    return found


def census_one(gamma: float, y0: float) -> dict:
    t0 = time.time()
    a, b = gamma - HALF, gamma + HALF
    # nudge the window edges off any zero: choose edges at line-grid midpoints
    reals = line_zeros(a - 1.0, b + 1.0)
    inner = [r for r in reals if a <= r <= b]
    if inner:
        lo_gap = [r for r in reals if r < a]
        hi_gap = [r for r in reals if r > b]
        if lo_gap:
            a = 0.5 * (lo_gap[-1] + inner[0])
        if hi_gap:
            b = 0.5 * (inner[-1] + hi_gap[0])
    reals = [r for r in reals if a < r < b]
    n_right, d_right = count_float(SIG_IN, a, b)
    n_all, d_all = count_float(SIG_ALL, a, b)
    entry = {"gamma": gamma, "y0": y0, "window": [a, b],
             "n_line": len(reals), "n_right_beta_gt_0.505": n_right,
             "defect_right": d_right, "n_strip": n_all, "defect_strip": d_all}
    entry["accounting_ok"] = bool(n_all == len(reals) + 2 * n_right)
    if not entry["accounting_ok"]:
        reals = line_zeros(a, b, per_gap=240)
        entry["n_line_refined"] = len(reals)
        entry["accounting_ok"] = bool(n_all == len(reals) + 2 * n_right)
    offl = offline_zeros(a, b, n_right)
    entry["n_offline_located"] = len(offl)
    entry["offline_located_ok"] = bool(len(offl) == n_right)
    me = min(offl, key=lambda z: abs(z - complex(0.5 + y0, gamma))) if offl else None
    entry["self_found"] = bool(me is not None and abs(me - complex(0.5 + y0, gamma)) < 1e-6)
    others = [{"x": z.imag, "y": z.real - 0.5} for z in offl if me is None or abs(z - me) > 1e-6]
    entry["other_pairs"] = [[o["x"], o["y"]] for o in others]
    near = min(reals, key=lambda r: abs(complex(0.5, r) - complex(0.5 + y0, gamma)))
    entry["nearest_line_zero_distance"] = abs(complex(0.5, near) - complex(0.5 + y0, gamma))
    entry["gap_ratio_d_over_h"] = abs(near - gamma) / probe.mean_gap(gamma)
    entry["landing_naive"] = y0 * y0 / 2
    if entry["accounting_ok"] and entry["offline_located_ok"] and entry["self_found"]:
        ode = probe.ode_null_control({"gamma": gamma, "y0": y0}, reals, others,
                                     t_end=1.25 * y0 * y0 / 2, n_steps=800, window=HALF)
        entry["landing_ode"] = ode["tstar_ode"]
        entry["shave_percent"] = (100 * (1 - ode["tstar_ode"] / (y0 * y0 / 2))
                                  if ode["tstar_ode"] else None)
        # the ODE matches the Xi-plane measurement to 0.04 percent, so a landing
        # only beats the measured floor if it clears that band
        entry["beats_floor"] = bool(ode["tstar_ode"] and ode["tstar_ode"] > FLOOR * 1.0004)
        entry["later_than_naive"] = bool(ode["tstar_ode"] and ode["tstar_ode"] > y0 * y0 / 2)
        entry["ode"] = {k: v for k, v in ode.items() if k != "trajectory_Q"}
    else:
        entry["landing_ode"] = None
        entry["skipped"] = "accounting or location did not close; not landed"
    entry["seconds"] = round(time.time() - t0, 1)
    return entry


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", type=int, default=None, help="run only the K deepest")
    ap.add_argument("--index", type=int, default=None, help="run one candidate by depth rank")
    ap.add_argument("--out", default=OUT)
    ap.add_argument("--source", default=None,
                    help="a deep_zeros screen artifact with a 'zeros' list (float locations) "
                         "instead of the decided low zeros")
    ap.add_argument("--min-y0", type=float, default=0.0,
                    help="with --source: land only zeros deeper than this")
    args = ap.parse_args()
    cands = []
    if args.source:
        for z in json.load(open(args.source))["zeros"]:
            if z["y0"] > args.min_y0:
                cands.append((z["y0"], z["gamma"]))
    else:
        for r in json.load(open(SRC))["rows"]:
            lo, hi = r["y0_enclosure_float"]
            tl, th = (float(Fraction(x)) for x in r["rectangle_t"])
            cands.append((0.5 * (lo + hi), 0.5 * (tl + th)))
    cands.sort(key=lambda c: -c[0])
    if args.index is not None:
        cands = [cands[args.index]]
    elif args.only:
        cands = cands[: args.only]
    data = json.load(open(args.out)) if os.path.exists(args.out) else {"rows": []}
    done = {round(e["gamma"], 3) for e in data["rows"]}
    for y0, g in cands:
        if round(g, 3) in done:
            continue
        e = census_one(g, y0)
        data["rows"].append(e)
        data["rows"].sort(key=lambda r: r["gamma"])
        with open(args.out, "w") as fh:
            json.dump(data, fh, indent=2)
        print(f"gamma {g:.4f} y0 {y0:.6f} line {e['n_line']} right {e['n_right_beta_gt_0.505']} "
              f"strip {e['n_strip']} acct {e['accounting_ok']} located {e['n_offline_located']} "
              f"t*_ode {e['landing_ode']} naive {e['landing_naive']:.6f} [{e['seconds']}s]", flush=True)


if __name__ == "__main__":
    main()
