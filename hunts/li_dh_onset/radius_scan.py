"""Establish the analyticity radius before any coefficient is extracted.

The Cauchy route reads log F(1/(1-z)) on |z| = r.  If F has a zero whose image
lands inside that circle the logarithm has no single-valued branch there and
every coefficient the pipeline returns is meaningless.  So the radius is not a
tuning knob, it is a claim about the zeros of the Davenport-Heilbronn function,
and this file is where that claim is measured instead of assumed.

Three legs, deliberately of different kinds so a shared defect is less likely.

1.  **The half-plane leg, arithmetic.**  With a_n the period-5 coefficients,
    |f(s)| >= 1 - sum_{n>=2} |a_n| n^{-Re s}, so f cannot vanish where that sum
    is below 1.  Re-measured here rather than quoted from ``zeta.epstein``.
2.  **The bounded-region leg, argument principle.**  ``count_zeros_box`` counts
    zeros of f in rectangles chosen to contain the part of the Apollonius disc
    {s : |1 - 1/s| <= r} with Re s <= 2.  A count of zero licenses the radius.
3.  **The off-line-census leg.**  Box counts against grid-refined sign-change
    counts on the critical line, window by window up to height 90.  This does
    not bear on the radius: every critical-line zero sits on |z| = 1 exactly and
    an off-line pair at height 85.7 sits at |z| = 0.99996.  It bears on the
    *onset* estimate, which is driven by the off-line quadruple of largest
    (2 beta - 1)/|1 - rho|^2, and that quantity is largest for the lowest strong
    pair.  A pair below height 85.7 would move the answer.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time

from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zeta.epstein import _stable_line_count, count_zeros_box, dh_coefficient, kappa

from dhli import apollonius_disc, disc_bounding_box, modulus_floor_for_radius

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")


def half_plane_bound(sigma: float, dps: int = 40) -> dict:
    """sum_{n>=2} |a_n| n^{-sigma}, in closed Hurwitz form, and its verdict.

    |a_n| is 1, kappa, kappa, 1, 0 on the period, so the sum is
    5^{-sigma}[zeta(s,1/5) + kappa zeta(s,2/5) + kappa zeta(s,3/5)
    + zeta(s,4/5)] - 1.  Below 1 it pins f away from zero on that vertical line
    and, since the sum decreases in sigma, on everything to its right.
    """
    with mp.workdps(dps):
        s = mp.mpf(sigma)
        k = kappa(dps)
        total = mp.power(5, -s) * (
            mp.zeta(s, mp.mpf(1) / 5)
            + k * mp.zeta(s, mp.mpf(2) / 5)
            + k * mp.zeta(s, mp.mpf(3) / 5)
            + mp.zeta(s, mp.mpf(4) / 5)
        )
        tail = total - 1
        # direct partial sum as a second route on the same quantity
        direct = mp.fsum(
            abs(dh_coefficient(n, dps)) * mp.power(n, -s) for n in range(2, 4001)
        )
        return {
            "sigma": float(sigma),
            "tail_hurwitz": mp.nstr(tail, 20),
            "tail_partial_sum_to_4000": mp.nstr(direct, 20),
            "zero_free": bool(tail < 1),
            "margin": mp.nstr(1 - tail, 20),
        }


def box(sig_lo, sig_hi, t_lo, t_hi, dps: int = 20) -> dict:
    t0 = time.time()
    n = count_zeros_box(
        mp.mpc(sig_lo, t_lo), mp.mpc(sig_hi, t_hi), dps=dps
    )
    return {
        "rect": [float(sig_lo), float(sig_hi), float(t_lo), float(t_hi)],
        "zeros": int(n),
        "seconds": round(time.time() - t0, 2),
    }


def radius_leg(radius: float, pad_sigma: float, pad_t: float, dps: int = 20) -> dict:
    """The rectangle that must be empty for ``radius`` to be admissible."""
    left, right, half = disc_bounding_box(radius, sigma_cap=2.0)
    c, rad = apollonius_disc(radius)
    rect = box(left - pad_sigma, right, -(half + pad_t), half + pad_t, dps=dps)
    return {
        "radius": radius,
        "apollonius_centre": c,
        "apollonius_radius": rad,
        "modulus_floor": modulus_floor_for_radius(radius),
        "disc_box_with_re_le_2": [left, right, half],
        "scanned": rect,
        "admissible": rect["zeros"] == 0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--radii", default="0.9,0.95")
    ap.add_argument("--tall-max", type=float, default=120.0)
    ap.add_argument("--census-min", type=float, default=0.0)
    ap.add_argument("--census-max", type=float, default=90.0)
    ap.add_argument("--dps", type=int, default=20)
    ap.add_argument("--out", default="radius_scan.json")
    ap.add_argument("--skip-radius-legs", action="store_true")
    ap.add_argument("--skip-tall", action="store_true")
    args = ap.parse_args()

    out: dict = {"generated": time.strftime("%Y-%m-%dT%H:%M:%S"), "dps": args.dps}

    out["half_plane"] = [half_plane_bound(s) for s in (2.0, 1.5)]

    out["radius_legs"] = []
    for r in ([] if args.skip_radius_legs else [float(x) for x in args.radii.split(",")]):
        leg = radius_leg(r, pad_sigma=0.006, pad_t=0.07, dps=args.dps)
        print("radius", r, "->", leg["scanned"], flush=True)
        out["radius_legs"].append(leg)

    # the brief's extended scan: nothing with Re > 1 below height tall_max
    out["tall_scan"] = []
    t = 0.0 if not args.skip_tall else args.tall_max
    while t < args.tall_max:
        hi = min(t + 20.0, args.tall_max)
        row = box(1.0001, 4.0, t, hi, dps=args.dps)
        print("tall", row, flush=True)
        out["tall_scan"].append(row)
        t = hi

    # box vs line, window by window: is there an off-line pair below 85.7?
    out["offline_census"] = []
    t = args.census_min
    while t < args.census_max:
        hi = min(t + 10.0, args.census_max)
        b = count_zeros_box(mp.mpc(-1.0, t), mp.mpc(2.0, hi), dps=args.dps)
        line = _stable_line_count(t, hi, dps=15)
        row = {"t_lo": t, "t_hi": hi, "box": int(b), "line": int(line),
               "excess": int(b) - int(line)}
        print("census", row, flush=True)
        out["offline_census"].append(row)
        t = hi

    os.makedirs(ART, exist_ok=True)
    path = os.path.join(ART, args.out)
    with open(path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("wrote", path)


if __name__ == "__main__":
    main()
