"""Where the measured background and the measured quadruples put the sign change.

This is an extrapolation and it is labelled one everywhere it appears.  The
computed lambda_n(DH) stop at n_max; the index this file reports is two or three
orders of magnitude beyond that, and it is a *statement about a fitted model*,
not a measured coefficient.  What makes it worth writing down is that both of
its inputs are measured on this machine rather than borrowed: the background
comes from fitting the lambda_n(DH) this hunt computed, and the growth constants
come from off-line zeros this repository located by the argument principle.

The mechanism, stated so the extrapolation can be attacked.  Group the zeros
into the quadruple {rho, conj rho, 1-rho, 1-conj rho}.  Writing sigma = 1 - rho
and u = 1 - 1/sigma, the identity (1 - 1/rho)(1 - 1/sigma) = 1 collapses the
four Li terms to

    Q_n = 4 - 2 (R^n + R^-n) cos(n psi),    R = |u|, psi = arg u,

with R > 1 exactly when Re rho > 1/2.  For n small enough that R^n is still near
1 this is 4 - 4 cos(n psi), which is bounded, absorbed by the background fit and
invisible.  What the fit cannot see is the part that grows:

    lambda_n  =  background(n)  -  sum_k 2 (R_k^n + R_k^-n - 2) cos(n psi_k),

and the first n at which that expression turns negative is what is reported.
Subtracting the 2 is what stops the quadruples being counted twice, once in the
fit and once in the correction.

Three things this deliberately does *not* do.  It does not reuse the
envelope-crossing indicator of ``hunts/jensen_clock`` phase 3, which compared
2 r^n against lambda_n itself and fired at n = 1 because lambda_1 is 0.023; that
page declares it useless and it is not used here.  It does not assume the
quadruple list is complete, it reports what completeness would require and what
``radius_scan`` measured.  And it does not claim the answer is sharp: the
sensitivity table is part of the output, not a footnote to it.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time

import numpy as np
from mpmath import mp

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from zero_side import offline_quadruples, quadruple_growth

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

#: The conductor-5 analogue of ``zeta.li.li_asymptotic``'s bracket.  Derived,
#: not remembered: the smooth Davenport-Heilbronn zero density is
#: (1/2 pi) log(5 t / 2 pi), which is zeta's with 2 pi replaced by 2 pi / 5, and
#: the same substitution u = n/t that turns zeta's density into
#: (n/2)(log n - log 2 pi + euler - 1) turns this one into
#: (n/2)(log n + log(5 / 2 pi) + euler - 1).
B_PREDICTED = 0.5 * (math.log(5 / (2 * math.pi)) + 0.5772156649015328606 - 1)
B_ZETA = 0.5 * (-math.log(2 * math.pi) + 0.5772156649015328606 - 1)


def load_lambda(path: str):
    blob = json.load(open(path))
    return blob, np.array([float(v) for v in blob["lambda"]])


def fit_background(lam: np.ndarray, lo: int, hi: int) -> dict:
    """Least squares of a n log n + b n + c against the computed coefficients.

    Fitted over a high-n window because the whole point is the behaviour the
    extrapolation will lean on; a fit that includes n = 1 is dominated by the
    part of the curve nobody is extrapolating from.
    """
    n = np.arange(lo, hi + 1, dtype=float)
    y = lam[lo - 1:hi]
    A = np.column_stack([n * np.log(n), n, np.ones_like(n)])
    coef, *_ = np.linalg.lstsq(A, y, rcond=None)
    resid = y - A @ coef
    # the same fit with the leading coefficient pinned at 1/2
    A2 = np.column_stack([n, np.ones_like(n)])
    y2 = y - 0.5 * n * np.log(n)
    coef2, *_ = np.linalg.lstsq(A2, y2, rcond=None)
    resid2 = y2 - A2 @ coef2
    return {
        "window": [lo, hi],
        "free": {"a": float(coef[0]), "b": float(coef[1]), "c": float(coef[2]),
                 "max_abs_residual": float(np.max(np.abs(resid))),
                 "rms_residual": float(np.sqrt(np.mean(resid ** 2)))},
        "a_pinned_half": {"b": float(coef2[0]), "c": float(coef2[1]),
                          "max_abs_residual": float(np.max(np.abs(resid2))),
                          "rms_residual": float(np.sqrt(np.mean(resid2 ** 2)))},
        "b_predicted_dh": B_PREDICTED,
        "b_predicted_zeta_shaped": B_ZETA,
    }


def growths(quads) -> list:
    rows = []
    for q in quads:
        g = quadruple_growth(q["beta"], q["gamma"], dps=40)
        rows.append(
            {
                "label": q["label"],
                "beta": q["beta"][:22],
                "gamma": q["gamma"][:22],
                "log_R": float(mp.log(g["R"])),
                "R_minus_1": float(g["R_minus_1"]),
                "psi": float(g["psi"]),
                "period_in_n": float(2 * mp.pi / abs(g["psi"])),
            }
        )
    rows.sort(key=lambda r: -r["R_minus_1"])
    return rows


def first_negative(b: float, c: float, rows, n_hi: int, a: float = 0.5,
                   chunk: int = 200000, n_lo: int = 2000) -> dict:
    """First n >= n_lo at which background(n) minus the correction is negative.

    Scanned rather than solved because the correction oscillates: the envelope
    crosses the background smoothly, but the sign change needs cos(n psi) near
    +1 as well, and the resonance recurs only every 2 pi / |psi| steps.

    ``n_lo`` defaults to the top of the fit window and is not cosmetic.  A three
    parameter background fitted on n in the thousands is worthless at n = 1: a
    zeta-shaped background evaluated there returns 0.5*1*log 1 - 1.13 + 1 < 0
    and the scan "finds" a sign change at the first index it looks at.  That is
    the same degeneracy ``hunts/jensen_clock`` phase 3 recorded when its
    envelope indicator fired at n = 1 against lambda_1 = 0.023, and refusing to
    look below the fit window is the fix.
    """
    logR = np.array([r["log_R"] for r in rows])
    psi = np.array([r["psi"] for r in rows])
    lo = max(1, int(n_lo))
    while lo <= n_hi:
        hi = min(lo + chunk - 1, n_hi)
        n = np.arange(lo, hi + 1, dtype=float)
        bg = a * n * np.log(n) + b * n + c
        corr = np.zeros_like(n)
        for lr, ps in zip(logR, psi):
            with np.errstate(over="ignore"):
                grow = np.exp(lr * n) + np.exp(-lr * n) - 2.0
            corr += 2.0 * grow * np.cos(ps * n)
        val = bg - corr
        idx = np.nonzero(val < 0)[0]
        if idx.size:
            k = int(idx[0])
            return {"first_negative_n": int(n[k]),
                    "value_there": float(val[k]),
                    "background_there": float(bg[k]),
                    "correction_there": float(corr[k]),
                    "searched_to": hi}
        lo = hi + 1
    return {"first_negative_n": None, "searched_to": n_hi}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--table", default=None)
    ap.add_argument("--n-hi", type=int, default=2000000)
    args = ap.parse_args()

    path = args.table or os.path.join(ART, "lambda_dh_n2000_r0.9.json")
    blob, lam = load_lambda(path)
    n_max = blob["n_max"]

    fit = fit_background(lam, max(2, n_max // 2), n_max)
    fit_small = fit_background(lam, max(2, n_max // 10), n_max // 2)
    rows = growths(offline_quadruples())

    a = 0.5
    b = fit["a_pinned_half"]["b"]
    c = fit["a_pinned_half"]["c"]
    n_lo = n_max

    results = {
        "measured_background_all_quadruples":
            first_negative(b, c, rows, args.n_hi, a=a, n_lo=n_lo),
        "measured_background_dominant_quadruple_only":
            first_negative(b, c, rows[:1], args.n_hi, a=a, n_lo=n_lo),
        "measured_background_lower_fit_window":
            first_negative(fit_small["a_pinned_half"]["b"],
                           fit_small["a_pinned_half"]["c"],
                           rows, args.n_hi, a=a, n_lo=n_lo),
        "zeta_shaped_background_all_quadruples":
            first_negative(B_ZETA, 1.0, rows, args.n_hi, a=a, n_lo=n_lo),
        "n_lo_used": n_lo,
    }
    sensitivity = []
    for db in (-0.05, -0.02, 0.02, 0.05):
        r = first_negative(b + db, c, rows, args.n_hi, a=a, n_lo=n_lo)
        sensitivity.append({"delta_b": db, "first_negative_n": r["first_negative_n"]})
    for da in (-0.001, 0.001):
        r = first_negative(b, c, rows, args.n_hi, a=a + da, n_lo=n_lo)
        sensitivity.append({"delta_a": da, "first_negative_n": r["first_negative_n"]})
    for dl in (-0.02, 0.02):
        bumped = [dict(r) for r in rows]
        bumped[0]["log_R"] = rows[0]["log_R"] * (1 + dl)
        r = first_negative(b, c, bumped, args.n_hi, a=a, n_lo=n_lo)
        sensitivity.append({"relative_delta_log_R_of_dominant_pair": dl,
                            "first_negative_n": r["first_negative_n"]})

    n = np.arange(1, n_max + 1, dtype=float)
    resid = lam - (0.5 * n * np.log(n) + b * n + c)
    envelope = []
    for lo_, hi_ in ((1, 200), (201, 500), (501, 1000), (1001, n_max)):
        seg = resid[lo_ - 1:hi_]
        envelope.append({"window": [lo_, hi_], "min": float(seg.min()),
                         "max": float(seg.max()), "mean": float(seg.mean())})

    out = {
        "generated": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "table": os.path.relpath(path, HERE),
        "n_max_computed": n_max,
        "background_fit": fit,
        "background_fit_lower_window": fit_small,
        "quadruples_by_growth": rows,
        "onset": results,
        "sensitivity": sensitivity,
        "residual_envelope_vs_fitted_background": envelope,
        "grade": "the coefficients are measured; this index is a fitted "
                 "extrapolation two orders of magnitude past them",
    }
    os.makedirs(ART, exist_ok=True)
    p = os.path.join(ART, "onset.json")
    with open(p, "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: out[k] for k in ("background_fit", "onset", "sensitivity")},
                     indent=1))
    print("wrote", p)


if __name__ == "__main__":
    main()
