"""Fit the measured convergence law err(c, N) from grid.json.

Models fitted to y(c) = log10 |gamma_1 error| at fixed N = 32 over the c
range where N = 32 is not yet the binding constraint, and to the c = 13
N-ladder.  Least squares in log space via numpy; emits ``rates.json``
with residuals so the fits are falsifiable (a held-out prediction for the
next c is printed for each model).
"""

from __future__ import annotations

import json
import os

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def fit_models(cs, ys):
    """y ~ a * f(c) + b for several f; returns per-model params + rms."""
    out = {}
    models = {
        "power_law": ("y = -a*c^q + b", None),  # nonlinear, small scan over q
        "linear_c": ("y = a*c + b", lambda c: c),
        "c_over_logc": ("y = a*c/log(c) + b", lambda c: c / np.log(c)),
        "sqrtc_logc": ("y = a*sqrt(c)*log(c) + b", lambda c: np.sqrt(c) * np.log(c)),
        "L2": ("y = a*log(c)^2 + b", lambda c: np.log(c) ** 2),
    }
    cs = np.asarray(cs, float)
    ys = np.asarray(ys, float)
    for name, (desc, f) in models.items():
        if f is not None:
            X = np.vstack([f(cs), np.ones_like(cs)]).T
            coef, res, *_ = np.linalg.lstsq(X, ys, rcond=None)
            pred = X @ coef
            rms = float(np.sqrt(np.mean((pred - ys) ** 2)))
            out[name] = {
                "form": desc,
                "a": float(coef[0]),
                "b": float(coef[1]),
                "rms_log10": rms,
            }
        else:
            best = None
            for q in np.arange(0.30, 1.51, 0.01):
                X = np.vstack([cs**q, np.ones_like(cs)]).T
                coef, *_ = np.linalg.lstsq(X, ys, rcond=None)
                pred = X @ coef
                rms = float(np.sqrt(np.mean((pred - ys) ** 2)))
                if best is None or rms < best["rms_log10"]:
                    best = {
                        "form": "y = a*c^q + b",
                        "a": float(coef[0]),
                        "q": round(float(q), 2),
                        "b": float(coef[1]),
                        "rms_log10": rms,
                    }
            out[name] = best
    return out


def main():
    data = json.load(open(os.path.join(HERE, "grid.json")))
    grid = data["grid"]
    ladder = data["ladder_c13"]

    # ---- N-saturation at c = 13 -----------------------------------------
    lad = [(r["N"], r["log10_gamma1_err"], r["log10_lambda_min_even"]) for r in ladder]
    # initial-regime slope: fit over the N range before saturation.  Detect
    # saturation as the point where the incremental gain drops below 20% of
    # the median early gain.
    Ns = [x[0] for x in lad]
    ys = [x[1] for x in lad]
    slopes = [(ys[i + 1] - ys[i]) / (Ns[i + 1] - Ns[i]) for i in range(len(Ns) - 1)]
    med = np.median(slopes[:3])
    cutidx = len(Ns)
    for i, s in enumerate(slopes):
        if abs(s) < 0.2 * abs(med):
            cutidx = i + 1
            break
    Xn = np.vstack([Ns[:cutidx], np.ones(cutidx)]).T
    coefN, *_ = np.linalg.lstsq(Xn, np.array(ys[:cutidx]), rcond=None)
    # local log-log exponents p(N) = d log10 err / d log10 N (Galerkin
    # power-law reading err ~ N^p)
    loglog = [
        (Ns[i + 1], (ys[i + 1] - ys[i]) / (np.log10(Ns[i + 1] / Ns[i])))
        for i in range(len(Ns) - 1)
    ]
    ladder_fit = {
        "regime_N": Ns[:cutidx],
        "slope_log10_per_mode": float(coefN[0]),
        "intercept": float(coefN[1]),
        "per_step_slopes": [float(s) for s in slopes],
        "local_loglog_exponents": [(int(n), float(p)) for n, p in loglog],
        "note": "log10 err_gamma1 vs N at c=13 before saturation",
    }

    # ---- c-law at N = 32 -------------------------------------------------
    rows = [r for r in grid if r["N"] == 32 and r["log10_gamma1_err"] is not None]
    cs = [r["c"] for r in rows]
    y1 = [r["log10_gamma1_err"] for r in rows]
    ylam = [r["log10_lambda_min_even"] for r in rows]
    fits_err = fit_models(cs, y1)
    fits_lam = fit_models(cs, ylam)

    # held-out check: refit each model without the largest c, predict it
    holdout = {}
    c_max = max(cs)
    idx = cs.index(c_max)
    cs_h = cs[:idx] + cs[idx + 1 :]
    y_h = y1[:idx] + y1[idx + 1 :]
    fits_h = fit_models(cs_h, y_h)
    for name, f in fits_h.items():
        if "q" in f:
            pred = f["a"] * c_max ** f["q"] + f["b"]
        elif name == "linear_c":
            pred = f["a"] * c_max + f["b"]
        elif name == "c_over_logc":
            pred = f["a"] * c_max / np.log(c_max) + f["b"]
        elif name == "sqrtc_logc":
            pred = f["a"] * np.sqrt(c_max) * np.log(c_max) + f["b"]
        else:
            pred = f["a"] * np.log(c_max) ** 2 + f["b"]
        holdout[name] = {"predicted_log10_err_at_cmax": float(pred), "actual": y1[idx]}

    # ratio |gamma1 err| / lambda_min across the N = 32 row (G1 Table 20
    # reports 6999..18489 across c = 13..67 at N = 100)
    ratio = [
        {
            "c": r["c"],
            "ratio": (
                r["gamma_errors"][0] / r["lambda_min_even"]
                if r["gamma_errors"][0]
                else None
            ),
        }
        for r in rows
    ]

    out = {
        "ladder_c13": ladder_fit,
        "c_law_N32_gamma1": fits_err,
        "c_law_N32_lambda_min": fits_lam,
        "holdout_at_cmax": holdout,
        "err_over_lambda_ratio_N32": ratio,
        "data_N32": {"c": cs, "log10_gamma1_err": y1, "log10_lambda_min": ylam},
    }
    with open(os.path.join(HERE, "rates.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
