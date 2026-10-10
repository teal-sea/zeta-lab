"""The loss, derived exactly, after the fitted version left a per-form offset.

`law.py` predicts the correct-digit count from the leading asymptotics and its
residual over 49 transition cells is `+0.13` mean, `0.86` rms.  Those residuals
are not noise: they are `+0.85` on average for the form `(1,1,4)` and `-0.75`
for `(2,1,3)`, a systematic gap of 1.6 digits between two forms at the same
`sigma` and `t`.  A per-subject offset means a term of the model is missing, so
the model is re-derived rather than re-fitted.

`epstein_completed` returns `d^{s/2} * mellin` with

    mellin = first + second/sqrt(d) + 1/(sqrt(d)(s-1)) - 1/s,

whose last two terms are of size about `1/t` and are the largest things formed
when the answer is small.  The answer itself is

    Lambda_Q(s) = (sqrt(d)/pi)^s Gamma(s) zeta_Q(s),   so
    |mellin| = |Lambda_Q(s)| d^{-sigma/2} = pi^{-sigma} |Gamma(s)| |zeta_Q(s)|.

The discriminant cancels, and the decimal digits lost are

    L(sigma, t, Q) = log10(1/t) - log10|mellin|
                   = -log10 t + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)|.

There is no fitted constant in that and no asymptotic in it either: `|Gamma|`
comes from mpmath and `|zeta_Q|` from the lattice oracle the surface already
carries.  Substituting Stirling recovers `law.py`'s leading `0.68219 t` and
shows what `law.py` dropped: a `-log10 t`, a `sigma log10 pi`, and the size of
`zeta_Q` itself, which is where the per-form offset lives.  For `(1,1,4)` the
least represented value is 1 and for `(2,1,3)` it is 2, so at `sigma = 5` their
`log10|zeta_Q|` differ by about 1.5, which is the gap observed.
"""
from __future__ import annotations

import json
import math
from pathlib import Path

from mpmath import mp

ART = Path(__file__).resolve().parent / "artifacts"
LOG10_PI = math.log10(math.pi)


def digits_lost_exact(sigma: float, t: float, zeta_q_abs: float) -> float:
    with mp.workdps(30):
        log_gamma = float(mp.log10(abs(mp.gamma(mp.mpc(sigma, t)))))
    return -math.log10(t) + sigma * LOG10_PI - log_gamma - math.log10(zeta_q_abs)


def main() -> None:
    rows = json.loads((ART / "surface.json").read_text(encoding="utf-8"))
    rows = [r for r in rows if r.get("oracle_abs")]
    ceil_by = {}
    for r in rows:
        k = (tuple(r["form"]), r["t"])
        ceil_by[k] = max(ceil_by.get(k, 0.0), r["correct_digits"])

    out, resid, by_form = [], [], {}
    for r in rows:
        k = (tuple(r["form"]), r["t"])
        L = digits_lost_exact(r["sigma"], r["t"], r["oracle_abs"])
        pred = max(0.0, min(ceil_by[k], r["dps"] + 20 - L))
        d = r["correct_digits"] - pred
        out.append({**r, "digits_lost_exact": L, "predicted_exact": pred, "residual": d})
        if 0.5 < r["correct_digits"] < ceil_by[k] - 0.5:
            resid.append(d)
            by_form.setdefault(tuple(r["form"]), []).append(d)

    n = len(resid)
    mean = sum(resid) / n
    rms = math.sqrt(sum(x * x for x in resid) / n)
    print(f"cells that test the law: {n}")
    print(f"residual observed - predicted: mean {mean:+.3f}, rms {rms:.3f}, "
          f"worst {max(resid, key=abs):+.2f}")
    print("per form:")
    for f, ds in sorted(by_form.items()):
        print(f"  {f}  n={len(ds):>3d}  mean {sum(ds)/len(ds):+.3f}  "
              f"rms {math.sqrt(sum(x*x for x in ds)/len(ds)):.3f}")
    (ART / "law2.json").write_text(json.dumps(
        {"n_testing_cells": n, "residual_mean": mean, "residual_rms": rms,
         "per_form": {str(k): {"n": len(v), "mean": sum(v)/len(v)}
                      for k, v in by_form.items()},
         "rows": out}, indent=1), encoding="utf-8")




def centred(rows_path: str = "law2.json") -> None:
    """The derived law leaves ONE constant, uniform over forms and heights.

    That is what a correct derivation should leave: the model assumed the
    largest quantity formed is exactly `1/t`, and it is a little smaller, so the
    routine carries about one digit more than the bound says.  Reporting the rms
    about that constant separates "the shape is right" from "the constant is
    fitted", and the guard keeps the unfitted version, which errs safe.
    """
    d = json.loads((ART / rows_path).read_text(encoding="utf-8"))
    resid = [r["residual"] for r in d["rows"]
             if r.get("residual") is not None]
    # recompute the testing set the same way main() did
    rows = d["rows"]
    ceil_by = {}
    for r in rows:
        k = (tuple(r["form"]), r["t"])
        ceil_by[k] = max(ceil_by.get(k, 0.0), r["correct_digits"])
    test = [r["residual"] for r in rows
            if 0.5 < r["correct_digits"] < ceil_by[(tuple(r["form"]), r["t"])] - 0.5]
    m = sum(test) / len(test)
    rms_about_mean = math.sqrt(sum((x - m) ** 2 for x in test) / len(test))
    print()
    print(f"one constant, fitted over the whole surface: {m:+.3f} digits")
    print(f"rms about it: {rms_about_mean:.3f} digits over {len(test)} cells, "
          f"three forms, heights 40 to 160")
    print(f"worst deviation from it: {max(test, key=lambda x: abs(x - m)) - m:+.2f}")
    d["fitted_constant"] = m
    d["rms_about_fitted_constant"] = rms_about_mean
    (ART / rows_path).write_text(json.dumps(d, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
    centred()
