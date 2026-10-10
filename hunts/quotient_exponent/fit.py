"""Fit log E = log C + a log N - b log y, and say what the fit does not settle.

The conjectured shape is `E >= c N / sqrt(y)`, i.e. `a = 1` and `b = 1/2`.  A
diagonal `y = floor(sqrt N)` cannot see `a` and `b` separately: it only sees
`a - b/2`.  The grid can.

Two restrictions, both stated rather than quietly applied.  Rows with zero
excess are excluded, because the logarithm is not defined there and because the
zero is a different phenomenon with its own measurement.  Rows with
`alpha > 0.5` are excluded from the headline fit, because the conjecture is
stated for `y <= sqrt N`; they are reported separately, since that is where the
shape visibly breaks.
"""
from __future__ import annotations

import glob
import json
import math
from pathlib import Path

import numpy as np

ART = Path(__file__).resolve().parent / "artifacts"


def load() -> list[dict]:
    rows = []
    for f in sorted(glob.glob(str(ART / "sweep*.json"))) + \
             [str(ART / "lp_small.json"), str(ART / "lp_large.json")]:
        try:
            rows += json.loads(Path(f).read_text(encoding="utf-8"))
        except FileNotFoundError:
            pass
    seen, out = set(), []
    for r in rows:
        if r.get("excess") is None:
            continue
        k = (r["N"], r["y"])
        if k in seen:
            continue
        seen.add(k)
        out.append(r)
    return out


def fit(rows) -> dict:
    A = np.array([[1.0, math.log(r["N"]), -math.log(r["y"])] for r in rows])
    b = np.array([math.log(r["excess"]) for r in rows])
    sol, *_ = np.linalg.lstsq(A, b, rcond=None)
    pred = A @ sol
    resid = b - pred
    return {"log_C": float(sol[0]), "a": float(sol[1]), "b": float(sol[2]),
            "n": len(rows), "resid_rms_in_log": float(np.sqrt((resid ** 2).mean())),
            "worst_rel": float(np.exp(np.abs(resid).max()) - 1)}


def main() -> None:
    rows = [r for r in load() if r["excess"] > 0]
    inside = [r for r in rows if math.log(r["y"]) / math.log(r["N"]) <= 0.5 + 1e-9]
    outside = [r for r in rows if math.log(r["y"]) / math.log(r["N"]) > 0.5 + 1e-9]

    res = {"inside_alpha_half": fit(inside)}
    if len(outside) >= 3:
        res["all_positive_rows"] = fit(rows)
    print("fit of log E = log C + a log N - b log y")
    for k, f in res.items():
        print(f"  {k:22s} n={f['n']:>3d}  a={f['a']:.3f}  b={f['b']:.3f}  "
              f"C={math.exp(f['log_C']):.4f}  rms(log)={f['resid_rms_in_log']:.3f}  "
              f"worst relative miss {100*f['worst_rel']:.0f}%")
    print()
    print("the conjectured shape is a = 1, b = 0.5")
    f = res["inside_alpha_half"]
    print(f"measured inside its own range: a = {f['a']:.3f}, b = {f['b']:.3f}")
    print()
    print("E*sqrt(y)/N at the right-hand endpoint y = floor(sqrt N), by N:")
    diag = sorted([r for r in rows if abs(math.log(r['y'])/math.log(r['N']) - 0.5) < 0.01],
                  key=lambda r: r["N"])
    for r in diag:
        print(f"  N={r['N']:>9d}  {r['excess']*math.sqrt(r['y'])/r['N']:.4f}")
    (ART / "fit.json").write_text(json.dumps(res, indent=1), encoding="utf-8")




def constrained_fit(rows, a_fixed=None, b_fixed=None) -> dict:
    """Least squares with a or b pinned, so the shapes can be compared directly."""
    cols, names = [np.ones(len(rows))], ["log_C"]
    target = np.array([math.log(r["excess"]) for r in rows])
    if a_fixed is None:
        cols.append(np.array([math.log(r["N"]) for r in rows])); names.append("a")
    else:
        target = target - a_fixed * np.array([math.log(r["N"]) for r in rows])
    if b_fixed is None:
        cols.append(np.array([-math.log(r["y"]) for r in rows])); names.append("b")
    else:
        target = target + b_fixed * np.array([math.log(r["y"]) for r in rows])
    A = np.vstack(cols).T
    sol, *_ = np.linalg.lstsq(A, target, rcond=None)
    resid = target - A @ sol
    out = dict(zip(names, (float(v) for v in sol)))
    out.update({"a": out.get("a", a_fixed), "b": out.get("b", b_fixed),
                "n": len(rows),
                "resid_rms_in_log": float(np.sqrt((resid ** 2).mean())),
                "worst_rel": float(np.exp(np.abs(resid).max()) - 1)})
    return out


def compare() -> None:
    rows = [r for r in load() if r["excess"] > 0]
    inside = [r for r in rows if math.log(r["y"]) / math.log(r["N"]) <= 0.5 + 1e-9]
    diag = [r for r in inside if abs(math.log(r["y"]) / math.log(r["N"]) - 0.5) < 0.01]
    print()
    print("model comparison, rms of the residual in log E (lower is better)")
    print(f"{'model':>34s} {'grid':>8s} {'diagonal only':>15s}")
    out = {}
    for label, kw in [("free a and b", {}),
                      ("conjectured: a=1, b=0.5", {"a_fixed": 1.0, "b_fixed": 0.5}),
                      ("a=1, b free", {"a_fixed": 1.0}),
                      ("b=0.5, a free", {"b_fixed": 0.5})]:
        g = constrained_fit(inside, **kw)
        d = constrained_fit(diag, **kw)
        out[label] = {"grid": g, "diagonal": d}
        print(f"{label:>34s} {g['resid_rms_in_log']:>8.4f} {d['resid_rms_in_log']:>15.4f}"
              f"   (a={g['a']:.3f}, b={g['b']:.3f})")
    (ART / "fit_comparison.json").write_text(json.dumps(out, indent=1), encoding="utf-8")
    print()
    print("A shape that fits the diagonal and not the grid is a shape the diagonal")
    print("could not test. That is the whole reason for the grid.")


if __name__ == "__main__":
    main()
    compare()
