"""The shave model with each pair's own local gap: a per-pair d/h refit.

Hunt #119, follow-up of 2026-10-26, the door `RESULTS.md` section 8.7 named:
the calibrated model `theory.t_star_gap(y0, gamma, dfac)` freezes the local
gap at DBAR = 1.4284 mean gaps for every pair, and its four large misses
(ODE / model < 0.7) all sit at measured d/h < 0.123.  This module asks two
things of the 29 ODE landings (`census_1e4.json`, `census_deep4_1e5.json`):

1. **plug-in**: the model with dfac = the pair's own measured d/h (distance
   from the pair's ordinate to the nearest line zero over 2 pi / log(5 gamma /
   2 pi)), against the ODE landing;
2. **inverse**: the dfac that makes the model reproduce the ODE landing
   exactly (brentq), against the measured d/h.

Grade: *measured* (float, one model, landings themselves measured).  Nothing
here is a fit with more than zero free parameters per pair in (1); (2) is a
diagnostic, not a model.

Run:  .venv/bin/python hunts/lambda_dh_exact/refit_dh.py
"""
from __future__ import annotations

import importlib.util
import json
import math
import os
import time

from scipy.optimize import brentq

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, "refit_dh.json")


def _theory():
    spec = importlib.util.spec_from_file_location("ldh_theory", os.path.join(HERE, "theory.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _rows():
    out = []
    for name in ("census_1e4.json", "census_deep4_1e5.json"):
        for r in json.load(open(os.path.join(HERE, name)))["rows"]:
            if r["landing_ode"] is not None:
                out.append((name, r))
    return out


def _stats(xs):
    m = sum(xs) / len(xs)
    rms = math.sqrt(sum((x - 1) ** 2 for x in xs) / len(xs))
    return {"mean": m, "rms_dev_from_1": rms, "min": min(xs), "max": max(xs)}


def _linear(pairs):
    """Least squares d_inverse = a + b d_measured, with residual rms and max."""
    n = len(pairs)
    mx = sum(x for x, _ in pairs) / n
    my = sum(y for _, y in pairs) / n
    b = sum((x - mx) * (y - my) for x, y in pairs) / sum((x - mx) ** 2 for x, _ in pairs)
    a = my - b * mx
    res = [y - (a + b * x) for x, y in pairs]
    return {"a": a, "b": b, "rms_resid": math.sqrt(sum(r * r for r in res) / n),
            "max_abs_resid": max(abs(r) for r in res)}


def main() -> None:
    t0 = time.time()
    th = _theory()
    rows = []
    for src, r in _rows():
        y0, g, tode, dh = r["y0"], r["gamma"], r["landing_ode"], r["gap_ratio_d_over_h"]
        m_frozen = float(th.t_star_gap(y0, g))
        m_plug = float(th.t_star_gap(y0, g, dfac=dh))
        f = lambda d: float(th.t_star_gap(y0, g, dfac=d)) - tode
        try:
            d_inv = brentq(f, 1e-3, 20.0, xtol=1e-8)
        except ValueError:
            d_inv = None
        rows.append({"source": src, "gamma": g, "y0": y0, "landing_ode": tode,
                     "d_over_h_measured": dh, "model_frozen_dbar": m_frozen,
                     "ratio_frozen": tode / m_frozen, "model_plugin": m_plug,
                     "ratio_plugin": tode / m_plug, "d_over_h_inverse": d_inv})
    rf = [r["ratio_frozen"] for r in rows]
    rp = [r["ratio_plugin"] for r in rows]
    inv = [(r["d_over_h_measured"], r["d_over_h_inverse"]) for r in rows if r["d_over_h_inverse"]]
    mx = sum(a for a, _ in inv) / len(inv)
    my = sum(b for _, b in inv) / len(inv)
    cov = sum((a - mx) * (b - my) for a, b in inv)
    corr = cov / math.sqrt(sum((a - mx) ** 2 for a, _ in inv) * sum((b - my) ** 2 for _, b in inv))
    out = {
        "what": "shave model with per-pair measured d/h vs frozen DBAR, against 29 ODE landings",
        "date": "2026-10-26", "DBAR": th.DBAR, "n": len(rows),
        "frozen": _stats(rf), "plugin": _stats(rp),
        "inverse_vs_measured": {"n": len(inv), "pearson_r": corr,
                                "mean_inverse": my, "mean_measured": mx,
                                "linear_fit": _linear(inv)},
        "plugin_ratio_above_1": sum(x > 1 for x in rp),
        "rows": rows, "seconds": round(time.time() - t0, 1),
    }
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=2)
    print(json.dumps({k: v for k, v in out.items() if k != "rows"}, indent=1))


if __name__ == "__main__":
    main()
