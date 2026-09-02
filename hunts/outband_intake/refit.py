"""Extrapolate the two LP ladders, and show how much the answer depends on the fit.

Reads the checkpointed solves in artifacts/ and fits `a + b * X^(-p)` to each
ladder three ways: the difference ladder `v_out - v_in` (the route RESULTS.md §1
first took), the out-of-band ladder alone, and the in-band control alone. The
in-band control's limit is known, it is the record `0.6725007036794116`, so its
fitted excess over the record is the method error of whichever fit produced it.

The point of running all three is that a three-parameter fit through five points
does not pin the limit tightly: the free-exponent difference fit lands on
`0.6793`, one digit from Chirre, Goncalves and de Laat's `0.6792`, and the direct
out-of-band fit lands near `0.6821`, one digit from the bandwidth-one ceiling
`0.6818286874638`. Neither coincidence is evidence. The honest statement is the
range these fits span once each is corrected by its own method error.

Run from the repo root:
    .venv/bin/python hunts/outband_intake/refit.py
"""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
from scipy.optimize import curve_fit

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE / "artifacts"
RECORD = 0.6725007036794116
CEILING = 0.6818286874638
CGDL = 0.6792


def ladders():
    out, inb = {}, {}
    for row in json.loads((ARTIFACTS / "lane-a-convergence.json").read_text()):
        (out if row["A_out"] else inb)[row["X"]] = row["value"]
    for row in json.loads((ARTIFACTS / "lane-a-control-inband-long.json").read_text()):
        inb[row["X"]] = row["value"]
    xs = sorted(out)
    return (np.array(xs), np.array([out[x] for x in xs]),
            np.array(sorted(inb)), np.array([inb[x] for x in sorted(inb)]))


def power(x, a, b, p):
    return a + b * x ** (-p)


def fit_free(x, y):
    (a, b, p), _ = curve_fit(power, x, y, p0=[y[-1] * 0.5, 1.0, 1.0], maxfev=20000)
    return a, p


def fit_pinned(x, y, p):
    design = np.vstack([np.ones_like(x), x ** (-p)]).T
    return np.linalg.lstsq(design, y, rcond=None)[0][0]


def main():
    x_out, v_out, x_in, v_in = ladders()
    common = np.isin(x_in, x_out)
    diff = v_out - v_in[common]

    print(f"out-of-band rungs X = {x_out.tolist()}")
    print(f"in-band rungs     X = {x_in.tolist()}\n")

    a_diff, p_diff = fit_free(x_out, diff)
    a_in, p_in = fit_free(x_in, v_in - RECORD)
    a_in4, p_in4 = fit_free(x_out, v_in[common] - RECORD)
    a_out, p_out = fit_free(x_out, v_out - RECORD)

    print("free-exponent fits, a + b X^(-p), excess over the record:")
    print(f"  difference ladder      a = {a_diff:+.5f}  p = {p_diff:.2f}"
          f"   -> record + a = {RECORD + a_diff:.4f}  (CGdL {CGDL})")
    print(f"  in-band, matched rungs a = {a_in4:+.5f}  p = {p_in4:.2f}   (true limit 0: method error)")
    print(f"  in-band, all rungs     a = {a_in:+.5f}  p = {p_in:.2f}   (true limit 0: method error)")
    print(f"  out-of-band direct     a = {a_out:+.5f}  p = {p_out:.2f}"
          f"   -> record + a = {RECORD + a_out:.4f}  (ceiling {CEILING:.4f})")
    print(f"  out-of-band direct, less the in-band overshoot on the same rungs:"
          f" {RECORD + a_out - a_in4:.4f}\n")

    print("exponent pinned instead of fitted:")
    print("  p     diff limit   in-band overshoot   out-of-band direct")
    for p in (0.5, 0.75, 1.0, 1.5, 2.0):
        print(f"  {p:<4}  {fit_pinned(x_out, diff, p):+.5f}     "
              f"{fit_pinned(x_out, v_in[common] - RECORD, p):+.5f}            "
              f"{RECORD + fit_pinned(x_out, v_out - RECORD, p):.4f}")


if __name__ == "__main__":
    main()
