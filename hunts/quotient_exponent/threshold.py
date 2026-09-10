"""Where the attainable-cell family reaches zero excess, by bisection in y.

`hunts/quotient_certificate/RESULTS.md` section 3 refutes a dimension count
that inferred zero excess from "more columns than cells", with an exact
`N = 27, y = 9` example whose minimum excess is `log 2`.  The count is
therefore not sufficient.  It is still the obvious candidate for where the
zero actually happens, and nobody had measured that.

`|Q_N| = 2 floor(sqrt N) - 1` is the number of attainable cells.  This module
bisects on `y` for the smallest support at which `T*(y, N) - psi(N)` is zero,
and reports it against `|Q_N|`.  Zero is read from the LP with a tolerance
tied to the problem's own scale, and every zero found is re-checked by
evaluating the excess directly from the returned coefficients through the
constraint definition, which the solver's objective does not go through.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path

import lp

ART = Path(__file__).resolve().parent / "artifacts"


def is_zero(N: int, y: int, tol_rel: float = 1e-9) -> tuple[bool, dict]:
    r = lp.solve(N, y, verbose=False)
    if not r["success"]:
        return False, r
    scale = max(1.0, r["psi_N"])
    zero = r["excess"] <= tol_rel * scale and r["excess_direct"] <= tol_rel * scale
    return zero, r


def bisect(N: int, lo: int, hi: int, log=print) -> dict:
    """Smallest y in [lo, hi] with zero excess, assuming monotonicity in y.

    Monotonicity is not assumed silently: the caller's bracket is checked at
    both ends, and the returned record carries the two straddling solves so a
    reader can see the transition rather than take the word for it.
    """
    zero_lo, r_lo = is_zero(N, lo)
    zero_hi, r_hi = is_zero(N, hi)
    if zero_lo:
        return {"N": N, "status": "bracket-low-already-zero", "lo": lo, "hi": hi}
    if not zero_hi:
        return {"N": N, "status": "bracket-high-not-zero", "lo": lo, "hi": hi,
                "excess_at_hi": r_hi["excess"]}
    a, b = lo, hi
    last_nonzero, last_zero = r_lo, r_hi
    while b - a > 1:
        m = (a + b) // 2
        z, r = is_zero(N, m)
        log(f"  N={N} y={m:>6d} excess={r['excess']:.6e} -> {'zero' if z else 'positive'}")
        if z:
            b, last_zero = m, r
        else:
            a, last_nonzero = m, r
    cells = lp.quotient_cells(N).size
    return {
        "N": N, "status": "found", "y_star": b, "cells": int(cells),
        "y_star_over_cells": b / cells,
        "y_star_alpha": math.log(b) / math.log(N),
        "last_positive": {"y": a, "excess": last_nonzero["excess"],
                          "excess_direct": last_nonzero["excess_direct"],
                          "min_e_direct": last_nonzero["min_e_direct"]},
        "first_zero": {"y": b, "excess": last_zero["excess"],
                       "excess_direct": last_zero["excess_direct"],
                       "min_e_direct": last_zero["min_e_direct"],
                       "max_abs_c": last_zero["max_abs_c"]},
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--out", default="threshold.json")
    args = ap.parse_args()
    rows = []
    for N in args.N:
        r = int(math.isqrt(N))
        row = bisect(N, lo=max(2, r // 2), hi=min(N - 1, 4 * r))
        rows.append(row)
        if row["status"] == "found":
            print(f"N={N:>9d}  y* = {row['y_star']:>6d}   |Q_N| = {row['cells']:>6d}   "
                  f"y*/|Q_N| = {row['y_star_over_cells']:.4f}   alpha = {row['y_star_alpha']:.4f}",
                  flush=True)
        else:
            print(f"N={N:>9d}  {row['status']}", flush=True)
    ART.mkdir(exist_ok=True)
    (ART / args.out).write_text(json.dumps(rows, indent=1), encoding="utf-8")


if __name__ == "__main__":
    main()
