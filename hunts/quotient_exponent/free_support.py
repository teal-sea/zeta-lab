"""The door this hunt ranked first, tested.

`RESULTS.md` doors item 2 says: every certificate in this family takes its
support as an initial segment `1..y`, the staircase says most of that segment is
inert, and "a support chosen for rank rather than for being an interval is the
obvious untested variation".  A scouting pass in the same session reported that
freeing the positions reaches zero excess at `N = 10^4`.  This tests it.

Two questions, and only the second is interesting.

**Freeing the positions with no limit on how many.**  Allow every `j <= N/2` and
minimise the excess.  It is zero, and that says nothing: the hunt's own
threshold run already reaches zero at `y* = 173` consecutive columns at
`N = 10^4`, and this programme has 5000 columns available.

**Freeing the positions at a comparable SUPPORT SIZE.**  Excess is
`sum_q w_q e_q` with every term non-negative, so excess zero is exactly
`W(q) = 1` at every cell carrying prime mass and `W(q) >= 1` at the rest.
Minimise the coefficient mass under that, and count the positions the optimum
uses.  That is the number to compare against `y*`.

Minimising mass WITHOUT the zero-excess constraint is not the same problem and
returns the trivial `c = (1)` at `j = 1`: feasible, mass 1, excess 4915 at
`N = 10^3`.  It was tried first here, and it is recorded because the difference
between the two programmes is the whole content of this file.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix

import lp

ART = Path(__file__).resolve().parent / "artifacts"


def zero_excess_min_mass(N: int, jmax: int | None = None) -> dict:
    jmax = jmax or N // 2
    psi = lp.von_mangoldt_prefix(N)
    cells = lp.quotient_cells(N)
    w = lp.cell_weights(N, cells, psi)
    js = np.arange(1, jmax + 1, dtype=np.int64)
    A = (cells[:, None] // js[None, :]).astype(np.float64)
    hot = w > 1e-12
    n = len(js)
    res = linprog(
        np.ones(2 * n),
        A_eq=csr_matrix(np.hstack([A[hot], -A[hot]])), b_eq=np.ones(int(hot.sum())),
        A_ub=-csr_matrix(np.hstack([A[~hot], -A[~hot]])), b_ub=-np.ones(int((~hot).sum())),
        bounds=[(0.0, None)] * (2 * n), method="highs")
    if not res.success:
        return {"N": N, "status": res.message}
    c = res.x[:n] - res.x[n:]
    e = A @ c - 1.0
    nz = np.abs(c) > 1e-9
    return {
        "N": N, "sqrt_N": int(math.isqrt(N)), "jmax": int(jmax),
        "cells": int(len(cells)), "prime_mass_cells": int(hot.sum()),
        "support_used": int(nz.sum()), "max_j_used": int(js[nz].max()),
        "l1_mass": float(np.abs(c).sum()),
        "min_slack_float": float(e.min()),
        "excess_float": float((w * np.maximum(e, 0.0)).sum()),
        "support": [int(j) for j in js[nz]],
        "coefficients": [float(v) for v in c[nz]],
    }


def exact_check(row: dict, denominator: int = 10 ** 9) -> dict:
    """Re-check one solution in exact integers, on every attainable cell.

    A float LP that reports a slightly negative slack has not established
    anything, so the rounded rational point is checked with Python integers:
    `W(q) >= 1` everywhere and `W(q) = 1` at every prime-mass cell, which is
    exactly `excess = 0`.
    """
    N = row["N"]
    cells = [int(q) for q in lp.quotient_cells(N)]
    psi = lp.von_mangoldt_prefix(N)
    w = lp.cell_weights(N, lp.quotient_cells(N), psi)
    hot = {q for q, h in zip(cells, w > 1e-12) if h}
    num = [round(v * denominator) for v in row["coefficients"]]
    sup = row["support"]

    def W(q: int) -> int:
        return sum(a * (q // j) for a, j in zip(num, sup))

    below = [q for q in cells if W(q) < denominator]
    unequal = [q for q in hot if W(q) != denominator]
    return {
        "denominator": denominator, "cells_checked": len(cells),
        "prime_mass_cells": len(hot),
        "cells_with_W_below_1": len(below),
        "prime_mass_cells_with_W_not_1": len(unequal),
        "exact_zero_excess": not below and not unequal,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", default=[1000, 10000, 100000])
    ap.add_argument("--exact-up-to", type=int, default=1000)
    args = ap.parse_args()

    rows = []
    for N in args.N:
        r = zero_excess_min_mass(N)
        if N <= args.exact_up_to:
            r["exact"] = exact_check(r)
        thr = lp.solve(N, int(math.isqrt(N)), verbose=False)["excess"]
        r["consecutive_excess_at_y_sqrtN"] = thr
        rows.append(r)
        print(f"N={N:>7d} sqrt(N)={r['sqrt_N']:>4d}  zero excess needs "
              f"{r['support_used']:>4d} free positions (max j {r['max_j_used']:>6d}), "
              f"mass {r['l1_mass']:>7.1f}"
              + (f", EXACT: {r['exact']['exact_zero_excess']}" if "exact" in r else "")
              + f"  | consecutive y=sqrt(N) gives {thr:.4f}")
    ART.mkdir(exist_ok=True)
    (ART / "free_support.json").write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / 'free_support.json'}")


if __name__ == "__main__":
    main()
