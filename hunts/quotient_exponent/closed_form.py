"""Why the LP's residual excess has an exact closed form on the plateau.

`sweep.py` reports the minimised excess

    E(N, y) = min  sum_{q in Q_N} w_q e_q,
    w_q = sum_{d >= 2, floor(N/d) = q} Lambda(d),   e_q = sum_j c_j floor(q/j) - 1 >= 0,

and just before it reaches zero it sits on a plateau: a run of consecutive `y`
where the value does not move at all.  Those plateau values are not arbitrary
reals.  At three of the four sizes measured they are a small rational multiple
of a single logarithm of a single prime, to every digit the float solver
carries:

    N = 10^3   E = (7/2) log 2
    N = 10^4   E = 3 log 23
    N = 10^5   E = 6 log 113

The reason is structural rather than numerical, and it is what this file
measures.  Almost every attainable cell is *arithmetically empty*: `w_q` is a
sum of `Lambda(d)` over the `d` with `floor(N/d) = q`, that is over the integers
in `(N/(q+1), N/q]`, and `Lambda` vanishes off the prime powers.  An empty cell
costs the objective nothing no matter how much excess sits in it, so the solver
parks excess there for free.  On the plateau the optimal solution carries
positive excess in a dozen or more cells and **exactly one of them has nonzero
weight**.  The objective therefore collapses to one term,

    E = e_q * Lambda(p^k) = (a rational) * log p,

and the prime that shows up is the unique prime power in that one cell's
interval.  Nothing was fitted: the rational and the prime are read out of the
solution and checked against the value.

At N = 10^6 no such form appears here, and this file reports that rather than
hiding it.

    .venv/bin/python hunts/quotient_exponent/closed_form.py
"""
from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from mpmath import mp
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, identity
from scipy.sparse import hstack as sparse_hstack

from lp import cell_weights, quotient_cells, von_mangoldt_prefix

ART = Path(__file__).resolve().parent / "artifacts"
mp.dps = 40

TOL = 1e-9


def solve(N: int, y: int):
    """The LP of lp.py, returning the cells, their weights and the excesses."""
    psi = von_mangoldt_prefix(N)
    cells = quotient_cells(N)
    w = cell_weights(N, cells, psi)
    m, n = len(cells), y
    A = (cells[:, None] // np.arange(1, y + 1)[None, :]).astype(np.float64)
    Aeq = sparse_hstack([csr_matrix(A), -identity(m, format="csr")], format="csr")
    res = linprog(np.concatenate([np.zeros(n), w]), A_eq=Aeq, b_eq=np.ones(m),
                  bounds=[(None, None)] * n + [(0.0, None)] * m, method="highs")
    if not res.success:
        return None
    return cells, w, res.x[y:], float(res.fun)


def prime_powers_in(lo: int, hi: int) -> list[tuple[int, int, int]]:
    """(d, p, k) for each prime power p^k with lo < d <= hi.  Trial division:
    the interval is one cell wide, so it holds a handful of integers at most."""
    out = []
    for d in range(max(lo + 1, 2), hi + 1):
        x, p, f = d, 2, {}
        while p * p <= x:
            while x % p == 0:
                f[p] = f.get(p, 0) + 1
                x //= p
            p += 1
        if x > 1:
            f[x] = f.get(x, 0) + 1
        if len(f) == 1:
            (q, k), = f.items()
            out.append((d, q, k))
    return out


def anatomy(N: int, y: int) -> dict:
    """Where the excess sits, and which of it the objective can see."""
    got = solve(N, y)
    if got is None:
        return {"N": N, "y": y, "solved": False}
    cells, w, e, E = got
    live = np.flatnonzero(e > TOL)
    weighted = [i for i in live if w[i] > TOL]

    rec = {
        "N": N, "y": y, "solved": True, "excess": E,
        "cells_with_excess": int(len(live)),
        "cells_with_excess_and_weight": int(len(weighted)),
        "closed_form": None,
    }
    if len(weighted) == 1:
        i = weighted[0]
        q = int(cells[i])
        pps = prime_powers_in(N // (q + 1), N // q)
        # the rational multiple, recovered from the solution not fitted to E
        frac = Fraction(e[i]).limit_denominator(64)
        rec["carrier"] = {
            "cell": q,
            "d_range": [int(N // (q + 1)) + 1, int(N // q)],
            "prime_powers_in_range": [{"d": d, "p": p, "k": k} for d, p, k in pps],
            "excess_in_cell": float(e[i]),
            "excess_as_fraction": [frac.numerator, frac.denominator],
            "weight_of_cell": float(w[i]),
        }
        if len(pps) == 1:
            _, p, _ = pps[0]
            pred = mp.mpf(frac.numerator) / frac.denominator * mp.log(p)
            rec["closed_form"] = {
                "expression": f"({frac.numerator}/{frac.denominator}) * log({p})"
                              if frac.denominator != 1 else
                              f"{frac.numerator} * log({p})",
                "value": mp.nstr(pred, 18),
                "observed": repr(E),
                "abs_diff": float(abs(pred - mp.mpf(E))),
                "rel_diff": float(abs(pred - mp.mpf(E)) / abs(pred)),
            }
    return rec


def plateau(N: int, y_lo: int, y_hi: int) -> dict:
    """The run of consecutive y on which E does not move, and its anatomy."""
    vals = {}
    for y in range(y_lo, y_hi + 1):
        got = solve(N, y)
        vals[y] = None if got is None else got[3]
    # longest run of equal, strictly positive values
    best, cur = [], []
    for y in range(y_lo, y_hi + 1):
        v = vals[y]
        if v is None or v <= TOL:
            cur = []
            continue
        if cur and abs(vals[cur[-1]] - v) <= TOL * max(1.0, abs(v)):
            cur.append(y)
        else:
            cur = [y]
        if len(cur) > len(best):
            best = list(cur)
    return {"values": vals, "plateau_y": best,
            "plateau_value": vals[best[0]] if best else None}


def main() -> None:
    out = {}
    # ranges bracket where sweep.py shows the last positive value before zero
    for N, lo, hi in [(1000, 50, 70), (10000, 150, 180), (100000, 545, 580)]:
        pl = plateau(N, lo, hi)
        ys = pl["plateau_y"]
        print(f"N={N}: plateau y = {ys[0]}..{ys[-1]} ({len(ys)} values), "
              f"E = {pl['plateau_value']!r}")
        rows = [anatomy(N, y) for y in (ys[0], ys[len(ys) // 2], ys[-1])] if ys else []
        for r in rows:
            cf = r.get("closed_form")
            print(f"   y={r['y']:>4}  cells with excess {r['cells_with_excess']:>3}, "
                  f"of which weighted {r['cells_with_excess_and_weight']}"
                  + (f"   {cf['expression']} = {cf['value']}  rel {cf['rel_diff']:.2e}"
                     if cf else "   (no single-carrier form)"))
        out[str(N)] = {"plateau": {"y": ys, "value": pl["plateau_value"]},
                       "anatomy": rows}

    # N = 10^6: one point only, each solve is ~40 s
    print("N=1000000: single point y=1995 (each solve ~40 s, no plateau scan)")
    r = anatomy(1000000, 1995)
    cf = r.get("closed_form")
    print(f"   y=1995  E={r.get('excess')!r}  cells with excess "
          f"{r.get('cells_with_excess')}, of which weighted "
          f"{r.get('cells_with_excess_and_weight')}"
          + (f"   {cf['expression']}" if cf else "   (no single-carrier form)"))
    out["1000000"] = {"plateau": None, "anatomy": [r]}

    (ART / "closed_form.json").write_text(json.dumps(out, indent=1) + "\n")
    print(f"-> {ART / 'closed_form.json'}")


if __name__ == "__main__":
    main()
