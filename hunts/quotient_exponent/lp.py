"""The attainable-cell factorial LP, in a formulation whose objective IS the excess.

`hunts/quotient_certificate/` states the object.  For a cutoff N and a support
bound y, a floor-sum certificate is

    W_c(t) = sum_{j<=y} c_j floor(t/j),   B_c(N) = sum_{j<=y} c_j log(floor(N/j)!),

and the Chebyshev identity gives exactly

    B_c(N) - psi(N) = sum_{d=2}^{N} Lambda(d) [W_c(floor(N/d)) - 1].          (E)

So positivity is only needed on the attainable quotients Q_N = {floor(N/d)},
of which there are at most 2*floor(sqrt(N)) - 1, and

    T*(y, N) - psi(N) = min  sum_{q in Q_N} w_q e_q,
                        s.t.  e_q = sum_j c_j floor(q/j) - 1 >= 0,
                        w_q = sum_{d >= 2, floor(N/d) = q} Lambda(d).

**Why this formulation and not the factorial one.**  Minimising
`sum_j c_j log(floor(N/j)!)` and subtracting `psi(N)` asks a float solver for a
quantity near 1e4 as a difference of quantities near 1e8, and the answer is
carried entirely in the cancelling digits.  Written as above, every objective
coefficient `w_q` is nonnegative and every variable `e_q` is nonnegative, so the
objective is a sum of nonnegative terms equal to the excess itself and nothing
cancels.  The two programmes are algebraically identical: `sum_q w_q floor(q/j)`
telescopes to `log(floor(N/j)!)` by the same identity, and `sum_q w_q = psi(N)`.
That identity is asserted by nobody here; `check_identity` measures it.
"""
from __future__ import annotations

import argparse
import json
import time
from pathlib import Path

import math

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, identity
from scipy.sparse import hstack as sparse_hstack

ART = Path(__file__).resolve().parent / "artifacts"


def von_mangoldt_prefix(N: int) -> np.ndarray:
    """psi_partial[m] = sum_{d<=m} Lambda(d), float64, for m = 0..N.

    A boolean prime sieve, then log p written at p, p^2, p^3, ...  The prime
    powers are the whole content of Lambda beyond the primes and there are only
    O(sqrt N) of them, so the second pass is free.
    """
    lam = np.zeros(N + 1, dtype=np.float64)
    is_c = np.zeros(N + 1, dtype=bool)          # composite flag
    is_c[:2] = True
    for p in range(2, math.isqrt(N) + 1):
        if not is_c[p]:
            is_c[p * p::p] = True
    primes = np.flatnonzero(~is_c)
    lam[primes] = np.log(primes.astype(np.float64))
    for pp in primes:
        p = int(pp)
        if p * p > N:
            break
        lp = math.log(p)
        q = p * p
        while q <= N:
            lam[q] = lp
            if q > N // p:
                break
            q *= p
    return np.cumsum(lam)


def quotient_cells(N: int) -> np.ndarray:
    r = int(math.isqrt(N))
    cells = set(range(1, r + 1)) | {N // d for d in range(1, r + 1)}
    cells.discard(N)
    return np.array(sorted(cells), dtype=np.int64)


def cell_weights(N: int, cells: np.ndarray, psi: np.ndarray) -> np.ndarray:
    """w_q = sum over d >= 2 with floor(N/d) = q of Lambda(d).

    floor(N/d) = q holds for d in (N/(q+1), N/q], so the weight is a difference
    of two prefix sums of Lambda, with the d = 1 term (q = N) already excluded
    by dropping N from the cell set.
    """
    hi = np.minimum(N // np.maximum(cells, 1), N)
    lo = N // (cells + 1)
    lo = np.maximum(lo, 1)          # d >= 2 means we never count d = 1
    return psi[hi] - psi[lo]


def check_identity(N: int, y: int, cells: np.ndarray, w: np.ndarray,
                   psi: np.ndarray) -> dict:
    """The two things the reformulation rests on, measured rather than assumed."""
    total = float(w.sum())
    psi_N = float(psi[N])
    js = np.arange(1, y + 1, dtype=np.int64)
    # sum_q w_q floor(q/j) should equal log(floor(N/j)!)
    from math import lgamma
    lhs = (w[None, :] * (cells[None, :] // js[:, None])).sum(axis=1)
    rhs = np.array([lgamma(int(N // j) + 1) for j in js])
    rel = np.abs(lhs - rhs) / np.maximum(np.abs(rhs), 1.0)
    return {
        "sum_w_minus_psi_N": total - psi_N,
        "sum_w_rel_defect": abs(total - psi_N) / max(psi_N, 1.0),
        "factorial_telescope_max_rel_defect": float(rel.max()),
        "factorial_telescope_argmax_j": int(js[int(rel.argmax())]),
    }


def solve(N: int, y: int, verbose: bool = True) -> dict:
    t0 = time.time()
    psi = von_mangoldt_prefix(N)
    cells = quotient_cells(N)
    w = cell_weights(N, cells, psi)
    ident = check_identity(N, y, cells, w, psi)
    t_setup = time.time() - t0

    m, n = len(cells), y
    # variables: c_1..c_y (free), then e_q >= 0 for each cell
    A = (cells[:, None] // np.arange(1, y + 1)[None, :]).astype(np.float64)
    # sparse assembly: a dense identity block of size m would dominate memory
    # at the sizes this hunt is built to reach (m ~ 2 sqrt N)
    Aeq = sparse_hstack([csr_matrix(A), -identity(m, format="csr")], format="csr")
    beq = np.ones(m)
    cost = np.concatenate([np.zeros(n), w])
    bounds = [(None, None)] * n + [(0.0, None)] * m

    t1 = time.time()
    res = linprog(cost, A_eq=Aeq, b_eq=beq, bounds=bounds, method="highs")
    t_solve = time.time() - t1

    out = {
        "N": N, "y": y, "cells": int(m), "variables": int(n + m),
        "status": res.status, "message": res.message,
        "success": bool(res.success),
        "excess": float(res.fun) if res.success else None,
        "psi_N": float(psi[N]),
        "identity": ident,
        "setup_seconds": round(t_setup, 2), "solve_seconds": round(t_solve, 2),
    }
    if res.success:
        c = res.x[:n]
        e = res.x[n:]
        out["n_binding_cells"] = int((e < 1e-9).sum())
        out["max_abs_c"] = float(np.abs(c).max())
        out["c_head"] = [float(v) for v in c[:12]]
        out["A_c"] = float((c / np.arange(1, y + 1)).sum())
        # independent recomputation of the objective from the returned c,
        # through the constraint definition rather than the solver's value
        e_direct = A @ c - 1.0
        out["min_e_direct"] = float(e_direct.min())
        out["excess_direct"] = float((w * np.maximum(e_direct, 0.0)).sum())
        out["excess_direct_defect"] = abs(out["excess_direct"] - out["excess"])
    if verbose:
        print(json.dumps({k: v for k, v in out.items() if k != "c_head"}, indent=1))
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--y", type=int, nargs="*", default=None,
                    help="support bound; default floor(sqrt(N))")
    ap.add_argument("--out", default="lp.json")
    args = ap.parse_args()

    rows = []
    for N in args.N:
        ys = args.y if args.y else [int(math.isqrt(N))]
        for y in ys:
            rows.append(solve(N, y))
    ART.mkdir(exist_ok=True)
    (ART / args.out).write_text(json.dumps(rows, indent=1), encoding="utf-8")
    print(f"-> {ART / args.out}")


if __name__ == "__main__":
    main()
