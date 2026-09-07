"""All-cells LP floor V*(y,N) by constraint generation.

Same LP as lp_frontier.py (W_c(n) >= 1 for EVERY integer cell n <= N), but the
N x y dense matrix is never formed.  Start from the cells below 4y plus the
prime-power cells floor(N/d), solve, scan W on all cells, add the violated
ones, repeat.  The final solution satisfies every cell constraint (checked
directly), so the value is the true all-cells optimum up to LP tolerance.

Floating LP, diagnostic grade.  W >= 1 is re-verified on all N cells at the end.
"""
from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np
from scipy.optimize import linprog
from scipy.special import gammaln


def mangoldt(N: int) -> np.ndarray:
    lam = np.zeros(N + 1)
    is_comp = np.zeros(N + 1, dtype=bool)
    for p in range(2, N + 1):
        if is_comp[p]:
            continue
        lp = math.log(p)
        q = p
        while q <= N:
            lam[q] = lp
            q *= p
        is_comp[p * p :: p] = True
    return lam


def W_all(c: np.ndarray, N: int) -> np.ndarray:
    """W(n) for n = 0..N, via the divisor-sum jumps w = c * 1."""
    w = np.zeros(N + 1)
    for j in np.nonzero(np.abs(c) > 0)[0]:
        w[j + 1 :: j + 1] += c[j]
    return np.cumsum(w)


def solve(N: int, y: int, batch: int = 3000, max_rounds: int = 60, tol: float = 1e-7) -> dict:
    t0 = time.time()
    lam = mangoldt(N)
    psiN = float(lam.sum())
    r = int(math.isqrt(N))
    j = np.arange(1, y + 1)
    L = gammaln((N // j).astype(float) + 1.0)

    d_small = np.nonzero(lam[: r + 1] > 0)[0]
    cells = np.unique(np.concatenate([np.arange(1, min(N, 4 * y) + 1), N // d_small]))
    rounds = []
    c = None
    for rnd in range(max_rounds):
        A = (cells[:, None] // j[None, :]).astype(float)
        res = linprog(L, A_ub=-A, b_ub=-np.ones(cells.size), bounds=(None, None), method="highs-ds")
        del A
        if res.status != 0:
            raise RuntimeError(f"LP failed at round {rnd}: {res.message}")
        c = np.asarray(res.x)
        W = W_all(c, N)
        viol = np.nonzero(W[1:] < 1.0 - tol)[0] + 1
        rounds.append({"round": rnd, "cells": int(cells.size), "value_minus_psi": float(res.fun) - psiN, "violations": int(viol.size), "worst": float(W[1:].min())})
        print(f"   round {rnd:2d}: cells={cells.size:>7d} value-psi={float(res.fun)-psiN:12.3f} viol={viol.size:>7d} Wmin={W[1:].min():.4f}", flush=True)
        if viol.size == 0:
            break
        # Add the most violated cells.  When the violated set is huge (first
        # rounds at N >= 10^6) take a larger batch so the round count stays
        # small; the LP is dense (cells x y), so cap the batch by memory.
        this_batch = max(batch, min(viol.size // 4, 8 * y, 40000))
        order = np.argsort(W[viol])
        add = viol[order[:this_batch]]
        cells = np.unique(np.concatenate([cells, add]))
    else:
        raise RuntimeError("constraint generation did not converge")

    V = float(res.fun)
    W = W_all(c, N)
    d = np.nonzero(lam > 0)[0]
    excess_direct = float(np.dot(lam[d], W[N // d] - 1.0))
    mask = d <= r
    return {
        "N": N,
        "y": y,
        "V_star": V,
        "psi_N": psiN,
        "excess": V - psiN,
        "excess_direct": excess_direct,
        "excess_over_N": (V - psiN) / N,
        "excess_over_sqrtN": (V - psiN) / math.sqrt(N),
        "excess_from_d_le_sqrtN": float(np.dot(lam[d[mask]], W[N // d[mask]] - 1.0)),
        "excess_from_d_gt_sqrtN": float(np.dot(lam[d[~mask]], W[N // d[~mask]] - 1.0)),
        "W_min_all_cells": float(W[1:].min()),
        "W_max": float(W[1:].max()),
        "c_l1": float(np.abs(c).sum()),
        "c_nonzero": int(np.count_nonzero(np.abs(c) > 1e-9)),
        "mobius_prefix": int(next((k for k in range(y) if abs(c[k] - mobius_val(k + 1)) > 1e-6), y)),
        "c_head": [float(v) for v in c[:40]],
        "rounds": rounds,
        "seconds": time.time() - t0,
    }


def mobius_val(n: int) -> int:
    m, res, p = n, 1, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    if m > 1:
        res = -res
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--alpha", type=float, nargs="+", default=[0.5])
    ap.add_argument("--y", type=int, nargs="*", default=[])
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    results = []
    for N in args.N:
        ys = sorted(set([int(round(N**a)) for a in args.alpha] + list(args.y)))
        for y in ys:
            print(f"N={N} y={y} (N^{math.log(y)/math.log(N):.3f})", flush=True)
            out = solve(N, y)
            results.append(out)
            print(
                f"=> N={N:>9d} y={y:>6d}  excess={out['excess']:12.3f}  /N={out['excess_over_N']:.6f}  /sqrtN={out['excess_over_sqrtN']:8.3f}  "
                f"[d<=rtN: {out['excess_from_d_le_sqrtN']:.2f}, d>rtN: {out['excess_from_d_gt_sqrtN']:.2f}]  "
                f"|c|_1={out['c_l1']:.1f} nnz={out['c_nonzero']} mobius_prefix={out['mobius_prefix']} Wmin={out['W_min_all_cells']:.6f}  {out['seconds']:.1f}s",
                flush=True,
            )
            with open(args.output, "w") as fh:
                json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
