"""Two dictionary variants of the all-cells LP, by constraint generation.

--lift M : the hunt's own family at finite N.  Seed a_j (j <= y) repeated at
           every radix-M scale: W(t) = sum_k sum_j a_j floor(t/(j M^k)),
           B(N) = sum_j a_j sum_k log floor(N/(j M^k))!.  Its floor at (y,N)
           bounds every seed/lift/carry/mask/repair construction whose seed
           lives below y.

--selberg : enlarge the dictionary by g_j(t) = log floor(t/j)! + log(N/t)
           floor(t/j).  Selberg's identity Lambda*log + Lambda log = mu*log^2
           gives sum_{d<=N} Lambda(d) g_j(N/d) = sum_{n<=N/j} log^2 n exactly,
           so these are admissible, exactly evaluable test functions.  The
           identity is re-checked numerically before use.

Floating LP, diagnostic grade; W >= 1 is re-verified on every cell.
"""
from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np
from scipy.optimize import linprog
from scipy.special import gammaln

from lp_allcells_cg import mangoldt


def build_columns(N: int, y: int, lift: int | None, selberg: bool):
    """Return (objective vector, function evaluating all columns on given cells,
    function evaluating W on all cells 1..N from a coefficient vector)."""
    j = np.arange(1, y + 1)
    cols = []  # each: (kind, j)
    obj = []
    if lift:
        for jj in j:
            val = 0.0
            k = 0
            while jj * lift**k <= N:
                val += gammaln(N // (jj * lift**k) + 1.0)
                k += 1
            obj.append(val)
            cols.append(("lift", int(jj)))
    else:
        for jj in j:
            obj.append(gammaln(N // jj + 1.0))
            cols.append(("floor", int(jj)))
    if selberg:
        logs = np.log(np.arange(1, N + 1, dtype=float))
        cum_log2 = np.cumsum(logs**2)
        for jj in j:
            obj.append(float(cum_log2[N // jj - 1]))
            cols.append(("selberg", int(jj)))

    def eval_cols(cells: np.ndarray) -> np.ndarray:
        # The Selberg columns carry log(N/t), which is not constant on the
        # cell [n, n+1).  W is affine in log(N/t) there, so imposing W >= 1
        # at both endpoints (t = n and t -> n+1) is exactly W >= 1 on the cell.
        # Without Selberg columns the two rows coincide and we keep one.
        nrow = 2 * cells.size if selberg else cells.size
        A = np.zeros((nrow, len(cols)))
        t_lo = cells.astype(float)
        t_hi = cells.astype(float) + 1.0
        for ci, (kind, jj) in enumerate(cols):
            if kind == "floor":
                col = cells // jj
            elif kind == "lift":
                col = np.zeros(cells.size)
                k = 0
                while jj * lift**k <= N:
                    col = col + cells // (jj * lift**k)
                    k += 1
            else:
                m = cells // jj
                A[: cells.size, ci] = gammaln(m + 1.0) + np.log(N / t_lo) * m
                A[cells.size :, ci] = gammaln(m + 1.0) + np.log(N / t_hi) * m
                continue
            A[: cells.size, ci] = col
            if selberg:
                A[cells.size :, ci] = col
        return A

    def W_all(x: np.ndarray) -> np.ndarray:
        """Minimum of W over each cell [n, n+1), n = 1..N (index n)."""
        cells = np.arange(1, N + 1)
        W = np.zeros(N + 1)
        S = np.zeros(N + 1)  # coefficient of log(N/t) on each cell
        for ci, (kind, jj) in enumerate(cols):
            if abs(x[ci]) < 1e-14:
                continue
            if kind == "floor":
                W[1:] += x[ci] * (cells // jj)
            elif kind == "lift":
                k = 0
                while jj * lift**k <= N:
                    W[1:] += x[ci] * (cells // (jj * lift**k))
                    k += 1
            else:
                m = cells // jj
                W[1:] += x[ci] * gammaln(m + 1.0)
                S[1:] += x[ci] * m
        t = cells.astype(float)
        W[1:] += np.minimum(S[1:] * np.log(N / t), S[1:] * np.log(N / (t + 1.0)))
        return W

    return np.array(obj), eval_cols, W_all, cols


def check_selberg_identity(N: int) -> float:
    lam = mangoldt(N)
    d = np.nonzero(lam > 0)[0]
    lhs = float(np.sum(lam[d] * (gammaln(N // d + 1.0) + np.log(d) * (N // d))))
    rhs = float(np.sum(np.log(np.arange(1, N + 1, dtype=float)) ** 2))
    return lhs - rhs


def solve(N: int, y: int, lift: int | None, selberg: bool, batch: int = 3000, tol: float = 1e-7) -> dict:
    t0 = time.time()
    lam = mangoldt(N)
    psiN = float(lam.sum())
    r = int(math.isqrt(N))
    obj, eval_cols, W_all, cols = build_columns(N, y, lift, selberg)
    d_small = np.nonzero(lam[: r + 1] > 0)[0]
    cells = np.unique(np.concatenate([np.arange(1, min(N, 4 * y) + 1), N // d_small]))
    for rnd in range(80):
        A = eval_cols(cells)
        res = linprog(obj, A_ub=-A, b_ub=-np.ones(A.shape[0]), bounds=(None, None), method="highs-ds")
        if res.status != 0:
            raise RuntimeError(f"LP failed at round {rnd}: {res.message}")
        x = np.asarray(res.x)
        W = W_all(x)
        viol = np.nonzero(W[1:] < 1.0 - tol)[0] + 1
        print(f"   round {rnd:2d}: cells={cells.size:>7d} value-psi={float(res.fun)-psiN:12.3f} viol={viol.size:>7d}", flush=True)
        if viol.size == 0:
            break
        cells = np.unique(np.concatenate([cells, viol[np.argsort(W[viol])[:batch]]]))
    else:
        raise RuntimeError("no convergence")
    V = float(res.fun)
    d = np.nonzero(lam > 0)[0]
    excess_direct = float(np.dot(lam[d], W[N // d] - 1.0))
    return {
        "N": N,
        "y": y,
        "lift": lift,
        "selberg": selberg,
        "excess": V - psiN,
        "excess_direct": excess_direct,
        "excess_over_N": (V - psiN) / N,
        "excess_over_sqrtN": (V - psiN) / math.sqrt(N),
        "W_min_all_cells": float(W[1:].min()),
        "x_l1": float(np.abs(x).sum()),
        "x_nonzero": int(np.count_nonzero(np.abs(x) > 1e-9)),
        "selberg_mass": float(np.sum(np.abs(x[[i for i, c in enumerate(cols) if c[0] == "selberg"]]))) if selberg else 0.0,
        "x_head": [float(v) for v in x[:30]],
        "seconds": time.time() - t0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--y", type=int, nargs="+", required=True)
    ap.add_argument("--lift", type=int, default=None)
    ap.add_argument("--selberg", action="store_true")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    results = []
    for N in args.N:
        if args.selberg:
            print(f"Selberg identity residual at N={N}: {check_selberg_identity(N):.3e}", flush=True)
        for y in args.y:
            print(f"N={N} y={y} lift={args.lift} selberg={args.selberg}", flush=True)
            out = solve(N, y, args.lift, args.selberg)
            results.append(out)
            print(
                f"=> N={N:>8d} y={y:>5d} lift={args.lift} selberg={args.selberg}  excess={out['excess']:11.3f}  /N={out['excess_over_N']:.6f}  "
                f"/sqrtN={out['excess_over_sqrtN']:7.3f}  |x|_1={out['x_l1']:.1f} nnz={out['x_nonzero']} selberg_mass={out['selberg_mass']:.3g} "
                f"Wmin={out['W_min_all_cells']:.6f} chk={out['excess']-out['excess_direct']:.1e}  {out['seconds']:.1f}s",
                flush=True,
            )
            with open(args.output, "w") as fh:
                json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
