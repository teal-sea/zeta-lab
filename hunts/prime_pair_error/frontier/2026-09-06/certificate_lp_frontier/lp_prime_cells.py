"""The relaxed floor: majorize only where the primes look.

B(N) - psi(N) = sum_{d<=N} Lambda(d) [W(N/d) - 1] involves W only at the cells
floor(N/d) with d a prime power.  For d > sqrt(N) those cells are (a subset
of) all n < sqrt(N); for d <= sqrt(N) they are the ~2 sqrt(N)/log N cells
floor(N/d).  So the honest constraint set is

    S(N) = {1..floor(sqrt N)}  U  {floor(N/d) : d <= sqrt N, Lambda(d) > 0},

about 1.2 sqrt(N) cells instead of N.  The LP

    P*(y,N) = min sum_{j<=y} c_j log floor(N/j)!   s.t.  W_c(n) >= 1, n in S(N)

is a valid ceiling for psi(N) (it uses the primes below sqrt N as input) and
a hard lower bound for every all-cell certificate, prime-aware or not.
Its excess P* - psi(N) is the true prime-weighted cost of support y at N.

Floating LP.  The certificate is re-verified at every prime-power cell and the
excess is recomputed directly from Lambda.  Diagnostic grade only.
"""
from __future__ import annotations

import argparse
import json
import math
import time

import numpy as np
from scipy.optimize import linprog


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


def log_factorial(m: np.ndarray) -> np.ndarray:
    from scipy.special import gammaln

    return gammaln(m.astype(float) + 1.0)


def solve(N: int, y: int, all_cells_below: int | None = None) -> dict:
    t0 = time.time()
    lam = mangoldt(N)
    psiN = float(lam.sum())
    r = int(math.isqrt(N))
    if all_cells_below is None:
        all_cells_below = r
    small = np.arange(1, all_cells_below + 1)
    d_small = np.nonzero(lam[: r + 1] > 0)[0]
    upper = N // d_small
    cells = np.unique(np.concatenate([small, upper]))
    cells = cells[cells <= N]

    j = np.arange(1, y + 1)
    L = log_factorial(N // j)
    A = (cells[:, None] // j[None, :]).astype(float)
    res = linprog(L, A_ub=-A, b_ub=-np.ones(cells.size), bounds=(None, None), method="highs-ds")
    if res.status != 0:
        raise RuntimeError(f"LP failed: {res.message}")
    c = np.asarray(res.x)
    V = float(res.fun)

    # Direct recomputation of the excess from Lambda over ALL prime powers.
    d = np.nonzero(lam > 0)[0]
    Wd = np.zeros(d.size)
    for jj in range(y):
        if c[jj] != 0.0:
            Wd += c[jj] * ((N // d) // (jj + 1))
    excess_direct = float(np.dot(lam[d], Wd - 1.0))
    Wmin_prime = float(Wd.min())
    # Where the excess sits: d <= sqrt N (sparse upper cells) vs d > sqrt N.
    mask_small_d = d <= r
    ex_upper = float(np.dot(lam[d[mask_small_d]], Wd[mask_small_d] - 1.0))
    ex_lower = float(np.dot(lam[d[~mask_small_d]], Wd[~mask_small_d] - 1.0))
    # Largest single contributions.
    contrib = lam[d] * (Wd - 1.0)
    top = np.argsort(-contrib)[:8]
    top_list = [{"d": int(d[i]), "N_over_d": int(N // d[i]), "W": float(Wd[i]), "contrib": float(contrib[i])} for i in top if contrib[i] > 1e-9]

    return {
        "N": N,
        "y": y,
        "n_cells": int(cells.size),
        "P_star": V,
        "psi_N": psiN,
        "excess": V - psiN,
        "excess_direct": excess_direct,
        "excess_over_N": (V - psiN) / N,
        "excess_over_sqrtN": (V - psiN) / math.sqrt(N),
        "excess_from_d_le_sqrtN": ex_upper,
        "excess_from_d_gt_sqrtN": ex_lower,
        "W_min_at_prime_cells": Wmin_prime,
        "c_l1": float(np.abs(c).sum()),
        "c_nonzero": int(np.count_nonzero(np.abs(c) > 1e-9)),
        "c_head": [float(v) for v in c[: min(30, y)]],
        "top_contributions": top_list,
        "seconds": time.time() - t0,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, nargs="+", required=True)
    ap.add_argument("--alpha", type=float, nargs="*", default=[], help="add y = round(N^alpha) for each alpha")
    ap.add_argument("--y", type=int, nargs="*", default=[])
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    if not args.alpha and not args.y:
        ap.error("give --y and/or --alpha (no default)")
    results = []
    for N in args.N:
        ys = sorted(set([int(round(N**a)) for a in args.alpha] + list(args.y)))
        for y in ys:
            out = solve(N, y)
            results.append(out)
            print(
                f"N={N:>9d} y={y:>6d} (N^{math.log(y)/math.log(N):.3f}) cells={out['n_cells']:>6d}  "
                f"excess={out['excess']:12.3f}  /N={out['excess_over_N']:.6f}  /sqrtN={out['excess_over_sqrtN']:8.3f}  "
                f"[d<=rtN: {out['excess_from_d_le_sqrtN']:.2f}, d>rtN: {out['excess_from_d_gt_sqrtN']:.2f}]  "
                f"|c|_1={out['c_l1']:.1f} nnz={out['c_nonzero']}  chk={out['excess']-out['excess_direct']:.1e}  {out['seconds']:.1f}s",
                flush=True,
            )
            with open(args.output, "w") as fh:
                json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
