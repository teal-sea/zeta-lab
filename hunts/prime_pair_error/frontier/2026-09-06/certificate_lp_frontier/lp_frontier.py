"""Exact-LP floor for factorial certificates of psi(N).

For support bound y and cutoff N the best factorial ceiling is

    V*(y,N) = min  sum_{j<=y} c_j log(floor(N/j)!)
              s.t. sum_{j<=y} c_j floor(n/j) >= 1   for n = 1..N.

Every seed/lift/carry/mask/repair construction in this hunt is a feasible
point of this LP (restricted to the j*15^k below N), so V*(y,N) - psi(N) is a
hard floor on the excess any such construction can reach at cutoff N with
support y.  We solve the sparse dual instead:

    max u_1   s.t. u_1 >= u_2 >= ... >= u_N >= 0,
                   sum_{m <= N/j} u_{j m} = log(floor(N/j)!)   (j = 1..y).

The true primes u_n = psi(N/n) are always dual-feasible, which is the
statement B(N) >= psi(N).  The primal certificate c is read off the equality
multipliers and re-verified directly.

Floating LP; this is a diagnostic, not an enclosure.  Nothing here is
rigorous beyond the re-verification of W_c >= 1 at every integer cell.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time

import numpy as np
import scipy.sparse as sp
from scipy.optimize import linprog


def mangoldt_psi_table(N: int) -> np.ndarray:
    """psi(x) for integer x in [0, N] via a sieve (exact in floats of logs)."""
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
    return np.cumsum(lam)


def log_factorial_table(N: int) -> np.ndarray:
    """log(m!) for m = 0..N, via cumulative log."""
    out = np.zeros(N + 1)
    out[1:] = np.cumsum(np.log(np.arange(1, N + 1, dtype=float)))
    return out


def solve(N: int, y: int, verbose: bool = False) -> dict:
    t0 = time.time()
    lf = log_factorial_table(N)
    L = np.array([lf[N // j] for j in range(1, y + 1)])  # log floor(N/j)!

    # Primal directly: min c.L  s.t.  sum_j c_j floor(n/j) >= 1 for n=1..N.
    # Dense N x y matrix; rows are the integer cells, columns the support.
    n = np.arange(1, N + 1)[:, None]
    j = np.arange(1, y + 1)[None, :]
    A = (n // j).astype(float)
    res = linprog(
        L,
        A_ub=-A,
        b_ub=-np.ones(N),
        bounds=(None, None),
        method="highs-ds",
        options={"disp": verbose},
    )
    if res.status != 0:
        raise RuntimeError(f"LP failed: {res.message}")

    V = float(res.fun)
    c = np.asarray(res.x)
    # Dual measure on the cells: nu_n = -marginal of row n (rows are -A c <= -1).
    nu_cells = -np.asarray(res.ineqlin.marginals)
    u = np.cumsum(nu_cells[::-1])[::-1]  # u_n = sum_{m>=n} nu_m
    del A

    # Direct re-verification of the certificate.
    W = np.zeros(N + 1)
    for j in range(1, y + 1):
        if c[j - 1] != 0.0:
            W[1:] += c[j - 1] * (np.arange(1, N + 1) // j)
    Wmin = float(W[1:].min())
    B = float(np.dot(c, L))

    psi_tab = mangoldt_psi_table(N)
    psiN = float(psi_tab[N])
    # The prime dual point u_n = psi(N/n): feasibility residual as a sanity check.
    u_prime = psi_tab[N // np.arange(1, N + 1)]
    # sum_{m<=N/j} psi(N/(jm)) must equal log floor(N/j)! for every j.
    resid_prime = max(abs(u_prime[j - 1 :: j].sum() - L[j - 1]) for j in range(1, y + 1))

    out = {
        "N": N,
        "y": y,
        "V_star": V,
        "psi_N": psiN,
        "gap_V_minus_psi": V - psiN,
        "gap_V_minus_N": V - N,
        "psi_minus_N": psiN - N,
        "B_from_c": B,
        "B_minus_V": B - V,
        "W_min_on_cells": Wmin,
        "c_l1": float(np.abs(c).sum()),
        "c_nonzero": int(np.count_nonzero(np.abs(c) > 1e-9)),
        "c_1": float(c[0]),
        "W_max": float(W[1:].max()),
        "W_at_N": float(W[N]),
        "prime_dual_residual": resid_prime,
        "u1_over_N": V / N,
        "seconds": time.time() - t0,
    }
    # Where does the optimal fake measure put mass, relative to the primes?
    nu = -np.diff(np.concatenate([u, [0.0]]))  # nu_n = u_n - u_{n+1}
    nu_prime = -np.diff(np.concatenate([u_prime, [0.0]]))
    # Mass in dyadic-ish bands of t = n (t = N/x, x the fake prime location).
    bands = []
    edges = [1, 2, 3, 5, 10, 30, 100, 300, 1000, 3000, 10000, 30000, 100000, 10**6, 10**7]
    for a, b in zip(edges, edges[1:]):
        if a > N:
            break
        sl = slice(a - 1, min(b, N + 1) - 1)
        bands.append({"t_lo": a, "t_hi": min(b, N + 1), "nu_opt": float(nu[sl].sum()), "nu_prime": float(nu_prime[sl].sum())})
    out["mass_bands"] = bands
    out["c_head"] = [float(v) for v in c[: min(40, y)]]
    return out, c, u


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, nargs="+", required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--verbose", action="store_true")
    args = ap.parse_args()
    results = []
    for y in args.y:
        out, c, u = solve(args.N, y, verbose=args.verbose)
        results.append(out)
        print(
            f"N={args.N:>8d} y={y:>6d}  V*-psi={out['gap_V_minus_psi']:14.3f}  "
            f"V*-N={out['gap_V_minus_N']:14.3f}  (V*-psi)/N={out['gap_V_minus_psi']/args.N:.6f}  "
            f"Wmin={out['W_min_on_cells']:.6f}  |c|_1={out['c_l1']:.2f}  nnz={out['c_nonzero']}  "
            f"B-V={out['B_minus_V']:.2e}  {out['seconds']:.1f}s",
            flush=True,
        )
    with open(args.output, "w") as fh:
        json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
