"""Exact all-N floor of the pure-seed lifted family.

The hunt's basic object: a balanced seed g(t) = sum_{d | L} a_d floor(t/d)
(period L), lifted by radix M, W(t) = sum_{k>=0} g(t/M^k).  The reviewed
coverage argument (ROUTE_ASSESSMENT.md, PR #199): if W(t) >= 1 for
1 <= t < R, g(t) >= 0 for t >= R and R >= M, then W >= 1 on all of [1, oo).
Both conditions are finite (g is L-periodic, both are step functions with
integer breakpoints), so the family's all-N leading constant

    C = (M/(M-1)) kappa(g),   kappa(g) = int_1^oo g(t) dt/t^2 = -sum_d a_d log d / d,

is an exact linear program in the a_d.  Its value is the floor for every
pure-seed construction with this (L, M, R): the period-2310 pilot, the
period-30030 structural step, and the seed part of everything after.

The carry, mask and repair corrections of the later packages are NOT in
this family (their denominators do not divide L and they act on the final
weight), so this floor does not bound those; it bounds the seed they start
from.  Floating LP, coefficients re-verified on every constrained cell.
"""
from __future__ import annotations

import argparse
import json
import math

import numpy as np
from scipy.optimize import linprog


def divisors(L: int) -> list[int]:
    ds = [d for d in range(1, int(math.isqrt(L)) + 1) if L % d == 0]
    ds += [L // d for d in ds if d * d != L]
    return sorted(ds)


def solve(L: int, M: int, R: int) -> dict:
    ds = np.array(divisors(L))
    nd = ds.size
    # Coverage below R: W(n) = sum_k g(n / M^k) >= 1, n = 1..R-1.
    n = np.arange(1, R)
    A1 = np.zeros((R - 1, nd))
    for ci, d in enumerate(ds):
        k = 0
        while d * M**k < R:
            A1[:, ci] += n // (d * M**k)
            k += 1
    # Nonnegativity beyond R over one full period: g(n) >= 0, n = R..R+L-1.
    n2 = np.arange(R, R + L)
    A2 = (n2[:, None] // ds[None, :]).astype(float)
    A = np.vstack([A1, A2])
    b = np.concatenate([np.ones(R - 1), np.zeros(L)])
    obj = -(np.log(ds) / ds) * (M / (M - 1))
    res = linprog(obj, A_ub=-A, b_ub=-b, A_eq=(1.0 / ds)[None, :], b_eq=[0.0], bounds=(None, None), method="highs-ds")
    if res.status != 0:
        raise RuntimeError(res.message)
    a = res.x
    C = float(res.fun)
    # Re-verify both coverage conditions directly.
    W = A1 @ a
    g = A2 @ a
    return {
        "L": L,
        "M": M,
        "R": R,
        "n_divisors": int(nd),
        "C": C,
        "C_minus_1": C - 1.0,
        "kappa_g": C * (M - 1) / M,
        "W_min_below_R": float(W.min()),
        "g_min_beyond_R": float(g.min()),
        "balance": float(np.dot(a, 1.0 / ds)),
        "a_l1": float(np.abs(a).sum()),
        "a_nonzero": int(np.count_nonzero(np.abs(a) > 1e-9)),
        "seed": {int(d): float(v) for d, v in zip(ds, a) if abs(v) > 1e-9},
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, nargs="+", required=True)
    ap.add_argument("--M", type=int, nargs="+", default=[15])
    ap.add_argument("--R", type=int, default=100000)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = []
    for L in args.L:
        for M in args.M:
            r = solve(L, M, args.R)
            out.append(r)
            print(
                f"L={L:>7} M={M:>3} R={args.R}: C = {r['C']:.10f}  (C-1 = {r['C_minus_1']:.6f})  divisors={r['n_divisors']} nnz={r['a_nonzero']} "
                f"|a|_1={r['a_l1']:.2f}  Wmin<R={r['W_min_below_R']:.6f}  gmin>=R={r['g_min_beyond_R']:.2e}  balance={r['balance']:.1e}",
                flush=True,
            )
            with open(args.output, "w") as fh:
                json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
