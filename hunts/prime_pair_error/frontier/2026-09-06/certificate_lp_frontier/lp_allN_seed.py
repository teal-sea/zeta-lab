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


def _coverage(a: np.ndarray, ds: np.ndarray, L: int, M: int, R: int):
    """Return (W on 1..R-1, g on R..R+L-1) for the seed a, by cumulative
    jumps: g(n) = sum_{m<=n} w(m), w(m) = sum_{d | m, d | L} a_d, and
    W(n) = sum_k g(floor(n / M^k)) since g is a step function with integer
    breakpoints."""
    top = R + L
    w = np.zeros(top + 1)
    for d, v in zip(ds, a):
        if v != 0.0:
            w[d::d] += v
    g = np.cumsum(w)
    n = np.arange(1, R)
    W = np.zeros(R - 1)
    k = 0
    while M**k < R:
        W += g[n // M**k]
        k += 1
    return W, g[R : R + L]


def solve_cg(L: int, M: int, R: int, batch: int = 20000, max_rounds: int = 60) -> dict:
    """Same LP as solve(), by constraint generation on both coverage sets."""
    ds = np.array(divisors(L))
    nd = ds.size
    obj = -(np.log(ds) / ds) * (M / (M - 1))
    rng = np.random.default_rng(0)
    cells_W = np.arange(1, min(R, 30000))
    cells_g = np.unique(np.concatenate([np.arange(R, R + min(L, 30000)), R + rng.integers(0, L, size=min(L, 30000))]))

    def rows_W(cells):
        A = np.zeros((cells.size, nd))
        for ci, d in enumerate(ds):
            k = 0
            while d * M**k < R:
                A[:, ci] += cells // (d * M**k)
                k += 1
        return A

    def rows_g(cells):
        return (cells[:, None] // ds[None, :]).astype(float)

    for rnd in range(max_rounds):
        A = np.vstack([rows_W(cells_W), rows_g(cells_g)])
        b = np.concatenate([np.ones(cells_W.size), np.zeros(cells_g.size)])
        res = linprog(obj, A_ub=-A, b_ub=-b, A_eq=(1.0 / ds)[None, :], b_eq=[0.0], bounds=(None, None), method="highs-ds")
        if res.status != 0:
            raise RuntimeError(f"round {rnd}: {res.message}")
        a = res.x
        W, g = _coverage(a, ds, L, M, R)
        vW = np.nonzero(W < 1 - 1e-9)[0] + 1
        vg = np.nonzero(g < -1e-9)[0] + R
        print(f"   round {rnd:2d}: W-cells={cells_W.size:>6d} g-cells={cells_g.size:>6d} C={float(res.fun):.8f} viol(W)={vW.size} viol(g)={vg.size}", flush=True)
        if vW.size == 0 and vg.size == 0:
            break
        if vW.size:
            cells_W = np.unique(np.concatenate([cells_W, vW[np.argsort(W[vW - 1])[:batch]]]))
        if vg.size:
            cells_g = np.unique(np.concatenate([cells_g, vg[np.argsort(g[vg - R])[:batch]]]))
    else:
        raise RuntimeError("constraint generation did not converge")
    C = float(res.fun)
    return {
        "L": L, "M": M, "R": R, "n_divisors": int(nd), "C": C, "C_minus_1": C - 1.0, "kappa_g": C * (M - 1) / M,
        "W_min_below_R": float(W.min()), "g_min_beyond_R": float(g.min()), "balance": float(np.dot(a, 1.0 / ds)),
        "a_l1": float(np.abs(a).sum()), "a_nonzero": int(np.count_nonzero(np.abs(a) > 1e-9)),
        "seed": {int(d): float(v) for d, v in zip(ds, a) if abs(v) > 1e-9}, "rounds": rnd + 1,
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
            r = solve_cg(L, M, args.R) if (args.R - 1 + L) * len(divisors(L)) > 2 * 10**7 else solve(L, M, args.R)
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
