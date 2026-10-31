"""Build a rational certificate for the DH negative cell.

Configuration found in step 0: kind=dh, even sector, N=64, c=1541/50 (30.82),
one negative pivot. This script extracts the exact rational midpoint matrix,
bounds the entry perturbation, finds a sparse rational direction, and checks
`w^T A w / w^T w + e < 0` in exact rational arithmetic.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
NUM = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (NUM, WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import arb_mat, ctx  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as W  # noqa: E402


def frac_of(x) -> Fraction:
    m, e = x.mid().man_exp()
    return Fraction(int(m), 1) * Fraction(2) ** int(e)


def rad_upper(x) -> Fraction:
    m, e = x.rad().man_exp()
    return Fraction(int(m), 1) * Fraction(2) ** int(e)


def main():
    prec = 256
    ctx.prec = prec
    c = Fraction(1541, 50)
    N = 64
    bt = EN.BallTruncation(W.cq(c), N, kind="dh", prec=prec)
    M = arb_mat(bt.even_matrix())
    n = M.nrows()
    A = [[frac_of(M[i, j]) for j in range(n)] for i in range(n)]
    asym = max(abs(A[i][j] - A[j][i]) for i in range(n) for j in range(n))
    e_rad = max(sum(rad_upper(M[i, j]) for j in range(n)) for i in range(n))
    with mp.workdps(120):  # no global mpmath state (review, 2026-10-30)
        Am = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Am[i, j] = mp.mpf(A[i][j].numerator) / A[i][j].denominator
        E, V = mp.eigsy(Am)
        lam = [E[i] for i in range(n)]
        print(json.dumps({"n": n, "asym": str(asym), "e_rad": float(e_rad),
                          "lambda_min": float(min(lam)), "lambda_max": float(max(lam))}))
        kmin = min(range(n), key=lambda i: E[i])
        v = [V[i, kmin] for i in range(n)]
        order = sorted(range(n), key=lambda i: -abs(v[i]))
        for k in (65, 40, 24, 16, 12, 8, 6, 4):
            idx = order[:k]
            u = [v[i] if i in set(idx) else mp.mpf(0) for i in range(n)]
            D = 10 ** 30
            wr = [Fraction(int(mp.nint(u[i] * D)), D) for i in range(n)]
            num = sum(wr[i] * wr[j] * A[i][j] for i in range(n) for j in range(n))
            den = sum(wr[i] * wr[i] for i in range(n))
            rq = num / den
            ok = rq + e_rad < 0
            print(json.dumps({"support": k, "rq": float(rq), "margin": float(-(rq + e_rad)),
                              "passes": ok}))
            if ok and k <= 16:
                break


if __name__ == "__main__":
    main()