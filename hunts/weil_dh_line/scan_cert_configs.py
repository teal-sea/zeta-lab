"""Scan window c at N=64 (even, DH) for the magnitude of the negative eigenvalue
and the smallest support that keeps a rational certificate passing.

Cheap: one mpmath eigensolve per c. Used to pick the configuration whose Lean
certificate is smallest.
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


def frac_of(x):
    m, e = x.mid().man_exp()
    return Fraction(int(m), 1) * Fraction(2) ** int(e)


def rad_upper(x):
    m, e = x.rad().man_exp()
    return Fraction(int(m), 1) * Fraction(2) ** int(e)


def one(c: Fraction, N: int = 64):
    prec = 256
    ctx.prec = prec
    bt = EN.BallTruncation(W.cq(c), N, kind="dh", prec=prec)
    M = arb_mat(bt.even_matrix())
    n = M.nrows()
    A = [[frac_of(M[i, j]) for j in range(n)] for i in range(n)]
    e_rad = max(sum(rad_upper(M[i, j]) for j in range(n)) for i in range(n))
    with mp.workdps(80):  # no global mpmath state (review, 2026-10-30)
        Am = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Am[i, j] = mp.mpf(A[i][j].numerator) / A[i][j].denominator
        E, V = mp.eigsy(Am)
        kmin = min(range(n), key=lambda i: E[i])
        lam = E[kmin]
        v = [V[i, kmin] for i in range(n)]
        order = sorted(range(n), key=lambda i: -abs(v[i]))
        best = None
        for k in (65, 48, 32, 24, 16, 12, 8):
            idx = set(order[:k])
            u = [v[i] if i in idx else mp.mpf(0) for i in range(n)]
            D = 10 ** 40
            wr = [Fraction(int(mp.nint(u[i] * D)), D) for i in range(n)]
            num = sum(wr[i] * wr[j] * A[i][j] for i in range(n) for j in range(n))
            den = sum(wr[i] * wr[i] for i in range(n))
            rq = num / den
            if rq + e_rad < 0:
                best = k
                break
        return {"c": str(c), "n": n, "lambda_min": float(lam),
                "e_rad": float(e_rad), "min_support_passing": best}


def main():
    out = []
    for c in (Fraction(1541, 50), Fraction(31), Fraction(32), Fraction(35),
              Fraction(40), Fraction(50)):
        rec = one(c)
        out.append(rec)
        print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()