"""Step 0 for DESIGN-kernel-negative-cell: find the smallest band where the DH
form is negative at the cell's window endpoints.

Ball LDL^T inertia at c in {30.62, 30.82} for N in {8, 16, 24, 32}, even and odd
sectors. No claim is made here: this only locates the smallest matrix a rational
certificate could be built on.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
NUM = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (NUM, WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import arb, arb_mat, ctx  # noqa: E402

import enclosures as EN  # noqa: E402
import wp_common as W  # noqa: E402


def ldl_inertia(A):
    """LDL^T without pivoting in Arb: (n_neg, n_pos, n_undecided) or (None, None, k)."""
    n = len(A)
    a = [row[:] for row in A]
    piv = []
    for k in range(n):
        d = a[k][k]
        piv.append(d)
        if not (bool(d > 0) or bool(d < 0)):
            return None, None, n - k
        inv = 1 / d
        for i in range(k + 1, n):
            li = a[i][k] * inv
            ai = a[i]
            for j in range(k + 1, i + 1):
                ai[j] -= li * a[j][k]
    neg = sum(1 for d in piv if bool(d < 0))
    return neg, n - neg, 0


def rows_of(M: arb_mat):
    n = M.nrows()
    return [[M[i, j] for j in range(n)] for i in range(n)]


def main():
    prec = 256
    out = []
    for c_str in ("3062/100", "3082/100"):
        c = Fraction(c_str)
        for N in (40, 48, 56, 64, 80, 96):
            bt = EN.BallTruncation(W.cq(c), N, kind="dh", prec=prec)
            ctx.prec = prec
            for sector, M in (("even", arb_mat(bt.even_matrix())),
                              ("odd", arb_mat(bt.odd_matrix()))):
                neg, pos, und = ldl_inertia(rows_of(M))
                rec = {"c": c_str, "N": N, "sector": sector,
                       "neg": neg, "pos": pos, "undecided": und}
                out.append(rec)
                print(json.dumps(rec), flush=True)
    print(json.dumps({"n_records": len(out)}))


if __name__ == "__main__":
    main()