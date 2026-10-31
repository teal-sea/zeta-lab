"""Generate the 65-mode integer certificate at (c, N) = (1541/50, 64).

Produces hunts/weil_dh_line/Cert65.lean with the quadratic form of the signed
integer matrix B = L * A (L the common denominator of the dyadic midpoints) and
integer vector u = D * w, where w is the high-precision bottom eigenvector.
The theorem states the integer sum is negative; `norm_num` checks it.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from math import gcd

import mpmath as mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
NUM = os.path.join(ROOT, "hunts", "weil_propagation", "numerics")
WT = os.path.join(ROOT, "hunts", "rogue_frontier", "weil_trunc")
for _p in (NUM, WT, ROOT):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from flint import arb_mat, ctx  # noqa: E402

import wp_common as W  # noqa: E402
import enclosures as EN  # noqa: E402


def frac_of(x):
    m, e = x.mid().man_exp()
    return Fraction(int(m), 1) * Fraction(2) ** int(e)


def lcm(a, b):
    return a * b // gcd(a, b)


def main():
    prec = 256
    ctx.prec = prec
    c = Fraction(1541, 50)
    N = 64
    bt = EN.BallTruncation(W.cq(c), N, kind="dh", prec=prec)
    M = arb_mat(bt.even_matrix())
    n = M.nrows()
    A = [[frac_of(M[i, j]) for j in range(n)] for i in range(n)]

    L = 1
    for i in range(n):
        for j in range(n):
            L = lcm(L, A[i][j].denominator)
    B = [[int(A[i][j] * L) for j in range(n)] for i in range(n)]
    assert all(A[i][j] * L == B[i][j] for i in range(n) for j in range(n))

    mp.mp.dps = 120
    Am = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            Am[i, j] = mp.mpf(A[i][j].numerator) / A[i][j].denominator
    E, V = mp.eigsy(Am)
    kmin = min(range(n), key=lambda i: E[i])
    v = [V[i, kmin] for i in range(n)]
    D = 10 ** 40
    u = [int(mp.nint(x * D)) for x in v]

    total = sum(u[i] * u[j] * B[i][j] for i in range(n) for j in range(n))
    norm = sum(x * x for x in u)
    print(json.dumps({"n": n, "L_bits": L.bit_length(), "lambda_min": float(E[kmin]),
                      "uTw": float(Fraction(total, norm * L)), "total_negative": total < 0}))

    terms = []
    for i in range(n):
        for j in range(i, n):
            coef = B[i][j] if i == j else 2 * B[i][j]
            terms.append(f"({coef}) * ({u[i]}) * ({u[j]})")
    body = " + ".join(terms)

    lean = f'''/-
Kernel certificate for the band-64 even Davenport–Heilbronn form at window
c = 1541/50 (30.82), the cell where the form first turns negative.

The matrix entries are exact rational midpoints of Arb enclosures (radius below
1e-72) scaled by L = 2^{L.bit_length() - 1}; the vector is the bottom eigenvector
rounded at 40 decimal places. The theorem below states that the scaled integer
quadratic form is negative, which is equivalent to the rational Rayleigh
quotient being negative. The passage from the Arb enclosure to these integers is
cited, not formalized.
-/
import Mathlib.Tactic

namespace ZetaLab

/-- The scaled integer quadratic form is negative. -/
theorem cert65 : {body} < 0 := by
  norm_num
'''
    out = os.path.join(HERE, "Cert65.lean")
    with open(out, "w") as f:
        f.write(lean)
    print(json.dumps({"lean_path": out, "terms": len(terms), "bytes": os.path.getsize(out)}))
    json.dump({"n": n, "L_bits": L.bit_length(), "D": "1e40", "total": str(total),
               "norm": str(norm)}, open(os.path.join(HERE, "cert65_meta.json"), "w"), indent=1)


if __name__ == "__main__":
    main()