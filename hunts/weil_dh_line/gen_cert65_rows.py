"""Superseded 2026-10-30 by gen_cert_lean.py (Cert65.lean, decide +kernel, built in CI).
Kept as the record of the 65-row norm_num file Cert65Rows.lean, never built in CI.

Row-wise certificate: 65 small theorems `row_i = literal`, plus one final
theorem combining the literal row sums. Avoids any 2145-term expression, so
elaboration stays cheap and each `norm_num` sees 65 terms.
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

    with mp.workdps(120):  # no global mpmath state (review, 2026-10-30)
        Am = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                Am[i, j] = mp.mpf(A[i][j].numerator) / A[i][j].denominator
        E, V = mp.eigsy(Am)
        kmin = min(range(n), key=lambda i: E[i])
        u = [int(mp.nint(V[i, kmin] * 10 ** 40)) for i in range(n)]

        rows = []
        for i in range(n):
            terms = " + ".join(f"({B[i][j]}) * ({u[j]})" for j in range(n))
            val = sum(B[i][j] * u[j] for j in range(n))
            rows.append((terms, val))

        total = sum(u[i] * rows[i][1] for i in range(n))
        assert total < 0

        thms = []
        for i, (terms, val) in enumerate(rows):
            thms.append(f"theorem row{i} : {terms} = ({val}) := by norm_num")
        # Final: sum of u_i * row_i is negative; each summand is the row value.
        final_terms = " + ".join(f"({u[i]}) * ({rows[i][1]})" for i in range(n))
        lean = f'''/-
Row-wise kernel certificate for the band-64 even Davenport–Heilbronn form at
window c = 1541/50 (30.82).

Entries are exact rational midpoints of Arb enclosures (radius below 1e-72),
scaled by L = 2^{L.bit_length() - 1}; the vector is the bottom eigenvector rounded
at 40 decimal places. Each row sum is checked by `norm_num` on 65 terms, and the
final theorem combines the row values. The passage from the Arb enclosure to
these integers is cited, not formalized.
-/
import Mathlib.Tactic

namespace ZetaLab

'''
    lean += "\n\n".join(thms)
    lean += f"\n\n/-- The scaled integer quadratic form is negative: the signed sum of the\nkernel-checked row values. -/\ntheorem cert65 : {final_terms} < 0 := by\n  norm_num\n"
    out = os.path.join(HERE, "Cert65Rows.lean")
    with open(out, "w") as f:
        f.write(lean)
    print(json.dumps({"lean_path": out, "bytes": os.path.getsize(out), "total": str(total)}))


if __name__ == "__main__":
    main()