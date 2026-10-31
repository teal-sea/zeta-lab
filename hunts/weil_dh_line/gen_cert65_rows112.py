"""Reduced-precision row certificate: entries rounded to multiples of 2^-BITS.

Rounding perturbs each entry by at most 2^-BITS-1; with 65 modes the spectral
perturbation is below 65 * 2^-BITS. The cell margin is 4.84e-32, so BITS = 112
keeps a factor ~70. Smaller integers make the kernel check much cheaper.
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

BITS = 112


def frac_of(x):
    m, e = x.mid().man_exp()
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

    scale = 1 << BITS
    R = [[Fraction(round(A[i][j] * scale), scale) for j in range(n)] for i in range(n)]
    B = [[int(R[i][j] * scale) for j in range(n)] for i in range(n)]

    mp.mp.dps = 120
    Am = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            Am[i, j] = mp.mpf(A[i][j].numerator) / A[i][j].denominator
    E, V = mp.eigsy(Am)
    kmin = min(range(n), key=lambda i: E[i])
    u = [int(mp.nint(V[i, kmin] * 10 ** 40)) for i in range(n)]

    # exact check on the rounded matrix
    num = sum(u[i] * u[j] * B[i][j] for i in range(n) for j in range(n))
    den = sum(x * x for x in u)
    rq_rounded = Fraction(num, den * scale)
    pert = Fraction(n, 1) * Fraction(1, 2) ** (BITS + 1)
    print(json.dumps({"lambda_min": float(E[kmin]), "rq_rounded": float(rq_rounded),
                      "perturbation_bound": float(pert), "passes": rq_rounded + pert < 0,
                      "margin": float(-(rq_rounded + pert))}))
    assert rq_rounded + pert < 0

    rows = []
    for i in range(n):
        terms = " + ".join(f"({B[i][j]}) * ({u[j]})" for j in range(n))
        val = sum(B[i][j] * u[j] for j in range(n))
        rows.append((terms, val))
    total = sum(u[i] * rows[i][1] for i in range(n))
    assert total < 0

    thms = [f"theorem row{i} : {terms} = ({val}) := by norm_num"
            for i, (terms, val) in enumerate(rows)]
    final_terms = " + ".join(f"({u[i]}) * ({rows[i][1]})" for i in range(n))
    lean = f'''/-
Reduced-precision row certificate for the band-64 even Davenport–Heilbronn form
at window c = 1541/50 (30.82).

Entries are the Arb midpoints rounded to multiples of 2^-{BITS}; the rounding
perturbs the form by at most 65 * 2^-{BITS + 1} = {float(pert):.3e}, against a
measured margin of {float(-rq_rounded):.3e}. The vector is the bottom eigenvector
rounded at 40 decimal places. Each row sum is checked by `norm_num`, and the
final theorem sums the kernel-checked row values.
-/
import Mathlib.Tactic

namespace ZetaLab

'''
    lean += "\n\n".join(thms)
    lean += f"\n\n/-- The scaled integer quadratic form is negative. -/\ntheorem cert65 : {final_terms} < 0 := by\n  norm_num\n"
    out = os.path.join(HERE, "Cert65Rows112.lean")
    with open(out, "w") as f:
        f.write(lean)
    print(json.dumps({"lean_path": out, "bytes": os.path.getsize(out), "total": str(total)}))


if __name__ == "__main__":
    main()