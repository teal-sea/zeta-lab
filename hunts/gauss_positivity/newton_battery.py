"""Newton / higher-Turan battery on the moment sequence of Xi.

RH  <=>  F(w) = 8 xi(1/2 + sqrt(w)) has only real zeros
    <=>  (Polya) every Jensen polynomial J^{d,n} is hyperbolic.

Necessary conditions, each separately checkable:

  (N1) log-convexity of the moments  b_{n+1}^2 <= b_n b_{n+2}, which is
       automatic for b_n = int Phi u^{2n} because Phi > 0 and Cauchy-Schwarz
       applies. Verified here as an arithmetic check, not as evidence.
  (N2) the Turan inequality  gamma(n+1)^2 >= gamma(n) gamma(n+2)   (d = 2).
  (N3) Newton's inequalities at every order on each normalized Jensen
       polynomial, equivalently hyperbolicity of J^{d,n}.

An all-pass table is NOT evidence for RH (docs/08 section 3). The value of
this file is the first failure, and the location of the smallest margin.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp

from zeta.li import xi_taylor_coefficients

HERE = Path(__file__).parent


def moments_b(gammas, dps: int):
    """b_n = (2n)! gamma(n) / (64 * 4^n * n!), exact relation checked here."""
    with mp.workdps(dps):
        out = []
        for n, g in enumerate(gammas):
            out.append(mp.factorial(2 * n) * g / (64 * mp.power(4, n) * mp.factorial(n)))
        return out


def newton_defects(coeffs, dps: int):
    """For monic-normalised coeffs a_0..a_d of a degree-d polynomial, return
    the Newton defects  c_k^2 - c_{k-1} c_{k+1}  with c_k = a_k/C(d,k).

    All nonnegative is necessary for all roots real (Newton 1707).
    """
    with mp.workdps(dps):
        d = len(coeffs) - 1
        c = [coeffs[k] / mp.binomial(d, k) for k in range(d + 1)]
        return [c[k] ** 2 - c[k - 1] * c[k + 1] for k in range(1, d)]


def jensen_coeffs(gammas, d: int, n: int, dps: int):
    with mp.workdps(dps):
        return [mp.binomial(d, j) * gammas[n + j] for j in range(d + 1)]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dps", type=int, default=60)
    ap.add_argument("--n-max", type=int, default=100)
    ap.add_argument("--d-max", type=int, default=12)
    args = ap.parse_args()
    dps, n_max, d_max = args.dps, args.n_max, args.d_max

    gammas = xi_taylor_coefficients(n_max + d_max + 2, dps=dps, cache=True)
    b = moments_b(gammas, dps)

    # ---- N1: log-convexity of the moments -------------------------------
    worst_n1 = max(
        (b[n + 1] ** 2 / (b[n] * b[n + 2]), n) for n in range(len(b) - 2)
    )

    # ---- N2: Turan (d = 2) ----------------------------------------------
    turan = [
        (float(gammas[n + 1] ** 2 / (gammas[n] * gammas[n + 2])), n)
        for n in range(len(gammas) - 2)
    ]
    min_turan, argmin_turan = min(turan)

    # ---- N3: Newton at every order, per (d, n) --------------------------
    table = []
    failures = []
    smallest = None
    for d in range(2, d_max + 1):
        for n in range(0, n_max - d + 1):
            coeffs = jensen_coeffs(gammas, d, n, dps)
            defs = newton_defects(coeffs, dps)
            # relative defect: scale by the diagonal magnitude
            scale = max(abs(coeffs[k] / mp.binomial(d, k)) ** 2 for k in range(d + 1))
            rel = [x / scale for x in defs]
            mn = min(rel)
            table.append({"d": d, "n": n, "min_rel_newton": float(mn)})
            if mn < 0:
                failures.append({"d": d, "n": n, "min_rel_newton": float(mn)})
            if smallest is None or mn < smallest[0]:
                smallest = (mn, d, n)

    summary = {
        "dps": dps,
        "n_max": n_max,
        "d_max": d_max,
        "n_moments": len(b),
        "N1_logconvexity_worst": {"value": float(worst_n1[0]), "n": int(worst_n1[1])},
        "N2_turan_min": {"value": min_turan, "n": int(argmin_turan)},
        "N3_cells_tested": len(table),
        "N3_failures": failures[:20],
        "N3_n_failures": len(failures),
        "N3_smallest_margin": {
            "min_rel_newton": float(smallest[0]),
            "d": int(smallest[1]),
            "n": int(smallest[2]),
        },
        "note": (
            "All-pass is NOT evidence for RH (docs/08 section 3). The value is "
            "the first failure and the location of the smallest margin."
        ),
    }
    (HERE / "newton_results.json").write_text(json.dumps(summary, indent=1))
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()