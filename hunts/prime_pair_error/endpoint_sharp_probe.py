"""Finite checks for ENDPOINT_SHARP.md.

Compares two divisor approximants of the indicator 1_{(n,P(Z))=1} at equal
level D_0, for n <= N:

  Bonferroni  B_m(n)  = sum_{d|P, d|n, omega(d)<=m} mu(d),      D_0 = Z^m
  beta-sieve  L+(n)   = sum_{d|P, d|n, d in D+}   mu(d),        D_0 = Z^s

where D+ is Rosser's upper-bound support for the linear sieve (beta = 2):
d = p_1 ... p_r, p_1 > ... > p_r, and p_1 ... p_{l-1} p_l^3 < D_0 for every
odd l <= r.  The properties ENDPOINT_BOUND.md consumes are checked directly:
coefficients in {-1, 0, 1}, support below D_0, one-sidedness
L+(n) >= 1_{(n,P)=1}, and the l^1 error sum_n (L+(n) - 1_{(n,P)=1}) against
N V(Z) e^{-s}.  Nothing asymptotic is asserted.
"""
from __future__ import annotations

import itertools
import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent


def primes_below(z):
    return [p for p in range(2, z) if all(p % r for r in range(2, int(p ** 0.5) + 1))]


def rosser_upper_support(ps, D):
    """All squarefree d | P (product of ps) in Rosser's upper-bound support at level D."""
    ps_desc = sorted(ps, reverse=True)
    out = []

    def rec(start, prod, chain):
        # chain holds primes in decreasing order; check the odd-length conditions as we go
        l = len(chain)
        if l % 2 == 1:
            # condition at odd l: p_1...p_{l-1} p_l^3 < D
            if (prod // chain[-1]) * chain[-1] ** 3 >= D:
                return
        out.append((prod, chain[:]))
        for i in range(start, len(ps_desc)):
            p = ps_desc[i]
            if prod * p >= D:
                continue
            chain.append(p)
            rec(i + 1, prod * p, chain)
            chain.pop()

    rec(0, 1, [])
    return out


def main():
    N = 10 ** 6
    Z = 50
    ps = primes_below(Z)
    P = math.prod(ps)
    V = math.prod(1 - 1 / p for p in ps)
    H = sum(1 / p for p in ps)
    n = np.arange(N + 1)
    coprime = np.ones(N + 1, dtype=bool)
    for p in ps:
        coprime[p::p] = False
    coprime[0] = False
    true_count = int(coprime.sum())

    rows = []
    # beta-sieve at several levels
    for s in (2.0, 3.0, 4.0, 5.0, 6.0):
        D = Z ** s
        supp = rosser_upper_support(ps, D)
        Lp = np.zeros(N + 1, dtype=np.int64)
        for d, chain in supp:
            Lp[d::d] += (-1) ** len(chain)
        one_sided = bool(np.all(Lp[1:] >= coprime[1:].astype(np.int64)))
        err = int(np.sum(Lp[1:]) - true_count)
        rows.append({"approximant": "beta-sieve", "s": s, "D0": D, "support_size": len(supp),
                     "max_support": max(d for d, _ in supp), "coeffs_in_pm1": True,
                     "one_sided": one_sided, "l1_error": err,
                     "l1_error_over_NV": err / (N * V), "e_minus_s": math.exp(-s),
                     "ratio_error_to_NVe-s": err / (N * V * math.exp(-s))})
    # Bonferroni at m = 1..6 (D_0 = Z^m)
    for m in range(1, 7):
        Bm = np.zeros(N + 1, dtype=np.int64)
        cnt = 0
        for r in range(0, m + 1):
            for combo in itertools.combinations(ps, r):
                d = math.prod(combo)
                Bm[d::d] += (-1) ** r
                cnt += 1
        # error is one-sided only for even m; report signed and absolute
        diff = Bm[1:] - coprime[1:].astype(np.int64)
        rows.append({"approximant": "Bonferroni", "m": m, "D0": Z ** m, "support_size": cnt,
                     "one_sided": bool(np.all(diff >= 0)), "l1_error": int(np.sum(np.abs(diff))),
                     "l1_error_over_NV": float(np.sum(np.abs(diff)) / (N * V)),
                     "H_Z_e_over_m": H * math.e / m})
    out = {"N": N, "Z": Z, "primes": ps, "V_Z": V, "H_Z": H, "true_count": true_count, "rows": rows}
    (HERE / "results_endpoint_sharp_probe.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"N={N} Z={Z} #primes={len(ps)} V(Z)={V:.4f} H_Z={H:.3f} eH_Z={math.e*H:.2f} true count={true_count}")
    for r in rows:
        if r["approximant"] == "beta-sieve":
            print(f"beta  s={r['s']:.0f} D0=Z^s={r['D0']:.3g} |supp|={r['support_size']:5d} one_sided={r['one_sided']} "
                  f"l1err/NV={r['l1_error_over_NV']:.4f} e^-s={r['e_minus_s']:.4f} ratio={r['ratio_error_to_NVe-s']:.2f}")
        else:
            print(f"bonf  m={r['m']} D0=Z^m={r['D0']:.3g} |supp|={r['support_size']:5d} one_sided={r['one_sided']} "
                  f"l1err/NV={r['l1_error_over_NV']:.4f} eH/m={r['H_Z_e_over_m']:.2f}")


if __name__ == "__main__":
    main()
