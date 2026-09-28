"""The h-decomposition of the signed witness, and the confluence triple.

Codex's upper certificate is beta_q = B_q/1387 (B given in DUAL_WITNESS.md
Section 12).  With g_a = sum_q Fold(a)_q and

    h_a = -g_a - (F^T beta)_a = -g_a - sum_q Fold(a)_q beta_q,

the reduced-cost identity holds for EVERY signed x with nu = m + Fx >= 0:

    g^T x = beta^T m + sum_a h_a (-x_a)_+ - sum_a h_a (x_a)_+ - beta^T nu.

(Proof: (F^T beta)_a = -g_a - h_a, so beta^T Fx = -g^T x - sum h_a x_a, and
beta^T nu = beta^T m + beta^T Fx.)  Hence for any feasible x,

    g^T x <= beta^T m + sum_{x_a < 0} h_a |x_a|,

so the upper-bound base beta^T m and the h-weighted negative mass bound the whole
signed family.  `h_decomposition` computes h, checks h >= 0, and verifies the
identity on the saved 132.729535 witness.

The confluence triple at an even zero-mass cell b (k = b/2):

    C(b) = Fold(2b) + Fold(2k+1) - Fold(b),

sources the double 2b and the odd twin 2k+1, deposits at b.  Zero moments by
Lemma 7.  It is a feasible dual witness iff no zero-mass cell is net-withdrawn,
with scale eps* = min_{C(b)_c < 0} m_c/(-C(b)_c) and gain eps*(g(2b)+g(2k+1)-g(b)).
`confluence` checks the integer moments and absence of zero-mass withdrawals
exactly. Scales and gains use point-valued mpmath evaluations and float output,
not interval enclosures.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as Fr

import mpmath as mp

from dual_witness import build, _preserve_precision
from fold_family import fold_vectors
from prefix_witness import mobius_table
from signed_fold import fold_measure, witness_delta

B = {33: 6363, 34: 1248, 43: 754, 45: 5139, 49: 2494, 50: 1673, 52: 2635, 53: 4447, 54: 6649,
     62: 2488, 69: 109, 73: 5467, 79: 4875, 83: 6905, 87: 2281, 89: 6123, 90: 2242, 92: 2349,
     101: 1387, 104: 8, 105: 147, 106: 572, 107: 1959, 108: 4161, 109: 5548, 113: 286, 114: 1673,
     116: 286, 117: 286, 158: 2248, 166: 6619, 169: 1101, 175: 1180, 178: 2248, 181: 1141,
     192: 286, 196: 1673, 204: 3052, 238: 1962, 250: 6090, 263: 2021, 277: 3627, 285: 6935,
     294: 2028, 303: 182, 384: 433, 434: 7629, 476: 5490, 500: 10128, 666: 1417, 833: 6472, 1250: 16456}


def _mass_terms(cells, e, primes):
    mt = {}
    for p in primes:
        for i, cnt in e[p].items():
            mt.setdefault(int(cells[i]), {})[p] = cnt
    return mt


@_preserve_precision
def h_decomposition(N: int, y: int, witness_path: str, dps: int = 50) -> dict:
    cells, idx, A_mat, e, primes, ell = build(N, y)
    mu = mobius_table(y)
    mt = _mass_terms(cells, e, primes)
    above = [int(c) for c in cells if int(c) > y]
    g = {a: fold_vectors(a, y, mu)[1] for a in above}
    beta = {q: Fr(v, 1387) for q, v in B.items()}
    h = {}
    for a in above:
        fb = sum(beta.get(c, Fr(0)) * v for c, v in fold_measure(a, y, mu).items())
        h[a] = -g[a] - fb
    h_nonneg = all(v >= 0 for v in h.values())

    delta = witness_delta(N, y, witness_path)
    x = {}
    for a in sorted(above, reverse=True):
        x[a] = 2 * x.get(2 * a, Fr(0)) + 2 * x.get(2 * a + 1, Fr(0)) - delta.get(a, Fr(0))
    x = {a: v for a, v in x.items() if v}

    mp.mp.dps = dps

    def L(c):
        return sum(mp.log(p) * k for p, k in mt.get(c, {}).items()) if c in mt else mp.mpf(0)

    betaTm = mp.fsum(float(beta[q]) * L(q) for q in beta)
    nu = {}
    for a in x:
        for c, v in fold_measure(a, y, mu).items():
            nu[c] = nu.get(c, Fr(0)) + x[a] * v
    betaTnu = mp.fsum(float(beta[q]) * (L(q) + float(nu.get(q, Fr(0)))) for q in beta)
    sum_h_neg = mp.fsum(float(h[a]) * float(-x[a]) for a in x if x[a] < 0)
    sum_h_pos = mp.fsum(float(h[a]) * float(x[a]) for a in x if x[a] > 0)
    gain = float(sum(x[a] * g[a] for a in x))
    rhs = float(betaTm + sum_h_neg - sum_h_pos - betaTnu)
    neg = [a for a in x if x[a] < 0]
    weighted = sorted(((float(h[a] * (-x[a])), a) for a in neg), reverse=True)
    return {
        "h_nonneg": h_nonneg,
        "beta_T_m": float(betaTm),
        "sum_h_negpart": float(sum_h_neg),
        "sum_h_pospart": float(sum_h_pos),
        "beta_T_nu": float(betaTnu),
        "identity_rhs": rhs,
        "witness_gain": gain,
        "identity_holds": abs(rhs - gain) < 1e-6,
        "negatives_h_zero": sorted(a for a in neg if h[a] == 0),
        "negatives_h_pos": sorted(a for a in neg if h[a] > 0),
        "top_weighted": [(round(w, 4), a) for w, a in weighted[:6]],
        "excess_over_base": gain - float(betaTm),
    }


@_preserve_precision
def confluence(N: int, y: int, b: int, dps: int = 40) -> dict:
    cells, idx, A_mat, e, primes, ell = build(N, y)
    mu = mobius_table(y)
    mt = _mass_terms(cells, e, primes)
    attain = set(int(c) for c in cells)
    k = b // 2
    dbl, tw = 2 * b, 2 * k + 1
    if dbl not in attain or tw not in attain:
        return {"b": b, "feasible": False, "reason": "double or twin not attainable"}
    coeffs = {dbl: 1, tw: 1, b: -1}
    D = {}
    for a, cf in coeffs.items():
        for c, v in fold_measure(a, y, mu).items():
            D[c] = D.get(c, Fr(0)) + cf * v
    D = {c: v for c, v in D.items() if v}
    m0 = all(sum(v * (c // j) for c, v in D.items()) == 0 for j in range(1, y + 1))
    g = lambda a: fold_vectors(a, y, mu)[1]
    neg = {c: -v for c, v in D.items() if v < 0}
    walls = [c for c in neg if c not in mt]
    gu = g(dbl) + g(tw) - g(b)
    feasible = m0 and not walls
    mp.mp.dps = dps
    Mp = lambda c: math.prod(p ** kk for p, kk in mt.get(c, {}).items())
    eps = min((mp.log(Mp(c)) / w for c, w in neg.items()), default=None) if feasible and neg else None
    return {
        "b": b, "double": dbl, "twin": tw, "prefix_k": k,
        "moments_zero": m0, "feasible": feasible, "walls_drained": walls,
        "gain_units": gu, "eps_star": None if eps is None else float(eps),
        "eps_binding": None if eps is None else min(neg, key=lambda c: float(mp.log(Mp(c)) / neg[c])),
        "total_gain": None if eps is None else round(float(eps) * gu, 6),
        "double_has_mass": dbl in mt, "twin_has_mass": tw in mt,
        "withdrawn_cells": {int(c): int(w) for c, w in sorted(neg.items())},
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=10000)
    ap.add_argument("--y", type=int, default=100)
    ap.add_argument("--witness", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = {"h_decomposition": h_decomposition(args.N, args.y, args.witness)}
    hd = out["h_decomposition"]
    print(f"h-decomposition: h>=0 {hd['h_nonneg']}, identity holds {hd['identity_holds']}")
    print(f"  gain {hd['witness_gain']:.6f} = beta^T m {hd['beta_T_m']:.6f} + sum h(-x)+ {hd['sum_h_negpart']:.6f} - sum h(x)+ {hd['sum_h_pospart']:.6f} - beta^T nu {hd['beta_T_nu']:.6f}")
    print(f"  excess over upper-bound base = {hd['excess_over_base']:.6f}; h=0 negatives {hd['negatives_h_zero']}; top weighted {hd['top_weighted']}")
    # confluence at the even zero-mass cells
    cells, idx, A_mat, e, primes, ell = build(args.N, args.y)
    mt = _mass_terms(cells, e, primes)
    zero_even = [int(c) for c in cells if int(c) > args.y and int(c) % 2 == 0 and int(c) not in mt]
    out["confluence"] = {}
    print("confluence C(b) = Fold(2b) + Fold(2k+1) - Fold(b):")
    for b in zero_even:
        r = confluence(args.N, args.y, b)
        out["confluence"][b] = r
        if r.get("feasible"):
            print(f"  b={b}: double {r['double']} twin {r['twin']}, gain_units {r['gain_units']}, eps* {r['eps_star']:.4f} (binds {r['eps_binding']}), total {r['total_gain']}")
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
