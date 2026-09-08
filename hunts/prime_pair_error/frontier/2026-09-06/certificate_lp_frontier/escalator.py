"""The halving escalator, the archived 232-exchanges, and the source-exhaustion bound.

Control (coordinator): J = Fold(232) + 2 Fold(116) - Fold(102) decomposes the
archived exchange 232 -> 102.  Fold(232) deposits +2 at the empty intermediate
116 = floor(232/2); 2 Fold(116) consumes exactly those +2 (net 0 at 116) and
carries the mass down.  So the "escalator"

    S(a) = sum_{j >= 0, a_j > y} 2^j Fold(a_j),   a_0 = a, a_{j+1} = floor(a_j/2)

telescopes: every intermediate cell a_1, ..., a_{J-1} cancels, leaving

    S(a) = -e_a + 2^J e_{a_J} + sum_j 2^j kappa(a_j),   a_J = floor(a/2^J) <= y

(Lemma 11).  Canonicity (review, 2026-09-08): S(a) and -z_a have the same
coordinates above y (-1 at a, 0 elsewhere) and both have zero moments, so
their difference is prefix-supported with zero moments; the prefix rows are
unitriangular, hence S(a) = -z_a, and every zero-moment delta on Q_N has the
unique signed escalator expansion delta = -sum_{a>y} delta_a S(a).
`z_identity_check` verifies S(a) = -z_a exactly.

Source exhaustion (Lemma 12, corrected domain and formula).  Assume {1..y}
attainable, a attainable above y, and D a finite set of attainable cells above
y EXCLUDING a; weights theta_b >= 0, T = sum_b theta_b, absent theta zero.  In

    C = sum_{b in D} theta_b (S(a) - Fold(b))

the exact coordinate at a is

    C_a = -T - 2 (theta_{2a} + theta_{2a+1}),

because Fold(2a) and Fold(2a+1) deposit +2 at a = floor(b/2) and enter with the
sign of -theta_b (disjointness from the DESCENDING chain does not exclude the
two parent labels).  Feasibility m + C >= 0 gives T + 2(theta_{2a}+theta_{2a+1})
<= m_a, hence T <= m_a, and the always-valid bound is

    gain(C) = sum_b theta_b (G_S(a) - g(b)) <= m_a * max({0} union {G_S(a) - g(b) : b in D}),
    G_S(a) = sum_j 2^j g(a_j),

the 0 covering an empty D and a negative maximum (a = 103, D = {204}: G_S = 3,
g(204) = 4, all-zero weights are feasible with gain 0 <= 0).  This is an upper
capacity bound for the restricted source collection; it is not a lower bound
on T* - psi.  The feasible finite example supplies the lower bound 5 log 43.

Evidence label: gains and scales here are point-valued mpmath evaluations at
40 digits, serialized as floats; they are NOT interval enclosures.  Moments,
coordinates and telescoping are exact integer/rational checks.  The reviewer's
independent exact capacity inequalities (M_c >= 43^{-J_b(c)}, M_c^3 >= 43^{-C_c})
and Arb enclosure of the gain, [18.806000578467812, 18.806000578467813],
support the finite result; no enclosure is claimed by this file.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as Fr

import mpmath as mp

from dual_witness import build
from fold_family import fold_vectors
from prefix_witness import mobius_table, prefix_rates
from signed_fold import fold_measure


def _setup(N, y):
    cells, idx, A_mat, e, primes, ell = build(N, y)
    mu = mobius_table(y)
    mt = {}
    for p in primes:
        for i, cnt in e[p].items():
            mt.setdefault(int(cells[i]), {})[p] = cnt
    return set(int(c) for c in cells), mu, mt


def chain(a, y):
    out = [a]
    while a // 2 > 0:
        a //= 2
        out.append(a)
    return out


def escalator_coeffs(a, y):
    ch = chain(a, y)
    return {ch[j]: 2 ** j for j in range(len(ch)) if ch[j] > y}


def measure(coeffs, y, mu):
    D = {}
    for a, cf in coeffs.items():
        for c, v in fold_measure(a, y, mu).items():
            D[c] = D.get(c, Fr(0)) + cf * v
    return {c: v for c, v in D.items() if v}


def analyze(N, y, coeffs, dps=40):
    """Exact moments/coordinates; point-valued mpmath (not enclosure) scale and gain."""
    attain, mu, mt = _setup(N, y)
    g = lambda a: fold_vectors(a, y, mu)[1]
    D = measure(coeffs, y, mu)
    m0 = all(sum(v * (c // j) for c, v in D.items()) == 0 for j in range(1, y + 1))
    neg = {c: -v for c, v in D.items() if v < 0}
    walls = [c for c in neg if c not in mt]
    gu = sum(cf * g(a) for a, cf in coeffs.items())
    mp.mp.dps = dps
    Mp = lambda c: math.prod(p ** k for p, k in mt.get(c, {}).items())
    feas = m0 and not walls
    eps = min((mp.log(Mp(c)) / w for c, w in neg.items()), default=None) if feas and neg else None
    binding = min(neg, key=lambda c: float(mp.log(Mp(c)) / neg[c])) if feas and neg else None
    # an empty or withdrawal-free measure is feasible with gain 0 at any scale
    raw = 0.0 if (feas and not neg) else (None if eps is None else float(eps) * gu)
    total = None if raw is None else round(raw, 6)
    return {
        "moments_zero": m0, "gain_units": gu, "feasible": feas, "walls_drained": walls,
        "eps_star": None if eps is None else float(eps),
        "eps_binding": binding,
        "total_gain": total,
        "total_gain_raw": raw,
        "coord_at_source": {a: int(D.get(a, 0)) for a in coeffs if a > y},
        "evidence": "exact moments/coordinates; point-valued mpmath scale/gain (no enclosure)",
    }


def z_identity_check(N, y, a):
    """S(a) = -z_a exactly, z_a = e_a - sum_s r^{(a)}_s e_s (prefix rates)."""
    attain, mu, mt = _setup(N, y)
    S = measure(escalator_coeffs(a, y), y, mu)
    r = prefix_rates(a, y, mu)
    neg_z = {a: Fr(-1)}
    for s in range(1, y + 1):
        if r[s - 1]:
            neg_z[s] = neg_z.get(s, Fr(0)) + Fr(r[s - 1])
    neg_z = {c: v for c, v in neg_z.items() if v}
    return S == neg_z


def source_exhaustion(N, y, a, dests, weights=None, dps=40):
    """Lemma 12 on the collection sum_b theta_b (S(a) - Fold(b)), D excluding a.
    Returns the exact coordinate at a against the predicted -T - 2(theta_2a+theta_2a+1),
    the bound m_a * max({0} u {G_S - g(b)}), and the (point-valued) gain."""
    attain, mu, mt = _setup(N, y)
    if a in dests:
        raise ValueError("D must exclude a")
    g = lambda c: fold_vectors(c, y, mu)[1]
    S = escalator_coeffs(a, y)
    ch = chain(a, y)
    aJ = next(c for c in ch if c <= y)
    Smeas = measure(S, y, mu)
    inter = [c for c in ch if y < c < a]
    telescopes = all(c not in Smeas for c in inter)
    G_S = sum(cf * g(c) for c, cf in S.items())
    w = {b: (1 if weights is None else weights[b]) for b in dests}
    T = sum(w.values())
    predicted_coord = -T - 2 * (w.get(2 * a, 0) + w.get(2 * a + 1, 0))
    per = {}
    for b in dests:
        coeffs = dict(S)
        coeffs[b] = coeffs.get(b, 0) - 1
        per[b] = analyze(N, y, coeffs)
    coll = {}
    for c, cf in S.items():
        coll[c] = coll.get(c, 0) + T * cf
    for b in dests:
        coll[b] = coll.get(b, 0) - w[b]
    coll = {c: v for c, v in coll.items() if v}
    collres = analyze(N, y, coll) if coll else {"feasible": True, "total_gain": 0.0, "total_gain_raw": 0.0, "gain_units": 0, "moments_zero": True}
    mp.mp.dps = dps
    Mp = lambda c: math.prod(p ** k for p, k in mt.get(c, {}).items())
    m_a = float(mp.log(Mp(a))) if a in mt else 0.0
    H = max([0] + [G_S - g(b) for b in dests])
    bound = m_a * H
    gain = collres["total_gain"]
    gain_raw = collres["total_gain_raw"]
    # the bound applies to feasible collections; None when there is nothing to bound
    within = None if gain_raw is None else (gain_raw <= bound + 1e-9)
    return {
        "a": a, "m_a": m_a, "chain": ch, "aJ": aJ, "escalator": S,
        "telescopes": telescopes, "intermediate_cells": inter, "G_S": G_S,
        "weights": w, "T": T,
        "per_destination": per,
        "collection_coord_at_a": int(measure(coll, y, mu).get(a, 0)) if coll else 0,
        "predicted_coord_at_a": predicted_coord,
        "coord_formula_holds": (int(measure(coll, y, mu).get(a, 0)) if coll else 0) == predicted_coord,
        "collection_total_gain": gain,
        "collection_feasible": collres["feasible"],
        "H_max0": H,
        "exhaustion_bound_m_a_times_H": round(bound, 6),
        "gain_within_bound": within,
        "z_identity_S_eq_minus_z": z_identity_check(N, y, a),
        "evidence": "exact coordinates/moments; point-valued mpmath gain (no enclosure)",
    }


def regression_controls(N, y):
    """The reviewer's boundary controls."""
    r1 = source_exhaustion(N, y, 102, [204])                 # parent label: coord -3, not -1
    r2 = source_exhaustion(N, y, 103, [204], weights={204: 0})  # zero weights: gain 0 <= bound 0
    r3 = source_exhaustion(N, y, 232, [])                     # empty D: bound m_a*0, gain 0
    return {"a102_D204": r1, "a103_D204_zero_weights": r2, "a232_empty_D": r3}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=10000)
    ap.add_argument("--y", type=int, default=100)
    ap.add_argument("--a", type=int, default=232)
    ap.add_argument("--dests", type=int, nargs="+", default=[102, 123, 126])
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    J = analyze(args.N, args.y, {232: 1, 116: 2, 102: -1})
    print(f"control J = F232 + 2F116 - F102: feasible {J['feasible']}, gain {J['total_gain']} (point mpmath; archived step-1 gain 18.806)")
    r = source_exhaustion(args.N, args.y, args.a, args.dests)
    print(f"escalator S({args.a}): chain {r['chain']}, telescopes {r['telescopes']}, S(a) = -z_a: {r['z_identity_S_eq_minus_z']}, G_S = {r['G_S']}")
    for b, pr in r["per_destination"].items():
        print(f"  J_{b} = S - F{b}: feasible {pr['feasible']}, gain_units {pr['gain_units']}, eps* {pr['eps_star']:.4f} binds {pr['eps_binding']}, total {pr['total_gain']}")
    print(f"collection over {args.dests}: coord at {args.a} = {r['collection_coord_at_a']} (predicted {r['predicted_coord_at_a']}, holds {r['coord_formula_holds']}), gain {r['collection_total_gain']}, bound m_a*max({{0}} u ...) = {r['exhaustion_bound_m_a_times_H']}, within {r['gain_within_bound']}")
    rc = regression_controls(args.N, args.y)
    for k, v in rc.items():
        print(f"  control {k}: coord {v['collection_coord_at_a']} (predicted {v['predicted_coord_at_a']}), gain {v['collection_total_gain']}, bound {v['exhaustion_bound_m_a_times_H']}, within {v['gain_within_bound']}")
    zc = {a: z_identity_check(args.N, args.y, a) for a in (102, 103, 116, 123, 126, 204, 232)}
    print(f"S(a) = -z_a on the seven controls: {zc}")
    with open(args.output, "w") as fh:
        json.dump({"control_J": J, "source_exhaustion": r, "regression_controls": rc, "z_identity_controls": zc}, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
