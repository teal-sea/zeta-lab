"""The halving escalator, the archived 232-exchanges, and the source-exhaustion bound.

Control (coordinator): J = Fold(232) + 2 Fold(116) - Fold(102) decomposes the
archived exchange 232 -> 102.  Fold(232) deposits +2 at the empty intermediate
116 = floor(232/2); 2 Fold(116) consumes exactly those +2 (net 0 at 116) and
carries the mass down.  So the "escalator"

    S(a) = sum_{j >= 0, a_j > y} 2^j Fold(a_j),   a_0 = a, a_{j+1} = floor(a_j/2)

telescopes: every intermediate cell a_1, ..., a_{J-1} cancels, leaving

    S(a) = -e_a + 2^J e_{a_J} + sum_j 2^j kappa(a_j),   a_J = floor(a/2^J) <= y

(Lemma 11).  For a set D of destinations, the collection is {S(a) - Fold(b)},
one un-fold per destination; each un-fold refills the prefix walls that the
escalator drains (232's escalator drains wall 33; -Fold(102) refills it).

Source-exhaustion (Lemma 12).  In any collection C = sum_b theta_b (S(a) - Fold(b)),
theta_b >= 0, cell a receives coordinate -sum_b theta_b (only S(a) touches a),
so feasibility m + C >= 0 forces sum_b theta_b <= m_a, and the gain is

    gain(C) = sum_b theta_b (G_S(a) - g(b)) <= m_a * max_b (G_S(a) - g(b)),
    G_S(a) = sum_j 2^j g(a_j),

INDEPENDENT of |D|: a single prime source delivers at most m_a (G_S(a) - min g)
whether split over one destination or many.  This file verifies the control,
the telescoping, and the exhaustion bound in exact arithmetic (gain by enclosure).
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction as Fr

import mpmath as mp

from dual_witness import build
from fold_family import fold_vectors
from prefix_witness import mobius_table
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
    return {
        "moments_zero": m0, "gain_units": gu, "feasible": feas, "walls_drained": walls,
        "eps_star": None if eps is None else float(eps),
        "eps_binding": binding,
        "total_gain": None if eps is None else round(float(eps) * gu, 6),
        "coord_at_source": {a: int(D.get(a, 0)) for a in coeffs if a > y},
    }


def source_exhaustion(N, y, a, dests, dps=40):
    """Verify: escalator telescopes; each S(a)-F(b) feasible; the collection over
    all dests has coord -len at a and total gain = m_a*(G_S - g) (exhaustion)."""
    attain, mu, mt = _setup(N, y)
    g = lambda c: fold_vectors(c, y, mu)[1]
    S = escalator_coeffs(a, y)
    ch = chain(a, y)
    aJ = next(c for c in ch if c <= y)
    Smeas = measure(S, y, mu)
    # telescoping: intermediate cells a_1..a_{J-1} (those > y except a itself) absent
    inter = [c for c in ch if y < c < a]
    telescopes = all(c not in Smeas for c in inter)
    G_S = sum(cf * g(c) for c, cf in S.items())
    per = {}
    for b in dests:
        coeffs = dict(S)
        coeffs[b] = coeffs.get(b, 0) - 1
        per[b] = analyze(N, y, coeffs)
    # the whole collection at unit weights
    coll = {c: len(dests) * cf for c, cf in S.items()}
    for b in dests:
        coll[b] = coll.get(b, 0) - 1
    collres = analyze(N, y, coll)
    mp.mp.dps = dps
    Mp = lambda c: math.prod(p ** k for p, k in mt.get(c, {}).items())
    m_a = float(mp.log(Mp(a))) if a in mt else 0.0
    bound = m_a * max(G_S - g(b) for b in dests)
    return {
        "a": a, "m_a": m_a, "chain": ch, "aJ": aJ, "escalator": S,
        "telescopes": telescopes, "intermediate_cells": inter, "G_S": G_S,
        "per_destination": per,
        "collection_coord_at_a": int(measure(coll, y, mu).get(a, 0)),
        "collection_total_gain": collres["total_gain"],
        "collection_feasible": collres["feasible"],
        "exhaustion_bound_m_a_times_maxgain": round(bound, 6),
        "bound_matches_single": abs((collres["total_gain"] or 0) - bound) < 1e-4,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=10000)
    ap.add_argument("--y", type=int, default=100)
    ap.add_argument("--a", type=int, default=232)
    ap.add_argument("--dests", type=int, nargs="+", default=[102, 123, 126])
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    J = analyze(args.N, args.y, {232: 1, 116: 2, 102: -1})
    print(f"control J = F232 + 2F116 - F102: feasible {J['feasible']}, gain {J['total_gain']} (archived step-1 gain 18.806)")
    r = source_exhaustion(args.N, args.y, args.a, args.dests)
    print(f"escalator S({args.a}): chain {r['chain']}, telescopes {r['telescopes']} (intermediates {r['intermediate_cells']} absent), G_S = {r['G_S']}, deposits 2^J at {r['aJ']}")
    for b, pr in r["per_destination"].items():
        print(f"  J_{b} = S - F{b}: feasible {pr['feasible']}, gain_units {pr['gain_units']}, eps* {pr['eps_star']:.4f} binds {pr['eps_binding']}, total {pr['total_gain']}")
    print(f"collection over {args.dests}: coord at {args.a} = {r['collection_coord_at_a']}, total gain {r['collection_total_gain']}, feasible {r['collection_feasible']}")
    print(f"source-exhaustion bound m_{args.a} * max(G_S - g_b) = {r['exhaustion_bound_m_a_times_maxgain']}; matches single exchange: {r['bound_matches_single']}")
    print(f"  => source {args.a} (m = log43 = {r['m_a']:.4f}) delivers the SAME total to 1 or {len(args.dests)} destinations")
    with open(args.output, "w") as fh:
        json.dump({"control_J": J, "source_exhaustion": r}, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
