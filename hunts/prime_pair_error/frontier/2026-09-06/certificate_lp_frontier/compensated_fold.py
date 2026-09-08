"""Compensated fold bundles: verification and a prescribed repair rule.

A bundle is an integer combination D = sum_a c_a Fold(a) of the halving folds
of fold_family.py (Lemma 7: each Fold(a) has zero moments and mass g(a)).
Scaled by eps > 0 it is a dual witness for T*(y, N) iff m_c + eps D_c >= 0 on
every cell; the largest admissible eps is min over D_c < 0 of m_c / (-D_c)
and the gain is eps * sum_a c_a g(a).

Lemma 8 (band structure).  On a top prefix cell w in (y/2, y] the action of
Fold(a) is the signed count of quotient indices,

    Fold(a)_w = sum_{k >= 1 : floor(a/k) = w} (-1)^{k+1}      (w in (y/2, y], w != floor(a/2)),

because r^{(a)}_w - 2 r^{(floor(a/2))}_w = #{k : floor(a/k) = w} - 2 #{k even : floor(a/k) = w}.
For w > sqrt(a) at most one k contributes, so Fold(a) drains w iff the unique
k with floor(a/k) = w is even, and refills it iff k is odd.  Below y/2 the
action is the full kappa_w(a) of Lemma 7 (Mobius-weighted parities).

Rule C (band-matched repair), prescribed before evaluation:
  1. Profitable sources P = {a > y : m_a > 0, g(a) > 0}, weight c_a = 1.
  2. For every wall w (zero-mass cell) with net drain D_w < 0, in increasing w:
     add the real-mass cells r > y with Fold(r)_w > 0, in increasing r, each with
     the weight needed to close the deficit (integer, at most the number of
     units it refills times...), until D_w >= 0; a repair may have any gain.
  3. Repeat over the walls (repairs may drain other walls) until no wall is
     negative or a wall has no untried refill; report the first such wall.
  4. eps* from the non-wall capacities; gain eps* (sum_P g + sum_R c_r g(r)).
The rule is deterministic; nothing is chosen by the optimizer.

All checks exact: moments as integers, capacities as integer inequalities
M_c^{den} >= prod over ... (or by enclosure), where M_c is the product of the
prime bases of the prime powers landing in cell c, so m_c = log M_c.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np

from dual_witness import build
from fold_family import fold_vectors
from prefix_witness import mobius_table


def setup(N: int, y: int):
    cells, idx, A, e, primes, ell = build(N, y)
    mu = mobius_table(y)
    mass_terms: dict[int, dict[int, int]] = {}
    for p in primes:
        for i, cnt in e[p].items():
            mass_terms.setdefault(int(cells[i]), {})[p] = cnt
    Mprod = {c: math.prod(p**k for p, k in mt.items()) for c, mt in mass_terms.items()}  # m_c = log Mprod[c]
    return cells, idx, mu, mass_terms, Mprod


def fold_measure(a: int, y: int, mu: np.ndarray) -> dict[int, int]:
    kappa, g = fold_vectors(a, y, mu)
    D = {a: -1}
    q = a // 2
    D[q] = D.get(q, 0) + 2
    for i in range(1, y + 1):
        if kappa[i - 1]:
            D[i] = D.get(i, 0) + kappa[i - 1]
    return {c: v for c, v in D.items() if v}


def bundle_measure(coeffs: dict[int, int], y: int, mu: np.ndarray) -> dict[int, int]:
    D: dict[int, int] = {}
    for a, c in coeffs.items():
        for cell, v in fold_measure(a, y, mu).items():
            D[cell] = D.get(cell, 0) + c * v
    return {c: v for c, v in D.items() if v}


def check_bundle(N: int, y: int, coeffs: dict[int, int], dps: int = 40) -> dict:
    cells, idx, mu, mass_terms, Mprod = setup(N, y)
    D = bundle_measure(coeffs, y, mu)
    support_ok = all(c in idx for c in D)
    moments_ok = all(sum(v * (c // j) for c, v in D.items()) == 0 for j in range(1, y + 1))
    gains = {a: fold_vectors(a, y, mu)[1] for a in coeffs}
    total_units = sum(c * gains[a] for a, c in coeffs.items())
    # largest eps: min over D_c < 0 of m_c / (-D_c); exact comparison via M_c
    import mpmath

    iv = mpmath.iv
    iv.dps = dps
    mpmath.mp.dps = dps

    def lo(x):
        return mpmath.mp.make_mpf(x._mpi_[0])

    def hi(x):
        return mpmath.mp.make_mpf(x._mpi_[1])

    neg = {c: -v for c, v in D.items() if v < 0}
    eps_lo = None
    binding = None
    for c, d in neg.items():
        if c not in Mprod:
            return {"support_ok": support_ok, "moments_ok": moments_ok, "feasible": False, "failing_cell": c, "reason": "zero-mass cell withdrawn", "D_at_cell": -d}
        cand = iv.log(iv.mpf(Mprod[c])) / d
        if eps_lo is None or lo(cand) < eps_lo:
            eps_lo, binding = lo(cand), c
    # exactness: with eps = log(M_b)/d_b at the binding cell b, feasibility at
    # every withdrawn cell c is the integer inequality M_c^{d_b} >= M_b^{d_c}.
    exact_ok = True
    b = binding
    if b is not None:
        for c, d in neg.items():
            if Mprod[c] ** neg[b] < Mprod[b] ** d:
                exact_ok = False
    gain = iv.log(iv.mpf(Mprod[b])) / neg[b] * total_units if b is not None else None
    return {
        "support_ok": support_ok,
        "moments_ok": moments_ok,
        "coefficients": coeffs,
        "gains_per_unit": gains,
        "total_gain_units": total_units,
        "D": {int(c): int(v) for c, v in sorted(D.items())},
        "withdrawn_cells": {int(c): int(d) for c, d in sorted(neg.items())},  # positive multiplicities -D_c
        "binding_cell": b,
        "eps_star": f"log({Mprod[b]})/{neg[b]}" if b is not None else None,
        "eps_star_float": float(eps_lo) if eps_lo is not None else None,
        "exact_capacity_inequalities_M_c^d_b>=M_b^d_c": exact_ok,
        "feasible": support_ok and moments_ok and exact_ok,
        "gain_interval": [mpmath.nstr(lo(gain), 20), mpmath.nstr(hi(gain), 20)] if gain is not None else None,
    }


def band_lemma_check(N: int, y: int) -> dict:
    """Lemma 8 on every real-mass source above y: for y/2 < w < y the action of
    Fold(a) at w is the signed count sum_{k : floor(a/k) = w} (-1)^{k+1}; at
    w = y it is floor(a/y) mod 2 (the last prefix rate is floor(q/y), not a
    difference).  Cells w = floor(a/2) carry the destination's +2 in addition."""
    cells, idx, mu, mass_terms, Mprod = setup(N, y)
    bad = 0
    tested = 0
    bad_y = 0
    for a in sorted(c for c in mass_terms if c > y):
        Dm = fold_measure(a, y, mu)
        q = a // 2
        for w in range(y // 2 + 1, y):
            signed = sum((-1) ** (k + 1) for k in range(1, a + 1) if a // k == w) + (2 if w == q else 0)
            tested += 1
            if Dm.get(w, 0) != signed:
                bad += 1
        expected_y = (a // y) % 2 + (2 if y == q else 0)
        if Dm.get(y, 0) != expected_y:
            bad_y += 1
    return {"tested": tested, "violations": bad, "violations_at_w_eq_y": bad_y}


def rule_c(N: int, y: int, verbose: bool = True, order: str = "clean-gain-r") -> dict:
    """order = 'r': repairs in increasing r (variant C0);
       order = 'clean-gain-r': repairs that withdraw at no wall first, then by
       decreasing fold gain g(r), then increasing r (Rule C)."""
    cells, idx, mu, mass_terms, Mprod = setup(N, y)
    real = sorted(c for c in mass_terms if c > y)
    walls = [c for c in range(1, y + 1) if c not in mass_terms]
    wallset = set(walls)
    fm = {a: fold_measure(a, y, mu) for a in real}
    g = {a: fold_vectors(a, y, mu)[1] for a in real}
    clean = {a: all(v >= 0 for c, v in fm[a].items() if c in wallset) for a in real}
    coeffs = {a: 1 for a in real if g[a] > 0}
    log = []
    tried: set[tuple[int, int]] = set()
    for _round in range(400):
        D = bundle_measure(coeffs, y, mu)
        bad_walls = [w for w in walls if D.get(w, 0) < 0]
        if not bad_walls:
            break
        w = bad_walls[0]
        deficit = -D[w]
        options = [r for r in real if fm[r].get(w, 0) > 0 and (r, w) not in tried]
        if not options:
            log.append({"wall": w, "deficit": deficit, "repair": None})
            break
        if order == "r":
            r = options[0]
        else:
            r = sorted(options, key=lambda t: (not clean[t], -g[t], t))[0]
        units = -(-deficit // fm[r][w])  # ceil(deficit / refill per unit)
        coeffs[r] = coeffs.get(r, 0) + units
        tried.add((r, w))
        log.append({"wall": w, "deficit": deficit, "repair": r, "units": units, "g_r": g[r], "clean": clean[r]})
    result = check_bundle(N, y, coeffs)
    result["order"] = order
    result["rule_log"] = log
    result["walls"] = walls
    result["profitable_sources"] = [a for a in real if g[a] > 0]
    result["clean_refills_available"] = {int(w): [int(r) for r in real if fm[r].get(w, 0) > 0 and clean[r]] for w in walls}
    result["repairs_added"] = {int(a): int(c - (1 if g[a] > 0 else 0)) for a, c in coeffs.items() if c - (1 if g[a] > 0 else 0) > 0}
    if verbose:
        print(f"Rule C ({order}) at N={N} y={y}: walls {walls}; profitable sources {result['profitable_sources']}")
        for entry in log:
            print(f"   wall {entry['wall']:>3} deficit {entry['deficit']}: repair {entry['repair']} x{entry.get('units')} (g = {entry.get('g_r')}, clean = {entry.get('clean')})")
        print(f"   support {result['support_ok']}, moments {result['moments_ok']}, feasible {result['feasible']}, binding {result.get('binding_cell')}, eps* = {result.get('eps_star')}, gain units {result.get('total_gain_units')}, gain {result.get('gain_interval')}")
        if not result["feasible"]:
            print(f"   FAILURE: {result.get('reason')} at cell {result.get('failing_cell')} (D = {result.get('D_at_cell')})")
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--bundle", type=str, default=None, help="e.g. 76:1,200:2,333:1")
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = {"N": args.N, "y": args.y, "band_lemma": band_lemma_check(args.N, args.y)}
    print(f"Lemma 8 check at N={args.N} y={args.y}: {out['band_lemma']}")
    if args.bundle:
        coeffs = {int(k): int(v) for k, v in (s.split(":") for s in args.bundle.split(","))}
        out["bundle"] = check_bundle(args.N, args.y, coeffs)
        b = out["bundle"]
        print(f"Bundle {coeffs}: support {b['support_ok']}, moments {b['moments_ok']}, gains {b['gains_per_unit']}, units {b['total_gain_units']}, withdrawn {b['withdrawn_cells']}, binding {b['binding_cell']}, eps* = {b['eps_star']}, exact capacities {b['exact_capacity_inequalities_M_c^d_b>=M_b^d_c']}, gain {b['gain_interval']}")
    out["rule_c0_increasing_r"] = rule_c(args.N, args.y, order="r")
    out["rule_c"] = rule_c(args.N, args.y, order="clean-gain-r")
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
