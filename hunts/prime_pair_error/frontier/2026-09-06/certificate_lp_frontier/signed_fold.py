"""Express the verified 132.729535 prefix-exchange witness in the signed fold basis.

The zero-moment measures on Q_N are spanned by the folds {Fold(a) : a in Q_N,
a > y} (98 of them at (10^4, 100), = dim of the zero-moment space).  For any
zero-moment delta on Q_N the fold coefficients x are the UNIQUE solution of the
triangular descending recurrence

    x_q = 2 x_{2q} + 2 x_{2q+1} - delta_q,   q in Q_N, q > y,   (missing indices 0),

because delta_a = -x_a + 2 sum_{b : floor(b/2) = a} x_b for a > y (each Fold(b)
with floor(b/2) = a lands +2 x_b at a, Fold(a) lands -x_a).  Solved top down.
The prefix coordinates of delta are then determined and are the reconstruction
check: delta must equal sum_a x_a Fold(a) at every prefix cell too.

Input delta: the greedy prefix-mediated exchange witness of Section 6, rebuilt
exactly from its saved steps (each theta_b z_b - theta_a z_a, z_q = e_q -
sum_s r^{(q)}_s e_s).  This file solves for x, checks the reconstruction,
reports the NEGATIVE fold coefficients (the moves the nonnegative-fold family
of Codex's upper certificate excludes) and the exchanges they encode, and tests
one grouping.  Exact rationals throughout; the final nonnegativity of m + delta
is re-checked by enclosure.
"""
from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction

import numpy as np

from dual_witness import build
from fold_family import fold_vectors
from prefix_witness import mobius_table, prefix_rates


def witness_delta(N: int, y: int, path: str) -> dict[int, Fraction]:
    """Rebuild the greedy witness delta as an exact measure on cells."""
    with open(path) as fh:
        steps = json.load(fh)["greedy"]
    mu = mobius_table(y)
    delta: dict[int, Fraction] = {}
    rate_cache: dict[int, list[int]] = {}

    def rates(q):
        if q not in rate_cache:
            rate_cache[q] = [int(x) for x in prefix_rates(q, y, mu)]
        return rate_cache[q]

    def add(c, v):
        delta[c] = delta.get(c, Fraction(0)) + v

    for s in steps:
        a, b = s["a"], s["b"]
        ta, tb = Fraction(s["theta_a"]), Fraction(s["theta_b"])
        add(b, tb)
        add(a, -ta)
        for i, rb in enumerate(rates(b), start=1):
            if rb:
                add(i, -tb * rb)
        for i, ra in enumerate(rates(a), start=1):
            if ra:
                add(i, ta * ra)
    return {c: v for c, v in delta.items() if v != 0}


def fold_measure(a: int, y: int, mu) -> dict[int, Fraction]:
    kappa, g = fold_vectors(a, y, mu)
    D = {a: Fraction(-1)}
    q = a // 2
    D[q] = D.get(q, Fraction(0)) + 2
    for i in range(1, y + 1):
        if kappa[i - 1]:
            D[i] = D.get(i, Fraction(0)) + kappa[i - 1]
    return {c: v for c, v in D.items() if v != 0}


def solve(N: int, y: int, path: str, verbose: bool = True) -> dict:
    cells, idx, A_mat, e, primes, ell = build(N, y)
    attain = set(int(c) for c in cells)
    mu = mobius_table(y)
    delta = witness_delta(N, y, path)
    gain = sum(delta.values())

    above = sorted((c for c in attain if c > y), reverse=True)
    x: dict[int, Fraction] = {}
    for a in above:
        x[a] = 2 * x.get(2 * a, Fraction(0)) + 2 * x.get(2 * a + 1, Fraction(0)) - delta.get(a, Fraction(0))
    x = {a: v for a, v in x.items() if v != 0}

    # reconstruct and check at EVERY cell (above y and prefix)
    recon: dict[int, Fraction] = {}
    g = {}
    for a, xa in x.items():
        fm = fold_measure(a, y, mu)
        g[a] = fold_vectors(a, y, mu)[1]
        for c, v in fm.items():
            recon[c] = recon.get(c, Fraction(0)) + xa * v
    all_cells = set(delta) | set(recon)
    recon_ok = all(recon.get(c, Fraction(0)) == delta.get(c, Fraction(0)) for c in all_cells)
    prefix_ok = all(recon.get(i, Fraction(0)) == delta.get(i, Fraction(0)) for i in range(1, y + 1))
    gain_from_x = sum(xa * g[a] for a, xa in x.items())

    neg = sorted((a for a, v in x.items() if v < 0))
    pos = sorted((a for a, v in x.items() if v > 0))

    # interpret negatives: -Fold(a) moves 2 units FROM floor(a/2) up to a and undoes the prefix kappa
    neg_detail = []
    for a in neg:
        neg_detail.append({"a": a, "x": str(x[a]), "dest_floor_a_over_2": a // 2, "g": g[a], "dest_also_in_x": (a // 2) in x, "x_at_dest": str(x.get(a // 2, 0))})

    # grouping test: pair each negative a with the fold at floor(a/2) (its destination).
    # A -Fold(a) + something at floor(a/2)?  Look at parent/child sign structure.
    parent_child = []
    for a in neg:
        d = a // 2
        parent_child.append({"child_a": a, "x_a": float(x[a]), "parent_2a": 2 * a in x, "x_2a": float(x.get(2 * a, 0)), "x_2a+1": float(x.get(2 * a + 1, 0)), "delta_a": float(delta.get(a, 0))})

    out = {
        "N": N, "y": y,
        "gain": float(gain), "gain_exact": str(gain),
        "reconstruction_exact_all_cells": recon_ok,
        "prefix_reconstruction_exact": prefix_ok,
        "gain_from_fold_coeffs_matches": gain_from_x == gain,
        "n_fold_coeffs": len(x),
        "n_negative": len(neg),
        "n_positive": len(pos),
        "negative_cells": neg,
        "negative_detail": neg_detail,
        "coeff_l1": str(sum(abs(v) for v in x.values())),
        "max_abs_coeff": str(max((abs(v) for v in x.values()), default=0)),
        "x": {int(a): str(v) for a, v in sorted(x.items())},
    }
    if verbose:
        print(f"Signed-fold expansion of the {float(gain):.6f} witness at N={N} y={y}:")
        print(f"  reconstruction exact (all cells): {recon_ok}; prefix exact: {prefix_ok}; gain from coeffs matches: {gain_from_x == gain}")
        print(f"  {len(x)} nonzero fold coeffs: {len(pos)} positive, {len(neg)} negative; |x|_1 = {float(sum(abs(v) for v in x.values())):.3f}, max|x| = {float(max((abs(v) for v in x.values()), default=0)):.4f}")
        print(f"  NEGATIVE fold cells (excluded by the nonnegative-fold family): {neg}")
        for d in neg_detail:
            print(f"    a={d['a']:>5}: x={float(Fraction(d['x'])):+.4f}  -Fold means +mass at {d['a']}, -2 at floor(a/2)={d['dest_floor_a_over_2']}, undo prefix; g={d['g']}, x_at_dest={float(Fraction(d['x_at_dest'])):+.4f}")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=10000)
    ap.add_argument("--y", type=int, default=100)
    ap.add_argument("--witness", required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = solve(args.N, args.y, args.witness)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
