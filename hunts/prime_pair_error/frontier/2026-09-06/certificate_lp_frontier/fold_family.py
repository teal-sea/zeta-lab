"""The halving-fold family: an explicit parameterized dual witness for T*.

For a real-mass attainable cell a > y put q = floor(a/2) = floor(N/(2d)),
attainable.  Because floor(a/j) - 2 floor(q/j) = floor(a/j) mod 2, the measure

    Fold(a) = -e_a + 2 e_q + sum_{i<=y} kappa_i(a) e_i,
    kappa_i(a) = T_i(a) - T_{i+1}(a),  T_i(a) = sum_{m <= y/i} mu(m) (floor(a/(im)) mod 2),  T_{y+1} = 0,

has A^T Fold(a) = 0 (checked as an exact integer identity for every a used)
and total mass g(a) = 1 + sum_{j<=y} mu(j) (floor(a/j) mod 2) = 1 + W_mu(a)
- 2 W_mu(q).  The family is

    D(t) = t * sum_{a in A} m_a Fold(a),      A = {a > y : m_a > 0, g(a) > 0},

with the single parameter t in [0, 1].  Support: the cells a, floor(a/2) and
the prefix 1..y, all attainable.  Net capacity on a cell c:

    m_c + t * [ -m_c [c in A] + 2 sum_{a in A, floor(a/2) = c} m_a + sum_{a in A} m_a kappa_c(a) [c <= y] ] >= 0,

which is m_c + t Delta_c >= 0 with an explicit Delta_c; feasible iff
t <= t* = min over cells with Delta_c < 0 of m_c / (-Delta_c) (and t <= 1).
Gain G(t) = t Gamma, Gamma = sum_{a in A} m_a g(a).

Variants evaluated with the same rule on prescribed subsets of A:
  F1  all of A;
  F2  the drain-safe subset {a in A : kappa_i(a) >= 0 at every prefix cell i with m_i = 0};
  F3  A restricted to a > 2y + 1 (destination above the prefix);
  F4  A restricted to a <= 2y + 1 (destination in the prefix: the withdrawal family).
Each verified: integer moment identities per source, capacities by interval
arithmetic at a rational t <= t*, gain as an enclosure.  One thread.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np

from dual_witness import build
from prefix_witness import mobius_table


def fold_vectors(a: int, y: int, mu: np.ndarray):
    """kappa_i(a) for i = 1..y and g(a), integers."""
    T = [0] * (y + 2)
    for i in range(1, y + 1):
        T[i] = sum(int(mu[m]) * ((a // (i * m)) % 2) for m in range(1, y // i + 1))
    kappa = [T[i] - T[i + 1] for i in range(1, y + 1)]
    g = 1 + sum(int(mu[j]) * ((a // j) % 2) for j in range(1, y + 1))
    return kappa, g


def evaluate(N: int, y: int, dps: int = 40, verbose: bool = True) -> dict:
    t0 = time.time()
    cells, idx, A, e, primes, ell = build(N, y)
    mu = mobius_table(y)
    if any(s not in idx for s in range(1, y + 1)):
        raise RuntimeError("a prefix cell is not attainable at this (N, y)")
    import mpmath

    iv = mpmath.iv
    iv.dps = dps
    mpmath.mp.dps = dps
    logs = {p: iv.log(iv.mpf(p)) for p in primes}

    def lo(x):
        return mpmath.mp.make_mpf(x._mpi_[0])

    def hi(x):
        return mpmath.mp.make_mpf(x._mpi_[1])

    def fr(x: Fraction):
        return iv.mpf(x.numerator) / iv.mpf(x.denominator)

    mass_terms: dict[int, dict[int, int]] = {}
    for p in primes:
        for i, cnt in e[p].items():
            mass_terms.setdefault(int(cells[i]), {})[p] = cnt

    def mass_iv(c: int):
        tot = iv.mpf(0)
        for p, cnt in mass_terms.get(c, {}).items():
            tot += logs[p] * cnt
        return tot

    m_f = {c: float(sum(math.log(p) * k for p, k in mt.items())) for c, mt in mass_terms.items()}
    m_lo = {c: float(lo(mass_iv(c))) for c in mass_terms}

    # the fold data for every real-mass cell above y
    sources = sorted(c for c in mass_terms if c > y)
    fold = {}
    moment_ok = True
    for a in sources:
        kappa, g = fold_vectors(a, y, mu)
        q = a // 2
        # exact integer moment identity: -floor(a/j) + 2 floor(q/j) + sum_i kappa_i floor(i/j) = 0
        for j in range(1, y + 1):
            if -(a // j) + 2 * (q // j) + sum(kappa[i - 1] * (i // j) for i in range(1, y + 1)) != 0:
                moment_ok = False
        fold[a] = (kappa, g, q)
    if not moment_ok:
        raise RuntimeError("fold moment identity failed")

    zero_mass_prefix = [i for i in range(1, y + 1) if i not in mass_terms]

    def run_variant(name: str, Aset: list[int]) -> dict:
        if not Aset:
            return {"variant": name, "sources": 0, "gain": 0.0, "note": "empty"}
        # Delta_c on every touched cell (float, with masses as floats for the search;
        # the final check is by enclosure at the rational t chosen)
        Delta: dict[int, float] = {}
        for a in Aset:
            kappa, g, q = fold[a]
            Delta[a] = Delta.get(a, 0.0) - m_f[a]
            Delta[q] = Delta.get(q, 0.0) + 2 * m_f[a]
            for i in range(1, y + 1):
                if kappa[i - 1]:
                    Delta[i] = Delta.get(i, 0.0) + m_f[a] * kappa[i - 1]
        binding, t_star = None, 1.0
        for c, d in Delta.items():
            if d < 0:
                cap = m_lo.get(c, 0.0)
                ratio = cap / (-d)
                if ratio < t_star:
                    t_star, binding = ratio, c
        Gamma = sum(m_f[a] * fold[a][1] for a in Aset)
        # rigorous version at rational t
        t_r = Fraction(int(math.floor(t_star * (1 - 1e-6) * 10**6)), 10**6) if t_star > 0 else Fraction(0)
        feasible = True
        min_lower = float("inf")
        if t_r > 0:
            # exact per-cell coefficient of each log p, then enclosure
            coef: dict[int, dict[int, Fraction]] = {}
            for a in Aset:
                kappa, g, q = fold[a]
                for p, cnt in mass_terms[a].items():
                    w = t_r * cnt
                    coef.setdefault(a, {})[p] = coef.get(a, {}).get(p, Fraction(0)) - w
                    coef.setdefault(q, {})[p] = coef.get(q, {}).get(p, Fraction(0)) + 2 * w
                    for i in range(1, y + 1):
                        if kappa[i - 1]:
                            coef.setdefault(i, {})[p] = coef.get(i, {}).get(p, Fraction(0)) + w * kappa[i - 1]
            for c, cp in coef.items():
                tot = mass_iv(c)
                for p, w in cp.items():
                    if w:
                        tot += logs[p] * fr(w)
                min_lower = min(min_lower, float(lo(tot)))
                if lo(tot) < 0:
                    feasible = False
        G = iv.mpf(0)
        for a in Aset:
            kappa, g, q = fold[a]
            for p, cnt in mass_terms[a].items():
                G += logs[p] * fr(t_r * cnt * g)
        best_single = max(Aset, key=lambda a: m_f[a] * fold[a][1])
        return {
            "variant": name,
            "sources": len(Aset),
            "Gamma_per_unit_t": Gamma,
            "t_star": t_star,
            "binding_cell": binding,
            "binding_cell_mass": m_lo.get(binding, 0.0) if binding is not None else None,
            "binding_cell_is_prefix": (binding is not None and binding <= y),
            "t_rational": str(t_r),
            "gain_interval": [mpmath.nstr(lo(G), 20), mpmath.nstr(hi(G), 20)],
            "gain": float(lo(G)),
            "feasible_by_enclosure": feasible,
            "min_cell_lower_endpoint": min_lower,
            "best_single_source": {"a": best_single, "m": m_f[best_single], "g": fold[best_single][1], "m_times_g": m_f[best_single] * fold[best_single][1]},
        }

    # ---- Family R: shift-down exchanges at y-rough cells (drain-free) ------
    # For a > y y-rough with real mass and a - 1 attainable, R_a - R_{a-1} = D_a
    # = e_1 (+ e_p if some prime p = i+1 <= y+1 divides a, impossible for
    # y-rough a unless p = y+1), so Shift(a) = e_1 + e_{a-1} - e_a has zero
    # moments and mass 1; the only capacity is m_a >= theta.  Gain sum m_a.
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    rough = [a for a in sources if spf[a] > y and (a - 1) in idx]
    rough_ok = True
    for a in rough:
        for j in range(1, y + 1):
            if (1 // j) + ((a - 1) // j) - (a // j) != 0:
                rough_ok = False
    R_gain = iv.mpf(0)
    for a in rough:
        R_gain += mass_iv(a)
    familyR = {
        "sources": rough,
        "moment_identities_exact": rough_ok,
        "gain_interval": [mpmath.nstr(lo(R_gain), 20), mpmath.nstr(hi(R_gain), 20)],
        "gain": float(lo(R_gain)),
        "note": "feasible for every t in [0,1] with no prefix drain; gain at t = 1 is the full mass of the sources",
    }

    Aall = [a for a in sources if fold[a][1] > 0]
    Asafe = [a for a in Aall if all(fold[a][0][i - 1] >= 0 for i in zero_mass_prefix)]
    variants = [
        run_variant("F1 all g>0", Aall),
        run_variant("F2 drain-safe at zero-mass prefix cells", Asafe),
        run_variant("F3 a > 2y+1", [a for a in Aall if a > 2 * y + 1]),
        run_variant("F4 a <= 2y+1 (withdrawals)", [a for a in Aall if a <= 2 * y + 1]),
    ]
    # single-source rigorous bounds (each alone), best few
    singles = []
    for a in Aall:
        r = run_variant(f"single {a}", [a])
        singles.append((r["gain"], a, r["t_star"], r["binding_cell"], fold[a][1]))
    singles.sort(reverse=True)
    # F5: the sources that are feasible alone at t = 1, taken jointly
    A5 = [s[1] for s in singles if s[2] >= 1.0 - 1e-12]
    variants.append(run_variant("F5 union of individually feasible sources", A5))

    out = {
        "N": N, "y": y, "sources_above_y_with_mass": len(sources), "A_size": len(Aall),
        "zero_mass_prefix_cells": zero_mass_prefix,
        "g_values": {a: fold[a][1] for a in sources},
        "moment_identities_exact_all_sources": moment_ok,
        "variants": variants,
        "family_R_rough_shift": familyR,
        "best_single_sources": [{"gain": s[0], "a": s[1], "t_star": s[2], "binding": s[3], "g": s[4]} for s in singles[:8]],
        "seconds": time.time() - t0,
    }
    if verbose:
        print(f"Fold family at N={N} y={y}: {len(sources)} real-mass cells above y, A (g>0) = {len(Aall)}, zero-mass prefix cells ({len(zero_mass_prefix)}) {zero_mass_prefix}")
        print(f"  moment identities exact for all {len(sources)} sources: {moment_ok}")
        for v in variants:
            if v.get("note") == "empty":
                print(f"  {v['variant']}: empty")
                continue
            bm = v["binding_cell_mass"]
            print(f"  {v['variant']}: sources {v['sources']}, Gamma = {v['Gamma_per_unit_t']:.4f}, t* = {v['t_star']:.6f} (binds at cell {v['binding_cell']}, mass {bm if bm is None else round(bm, 4)}, prefix {v['binding_cell_is_prefix']}), gain = {v['gain']:.6f}, feasible {v['feasible_by_enclosure']}")
        print("  best single sources (gain, a, t*, binding cell, g):", [(round(s[0], 4), s[1], round(s[2], 4), s[3], s[4]) for s in singles[:6]])
        print(f"  Family R (rough shifts): sources {rough}, moments exact {rough_ok}, gain {familyR['gain']:.6f}")
        print(f"  {time.time()-t0:.1f}s")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = evaluate(args.N, args.y)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1, default=str)


if __name__ == "__main__":
    main()
