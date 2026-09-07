"""Parameterized dual witnesses for T*(y, N) with the Mobius-prefix basis.

Basis S0 = {1, ..., y} (all attainable for y <= sqrt(N) - 1).  A_{S0} is
unitriangular and the tight certificate is c = mu_{<= y}.  For a cell q > y
the exact redistribution rates onto S0 have the closed form

    R_q(t) = sum_{k <= y/t} mu(k) floor(q / (t k)),   r^{(q)}_s = R_q(s) - R_q(s+1),

(R_q(t) counts multiples of t up to q whose cofactor has no divisor in
[2, y/t]; R_q(y+1) = 0), and the gain per unit mass is R_q(1) - 1 = W_mu(q) - 1.
Moving all mass gives the explicit measure

    nu_s = N(s) - N(s+1),   N(t) = sum_{k <= y/t} mu(k) log floor(N/(t k))!,

so feasibility of the full transfer is exactly that t -> N(t) is nonincreasing
on [1, y], and its gain is B_mu(N) - psi(N).  Moving a fraction theta_q in
[0, 1] of each cell's mass is a small LP; the rationalized optimum is
re-verified exactly (moments) and by enclosure (signs, gain).

Also the three-cell relation R_q - R_{q-1} = R_1 for y-rough q (the rough
spike in T* form), valid whenever q and q-1 are both attainable.

Everything here is a LOWER bound on T*(y,N) - psi(N) once verified; the
exact optimum is in dual_witness.py.
"""
from __future__ import annotations

import argparse
import json
import math
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog

from dual_witness import build, lu_solve_exact, float_L


def mobius_table(n: int) -> np.ndarray:
    mu = np.ones(n + 1, dtype=np.int64)
    mu[0] = 0
    is_p = np.ones(n + 1, dtype=bool)
    for p in range(2, n + 1):
        if not is_p[p]:
            continue
        is_p[2 * p :: p] = False
        mu[p::p] *= -1
        mu[p * p :: p * p] = 0
    return mu


def prefix_rates(q: int, y: int, mu: np.ndarray) -> list[Fraction]:
    """r^{(q)}_s for s = 1..y, exact integers, by the closed form."""
    R = [0] * (y + 2)
    for t in range(1, y + 1):
        R[t] = sum(int(mu[k]) * (q // (t * k)) for k in range(1, y // t + 1))
    return [Fraction(R[s] - R[s + 1]) for s in range(1, y + 1)]


def prefix_family(N: int, y: int, dps: int = 60, verbose: bool = True) -> dict:
    t0 = time.time()
    cells, idx, A, e, primes, ell = build(N, y)
    nq = cells.size
    mu = mobius_table(y)
    S0 = list(range(1, y + 1))
    if any(s not in idx for s in S0):
        raise RuntimeError("prefix basis not attainable at this (N, y)")
    Aq = [[Fraction(int(v)) for v in A[i]] for i in range(nq)]
    AST = [[Fraction(s // j) for s in S0] for j in range(1, y + 1)]

    # cells above y, their masses as {p: count}, and their rates
    mass_terms: dict[int, dict[int, int]] = {}
    for p in primes:
        for i, cnt in e[p].items():
            mass_terms.setdefault(i, {})[p] = cnt
    above = [i for i in range(nq) if cells[i] > y and i in mass_terms]
    rates = {}
    gains = {}
    # closed form, and an exact check against the basis solve for every cell
    exact_check = lu_solve_exact(AST, [Aq[i] for i in above])
    for t, i in enumerate(above):
        q = int(cells[i])
        r = prefix_rates(q, y, mu)
        if r != exact_check[t]:
            raise RuntimeError(f"closed-form rates disagree with the basis solve at q = {q}")
        rates[i] = r
        gains[i] = sum(r) - 1  # = W_mu(q) - 1, exact integer
        assert gains[i] == sum(int(mu[j]) * (q // j) for j in range(1, y + 1)) - 1

    # masses in float for the LP
    mf = {i: sum(math.log(p) * cnt for p, cnt in mt.items()) for i, mt in mass_terms.items()}
    own = np.array([mf.get(idx[s], 0.0) for s in S0])

    def nu_float(theta: dict[int, float]) -> np.ndarray:
        v = own.copy()
        for i, th in theta.items():
            if th:
                v += th * mf[i] * np.array([float(x) for x in rates[i]])
        return v

    # full transfer
    full = nu_float({i: 1.0 for i in above})
    gain_full = sum(mf[i] * float(gains[i]) for i in above)
    # theta-LP: maximize sum theta_i mf_i gain_i  s.t.  own + sum theta_i mf_i r_i >= 0, 0 <= theta <= 1
    nv = len(above)
    obj = -np.array([mf[i] * float(gains[i]) for i in above])
    M = np.array([[mf[i] * float(rates[i][s]) for i in above] for s in range(y)])
    res = linprog(obj, A_ub=-M, b_ub=own, bounds=[(0, 1)] * nv, method="highs-ds")
    if res.status != 0:
        raise RuntimeError(res.message)
    theta_f = {i: float(t) for i, t in zip(above, res.x)}
    gain_lp = float(-res.fun)
    # rationalize theta and re-verify exactly: nu_s = sum_p log p * (rational)
    den = 1000
    theta_r = {i: Fraction(int(round(theta_f[i] * den)), den) for i in above}
    # per-prime rational coefficients of nu on S0
    import mpmath

    iv = mpmath.iv
    iv.dps = dps
    mpmath.mp.dps = dps
    logs = {p: iv.log(iv.mpf(p)) for p in primes}

    def fr(x: Fraction):
        return iv.mpf(x.numerator) / iv.mpf(x.denominator)

    def lo(x):
        return mpmath.mp.make_mpf(x._mpi_[0])

    def hi(x):
        return mpmath.mp.make_mpf(x._mpi_[1])

    coef = {s: {} for s in range(y)}  # coef[s][p] rational
    for s in S0:
        i0 = idx[s]
        for p, cnt in mass_terms.get(i0, {}).items():
            coef[s - 1][p] = coef[s - 1].get(p, Fraction(0)) + cnt
    for i in above:
        th = theta_r[i]
        if th == 0:
            continue
        for p, cnt in mass_terms[i].items():
            for s in range(y):
                if rates[i][s] != 0:
                    coef[s][p] = coef[s].get(p, Fraction(0)) + th * cnt * rates[i][s]
    min_lower = float("inf")
    ok = True
    for s in range(y):
        tot = iv.mpf(0)
        for p, c in coef[s].items():
            if c != 0:
                tot += logs[p] * fr(c)
        if coef[s]:
            min_lower = min(min_lower, float(lo(tot)))
            if lo(tot) < 0:
                ok = False
    # exact moment identity of the perturbation: sum_s nu_s floor(s/j) = L_j (rational coefficients per p)
    # (equivalently sum_q delta_q floor(q/j) = 0); check per prime as integers
    ident_ok = True
    for p in primes:
        for j in range(1, y + 1):
            lhs = sum(coef[s].get(p, Fraction(0)) * (S0[s] // j) for s in range(y))
            # mass of p that stays above y (not moved) contributes its own floor moments
            stay = sum((1 - theta_r[i]) * cnt * (int(cells[i]) // j) for i in above for pp, cnt in mass_terms[i].items() if pp == p)
            if lhs + stay != Fraction(int(ell[p][j - 1])):
                ident_ok = False
                break
        if not ident_ok:
            break
    gain_r = iv.mpf(0)
    for i in above:
        if theta_r[i] != 0:
            for p, cnt in mass_terms[i].items():
                gain_r += logs[p] * fr(theta_r[i] * cnt * gains[i])

    # rough-spike three-cell relation in T* form
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    rough_gain = 0.0
    rough_cells = []
    for i in above:
        q = int(cells[i])
        if q <= int(math.isqrt(N)) and spf[q] > y and (q - 1) in idx:
            rough_gain += mf[i]
            rough_cells.append(q)

    out = {
        "N": N,
        "y": y,
        "basis": "prefix {1..y}, c = mu",
        "cells_above_y_with_mass": len(above),
        "closed_form_rates_verified_exactly": True,
        "full_transfer_gain": gain_full,
        "full_transfer_min_nu": float(full.min()),
        "full_transfer_feasible": bool(full.min() >= 0),
        "theta_lp_gain_float": gain_lp,
        "theta_lp_cells_moved": int(sum(1 for t in theta_f.values() if t > 1e-9)),
        "theta_lp_cells_full": int(sum(1 for t in theta_f.values() if t > 1 - 1e-9)),
        "rationalized_theta_denominator": den,
        "rationalized_gain_interval": [mpmath.nstr(lo(gain_r), dps), mpmath.nstr(hi(gain_r), dps)],
        "rationalized_gain_mid": float((lo(gain_r) + hi(gain_r)) / 2),
        "rationalized_nu_min_lower_endpoint": min_lower,
        "rationalized_feasible_by_enclosure": ok,
        "rationalized_moment_identities_exact": ident_ok,
        "positive_gain_cells": {int(cells[i]): int(gains[i]) for i in above if gains[i] > 0},
        "negative_gain_cells_count": int(sum(1 for i in above if gains[i] < 0)),
        "rough_spike_T_gain": rough_gain,
        "rough_spike_cells": rough_cells,
        "seconds": time.time() - t0,
    }
    if verbose:
        print(f"prefix family at N={N} y={y}: {len(above)} cells above y carry mass")
        print(f"  closed-form rates == basis solve: exact, all cells")
        print(f"  full transfer: gain {gain_full:.4f}, min nu {full.min():.4f}, feasible {full.min() >= 0}")
        print(f"  theta-LP: gain {gain_lp:.4f}, cells moved {out['theta_lp_cells_moved']} (fully {out['theta_lp_cells_full']}) of {len(above)}")
        print(f"  rationalized (den {den}): gain in [{float(lo(gain_r)):.6f}, {float(hi(gain_r)):.6f}], nu >= 0: {ok} (min {min_lower:.3e}), moments exact: {ident_ok}")
        print(f"  positive-gain cells: {out['positive_gain_cells']}")
        print(f"  rough-spike (3-cell) T* gain: {rough_gain:.4f} from cells {rough_cells}")
        print(f"  {time.time()-t0:.1f}s")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--output", required=True)
    args = ap.parse_args()
    out = prefix_family(args.N, args.y)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
