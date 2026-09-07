"""Exact dual witnesses for the attainable-quotient floor T*(y, N).

Setting (RESULTS.md Section 4.6, PR #203).  Q_N = {floor(N/d) : 2 <= d <= N},
A[q, j] = floor(q/j) for q in Q_N and j <= y, L_j = log floor(N/j)!.  The dual
of T* is

    maximize  sum_q nu_q   s.t.  A^T nu = L,  nu >= 0,

and the prime-power measure m_q = sum_{d : floor(N/d) = q} Lambda(d) is
feasible with value psi(N).  Any feasible nu certifies T*(y,N) - psi(N) >=
sum_q nu_q - psi(N) (Lemma 1 of BARRIER.md, restricted to Q_N).

Structure of every witness.  Pick a basis S of y cells with A_S invertible.
The mass of a cell q is redistributed onto S by the exact rational rates

    r^{(q)} = (A_S^T)^{-1} A[q, :]        (so A_S^T r^{(q)} = A[q, :]),

which preserve all y moments, and its gain per unit mass is
1^T r^{(q)} - 1 = W_c(q) - 1 with c = A_S^{-1} 1 the primal certificate that is
tight on S.  Because L = sum_p log(p) l^{(p)} with integer vectors
l^{(p)}_j = sum_k floor(N/(p^k j)), the redistributed measure is

    nu_s = sum_p log(p) * nu^{(p)}_s,     nu^{(p)} = (A_S^T)^{-1} l^{(p)}  (rational),

so each sign is decided by an enclosure of finitely many log p, and the gain is
G = sum_p log(p) * s_p with rational s_p = 1^T nu^{(p)} - #{k : p^k <= N}.

This file: build the problem, take the basis from a floating dual simplex,
recompute everything in exact rationals, verify the moment identities
exactly, decide signs and the gain with interval arithmetic (mpmath.iv), and
report the exchange pattern (which cells empty, where their mass goes).
"""
from __future__ import annotations

import argparse
import json
import math
import sys
import time
from fractions import Fraction

import numpy as np
from scipy.optimize import linprog


# ----------------------------------------------------------------------------
# problem data
# ----------------------------------------------------------------------------
def sieve_lambda_primes(N: int):
    """(prime of d, or 0) for d <= N, i.e. Lambda(d) = log(prime[d]) if > 0."""
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            spf[p::p][spf[p::p] == 0] = p
    prime_of = np.zeros(N + 1, dtype=np.int64)
    for d in range(2, N + 1):
        p = spf[d]
        m = d
        while m % p == 0:
            m //= p
        if m == 1:
            prime_of[d] = p
    return prime_of


def build(N: int, y: int):
    cells = np.array(sorted({N // d for d in range(2, N + 1)}), dtype=np.int64)
    idx = {int(q): i for i, q in enumerate(cells)}
    A = (cells[:, None] // np.arange(1, y + 1)[None, :]).astype(np.int64)  # |Q| x y
    prime_of = sieve_lambda_primes(N)
    # mass bookkeeping: e[p][i] = number of powers of p landing in cell i
    e: dict[int, dict[int, int]] = {}
    for d in range(2, N + 1):
        p = int(prime_of[d])
        if p:
            i = idx[N // d]
            e.setdefault(p, {})
            e[p][i] = e[p].get(i, 0) + 1
    primes = sorted(e)
    # integer right-hand sides l^{(p)} = sum_k A[cell(p^k), :]
    ell = {p: sum((A[i] * cnt for i, cnt in e[p].items()), np.zeros(y, dtype=np.int64)) for p in primes}
    return cells, idx, A, e, primes, ell


def float_L(primes, ell, y):
    L = np.zeros(y)
    for p in primes:
        L += math.log(p) * ell[p]
    return L


# ----------------------------------------------------------------------------
# exact linear algebra over Q
# ----------------------------------------------------------------------------
def lu_solve_exact(M: list[list[Fraction]], rhs_list: list[list[Fraction]]):
    """Solve M x = b for several b, M square over Q, by one Gauss-Jordan pass.
    Returns list of solutions or raises if singular."""
    n = len(M)
    k = len(rhs_list)
    # augmented matrix [M | b_1 ... b_k]
    aug = [row[:] + [rhs[i] for rhs in rhs_list] for i, row in enumerate(M)]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            raise ValueError("singular basis matrix")
        aug[col], aug[piv] = aug[piv], aug[col]
        pv = aug[col][col]
        if pv != 1:
            aug[col] = [v / pv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                rowc = aug[col]
                aug[r] = [a - f * b for a, b in zip(aug[r], rowc)]
    return [[aug[i][n + t] for i in range(n)] for t in range(k)]


def rank_exact(M: list[list[Fraction]]) -> int:
    rows = [r[:] for r in M]
    rank = 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = next((r for r in range(rank, len(rows)) if rows[r][col] != 0), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        pv = rows[rank][col]
        rows[rank] = [v / pv for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][col] != 0:
                f = rows[r][col]
                rows[r] = [a - f * b for a, b in zip(rows[r], rows[rank])]
        rank += 1
    return rank


# ----------------------------------------------------------------------------
# the witness
# ----------------------------------------------------------------------------
def witness(N: int, y: int, dps: int = 60, verbose: bool = True) -> dict:
    t0 = time.time()
    cells, idx, A, e, primes, ell = build(N, y)
    nq = cells.size
    L = float_L(primes, ell, y)
    psiN = sum(math.log(p) * sum(e[p].values()) for p in primes)

    # 1. floating dual simplex: a vertex of {A^T nu = L, nu >= 0} maximizing 1.nu
    res = linprog(-np.ones(nq), A_eq=A.T.astype(float), b_eq=L, bounds=(0, None), method="highs-ds")
    if res.status != 0:
        raise RuntimeError(res.message)
    nu_f = res.x
    gain_f = float(-res.fun) - psiN
    support = [i for i in range(nq) if nu_f[i] > 1e-9]

    # 2. basis: extend the support to y independent columns of A^T (exact rank)
    Aq = [[Fraction(int(v)) for v in A[i]] for i in range(nq)]  # rows = cells
    basis = list(support)
    if rank_exact([Aq[i] for i in basis]) < len(basis):
        raise RuntimeError("support rows dependent; degenerate vertex needs care")
    for i in range(nq):
        if len(basis) == y:
            break
        if i in basis:
            continue
        if rank_exact([Aq[t] for t in basis + [i]]) == len(basis) + 1:
            basis.append(i)
    if len(basis) != y:
        raise RuntimeError(f"could not complete a basis: rank {len(basis)} < y = {y}")
    basis.sort()
    # A_S^T nu_S = l^{(p)}: the square system has matrix (A_S)^T, i.e. rows j, columns s.
    AST = [[Aq[s][j] for s in basis] for j in range(y)]  # y x y, entry (j, s) = floor(s/j)
    rhs = [[Fraction(int(v)) for v in ell[p]] for p in primes]
    sols = lu_solve_exact(AST, rhs)  # sols[t] = nu^{(p_t)} on basis
    nu_p = {p: sols[t] for t, p in enumerate(primes)}

    # 3. exact moment identities: A_S^T nu^{(p)} = l^{(p)} for every p
    bad = 0
    for p in primes:
        v = nu_p[p]
        for j in range(y):
            if sum(AST[j][k] * v[k] for k in range(y)) != Fraction(int(ell[p][j])):
                bad += 1
    if bad:
        raise RuntimeError(f"exact moment identity failed in {bad} places")

    # 4. signs by interval arithmetic, and the gain
    import mpmath

    iv = mpmath.iv
    iv.dps = dps
    mpmath.mp.dps = dps
    logs = {p: iv.log(iv.mpf(p)) for p in primes}

    def fr(x: Fraction):
        return iv.mpf(x.numerator) / iv.mpf(x.denominator)

    # iv endpoints .a/.b are degenerate intervals; take plain mpf endpoints.
    def lo(x):
        return mpmath.mp.make_mpf(x._mpi_[0])

    def hi(x):
        return mpmath.mp.make_mpf(x._mpi_[1])

    nu_iv = []
    zero_exact = []
    for k, s in enumerate(basis):
        coeffs = {p: nu_p[p][k] for p in primes if nu_p[p][k] != 0}
        if not coeffs:
            nu_iv.append(None)
            zero_exact.append(True)
            continue
        zero_exact.append(False)
        tot = iv.mpf(0)
        for p, c in coeffs.items():
            tot += logs[p] * fr(c)
        nu_iv.append(tot)
    min_lower = min((float(lo(v)) for v in nu_iv if v is not None), default=float("inf"))
    nonneg = all(v is None or lo(v) >= 0 for v in nu_iv)
    # gain G = sum_p log p * s_p
    s_p = {p: sum(nu_p[p]) - Fraction(sum(e[p].values())) for p in primes}
    G = iv.mpf(0)
    for p in primes:
        if s_p[p] != 0:
            G += logs[p] * fr(s_p[p])
    # 5. the exchange pattern: per cell q, the exact rates r^{(q)} and gain g(q)
    # (solved once per distinct row; rows of prime cells are what matter).
    row_sols = lu_solve_exact(AST, [Aq[i] for i in range(nq)])
    gain_per_unit = [sum(row_sols[i]) - 1 for i in range(nq)]  # = W_c(q) - 1 exactly
    c_primal = lu_solve_exact([[Aq[s][j] for j in range(y)] for s in basis], [[Fraction(1)] * y])[0]
    # W_c on all cells, exactly, and check it equals 1 + gain_per_unit
    Wc = [sum(Aq[i][j] * c_primal[j] for j in range(y)) for i in range(nq)]
    assert all(Wc[i] - 1 == gain_per_unit[i] for i in range(nq))
    primal_feasible = all(w >= 1 for w in Wc)

    # mass per cell (exact as {p: count}) and which cells are emptied
    cell_mass_terms = {}
    for p in primes:
        for i, cnt in e[p].items():
            cell_mass_terms.setdefault(i, {})[p] = cnt
    emptied = [i for i in cell_mass_terms if i not in basis]
    moved_gain = {}
    for i in emptied:
        g = gain_per_unit[i]
        moved_gain[i] = g
    out = {
        "N": N,
        "y": y,
        "n_cells": int(nq),
        "n_primes": len(primes),
        "psi_N": psiN,
        "lp_gain_float": gain_f,
        "support_size": len(support),
        "basis_cells": [int(cells[i]) for i in basis],
        "basis_is_support": len(support) == y,
        "moment_identities_exact": True,
        "primal_tight_certificate_feasible_on_Q": primal_feasible,
        "primal_c": {j + 1: str(c_primal[j]) for j in range(y) if c_primal[j] != 0},
        "nu_min_lower_endpoint": min_lower,
        "nu_all_nonnegative_by_enclosure": nonneg,
        "nu_exactly_zero_on_basis": int(sum(zero_exact)),
        "gain_interval": [mpmath.nstr(lo(G), dps), mpmath.nstr(hi(G), dps)],
        "gain_mid": float((lo(G) + hi(G)) / 2),
        "gain_width": float(hi(G) - lo(G)),
        "s_p_nonzero": {p: str(s_p[p]) for p in primes if s_p[p] != 0},
        "emptied_cells": sorted(int(cells[i]) for i in emptied),
        "emptied_cells_gain_per_unit": {int(cells[i]): str(moved_gain[i]) for i in sorted(emptied, key=lambda i: cells[i])},
        "cells_with_mass_kept": sorted(int(cells[i]) for i in cell_mass_terms if i in basis),
        "exchange_rates": {
            int(cells[i]): {int(cells[basis[k]]): str(row_sols[i][k]) for k in range(y) if row_sols[i][k] != 0}
            for i in sorted(emptied, key=lambda i: cells[i])
        },
        "seconds": time.time() - t0,
    }
    if verbose:
        print(f"N={N} y={y}: cells={nq} primes={len(primes)} psi={psiN:.6f}")
        print(f"  LP gain (float) = {gain_f:.9f}; support {len(support)} of y={y}; basis {out['basis_cells']}")
        print(f"  exact moment identities: OK for all {len(primes)} primes")
        print(f"  nu >= 0 by enclosure: {nonneg} (min lower endpoint {min_lower:.3e}); exactly-zero basis entries: {sum(zero_exact)}")
        print(f"  primal tight certificate feasible on Q_N: {primal_feasible}")
        print(f"  GAIN = T*-psi >= [{mpmath.nstr(lo(G), 40)}, {mpmath.nstr(hi(G), 40)}]  (width {float(hi(G) - lo(G)):.1e})")
        print(f"  emptied cells (mass fully moved): {out['emptied_cells']}")
        print(f"  gain per unit mass at emptied cells (= W_c(q)-1): {out['emptied_cells_gain_per_unit']}")
        print(f"  {time.time()-t0:.1f}s")
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--output", required=True)
    ap.add_argument("--dps", type=int, default=60)
    args = ap.parse_args()
    out = witness(args.N, args.y, dps=args.dps)
    with open(args.output, "w") as fh:
        json.dump(out, fh, indent=1)


if __name__ == "__main__":
    main()
