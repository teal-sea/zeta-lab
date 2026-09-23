"""Tasks 2 and 3: ground-state transport between windows on a fine c-grid.

Usage:  transport.py KIND N [c_lo c_hi denom]
        (defaults: c in [29, 32] step 1/16)

Per grid window c (exact dyadic), even sector, band N:
  cells[c]  lambda_1, lambda_2 (ball Rayleigh quotients of the inverse-
            iteration vectors), residual, edge amplitude mu_0 = sqrt(L) f(0);
            DH only: the zero-side split lambda = Q_1 + Q_2 + S_on(T<=120) + rest,
            with Q_k = 4 Re g_v(gamma_k - i delta_k) the off-line quadruples and
            S_on the on-line sum over the 64 cached float ordinates below 120.
  hf[c]     Hellmann-Feynman derivative d lambda / dL at fixed coefficient
            vector (the dilation picture), split into pole / arch / prime
            pieces by central differences at c(1 +- eps) (eps tiny, high prec).
            Only at non-integer c, so no coefficient enters inside the stencil.
  pairs     for c' = c + h, h in {1/16, 1/4, 1}:
            zero extension (centered, the transport under which the continuum
            form is invariant): overlap |<v', P v>|, ||P v||^2, RQ_{c'}(P v),
            where P v = G^T v is the projection of the zero-extended ground
            state onto the band-N space at c';
            dilation (same coefficient vector read in the c' basis): overlap
            v.v', and the exact finite-step sandwich
              R_{c'}(v') - R_c(v') <= lambda(c') - lambda(c) <= R_{c'}(v) - R_c(v)
            with both brackets split into pole / arch / prime_old (n <= c,
            positions rescaled) / prime_new (c < n <= c').
Checkpointed per cell into grid_<kind>_N<N>.json.
"""

from __future__ import annotations

import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import acb, arb, ctx, fmpq  # noqa: E402

KIND = sys.argv[1]
N = int(sys.argv[2])
C_LO = Fraction(sys.argv[3]) if len(sys.argv) > 3 else Fraction(29)
C_HI = Fraction(sys.argv[4]) if len(sys.argv) > 4 else Fraction(32)
DEN = int(sys.argv[5]) if len(sys.argv) > 5 else 16
STEPS = [Fraction(1, 16), Fraction(1, 4), Fraction(1)]
OUT = os.path.join(W.HERE, f"grid_{KIND}_N{N}.json")

# HF stencil: eps and precision chosen so O(eps^2) truncation and the
# 2^-prec/eps cancellation both sit far below |lambda| (DH ~1e-30, zeta ~1e-141).
HF = {"dh": (Fraction(1, 2**64), 600), "zeta": (Fraction(1, 2**250), 1600)}

ZEROS = [float(x) for x in json.load(open(os.path.join(W.ROOT, "data", "dh_zeros_online_T120.json")))["zeros"]]


def grid():
    c = C_LO
    step = Fraction(1, DEN)
    while c <= C_HI:
        yield c
        c += step


def key(c: Fraction) -> str:
    return str(c.numerator) if c.denominator == 1 else f"{c.numerator}/{c.denominator}"


_cache = {}


def ground(c: Fraction):
    """(bt, A, lam1, v1, lam2) at window c, cached for this run."""
    k = key(c)
    if k not in _cache:
        bt, A = W.build(W.cq(c), N, KIND)
        (r1, v1), (r2, _) = W.lowest_pairs(A, 2)
        _cache[k] = (bt, A, r1, v1, r2)
    return _cache[k]


def zero_side(v, L):
    q1 = W.offline_quadruple(v, L, W.GAMMA_OFF, W.DELTA_OFF)
    q2 = W.offline_quadruple(v, L, W.GAMMA_OFF2, W.DELTA_OFF2)
    s_on = arb(0)
    for g in ZEROS:
        F = W.F_even_acb(v, L, acb(arb(g)))
        s_on += 2 * (F * F).real / L
    return q1, q2, s_on


def cell(c: Fraction) -> dict:
    t0 = time.time()
    bt, A, r1, v1, r2 = ground(c)
    res = W.residual_norm(A, v1, r1)
    rec = {
        "c": key(c), "c_float": float(c), "L": W.fnum(bt.L),
        "band_edge": float(2 * 3.141592653589793 * N / W.fnum(bt.L)),
        "lam1": W.as_str(r1, 20), "lam2": W.as_str(r2, 8),
        "residual": res.str(3), "mu0": W.as_str(W.mu0(v1), 12),
        "v_head": [W.fnum(v1[i, 0]) for i in range(6)],
    }
    if KIND == "dh":
        q1, q2, s_on = zero_side(v1, bt.L)
        rec["zero_side"] = {
            "Q1": q1.str(10), "Q2": q2.str(10), "S_on_T120": s_on.str(10),
            "rest_lam_minus_Q1_Q2_Son": (r1 - q1 - q2 - s_on).str(6),
            "note": "float on-line ordinates (64 below 120), rho_1 to 50 digits, rho_2 to 10: measured",
        }
    rec["elapsed_s"] = round(time.time() - t0, 2)
    return rec


def hf(c: Fraction) -> dict | None:
    if c.denominator == 1:
        return None
    t0 = time.time()
    eps, prec = HF[KIND]
    _, _, r1, v1, _ = ground(c)
    ctx.prec = prec
    parts = {}
    Ls = []
    for sgn in (+1, -1):
        cc = c + sgn * eps
        bt = W.EN.BallTruncation(W.cq(cc), N, kind=KIND, prec=prec)
        comp = W.components(bt, check=False)
        Ls.append(bt.L)
        for name in ("pole", "arch", "prime"):
            M = comp[name]
            if M is None:
                continue
            ctx.prec = prec
            parts.setdefault(name, []).append(W.quad(M, v1))
    dL = Ls[0] - Ls[1]
    out = {name: (vals[0] - vals[1]) / dL for name, vals in parts.items()}
    tot = sum(out.values(), arb(0))
    rec = {name: val.str(12) for name, val in out.items()}
    rec["total_dlam_dL"] = tot.str(12)
    rec["eps"] = f"2^-{eps.denominator.bit_length() - 1}"
    rec["prec"] = prec
    rec["elapsed_s"] = round(time.time() - t0, 2)
    ctx.prec = W.prec_for(KIND, N)
    return rec


def pair(c: Fraction, c2: Fraction) -> dict:
    t0 = time.time()
    ctx.prec = W.prec_for(KIND, N)
    bt, A, r1, v1, _ = ground(c)
    bt2, A2, s1, w1, _ = ground(c2)
    ctx.prec = W.prec_for(KIND, N)
    # zero extension
    G = W.gram_zero_ext(W.cq(c), N, W.cq(c2), N)
    Pv = G.transpose() * v1
    nPv = W.dot(Pv, Pv)
    ov_ze = W.dot(w1, Pv)
    rq_ze = W.rq(A2, Pv)
    # dilation: same coefficients
    ov_dil = W.dot(w1, v1)
    comp2 = W.components(bt2, split=W.cq(c))
    comp1 = W.components(bt, split=W.cq(c))
    names = ["pole", "arch", "prime_old", "prime_new"]

    def piece(compA, compB, x, name):
        MA = compA.get(name)
        MB = compB.get(name)
        a = W.quad(MA, x) if MA is not None else arb(0)
        b = W.quad(MB, x) if MB is not None else arb(0)
        return a - b

    up = {n: piece(comp2, comp1, v1, n) for n in names if not (n == "pole" and KIND == "dh")}
    lo = {n: piece(comp2, comp1, w1, n) for n in names if not (n == "pole" and KIND == "dh")}
    up_tot = sum(up.values(), arb(0))
    lo_tot = sum(lo.values(), arb(0))
    dlam = s1 - r1
    rec = {
        "c": key(c), "c2": key(c2),
        "zero_ext": {
            "overlap_abs": abs(ov_ze).str(15),
            "one_minus_overlap": (1 - abs(ov_ze)).str(6),
            "proj_norm2": nPv.str(15),
            "rq_c2_of_projection": rq_ze.str(12),
            "rq_minus_lam_c": (rq_ze - r1).str(6),
            "note": "continuum identity: W(zero-extended f_c) = lambda(c) exactly; any deviation here is the band-N projection",
        },
        "dilation": {
            "overlap_abs": abs(ov_dil).str(15),
            "one_minus_overlap": (1 - abs(ov_dil)).str(6),
            "upper_bracket_Rc2(v)-lam(c)": up_tot.str(10),
            "upper_parts": {n: x.str(10) for n, x in up.items()},
            "lower_bracket_lam(c2)-Rc(v2)": lo_tot.str(10),
            "lower_parts": {n: x.str(10) for n, x in lo.items()},
        },
        "dlam": dlam.str(10),
        # rigorous comparisons: True only if certainly violated
        "sandwich_violated": bool((lo_tot > dlam) or (dlam > up_tot)),
        "elapsed_s": round(time.time() - t0, 2),
    }
    return rec


def main():
    d = W.load(OUT, {"meta": {"kind": KIND, "N": N, "sector": "even",
                              "grid": f"[{C_LO}, {C_HI}] step 1/{DEN}", "steps": [str(s) for s in STEPS]},
                     "cells": {}, "hf": {}, "pairs": {}})
    t_run = time.time()
    cs = list(grid())
    for c in cs:
        k = key(c)
        if k not in d["cells"]:
            d["cells"][k] = cell(c)
            W.save(OUT, d)
        if k not in d["hf"]:
            h = hf(c)
            if h is not None:
                d["hf"][k] = h
                W.save(OUT, d)
        for s in STEPS:
            c2 = c + s
            if c2 > C_HI:
                continue
            pk = f"{k}->{key(c2)}"
            if pk not in d["pairs"]:
                d["pairs"][pk] = pair(c, c2)
                W.save(OUT, d)
        rc = d["cells"][k]
        print(f"{KIND} N={N} c={k:>7}: lam1 {rc['lam1'][:28]} mu0 {rc['mu0'][:18]} "
              f"hf {d['hf'].get(k, {}).get('total_dlam_dL', '-')[:24]} [{time.time() - t_run:.0f}s]", flush=True)
    d["meta"]["elapsed_s_last_run"] = round(time.time() - t_run, 1)
    W.save(OUT, d)


if __name__ == "__main__":
    main()
