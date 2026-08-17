"""Enclosure-checked smallest-eigenvalue table over the (c, N) grid.

For each cell, three independent rigorous statements about the even sector
(and inertia for the odd sector):

* matrix inertia at shift 0 from a ball LDL^T (n_neg = 0 means every
  eigenvalue is strictly positive, rigorously);
* a bracket [LDL lower shift, Rayleigh upper] around lambda_min;
* python-flint acb_mat.eig (Rump) enclosure of lambda_min.

Emits ``enclosures.json``.  Hardened grade: enclosure-carrying arithmetic
on every step after the (exact, cited) closed-form entry formulas.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.getcwd())

from mpmath import mp  # noqa: E402

import galerkin as G  # noqa: E402
import enclosures as EN  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))

CELLS = [(c, N) for c in (6, 9, 13, 19, 29) for N in (4, 8, 16, 32)]


def one_cell(c, N, kind="zeta"):
    # float pass for the precision policy and the Rayleigh vector
    with mp.workdps(60):
        t = G.Truncation(c, N, kind=kind)
        ev, vecs = G.eigsy_sorted(t.even_matrix())
        lam0 = float(ev[0])
    digits = abs(math.log10(abs(lam0))) if lam0 else 40
    if digits + 45 > 55:  # second float pass at enough precision
        with mp.workdps(int(digits) + 45):
            t = G.Truncation(c, N, kind=kind)
            ev, vecs = G.eigsy_sorted(t.even_matrix())
            lam0 = float(ev[0])
            digits = abs(math.log10(abs(lam0)))
    prec = int(3.4 * (digits + 45)) + 120
    bt = EN.BallTruncation(c, N, kind=kind, prec=prec)
    M = bt.even_matrix()
    npos, nneg, concl = EN.ldlt_inertia(M)
    res = EN.lambda_min_enclosure(M, lam0, prec)
    up = EN.rayleigh_upper(M, [float(x) for x in vecs[0]])
    eigs = EN.eig_enclosures(M, prec)
    lam_ball = eigs[0].real if eigs else None
    Mo = bt.odd_matrix()
    nposo, nnego, conclo = EN.ldlt_inertia(Mo)
    lo = res["lower"]
    out = {
        "c": c,
        "N": N,
        "kind": kind,
        "prec_bits": prec,
        "even_inertia_at_0": [npos, nneg, bool(concl)],
        "odd_inertia_at_0": [nposo, nnego, bool(conclo)],
        "lambda_min_float": lam0,
        "ldl_lower": str(lo) if lo is not None else None,
        "rayleigh_upper": str(up),
        "eig_ball_mid": str(lam_ball.mid()) if lam_ball is not None else None,
        "eig_ball_rad": float(lam_ball.rad()) if lam_ball is not None else None,
        "consistent": None,
    }
    if lam_ball is not None and lo is not None:
        # both routes contain lambda_min, so they must intersect:
        # eig ball vs [ldl_lower, rayleigh_upper]
        ok = (lam_ball.mid() + lam_ball.rad() > lo) and (
            lam_ball.mid() - lam_ball.rad() < up
        )
        out["consistent"] = bool(ok)
    return out


def main():
    t0 = time.time()
    rows = []
    for c, N in CELLS:
        r = one_cell(c, N)
        rows.append(r)
        print(
            f"c={c:3d} N={N:3d} prec={r['prec_bits']:5d} "
            f"inertia_even={tuple(r['even_inertia_at_0'])} "
            f"inertia_odd={tuple(r['odd_inertia_at_0'])} "
            f"lam_min={r['lambda_min_float']:.3e} rad={r['eig_ball_rad']:.1e} "
            f"consistent={r['consistent']}",
            flush=True,
        )
    out = {"cells": rows, "elapsed_s": round(time.time() - t0, 1)}
    with open(os.path.join(HERE, "enclosures.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote enclosures.json in", out["elapsed_s"], "s")


if __name__ == "__main__":
    main()
