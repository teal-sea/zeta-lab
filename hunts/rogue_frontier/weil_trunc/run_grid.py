"""Float-route (c, N) grid for zeta: lambda_min both sectors, ground-state
zero extraction against gamma_1..gamma_5, N-saturation ladder at c = 13.

Emits ``grid.json``.  Measured grade only; enclosures are run_enclosures.py.
"""

from __future__ import annotations

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.getcwd())

from mpmath import mp  # noqa: E402

import galerkin as G  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))

C_LIST = [6, 7, 9, 11, 13, 17, 19, 23, 29, 31, 37]
N_LIST = [4, 8, 16, 24, 32]
N_LADDER_C13 = [4, 8, 12, 16, 20, 24, 32, 40, 48, 64]

GAMMAS = None  # loaded once


def load_gammas(k=12):
    """Reference ordinates at dps 130 (mpmath.zetazero; generated locally so
    the comparison is never floored by the repo's dps-30 cache)."""
    global GAMMAS
    if GAMMAS is None:
        path = os.path.join(HERE, "gammas_dps130.json")
        zeros = json.load(open(path))["zeros"]
        with mp.workdps(135):  # parse at full stored precision, NOT the
            GAMMAS = [mp.mpf(z) for z in zeros[:k]]  # ambient cell dps
    return GAMMAS


def cell(c, N, dps, kind="zeta", zmax=52):
    """One grid cell at working precision dps: spectra + zero errors."""
    with mp.workdps(dps):
        t = G.Truncation(c, N, kind=kind)
        E = t.even_matrix()
        ev_e, vec_e = G.eigsy_sorted(E)
        O = t.odd_matrix()
        ev_o, vec_o = G.eigsy_sorted(O)
        lam_e, lam_o = ev_e[0], ev_o[0]
        n_neg_e = sum(1 for x in ev_e if x < 0)
        n_neg_o = sum(1 for x in ev_o if x < 0)
        # ground-state zero extraction (even sector)
        F = G.F_even(vec_e[0], t.L)
        zs = G.find_zeros(F, mp.mpf(2), mp.mpf(zmax), step=mp.mpf("0.2"))
        gams = load_gammas()
        errs = []
        for gm in gams:
            if gm > zmax - 2:
                break
            best = min((abs(z - gm) for z in zs), default=None)
            errs.append(float(best) if best is not None else None)
        out = {
            "c": c,
            "N": N,
            "dps": dps,
            "lambda_min_even": float(lam_e),
            "lambda_min_odd": float(lam_o),
            "n_neg_even": n_neg_e,
            "n_neg_odd": n_neg_o,
            "log10_lambda_min_even": float(mp.log10(abs(lam_e))) if lam_e != 0 else None,
            "gamma_errors": errs,
            "log10_gamma1_err": float(mp.log10(errs[0])) if errs and errs[0] else None,
            "n_extracted_zeros": len(zs),
        }
    return out


def dps_for(c, N):
    """Working precision: generous headroom over the expected lambda_min."""
    # empirical: |log10 lambda_min| grows with both c and N; be generous.
    guess = 10 + 1.6 * N + 0.35 * c * (N / 32) ** 0.5
    return int(max(40, min(300, guess + 30)))


def main():
    t0 = time.time()
    results = []
    for c in C_LIST:
        for N in N_LIST:
            d = dps_for(c, N)
            r = cell(c, N, d)
            results.append(r)
            print(
                f"c={c:3d} N={N:3d} dps={d:3d}: lam_e={r['lambda_min_even']:.3e} "
                f"lam_o={r['lambda_min_odd']:.3e} g1err={r['gamma_errors'][0]:.2e} "
                f"nneg=({r['n_neg_even']},{r['n_neg_odd']})",
                flush=True,
            )
    ladder = []
    for N in N_LADDER_C13:
        d = dps_for(13, N)
        r = cell(13, N, d)
        ladder.append(r)
        print(
            f"[ladder c=13] N={N:3d} dps={d}: lam_e={r['lambda_min_even']:.3e} "
            f"g1err={r['gamma_errors'][0]:.2e}",
            flush=True,
        )
    out = {"grid": results, "ladder_c13": ladder, "elapsed_s": round(time.time() - t0, 1)}
    with open(os.path.join(HERE, "grid.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote grid.json in", out["elapsed_s"], "s")


if __name__ == "__main__":
    main()
