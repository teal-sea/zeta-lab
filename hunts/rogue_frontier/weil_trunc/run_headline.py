"""The (c, N) = (13, 100) headline cell, cutoff-free, vs G1 Table 3.

G1 (T = 800, N = 100, dps 150/200): lambda_min^even = 2.865e-59,
|gamma_1 error| = 2.005e-55.  Our entries are cutoff-free (T = infinity),
so lambda_min must come out slightly ABOVE the T = 800 value (the omitted
archimedean tail is positive definite, G2 Thm 3.2), and the gamma_1 error
should land inside the published cluster 2.0e-55 .. 2.6e-55.

Also runs (14, 100) against G1 Table 3 (4.835e-65 / 3.541e-61) and the CCM
c = 13, N = 120 comparison value 2.44e-55.  Emits ``headline.json``.
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


def one(c, N, dps):
    t0 = time.time()
    with mp.workdps(dps):
        t = G.Truncation(c, N)
        E = t.even_matrix()
        ev, vecs = G.eigsy_sorted(E)
        lam = ev[0]
        n_neg = sum(1 for x in ev if x < 0)
        F = G.F_even(vecs[0], t.L)
        # gamma_1 = 14.1347...; bracket tightly and bisect
        zs = G.find_zeros(F, mp.mpf(13), mp.mpf(15), step=mp.mpf("0.1"))
        g1 = mp.mpf(json.load(open(os.path.join(HERE, "gammas_dps130.json")))["zeros"][0])
        err = min(abs(z - g1) for z in zs) if zs else None
        # first ten zeros
        gams = [mp.mpf(z) for z in json.load(open(os.path.join(HERE, "gammas_dps130.json")))["zeros"][:10]]
        zs_all = G.find_zeros(F, mp.mpf(10), mp.mpf(50), step=mp.mpf("0.15"))
        errs = [float(min(abs(z - gm) for z in zs_all)) for gm in gams if gm < 49]
    return {
        "c": c,
        "N": N,
        "dps": dps,
        "lambda_min_even": mp.nstr(lam, 8),
        "n_neg_even": n_neg,
        "gamma1_abs_err": mp.nstr(err, 8) if err is not None else None,
        "log10_gamma1_err": float(mp.log10(err)) if err else None,
        "gamma_errors_first": [f"{e:.3e}" for e in errs],
        "elapsed_s": round(time.time() - t0, 1),
    }


def main():
    out = {}
    r13 = one(13, 100, 200)
    out["c13_N100"] = r13
    out["published_c13_N100_T800"] = {"lambda_min": 2.865e-59, "gamma1_err": 2.005e-55}
    out["published_cluster_c13"] = [2.005e-55, 2.44e-55, 2.5e-55, 2.6e-55]
    print(json.dumps(r13, indent=1), flush=True)
    r14 = one(14, 100, 200)
    out["c14_N100"] = r14
    out["published_c14_N100_T800"] = {"lambda_min": 4.835e-65, "gamma1_err": 3.541e-61}
    print(json.dumps(r14, indent=1), flush=True)
    with open(os.path.join(HERE, "headline.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote headline.json")


if __name__ == "__main__":
    main()
