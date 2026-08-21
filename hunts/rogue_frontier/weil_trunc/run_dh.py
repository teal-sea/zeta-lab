"""Battery discipline: the same truncation pipeline on Davenport-Heilbronn.

The DH function satisfies a Riemann-type functional equation, has real
coefficients and a real Hardy-style Z, and violates the RH analogue
(zeta/epstein.py; docs/09 gate #3).  The construction ports (SOURCE.md s4):
prime block from Lambda_f (log-derivative recursion, supported on ALL
n >= 2), no pole block, archimedean density Re psi(3/4 + i r/2) - log(pi/5).

Questions measured here:

1. Is the DH truncated form positive over the grid (its continuum Weil
   positivity is FALSE), and if so, how does lambda_min(c, N) compare with
   zeta's?
2. Does the DH ground state extract DH's on-line ordinates the way zeta's
   extracts gamma_k, and at what accuracy?
3. Any negative eigenvalue gets an enclosure check before being believed.

Emits ``dh_control.json``.
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

C_LIST = [6, 9, 13, 19, 29, 37, 47]
N_LIST = [4, 8, 16, 32]


def dh_ordinates(k: int = 10, dps: int = 40):
    """First k DH on-line ordinates, refined with zeta.epstein.Z_dh.

    Seeds from the lab's cached scan (data/dh_zeros_online_T120.json,
    read-only), then bisects Z_dh at working precision.
    """
    from zeta.epstein import Z_dh

    seeds = json.load(open("data/dh_zeros_online_T120.json"))["zeros"][:k]
    out = []
    with mp.workdps(dps):
        for s in seeds:
            lo, hi = mp.mpf(s) - mp.mpf("0.01"), mp.mpf(s) + mp.mpf("0.01")
            flo = Z_dh(lo, dps=dps)
            fhi = Z_dh(hi, dps=dps)
            if flo * fhi > 0:
                out.append(mp.mpf(s))  # keep the seed; note low precision
                continue
            for _ in range(int(dps * 3.4) + 10):
                mid = (lo + hi) / 2
                fm = Z_dh(mid, dps=dps)
                if fm == 0:
                    lo = hi = mid
                    break
                if flo * fm < 0:
                    hi = mid
                else:
                    lo, flo = mid, fm
            out.append((lo + hi) / 2)
    return out


def cell(c, N, dps, gams_dh, zmax=52):
    with mp.workdps(dps):
        t = G.Truncation(c, N, kind="dh")
        E = t.even_matrix()
        ev_e, vec_e = G.eigsy_sorted(E)
        O = t.odd_matrix()
        ev_o, vec_o = G.eigsy_sorted(O)
        n_neg_e = sum(1 for x in ev_e if x < 0)
        n_neg_o = sum(1 for x in ev_o if x < 0)
        F = G.F_even(vec_e[0], t.L)
        zs = G.find_zeros(F, mp.mpf(2), mp.mpf(zmax), step=mp.mpf("0.2"))
        errs = []
        for gm in gams_dh:
            if gm > zmax - 2:
                break
            best = min((abs(z - gm) for z in zs), default=None)
            errs.append(float(best) if best is not None else None)
        return {
            "c": c,
            "N": N,
            "dps": dps,
            "lambda_min_even": float(ev_e[0]),
            "lambda_min_odd": float(ev_o[0]),
            "n_neg_even": n_neg_e,
            "n_neg_odd": n_neg_o,
            "spectrum_head_even": [float(x) for x in ev_e[:4]],
            "dh_gamma_errors": errs,
            "n_extracted_zeros": len(zs),
        }


def dps_for(c, N):
    guess = 10 + 1.6 * N + 0.35 * c * (N / 32) ** 0.5
    return int(max(40, min(300, guess + 30)))


def main():
    t0 = time.time()
    print("refining DH on-line ordinates with zeta.epstein.Z_dh ...", flush=True)
    gams = dh_ordinates(k=10, dps=60)
    print("  first DH ordinates:", [mp.nstr(g, 12) for g in gams[:5]], flush=True)
    rows = []
    negatives = []
    for c in C_LIST:
        for N in N_LIST:
            d = dps_for(c, N)
            r = cell(c, N, d, gams)
            rows.append(r)
            print(
                f"c={c:3d} N={N:3d} dps={d:3d}: lam_e={r['lambda_min_even']:.3e} "
                f"lam_o={r['lambda_min_odd']:.3e} "
                f"g1err={r['dh_gamma_errors'][0] if r['dh_gamma_errors'] else None} "
                f"nneg=({r['n_neg_even']},{r['n_neg_odd']})",
                flush=True,
            )
            if r["n_neg_even"] or r["n_neg_odd"]:
                negatives.append((c, N))
    encl = []
    if negatives:
        print("negative eigenvalues seen; running ball enclosures:", negatives, flush=True)
        import math
        import enclosures as EN

        for c, N in negatives:
            with mp.workdps(dps_for(c, N)):
                t = G.Truncation(c, N, kind="dh")
                ev_e, _ = G.eigsy_sorted(t.even_matrix())
                lam0 = float(ev_e[0])
            digits = abs(math.log10(abs(lam0))) if lam0 else 40
            prec = int(3.4 * (digits + 45)) + 120
            bt = EN.BallTruncation(c, N, kind="dh", prec=prec)
            npos, nneg, concl = EN.ldlt_inertia(bt.even_matrix())
            nposo, nnego, conclo = EN.ldlt_inertia(bt.odd_matrix())
            encl.append(
                {
                    "c": c,
                    "N": N,
                    "prec_bits": prec,
                    "even_inertia_at_0": [npos, nneg, bool(concl)],
                    "odd_inertia_at_0": [nposo, nnego, bool(conclo)],
                }
            )
            print(f"  (c={c},N={N}): even inertia {npos},{nneg},{concl}; "
                  f"odd {nposo},{nnego},{conclo}", flush=True)
    out = {
        "dh_ordinates_dps40": [mp.nstr(g, 30) for g in gams],
        "grid": rows,
        "negative_cells_enclosures": encl,
        "elapsed_s": round(time.time() - t0, 1),
    }
    with open(os.path.join(HERE, "dh_control.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote dh_control.json in", out["elapsed_s"], "s")


if __name__ == "__main__":
    main()
