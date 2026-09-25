"""Follow-up 3, step 3: the QR route of ta_mellin.rho against its acceptance (RESULTS.md s10.2).

Writes ta_rho_check.json, one part per process. The acceptance was committed
(5b5a311) before any of this ran.

  a1 NVEC S [npz]  A1: rho (QR of the Gram factor) against rho_inv (inverse of
                   the formed G) at a delivered truncation, Z and B, with the
                   bound 10 eps cond(G) max|rho|; and the change of Delta_T on
                   the delivered (c, N) of that truncation.
  a2 [cache]       A2: at nvec 80 and S = 300 (and S = 200, 150, 120, looking for where it stops),
                   rho and rho_inv against a reference carried at raised
                   precision end to end: zeta^ at every s-node from kernel/'s
                   closed form (zeta_mellin_all, dps 30, no quadrature), J and
                   A at dps 30, G and the solve in Arb at 256 bits
                   (python-flint), rho on 64 of the s-nodes.
  a3 npz           A3: an entrywise relative perturbation of 2^-52 on Z, B, J,
                   A at (200, 2400), N = 32; spectral change of Delta_T, old
                   route against new (a proxy for the platform drift).
  a4 npz           A4: (200, 1200), N = 32, the regime of the 280, 319 and
                   364-mode rows: T_S's low eigenvalues by both routes, against
                   band(c, 32) of checker/ s7.7.
  gp NVEC S        the inventory item ta_gram_probe.json: its Delta_T by both
                   routes at one of its local truncations, and against the
                   committed value.

npz: the hats of TP.hats_modes(ProlateModes(200, 20), s_grid(2400, 1, 8), 1.0)
saved by the run of ta_rho_diag.py scan200 (the identical call). All grid
choices are delta_T_cells' (s-grid width 1, 8 nodes per panel). Float64
except the reference: measured grade.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from multiprocessing import Pool

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import ta_mellin as TM  # noqa: E402
import ta_prolate as TP  # noqa: E402

OUT = os.path.join(HERE, "ta_rho_check.json")
EPS = float(np.finfo(float).eps)
CELLS = ("2.2", "2.5", "2.9")
DELIVERED = {(80, 1200.0): (8, 16), (120, 1600.0): (16,), (200, 2400.0): (32,)}
# band(c, 32): checker/ RESULTS.md s7.7 (the 240-mode refinement response), read-only.
# That is the old-route band (3dc0a74), the one A4's acceptance was written against;
# checker/ s7.8 regraded the rows under the QR route (RESULTS.md s10.6).
BAND32 = {"2.2": 3.92e-2, "2.5": 2.37e-2, "2.9": 3.16e-2}


def load(nvec, S, npz=None, Smax=None):
    """(s, sw, Z, B, jz, jb, A) on s_grid(S, 1, 8); from npz (restricted to |s| <= S) or computed."""
    if npz:
        d = np.load(npz)
        m = np.abs(d["s"]) <= S + 1e-9
        return d["s"][m], d["sw"][m], d["Z"][:, m], d["B"][:, m], d["jz"], d["jb"], d["A"]
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    s, sw = TM.s_grid(S, width=1.0, per_panel=8)
    Z, B = TP.hats_modes(pm, s, 1.0)
    jz, jb = TP.jumps(pm, 1.0)
    return s, sw, Z, B, jz, jb, pm.derivs[:, 0] * pm.norm


def factors(data, S):
    s, sw, Z, B, jz, jb, A = data
    return TP.gram_factor_s(Z, sw, jz, S, A, 1.0), TP.gram_factor_s(B, sw, jb, S, A, 2.0)


def cond(F) -> float:
    sv = np.linalg.svd(F, compute_uv=False)
    return float(sv[0] / sv[-1])


def rhos(data, S, route):
    s, sw, Z, B, jz, jb, A = data
    Fz, Fb = factors(data, S)
    if route == "new":
        return TM.rho(Z, factor=Fz), TM.rho(B, factor=Fb)
    return TM.rho_inv(Z, np.conj(Fz.T) @ Fz), TM.rho_inv(B, np.conj(Fb.T) @ Fb)


def delta_T(data, rz, rb, c, N):
    s, sw = data[0], data[1]
    L = math.log(float(c))
    dT = TM.T_from_rho(rz, s, sw, L, N) - TM.T_from_rho(rb, s, sw, L, N)
    return ((dT + dT.conj().T) / 2).real


def a1(nvec, S, npz=None) -> dict:
    t0 = time.time()
    data = load(nvec, S, npz)
    Fz, Fb = factors(data, S)
    new, old = rhos(data, S, "new"), rhos(data, S, "old")
    out = {"nvec": nvec, "S": S, "cond_Fz": cond(Fz), "cond_Fb": cond(Fb)}
    for i, part in enumerate(("z", "b")):
        cF = out[f"cond_F{part}"]
        dev = float(np.abs(new[i] - old[i]).max())
        top = float(np.abs(new[i]).max())
        bound = 10 * EPS * cF**2 * top
        out[part] = {"max_dev": dev, "max_rho": top, "bound": bound, "ratio_to_eps_condG_rho": dev / (EPS * cF**2 * top)}
    out["dT_change_norm2"] = {f"{c}|{N}": float(np.linalg.norm(delta_T(data, *new, c, N) - delta_T(data, *old, c, N), 2))
                              for N in DELIVERED[(nvec, S)] for c in CELLS}
    out["seconds"] = round(time.time() - t0, 1)
    return out


# ---- A2: the raised-precision reference ----

def _closed_form(chunk):
    from mpmath import mp
    out = []
    for s0 in chunk:
        vals = TP.sonin.zeta_mellin_all(float(s0), 30, 0, 80)
        out.append([(mp.nstr(mp.re(v), 40), mp.nstr(mp.im(v), 40)) for v in vals])
    return out


def _edge_data(nvec=80, dps=30):
    """(J_n = zeta_n(1+), A_n = phi~_n(1) / sqrt(1 - lam_n^2)) as 40-digit strings."""
    from mpmath import mp
    son = TP.sonin
    J = son.sonin_z_all(1, dps, 0, nvec)
    pv, pd = son.prolate_vectors(dps, 0, nvec), son.prolate_data(dps, 0)
    with mp.workdps(dps + 10):
        lam = list(pd["lam"]) + [mp.mpf(0)] * nvec
        A = [mp.fsum(pv["coef"][n]) / mp.sqrt(1 - lam[n] ** 2) for n in range(nvec)]
        return [mp.nstr(x, 40) for x in J], [mp.nstr(x, 40) for x in A]


def a2(Ss=(300.0, 200.0, 150.0, 120.0), nvec=80, nsub=64, procs=2, cache=None) -> dict:
    """cache: optional path of a JSON file holding the reference samples (written if absent)."""
    import flint

    t0 = time.time()
    Smax = max(Ss)
    s_all, _ = TM.s_grid(Smax, width=1.0, per_panel=8)
    if cache and os.path.exists(cache):
        with open(cache) as fh:
            ref_hats, Js, As = json.load(fh)
    else:
        with Pool(procs) as pool:
            parts = pool.map(_closed_form, np.array_split(s_all, 4 * procs))
        ref_hats = [row for p in parts for row in p]  # per node: nvec (re, im) strings
        Js, As = _edge_data(nvec)
        if cache:
            with open(cache, "w") as fh:
                json.dump([ref_hats, Js, As], fh)
    t_ref = time.time() - t0
    flint.ctx.prec = 256
    out = {"nvec": nvec, "reference": "kernel/ zeta_mellin_all dps 30; Gram and solve in Arb at 256 bits",
           "seconds_reference_samples": round(t_ref, 1)}
    for S in Ss:
        t1 = time.time()
        data = load(nvec, S)
        s, sw, Z, B, jz, jb, A = data
        idx = np.where(np.abs(s_all) <= S + 1e-9)[0]
        assert np.array_equal(s_all[idx], s)
        # float64 samples against the reference samples
        Zr = np.array([[complex(float(a), float(b)) for a, b in ref_hats[i]] for i in idx]).T
        sample_dev = float(np.abs(Z - Zr).max())
        jr, ar = np.array([float(x) for x in Js]), np.array([float(x) for x in As])
        # reference factor, entirely from the reference samples, weights exact from the float grid
        wf = [flint.arb(float(w)) / (2 * flint.arb.pi()) for w in sw]
        rows = [[flint.acb(flint.arb(a), flint.arb(b)) * wf[k].sqrt() for a, b in ref_hats[i]] for k, i in enumerate(idx)]
        t = (1 / (flint.arb.pi() * flint.arb(float(S)))).sqrt()
        rows.append([flint.acb(flint.arb(x)) * t for x in Js])
        rows.append([flint.acb(flint.arb(x)) * t for x in As])
        Fr = flint.acb_mat(rows)
        G = Fr.conjugate().transpose() * Fr
        sub = idx[:: max(1, idx.size // nsub)][:nsub]
        pos = [int(np.where(idx == i)[0][0]) for i in sub]
        X = flint.acb_mat([[flint.acb(flint.arb(ref_hats[i][n][0]), -flint.arb(ref_hats[i][n][1])) for i in sub] for n in range(nvec)])
        Y = G.solve(X)
        rho_ref = np.array([float(sum((X[n, j].conjugate() * Y[n, j]).real for n in range(nvec))) for j in range(len(sub))])
        Fz = TP.gram_factor_s(Z, sw, jz, S, A, 1.0)
        new = TM.rho(Z, factor=Fz)[pos]
        old = TM.rho_inv(Z, np.conj(Fz.T) @ Fz)[pos]
        scale = float(np.abs(rho_ref).max())
        out[str(int(S))] = {
            "S": S, "cond_Fz": cond(Fz), "n_nodes": int(idx.size), "n_compared": len(sub),
            "sample_max_abs_dev": sample_dev, "J_max_abs_dev": float(np.abs(jz - jr).max()),
            "A_max_abs_dev": float(np.abs(A - ar).max()), "max_rho_ref": scale,
            "new_max_rel_dev": float(np.abs(new - rho_ref).max() / scale),
            "old_max_rel_dev": float(np.abs(old - rho_ref).max() / scale),
            "seconds": round(time.time() - t1, 1),
        }
    return out


def _perturb(x, rng, eps):
    x = np.asarray(x)
    u = np.exp(2j * np.pi * rng.random(x.shape)) if np.iscomplexobj(x) else rng.choice([-1.0, 1.0], x.shape)
    return x * (1 + eps * u)


def a3(npz, seed=7) -> dict:
    data = load(200, 2400.0, npz)
    rng = np.random.default_rng(seed)
    s, sw, Z, B, jz, jb, A = data
    pdata = (s, sw, _perturb(Z, rng, 2.0**-52), _perturb(B, rng, 2.0**-52), _perturb(jz, rng, 2.0**-52),
             _perturb(jb, rng, 2.0**-52), _perturb(A, rng, 2.0**-52))
    out = {"nvec": 200, "S": 2400.0, "N": 32, "rel_perturbation": 2.0**-52, "seed": seed}
    for route in ("old", "new"):
        r0, r1 = rhos(data, 2400.0, route), rhos(pdata, 2400.0, route)
        out[route] = {c: float(np.linalg.norm(delta_T(pdata, *r1, c, 32) - delta_T(data, *r0, c, 32), 2)) for c in CELLS}
    return out


def a4(npz) -> dict:
    import ta_ts as T

    kp = T.KernelProvider()
    lo, hi = load(200, 1200.0, npz), load(200, 2400.0, npz)
    Fz, Fb = factors(lo, 1200.0)
    out = {"nvec": 200, "S": 1200.0, "N": 32, "cond_Fz": cond(Fz), "cond_Fb": cond(Fb), "band": BAND32, "cells": {}}
    new_lo, old_lo, new_hi = rhos(lo, 1200.0, "new"), rhos(lo, 1200.0, "old"), rhos(hi, 2400.0, "new")
    for c in CELLS:
        Tinf = kp.T_inf_matrix(c, 32, 40)
        TS = {k: Tinf + delta_T(d, *r, c, 32) for k, d, r in (("new", lo, new_lo), ("old", lo, old_lo), ("new_2400", hi, new_hi))}
        ev = {k: np.linalg.eigvalsh(v) for k, v in TS.items()}
        out["cells"][c] = {
            "new_low3": [float(x) for x in ev["new"][:3]], "old_low3": [float(x) for x in ev["old"][:3]],
            "new_n_below_band": int((ev["new"] < -BAND32[c]).sum()), "old_n_below_band": int((ev["old"] < -BAND32[c]).sum()),
            "new_2400_low3": [float(x) for x in ev["new_2400"][:3]],
            "new_S_response_norm2": float(np.linalg.norm(TS["new"] - TS["new_2400"], 2)),
        }
    return out


def gp(nvec, S) -> dict:
    """ta_gram_probe.json's dependence on rho: its Delta_T (c = 2.2, N = 8, s-grid width 2)
    by both routes at one of its local truncations, and the factor conditions."""
    import ta_gram_probe as GP

    t0 = time.time()
    pm = TP.ProlateModes(nvec=nvec, dps=20)
    s, sw, Z, B, Fz, Fb = GP.grams(pm, S)
    new = GP.delta_T(s, sw, Z, B, Fz, Fb)
    L = math.log(float(GP.C))
    Mi = TM.T_from_rho(TM.rho_inv(Z, np.conj(Fz.T) @ Fz), s, sw, L, GP.N)
    Ms = TM.T_from_rho(TM.rho_inv(B, np.conj(Fb.T) @ Fb), s, sw, L, GP.N)
    old = ((Mi - Ms) + (Mi - Ms).conj().T).real / 2
    with open(os.path.join(HERE, "ta_gram_probe.json")) as fh:
        committed = np.array(json.load(fh)["runs"][f"{nvec},{int(S)}"]["dT"])
    return {"nvec": nvec, "S": S, "cond_Fz": cond(Fz), "cond_Fb": cond(Fb),
            "dT_new_minus_old_norm2": float(np.linalg.norm(new - old, 2)),
            "dT_new_minus_committed_max_abs": float(np.abs(new - committed).max()),
            "seconds": round(time.time() - t0, 1)}


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    try:
        with open(OUT) as fh:
            out = json.load(fh)
    except (OSError, ValueError):
        out = {}
    out["eps"] = EPS
    part = argv[0]
    if part == "a1":
        nvec, S = int(argv[1]), float(argv[2])
        out.setdefault("A1", {})[f"{nvec},{int(S)}"] = a1(nvec, S, argv[3] if len(argv) > 3 else None)
    elif part == "a2":
        out["A2"] = a2(cache=argv[1] if len(argv) > 1 else None)
    elif part == "a3":
        out["A3"] = a3(argv[1])
    elif part == "a4":
        out["A4"] = a4(argv[1])
    elif part == "gp":
        nvec, S = int(argv[1]), float(argv[2])
        out.setdefault("gram_probe_dependence", {})[f"{nvec},{int(S)}"] = gp(nvec, S)
    with open(OUT, "w") as fh:
        json.dump(out, fh, indent=1)
    return out


if __name__ == "__main__":
    main()
