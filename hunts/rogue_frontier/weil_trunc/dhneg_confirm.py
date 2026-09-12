"""Confirmation package for the first negative cell of the DH truncated form.

Stages (all checkpointed to dhneg_scan.json as they complete):

1. deep ladders: c = 29 and 30 pushed to N = 256, c = 31 to N = 192, so the
   'first cell' claim carries an explicit search ceiling.
2. float scout at the crossing: independent mpmath route (galerkin.py)
   eigenvalues at (31, 59) and (31, 60).
3. lambda_min trajectories for c = 31, 32, 33 across the crossing, and a
   c-slice at N = 128 for c = 28..36.
4. enclosure package at (c*, N*) = (31, 60): ball LDL inertia at shift 0,
   a Rayleigh upper bound on lambda_min from a recorded dyadic vector
   (upper ball endpoint strictly below zero), and Rump eig enclosures.
5. zeta control at (31, 60): same assembly, zeta data; ball LDL inertia
   (expect all positive) and smallest-eigenvalue enclosure.
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "..", ".."))

from flint import acb, acb_mat, arb, ctx  # noqa: E402
from mpmath import mp  # noqa: E402

import enclosures as EN  # noqa: E402
import galerkin as G  # noqa: E402
from dhneg_scan import load_scan, save_scan, pivot_signs, first_neg_from_signs  # noqa: E402

CSTAR, NSTAR = 31, 60


def log(msg):
    print(msg, flush=True)


def put(path_keys, value):
    d = load_scan()
    cur = d
    for k in path_keys[:-1]:
        cur = cur.setdefault(k, {})
    cur[path_keys[-1]] = value
    save_scan(d)


# ---------------------------------------------------------------------------
# 1. deep ladders
# ---------------------------------------------------------------------------


def deep_ladders():
    for c, Nmax in ((29, 256), (30, 256), (31, 192)):
        t0 = time.time()
        bt = EN.BallTruncation(c, Nmax, kind="dh", prec=600)
        se, ce = pivot_signs(bt.even_matrix(), 600)
        so, co = pivot_signs(bt.odd_matrix(), 600)
        rec = {
            "c": c,
            "Nmax": Nmax,
            "prec": 600,
            "conclusive_even": bool(ce),
            "conclusive_odd": bool(co),
            "n_neg_even": sum(1 for s in se if s < 0),
            "n_neg_odd": sum(1 for s in so if s < 0),
            "first_neg_N_even": first_neg_from_signs(se, "even"),
            "first_neg_N_odd": first_neg_from_signs(so, "odd"),
            "elapsed_s": round(time.time() - t0, 1),
        }
        put(["ladders_deep", str(c)], rec)
        log(f"deep c={c} Nmax={Nmax}: first_neg even={rec['first_neg_N_even']} "
            f"odd={rec['first_neg_N_odd']} n_neg=({rec['n_neg_even']},"
            f"{rec['n_neg_odd']}) concl=({ce},{co}) [{rec['elapsed_s']}s]")


# ---------------------------------------------------------------------------
# 2. float scout at the crossing (independent mpmath route)
# ---------------------------------------------------------------------------


def crossing_scout():
    for c, N in ((CSTAR, NSTAR - 1), (CSTAR, NSTAR), (CSTAR, 64)):
        t0 = time.time()
        with mp.workdps(60):
            t = G.Truncation(c, N, kind="dh")
            ev, vecs = G.eigsy_sorted(t.even_matrix())
            rec = {
                "c": c,
                "N": N,
                "dps": 60,
                "lambda_min_even": mp.nstr(ev[0], 20),
                "next_eigs": [mp.nstr(x, 8) for x in ev[1:4]],
                "n_neg_even": sum(1 for x in ev if x < 0),
                "elapsed_s": round(time.time() - t0, 1),
            }
        put(["crossing_scout", f"{c},{N}"], rec)
        log(f"scout ({c},{N}): lam_min={rec['lambda_min_even']} "
            f"n_neg={rec['n_neg_even']} [{rec['elapsed_s']}s]")
        if (c, N) == (CSTAR, NSTAR):
            v0 = [float(x) for x in vecs[0]]
            put(["confirm_cell", "rayleigh_vector_float64"], v0)
            # exact dyadic snapshot of the dps-60 eigenvector: each mpf is
            # sign*man*2^exp exactly; recorded as [signed_man, exp] pairs
            dyadic = []
            for x in vecs[0]:
                sign, man, exp, _ = mp.mpf(x)._mpf_
                dyadic.append([str(-man if sign else man), int(exp)])
            put(["confirm_cell", "rayleigh_vector_dyadic"], dyadic)


# ---------------------------------------------------------------------------
# 3. trajectories across the crossing + c-slice at N = 128
# ---------------------------------------------------------------------------


def eig_min_of(bt_matrix, n, prec):
    ctx.prec = prec
    A = acb_mat([[acb(bt_matrix[i][j]) for j in range(n)] for i in range(n)])
    E = A.eig(nonstop=True, multiple=True)
    lo = min(E, key=lambda e: float(e.real.mid()))
    return str(lo.real.mid()), float(lo.real.rad())


def crossing_trajectories():
    plans = {
        31: [40, 44, 48, 52, 56, 58, 59, 60, 61, 62, 64, 72, 80, 96, 128, 160, 192],
        32: [40, 44, 48, 49, 50, 52, 56, 64, 96, 128],
        33: [40, 44, 46, 47, 48, 52, 56, 64, 96, 128],
    }
    for c, Ns in plans.items():
        Nmax = max(Ns)
        bt = EN.BallTruncation(c, Nmax, kind="dh", prec=600)
        M = bt.even_matrix()
        for N in Ns:
            mid, rad = eig_min_of(M, N + 1, 600)
            pt = {
                "kind": "dh", "sector": "even", "c": c, "N": N,
                "prec": 600, "lam_min_mid": mid, "lam_min_rad": rad,
            }
            d = load_scan()
            d["trajectories"].append(pt)
            save_scan(d)
            log(f"traj c={c} N={N}: {mid[:26]}")


def c_slice():
    for c in range(28, 37):
        bt = EN.BallTruncation(c, 128, kind="dh", prec=600)
        M = bt.even_matrix()
        mid, rad = eig_min_of(M, 129, 600)
        put(["c_slice_N128", str(c)], {"lam_min_mid": mid, "lam_min_rad": rad})
        log(f"c-slice c={c} N=128: {mid[:26]}")


# ---------------------------------------------------------------------------
# 4. enclosure package at (31, 60)
# ---------------------------------------------------------------------------


def confirm_cell():
    prec = 700
    t0 = time.time()
    bt = EN.BallTruncation(CSTAR, NSTAR, kind="dh", prec=prec)
    Me = bt.even_matrix()
    Mo = bt.odd_matrix()
    se, ce = pivot_signs(Me, prec)
    so, co = pivot_signs(Mo, prec)
    rec = {
        "c": CSTAR, "N": NSTAR, "prec": prec,
        "even_inertia_at_0": [sum(1 for s in se if s > 0),
                              sum(1 for s in se if s < 0), bool(ce)],
        "odd_inertia_at_0": [sum(1 for s in so if s > 0),
                             sum(1 for s in so if s < 0), bool(co)],
    }
    # Rayleigh upper bound from the recorded exact-dyadic vector: the
    # quadratic form of ANY nonzero vector bounds lambda_min from above,
    # so an upper ball endpoint below zero is a rigorous negativity claim
    # regardless of where the vector came from.
    d = load_scan()
    dyadic = d["confirm_cell"]["rayleigh_vector_dyadic"]
    ctx.prec = prec
    v = [arb(int(mstr)) * (arb(2) ** e) for mstr, e in dyadic]
    num = arb(0)
    n = len(Me)
    for i in range(n):
        for j in range(n):
            num += v[i] * Me[i][j] * v[j]
    den = sum((x * x for x in v), arb(0))
    q = num / den
    up = q.mid() + q.rad()
    rec["rayleigh_quotient_mid"] = str(q.mid())
    rec["rayleigh_upper_endpoint"] = str(up)
    rec["rayleigh_upper_is_negative"] = bool(up < 0)
    # Rump eig enclosures of the full even sector
    eigs = EN.eig_enclosures(Me, prec)
    if eigs is not None:
        lo = eigs[0].real
        rec["eig_rump_min_mid"] = str(lo.mid())
        rec["eig_rump_min_rad"] = float(lo.rad())
        rec["eig_rump_min_strictly_negative"] = bool(lo.mid() + lo.rad() < 0)
        rec["eig_rump_next_mid"] = str(eigs[1].real.mid())
    rec["elapsed_s"] = round(time.time() - t0, 1)
    for k, v in rec.items():
        put(["confirm_cell", k], v)
    log(f"confirm (31,60): even inertia {rec['even_inertia_at_0']} "
        f"odd {rec['odd_inertia_at_0']} rayleigh_up={rec['rayleigh_upper_endpoint'][:24]} "
        f"rump_min={rec.get('eig_rump_min_mid','?')[:24]}+/-{rec.get('eig_rump_min_rad')}")


# ---------------------------------------------------------------------------
# 5. zeta control at (31, 60)
# ---------------------------------------------------------------------------


def zeta_control(prec: int = 2400):
    # prec note: zeta's floor at (31, 60) is ~5e-100, so LDL elimination
    # entries reach ~1e100 and the pivot-ball radii pick up ~200 decimal
    # digits of cascade error; prec 700 was inconclusive at pivot 51,
    # prec 2400 leaves ~500 digits of headroom.
    t0 = time.time()
    bt = EN.BallTruncation(CSTAR, NSTAR, kind="zeta", prec=prec)
    Me = bt.even_matrix()
    Mo = bt.odd_matrix()
    se, ce = pivot_signs(Me, prec)
    so, co = pivot_signs(Mo, prec)
    rec = {
        "c": CSTAR, "N": NSTAR, "prec": prec,
        "even_inertia_at_0": [sum(1 for s in se if s > 0),
                              sum(1 for s in se if s < 0), bool(ce)],
        "odd_inertia_at_0": [sum(1 for s in so if s > 0),
                             sum(1 for s in so if s < 0), bool(co)],
    }
    mid, rad = eig_min_of(Me, NSTAR + 1, prec)
    rec["lam_min_mid"] = mid
    rec["lam_min_rad"] = rad
    rec["elapsed_s"] = round(time.time() - t0, 1)
    put(["zeta_control"], rec)
    log(f"zeta control (31,60): even inertia {rec['even_inertia_at_0']} "
        f"odd {rec['odd_inertia_at_0']} lam_min={mid[:26]} [{rec['elapsed_s']}s]")


if __name__ == "__main__":
    stages = sys.argv[1:] or ["deep", "scout", "traj", "cslice", "confirm", "control"]
    if "deep" in stages:
        deep_ladders()
    if "scout" in stages:
        crossing_scout()
    if "traj" in stages:
        crossing_trajectories()
    if "cslice" in stages:
        c_slice()
    if "confirm" in stages:
        confirm_cell()
    if "control" in stages:
        zeta_control()
