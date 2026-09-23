"""Task 1: reproduce recorded lambda_min cells before building on the solver.

Route A (used everywhere downstream): Arb assembly imported from
weil_trunc/enclosures.py, inverse iteration on the midpoint matrix, ball
Rayleigh quotient of the resulting exact vector, and a Temple bracket from a
ball LDL^T at a shift between lambda_1 and lambda_2 (both ends rigorous).

Route B (independent code path, float grade): weil_trunc/galerkin.py mpmath
assembly + mp.eigsy, at a few cells including NON-integer c, which the
record never used; this is the check that fractional windows mean the same
thing in both assemblies.

Recorded values are read from the weil_trunc JSON files, not retyped.
Writes repro.json.
"""

from __future__ import annotations

import json
import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from mpmath import mp  # noqa: E402

OUT = os.path.join(W.HERE, "repro.json")


def recorded():
    enc = json.load(open(os.path.join(W.WT, "enclosures.json")))["cells"]
    scan = json.load(open(os.path.join(W.WT, "dhneg_scan.json")))
    rec = []
    for x in enc:
        key = (x["kind"], x["c"], x["N"])
        if key in {("zeta", 13, 4), ("zeta", 13, 8), ("zeta", 13, 16), ("zeta", 13, 32),
                   ("zeta", 29, 32), ("zeta", 6, 32), ("dh", 13, 32), ("dh", 29, 32)}:
            rec.append((x["kind"], x["c"], x["N"], x["eig_ball_mid"], "enclosures.json eig_ball_mid"))
    for t in scan["trajectories"]:
        if (t["c"], t["N"]) in {(29, 128), (31, 59), (31, 60), (31, 128)}:
            rec.append(("dh", t["c"], t["N"], t["lam_min_mid"], "dhneg_scan.json trajectories"))
    rec.append(("dh", 30, 128, scan["c_slice_N128"]["30"]["lam_min_mid"], "dhneg_scan.json c_slice_N128"))
    zc = scan["zeta_control"]
    rec.append(("zeta", zc["c"], zc["N"], zc["lam_min_mid"], "dhneg_scan.json zeta_control"))
    return rec


def ball_mid(s: str) -> mp.mpf:
    s = s.strip()
    if s.startswith("["):
        s = s[1:].split("+/-")[0].strip().rstrip("]").strip()
    return mp.mpf(s)


def route_a(kind, c, N):
    t0 = time.time()
    bt, A = W.build(c, N, kind)
    (r1, v1), (r2, _) = W.lowest_pairs(A, 2)
    # Temple shift: geometric mean of |lambda_1| and lambda_2 midpoints
    l1, l2 = abs(float(r1.mid())), float(r2.mid())
    shift = mp.nstr(mp.sqrt(mp.mpf(max(l1, 1e-300)) * mp.mpf(l2)), 5)
    pb = W.ldl_prec(kind, N)
    tb = None
    for _ in range(3):
        _, Ah = W.build(c, N, kind, prec=pb)
        tb = W.temple_bracket(Ah, v1, shift)
        if tb["conclusive"]:
            break
        pb *= 2
    return {
        "lam_min_rq": W.as_str(r1, 22),
        "lam_2_rq": W.as_str(r2, 8),
        "temple": tb,
        "ldl_prec": pb,
        "mu0": W.as_str(W.mu0(v1), 12),
        "elapsed_s": round(time.time() - t0, 2),
    }


def route_b(kind, c, N, dps):
    t0 = time.time()
    with mp.workdps(dps):
        tr = W.GK.Truncation(mp.mpf(int(c.p)) / int(c.q), N, kind=kind)
        ev, _ = W.GK.eigsy_sorted(tr.even_matrix())
        lam = ev[0]
        return {"dps": dps, "lam_min": mp.nstr(lam, 22), "elapsed_s": round(time.time() - t0, 2)}, lam


def main():
    out = {"meta": {"note": "Task 1 reproduction; route A = Arb assembly + inverse iteration + "
                            "ball Rayleigh quotient + Temple/LDL bracket; route B = mpmath "
                            "assembly + eigsy (independent linear algebra)."},
           "recorded": [], "route_b": []}
    for kind, c, N, val, src in recorded():
        a = route_a(kind, W.cq(c), N)
        with mp.workdps(60):
            ref = ball_mid(val)
            mine = ball_mid(a["lam_min_rq"])
            rel = abs(mine - ref) / abs(ref)
        row = {"kind": kind, "c": c, "N": N, "recorded": val[:60], "source": src,
               "rel_dev": mp.nstr(rel, 3), **a}
        out["recorded"].append(row)
        print(f"{kind:4s} c={c:>3} N={N:>3}: mine {a['lam_min_rq'][:26]} rec {val[:24]} "
              f"rel {mp.nstr(rel, 3)} temple={a['temple']['conclusive']} [{a['elapsed_s']}s]", flush=True)
        W.save(OUT, out)
    # route B: independent assembly + eigensolver, integer and fractional c
    for kind, c, N, dps in [("zeta", "13", 8, 60), ("dh", "13", 16, 40),
                            ("dh", "61/2", 24, 50), ("zeta", "61/2", 16, 90),
                            ("dh", "497/16", 32, 50)]:
        from fractions import Fraction
        q = W.cq(Fraction(c))
        b, lam_b = route_b(kind, q, N, dps)
        a = route_a(kind, q, N)
        with mp.workdps(60):
            rel = abs(ball_mid(a["lam_min_rq"]) - lam_b) / abs(lam_b)
        row = {"kind": kind, "c": c, "N": N, "route_b": b, "route_a_lam_min": a["lam_min_rq"],
               "route_a_temple": a["temple"], "rel_dev": mp.nstr(rel, 3)}
        out["route_b"].append(row)
        print(f"B {kind:4s} c={c:>7} N={N:>3}: mpmath {b['lam_min'][:22]} arb {a['lam_min_rq'][:24]} "
              f"rel {mp.nstr(rel, 3)} [{b['elapsed_s']}s]", flush=True)
        W.save(OUT, out)


if __name__ == "__main__":
    main()
