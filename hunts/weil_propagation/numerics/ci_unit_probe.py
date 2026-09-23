"""Cost probe for the proposed CI job (RUNS.md, "Proposed CI job"): ONE unit
of the boundary-adapted computation, timed. Not the job itself.

A unit is one (kind, c, N) cell of the edge-constrained family: the subspace
of V_N(c) with mu_0 = 0 (the band-N function vanishes at the window edge),
obtained from the validated assembly by one Householder reflection (no new
closed forms), then: its lowest eigenpair by inverse iteration, the
Hellmann-Feynman derivative d lambda/dL of that pair (wp_common.hf_derivative
on the embedded vector: the constraint does not depend on L), and the edge
profile f(y) at y = L 2^-j, j = 4..12. Timed per stage.

Usage: ci_unit_probe.py KIND N   (appends to ci_unit_probe.json)
"""

from __future__ import annotations

import os
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import wp_common as W  # noqa: E402
from flint import arb, arb_mat, ctx  # noqa: E402

KIND = sys.argv[1]
N = int(sys.argv[2])
C = "61/2"
PREC = 600 if KIND == "dh" else 2000
OUT = os.path.join(W.HERE, "ci_unit_probe.json")


def main():
    from fractions import Fraction

    t = {}
    t0 = time.time()
    bt, E = W.build(W.cq(Fraction(C)), N, KIND, prec=PREC)
    t["assemble"] = time.time() - t0
    ctx.prec = PREC
    n = N + 1
    s2 = arb(2).sqrt()
    a = arb_mat(n, 1, [arb(1)] + [s2] * N)
    na = W.dot(a, a).sqrt()
    w = arb_mat(n, 1, [a[i, 0] / na - (1 if i == 0 else 0) for i in range(n)])
    beta = 2 / W.dot(w, w)
    t0 = time.time()
    Ew = E * w
    wEw = W.dot(w, Ew)
    HEH = E - (w * Ew.transpose() + Ew * w.transpose()) * beta + (w * w.transpose()) * (beta * beta * wEw)
    EZ = arb_mat(n - 1, n - 1, [HEH[i, j] for i in range(1, n) for j in range(1, n)])
    t["project"] = time.time() - t0
    t0 = time.time()
    (rz, vz), (rz2, _) = W.lowest_pairs(EZ, 2)
    t["eigen"] = time.time() - t0
    y = arb_mat(n, 1, [arb(0)] + [vz[i, 0] for i in range(n - 1)])
    vfull = y - w * (beta * W.dot(w, y))  # H (0, v_Z)
    mu0 = W.mu0(vfull)
    t0 = time.time()
    hf = W.hf_derivative(W.cq(Fraction(C)), N, KIND, vfull)
    t["hf"] = time.time() - t0
    t0 = time.time()
    ctx.prec = PREC
    L = bt.L
    pi = arb.pi()
    prof = []
    for j in range(4, 13):
        yy = L / 2**j
        f = vfull[0, 0] * L.rsqrt() + sum(
            ((2 / L).sqrt() * (2 * pi * k * yy / L).cos() * vfull[k, 0] for k in range(1, n)), arb(0))
        prof.append([j, float(f.mid())])
    t["profile"] = time.time() - t0
    (rf, _), = W.lowest_pairs(E, 1)
    rec = {
        "kind": KIND, "c": C, "N": N, "prec": PREC, "hf_prec": hf["_prec"],
        "seconds": {k: round(v, 2) for k, v in t.items()},
        "total_s": round(sum(t.values()), 1),
        "sanity": {"lam_constrained": W.as_str(rz, 8), "lam_unconstrained": W.as_str(rf, 8),
                   "constrained_ge_unconstrained": bool(rz.mid() >= rf.mid()),
                   "mu0_of_constrained_vector": mu0.str(3)},
        "note": "cost probe of one unit; outputs are sanity checks, not results",
    }
    d = W.load(OUT, {"units": []})
    d["units"].append(rec)
    W.save(OUT, d)
    print(rec, flush=True)


if __name__ == "__main__":
    main()
