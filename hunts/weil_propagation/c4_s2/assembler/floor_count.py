"""assembler/, PREREG Addendum A: the mode-free floor and ceiling from
bound_trunc/'s Lemma 3 (kappa T_inf <= T_S <= K T_inf, kappa = (sqrt2 - 1)^4,
K = 1/kappa), counted with enclosures end to end.

    F_N(c) = n_-(Q_mp - kappa_lo T_inf_mp + eta_N I) <= n_-(R_ex(c, N))
    G_N(c) = n_-(Q_mp - K_hi   T_inf_mp - eta_N I) >= n_-(R_ex(c, N))

Q_mp from checker_q.Q_matrix(c, N, 40), T_inf_mp from kernel/sonin.T_inf_matrix
(c, N, 40), read-only; every entry an exact binary rational. Route 1 is
run_checker_inertia's two rational routes; route 2 is its ball elimination
with kappa and K as arb balls; V_4 by balls on Z(c)^T (.) Z(c).

    PYTHONPATH=<worktree root> <venv python> .../floor_count.py [--cells 2.9] [--Ns 8,16,32]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import numpy as np  # noqa: E402
from flint import arb, arb_mat, fmpq  # noqa: E402
from mpmath import mp  # noqa: E402

import assemble as AS  # noqa: E402  (checker/ on sys.path)

RI = AS.RI
BITS = 256
_S = fmpq(math.isqrt(2 * 4 ** BITS) + 1, 2 ** BITS)  # >= sqrt 2
KAPPA_LO = 17 - 12 * _S  # <= kappa = 17 - 12 sqrt 2
K_HI = 17 + 12 * _S  # >= K = 17 + 12 sqrt 2 = 1/kappa
DELTA = AS.DELTA
OUT = os.path.join(HERE, "floor_count.json")


def eta(N: int) -> fmpq:
    """PREREG A.2: bounds ||(Q_ex - Q_mp) - c (T_ex - T_mp)|| for every c <= K_HI."""
    return (2 * N + 1) * (AS.E_Q_ENTRY + K_HI * AS.E_TINF_ENTRY)


def t_inf_direct(c: str, N: int):
    """kernel/sonin.T_inf_matrix(c, N, 40), read-only import."""
    if AS.KERNEL not in sys.path:
        sys.path.insert(0, AS.KERNEL)
    import sonin

    return sonin.T_inf_matrix(float(c), N, 40)


def exact(M) -> list:
    n = M.rows
    return [[AS.mpf_to_q(M[i, j]) for j in range(n)] for i in range(n)]


def combo(Qq, Tq, coef: fmpq, shift: fmpq) -> list:
    """Q - coef T + shift I, exactly."""
    n = len(Qq)
    return [[Qq[i][j] - coef * Tq[i][j] + (shift if i == j else 0) for j in range(n)] for i in range(n)]


def balls(Qq, Tq, coef: arb, shift: fmpq, prec: int) -> arb_mat:
    n = len(Qq)
    with RI.arb_prec(prec):
        A = arb_mat(n, n)
        s = arb(shift)
        for i in range(n):
            for j in range(n):
                A[i, j] = arb(Qq[i][j]) - coef * arb(Tq[i][j]) + (s if i == j else 0)
        return A


def ball_inertia(A: arb_mat):
    m = A.nrows()
    return RI.inertia_balls([[A[i, j] for j in range(m)] for i in range(m)])


def class_ball_inertia(Qq, Tq, which: str, shift: fmpq, N: int, c: str) -> dict:
    """In(Z^T (Q - coef T + shift I) Z) on V_4 at the first precision that decides."""
    for prec in AS.BALL_PRECS:
        with RI.arb_prec(prec):
            coef = (17 - 12 * arb(2).sqrt()) if which == "kappa" else (17 + 12 * arb(2).sqrt())
            A = balls(Qq, Tq, coef, shift, prec)
            Z, _ = AS.class_basis_c(AS.C_EXACT[c], N, prec)
            M = Z.transpose() * A * Z
            res = ball_inertia(M)
        if res is not None:
            return {"n_minus": res[0], "n_plus": res[2], "dim": M.nrows(), "prec": prec}
    return {"n_minus": None, "undecided": True, "dim": 2 * N + 1 - AS.CODIM_V4, "prec": AS.BALL_PRECS[-1]}


def count_cell(c: str, N: int) -> dict:
    t0 = time.time()
    Qm = AS.CQ.Q_matrix(c, N, 40)
    t1 = time.time()
    Tm = t_inf_direct(c, N)
    t2 = time.time()
    Qq, Tq = exact(Qm), exact(Tm)
    e = eta(N)
    F = RI.inertia_both(combo(Qq, Tq, KAPPA_LO, e))
    G = RI.inertia_both(combo(Qq, Tq, K_HI, -e))
    rec = {"c": c, "N": N, "dim": 2 * N + 1, "eta": AS.q_pair(e), "eta_float": float(e),
           "F": F[0], "F_inertia": list(F), "G": G[0], "G_inertia": list(G),
           "seconds_Q": round(t1 - t0, 1), "seconds_T_inf": round(t2 - t1, 1)}
    # the T_inf of the stored route (KernelProvider's moments) against the direct call
    Tk = AS.t_inf_mp(c, N)
    with mp.workdps(40):
        rec["T_inf_direct_vs_moments"] = float(max(abs(Tm[i, j] - Tk[i, j]) for i in range(2 * N + 1)
                                                  for j in range(2 * N + 1)))
    # robustness (reported): F at eta +- delta
    rec["F_at_eta_minus_delta"] = RI.inertia_both(combo(Qq, Tq, KAPPA_LO, e - DELTA))[0]
    rec["F_at_eta_plus_delta"] = RI.inertia_both(combo(Qq, Tq, KAPPA_LO, e + DELTA))[0]
    # route 2: balls, kappa and K as balls
    with RI.arb_prec(256):
        kap, KK = 17 - 12 * arb(2).sqrt(), 17 + 12 * arb(2).sqrt()
        rF = ball_inertia(balls(Qq, Tq, kap, e, 256))
        rG = ball_inertia(balls(Qq, Tq, KK, -e, 256))
    rec["route2"] = {"F": None if rF is None else rF[0], "G": None if rG is None else rG[0], "prec": 256}
    # V_4
    rec["V4"] = {"F": class_ball_inertia(Qq, Tq, "kappa", e, N, c), "G": class_ball_inertia(Qq, Tq, "K", -e, N, c)}
    # the negative eigenvalues of Q_mp - kappa_lo T_mp, bracketed by exact counts (reported)
    B0 = combo(Qq, Tq, KAPPA_LO, fmpq(0))
    w = np.linalg.eigvalsh(np.array([[float(x) for x in r] for r in B0]))
    k0 = RI.inertia_both(B0)[0]
    brs = []
    for k in range(1, k0 + 1):
        b = RI.bracket(B0, k, w[k - 1])
        brs.append({"k": k, "lo": AS.q_pair(b["lo"]), "hi": AS.q_pair(b["hi"]),
                    "lo_float": float(b["lo"]), "hi_float": float(b["hi"]), "evals": b["evals"]})
    rec["negatives_kappa_lo"] = brs
    rec["n_minus_kappa_lo_unshifted"] = k0
    rec["lowest_float"] = [float(x) for x in w[:4]]
    rec["seconds"] = round(time.time() - t0, 1)
    return rec


def run(cells=AS.CELLS, Ns=AS.NS, out_path: str = OUT) -> dict:
    out = {"meta": {"kappa_lo": AS.q_pair(KAPPA_LO), "K_hi": AS.q_pair(K_HI), "bits": BITS,
                    "E_Q_ENTRY": AS.q_pair(AS.E_Q_ENTRY), "E_TINF_ENTRY": AS.q_pair(AS.E_TINF_ENTRY),
                    "delta": AS.q_pair(DELTA), "python": sys.executable,
                    "sonin_sha256": hashlib.sha256(open(os.path.join(AS.KERNEL, "sonin.py"), "rb").read()).hexdigest(),
                    "checker_q_sha256": hashlib.sha256(open(os.path.join(AS.CHECKER, "checker_q.py"), "rb").read()).hexdigest()},
           "cells": {}}
    if os.path.exists(out_path):
        with open(out_path) as fh:
            old = json.load(fh)
        if old.get("meta") == out["meta"]:
            out["cells"] = old.get("cells", {})
    for c in cells:
        for N in Ns:
            key = f"{c}|{N}"
            if key in out["cells"]:
                continue
            rec = count_cell(c, N)
            out["cells"][key] = rec
            AS._dump(out, out_path)
            print(key, "F", rec["F"], "G", rec["G"], "route2", rec["route2"], "V4",
                  rec["V4"]["F"]["n_minus"], rec["V4"]["G"]["n_minus"], rec["seconds"], "s", flush=True)
    return out


def combined(routed_decisions_agg: dict | None, floor: dict, c: str, space: str) -> dict:
    """PREREG A.3: L_N <- max(L*_N, F_N), U_N <- min(U*_N, G_N), then interlacing,
    the check and decide(), every N counted as bounded."""
    pb = {}
    for N in AS.NS:
        r = floor["cells"][f"{c}|{N}"]
        if space == "full":
            F, G = r["F"], r["G"]
        else:
            fv, gv = r["V4"]["F"]["n_minus"], r["V4"]["G"]["n_minus"]
            F = fv if fv is not None else max(r["F"] - AS.CODIM_V4, 0)
            G = gv if gv is not None else r["G"]
        items = [(F, G)]
        if routed_decisions_agg is not None and routed_decisions_agg["has_bound"][N]:
            items.append((routed_decisions_agg["raw_L"][N], routed_decisions_agg["raw_U"][N]))
        pb[N] = items
    agg = AS.aggregate(pb, space)
    return {"agg": agg, "decision": AS.decide(agg)}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--cells", default=",".join(AS.CELLS))
    ap.add_argument("--Ns", default="8,16,32")
    a = ap.parse_args()
    run(cells=tuple(a.cells.split(",")), Ns=tuple(int(x) for x in a.Ns.split(",")))
