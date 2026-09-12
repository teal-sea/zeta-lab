"""Locate the first (c, N) where the DH truncated Weil form goes negative.

Strategy (see dhneg_log.md for the regime reasoning):

* For each integer c, ONE ball LDL^T factorization of the even (and odd)
  sector at N = Nmax yields the inertia of every leading principal
  submatrix at once: the number of negative eigenvalues at band N is the
  number of negative pivots among the first N+1 (even) / N (odd) pivots.
  So first_neg_N(c) drops out of a single factorization per sector.
* lambda_min(c, N) trajectories come from eig (nonstop enclosures) on
  principal submatrices of the same assembly.

Reuses the ball assembly in ``enclosures.BallTruncation`` (which mirrors
``galerkin.Truncation`` entry-for-entry); nothing is re-derived here.

Checkpoint discipline: every computed data point is written to
``dhneg_scan.json`` immediately (read-modify-write per point).
"""

from __future__ import annotations

import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from flint import acb, acb_mat, arb, ctx  # noqa: E402

import enclosures as EN  # noqa: E402

SCAN = os.path.join(HERE, "dhneg_scan.json")

GAMMA_OFF = "85.699348485377592171929267708941729037987829423408"
DELTA_OFF = "0.30851718245663738555335196060684412785067026830502"


# ---------------------------------------------------------------------------
# checkpointed JSON store
# ---------------------------------------------------------------------------


def load_scan():
    if os.path.exists(SCAN):
        with open(SCAN) as f:
            return json.load(f)
    return {
        "meta": {
            "gamma_off": GAMMA_OFF,
            "delta_off": DELTA_OFF,
            "note": "DH truncated Weil form negativity scan; ball LDL pivot "
            "signs give n_neg(N) for every principal N from one "
            "factorization at Nmax. Sign claims are conclusive only "
            "where 'conclusive' is true.",
        },
        "ladders": {},
        "trajectories": [],
        "scout": [],
    }


def save_scan(d):
    tmp = SCAN + ".tmp"
    with open(tmp, "w") as f:
        json.dump(d, f, indent=1)
    os.replace(tmp, SCAN)


# ---------------------------------------------------------------------------
# pivot-sign LDL (sign sequence, not just counts)
# ---------------------------------------------------------------------------


def pivot_signs(M, prec: int):
    """Ball LDL^T of M; returns (signs, conclusive) with signs[j] in
    {+1, -1, 0}; 0 = pivot ball straddles zero (factorization stops there,
    later entries are not claimed)."""
    ctx.prec = prec
    n = len(M)
    A = [[M[i][j] for j in range(n)] for i in range(n)]
    d = []
    Lf = [[arb(0)] * n for _ in range(n)]
    signs = []
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s -= Lf[j][k] * Lf[j][k] * d[k]
        if s > 0:
            signs.append(1)
        elif s < 0:
            signs.append(-1)
        else:
            signs.append(0)
            return signs, False
        d.append(s)
        for i in range(j + 1, n):
            t = A[i][j]
            for k in range(j):
                t -= Lf[i][k] * Lf[j][k] * d[k]
            Lf[i][j] = t / s
    return signs, True


def first_neg_from_signs(signs, sector: str):
    """Smallest band N whose sector matrix has a negative eigenvalue.

    Even sector: leading (N+1) pivots are modes 0..N, so pivot index j
    corresponds to N = j.  Odd sector: leading N pivots are modes 1..N,
    so pivot index j corresponds to N = j + 1."""
    for j, s in enumerate(signs):
        if s < 0:
            return j if sector == "even" else j + 1
    return None


# ---------------------------------------------------------------------------
# ladder for one c
# ---------------------------------------------------------------------------


def run_ladder(c: int, Nmax: int, prec: int = 600):
    t0 = time.time()
    bt = EN.BallTruncation(c, Nmax, kind="dh", prec=prec)
    Me = bt.even_matrix()
    Mo = bt.odd_matrix()
    se, ce = pivot_signs(Me, prec)
    so, co = pivot_signs(Mo, prec)
    rec = {
        "c": c,
        "Nmax": Nmax,
        "prec": prec,
        "conclusive_even": bool(ce),
        "conclusive_odd": bool(co),
        "n_neg_even_at_Nmax": sum(1 for s in se if s < 0),
        "n_neg_odd_at_Nmax": sum(1 for s in so if s < 0),
        "first_neg_N_even": first_neg_from_signs(se, "even"),
        "first_neg_N_odd": first_neg_from_signs(so, "odd"),
        "neg_pivot_indices_even": [j for j, s in enumerate(se) if s < 0],
        "neg_pivot_indices_odd": [j for j, s in enumerate(so) if s < 0],
        "elapsed_s": round(time.time() - t0, 2),
    }
    return rec, bt, Me


def eig_lambda_min(M, n: int, prec: int):
    """Smallest-real-part eigenvalue of the leading n x n principal
    submatrix, via nonstop enclosures; returns (mid, rad) as floats-ish."""
    ctx.prec = prec
    A = acb_mat([[acb(M[i][j]) for j in range(n)] for i in range(n)])
    E = A.eig(nonstop=True, multiple=True)
    lo = min(E, key=lambda e: float(e.real.mid()))
    return lo.real.mid(), lo.real.rad()


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main():
    c_lo = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    c_hi = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    Nmax = int(sys.argv[3]) if len(sys.argv) > 3 else 128
    prec = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    traj_c = {13, 19, 29, 37, 41, 43, 45, 47, 53}
    traj_N = [8, 16, 24, 32, 36, 40, 44, 48, 52, 56, 60, 64, 72, 80, 96, 128]

    for c in range(c_lo, c_hi + 1):
        d = load_scan()
        key = str(c)
        if key in d["ladders"] and d["ladders"][key]["Nmax"] >= Nmax:
            continue
        rec, bt, Me = run_ladder(c, Nmax, prec)
        if not (rec["conclusive_even"] and rec["conclusive_odd"]):
            rec2, bt, Me = run_ladder(c, Nmax, prec * 2)
            if rec2["conclusive_even"] and rec2["conclusive_odd"]:
                rec = rec2
        d = load_scan()
        d["ladders"][key] = rec
        save_scan(d)
        print(
            f"c={c:3d}: first_neg_N even={rec['first_neg_N_even']} "
            f"odd={rec['first_neg_N_odd']} "
            f"n_neg@{Nmax}=({rec['n_neg_even_at_Nmax']},{rec['n_neg_odd_at_Nmax']}) "
            f"concl=({rec['conclusive_even']},{rec['conclusive_odd']}) "
            f"[{rec['elapsed_s']}s]",
            flush=True,
        )
        if c in traj_c:
            for N in traj_N:
                if N > Nmax:
                    continue
                mid, rad = eig_lambda_min(Me, N + 1, prec)
                pt = {
                    "kind": "dh",
                    "sector": "even",
                    "c": c,
                    "N": N,
                    "prec": prec,
                    "lam_min_mid": str(mid),
                    "lam_min_rad": float(rad),
                }
                d = load_scan()
                d["trajectories"].append(pt)
                save_scan(d)
                print(f"    traj c={c} N={N}: lam_min ~ {str(mid)[:24]}", flush=True)


if __name__ == "__main__":
    main()
