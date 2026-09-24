"""The mode-free floor (DERIVATION.md s1.4, Lemma 3): exact inertia of Q - kappa T_inf.

Lemma 3 (ordinary argument, unreviewed): kappa T_inf <= T_S <= T_inf / kappa as
forms on window functions, kappa = ((1 - a)/(1 + a))^2 = (sqrt2 - 1)^4
= 17 - 12 sqrt2, a = 2^{-1/2}. Hence R_S = Q - T_S <= Q - kappa T_inf, and on
the window space n_-(R_S) >= n_-(Q - kappa T_inf) by min-max. Since the exact
T_inf is a positive form, Q - kappa T_inf <= Q - kappa_lo T_inf for any
kappa_lo <= kappa, so a rational kappa_lo (below kappa by at most 2^-80) is
used and the count only gets harder to reach.

The matrices. Q is checker/'s (`checker_q.Q_matrix`, dps 40) and T_inf is
kernel/'s (`sonin.T_inf_matrix`, dps 40), both at N = 32; N = 8 and 16 are
central blocks (their entries do not depend on N). A := Q - kappa_lo T_inf is
formed at dps 60 and rounded to float64; each float64 entry is the exact
dyadic rational it is. The spectral size of that rounding is recorded
(`round_frob`, a Frobenius norm, which bounds the spectral one).

Two exact routes over the rationals (checker/'s `inertia_both`: symmetric
elimination with Sylvester's law, and the characteristic polynomial with
Descartes' rule, which must agree) count the eigenvalues strictly below a
threshold t: n_-(A - t I). Thresholds 0 and -MARGIN. The counted eigenvalues
are bracketed by exact counts (checker/'s `bracket`).

The C4 function class V_4 (g-hat vanishing at +i/2, -i/2, 0), the same
codimension-3 real subspace checker/ s7.9 uses, here for every c: v_0 = 0
and v orthogonal to h_n = 1/(L^2 + 16 pi^2 n^2) and n h_n. Its basis is
enclosed in arb balls and In(Z^T A Z) is decided by ball elimination
(checker/'s `inertia_balls`, every pivot excluding 0), else "undecided".

What the counts mean, and what they do not: each eigenvalue of the stored A
below -t with t larger than the errors of Q and T_inf (assembler/ states
them) is a negative eigenvalue of the Galerkin compression of the exact
R_S. No prolate truncation, no s cutoff and no Delta_T enter.

    PYTHONPATH=<worktree root> <venv python> .../bound_trunc/kappa_floor.py   # about 1 to 2 minutes
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np
from flint import arb, arb_mat, fmpq
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
for sub in ("checker", "kernel"):
    p = os.path.join(C4S2, sub)
    if p not in sys.path:
        sys.path.insert(0, p)

import checker_q as CQ  # noqa: E402  (checker/, read-only)
import run_checker_inertia as RI  # noqa: E402  (checker/, read-only: exact inertia routines)
import sonin  # noqa: E402  (kernel/, read-only)

OUT = os.path.join(HERE, "kappa_floor.json")
CELLS = ("2.2", "2.5", "2.9")
NS = (8, 16, 32)
DPS = 40
MARGIN = fmpq(1, 2**40)  # about 9.1e-13
KBITS = 80


def kappa_bounds(bits: int = KBITS) -> tuple[fmpq, fmpq]:
    """Rationals kappa_lo < kappa = 17 - 12 sqrt2 < kappa_hi, width 12 * 2^-bits, by integer sqrt."""
    r = math.isqrt(2 * 4**bits)  # floor(sqrt2 * 2^bits); sqrt2 is irrational, so strict
    s_lo, s_hi = fmpq(r, 2**bits), fmpq(r + 1, 2**bits)
    return 17 - 12 * s_hi, 17 - 12 * s_lo


def kappa_arb(prec: int = 128) -> arb:
    return 17 - 12 * arb(2).sqrt()


def _c_fmpq(c: str) -> fmpq:
    num, den = c.replace(".", ""), 10 ** len(c.split(".")[1])
    return fmpq(int(num), den)


def class_basis(c: str, N: int, prec: int):
    """arb enclosure of the basis Z of V_4 at this c (checker/ s7.9's construction, c as a parameter)."""
    with RI.arb_prec(prec):
        L = arb(_c_fmpq(c)).log()
        pi = arb.pi()
        L2, P2 = L * L, 16 * pi * pi
        free = [n for n in range(-N, N + 1) if abs(n) >= 2]
        Z = arb_mat(2 * N + 1, len(free))
        for j, n in enumerate(free):
            r = (L2 + P2) / (L2 + P2 * n * n)  # h_n / h_1
            Z[n + N, j] = arb(1)
            Z[1 + N, j] = -(1 + n) * r / 2
            Z[-1 + N, j] = -(1 - n) * r / 2
        return Z


def class_inertia(A: np.ndarray, c: str, N: int) -> dict:
    n = A.shape[0]
    for prec in (256, 512):
        with RI.arb_prec(prec):
            Z = class_basis(c, N, prec)
            M = arb_mat(n, n)
            for i in range(n):
                for j in range(n):
                    M[i, j] = arb(float(A[i, j]))
            B = Z.transpose() * M * Z
            m = B.nrows()
            res = RI.inertia_balls([[B[i, j] for j in range(m)] for i in range(m)])
        if res is not None:
            return {"n_minus": res[0], "n_plus": res[2], "dim": m, "prec": prec}
    return {"n_minus": None, "undecided": True, "dim": n - 3}


def floor_matrices(c: str):
    """{N: (A float64 symmetric, round_frob)} with A = Q - kappa_lo T_inf."""
    klo, _ = kappa_bounds()
    Q32 = CQ.Q_matrix(c, 32, DPS)
    T32 = sonin.T_inf_matrix(c, 32, DPS)
    out = {}
    for N in NS:
        Q = CQ.central_block(Q32, N) if N < 32 else Q32
        T = CQ.central_block(T32, N) if N < 32 else T32
        n = 2 * N + 1
        with mp.workdps(60):
            k = mp.mpf(int(klo.p)) / mp.mpf(int(klo.q))
            Am = [[mp.re(Q[i, j]) - k * mp.re(T[i, j]) for j in range(n)] for i in range(n)]
            A = np.array([[float(Am[i][j]) for j in range(n)] for i in range(n)])
            A = (A + A.T) / 2  # exact symmetrisation of the rounded table (entries equal in pairs up to rounding)
            frob = mp.sqrt(mp.fsum((Am[i][j] - mp.mpf(A[i, j])) ** 2 for i in range(n) for j in range(n)))
            asym = max(abs(mp.re(Q[i, j]) - mp.re(Q[j, i])) + abs(mp.re(T[i, j]) - mp.re(T[j, i])) for i in range(n) for j in range(n))
        out[N] = (A, float(frob), float(asym))
    return out


def analyse(c: str, N: int, A: np.ndarray, round_frob: float, asym: float) -> dict:
    t0 = time.time()
    Aq = RI.exact_matrix(A)
    ev = np.linalg.eigvalsh(A)
    n0 = RI.count_below(Aq, fmpq(0))
    nm = RI.count_below(Aq, -MARGIN)
    brackets = []
    for k in range(1, n0 + 1):
        b = RI.bracket(Aq, k, ev[k - 1], split=fmpq(0))
        brackets.append({"k": k, "lo": str(b["lo"]), "hi": str(b["hi"]), "lo_float": float(b["lo"].p) / float(b["lo"].q),
                         "hi_float": float(b["hi"].p) / float(b["hi"].q)})
    cls = class_inertia(A, c, N)
    return {"c": c, "N": N, "count_below_0": n0, "count_below_minus_margin": nm,
            "margin": str(MARGIN), "brackets": brackets, "lowest_float": [float(x) for x in ev[:4]],
            "class_V4": cls, "round_frob": round_frob, "input_asym": asym, "seconds": round(time.time() - t0, 1)}


def main():
    klo, khi = kappa_bounds()
    rows = []
    t_all = time.time()
    for c in CELLS:
        mats = floor_matrices(c)
        for N in NS:
            A, frob, asym = mats[N]
            rows.append(analyse(c, N, A, frob, asym))
            r = rows[-1]
            print(c, N, r["count_below_0"], r["count_below_minus_margin"], r["class_V4"], r["lowest_float"][:3], r["seconds"], flush=True)
    doc = {"meta": {"what": "exact inertia of Q - kappa_lo T_inf (DERIVATION.md s1.4, Lemma 3)",
                    "kappa": "17 - 12 sqrt2 = (sqrt2 - 1)^4", "kappa_lo": str(klo), "kappa_hi": str(khi),
                    "kappa_arb": str(kappa_arb()), "dps": DPS, "Q": "checker_q.Q_matrix(c, 32, 40), central blocks",
                    "T_inf": "sonin.T_inf_matrix(c, 32, 40), central blocks",
                    "routes": "checker/run_checker_inertia.inertia_both (LDL^T and charpoly), bracket, inertia_balls",
                    "seconds": round(time.time() - t_all, 1)},
           "rows": rows}
    with open(OUT, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("wrote", OUT)


if __name__ == "__main__":
    main()
