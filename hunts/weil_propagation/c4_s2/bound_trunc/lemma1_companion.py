"""Measured companion of Lemma 1 (DERIVATION.md s1.2): the divergent trace, mode by mode.

Lemma 1 says tau_f(R_n) = sum_{j >= n} ||theta(f) zeta_j||^2 = +infinity for every
n. Its heuristic rate: |zeta^_j(s)|^2 ~ 4j/(s^2 + 4j^2), so for j well above the
window's frequencies each mode adds about w_f / j and the partial sums
P(n) = sum_{j < n} ||theta(f) zeta_j||^2 grow like w_f log n.

This script measures P(n) for one window function, f = U_0 at c = 2.9 (the
constant on [0, L], unit norm, |f^(s)|^2 = 4 sin^2(sL/2) / (L s^2)), with the
s-integral restricted to |s| <= S0:

    P_S0(n) = (1/2pi) int_{|s| <= S0} |f^(s)|^2 sum_{j < n} |zeta^_j(s)|^2 ds,
    w_f     = (1/2pi) int_{|s| <= S0} |f^(s)|^2 ds.

The restriction is part of the measured quantity's definition (P_S0 <= P, and
P_S0 already diverges like w_f log n). zeta^_j(s) is kernel/'s closed form
(`sonin.zeta_mellin_all`, Tate's local functional equation, mpmath at dps 20),
not two_adic/'s w-quadrature, so this is a second route to the same
transforms. Gauss-Legendre panels on [0, S0] (the integrand is even in s).

It also reads the stored Delta_T = T_S - T_inf at the same vector (the U_0
diagonal entry) on the five c = 2.9, N = 32 builds (200 to 364 modes), the
quantity whose two divergent pieces P_S0 is one of: it moves by at most
a few 1e-3 while P_S0 grows by about w_f log(364/200).

Measured grade: float64 of mpmath values, one window vector, one c.

    PYTHONPATH=<worktree root> <venv python> .../bound_trunc/lemma1_companion.py   # about 3 to 5 minutes
"""

from __future__ import annotations

import json
import math
import os
import sys
import time

import numpy as np
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
C4S2 = os.path.normpath(os.path.join(HERE, ".."))
for sub in ("kernel",):
    p = os.path.join(C4S2, sub)
    if p not in sys.path:
        sys.path.insert(0, p)
if HERE not in sys.path:
    sys.path.insert(0, HERE)

import sonin  # noqa: E402  (kernel/, read-only)

OUT = os.path.join(HERE, "lemma1_companion.json")
C = "2.9"
S0 = 60.0
NMAX = 240
PANELS = 24
PER_PANEL = 6
DPS = 20
MARKS = (10, 20, 40, 80, 120, 160, 200, 240)


def f_hat_sq(s: np.ndarray, L: float) -> np.ndarray:
    """|U_0^(s)|^2 = 4 sin^2(sL/2) / (L s^2)."""
    s = np.asarray(s, dtype=float)
    out = np.empty_like(s)
    small = np.abs(s) < 1e-12
    out[~small] = 4.0 * np.sin(s[~small] * L / 2) ** 2 / (L * s[~small] ** 2)
    out[small] = L
    return out


def s_nodes(S0: float = S0, panels: int = PANELS, per_panel: int = PER_PANEL):
    x, w = np.polynomial.legendre.leggauss(per_panel)
    edges = np.linspace(0.0, S0, panels + 1)
    s = np.concatenate([(a + b) / 2 + (b - a) / 2 * x for a, b in zip(edges[:-1], edges[1:])])
    ws = np.concatenate([(b - a) / 2 * w for a, b in zip(edges[:-1], edges[1:])])
    return s, ws


def mode_contributions(nmax: int = NMAX):
    """c_j = (1/2pi) int_{|s| <= S0} |f^|^2 |zeta^_j|^2 ds, j < nmax, and w_f."""
    L = math.log(float(C))
    s, ws = s_nodes()
    H = np.zeros((nmax, s.size))
    for i, si in enumerate(s):
        z = sonin.zeta_mellin_all(mp.mpf(float(si)), DPS, 0, nmax)
        H[:, i] = [float(abs(x)) ** 2 for x in z]
    fw = f_hat_sq(s, L) * ws * 2.0 / (2.0 * math.pi)  # even integrand: 2 int_0^S0, then 1/2pi
    return H @ fw, float(fw.sum()), H, s


def stored_delta_T_diag():
    """Delta_T[U_0, U_0] = T_S - T_inf at index N on the c = 2.9, N = 32 builds."""
    import eps_trunc as E

    snap = E._snapshot()
    T = sonin.T_inf_matrix(C, 32, 40)
    t00 = float(T[32, 32])
    out = []
    for nv, S in E.BUILDS[32]:
        TS = E.stored_T_S(snap, C, 32, nv, S)
        out.append({"nvec": nv, "S": S, "delta_T_00": float(TS[32, 32]) - t00})
    return out, t00


def main():
    t0 = time.time()
    cj, wf, H, s = mode_contributions()
    P = np.cumsum(cj)
    marks = {str(n): float(P[n - 1]) for n in MARKS}
    heur = [float(np.sum(f_hat_sq(s, math.log(float(C))) * s_nodes()[1] * 2 / (2 * math.pi)
                         * 4 * j / (s**2 + 4 * j * j))) for j in range(1, NMAX)]
    slope = {f"{a}-{b}": float((P[b - 1] - P[a - 1]) / math.log(b / a)) for a, b in ((40, 80), (80, 160), (120, 240))}
    dT, t00 = stored_delta_T_diag()
    doc = {"meta": {"what": "partial sums of tau_f(Q_inf^(n)) restricted to |s| <= S0, f = U_0 at c = 2.9 (DERIVATION s1.2, Lemma 1)",
                    "c": C, "S0": S0, "nmax": NMAX, "panels": PANELS, "per_panel": PER_PANEL, "dps": DPS,
                    "route": "kernel/sonin.zeta_mellin_all (closed form)", "seconds": round(time.time() - t0, 1)},
           "w_f": wf, "P": marks, "c_j": [float(x) for x in cj],
           "heuristic_c_j": {"note": "same quadrature with |zeta^_j|^2 replaced by 4j/(s^2 + 4j^2), j >= 1", "values": heur},
           "slope_per_log_n": slope,
           "stored_delta_T_00": dT, "T_inf_00": t00}
    with open(OUT, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("w_f", wf, "P", marks, "slope", slope, "dT", dT, "seconds", round(time.time() - t0, 1))


if __name__ == "__main__":
    main()
