#!/usr/bin/env python3
"""Step 6: the active constraints at the family optimum, and their shadow prices.

Runs the cutting plane to convergence under the corrected stopping rule (which
tests the LP value against the INDEPENDENT multistart, never against the pool
minimum -- see the comment in epsstar.eps_star), then re-solves the LP once at
the final cut set to read:

  * the dual on each span-capacity row, i.e. d(eps*)/d(capacity_s);
  * the dual on the total-pressure row, i.e. d(eps*)/dB, to compare against the
    break-even that the assembly shadow prices set;
  * which pair weights and pressures sit on their bounds;
  * which gap vectors are active at F = eps*, i.e. what actually pins the floor.

Everything printed here is a property of the linear programme, not of a
minimiser, except the identity of the active gap vectors.
"""
from __future__ import annotations

import json
import sys

import numpy as np
from scipy.optimize import linprog

from ceiling import W_matrix, _span_blocks, family_bound
from epsstar import eps_star
from family import (H_of, amtopa_a, amtopa_b, amtopa_coeffs, frequencies,
                    kernel, window_matrices, PAIR_LIST)

BLOCKS = _span_blocks()
NPAIR, QG = 21, 6
AMTOPA_BOUND = 0.6734164909714992949
AMTOPA_FLOATMIN = 0.007911105155226424


def main() -> int:
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 90
    c = amtopa_coeffs()
    w = frequencies(17)
    u, _, _, M = window_matrices(w)
    H = H_of(c, u, M)
    k0 = float(kernel(0.0, c, w)[0])
    B0 = float(amtopa_b().sum())

    pool = np.load("artifacts/cut_pool.npy")
    print(f"pool {pool.shape[0]} cuts, running {rounds} cutting-plane rounds")
    r = eps_star(B0, c, w, k0, rounds=rounds, seed=4242, cut_pool=pool.copy(),
                 coarse=90000, keep=90, verbose=True, patience=8)
    G = r["cuts"]
    print(f"\neps* bracket [{r['lower']:.12f}, {r['upper']:.12f}] over "
          f"{G.shape[0]} cuts")

    # one clean LP at the final cut set, for the duals
    Wm = W_matrix(G, c, w, k0)
    n = NPAIR + QG + 1
    A_eq = np.zeros((QG + 1, n))
    for s, cols in enumerate(BLOCKS):
        A_eq[s, cols] = 1.0
    A_eq[QG, NPAIR:NPAIR + QG] = 1.0
    b_eq = np.concatenate([np.full(QG, 2.0), [B0]])
    bounds = [(0.0, 2.0)] * NPAIR + [(0.0, B0)] * QG + [(None, None)]
    cost = np.zeros(n)
    cost[-1] = -1.0
    A_ub = np.hstack([-Wm, -G, np.ones((G.shape[0], 1))])
    res = linprog(cost, A_ub=A_ub, b_ub=np.zeros(G.shape[0]), A_eq=A_eq,
                  b_eq=b_eq, bounds=bounds, method="highs")
    assert res.success, res.message
    eps = float(res.x[-1])
    a, b = res.x[:NPAIR], res.x[NPAIR:NPAIR + QG]
    d = res.eqlin.marginals

    base, m = family_bound(H, eps, B0)
    h = 1e-8
    dH = (family_bound(H + h, eps, B0)[0] - base) / h
    de = (family_bound(H, eps + h, B0)[0] - base) / h
    dB = (family_bound(H, eps, B0 + h)[0] - base) / h

    print(f"\neps* = {eps:.12f}   assembled {base:.16f} at m={m}")
    print(f"AMTOPA headline {AMTOPA_BOUND:.16f}   delta {base-AMTOPA_BOUND:+.4e}")
    print(f"\nassembly shadow prices:")
    print(f"  d(bound)/dH   = {dH:+.6f}")
    print(f"  d(bound)/deps = {de:+.6f}")
    print(f"  d(bound)/dB   = {dB:+.6f}")
    print(f"  break-even d(eps)/dB      = {-dB/de:.6f}")
    print(f"  break-even d(eps)/d(-H)   = {dH/de:.6f}")

    print(f"\nLP duals, d(eps*)/d(rhs), and their value in bound units:")
    rows = []
    for s in range(QG):
        pr = float(-d[s])
        rows.append(("span %d capacity" % (s + 1), pr, pr * de))
    pb = float(-d[QG])
    print(f"  {'constraint':<22} {'d eps*/d rhs':>14} {'x d(bound)/deps':>16}")
    for name, pr, bu in sorted(rows, key=lambda t: -t[1]):
        print(f"  {name:<22} {pr:>14.9f} {bu:>16.9f}")
    print(f"  {'total pressure':<22} {pb:>14.9f} {'':>16}")
    print(f"  net d(bound)/dB including the floor it buys = {dB + de*pb:+.6f}")

    print(f"\nactive set:")
    print(f"  pair weights at 0        : {int((a < 1e-9).sum())} of 21")
    print(f"  pair weights at cap 2    : {int((a > 2 - 1e-9).sum())} of 21")
    print(f"  pressures at 0           : {int((b < 1e-13).sum())} of 6")
    fv = Wm @ a + G @ b
    act = np.where(np.abs(fv - eps) < 1e-9)[0]
    print(f"  gap vectors with F = eps : {len(act)} of {G.shape[0]}")
    for i in act[:8]:
        print(f"    {np.round(G[i], 6)}  F={float(fv[i]):.12f}")

    # ---- the window trade, both ends, under the same stopping rule ----------
    e0 = np.zeros(17)
    e0[0] = 1.0
    H0 = H_of(e0, u, M)
    k00 = float(kernel(0.0, e0, w)[0])
    print(f"\n-- the window trade, both ends, same rule --")
    r0 = eps_star(B0, e0, w, k00, rounds=rounds, seed=77,
                  cut_pool=pool.copy(), coarse=90000, keep=90, patience=8)
    v0, m0 = family_bound(H0, r0["upper"], B0)
    print(f"  pure sqrt(2)     H={H0:.16f}  eps*<={r0['upper']:.10f}  "
          f"bound={v0:.16f} (m={m0})")
    print(f"  AMTOPA 17-term   H={H:.16f}  eps*<={eps:.10f}  "
          f"bound={base:.16f} (m={m})")
    dHw = H0 - H
    dew = eps - r0["upper"]
    print(f"  they spend {dHw:.6e} of window constant and buy {dew:.6e} of floor")
    print(f"  exchange rate {dew/dHw:.4f} against break-even {dH/de:.4f}")

    with open("doors.json", "w") as fh:
        json.dump({
            "eps_star": eps, "eps_bracket": [r["lower"], r["upper"]],
            "cuts": int(G.shape[0]), "bound": base, "m": int(m),
            "amtopa_headline": AMTOPA_BOUND, "amtopa_floor": AMTOPA_FLOATMIN,
            "d_bound_dH": dH, "d_bound_deps": de, "d_bound_dB": dB,
            "span_duals": [float(-d[s]) for s in range(QG)],
            "pressure_dual": pb,
            "net_d_bound_dB": dB + de * pb,
            "a": a.tolist(), "b": b.tolist(),
            "active_cuts": G[act][:40].tolist(),
            "pure_sqrt2": {"H": H0, "eps_upper": r0["upper"], "bound": v0,
                           "m": int(m0)},
            "window_exchange_rate": float(dew / dHw),
        }, fh, indent=2)
    np.save("/tmp/doors_pool.npy", G)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
