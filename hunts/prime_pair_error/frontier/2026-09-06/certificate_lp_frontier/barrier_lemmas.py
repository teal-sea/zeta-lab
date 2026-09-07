"""Lower bounds on the prime-blind LP floor by explicit dual constructions.

Setting.  c supported on [1, y], W_c(n) = sum_j c_j floor(n/j) >= 1 for every
integer cell n <= N, excess E(c) = B(N) - psi(N) = sum_n (W(n) - 1) m_n with
m_n = psi(N/n) - psi(N/(n+1)) the prime mass landing in cell n.

Dual lemma.  If delta: {1..N} -> R has zero floor-moments,
sum_n delta_n floor(n/j) = 0 for j = 1..y, and delta_n >= -m_n for all n, then
E(c) >= sum_n delta_n for every feasible c.  Proof: (W-1) >= 0 and
m_n >= -delta_n give E >= -sum (W-1) delta = -sum_j c_j sum_n delta_n floor(n/j)
+ sum delta = sum delta.

Parametrization.  With tail sums U(k) = sum_{n>=k} delta_n the moment
conditions read sum_{m>=1} U(jm) = 0 (j <= y).  For any T supported on (y, N],
U(k) := sum_m mu(m) T(km) satisfies them (Mobius inversion), with gain
U(1) = sum_{m>y} mu(m) T(m), and the only constraint left is
U(k) - U(k+1) >= -m_k.

Three constructions, each verified directly (moments and slack) before its
gain is reported:

  rough_spike      T = -m_q at each y-rough q: recovers the rough-spike lemma.
  alternating      T = tau mu(m) on (y, Y], tau the largest feasible value.
  restricted_dual  the best T supported on (y, Y]: a small LP whose value is
                   a rigorous lower bound on the full floor V*(y,N) - psi(N),
                   increasing to it as Y -> N.

Floating arithmetic; the verification tolerances are printed.
"""
from __future__ import annotations

import argparse
import json
import math

import numpy as np
from scipy.optimize import linprog

from lp_allcells_cg import mangoldt, mobius_val


def mobius_table(n: int) -> np.ndarray:
    mu = np.ones(n + 1, dtype=np.int64)
    mu[0] = 0
    is_p = np.ones(n + 1, dtype=bool)
    for p in range(2, n + 1):
        if not is_p[p]:
            continue
        is_p[2 * p :: p] = False
        mu[p::p] *= -1
        mu[p * p :: p * p] = 0
    return mu


def cell_masses(N: int) -> np.ndarray:
    """m_n = psi(N/n) - psi(N/(n+1)) for n = 1..N (index n)."""
    psi = np.cumsum(mangoldt(N))
    n = np.arange(1, N + 1)
    m = np.zeros(N + 2)
    m[1:-1] = psi[N // n] - psi[N // (n + 1)]
    return m


def U_from_T(N: int, T: dict[int, float], mu: np.ndarray) -> np.ndarray:
    """U(k) = sum_m mu(m) T(km), k = 1..N+1 (U(N+1) = 0)."""
    U = np.zeros(N + 2)
    for mm, val in T.items():
        if val == 0.0:
            continue
        # every factorization mm = k * m contributes mu(m) * T(mm) to U(k)
        for k in range(1, int(math.isqrt(mm)) + 1):
            if mm % k == 0:
                m = mm // k
                U[k] += mu[m] * val
                if m != k:
                    U[m] += mu[k] * val
    return U


def verify(N: int, y: int, U: np.ndarray, m: np.ndarray) -> dict:
    delta = U[1 : N + 1] - U[2 : N + 2]
    n = np.arange(1, N + 1)
    moments = np.array([float(np.dot(delta, n // j)) for j in range(1, y + 1)])
    slack = delta + m[1 : N + 1]
    return {
        "gain": float(U[1]),
        "max_abs_moment": float(np.abs(moments).max()),
        "min_slack": float(slack.min()),
        "feasible": bool(np.abs(moments).max() < 1e-6 * max(1.0, np.abs(U).max()) and slack.min() > -1e-9),
    }


def rough_spike(N: int, y: int, mu: np.ndarray, m: np.ndarray) -> dict:
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            block = spf[p::p]
            block[block == 0] = p
            spf[p::p] = block
    q = np.arange(y + 1, N + 1)
    q = q[spf[q] > y]
    T = {int(qq): -float(m[qq]) for qq in q if m[qq] > 0}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    out["construction"] = "rough_spike"
    return out


def alternating(N: int, y: int, Y: int, mu: np.ndarray, m: np.ndarray) -> dict:
    T1 = {mm: float(mu[mm]) for mm in range(y + 1, Y + 1) if mu[mm] != 0}
    U1 = U_from_T(N, T1, mu)
    d1 = U1[1 : N + 1] - U1[2 : N + 2]
    neg = d1 < -1e-12
    if not neg.any():
        tau = float("inf")
    else:
        tau = float(np.min(m[1 : N + 1][neg] / (-d1[neg])))
    T = {k: tau * v for k, v in T1.items()}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    out.update({"construction": "alternating", "Y": Y, "tau": tau, "binding_cells": int(np.sum(np.isclose(m[1 : N + 1][neg], tau * (-d1[neg])))) if neg.any() else 0})
    return out


def restricted_dual(N: int, y: int, Y: int, mu: np.ndarray, m: np.ndarray) -> dict:
    """max sum_m mu(m) T(m) over T on (y, Y] s.t. U(k)-U(k+1) >= -m_k for k <= Y."""
    ms = np.arange(y + 1, Y + 1)
    nv = ms.size
    # Build U as a linear map of T: U(k) = sum_{m: km in (y,Y]} mu(m) T(km).
    rows, cols, vals = [], [], []
    for ci, mm in enumerate(ms):
        for k in range(1, int(math.isqrt(mm)) + 1):
            if mm % k == 0:
                mq = mm // k
                rows.append(k); cols.append(ci); vals.append(float(mu[mq]))
                if mq != k:
                    rows.append(mq); cols.append(ci); vals.append(float(mu[k]))
    Umat = np.zeros((Y + 2, nv))
    for r, c_, v in zip(rows, cols, vals):
        Umat[r, c_] += v
    D = Umat[1 : Y + 1] - Umat[2 : Y + 2]  # delta_k for k = 1..Y
    obj = -np.array([float(mu[mm]) for mm in ms])  # minimise -gain
    res = linprog(obj, A_ub=-D, b_ub=m[1 : Y + 1], bounds=(None, None), method="highs")
    if res.status != 0:
        return {"construction": "restricted_dual", "Y": Y, "status": res.message}
    T = {int(mm): float(t) for mm, t in zip(ms, res.x)}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    out.update({"construction": "restricted_dual", "Y": Y, "lp_value": float(-res.fun), "T_abs_max": float(np.abs(res.x).max())})
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, required=True)
    ap.add_argument("--y", type=int, required=True)
    ap.add_argument("--Y", type=int, nargs="*", default=[])
    ap.add_argument("--output", default=None)
    args = ap.parse_args()
    N, y = args.N, args.y
    mu = mobius_table(N)
    m = cell_masses(N)
    results = [rough_spike(N, y, mu, m)]
    Ys = args.Y or [2 * y, 4 * y, 10 * y]
    for Y in Ys:
        Y = min(Y, N)
        results.append(alternating(N, y, Y, mu, m))
        results.append(restricted_dual(N, y, Y, mu, m))
    for r in results:
        print({k: (round(v, 4) if isinstance(v, float) else v) for k, v in r.items()})
    if args.output:
        with open(args.output, "w") as fh:
            json.dump({"N": N, "y": y, "results": results}, fh, indent=1)


if __name__ == "__main__":
    main()
