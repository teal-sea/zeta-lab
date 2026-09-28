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
    """Two statements.  Primal (Lemma 3): W(q) >= 2 at every y-rough q, so
    E >= sum over y-rough q in (y, N] of m_q; reported as `primal_bound`.
    Dual: T(q) = -m_q at PRIMES q > y only (for a composite y-rough q = p1 p2
    the term mu(p2) T(q) lands in U(p1) and mu(q) T(q) flips the gain), giving
    U(1) = sum_{p > y prime} m_p, U(p) = -m_p, and (C) holds; reported as
    `gain`.  The two coincide when (y, N] holds no composite y-rough number."""
    spf = np.zeros(N + 1, dtype=np.int64)
    for p in range(2, N + 1):
        if spf[p] == 0:
            block = spf[p::p]
            block[block == 0] = p
            spf[p::p] = block
    q = np.arange(y + 1, N + 1)
    rough = q[spf[q] > y]
    primes = rough[spf[rough] == rough]
    T = {int(p): -float(m[p]) for p in primes if m[p] > 0}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    out["construction"] = "rough_spike"
    out["primal_bound"] = float(m[rough].sum())
    out["n_rough"] = int(rough.size)
    out["n_prime"] = int(primes.size)
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


def staircase(N: int, y: int, Y: int, mu: np.ndarray, m: np.ndarray, sign: int = -1) -> dict:
    """T = sign * theta * A on (y, Y], A(m) = sum_{m<=k<=Y} m_k the prime mass
    beyond m.  In the top layer (k > Y/2) U(k) = T(k) rises by exactly theta m_k
    at every cell, so (C) holds there for theta <= 1 when sign = -1.  The
    largest feasible theta overall is computed from the lower layers, and the
    gain is theta * sign * sum_{y<m<=Y} mu(m) A(m): a Mobius increment."""
    A = np.zeros(N + 2)
    A[: Y + 1] = np.cumsum(m[: Y + 1][::-1])[::-1]  # A(k) = sum_{k<=i<=Y} m_i
    T1 = {mm: float(sign * A[mm]) for mm in range(y + 1, Y + 1) if A[mm] != 0.0}
    U1 = U_from_T(N, T1, mu)
    d1 = U1[1 : N + 1] - U1[2 : N + 2]
    neg = d1 < -1e-12
    theta = float(np.min(m[1 : N + 1][neg] / (-d1[neg]))) if neg.any() else 1.0
    theta = min(theta, 1.0)
    binding = np.nonzero(neg & np.isclose(m[1 : N + 1] / np.where(neg, -d1, 1.0), theta))[0] + 1 if neg.any() else np.array([], dtype=int)
    T = {k: theta * v for k, v in T1.items()}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    G = float(sign * sum(mu[mm] * A[mm] for mm in range(y + 1, Y + 1)))
    out.update({"construction": "staircase", "sign": sign, "Y": Y, "theta": theta, "G_unscaled": G, "binding_cells": [int(k) for k in binding[:12]], "n_binding": int(binding.size)})
    return out


def tapered_staircase(N: int, y: int, Y: int, mu: np.ndarray, m: np.ndarray, L: int | None = None) -> dict:
    """T = -theta A(m) w(m) with the ramp w(m) = min(1, (m - y)/L), L = y by
    default.  The ramp spreads the left-boundary rises of U (which the pure
    staircase concentrates on the cells floor(y/j), mu(j) = -1) over L cells
    each.  theta is the largest feasible scale; gain theta * G with
    G = -sum mu(m) A(m) w(m), a smoothed Mobius increment over (y, Y]."""
    L = L or y
    A = np.zeros(N + 2)
    A[: Y + 1] = np.cumsum(m[: Y + 1][::-1])[::-1]
    T1 = {}
    for mm in range(y + 1, Y + 1):
        w = min(1.0, (mm - y) / L)
        if A[mm] * w != 0.0:
            T1[mm] = -float(A[mm] * w)
    U1 = U_from_T(N, T1, mu)
    d1 = U1[1 : N + 1] - U1[2 : N + 2]
    neg = d1 < -1e-12
    theta = float(np.min(m[1 : N + 1][neg] / (-d1[neg]))) if neg.any() else 1.0
    theta = min(theta, 1.0)
    binding = np.nonzero(neg & np.isclose(m[1 : N + 1] / np.where(neg, -d1, 1.0), theta))[0] + 1 if neg.any() else np.array([], dtype=int)
    T = {k: theta * v for k, v in T1.items()}
    U = U_from_T(N, T, mu)
    out = verify(N, y, U, m)
    G = -sum(T1[mm] for mm in T1) * 0.0  # placeholder to keep types simple
    G = float(-sum(mu[mm] * (-T1[mm]) for mm in T1))
    out.update({"construction": "tapered_staircase", "Y": Y, "L": L, "theta": theta, "G_unscaled": G, "binding_cells": [int(k) for k in binding[:12]], "n_binding": int(binding.size)})
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
        results.append(staircase(N, y, Y, mu, m, sign=-1))
        results.append(tapered_staircase(N, y, Y, mu, m))
        results.append(restricted_dual(N, y, Y, mu, m))
    for r in results:
        print({k: (round(v, 4) if isinstance(v, float) else v) for k, v in r.items()})
    if args.output:
        with open(args.output, "w") as fh:
            json.dump({"N": N, "y": y, "results": results}, fh, indent=1)


if __name__ == "__main__":
    main()
