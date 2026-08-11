"""THREAD 1's LP: pair-measure data, positivity, multiplicity types.

Model. Unfolded zero configuration at density 1 as weighted marked points:
p_m = density of on-line points of multiplicity m; q = density of off-line
pairs (depth -> 0, the extremal case per the paper's section 7.5(b)); the
off-diagonal pair measure rho = 1 + tau with tau >= -1 (positivity of pair
counts). Bandwidth-one data: R2hat(alpha) = delta(alpha) + |alpha| on
[-1,1], i.e. D + tauhat(alpha) = alpha on [0,1] with D = sum m^2 p_m + 4q.
Sanity anchor: GUE (all simple) has tau = -sinc^2, tauhat = alpha - 1. The
optional out-of-band constraint D + tauhat(alpha) >= 0 for alpha in (1, A]
is the form-factor nonnegativity that BGSTB 2023 (arXiv:2306.04799,
Theorem 1) prove unconditionally.

Discretisation: tau on a grid of step h truncated at X (a RESTRICTION of the
adversary; values decrease as X grows), data constraints on an alpha-grid of
J+1 points as a band of half-width eps (the truncation error floor is
~1/(pi^2 X); values increase as eps shrinks). The objective reduction
p1 = 2 - D + sum_{m>=3}(m^2-2m) p_m (+0*q) means the in-band LP value is
exactly 2 - sup D over the discretised feasible set: the LP measures the
Montgomery-Taylor dual.

Run from the repo root:
    .venv/bin/python hunts/frontier_math/configuration_lp.py          # ladder
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import linprog


def reconstruct_p1(type_densities, off_pair_density=0):
    """Exact elimination identity from density and diagonal mass.

    ``type_densities[m]`` is ``p_m``. The function deliberately performs no
    float conversion, so callers may use ``fractions.Fraction``.
    """

    total_density = sum(m * p for m, p in type_densities.items()) + 2 * off_pair_density
    diagonal_mass = sum(m * m * p for m, p in type_densities.items()) + 4 * off_pair_density
    correction = sum(
        (m * m - 2 * m) * p for m, p in type_densities.items() if m >= 3
    )
    return 2 * total_density - diagonal_mass + correction


def solve(J=640, X=160.0, h=1 / 16, eps=2.5e-3, M=6, A_out=None,
          objective="simple"):
    """One LP solve; returns None if infeasible (eps below the floor)."""
    n = int(round(X / h))
    x = h * (np.arange(1, n + 1) - 0.5)
    a = np.arange(J + 1) / J
    nv = n + M + 1
    row_m = np.array([m * m for m in range(1, M + 1)], float)
    Cin = 2.0 * h * np.cos(2.0 * np.pi * np.outer(a, x))
    rows = [Cin, -Cin]
    rhs = [a + eps, -(a - eps)]
    if A_out is not None:
        aout = 1.0 + np.arange(1, int((A_out - 1) * J) + 1) / J
        Cout = 2.0 * h * np.cos(2.0 * np.pi * np.outer(aout, x))
        rows.append(-Cout)
        rhs.append(np.zeros(len(aout)))
    nrows = sum(r.shape[0] for r in rows)
    Aub = np.zeros((nrows, nv))
    bub = np.concatenate(rhs)
    at = 0
    for blk, sgn in zip(rows, (1.0, -1.0, -1.0)):
        m_ = blk.shape[0]
        Aub[at:at + m_, :n] = blk
        Aub[at:at + m_, n:n + M] = sgn * row_m
        Aub[at:at + m_, n + M] = sgn * 4.0
        at += m_
    Aeq = np.zeros((1, nv))
    beq = np.array([1.0])
    Aeq[0, n:n + M] = np.arange(1, M + 1)
    Aeq[0, n + M] = 2.0
    c = np.zeros(nv)
    if objective == "simple":
        c[n] = 1.0
    elif objective == "distinct":
        c[n:n + M] = 1.0
        c[n + M] = 2.0
    bounds = [(-1.0, None)] * n + [(0.0, None)] * (M + 1)
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds,
                  method="highs")
    if not res.success:
        return None
    return {"value": float(res.fun),
            "D": float(row_m @ res.x[n:n + M] + 4 * res.x[n + M]),
            "p": res.x[n:n + M], "q": float(res.x[n + M])}


def ladder(A_out=None, cases=None):
    """The (X, J, eps) ladder used in RESULTS; eps = 0.4/X tracks the floor."""
    if cases is None:
        cases = [(40.0, 200), (80.0, 320), (160.0, 640)]
    out = []
    for X, J in cases:
        r = solve(J=J, X=X, eps=0.4 / X, A_out=A_out)
        out.append((X, J, 0.4 / X, r["value"] if r else None,
                    r["D"] if r else None))
    return out


if __name__ == "__main__":
    print("in-band (positivity + types); paper Theorem D floor 0.6725007:")
    for X, J, eps, v, D in ladder():
        print(f"  X={X:5.0f} J={J:4d} eps={eps:.1e}: min p1 = {v:.7f}  D = {D:.6f}")
    print("with out-of-band F >= 0 (BGSTB), A = 3 (the CGdL-class analogue):")
    for X, J, eps, v, D in ladder(A_out=3.0, cases=[(40.0, 200), (80.0, 320)]):
        print(f"  X={X:5.0f} J={J:4d} eps={eps:.1e}: min p1 = {v:.7f}  D = {D:.6f}")
