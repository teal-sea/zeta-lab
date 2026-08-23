#!/usr/bin/env python3
"""Numerical probe of the two forms of S2, and of the tightness reading.

The inequalities themselves are kernel-checked in
`hunts/frontier_math/zeta23ext/Zeta23Ext/StableRankTrace.lean`, so this script is
not evidence that they hold.  It answers two different questions that a Lean
proof does not:

1. **Is the bound a real constraint, or is the slack always large?**  Random
   instances measure the gap.
2. **Is the sharp form attained on the family that `Zeta23.ZeroSide.TightMult`
   proves makes Lemma R an equality** (integer multiplicities `1 <= m_j <= c` on
   orthonormal vectors plus `b` pair-blocks of eigenvalue `c`)?  §8 of
   ARISTOTLE-PROBE.md reads that off two upstream statements; this measures it.

Run:  .venv/bin/python hunts/ainta_seven_point/check_stable_rank_trace.py
"""

from __future__ import annotations

import numpy as np


def psi(t):
    """Ainta's profile.  Equals upstream `gc 2` plus one."""
    t = np.asarray(t, dtype=float)
    return np.where(t <= 2.0, (t - 1.0) ** 2, 2.0 * t - 3.0)


def gc2(t):
    """Upstream `gc c x = x^2 - c x - ((x-c)+)^2` at `c = 2`."""
    t = np.asarray(t, dtype=float)
    return t**2 - 2.0 * t - np.maximum(t - 2.0, 0.0) ** 2


def sides(V, Q):
    """Return (lhs_sharp, lhs_trustmap, rhs) for a given V and Hermitian Q."""
    P = V @ V.conj().T
    M = P + Q
    rhs = float(np.real(np.trace(M.conj().T @ M)))            # frobSq
    tr_P = float(np.real(np.trace(P)))
    tr_Q = float(np.real(np.trace(Q)))
    card_r = V.shape[1]
    qeig = np.linalg.eigvalsh((Q + Q.conj().T) / 2)
    tol = 1e-9 * max(1.0, float(np.max(np.abs(qeig))) if qeig.size else 1.0)
    b = int(np.sum(qeig > tol))                                # posIndex, with a
                                                               # tolerance: the
                                                               # structured family
                                                               # has exact zeros
                                                               # that float noise
                                                               # pushes positive.
    mu = np.linalg.eigvalsh(V.conj().T @ V)
    defect = float(np.sum(psi(mu)))                            # rtrace (specMap _ Psi)
    lhs_sharp = 2 * tr_P + 4 * tr_Q - card_r - 4 * b + defect
    lhs_map = 4 * (tr_P + tr_Q) - 3 * card_r - 4 * b + defect
    return lhs_sharp, lhs_map, rhs, b


def main() -> None:
    rng = np.random.default_rng(20260823)

    # --- 0. the identification, pointwise -----------------------------------
    grid = np.linspace(-3.0, 8.0, 100001)
    ident = float(np.max(np.abs(psi(grid) - (gc2(grid) + 1.0))))
    print(f"[0] max |Psi - (gc2 + 1)| over [-3, 8]:          {ident:.3e}")

    # --- 1. random instances, complex, columns normalised to <= 1 -----------
    worst_sharp = np.inf
    worst_map = np.inf
    for _ in range(4000):
        n = int(rng.integers(2, 9))
        r = int(rng.integers(1, 9))
        V = rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))
        colnorm = np.linalg.norm(V, axis=0)
        V = V / np.maximum(colnorm, 1e-12) * rng.uniform(0.0, 1.0, size=r)
        A = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        Q = (A + A.conj().T) / 2 * rng.uniform(0.0, 3.0)
        ls, lm, rhs, _ = sides(V, Q)
        worst_sharp = min(worst_sharp, rhs - ls)
        worst_map = min(worst_map, rhs - lm)
    print(f"[1] 4000 random (hV-satisfying) instances")
    print(f"    min slack, sharp form:                       {worst_sharp:+.6f}")
    print(f"    min slack, trust-map form:                   {worst_map:+.6f}")

    # --- 2. random instances with NO column bound (sharp form only) ---------
    worst_free = np.inf
    for _ in range(4000):
        n = int(rng.integers(2, 9))
        r = int(rng.integers(1, 9))
        V = (rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))) * rng.uniform(0.1, 3.0)
        A = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
        Q = (A + A.conj().T) / 2 * rng.uniform(0.0, 3.0)
        ls, _, rhs, _ = sides(V, Q)
        worst_free = min(worst_free, rhs - ls)
    print(f"[2] 4000 random instances with hV VIOLATED")
    print(f"    min slack, sharp form:                       {worst_free:+.6f}")

    # --- 3. the tightness family of Zeta23.ZeroSide.TightMult ---------------
    # P = sum_j m_j v_j v_j^H on orthonormal v_j with m_j in {1, 2};
    # Q = 2 * (projector onto b further orthonormal directions), so n+(Q) = b.
    print("[3] the TightMult family (orthonormal columns, m_j in {1,2}, c = 2)")
    worst_family = 0.0
    for _ in range(400):
        s = int(rng.integers(1, 6))
        b = int(rng.integers(0, 4))
        n = s + b + int(rng.integers(0, 3))
        m = rng.integers(1, 3, size=s).astype(float)
        Uq, _ = np.linalg.qr(rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n)))
        Vcols = Uq[:, :s] * np.sqrt(m)                   # column j has norm^2 = m_j
        Qdirs = Uq[:, s : s + b]
        Q = 2.0 * (Qdirs @ Qdirs.conj().T)
        ls, _, rhs, bb = sides(Vcols, Q)
        assert bb == b, (bb, b)
        worst_family = max(worst_family, abs(rhs - ls))
    print(f"    max |slack| over 400 instances:              {worst_family:.3e}")
    print("    (zero slack = the sharp form is an EQUALITY on this family)")

    # --- 4. how much the trust-map form gives away --------------------------
    print("[4] gap between the two forms on the hV-satisfying draws")
    give = []
    for _ in range(2000):
        n = int(rng.integers(2, 9))
        r = int(rng.integers(1, 9))
        V = rng.normal(size=(n, r)) + 1j * rng.normal(size=(n, r))
        colnorm = np.linalg.norm(V, axis=0)
        V = V / np.maximum(colnorm, 1e-12) * rng.uniform(0.0, 1.0, size=r)
        P = V @ V.conj().T
        give.append(2 * (V.shape[1] - float(np.real(np.trace(P)))))
    give = np.array(give)
    print(f"    2*(card r - tr P):  min {give.min():.4f}  mean {give.mean():.4f}  max {give.max():.4f}")


if __name__ == "__main__":
    main()
