"""Historical Cheer-Goldston floor computation for a withdrawn transplant.

Cheer-Goldston (PAMS 118 (1993) 365-372) improve Montgomery-Taylor's
RH-conditional bound "N_s >= 0.6725007 N" to 0.6727534 by lower-bounding the
pair sum that Montgomery's argument discards: the zeros lambda_k of the MT
kernel g are not multiples of lambda_1, so consecutive gaps cannot all sit
at kernel zeros -- abutting short gaps force next-to-consecutive gaps where
g > 0. Their argument needs three inputs: the kernel g (with its zeros), a
lower bound nu on the density of consecutive distinct gaps, and the total
length constraint. Nothing else.

The former transplant observation was false. It used conjugate-transpose
rank-one terms where the pinned upstream zero side uses transpose terms.
Consequently ``tr(P1 Q')`` can be negative and the following historical chain
breaks at its middle line:

    ||A||_F^2 = tr P1^2 + 2 tr(P1 Q') + tr Q'^2
    tr P1^2   = s1 + cross          (exact identity, simple on-line zeros)
    tr(P1 Q') >= 0                  (blockwise nonnegativity)
    tr Q'^2   >= 4 tr Q' - 4(s2+p)  (per-eigenvalue (x-2)^2 >= 0 + Prop 4.1)

The LP values below remain useful calibration outputs for the ordered-real
configuration problem, but they imply no unconditional zeta improvement.
See ``CLEAN-KILL-REPORT.md`` and ``clean_kill.py``.

This module computes the bucket floor as an LP: buckets A0 (< a), B0 (a,b),
Nn (b,c), C0 (c,d), R (> d) of consecutive distinct gap counts per unit
density; N2 >= max(2 Nn - nu, 0) next-to-consecutive gaps in (2b, 2c);
adversary minimises  g(a)A0 + g(b)B0 + min_{[c,d]}g * C0 + min_{[2b,2c]}g * N2
subject to the census and total length <= 1.

Controls: reproduce CG's printed floor and constant from their exact edges
(the calibration); a lesion with lambda_2 moved to 2*lambda_1 must kill the
floor (the mechanism IS lambda_2 != 2 lambda_1); a discretization ladder on
the kernel-minimum grid.

Run from the repo root:  .venv/bin/python hunts/frontier_math/cg_transplant.py
"""

from __future__ import annotations

import numpy as np
from scipy.optimize import brentq, linprog

S2 = np.sqrt(2.0)

#: paper Theorem D / MT: N* <= (1/2 + 2^{-1/2} cot(2^{-1/2})) N, H = 2 - that
MT_CONST = 0.5 + (1.0 / S2) / np.tan(1.0 / S2)   # 1.3274992766...
H_PAPER = 2.0 - MT_CONST                          # 0.6725007233...

#: CG's printed values, the calibration targets
CG_EDGES = (1.0233, 1.033396, 1.47, 1.99)
CG_NU = 0.83625
CG_FLOOR = 0.00012636
CG_CONST = 0.6727534


def g_kernel(u):
    """Montgomery-Taylor kernel, g(0) = 1, ghat supported in [-1,1]."""
    u = np.asarray(u, float)
    d1 = S2 - 2 * np.pi * u
    d2 = S2 + 2 * np.pi * u
    A = np.sin(d1 / 2) / np.where(np.abs(d1) > 1e-12, d1, 1.0)
    B = np.sin(d2 / 2) / np.where(np.abs(d2) > 1e-12, d2, 1.0)
    return (A + B) ** 2 / (1.0 - np.cos(S2))


def lambda_roots(kmax: int = 4) -> list[float]:
    """Positive zeros of the MT kernel: 1.05727, 2.03006, 3.02024, ..."""
    f = lambda u: (np.sin((S2 - 2 * np.pi * u) / 2) / (S2 - 2 * np.pi * u)
                   + np.sin((S2 + 2 * np.pi * u) / 2) / (S2 + 2 * np.pi * u))
    return [brentq(f, k + 1e-9, k + 0.5) for k in range(1, kmax + 1)]


class _GTable:
    def __init__(self, n: int = 600001, hi: float = 6.0):
        self.x = np.linspace(0.0, hi, n)
        self.v = g_kernel(self.x)
        self.roots = lambda_roots(max(1, int(np.ceil(hi))))

    def minimum(self, lo: float, hi: float) -> float:
        """Discovery-stage sampled minimum, with known root cells set to zero.

        Away from known roots this remains a sampled value, not a one-sided
        continuum enclosure.
        """
        if any(lo <= root <= hi for root in self.roots):
            return 0.0
        i, j = np.searchsorted(self.x, [lo, hi])
        return float(self.v[max(i - 1, 0): j + 1].min())


def bucket_floor(nu, a, b, c, d, table: _GTable | None = None,
                 g=None) -> float | None:
    """The LP value: the least discarded one-sided pair mass per TL."""
    if g is None:
        g = g_kernel
    if table is None:
        table = _GTable()
    h = table.minimum(c, d)
    j = table.minimum(2 * b, 2 * c)
    cobj = np.array([float(g(np.array([a]))[0]), float(g(np.array([b]))[0]),
                     0.0, h, 0.0, j])
    Aeq = np.array([[1., 1., 1., 1., 1., 0.]])
    beq = np.array([nu])
    Aub = np.array([[0., a, b, c, d, 0.],
                    [0., 0., 2., 0., 0., -1.]])
    bub = np.array([1.0, nu])
    res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * 6, method="highs")
    return float(res.fun) if res.success else None


def optimize_edges(nu, n1=14, n2=14, refine=2, table=None):
    """Coarse-to-fine grid over (a, b, c, d); returns (floor, edges)."""
    lam = lambda_roots(2)
    if table is None:
        table = _GTable()
    box = (0.90, lam[0] - 0.0005, lam[0] + 0.02, 2.95)
    best = (0.0, None)
    for _ in range(refine + 1):
        alo, ahi, clo, chi = box
        for aa in np.linspace(alo, ahi, n1):
            for bb in np.linspace(aa + 1e-4, lam[0] - 2e-4, 8):
                if 2 * bb <= lam[1] + 1e-6:
                    continue
                for cc in np.linspace(clo, chi - 0.05, n2):
                    for dd in np.linspace(cc + 0.03, 2.98, n2):
                        fl = bucket_floor(nu, aa, bb, cc, dd, table)
                        if fl is not None and fl > best[0]:
                            best = (fl, (aa, bb, cc, dd))
        if best[1] is None:
            break
        aa, bb, cc, dd = best[1]
        w1 = (ahi - alo) / n1
        w2 = (chi - clo) / n2
        box = (max(0.9, aa - w1), min(lam[0] - 5e-4, aa + w1),
               max(lam[0] + 0.02, cc - w2), min(2.95, cc + 2 * w2))
    return best


def lesion_wrong_lambda2(nu: float, edges) -> float | None:
    """Kernel with its second zero moved to 2*lambda_1: floor must die.

    If lambda_2 were exactly 2*lambda_1, abutting lambda_1-gaps would land on
    a kernel zero and cost nothing; the mechanism vanishes. Implemented by
    evaluating the floor with j (the [2b,2c] minimum) forced to 0.
    """
    a, b, c, d = edges
    table = _GTable()
    h = table.minimum(c, d)
    cobj = np.array([float(g_kernel(np.array([a]))[0]),
                     float(g_kernel(np.array([b]))[0]), 0.0, h, 0.0, 0.0])
    Aeq = np.array([[1., 1., 1., 1., 1., 0.]])
    beq = np.array([nu])
    Aub = np.array([[0., a, b, c, d, 0.], [0., 0., 2., 0., 0., -1.]])
    bub = np.array([1.0, nu])
    res = linprog(cobj, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, None)] * 6, method="highs")
    return float(res.fun) if res.success else None


def main() -> None:
    lam = lambda_roots()
    print("lambda_k:", ", ".join(f"{x:.5f}" for x in lam))
    print(f"MT constant {MT_CONST:.9f}; paper H = {H_PAPER:.7f}")

    fl = bucket_floor(CG_NU, *CG_EDGES)
    print(f"control  CG edges/nu:      floor = {fl:.8f}   (CG printed {CG_FLOOR})")
    print(f"         conditional H >= {2 - (MT_CONST - 2 * fl):.7f}   (CG: {CG_CONST})")

    nu_on = H_PAPER  # bootstrap: simple on-line zeros are distinct on-line points
    best = optimize_edges(nu_on)
    print(f"withdrawn arithmetic  nu_on = {nu_on:.7f}: floor c_u = {best[0]:.8f} "
          f"at edges {tuple(round(x, 5) for x in best[1])}")
    print(f"         withdrawn arithmetic value = {H_PAPER + 2 * best[0]:.7f}")

    le = lesion_wrong_lambda2(nu_on, best[1])
    print(f"lesion  (lambda_2 -> 2 lambda_1): floor = {le:.8f}  (must be ~0)")

    for n in (150001, 600001, 2400001):
        t = _GTable(n=n)
        fl_n = bucket_floor(nu_on, *best[1], table=t)
        print(f"ladder  g-table n={n}: floor = {fl_n:.10f}")


if __name__ == "__main__":
    main()
