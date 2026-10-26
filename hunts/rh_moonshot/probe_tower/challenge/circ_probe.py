"""Circularity challenger's recomputation for probe_tower (hunt #150).

Written by the circularity challenger, sharing no code with ``tower_template.py``.
It rebuilds, from the formulas quoted in NOTES section 2.2 only:

1. sigma_0(k) from the signal exponent and the direct bound, symbolically in k
   (sympy), and its value at the paper's geometry for k = 6;
2. the walls of NOTES section 3.2 by exact vertex enumeration of the LP over
   (ell, M, b) in Fractions (no LP solver, no dual multipliers taken from the
   builder);
3. DH's correction H = DH * (c1/L(chi) + c2/L(chibar)) at its off-line zero,
   with L(s, chi) built from Hurwitz zeta, not from ``zeta.epstein``;
4. the rival zeta(s - delta), which the NOTES do not test: its squarefree
   Moebius sum is 1/zeta(s - delta) exactly, so it passes (E_k) with H = 1.

Writes nothing into the tree.
"""
from __future__ import annotations

import itertools
import sys
from fractions import Fraction as Fr

import sympy as sp
from mpmath import mp


def sigma0_symbolic():
    k, M, ell, b = sp.symbols("k M ell b", positive=True)
    lx = (M - b) / 2
    h = 1 - lx + ell
    c = lx / 2 - 1 + h / k            # signal exponent offset, NOTES 2.2
    direct = lx / 2 + b / (2 * k)     # direct bound exponent, NOTES 2.2
    sig = sp.simplify(direct - c)     # C(sigma_0) = sigma_0 + c = direct bound
    closed = 1 - 1 / k + (M - 2 * ell) / (2 * k)
    return sig, sp.simplify(sig - closed), sig.subs({k: 6, M: sp.Rational(5, 6), ell: sp.Rational(1, 6), b: sp.Rational(1, 8)})


def dual_identity_residual(y1_scale=1):
    """(M - 2 ell) - m* - [y1 (-floor) + y2 (1 - M - ell) + y3 b], symbolic in k and
    delta0, with the multipliers quoted in NOTES section 3.2; 0 means the floor wall
    is a valid lower bound for every geometry whenever y1, y2, y3 >= 0 (k >= 2)."""
    k, M, ell, b, d = sp.symbols("k M ell b delta0")
    floor = sp.Rational(1, 2) + ell / 2 - sp.Rational(3, 4) * M + b * (sp.Rational(1, 4) - 1 / (2 * k)) + (1 + ell - M / 2) * d
    m_star = (2 + 12 * d) / (5 + 6 * d)
    y1, y2 = y1_scale * 12 / (5 + 6 * d), 4 / (5 + 6 * d)
    y3 = y1 * (sp.Rational(1, 4) - 1 / (2 * k))
    return sp.simplify((M - 2 * ell) - m_star - (y1 * (-floor) + y2 * (1 - M - ell) + y3 * b))


def _solve3(rows):
    """Solve a 3x3 system [A | r] in Fractions; None if singular."""
    A = [list(r) for r in rows]
    for col in range(3):
        piv = next((i for i in range(col, 3) if A[i][col] != 0), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        for i in range(3):
            if i != col and A[i][col] != 0:
                f = A[i][col] / A[col][col]
                A[i] = [x - f * y for x, y in zip(A[i], A[col])]
    return [A[i][3] / A[i][i] for i in range(3)]


def lp_min_m(k: int, delta0: Fr | None, floor: bool):
    """min of M - 2 ell over ell, b >= 0, M - b >= 0, M + ell <= 1 [, floor rows].

    Constraints as a.x <= r with x = (ell, M, b). Floor row (NOTES 2.2):
    1/2 + ell/2 - 3M/4 + b(1/4 - 1/(2k)) + (1 + ell - M/2) delta0 <= 0.
    """
    cons = [((-1, 0, 0), 0), ((0, 0, -1), 0), ((0, -1, 1), 0), ((1, 1, 0), 1)]
    if floor:
        d = delta0
        cons.append(((Fr(1, 2) + d, Fr(-3, 4) - d / 2, Fr(1, 4) - Fr(1, 2 * k)), -Fr(1, 2) - d))
    cons = [(tuple(Fr(x) for x in a), Fr(r)) for a, r in cons]
    best = None
    for tri in itertools.combinations(cons, 3):
        x = _solve3([list(a) + [r] for a, r in tri])
        if x is None:
            continue
        if all(sum(ai * xi for ai, xi in zip(a, x)) <= r for a, r in cons):
            m = x[1] - 2 * x[0]
            if best is None or m < best[0]:
                best = (m, tuple(x))
    return best


def sigma0_from_m(k: int, m: Fr) -> Fr:
    return 1 - Fr(1, k) + m / (2 * k)


def dh_correction_at_zero(dps: int = 30) -> dict:
    with mp.workdps(dps + 10):
        kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
        c1 = (1 - 1j * kappa) / 2
        c2 = (1 + 1j * kappa) / 2
        chi = {1: 1, 2: 1j, 3: -1j, 4: -1}
        rho = mp.mpc("0.80851718245663738", "85.69934848537759")
        rho = mp.findroot(lambda s: _dh(s, c1, c2, chi), rho)

        def L(s, conj):
            return 5 ** (-s) * sum((mp.conj(chi[a]) if conj else chi[a]) * mp.zeta(s, mp.mpf(a) / 5) for a in range(1, 5))

        L1, L2 = L(rho, False), L(rho, True)
        dh = c1 * L1 + c2 * L2
        R = c1 / L1 + c2 / L2
        H = dh * R
        closed = c1 * c2 * (L1 - L2) ** 2 / (L1 * L2)
        return {"rho": rho, "absDH": abs(dh), "absL1": abs(L1), "absL2": abs(L2),
                "absR": abs(R), "absHminus1": abs(H - 1), "closed_gap": abs((H - 1) - closed)}


def _dh(s, c1, c2, chi):
    tot = 0
    for a in range(1, 5):
        tot += (c1 * chi[a] + c2 * mp.conj(chi[a])) * mp.zeta(s, mp.mpf(a) / 5)
    return 5 ** (-s) * tot


def squarefree_moebius_sum(f, s, n_max: int):
    """sum over squarefree n <= n_max of mu(n) f(n) n^(-s), by a sieve."""
    mu = [1] * (n_max + 1)
    is_comp = [False] * (n_max + 1)
    for p in range(2, n_max + 1):
        if not is_comp[p]:
            for j in range(p, n_max + 1, p):
                if j > p:
                    is_comp[j] = True
                mu[j] = -mu[j]
            for j in range(p * p, n_max + 1, p * p):
                mu[j] = 0
    return sum(mu[n] * f(n) * mp.mpf(n) ** (-s) for n in range(1, n_max + 1) if mu[n] != 0)


def main() -> int:
    sig, gap, at6 = sigma0_symbolic()
    print("sigma_0 =", sig, "| minus closed form:", gap, "| at paper geometry k=6:", at6)
    print("k  dual-only        floor(delta0=0)   floor(delta0=1/50)")
    for k in (2, 3, 4, 5, 6, 7, 8, 12, 100):
        d = lp_min_m(k, None, floor=False)
        f0 = lp_min_m(k, Fr(0), floor=True)
        f1 = lp_min_m(k, Fr(1, 50), floor=True)
        print(k, sigma0_from_m(k, d[0]), sigma0_from_m(k, f0[0]), f0[1], sigma0_from_m(k, f1[0]))
    inc = all(sigma0_from_m(k + 1, lp_min_m(k + 1, Fr(0), True)[0]) > sigma0_from_m(k, lp_min_m(k, Fr(0), True)[0])
              for k in range(2, 40))
    print("floor wall strictly increasing for k = 2..40:", inc)
    print("dual-multiplier identity residual (symbolic in k, delta0):", dual_identity_residual())
    with mp.workdps(30):
        r = dh_correction_at_zero()
        print("DH zero (refined):", mp.nstr(r["rho"], 20))
        for key in ("absDH", "absL1", "absL2", "absR", "absHminus1", "closed_gap"):
            print("  ", key, mp.nstr(r[key], 8))
        for delta in (mp.mpf(1) / 4, mp.mpf(1) / 10):
            s = mp.mpf(3)
            S = squarefree_moebius_sum(lambda n: mp.mpf(n) ** delta, s, 20000)
            print("zeta(s-%s): squarefree Moebius sum at s=3 to 20000 = %s, 1/zeta(3-delta) = %s"
                  % (mp.nstr(delta, 3), mp.nstr(S, 12), mp.nstr(1 / mp.zeta(s - delta), 12)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
