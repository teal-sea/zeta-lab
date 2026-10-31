"""Circularity challenger's recomputation for positivity_geometry (hunt #150).

Written by the circularity challenger, sharing no code with ``frobenius_span.py``.
Nothing here imports the construction. Every routine prints or returns numbers
and writes nothing into the tree.

Checks:

1. The golden fake Z(T) = (1 - 5T + 5T^2)/((1 - T)(1 - 5T)): closed-point counts
   b_d and the quadratic split/inert counts over F_5(t) with ramification
   {deg 1, deg 3}, exact integers, to a degree far past the builder's 40/60.
2. The window-2g lemma (NOTES section 2.4) on arbitrary inversion- and
   conjugation-closed multisets, not only Weil-type integer polynomials.
3. G1/G2 for the rival zeta(s - delta), which the NOTES table omits, and an
   independent recomputation of Lambda_DH(6) = (1 + kappa^2) log 6.
"""
from __future__ import annotations

import random
import sys
from fractions import Fraction

from mpmath import mp


def mobius(n: int) -> int:
    res, m, p = 1, n, 2
    while p * p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0:
                return 0
            res = -res
        p += 1
    return -res if m > 1 else res


def divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def golden_traces(n_max: int, q: int = 5, a: int = 5) -> list[int]:
    """t_n = alpha^n + beta^n for x^2 - a x + q, by the recurrence; t_0 = 2."""
    t = [2, a]
    while len(t) <= n_max:
        t.append(a * t[-1] - q * t[-2])
    return t


def closed_points(n_max: int, q: int = 5, a: int = 5) -> list[int]:
    """b_d for d = 1..n_max from N_n = q^n + 1 - t_n; asserts integrality."""
    t = golden_traces(n_max, q, a)
    N = [None] + [q ** n + 1 - t[n] for n in range(1, n_max + 1)]
    out = []
    for d in range(1, n_max + 1):
        s = sum(mobius(d // e) * N[e] for e in divisors(d))
        assert s % d == 0, d
        out.append(s // d)
    return out


def places(q: int, d: int) -> int:
    """Places of F_q(t) of degree d: monic irreducibles of degree d, plus infinity at d = 1."""
    s = sum(mobius(d // e) * q ** e for e in divisors(d))
    return s // d + (1 if d == 1 else 0)


def quadratic_split(n_max: int, q: int = 5, a: int = 5, ram=None):
    """Split/inert counts (s_d, i_d) forced by P(T) = 1 - aT + qT^2 over F_q(t).

    Exponents c_d of P = prod (1 - T^d)^(-c_d) satisfy sum_{d|n} d c_d = -t_n.
    Then 2 s_d + r_d + i_{d/2} = pi(d) + c_d and s_d + i_d + r_d = pi(d).
    Returns lists (s, i) indexed from d = 1, as Fractions so that a failure of
    integrality shows instead of being rounded away.
    """
    ram = ram or {1: 1, 3: 1}
    t = golden_traces(n_max, q, a)
    c = {}
    for n in range(1, n_max + 1):
        c[n] = Fraction(-t[n] - sum(d * c[d] for d in divisors(n) if d < n), n)
    s, i = {}, {}
    for d in range(1, n_max + 1):
        r = ram.get(d, 0)
        half = i.get(d // 2, 0) if d % 2 == 0 else 0
        s[d] = (places(q, d) + c[d] - r - half) / 2
        i[d] = places(q, d) - r - s[d]
    return [s[d] for d in range(1, n_max + 1)], [i[d] for d in range(1, n_max + 1)]


def toeplitz_min_eig(us, m: int, dps: int = 30):
    """Smallest eigenvalue of T_m = [sum_i u_i^(a-b)]_{0<=a,b<m}."""
    with mp.workdps(dps):
        T = mp.matrix(m, m)
        for x in range(m):
            for y in range(m):
                T[x, y] = mp.re(sum(mp.mpc(u) ** (x - y) for u in us))
        ev = mp.eigsy(T, eigvals_only=True)
        return min(ev)


def random_closed_multiset(g: int, off: bool, rng: random.Random):
    """2g values closed under conjugation and inversion; on the circle unless off."""
    us = []
    while len(us) < 2 * g:
        th = rng.uniform(0.1, 3.0)
        if off and not us and rng.random() < 0.5:
            r = rng.uniform(1.05, 2.0)
            z = mp.mpc(r * mp.cos(th), r * mp.sin(th))
            us += [z, mp.conj(z), 1 / z, 1 / mp.conj(z)]
        elif off and not us:
            r = rng.uniform(1.05, 2.0)
            us += [mp.mpf(r), 1 / mp.mpf(r)]
        else:
            z = mp.mpc(mp.cos(th), mp.sin(th))
            us += [z, mp.conj(z)]
    return us[: 2 * g]


def log_derivative(coef, n_max: int, dps: int = 30):
    """Lambda_F(n) from a(n): a(n) log n = sum_{d | n} Lambda(d) a(n/d), a(1) = 1."""
    with mp.workdps(dps):
        lam = [mp.mpf(0)] * (n_max + 1)
        for n in range(2, n_max + 1):
            acc = coef(n) * mp.log(n)
            for d in divisors(n)[:-1]:
                acc -= lam[d] * coef(n // d)
            lam[n] = acc
        return lam


def is_prime_power(n: int) -> bool:
    p = next(p for p in range(2, n + 1) if n % p == 0)
    while n % p == 0:
        n //= p
    return n == 1


def shifted_zeta_g1(delta, n_max: int = 60, dps: int = 30) -> dict:
    with mp.workdps(dps):
        lam = log_derivative(lambda n: mp.mpf(n) ** delta, n_max, dps)
        tol = mp.mpf(10) ** (-(dps - 8))
        neg = [n for n in range(2, n_max + 1) if lam[n] < -tol]
        off = [n for n in range(2, n_max + 1) if not is_prime_power(n) and abs(lam[n]) > tol]
        eps = mp.mpf(10) ** (-12)
        res = eps * mp.zeta(1 + eps)  # residue of zeta(s - delta) at s = 1 + delta
        return {"first_negative": neg[:1], "first_off_prime_power": off[:1], "residue": res}


def dh_lambda6(dps: int = 30):
    with mp.workdps(dps):
        kappa = (mp.sqrt(10 - 2 * mp.sqrt(5)) - 2) / (mp.sqrt(5) - 1)
        per = {0: 0, 1: 1, 2: kappa, 3: -kappa, 4: -1}
        lam = log_derivative(lambda n: per[n % 5], 6, dps)
        return lam[2], lam[3], lam[6], (1 + kappa ** 2) * mp.log(6), kappa


def main() -> int:
    D = 300
    b = closed_points(D)
    print("golden fake b_1..b_8:", b[:8], " min over d<=%d:" % D, min(b))
    s, i = quadratic_split(D)
    ok = all(x.denominator == 1 and x >= 0 for x in s + i)
    print("split 1..8:", [int(x) for x in s[:8]])
    print("inert 1..8:", [int(x) for x in i[:8]])
    print("split/inert nonnegative integers to d = %d:" % D, ok)
    rng = random.Random(150)
    bad = 0
    for g in (2, 3, 4):
        for off in (False, True):
            for _ in range(20):
                us = random_closed_multiset(g, off, rng)
                ev = toeplitz_min_eig(us, 2 * g)
                if (ev < -mp.mpf(10) ** -15) != off:
                    bad += 1
    print("window-2g lemma, 120 random closed multisets, disagreements:", bad)
    for delta in (Fraction(1, 10), Fraction(1, 4)):
        r = shifted_zeta_g1(mp.mpf(delta.numerator) / delta.denominator)
        print("zeta(s - %s): first negative %s, first off prime power %s, residue at 1+delta %s"
              % (delta, r["first_negative"], r["first_off_prime_power"], mp.nstr(r["residue"], 12)))
    l2, l3, l6, cf, kappa = dh_lambda6()
    print("DH: Lambda(2)/log2 =", mp.nstr(l2 / mp.log(2), 15), " kappa =", mp.nstr(kappa, 15))
    print("DH: Lambda(3)/log3 =", mp.nstr(l3 / mp.log(3), 15))
    print("DH: Lambda(6) =", mp.nstr(l6, 20), " (1+kappa^2) log 6 =", mp.nstr(cf, 20))
    return 0


if __name__ == "__main__":
    sys.exit(main())
