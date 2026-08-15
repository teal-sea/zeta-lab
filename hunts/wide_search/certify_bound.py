"""Exact rational certificate for the xi' window ceiling: c* <= C and H* < 86957/100000.

Setting (RESULTS-xiprime-global-optimality.md). I = [-1/2, 1/2], A = I + T on
L^2_even(I), (Tv)(s) = int_I F_1(s-t) v(t) dt with the Farmer-Gonek-Lee kernel

    F_1(x) = |x| - 4x^2 + sum_{k>=1} a_k |x|^{2k+1},   a_k = 2^{2k+1} (k-1)!/(2k)!,

c* = <1, A^{-1} 1>, H* = 2 - 1/c*, and the established coercivity bound
||A^{-1}|| <= 9/5.

Certificate. Split A = A_0 + E, where A_0 uses the kernel truncated at k = M and
E is the integral operator of the omitted tail R_M(x) = sum_{k>M} a_k |x|^{2k+1}.
With rho >= sup_{|x|<=1} R_M(x) and |I| = 1, Schur's test gives ||E|| <= rho, so
|<u,Eu>| <= rho ||u||^2 and ||Eu|| <= rho ||u||. For any trial u, writing
r = 1 - Au and w = A^{-1} 1 = u + A^{-1} r,

    c* = <1,u> + <w,r> = 2<1,u> - <u,Au> + <A^{-1} r, r>
       <= 2<1,u> - <u,A_0 u> + rho ||u||^2 + (9/5) (||1 - A_0 u|| + rho ||u||)^2 =: C.

Every quantity on the right is an exact rational (u is a rational even
polynomial, A_0 u is a rational polynomial on I) except the two square roots,
which are replaced by rational upper bounds. Since c* > 0 and H* increases with
c*, H* <= 2 - 1/C, and the final comparison 2 - 1/C < 86957/100000 is an exact
rational comparison. Nothing load-bearing is evaluated in floating point.

Run from hunts/wide_search with the repo's .venv python. Exit code 0 iff PASS.
"""

from __future__ import annotations

import sys
from fractions import Fraction
from math import factorial, isqrt

import sympy as sp

TARGET = Fraction(86957, 100000)
INV_NORM_BOUND = Fraction(9, 5)
M = 20

# Even trial polynomial u(s) = sum_j U_COEFFS[j] s^(2j). Taken once from
# xiprime.optimise(n_basis=6) and rounded to denominators <= 10^6. The bound C
# is valid for every u, so how u was chosen carries no proof weight; a poor u
# only makes C looser.
U_COEFFS = [
    Fraction(427163, 446844),
    Fraction(-205089, 684401),
    Fraction(-2976898, 824779),
    Fraction(-13369, 15690),
    Fraction(-104561, 672519),
    Fraction(-32375, 630751),
]


def a_coeff(k: int) -> Fraction:
    return Fraction(2 ** (2 * k + 1) * factorial(k - 1), factorial(2 * k))


def tail_bound(m: int) -> Fraction:
    """rho >= sum_{k>m} a_k >= sup_{|x|<=1} R_m(x).

    a_{k+1}/a_k = 2k/((k+1)(2k+1)) decreases in k, so the tail from k = m+1 is
    dominated by the geometric series with ratio a_{m+2}/a_{m+1}.
    """
    r = Fraction(2 * (m + 1), (m + 2) * (2 * m + 3))
    if not r < 1:
        raise ValueError("geometric ratio must be < 1")
    return a_coeff(m + 1) / (1 - r)


def sqrt_upper(x: Fraction, digits: int = 40) -> Fraction:
    """A rational q with q^2 >= x >= 0."""
    if x < 0:
        raise ValueError("negative argument")
    scale = 10 ** digits
    n, d = x.numerator * scale * scale, x.denominator
    q = Fraction(isqrt(n * d) + 1, d * scale)
    if not q * q >= x:
        raise ArithmeticError("sqrt_upper failed")
    return q


def to_fraction(x) -> Fraction:
    x = sp.nsimplify(x)
    if not x.is_Rational:
        raise TypeError(f"expected an exact rational, got {x}")
    return Fraction(int(x.p), int(x.q))


def exact_quantities(m: int):
    s, t = sp.symbols("s t")
    half = sp.Rational(1, 2)
    u = sum(sp.Rational(c.numerator, c.denominator) * s ** (2 * j) for j, c in enumerate(U_COEFFS))
    u_t = u.subs(s, t)

    # F_1 truncated at k = m:  -4x^2 + |x| P(x^2),  P(y) = 1 + sum_{k=1}^m a_k y^k
    def P(y):
        return 1 + sum(sp.Rational(a_coeff(k).numerator, a_coeff(k).denominator) * y**k for k in range(1, m + 1))

    even_part = sp.integrate(-4 * (s - t) ** 2 * u_t, (t, -half, half))
    left = sp.integrate((s - t) * P((s - t) ** 2) * u_t, (t, -half, s))
    right = sp.integrate((t - s) * P((t - s) ** 2) * u_t, (t, s, half))
    A0u = sp.expand(u + even_part + left + right)

    one_u = sp.integrate(u, (s, -half, half))
    u_A0u = sp.integrate(sp.expand(u * A0u), (s, -half, half))
    resid_sq = sp.integrate(sp.expand((1 - A0u) ** 2), (s, -half, half))
    u_sq = sp.integrate(sp.expand(u * u), (s, -half, half))
    return tuple(to_fraction(q) for q in (one_u, u_A0u, resid_sq, u_sq))


def certify() -> bool:
    one_u, u_A0u, resid_sq, u_sq = exact_quantities(M)
    rho = tail_bound(M)
    resid_norm = sqrt_upper(resid_sq)
    u_norm = sqrt_upper(u_sq)

    C = 2 * one_u - u_A0u + rho * u_sq + INV_NORM_BOUND * (resid_norm + rho * u_norm) ** 2
    L = 2 * one_u - u_A0u - rho * u_sq
    
    if not C > 0 or not L > 0:
        print("Certificate: FAIL (C <= 0 or L <= 0)")
        return False
        
    # Round C up and L down to 18 decimals: printable rationals preserving the bounds.
    scale = 10**18
    C_r = Fraction(-((-C.numerator * scale) // C.denominator), scale)
    L_r = Fraction((L.numerator * scale) // L.denominator, scale)
    
    if not (C_r >= C and L_r <= L):
        raise ArithmeticError("rounding must not violate the bound")
        
    H_upper = 2 - 1 / C_r
    H_lower = 2 - 1 / L_r
    passed = H_upper < TARGET

    print("--- EXACT RATIONAL CERTIFICATE (M = %d, ||A^-1|| <= %s) ---" % (M, INV_NORM_BOUND))
    print(f"<1,u>       = {one_u}")
    print(f"||u||^2     = {u_sq}")
    print(f"<u,A0u>     ~ {float(u_A0u):.15f}   (exact rational, {len(str(u_A0u))} chars)")
    print(f"||1-A0u||^2 ~ {float(resid_sq):.3e}   (exact rational, {len(str(resid_sq))} chars)")
    print(f"rho         = {rho}   (~{float(rho):.3e})")
    print(f"sqrt bounds : ||1-A0u|| <= {float(resid_norm):.6e}, ||u|| <= {float(u_norm):.12f}")
    print("---------------------------------------")
    print(f"Two-sided enclosure: L <= c* <= U")
    print(f"L = floor(L_exact*1e18)/1e18 = {L_r}")
    print(f"U = ceil(C_exact*1e18)/1e18  = {C_r}")
    print(f"H* enclosure: {H_lower} <= H* <= {H_upper}")
    print(f"target                       = {TARGET}")
    print(f"exact comparison H_upper < target: {passed}")
    print("--- decimal approximations (display only, not part of the proof) ---")
    print(f"{float(L_r):.18f} <= c* <= {float(C_r):.18f}")
    print(f"{float(H_lower):.18f} <= H* <= {float(H_upper):.18f}")
    print(f"margin target - bound ~ {float(TARGET - H_upper):.6e}")
    print("---------------------------------------")
    print("Certificate: PASS" if passed else "Certificate: FAIL")
    return passed


if __name__ == "__main__":
    sys.exit(0 if certify() else 1)
