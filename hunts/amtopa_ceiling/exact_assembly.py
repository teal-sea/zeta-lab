#!/usr/bin/env python3
"""Exact-rational replay of the AMTOPA scalar-Gram assembly.

AMTOPA's own ``src/check_final_bound.py`` evaluates the final projection with
``mpmath.mpf`` at 100 decimal digits and a floating ``mp.sqrt``.  Their prose
calls that step "exact arithmetic".  This module redoes it in ``fractions.Fraction``
with an exact rational *under*-estimate of the only irrational, so the printed
bound is a rigorous lower bound on the value their formula produces.

The assembly, transcribed from ``check_final_bound.py``:

    A_m   = eps * (m - q)
    R_m   = h_m(A_m),   h_m(E) = E              if E <= m/(m-1)
                                = E/m + 2*sqrt((m-1)E/m) - 1   otherwise
    eta_m = R_m / A_m
    bound = (m*H - eta_m*B*(m-q)) / (m - R_m)
          = (m*H - B*R_m/eps)  / (m - R_m)      [identical, eta*(m-q) = R/eps]

d(bound)/dR = (m*H - m*B/eps)/(m-R)^2 > 0 whenever H > B/eps, which holds at the
published inputs, so replacing R by a rational lower bound gives a rigorous
lower bound on the assembled value.  That direction is asserted, not assumed.

Usage:  python3 exact_assembly.py
"""
from __future__ import annotations

import math
from fractions import Fraction

# ---------------------------------------------------------------- exact sqrt


def sqrt_lower(x: Fraction, digits: int = 200) -> Fraction:
    """Rational r with r <= sqrt(x), accurate to about ``digits`` decimals."""
    if x < 0:
        raise ValueError("negative radicand")
    scale = 10 ** digits
    # sqrt(p/q) = sqrt(p*q)/q
    radicand = x.numerator * x.denominator * scale * scale
    root = math.isqrt(radicand)
    return Fraction(root, x.denominator * scale)


def sqrt_upper(x: Fraction, digits: int = 200) -> Fraction:
    lo = sqrt_lower(x, digits)
    return lo + Fraction(1, x.denominator * 10 ** digits)


# ------------------------------------------------------------------ assembly


def h_m_lower(m: int, E: Fraction, digits: int = 200) -> Fraction:
    """Rational lower bound on h_m(E)."""
    if E <= Fraction(m, m - 1):
        return E
    return E / m + 2 * sqrt_lower(Fraction(m - 1, m) * E, digits) - 1


def h_m_upper(m: int, E: Fraction, digits: int = 200) -> Fraction:
    if E <= Fraction(m, m - 1):
        return E
    return E / m + 2 * sqrt_upper(Fraction(m - 1, m) * E, digits) - 1


def bound_at(m: int, H: Fraction, eps: Fraction, B: Fraction, q: int,
             digits: int = 200) -> Fraction:
    """Rigorous rational lower bound on the assembled proportion at block m."""
    A = eps * (m - q)
    R = h_m_lower(m, A, digits)
    if not (H > B / eps):
        raise AssertionError("monotonicity in R needs H > B/eps; it fails here")
    den = m - R
    if den <= 0:
        raise AssertionError(f"non-positive denominator at m={m}")
    return (m * H - B * R / eps) / den


def bound_upper_at(m: int, H: Fraction, eps: Fraction, B: Fraction, q: int,
                   digits: int = 200) -> Fraction:
    A = eps * (m - q)
    R = h_m_upper(m, A, digits)
    den = m - R
    if den <= 0:
        raise AssertionError(f"non-positive denominator at m={m}")
    return (m * H - B * R / eps) / den


def scan(H: Fraction, eps: Fraction, B: Fraction, q: int = 6,
         m_hi: int = 20000, digits: int = 60):
    """Exact scan over the block length.  Returns (best_bound, best_m)."""
    best = None
    for m in range(q + 1, m_hi + 1):
        try:
            v = bound_at(m, H, eps, B, q, digits)
        except AssertionError:
            continue
        if best is None or v > best[0]:
            best = (v, m)
    return best


def dec(x: Fraction, n: int = 60) -> str:
    """Decimal expansion of a Fraction, truncated (never rounded up)."""
    neg = x < 0
    x = abs(x)
    whole = x.numerator // x.denominator
    rem = x - whole
    digits = []
    for _ in range(n):
        rem *= 10
        d = rem.numerator // rem.denominator
        digits.append(str(d))
        rem -= d
    return ("-" if neg else "") + str(whole) + "." + "".join(digits)


# --------------------------------------------------------------- their point

AMTOPA_H = Fraction(336094079, 500000000)      # 0.6721881580, their H floor
AMTOPA_EPS = Fraction(79107, 10000000)         # 0.0079107
AMTOPA_B = Fraction(93, 23000)
AMTOPA_Q = 6
AMTOPA_M = 145
AMTOPA_PUBLISHED = (
    "0.6734164909714992949500355331074903174997772794755665475125243371226272"
)


def main() -> int:
    print("== AMTOPA root assembly, exact rational ==")
    print(f"H   = {AMTOPA_H} = {dec(AMTOPA_H, 20)}")
    print(f"eps = {AMTOPA_EPS} = {dec(AMTOPA_EPS, 20)}")
    print(f"B   = {AMTOPA_B} = {dec(AMTOPA_B, 20)}")
    print(f"H - B/eps = {dec(AMTOPA_H - AMTOPA_B / AMTOPA_EPS, 20)}  (must be > 0)")

    lo = bound_at(AMTOPA_M, AMTOPA_H, AMTOPA_EPS, AMTOPA_B, AMTOPA_Q, 200)
    hi = bound_upper_at(AMTOPA_M, AMTOPA_H, AMTOPA_EPS, AMTOPA_B, AMTOPA_Q, 200)
    print(f"\nat their m={AMTOPA_M}:")
    print(f"  lower  {dec(lo, 70)}")
    print(f"  upper  {dec(hi, 70)}")
    print(f"  theirs {AMTOPA_PUBLISHED}")
    n = len(AMTOPA_PUBLISHED) - 2
    agree = dec(lo, n)[: len(AMTOPA_PUBLISHED)] == AMTOPA_PUBLISHED
    print(f"  first {n} decimals agree: {agree}")

    best, best_m = scan(AMTOPA_H, AMTOPA_EPS, AMTOPA_B, AMTOPA_Q, m_hi=20000, digits=60)
    print(f"\nexact scan over m in [7, 20000]: argmax m = {best_m}")
    print(f"  bound  {dec(best, 40)}")
    print(f"  matches their scan_best_m=145: {best_m == AMTOPA_M}")

    safe = Fraction(6734164909, 10000000000)
    print(f"\nsafe floor 0.6734164909 cleared: {best > safe}")
    print(f"  margin {dec(best - safe, 25)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
