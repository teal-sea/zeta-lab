"""Interval instruments for the prime_zeta_rightmost hunt (WP2, WP4 constants).

Everything here computes *decided* quantities: an interval or ball enclosure
whose exact endpoints settle a sign, stated with backend and precision. The
strongest vocabulary used is measured / observed / decided / enclosure, per
the hunt's vocabulary contract.

Two backends, deliberately independent code paths:

  flint    : python-flint arb balls (Arb). arb.zeta is used directly; the
             prime zeta P(sigma) is evaluated through the Moebius series
             (tail bound derived below). Working precision in bits is set
             per call via flint.ctx.prec.
  mpmath.iv: mpmath's interval context. NOTE: in mpmath 1.3.0 the attribute
             iv.zeta exists but raises AttributeError('bernoulli') when
             called, so this leg carries its own zeta enclosure: a finite
             Dirichlet sum plus an Euler-Maclaurin tail with a decided
             remainder bound (derivation below). This is the honest weaker
             leg: wider intervals, same exact-endpoint sign logic.

Bracket bookkeeping is done in exact Fractions; backend arithmetic only ever
answers sign questions about function values, so a rounding error can widen
an interval but can never produce a wrong decided sign.

Tail-bound derivations (each inequality used is proved here, then evaluated
in outward-rounded interval arithmetic):

1. Moebius series for the prime zeta function, Re s > 1:

       P(s) = sum_p p^{-s} = sum_{k>=1} mu(k)/k * log zeta(k s).

   Standard, by Moebius inversion of log zeta(s) = sum_k P(k s)/k
   (Titchmarsh, Theory of the Riemann Zeta-function, 1.6; Froberg 1968).
   Truncation tail bound: for y >= 2,

       0 < zeta(y) - 1 = sum_{n>=2} n^{-y}
         <= 2^{-y} + int_2^inf t^{-y} dt
          = 2^{-y} + 2^{1-y}/(y-1)
          = 2^{-y} (1 + 2/(y-1)) <= 3 * 2^{-y}      (since y >= 2),

   and 0 < log zeta(y) = log(1 + (zeta(y)-1)) <= zeta(y) - 1 <= 3 * 2^{-y}.
   Hence for s >= 1 and K >= 1 (so that k s >= 2 for every k > K):

       | sum_{k>K} mu(k)/k * log zeta(k s) |
         <= (1/(K+1)) * sum_{k>K} 3 * 2^{-k s}
          = 3 * 2^{-(K+1) s} / ((K+1) * (1 - 2^{-s}))  =: T(s, K).

   The code adds the interval [-T, T] to the truncated sum, with T itself
   evaluated in outward interval arithmetic.

2. Euler-Maclaurin zeta enclosure for the iv leg, real y > 1:
   with a = N + 1 and f(x) = x^{-y},

       zeta(y) = sum_{n=1}^{N} n^{-y} + sum_{n=a}^{inf} n^{-y},
       sum_{n=a}^{inf} f(n)
         = int_a^inf f + f(a)/2 - B_2/2! * f'(a) + R_2
         = a^{1-y}/(y-1) + a^{-y}/2 + y*a^{-y-1}/12 + R_2,

   with the classical remainder bound (f^{(4)} has constant sign on [a,inf))

       |R_2| <= |B_4|/4! * int_a^inf |f^{(4)}(x)| dx
              = (1/720) * |f'''(a)| = y (y+1) (y+2) a^{-y-3} / 720 =: E.

   The code adds the interval [-E, E], with E evaluated in iv arithmetic.

3. Monotonicity guards. With h(s) = P(s) - 2^{1-s} = sum_{p>=3} p^{-s} - 2^{-s},

       h'(s) = log 2 * 2^{-s} - sum_{p>=3} log p * p^{-s}.

   Dropping the (positive) tail of the prime sum only *raises* the value, so

       h'(s) <= log 2 * 2^{-s} - sum_{3<=p<=P0} log p * p^{-s},

   and an interval evaluation of the right-hand side over s in [a,b] whose
   upper endpoint is negative decides h' < 0 on [a,b], hence h strictly
   decreasing there, hence at most one root there. Same shape for
   u(s) = P(s) - 2^{-s} - 2*3^{-s} (the {p>=3} subset balance):

       u'(s) <= log 2 * 2^{-s} + 2 log 3 * 3^{-s} - sum_{p<=P0} log p * p^{-s}.

   For x* the guard needs no numerics: zeta'(x) = -sum_{n>=2} log n * n^{-x}
   is negative termwise for x > 1, so zeta is strictly decreasing on (1,2)
   exactly, and zeta(x) = 2 has at most one root there.
"""

from __future__ import annotations

import time
from fractions import Fraction
from math import ceil, floor
from typing import Callable, List, Tuple

import flint
import mpmath

arb = flint.arb
fctx = flint.ctx
iv = mpmath.iv


# ----------------------------------------------------------------------
# sieves (exact integer combinatorics, no rounding anywhere)
# ----------------------------------------------------------------------

def mobius_sieve(n: int) -> List[int]:
    """mu(0..n) by a plain sieve; mu[0] unused."""
    mu = [1] * (n + 1)
    is_comp = [False] * (n + 1)
    for p in range(2, n + 1):
        if is_comp[p]:
            continue
        for m in range(p, n + 1, p):
            if m > p:
                is_comp[m] = True
            mu[m] = -mu[m]
        pp = p * p
        for m in range(pp, n + 1, pp):
            mu[m] = 0
    return mu


def primes_upto(n: int) -> List[int]:
    sieve = [True] * (n + 1)
    sieve[0:2] = [False, False]
    for p in range(2, int(n ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p :: p] = [False] * len(sieve[p * p :: p])
    return [p for p in range(2, n + 1) if sieve[p]]


# ----------------------------------------------------------------------
# exact endpoints and outward decimal rounding
# ----------------------------------------------------------------------

def arb_endpoints(x: arb) -> Tuple[Fraction, Fraction]:
    """Exact rational endpoints [mid - rad, mid + rad] of an arb ball."""

    def to_fr(a) -> Fraction:
        if a.is_zero():
            return Fraction(0)
        man, exp = a.man_exp()
        return Fraction(int(man)) * (Fraction(2) ** int(exp))

    m = to_fr(x.mid())
    r = to_fr(x.rad())
    return m - r, m + r


def iv_endpoints(x) -> Tuple[Fraction, Fraction]:
    """Exact rational endpoints of an iv.mpf interval, read from the raw
    representation ``x._mpi_`` and never through a context conversion.

    Instrument defect, found and fixed 2026-08-16: the first version went
    through ``mpmath.mpf(x.a)``, and ``x.a`` is itself an interval object, so
    that call converts through the *global* mp context (default dps 15) and
    rounds both endpoints to the nearest 53-bit float. Rounding to nearest at
    relative precision can never move a value across zero, so every recorded
    sign decision made through the old path was sound; but value enclosures
    were collapsed to zero width and misplaced beyond the 16th digit. Caught
    by a cross-backend check: the two legs' enclosures of log2(69/(5 log 23))
    came out disjoint, which marks the instrument, not the mathematics
    (MISSION.md kill condition 3). ``_mpi_`` holds the true endpoint pair as
    raw mpf tuples; converting those to Fractions is exact.
    """

    def to_fr(t) -> Fraction:
        sign, man, exp, _ = t
        f = Fraction(int(man)) * (Fraction(2) ** int(exp))
        return -f if sign else f

    a_raw, b_raw = x._mpi_
    return to_fr(a_raw), to_fr(b_raw)


def outward_decimal(lo: Fraction, hi: Fraction, digits: int) -> Tuple[str, str]:
    """Decimal strings d_lo <= lo, d_hi >= hi with `digits` places (values > 0)."""
    assert lo > 0 and hi >= lo
    scale = 10 ** digits
    lo_i = floor(lo * scale)
    hi_i = ceil(hi * scale)

    def fmt(n: int) -> str:
        return f"{n // scale}.{n % scale:0{digits}d}"

    return fmt(lo_i), fmt(hi_i)


# ----------------------------------------------------------------------
# flint (arb) leg
# ----------------------------------------------------------------------

def arb_from_fraction(q: Fraction) -> arb:
    """A ball containing the exact rational q (tiny radius at current prec)."""
    return arb(q.numerator) / arb(q.denominator)


def arb_interval(lo: Fraction, hi: Fraction) -> arb:
    """A ball containing the whole interval [lo, hi]."""
    return arb_from_fraction(lo).union(arb_from_fraction(hi))


def prime_zeta_arb(s: arb, K: int, mu: List[int]) -> arb:
    """Enclosure of P(s) by the Moebius series with the T(s,K) tail (docstring 1).

    Valid for s a ball inside (1, inf) with lower endpoint >= 1; K >= 1.
    """
    total = arb(0)
    for k in range(1, K + 1):
        if mu[k] == 0:
            continue
        total += (arb(mu[k]) / k) * arb.zeta(arb(k) * s).log()
    two = arb(2)
    T = 3 * two ** (-(arb(K + 1) * s)) / ((K + 1) * (1 - two ** (-s)))
    return total + T.union(-T)


def h_arb(s: arb, K: int, mu: List[int]) -> arb:
    """h(s) = P(s) - 2^(1-s)."""
    return prime_zeta_arb(s, K, mu) - arb(2) ** (1 - s)


def u_arb(s: arb, K: int, mu: List[int]) -> arb:
    """u(s) = P(s) - 2^(-s) - 2*3^(-s), the {p>=3} subset balance."""
    return prime_zeta_arb(s, K, mu) - arb(2) ** (-s) - 2 * arb(3) ** (-s)


# ----------------------------------------------------------------------
# mpmath.iv leg
# ----------------------------------------------------------------------

def iv_from_fraction(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def zeta_iv(y, N: int):
    """Enclosure of zeta(y) for a point interval y > 1: finite Dirichlet sum
    over n <= N plus the Euler-Maclaurin tail with decided remainder
    (docstring 2). iv.zeta is unusable in mpmath 1.3.0 (raises on call),
    so this is the whole iv-side zeta.
    """
    s = iv.mpf(0)
    for n in range(1, N + 1):
        s += iv.mpf(n) ** (-y)
    a = iv.mpf(N + 1)
    one = iv.mpf(1)
    tail = a ** (one - y) / (y - one) + a ** (-y) / 2 + y * a ** (-y - one) / 12
    E = y * (y + one) * (y + 2) * a ** (-y - 3) / 720
    return s + tail + iv.mpf([-1, 1]) * E


def _iv_N_for_k(k: int) -> int:
    """Dirichlet-sum length for the k-th Moebius term (argument y ~ 1.7*k)."""
    if k == 1:
        return 2000
    if k == 2:
        return 400
    if k <= 5:
        return 100
    return 30


def prime_zeta_iv(s, K: int, mu: List[int]):
    """Enclosure of P(s) on the iv leg: Moebius series with zeta_iv per term
    and the same T(s,K) tail bound as the flint leg (docstring 1)."""
    total = iv.mpf(0)
    for k in range(1, K + 1):
        if mu[k] == 0:
            continue
        z = zeta_iv(iv.mpf(k) * s, _iv_N_for_k(k))
        total += iv.mpf(mu[k]) / k * iv.log(z)
    two = iv.mpf(2)
    T = 3 * two ** (-(iv.mpf(K + 1) * s)) / ((K + 1) * (1 - two ** (-s)))
    return total + iv.mpf([-1, 1]) * T


def h_iv(s, K: int, mu: List[int]):
    return prime_zeta_iv(s, K, mu) - iv.mpf(2) ** (1 - s)


def u_iv(s, K: int, mu: List[int]):
    return prime_zeta_iv(s, K, mu) - iv.mpf(2) ** (-s) - 2 * iv.mpf(3) ** (-s)


# ----------------------------------------------------------------------
# sign-decided bisection (backend-independent bookkeeping)
# ----------------------------------------------------------------------

def decided_sign(lo: Fraction, hi: Fraction) -> int:
    """+1 / -1 when the exact endpoints settle the sign, 0 when they straddle 0."""
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    return 0


def bisect_decreasing(
    f_endpoints: Callable[[Fraction], Tuple[Fraction, Fraction]],
    lo: Fraction,
    hi: Fraction,
    target_width: Fraction,
    max_iter: int = 300,
) -> dict:
    """Bisection for the unique root of a strictly decreasing f on [lo, hi].

    f_endpoints(x) returns exact rational endpoints of an enclosure of f(x).
    Endpoint signs are decided first (f(lo) > 0, f(hi) < 0 required). Stops
    when hi - lo < target_width, or when the sign at a midpoint can no longer
    be decided (recorded honestly in 'sign_stalled'). Every step preserves
    the invariant: decided f(lo) > 0 and decided f(hi) < 0, so the root of f
    lies in [lo, hi] whenever f is continuous and strictly decreasing there.
    """
    s_lo = decided_sign(*f_endpoints(lo))
    s_hi = decided_sign(*f_endpoints(hi))
    if s_lo != 1 or s_hi != -1:
        raise ValueError(f"bracket endpoint signs not decided: f({lo}) sign {s_lo}, f({hi}) sign {s_hi}")
    iters = 0
    stalled = False
    while hi - lo >= target_width and iters < max_iter:
        mid = (lo + hi) / 2
        s = decided_sign(*f_endpoints(mid))
        if s == 0:
            stalled = True
            break
        if s > 0:
            lo = mid
        else:
            hi = mid
        iters += 1
    return {"lo": lo, "hi": hi, "iterations": iters, "sign_stalled": stalled}


# ----------------------------------------------------------------------
# monotonicity guards (docstring 3)
# ----------------------------------------------------------------------

def h_prime_upper_arb(a: Fraction, b: Fraction, prime_cutoff: int) -> Tuple[Fraction, Fraction]:
    """Endpoints of an enclosure of an *upper bound* for h'(s) on [a,b]:
    log2*2^(-s) - sum_{3<=p<=P0} log p * p^(-s), evaluated over the interval."""
    I = arb_interval(a, b)
    val = arb(2).log() * arb(2) ** (-I)
    for p in primes_upto(prime_cutoff):
        if p == 2:
            continue
        val -= arb(p).log() * arb(p) ** (-I)
    return arb_endpoints(val)


def u_prime_upper_arb(a: Fraction, b: Fraction, prime_cutoff: int) -> Tuple[Fraction, Fraction]:
    """Endpoints of an enclosure of an upper bound for u'(s) on [a,b]:
    log2*2^(-s) + 2 log3*3^(-s) - sum_{p<=P0} log p * p^(-s)."""
    I = arb_interval(a, b)
    val = arb(2).log() * arb(2) ** (-I) + 2 * arb(3).log() * arb(3) ** (-I)
    for p in primes_upto(prime_cutoff):
        val -= arb(p).log() * arb(p) ** (-I)
    return arb_endpoints(val)


def h_prime_upper_iv(a: Fraction, b: Fraction, prime_cutoff: int) -> Tuple[Fraction, Fraction]:
    lo = iv_from_fraction(a)
    hi = iv_from_fraction(b)
    I = iv.mpf([lo.a, hi.b])
    val = iv.log(iv.mpf(2)) * iv.mpf(2) ** (-I)
    for p in primes_upto(prime_cutoff):
        if p == 2:
            continue
        val -= iv.log(iv.mpf(p)) * iv.mpf(p) ** (-I)
    return iv_endpoints(val)


def u_prime_upper_iv(a: Fraction, b: Fraction, prime_cutoff: int) -> Tuple[Fraction, Fraction]:
    lo = iv_from_fraction(a)
    hi = iv_from_fraction(b)
    I = iv.mpf([lo.a, hi.b])
    val = iv.log(iv.mpf(2)) * iv.mpf(2) ** (-I) + 2 * iv.log(iv.mpf(3)) * iv.mpf(3) ** (-I)
    for p in primes_upto(prime_cutoff):
        val -= iv.log(iv.mpf(p)) * iv.mpf(p) ** (-I)
    return iv_endpoints(val)


# ----------------------------------------------------------------------
# small utility
# ----------------------------------------------------------------------

class Timer:
    def __enter__(self):
        self.t0 = time.perf_counter()
        return self

    def __exit__(self, *exc):
        self.seconds = time.perf_counter() - self.t0
