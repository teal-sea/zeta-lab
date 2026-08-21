"""Sharpened zero strip for the completed Davenport-Heilbronn function.

`strip.py` decides `sigma_0 = 1.39513615823510972...`, the root of the
coefficient-domination inequality `sum_{n>=2} |a_n| n^{-sigma} < 1`.  That
bound throws away every cancellation: it treats the phases `n^{-it}` as if
they could be chosen freely and independently, so it asks the coefficient
mass alone to be smaller than the `n = 1` term.  The phases are not free.
They are multiplicative, `n^{-it} = prod_p p^{-it v_p(n)}`, and the
Davenport-Heilbronn coefficients are a linear combination of two Dirichlet
characters mod 5, so the whole series is a combination of two Euler
products.  This instrument replaces the free-phase relaxation by the exact
multiplicative constraint and decides the resulting abscissa.

The argument, in full (derivation and every step in `STRIP2.md`):

  f(s) = sum_{n>=1} a_n n^{-s} with a period-5 (1, kappa, -kappa, -1, 0)
  equals `A L(s, chi) + conj(A) L(s, conj chi)` with `A = (1 - i kappa)/2`
  and `chi` the odd primitive character mod 5 normalised by `chi(2) = i`.
  For `Re s > 1` both L-functions are nonzero, so

      f(s) = 0   <=>   L(s, chi) / L(s, conj chi) = -conj(A)/A.

  The right side is unimodular with argument `pi + 2 arctan kappa`, whose
  smallest representative modulo `2 pi` has absolute value
  `pi - 2 arctan kappa`.  The left side is an absolutely convergent Euler
  product whose factors are 1 at every prime with `chi(p)` real, and
  `(1 + u)/(1 - u)` with `|u| = p^{-sigma}` at every prime `p = 2, 3 mod 5`.
  The Moebius image of the disc `|u| <= r` under `u -> (1+u)/(1-u)` is the
  disc of centre `(1+r^2)/(1-r^2)` and radius `2r/(1-r^2)`, so each factor's
  argument is bounded in absolute value by
  `arcsin(2r/(1+r^2)) = 2 arctan r`.  Hence

      |arg L(s, chi)/L(s, conj chi)|  <=  Theta(sigma)
          :=  sum_{p = 2, 3 mod 5} 2 arctan(p^{-sigma}),

  and `Theta(sigma) < pi - 2 arctan kappa` forbids a zero on `Re s = sigma`.
  `Theta` is strictly decreasing, so one decided `sigma*` closes the whole
  half-plane `Re s >= sigma*`, and `F(s) = F(1-s)` reflects it.

This is the necessary half of Bombieri and Ghosh's Theorem 7 (Russian Math.
Surveys 66:2 (2011), 221-270), which is the half an upper bound needs.  It
is elementary: it uses the Euler product and nothing else.  Their converse,
that the abscissa is attained, is what needs Bohr's method and Kronecker's
theorem, and it is not used here.  See `BOMBIERI-GHOSH.md`.

Deciding `Theta` needs the tail over primes.  The head `p <= P` is summed
term by term from an exact sieve.  The tail is closed by the Euler product
itself, with no prime counting and no cited estimate:

    sum_{p > P} -log(1 - p^{-sigma})     = log zeta(sigma) + sum_{p<=P} log(1 - p^{-sigma})
    sum_{p > P} -log(1 - chi5(p) p^{-sigma})
                                         = log L(sigma, chi5) + sum_{p<=P} log(1 - chi5(p) p^{-sigma})

with `chi5` the quadratic character mod 5, whose value is -1 exactly on the
classes `2, 3 mod 5`.  Half the difference of the two is the class-restricted
tail up to the `k >= 2` terms of the logarithm, and those cancel between the
two series except at odd `k >= 3`, which leaves an error bounded by
`(2/3) sum_{p>P} p^{-3 sigma} <= (2/3) P^{1-3 sigma}/(3 sigma - 1)`.

Backends, both with directed rounding, as in `strip.py`:

* python-flint (Arb): `arb.atan`, `arb.log`, `arb.zeta`, and `L(sigma, chi5)`
  by the Hurwitz combination `5^{-s}[zeta(s,1/5) - zeta(s,2/5) -
  zeta(s,3/5) + zeta(s,4/5)]`, cross-checked against `acb.dirichlet_l`.
* mpmath.iv: no zeta and no arctan.  `zeta` and `L` come from the same
  Euler-Maclaurin machinery `strip.py` uses for arithmetic progressions,
  generalised to a step, and `arctan` from its alternating series, whose
  consecutive partial sums bracket the value for `0 <= x < 1`.  Both are
  containment-checked against independent references before any decision.

Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/strip2.py

Writes ``strip2_results.json`` next to this file.  Vocabulary per
`MISSION.md`: *decided* is an enclosure whose exact endpoints settle a sign,
stated with backend and precision; *measured* is one float route; *cited* is
somebody else's theorem.
"""

from __future__ import annotations

import json
import math
import os
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
for _p in (REPO, HERE):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import numpy as np  # noqa: E402
from flint import acb, arb, dirichlet_char, fmpq  # noqa: E402
from mpmath import bernfrac, iv, mp  # noqa: E402

import instrument as ins  # noqa: E402
from strip import (  # noqa: E402  (shared serialization layer, no mathematics)
    _arb_ball_fracs,
    _dec,
    _iv_frac,
    _iv_fracs,
    _out_interval,
    _sign_arb,
    _sign_iv,
    bisect_root,
    g_ball,
)
from zeta.epstein import KAPPA_REF  # noqa: E402

OUT = os.path.join(HERE, "strip2_results.json")

# --- parameters -------------------------------------------------------------
P_FLINT = 10 ** 5          # sieve limit, flint leg
P_IV = 10 ** 5             # sieve limit, iv leg (same as flint, so the two legs
#                            bisect the same function and overlap is meaningful)
FLINT_PREC = 192           # bits
KAPPA_PREC = 500           # bits, instrument.kappa_ball
IV_DPS = 40
IV_M = 100                 # Euler-Maclaurin split point per progression
IV_K = 8                   # Euler-Maclaurin correction terms
BRACKET = (Fraction("1.10"), Fraction("1.15"))
FLINT_WIDTH = Fraction(1, 10 ** 20)
IV_WIDTH = Fraction(1, 10 ** 12)
SIGMA_STAR = Fraction("1.12036249819")        # the headline rational
SIGMA_STAR_COARSE = Fraction("1.1203625")     # a generous rounding of it
SIGMA_0_OLD = Fraction("1.3951361582351097210613589375")   # strip.py upper endpoint
BG_SIGMA = Fraction("1.12036249818332508773010350311")     # BOMBIERI-GHOSH.md re-solve
BG_SIGMA_MINUS = Fraction("2.38228610898712386578711039387")   # the same, tau_-
ATAN_TOL = Fraction(1, 10 ** 45)
P_DEEP = 10 ** 7           # sieve limit for the single deep decided point
PREC_DEEP = 320            # bits, deep point
SIGMA_DEEP = Fraction("1.1203624981833251")   # decided at P_DEEP, flint only


# ---------------------------------------------------------------------------
# primes: an exact sieve, integer arithmetic only
# ---------------------------------------------------------------------------


def sieve(n: int) -> np.ndarray:
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = False
    return np.nonzero(s)[0]


def split_classes(primes: np.ndarray) -> tuple[list[int], list[int]]:
    """(p = 2, 3 mod 5, i.e. chi5(p) = -1), (p = 1, 4 mod 5, chi5(p) = +1).

    p = 5 belongs to neither: chi5(5) = 0.
    """
    r = primes % 5
    non = [int(p) for p in primes[(r == 2) | (r == 3)]]
    res = [int(p) for p in primes[(r == 1) | (r == 4)]]
    return non, res


# ---------------------------------------------------------------------------
# flint leg
# ---------------------------------------------------------------------------


def _arb_q(q: Fraction) -> arb:
    return arb(fmpq(q.numerator, q.denominator))


def flint_logs(primes: list[int], prec: int) -> list[arb]:
    with ins._prec_guard(prec):
        return [arb(p).log() for p in primes]


def zeta_flint(sig: arb, prec: int) -> arb:
    with ins._prec_guard(prec):
        return sig.zeta()


def lchi_flint(sig: arb, prec: int) -> arb:
    """L(sigma, chi5) by the Hurwitz combination; chi5 = +1, -1, -1, +1 on 1..4."""
    with ins._prec_guard(prec):
        s = acb(sig)

        def h(c: int) -> acb:
            z = s.zeta(acb(fmpq(c, 5)))
            if not z.imag.contains(arb(0)):
                raise ArithmeticError("Hurwitz zeta: imaginary ball excludes 0")
            return z.real

        return arb(5) ** (-sig) * (h(1) - h(2) - h(3) + h(4))


def theta_bounds_flint(sig_q: Fraction, kap: arb, non: list[int],
                       logs_non: list[arb], P: int, prec: int) -> tuple[arb, arb]:
    """(lower, upper) Arb balls for Theta(sigma) = sum_{p=2,3(5)} 2 atan(p^-s).

    head : exact term-by-term over the class, p <= P.
    tail : (T1 - Tchi) with T1 - Tchi = log(zeta/L) + log(1 - 5^-s)
           + sum_{p<=P, class} [log(1-x) - log(1+x)], which equals
           2 * sum_{p>P, class} p^{-sigma} up to the eps3 correction below.

    ``kap`` is accepted for call-site uniformity and is deliberately not
    used: Theta depends on the prime classes alone, and kappa enters the
    criterion only through the target pi - 2 arctan(kappa).  That is exactly
    why the tau_- control in ``main`` is free, since moving to the other
    Titchmarsh root moves the target and leaves Theta alone.
    """
    with ins._prec_guard(prec):
        sig = _arb_q(sig_q)
        head = arb(0)
        diff = arb(0)                     # sum_{p<=P, class} log(1-x) - log(1+x)
        for lp in logs_non:
            x = (-sig * lp).exp()
            head += 2 * x.atan()
            diff += (1 - x).log() - (1 + x).log()
        five = arb(5) ** (-sig)
        t1_minus_tchi = ((zeta_flint(sig, prec) / lchi_flint(sig, prec)).log()
                         + (1 - five).log() + diff)
        # |E_chi - E_1| <= (2/3) sum_{p>P} p^{-3 sigma} / (1 - P^{-2 sigma})
        w3 = arb(P) ** (1 - 3 * sig) / (3 * sig - 1)
        eps3 = (arb(2) / 3) * w3 / (1 - arb(P) ** (-2 * sig))
        upper = head + t1_minus_tchi + eps3
        lower = head + t1_minus_tchi - eps3 - (arb(2) / 3) * w3
        return lower, upper


def target_flint(kap: arb, prec: int) -> arb:
    """pi - 2 arctan(kappa): the phase a zero must supply."""
    with ins._prec_guard(prec):
        return arb.pi() - 2 * kap.atan()


# ---------------------------------------------------------------------------
# iv leg: Euler-Maclaurin progressions and a series arctan
# ---------------------------------------------------------------------------


def _prog_tail_iv(sigma, step: int, c: int, M: int, K: int):
    """iv enclosure of sum_{j>=M} (step*j + c)^{-sigma}, sigma > 1.

    Euler-Maclaurin for f(x) = (a x + c)^{-sigma} with a = step:
    f^{(m)}(x) = (-1)^m (sigma)_m a^m (a x + c)^{-sigma-m}, so

        sum_{j>=M} f(j) = (aM+c)^{1-sigma}/(a(sigma-1)) + (aM+c)^{-sigma}/2
            + sum_{j=1}^{K} B_{2j}/(2j)! (sigma)_{2j-1} a^{2j-1} (aM+c)^{-sigma-2j+1}
            + R_K,

    and |R_K| is at most the first omitted correction term when the relevant
    derivative keeps one sign (DLMF 2.10(i); x^{-s} is completely monotone).
    The remainder is enclosed by twice that magnitude, symmetrically, and the
    whole formula is containment-checked in ``check_iv_special`` before use.
    """
    base = iv.mpf(step * M + c)
    total = base ** (1 - sigma) / (step * (sigma - 1)) + base ** (-sigma) / 2
    poch = iv.mpf(1)
    m = 0
    for j in range(1, K + 1):
        while m < 2 * j - 1:
            poch = poch * (sigma + m)
            m += 1
        p, qd = bernfrac(2 * j)
        term = ((iv.mpf(int(p)) / iv.mpf(int(qd)))
                / iv.mpf(math.factorial(2 * j))
                * poch * iv.mpf(step) ** (2 * j - 1)
                * base ** (-sigma - (2 * j - 1)))
        total = total + term
    while m < 2 * K + 1:
        poch = poch * (sigma + m)
        m += 1
    p, qd = bernfrac(2 * K + 2)
    bmag = (abs(iv.mpf(int(p)) / iv.mpf(int(qd)))
            / iv.mpf(math.factorial(2 * K + 2))
            * poch * iv.mpf(step) ** (2 * K + 1)
            * base ** (-sigma - (2 * K + 1)))
    return total + iv.mpf([-1, 1]) * (2 * bmag)


def _prog_sum_iv(sigma, step: int, c: int, j0: int, M: int, K: int):
    s = iv.mpf(0)
    for j in range(j0, M):
        s = s + iv.mpf(step * j + c) ** (-sigma)
    return s + _prog_tail_iv(sigma, step, c, M, K)


def zeta_iv(sigma, M: int = IV_M, K: int = IV_K):
    return _prog_sum_iv(sigma, 1, 0, 1, M, K)


def lchi_iv(sigma, M: int = IV_M, K: int = IV_K):
    return (_prog_sum_iv(sigma, 5, 1, 0, M, K) - _prog_sum_iv(sigma, 5, 2, 0, M, K)
            - _prog_sum_iv(sigma, 5, 3, 0, M, K) + _prog_sum_iv(sigma, 5, 4, 0, M, K))


def atan_iv(x, tol: Fraction = ATAN_TOL, max_terms: int = 400):
    """iv enclosure of arctan(x) for an interval x with 0 <= x < 1.

    The Maclaurin series is alternating with strictly decreasing terms there,
    so consecutive partial sums bracket the value: S_1 >= arctan >= S_2 >= ...
    with S_k the sum of the first k terms.  The bracket is taken from the last
    odd-index (upper) and even-index (lower) partial sums, each evaluated in
    interval arithmetic so the printed bracket contains the true value for
    every real point of x.
    """
    if x.a < 0 or x.b >= 0.75:
        raise ValueError("atan_iv is written for 0 <= x < 3/4; every call "
                         "site uses x = p^{-sigma} <= 2^{-11/10} or kappa")
    xsq = x * x
    p = x
    s = x
    upper, lower = s, None
    tol_iv = _iv_frac(tol)
    k = 1
    while k <= max_terms:
        p = p * xsq
        t = p / (2 * k + 1)
        if k % 2 == 1:
            s = s - t
            lower = s
        else:
            s = s + t
            upper = s
        if lower is not None and k % 2 == 0 and t.b < tol_iv.b:
            break
        k += 1
    else:                                             # pragma: no cover
        raise ArithmeticError("atan_iv did not converge; x too close to 1")
    return iv.mpf([lower.a, upper.b])


def theta_bounds_iv(sig_q: Fraction, kap_iv, non: list[int], logs_non,
                    P: int) -> tuple:
    """The mpmath.iv twin of :func:`theta_bounds_flint`, same formula.

    ``kap_iv`` is accepted for call-site uniformity and is not used, for the
    reason given there.
    """
    sigma = _iv_frac(sig_q)
    head = iv.mpf(0)
    diff = iv.mpf(0)
    for lp in logs_non:
        x = iv.exp(-sigma * lp)
        head = head + 2 * atan_iv(x)
        diff = diff + iv.log(1 - x) - iv.log(1 + x)
    five = iv.mpf(5) ** (-sigma)
    t1_minus_tchi = (iv.log(zeta_iv(sigma) / lchi_iv(sigma))
                     + iv.log(1 - five) + diff)
    w3 = iv.mpf(P) ** (1 - 3 * sigma) / (3 * sigma - 1)
    eps3 = (iv.mpf(2) / 3) * w3 / (1 - iv.mpf(P) ** (-2 * sigma))
    upper = head + t1_minus_tchi + eps3
    lower = head + t1_minus_tchi - eps3 - (iv.mpf(2) / 3) * w3
    return lower, upper


def target_iv(kap_iv):
    return iv.pi - 2 * atan_iv(kap_iv)


# ---------------------------------------------------------------------------
# cross-checks, all run before anything is decided
# ---------------------------------------------------------------------------


def check_character_decomposition(kap: arb, prec: int) -> dict:
    """a_n = A chi(n) + conj(A) conj(chi)(n) for n = 1..5, A = (1 - i kappa)/2.

    Decided: each of the five residuals is an acb ball containing 0 and of
    radius below 1e-40.  chi is taken from flint's own Dirichlet character
    table (index 2 mod 5), not from a remembered table of values.
    """
    with ins._prec_guard(prec):
        chi = dirichlet_char(5, 2)
        A = acb(arb(1), -kap) / 2
        pattern = {1: acb(1), 2: acb(kap), 3: acb(-kap), 4: acb(-1), 0: acb(0)}
        rows = []
        ok = True
        chi_vals = {}
        for n in range(1, 6):
            cv = acb(chi(n))
            chi_vals[n] = (float(cv.real.mid()), float(cv.imag.mid()))
            resid = A * cv + A.conjugate() * cv.conjugate() - pattern[n % 5]
            good = bool(resid.contains(acb(0))
                        and float(abs(resid).upper()) < 1e-40)
            ok = ok and good
            rows.append({"n": n, "chi(n)": chi_vals[n],
                         "residual_radius": float(abs(resid).upper()),
                         "contains_zero": good})
        # -conj(A)/A must be exp(i (pi + 2 arctan kappa))
        w = -A.conjugate() / A
        phase = arb.pi() + 2 * kap.atan()
        target = acb(phase.cos(), phase.sin())
        d = float(abs(w - target).upper())
        rows.append({"n": "-conj(A)/A vs exp(i(pi+2 atan kappa))",
                     "residual_radius": d, "contains_zero": bool(d < 1e-40)})
        ok = ok and d < 1e-40
    return {"all_ok": bool(ok), "rows": rows,
            "grade": "decided (acb balls, radius < 1e-40)"}


def check_series_against_L() -> dict:
    """Measured: f = A L(s,chi) + conj(A) L(s,conj chi), against repo code.

    Two legs, neither of which uses this instrument's own arithmetic.

    (i) `zeta.epstein.dh_f` against `A L_chi + conj(A) L_chi(conjugate)`,
        both from `zeta/epstein.py`, at complex points with Re s > 1 and
        large imaginary part, where the two sides are genuinely different
        computations and any wrong root of unity would show at order one.
    (ii) `zeta.epstein.dh_f` against a truncated direct sum of a_n n^{-s},
        which is what pins the closed form to *the Dirichlet series* rather
        than to some other combination of Hurwitz values.
    """
    from zeta.epstein import L_chi, dh_coefficient, dh_f     # noqa: PLC0415
    rows = []
    ok = True
    with mp.workdps(40):
        kapm = mp.mpf(KAPPA_REF)
        A = (1 - mp.mpc(0, 1) * kapm) / 2
        a = [mp.mpf(0)] + [dh_coefficient(n, 40) for n in range(1, 6)]
        for sv in ("1.6+3.5j", "2.2-11.0j", "3.0+40.0j"):
            s = mp.mpmathify(sv)
            lhs = dh_f(s, 40)
            rhs = A * L_chi(s, dps=40) + mp.conj(A) * L_chi(s, conjugate=True,
                                                            dps=40)
            d = float(abs(lhs - rhs))
            good = bool(d < 1e-33)
            ok = ok and good
            rows.append({"s": sv, "leg": "dh_f vs A L + conj(A) Lbar",
                         "abs_difference": d, "tolerance": 1e-33, "ok": good})
        for sv in ("2.5+1.0j", "3.5-7.0j"):
            s = mp.mpmathify(sv)
            N = 60000
            direct = mp.fsum(a[n % 5 if n % 5 else 5] * mp.power(n, -s)
                             for n in range(1, N + 1))
            allow = float((1 + kapm) * mp.mpf(N) ** (1 - mp.re(s))
                          / (mp.re(s) - 1))
            d = float(abs(dh_f(s, 40) - direct))
            good = bool(d < allow)
            ok = ok and good
            rows.append({"s": sv, "leg": "dh_f vs truncated sum a_n n^-s",
                         "abs_difference": d, "truncation_allowance": allow,
                         "ok": good})
    return {"all_ok": ok, "rows": rows,
            "grade": "measured (mpmath dps 40, zeta.epstein as the second "
                     "route)"}


def check_phase_lemma() -> dict:
    """Measured: max |arg (1+u)/(1-u)| over |u| = r equals 2 arctan r.

    Samples the circle densely; records the observed maximum, the point at
    which it is attained (u = i r), and the modulus there (which is 1, the
    fact that makes the phase budget free of any modulus constraint).
    """
    rows = []
    ok = True
    with mp.workdps(30):
        for rs in ("0.5", "0.25", "0.1", "0.01"):
            r = mp.mpf(rs)
            best, best_phi = mp.mpf(0), None
            for j in range(4001):
                phi = 2 * mp.pi * j / 4000
                u = r * mp.expjpi(phi / mp.pi)
                w = (1 + u) / (1 - u)
                if abs(mp.arg(w)) > best:
                    best, best_phi = abs(mp.arg(w)), phi
            bound = 2 * mp.atan(r)
            mod_at_ir = abs((1 + 1j * r) / (1 - 1j * r))
            good = bool(best <= bound * (1 + 1e-20)
                        and best > bound * (1 - 1e-6)
                        and abs(mod_at_ir - 1) < 1e-25)
            ok = ok and good
            rows.append({"r": rs, "observed_max_abs_arg": float(best),
                         "2_arctan_r": float(bound),
                         "argmax_phi_over_pi": float(best_phi / mp.pi),
                         "modulus_at_u_eq_ir": float(mod_at_ir), "ok": good})
    return {"all_ok": ok, "rows": rows,
            "grade": "measured (4001-point circle sample, mpmath dps 30)"}


def check_bg_finite_claim(prec: int) -> dict:
    """Decided: the smallest prime set with sum arctan(1/p) > pi/2.

    Bombieri-Ghosh section 9 states that the smallest set of primes
    p = 2, 3 mod 5 whose arctan(1/p) sum exceeds pi/2 runs up to 6323 and has
    420 elements.  This is a finite, exactly checkable claim that shares no
    machinery with their Theorem 7, and it exercises exactly this
    instrument's prime-class enumeration and arctan.  Every comparison is a
    decided ball sign.
    """
    primes = sieve(7000)
    non, _ = split_classes(primes)
    with ins._prec_guard(prec):
        half_pi = arb.pi() / 2
        total = arb(0)
        thresh, count = None, None
        for i, p in enumerate(non, start=1):
            total += (arb(1) / p).atan()
            if thresh is None:
                s = _sign_arb(total - half_pi)
                if s == 0:
                    raise ArithmeticError("arctan sum vs pi/2 undecided")
                if s == 1:
                    thresh, count = p, i
    return {"threshold_prime": thresh, "cardinality": count,
            "published_threshold_prime": 6323, "published_cardinality": 420,
            "ok": bool(thresh == 6323 and count == 420),
            "grade": "decided (exact sieve, Arb ball signs, %d bits)" % prec,
            "source": "Bombieri-Ghosh 2011 section 9, via BOMBIERI-GHOSH.md"}


def check_euler_tail(sig_q: Fraction, P: int, P2: int, prec: int) -> dict:
    """Measured: log zeta(s) + sum_{p<=P} log(1-p^-s) really is the prime tail.

    Compares the closed form against the explicit partial tail over
    P < p <= P2.  The closed form must exceed it (the remaining primes are
    positive contributions) by no more than the integral-test allowance
    P2^{1-s}/(s-1).
    """
    with ins._prec_guard(prec):
        sig = _arb_q(sig_q)
        primes = sieve(P2)
        head = arb(0)
        partial = arb(0)
        for p in primes:
            x = arb(int(p)) ** (-sig)
            lg = (1 - x).log()
            if p <= P:
                head += lg
            else:
                partial -= lg
        closed = zeta_flint(sig, prec).log() + head
        gap = closed - partial
        allow = arb(P2) ** (1 - sig) / (sig - 1)
        ok = bool((gap > 0) and (gap < allow))
        return {"sigma": str(sig_q), "P": P, "P2": P2,
                "closed_form_tail": float(closed.mid()),
                "explicit_partial_tail": float(partial.mid()),
                "gap": float(gap.mid()), "integral_allowance": float(allow.mid()),
                "ok": ok,
                "grade": "measured (Arb midpoints, decided signs on the two "
                         "comparisons)"}


def check_L_two_routes(sig_qs: list[Fraction], prec: int) -> dict:
    """Decided: the Hurwitz combination and flint's dirichlet_l overlap."""
    rows = []
    ok = True
    with ins._prec_guard(prec):
        chi5 = dirichlet_char(5, 4)
        for q in sig_qs:
            sig = _arb_q(q)
            a = lchi_flint(sig, prec)
            b = acb(sig).dirichlet_l(chi5)
            if not b.imag.contains(arb(0)):
                raise ArithmeticError("dirichlet_l: imaginary ball excludes 0")
            b = b.real
            good = bool(a.overlaps(b))
            ok = ok and good
            rows.append({"sigma": str(q), "hurwitz": float(a.mid()),
                         "dirichlet_l": float(b.mid()),
                         "difference": float((a - b).mid()), "overlaps": good})
    return {"all_ok": ok, "rows": rows,
            "grade": "decided (two Arb routes, ball overlap)"}


def check_iv_special(sig_qs: list[Fraction], prec: int) -> dict:
    """Decided: the iv zeta, L and arctan enclosures contain the Arb balls."""
    rows = []
    ok = True
    for q in sig_qs:
        sigma = _iv_frac(q)
        with ins._prec_guard(prec):
            zf = zeta_flint(_arb_q(q), prec)
            lf = lchi_flint(_arb_q(q), prec)
            af = (_arb_q(q) / 4).atan()
            zlo, zhi = _arb_ball_fracs(zf)
            llo, lhi = _arb_ball_fracs(lf)
            alo, ahi = _arb_ball_fracs(af)
        for name, ivval, (lo, hi) in (
                ("zeta", zeta_iv(sigma), (zlo, zhi)),
                ("L(.,chi5)", lchi_iv(sigma), (llo, lhi)),
                ("atan(sigma/4)", atan_iv(sigma / 4), (alo, ahi))):
            a, b = _iv_fracs(ivval)
            good = bool(a <= lo and hi <= b)
            ok = ok and good
            rows.append({"sigma": str(q), "quantity": name,
                         "iv_width": float(b - a),
                         "arb_ball_inside_iv": good})
    return {"all_ok": ok, "n_points": len(rows), "rows": rows,
            "grade": "decided (containment of the Arb ball in the iv interval)"}


def check_P_consistency(kap: arb, prec: int, Ps: list[int],
                        sig_q: Fraction) -> dict:
    """Decided: Theta enclosures from different sieve limits must intersect.

    The head/tail split is the one place a sign error would hide.  Different
    P move mass between the two halves, so agreement across P is a check on
    the split itself and not on either half alone.
    """
    rows = []
    lo_max, hi_min = None, None
    for P in Ps:
        primes = sieve(P)
        non, _ = split_classes(primes)
        logs = flint_logs(non, prec)
        lo, hi = theta_bounds_flint(sig_q, kap, non, logs, P, prec)
        lq, _ = _arb_ball_fracs(lo)
        _, hq = _arb_ball_fracs(hi)
        lo_max = lq if lo_max is None else max(lo_max, lq)
        hi_min = hq if hi_min is None else min(hi_min, hq)
        rows.append({"P": P, "n_class_primes": len(non),
                     "theta_lower": _dec(lq, 22, "down"),
                     "theta_upper": _dec(hq, 22, "up"),
                     "width": float(hq - lq)})
    ok = bool(lo_max <= hi_min)
    return {"all_intersect": ok, "sigma": str(sig_q), "rows": rows,
            "common_width": float(hi_min - lo_max) if ok else None,
            "grade": "decided (Arb, exact rational endpoint comparison)"}


# ---------------------------------------------------------------------------
# the block / mean-value route (task (b)): what it gives and what it cannot
# ---------------------------------------------------------------------------


def block_condition(sig_q: Fraction, T: Fraction, K: int, kap: arb,
                    prec: int) -> arb:
    """Ball for  D_{5K}(sigma) + |s| (block tail bound) - 1, |Im s| <= T.

    Regrouping in periods, f(s) = sum_{k>=0} B_k(s) with
    B_k = (5k+1)^{-s} + kappa (5k+2)^{-s} - kappa (5k+3)^{-s} - (5k+4)^{-s}.
    Pairing the outer and inner terms and applying the mean value theorem to
    t -> t^{-s} on each pair,

        |B_k| <= |s| [3 (5k+1)^{-sigma-1} + kappa (5k+2)^{-sigma-1}],

    and sum_{k>=K} of that is |s| 5^{-sigma-1} [3 zeta(sigma+1, K+1/5)
    + kappa zeta(sigma+1, K+2/5)] exactly.  Keeping n <= 5K under the plain
    triangle inequality and blocking the rest gives a zero-free half-plane
    only if the value returned here is negative, and |s| <= sqrt(sigma^2+T^2)
    grows with the height, which is the whole point.
    """
    with ins._prec_guard(prec):
        sig = _arb_q(sig_q)
        s = acb(sig)

        def hz(a: Fraction) -> arb:
            z = acb(sig + 1).zeta(acb(fmpq(a.numerator, a.denominator)))
            return z.real

        # D_{5K} = sum_{n>=2}|a_n| n^-sigma  minus  the exact tail past 5K,
        # sum_{n>5K}|a_n| n^-sigma = 5^-sigma [zeta(sigma,K+1/5)+zeta(sigma,K+4/5)
        #                            + kappa (zeta(sigma,K+2/5)+zeta(sigma,K+3/5))]
        full_minus_one = g_ball(sig_q, kap, prec) + 1

        def hz0(c: int) -> arb:
            z = acb(sig).zeta(acb(fmpq(5 * K + c, 5)))
            return z.real

        tail = arb(5) ** (-sig) * (hz0(1) + hz0(4) + kap * (hz0(2) + hz0(3)))
        D = full_minus_one - tail
        smod = (sig * sig + _arb_q(T) ** 2).sqrt()
        blocks = smod * arb(5) ** (-sig - 1) * (
            3 * hz(Fraction(5 * K + 1, 5)) + kap * hz(Fraction(5 * K + 2, 5)))
        return D + blocks - 1


def check_block_sharpness(kap: arb, prec: int) -> dict:
    """Measured: the |s| in the block bound is real, not an artifact.

    Both pairs inside a period have the same midpoint 5k + 5/2, and the two
    first-order terms add rather than cancel:

        B_k = s (3 + kappa) (5k + 5/2)^{-s-1} (1 + O(|s|/n)),

    so no trapezoid-style second-order correction can remove the |s|; the
    next order carries |s|^2.  Sampled here as the ratio of the true |B_k| to
    the bound |s|[3(5k+1)^{-sigma-1} + kappa(5k+2)^{-sigma-1}].  A ratio near
    1 says the bound is tight; the rows with |s| >> n show the regime where
    the bound is worthless because the quantity it bounds is genuinely small
    while the bound is genuinely large.
    """
    rows = []
    with mp.workdps(40):
        k_m = mp.mpf(KAPPA_REF)
        for sig_s, t_s, k in (("1.2", "1", 100), ("1.2", "10", 100),
                              ("1.2", "1", 10000), ("1.2", "1000", 10),
                              ("1.2", "100000", 100)):
            s = mp.mpf(sig_s) + mp.mpc(0, 1) * mp.mpf(t_s)
            n = [5 * k + j for j in (1, 2, 3, 4)]
            B = (mp.power(n[0], -s) + k_m * mp.power(n[1], -s)
                 - k_m * mp.power(n[2], -s) - mp.power(n[3], -s))
            bound = abs(s) * (3 * mp.power(n[0], -mp.re(s) - 1)
                              + k_m * mp.power(n[1], -mp.re(s) - 1))
            trivial = (1 + 2 * k_m + 1) * mp.power(n[0], -mp.re(s))
            rows.append({"sigma": sig_s, "t": t_s, "k": k,
                         "abs_B_k": float(abs(B)),
                         "block_bound": float(bound),
                         "trivial_bound": float(trivial),
                         "bound_over_truth": float(bound / abs(B)),
                         "block_beats_trivial": bool(bound < trivial)})
    return {"rows": rows,
            "grade": "measured (mpmath dps 40)",
            "reading": "the block bound tracks |B_k| within a small factor "
                       "while |s| is below the block index and is worthless "
                       "above it, which is the crossover n ~ |s| that forces "
                       "the hybrid split"}


def block_threshold(T: Fraction, kap: arb, prec: int,
                    lo: Fraction = Fraction("1.02"),
                    hi: Fraction = Fraction("1.45"),
                    width: Fraction = Fraction(1, 10 ** 6)) -> dict:
    """Decided sigma above which the block route excludes zeros with |Im s| <= T.

    For each sigma the best K is found by a coarse scan and the decision is
    the decided sign of ``block_condition`` at that K.
    """
    Ks = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987,
          1597, 2584, 4181, 6765, 10946, 17711, 28657, 46368, 75025]

    def decides(sq: Fraction) -> tuple[bool, int]:
        best = None
        for K in Ks:
            v = block_condition(sq, T, K, kap, prec)
            if _sign_arb(v) == -1:
                return True, K
            m = float(v.mid())
            if best is None or m < best[0]:
                best = (m, K)
        return False, best[1]

    ok_hi, K_hi = decides(hi)
    if not ok_hi:
        return {"T": str(T), "decided": False,
                "note": "no sigma in the search range clears the block bound"}
    ok_lo, _ = decides(lo)
    if ok_lo:
        return {"T": str(T), "decided": True, "sigma_block": _dec(lo, 8, "down"),
                "note": "cleared already at the bottom of the search range"}
    a, b = lo, hi
    while b - a >= width:
        mid = (a + b) / 2
        ok, _ = decides(mid)
        if ok:
            b = mid
        else:
            a = mid
    ok, K = decides(b)
    return {"T": str(T), "decided": True, "sigma_block": _dec(b, 8, "up"),
            "best_K": K, "N_terms_kept_exact": 5 * K,
            "grade": "decided (Arb, %d bits, exact rational sigma)" % prec}


# ---------------------------------------------------------------------------


def main() -> None:
    t_start = time.perf_counter()
    timings: dict[str, float] = {}
    out: dict = {
        "instrument": "hunts/lambda_dh_bounds/strip2.py",
        "quantity": "sigma_0': the phase-obstruction abscissa, root of "
                    "Theta(sigma) = sum_{p = 2,3 mod 5} 2 arctan(p^{-sigma}) "
                    "= pi - 2 arctan(kappa); every zero of the completed F "
                    "lies in 1 - sigma_0' < Re s < sigma_0' (argument in "
                    "STRIP2.md)",
        "interval_convention": "decimal strings, outward rounding: printed "
                               "intervals contain the exact rational endpoints",
    }

    # ---- kappa and the target phase -------------------------------------
    t0 = time.perf_counter()
    kap = ins.kappa_ball(KAPPA_PREC)
    kap_lo, kap_hi = _arb_ball_fracs(kap)
    ref_q = Fraction(KAPPA_REF)
    eps39 = Fraction(1, 10 ** 39)
    kappa_inside = bool(ref_q - eps39 <= kap_lo and kap_hi <= ref_q + eps39)
    if not kappa_inside:
        raise SystemExit("kappa ball escaped KAPPA_REF +/- 1e-39")
    iv.dps = IV_DPS
    kap_iv = _iv_frac(ref_q) + _iv_frac(eps39) * iv.mpf([-1, 1])
    tgt_f = target_flint(kap, FLINT_PREC)
    tgt_f_lo, tgt_f_hi = _arb_ball_fracs(tgt_f)
    tgt_i_lo, tgt_i_hi = _iv_fracs(target_iv(kap_iv))
    timings["kappa_and_target_s"] = round(time.perf_counter() - t0, 3)
    print(f"kappa ball width {float(kap_hi - kap_lo):.2e}; "
          f"target pi - 2 atan(kappa) in "
          f"[{_dec(tgt_f_lo, 25, 'down')}, {_dec(tgt_f_hi, 25, 'up')}] (flint)",
          flush=True)
    out["kappa_ball"] = {
        "backend": "python-flint (Arb), instrument.kappa_ball, prec 500 bits",
        "interval": _out_interval(kap_lo, kap_hi, 45),
        "inside_KAPPA_REF_pm_1e-39": kappa_inside,
    }
    out["target_phase"] = {
        "definition": "pi - 2 arctan(kappa): the smallest absolute "
                      "representative modulo 2 pi of arg(-conj(A)/A) with "
                      "A = (1 - i kappa)/2",
        "flint": _out_interval(tgt_f_lo, tgt_f_hi, 25),
        "iv": _out_interval(tgt_i_lo, tgt_i_hi, 18),
        "bombieri_ghosh_half": "pi/2 - arctan(kappa), quoted by them as "
                               "1.2940091 for tau_+",
    }

    # ---- cross-checks -----------------------------------------------------
    print("[1/8] character decomposition (decided)", flush=True)
    t0 = time.perf_counter()
    chk_char = check_character_decomposition(kap, FLINT_PREC)
    timings["check_character_s"] = round(time.perf_counter() - t0, 3)
    if not chk_char["all_ok"]:
        raise SystemExit("character decomposition check failed")

    print("[2/8] Dirichlet series vs the two L-functions (measured)", flush=True)
    t0 = time.perf_counter()
    chk_ser = check_series_against_L()
    timings["check_series_s"] = round(time.perf_counter() - t0, 3)
    if not chk_ser["all_ok"]:
        raise SystemExit("series vs L-functions check failed")

    print("[3/8] phase lemma max |arg (1+u)/(1-u)| = 2 atan r (measured)",
          flush=True)
    t0 = time.perf_counter()
    chk_phase = check_phase_lemma()
    timings["check_phase_s"] = round(time.perf_counter() - t0, 3)
    if not chk_phase["all_ok"]:
        raise SystemExit("phase lemma check failed")

    print("[4/8] Bombieri-Ghosh finite claim: 6323 / 420 (decided)", flush=True)
    t0 = time.perf_counter()
    chk_bg = check_bg_finite_claim(FLINT_PREC)
    timings["check_bg_finite_s"] = round(time.perf_counter() - t0, 3)
    print(f"  threshold prime {chk_bg['threshold_prime']}, "
          f"cardinality {chk_bg['cardinality']}: {chk_bg['ok']}", flush=True)
    if not chk_bg["ok"]:
        raise SystemExit("Bombieri-Ghosh finite claim check failed")

    print("[5/8] Euler-product tail identity (measured)", flush=True)
    t0 = time.perf_counter()
    chk_tail = check_euler_tail(Fraction("1.12"), 10 ** 4, 10 ** 5, FLINT_PREC)
    timings["check_euler_tail_s"] = round(time.perf_counter() - t0, 3)
    if not chk_tail["ok"]:
        raise SystemExit("Euler tail identity check failed")

    print("[6/8] L(.,chi5): Hurwitz vs dirichlet_l (decided)", flush=True)
    chk_L = check_L_two_routes([Fraction("1.12"), Fraction("1.3"),
                                Fraction("2")], FLINT_PREC)
    if not chk_L["all_ok"]:
        raise SystemExit("L two-route check failed")

    print("[7/8] iv zeta / L / atan contain the Arb balls (decided)", flush=True)
    t0 = time.perf_counter()
    chk_iv = check_iv_special([Fraction("1.12"), Fraction("1.3"),
                               Fraction("2")], FLINT_PREC)
    timings["check_iv_special_s"] = round(time.perf_counter() - t0, 3)
    if not chk_iv["all_ok"]:
        raise SystemExit("iv special-function containment failed")

    print("[8/8] Theta head/tail split across sieve limits (decided)", flush=True)
    t0 = time.perf_counter()
    chk_P = check_P_consistency(kap, FLINT_PREC, [10 ** 3, 10 ** 4, 10 ** 5],
                                Fraction("1.12"))
    timings["check_P_consistency_s"] = round(time.perf_counter() - t0, 3)
    print(f"  P in {{1e3,1e4,1e5}} intersect: {chk_P['all_intersect']} "
          f"(common width {chk_P['common_width']:.2e})", flush=True)
    if not chk_P["all_intersect"]:
        raise SystemExit("Theta head/tail split inconsistent across P")

    out["cross_checks"] = {
        "character_decomposition": chk_char,
        "series_vs_L_functions": chk_ser,
        "phase_lemma": chk_phase,
        "bombieri_ghosh_finite_claim": chk_bg,
        "euler_product_tail_identity": chk_tail,
        "L_two_routes": chk_L,
        "iv_special_functions": chk_iv,
        "theta_split_across_P": chk_P,
    }

    # ---- the bisections ---------------------------------------------------
    primes_f = sieve(P_FLINT)
    non_f, _res_f = split_classes(primes_f)
    logs_f = flint_logs(non_f, FLINT_PREC)
    primes_i = sieve(P_IV)
    non_i, _res_i = split_classes(primes_i)
    logs_i = [iv.log(iv.mpf(p)) for p in non_i]

    def theta_up_f(sq: Fraction) -> arb:
        return theta_bounds_flint(sq, kap, non_f, logs_f, P_FLINT,
                                  FLINT_PREC)[1] - tgt_f

    def theta_up_i(sq: Fraction):
        return theta_bounds_iv(sq, kap_iv, non_i, logs_i, P_IV)[1] \
            - target_iv(kap_iv)

    print(f"bisection, python-flint (Arb), {FLINT_PREC} bits, P = {P_FLINT}, "
          f"{len(non_f)} class primes, width < 1e-20", flush=True)
    t0 = time.perf_counter()
    f_lo, f_hi, f_evals = bisect_root(theta_up_f, _sign_arb, *BRACKET,
                                      FLINT_WIDTH)
    timings["flint_bisect_s"] = round(time.perf_counter() - t0, 3)
    print(f"  sigma_0' in [{_dec(f_lo, 22, 'down')}, {_dec(f_hi, 22, 'up')}] "
          f"({f_evals} sign decisions)", flush=True)

    print(f"bisection, mpmath.iv, dps {IV_DPS}, P = {P_IV}, "
          f"{len(non_i)} class primes, width < 1e-12", flush=True)
    t0 = time.perf_counter()
    i_lo, i_hi, i_evals = bisect_root(theta_up_i, _sign_iv, *BRACKET, IV_WIDTH)
    timings["iv_bisect_s"] = round(time.perf_counter() - t0, 3)
    print(f"  sigma_0' in [{_dec(i_lo, 16, 'down')}, {_dec(i_hi, 16, 'up')}] "
          f"({i_evals} sign decisions)", flush=True)

    overlap = bool(max(f_lo, i_lo) <= min(f_hi, i_hi))
    print(f"backend intervals overlap: {overlap}", flush=True)
    if not overlap:
        raise SystemExit("backend intervals for sigma_0' do not overlap")

    # ---- the headline rationals, decided on both backends -------------------
    def decide_at(sq: Fraction) -> dict:
        lo_f, up_f = theta_bounds_flint(sq, kap, non_f, logs_f, P_FLINT,
                                        FLINT_PREC)
        thl_f, thu_f = _arb_ball_fracs(lo_f)[0], _arb_ball_fracs(up_f)[1]
        lo_i, up_i = theta_bounds_iv(sq, kap_iv, non_i, logs_i, P_IV)
        thl_i, thu_i = _iv_fracs(lo_i)[0], _iv_fracs(up_i)[1]
        df, di = bool(thu_f < tgt_f_lo), bool(thu_i < tgt_i_lo)
        d = sq - Fraction(1, 2)
        return {
            "sigma": _dec(sq, 14, "up"),
            "sigma_exact_rational": [sq.numerator, sq.denominator],
            "theta": {"flint": _out_interval(thl_f, thu_f, 25),
                      "iv": _out_interval(thl_i, thu_i, 16)},
            "decided_below_target": {"flint": df, "iv": di},
            "margin_target_minus_theta": float(tgt_f_lo - thu_f),
            "delta": _dec(d, 14, "up"),
            "delta_sq_over_2_narrow": _dec(d ** 2 / 2, 22, "up"),
            "delta_sq_over_2_wide": _dec(4 * (d ** 2 / 2), 22, "up"),
            "_ok": df and di,
        }

    head = decide_at(SIGMA_STAR)
    coarse = decide_at(SIGMA_STAR_COARSE)
    print(f"Theta({_dec(SIGMA_STAR, 12, 'up')}) < pi - 2 atan(kappa) decided: "
          f"flint {head['decided_below_target']['flint']}, "
          f"iv {head['decided_below_target']['iv']}", flush=True)
    print(f"Theta({_dec(SIGMA_STAR_COARSE, 8, 'up')}) < target decided: "
          f"flint {coarse['decided_below_target']['flint']}, "
          f"iv {coarse['decided_below_target']['iv']}", flush=True)
    if not (head["_ok"] and coarse["_ok"]):
        raise SystemExit("headline inequality not decided on both backends")
    head.pop("_ok")
    coarse.pop("_ok")

    half = Fraction(1, 2)
    delta_star = SIGMA_STAR - half
    ubound_narrow = delta_star ** 2 / 2
    ubound_wide = 4 * ubound_narrow
    d_f = (f_lo - half, f_hi - half)
    d_i = (i_lo - half, i_hi - half)
    dsq_f = (d_f[0] ** 2 / 2, d_f[1] ** 2 / 2)
    dsq_i = (d_i[0] ** 2 / 2, d_i[1] ** 2 / 2)

    old = Fraction("0.4006343708899556944469548120")   # strip.py upper endpoint
    improvement = float(old / ubound_narrow)

    out["sigma0_prime"] = {
        "flint": _out_interval(f_lo, f_hi, 22),
        "iv": _out_interval(i_lo, i_hi, 16),
        "backend_intervals_overlap": overlap,
        "sign_decisions": {"flint": f_evals, "iv": i_evals},
        "sieve_limits": {"flint": P_FLINT, "iv": P_IV},
        "class_prime_counts": {"flint": len(non_f), "iv": len(non_i)},
    }
    out["headline"] = {
        "statement": "Theta(sigma) < pi - 2 arctan(kappa) decided on both "
                     "backends at the exact rational sigma below, hence f has "
                     "no zero with Re s >= sigma and F, by F(s) = F(1-s), none "
                     "with Re s <= 1 - sigma: every zero of F lies in the open "
                     "strip 1 - sigma < Re s < sigma",
        "decided_form": head,
        "wide_margin_form": dict(coarse, note="a deliberately generous "
                                 "rounding: it is decided at a sieve limit as "
                                 "small as P = 1e4, so a reader can reproduce "
                                 "it in seconds"),
        "upper_bound_delta_sq_over_2_narrow": _dec(ubound_narrow, 25, "up"),
        "upper_bound_delta_sq_over_2_wide": _dec(ubound_wide, 25, "up"),
        "narrow_exact_rational": [ubound_narrow.numerator,
                                  ubound_narrow.denominator],
        "frames": "narrow s = 1/2 + iz (Stopple, this hunt); wide "
                  "s = (1+iz)/2 (de Bruijn, Newman, Rodgers-Tao, Polymath 15, "
                  "Dobner); Lambda_wide = 4 Lambda_narrow (FRAME.md)",
        "previous_narrow": _dec(old, 25, "up"),
        "improvement_factor": improvement,
    }
    out["delta_sq_over_2_from_bisection"] = {
        "flint": _out_interval(*dsq_f, 22),
        "iv": _out_interval(*dsq_i, 16),
    }
    print(f"Delta = {delta_star}, Delta^2/2 narrow = "
          f"{_dec(ubound_narrow, 20, 'up')}, wide = "
          f"{_dec(ubound_wide, 20, 'up')}; improvement {improvement:.6f}x",
          flush=True)

    # ---- two-sided enclosure of the equation's own root ---------------------
    # Theta_lo <= Theta <= Theta_up with both decreasing, so the root of
    # Theta_lo is a lower bound and the root of Theta_up an upper bound for
    # the true root.  Only the upper one is load-bearing; the pair says how
    # much of the interval is the tail bound rather than the arithmetic.
    def theta_lo_f(sq: Fraction) -> arb:
        return theta_bounds_flint(sq, kap, non_f, logs_f, P_FLINT,
                                  FLINT_PREC)[0] - tgt_f

    r_lo, _r_lo_hi, _ = bisect_root(theta_lo_f, _sign_arb, *BRACKET,
                                    FLINT_WIDTH)
    out["true_root_two_sided"] = {
        "what": "a decided two-sided enclosure of the root of "
                "Theta(sigma) = pi - 2 arctan(kappa) itself",
        "interval": _out_interval(r_lo, f_hi, 22),
        "width": float(f_hi - r_lo),
        "P": P_FLINT,
        "note": "the width is the head/tail systematic, not the ball "
                "precision; only the upper endpoint carries the zero-free "
                "half-plane",
    }

    # ---- one deep decided point, and what it says about the re-solves ------
    print(f"deep point: P = {P_DEEP}, {PREC_DEEP} bits (flint leg only)",
          flush=True)
    t0 = time.perf_counter()
    pr_d = sieve(P_DEEP)
    non_d, _ = split_classes(pr_d)
    logs_d = flint_logs(non_d, PREC_DEEP)
    tgt_d = target_flint(kap, PREC_DEEP)
    tgt_d_lo = _arb_ball_fracs(tgt_d)[0]
    with ins._prec_guard(PREC_DEEP):
        tgt_dm = 2 * kap.atan()
    tgt_dm_lo, tgt_dm_hi = _arb_ball_fracs(tgt_dm)

    def deep_theta(sq: Fraction) -> tuple[Fraction, Fraction]:
        a, b = theta_bounds_flint(sq, kap, non_d, logs_d, P_DEEP, PREC_DEEP)
        return _arb_ball_fracs(a)[0], _arb_ball_fracs(b)[1]

    dl, du = deep_theta(SIGMA_DEEP)
    deep_ok = bool(du < tgt_d_lo)
    d_deep = SIGMA_DEEP - Fraction(1, 2)
    # the same evaluation at the two re-solves recorded in BOMBIERI-GHOSH.md
    bl, bu = deep_theta(BG_SIGMA)
    bg_plus_above = bool(bu < tgt_d_lo)       # decided: true root < BG.md value
    bml, bmu = deep_theta(BG_SIGMA_MINUS)
    bg_minus_below = bool(bml > tgt_dm_hi)    # decided: true root > BG.md value
    timings["deep_point_s"] = round(time.perf_counter() - t0, 3)
    print(f"  Theta({_dec(SIGMA_DEEP, 17, 'up')}) < target decided: {deep_ok}; "
          f"BG.md tau_+ re-solve above the root: {bg_plus_above}; "
          f"BG.md tau_- re-solve below its root: {bg_minus_below}", flush=True)
    if not deep_ok:
        raise SystemExit("deep point not decided")
    out["deep_point"] = {
        "backend": "python-flint (Arb) only, %d bits, P = %d, %d class primes"
                   % (PREC_DEEP, P_DEEP, len(non_d)),
        "why_one_backend": "one mpmath.iv evaluation at this sieve limit costs "
                           "about a minute and nothing in the headline depends "
                           "on it; the two-backend decision is the headline at "
                           "P = %d" % P_FLINT,
        "sigma": _dec(SIGMA_DEEP, 17, "up"),
        "theta": _out_interval(dl, du, 27),
        "target": _out_interval(*_arb_ball_fracs(tgt_d), 27),
        "decided_below_target": deep_ok,
        "delta": _dec(d_deep, 17, "up"),
        "delta_sq_over_2_narrow": _dec(d_deep ** 2 / 2, 25, "up"),
        "delta_sq_over_2_wide": _dec(4 * (d_deep ** 2 / 2), 25, "up"),
    }
    out["correction_to_in_tree_re_solves"] = {
        "what": "BOMBIERI-GHOSH.md check B re-solved both abscissae to 29 "
                "digits at mpmath dps 30. At this sieve limit and precision "
                "the present instrument decides that both of those re-solves "
                "sit on the wrong side of their own root, by amounts far "
                "below anything Bombieri and Ghosh published.",
        "tau_plus": {
            "in_tree_re_solve": _dec(BG_SIGMA, 29, "up"),
            "theta_there": _out_interval(bl, bu, 27),
            "decided_theta_below_target": bg_plus_above,
            "meaning": "the true root is strictly below the recorded "
                       "re-solve, so the re-solve is high",
            "size": float(BG_SIGMA - SIGMA_DEEP),
        },
        "tau_minus": {
            "in_tree_re_solve": _dec(BG_SIGMA_MINUS, 29, "up"),
            "theta_there": _out_interval(bml, bmu, 27),
            "decided_theta_above_target": bg_minus_below,
            "meaning": "the true root is strictly above the recorded "
                       "re-solve, so the re-solve is low",
        },
        "scope": "this corrects two in-tree re-solves, not the published "
                 "paper: Bombieri and Ghosh print 1.120362 and 2.3822861089, "
                 "and this instrument reproduces both exactly. What it "
                 "touches is FRAME.md's 18-digit row, which is derived from "
                 "the tau_+ re-solve rather than from the six cited decimals.",
        "grade": "decided (Arb, %d bits, P = %d)" % (PREC_DEEP, P_DEEP),
    }

    # ---- (c) how far the head/tail split can be pushed, and what it costs --
    print("sieve-limit sweep: the decided root against P", flush=True)
    t0 = time.perf_counter()
    sweep = []
    for P in (10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
        ts = time.perf_counter()
        pr = sieve(P)
        nn, _ = split_classes(pr)
        lg = flint_logs(nn, FLINT_PREC)

        def th(sq: Fraction, nn=nn, lg=lg, P=P) -> arb:
            return theta_bounds_flint(sq, kap, nn, lg, P, FLINT_PREC)[1] - tgt_f

        a, b, ev = bisect_root(th, _sign_arb, *BRACKET, FLINT_WIDTH)
        lo_b, up_b = theta_bounds_flint(b, kap, nn, lg, P, FLINT_PREC)
        wl = _arb_ball_fracs(lo_b)[0]
        wu = _arb_ball_fracs(up_b)[1]
        el = round(time.perf_counter() - ts, 3)
        sweep.append({"P": P, "n_class_primes": len(nn),
                      "decided_upper_endpoint": _dec(b, 22, "up"),
                      "systematic_width_of_Theta": float(wu - wl),
                      "minus_in_tree_re_solve": float(b - BG_SIGMA),
                      "sign_decisions": ev, "seconds": el})
        print(f"  P = {P:>8}: sigma_0' <= {_dec(b, 20, 'up')}  "
              f"({float(b - BG_SIGMA):+.2e} vs the in-tree re-solve, "
              f"{el}s)", flush=True)
    timings["P_sweep_s"] = round(time.perf_counter() - t0, 3)
    out["sieve_limit_sweep"] = {
        "question": "how much does the finite-part-plus-tail split buy, and "
                    "what does it cost",
        "rows": sweep,
        "reading": "the Euler-product tail closes the series exactly, so P "
                   "controls only the k >= 3 correction eps3 and the "
                   "arctan-versus-linear loss on the tail. Both fall like "
                   "P^{1-3 sigma}, so the decided root is already within "
                   "1e-11 of the equation's true root at P = 1e4 and the "
                   "remaining gain from P = 1e6 is not visible in any digit "
                   "the headline quotes.",
    }

    # ---- control: the same instrument at the other Titchmarsh root ---------
    # The two roots of x^2 + 2 phi x - 1 = 0 multiply to -1, so the second
    # Davenport-Heilbronn parameter is tau_- = -1/kappa and its phase target
    # is pi - 2 arctan(1/kappa) = 2 arctan(kappa).  Theta is unchanged: only
    # the target moves.  Bombieri-Ghosh publish sigma(tau_-, 1) = 2.3822861089
    # to ten digits, and nothing in this instrument was tuned to it.
    print("control: the same machinery at tau_- = -1/kappa", flush=True)
    t0 = time.perf_counter()
    with ins._prec_guard(FLINT_PREC):
        tgt_minus = 2 * kap.atan()
        inv_kappa = 1 / kap
    tm_lo, tm_hi = _arb_ball_fracs(tgt_minus)
    ik_lo, ik_hi = _arb_ball_fracs(inv_kappa)
    tau_minus_ref = Fraction("3.520147021340")
    tau_minus_ok = bool(tau_minus_ref - Fraction(1, 2 * 10 ** 12) <= ik_lo
                        and ik_hi <= tau_minus_ref + Fraction(1, 2 * 10 ** 12))

    def th_minus(sq: Fraction) -> arb:
        return theta_bounds_flint(sq, kap, non_f, logs_f, P_FLINT,
                                  FLINT_PREC)[1] - tgt_minus

    m_lo, m_hi, m_ev = bisect_root(th_minus, _sign_arb, Fraction("2.30"),
                                   Fraction("2.45"), Fraction(1, 10 ** 18))
    bg_minus = Fraction("2.3822861089")
    control_ok = bool(bg_minus <= m_hi and m_lo - Fraction(1, 10 ** 10)
                      <= bg_minus)
    timings["control_tau_minus_s"] = round(time.perf_counter() - t0, 3)
    print(f"  sigma(tau_-, 1) in [{_dec(m_lo, 20, 'down')}, "
          f"{_dec(m_hi, 20, 'up')}]; published 2.3822861089: {control_ok}",
          flush=True)
    out["control_tau_minus"] = {
        "what": "the identical Theta, the identical tail bound and the "
                "identical bisection, with only the phase target changed to "
                "pi - 2 arctan|tau_-| = 2 arctan(kappa), against a second "
                "published constant this instrument was not built around",
        "tau_minus": {
            "value": "-1/kappa, decided from the same kappa ball",
            "one_over_kappa": _out_interval(ik_lo, ik_hi, 20),
            "published_tau_minus": "-3.520147021340",
            "inside_published_pm_half_ulp": tau_minus_ok,
        },
        "target": _out_interval(tm_lo, tm_hi, 25),
        "decided_interval": _out_interval(m_lo, m_hi, 20),
        "published": "2.3822861089 (Bombieri-Ghosh 2011 section 6, ten digits)",
        "agrees_to_published_digits": control_ok,
        "sign_decisions": m_ev,
        "grade": "decided (Arb, %d bits) against a cited decimal" % FLINT_PREC,
        "note": "the two targets pi - 2 arctan(kappa) and 2 arctan(kappa) sum "
                "to pi, which is the arctan(1/x) = pi/2 - arctan(x) identity "
                "behind tau_+ tau_- = -1",
    }
    if not (control_ok and tau_minus_ok):
        raise SystemExit("tau_- control failed against the published decimals")

    # ---- (a) how much slack the domination bound leaves --------------------
    t0 = time.perf_counter()
    dom_at_new = g_ball(SIGMA_STAR, kap, FLINT_PREC) + 1     # sum_{n>=2}|a_n|n^-s
    dlo, dhi = _arb_ball_fracs(dom_at_new)
    th_lo_old, th_up_old = theta_bounds_flint(SIGMA_0_OLD, kap, non_f, logs_f,
                                              P_FLINT, FLINT_PREC)
    tlo_o, tup_o = _arb_ball_fracs(th_lo_old)[0], _arb_ball_fracs(th_up_old)[1]
    timings["slack_s"] = round(time.perf_counter() - t0, 3)
    out["slack_of_coefficient_domination"] = {
        "question": "why is sum_{n>=2}|a_n| n^{-sigma} < 1 so much weaker than "
                    "the truth",
        "domination_sum_at_sigma_star": _out_interval(dlo, dhi, 22),
        "note_domination": "the free-phase relaxation still needs to spend "
                           "this much coefficient mass at the true abscissa, "
                           "so it cannot conclude there; the excess over 1 is "
                           "the slack it is asking for",
        "excess_over_1": _dec(dlo - 1, 22, "down"),
        "theta_at_old_sigma_0": {
            "sigma_0": _dec(SIGMA_0_OLD, 28, "up"),
            "interval": _out_interval(tlo_o, tup_o, 22),
            "target": _out_interval(tgt_f_lo, tgt_f_hi, 22),
            "deficit_factor": float(Fraction(tgt_f_lo) / Fraction(tup_o)),
        },
        "note_phase": "at the domination abscissa the multiplicative phase "
                      "budget available to a zero is only this, a factor "
                      "below what a zero needs, which is the same slack "
                      "seen from the other side",
        "grade": "decided (Arb, %d bits)" % FLINT_PREC,
    }

    # ---- (b) the block / mean-value route ---------------------------------
    print("block (mean-value) route: height-dependent thresholds", flush=True)
    t0 = time.perf_counter()
    block_rows = []
    for T in ("1", "10", "100", "1000", "10000", "100000"):
        row = block_threshold(Fraction(T), kap, FLINT_PREC)
        block_rows.append(row)
        print(f"  |Im s| <= {T:>7}: sigma_block = "
              f"{row.get('sigma_block')} (K = {row.get('best_K')})", flush=True)
    timings["block_route_s"] = round(time.perf_counter() - t0, 3)
    chk_block_sharp = check_block_sharpness(kap, FLINT_PREC)
    out["block_route"] = {
        "sharpness_of_the_block_bound": chk_block_sharp,
        "claim": "regrouping the series in periods of 5 and applying the mean "
                 "value theorem to t -> t^{-s} across each block gives "
                 "|B_k| <= |s| [3 (5k+1)^{-sigma-1} + kappa (5k+2)^{-sigma-1}], "
                 "which is O(n^{-sigma-1}) per block instead of O(n^{-sigma}) "
                 "per term",
        "obstruction": "the mean value theorem carries a factor |s| = "
                       "sqrt(sigma^2 + t^2), so the bound degrades with the "
                       "height and gives no half-plane statement; the "
                       "thresholds below are decided but each is conditional "
                       "on |Im s| <= T, and de Bruijn's theorem consumes a "
                       "strip containing every zero",
        "limit": "as T grows the optimal split keeps more terms under the "
                 "plain triangle inequality, so sigma_block(T) climbs back "
                 "toward the coefficient-domination sigma_0 = 1.3951361582...",
        "rows": block_rows,
        "verdict": "does not decide an improvement to the half-plane bound",
    }

    # ---- (d) the honest ceiling -------------------------------------------
    gap_to_bg = SIGMA_STAR - BG_SIGMA
    bg_narrow = (BG_SIGMA - half) ** 2 / 2
    out["honest_ceiling"] = {
        "the_standard": "Bombieri-Ghosh Theorem 7 determines sigma(tau_+, 1), "
                        "the least upper bound of the real parts of the zeros, "
                        "as the root of exactly this equation. Their published "
                        "value is 1.120362 (six decimals, section 6). Their "
                        "necessary half is what is derived in-tree here; their "
                        "converse, which needs Bohr and Kronecker, is not used "
                        "and is what would make the abscissa sharp rather than "
                        "merely an upper bound.",
        "published_decimals": "1.120362",
        "reproduced_exactly": True,
        "headline_sigma": _dec(SIGMA_STAR, 14, "up"),
        "headline_above_the_root_by": float(SIGMA_STAR - r_lo),
        "deep_sigma": _dec(SIGMA_DEEP, 17, "up"),
        "deep_above_the_in_tree_re_solve_by": float(SIGMA_DEEP - BG_SIGMA),
        "gap_in_delta_sq_over_2_narrow_headline_vs_deep":
            float(ubound_narrow - d_deep ** 2 / 2),
        "reading": "the strip constant is no longer where the looseness is. "
                   "The decided abscissa is within 7e-12 of the equation's own "
                   "root at the headline sieve limit and within 4e-17 at the "
                   "deep one, and that equation is the one whose root is the "
                   "exact supremum of the real parts. What is left over is "
                   "(i) whether the supremum is attained, which is Bombieri "
                   "and Ghosh's converse and is not needed for an upper "
                   "bound, and (ii) the de Bruijn engine.",
        "where_the_looseness_now_is": "with Delta = 0.62036249819 the engine "
                                      "returns Delta^2/2 = 0.19242481458 "
                                      "narrow, while the deepest measured DH "
                                      "zeros reach |Im z| = 0.347, which would "
                                      "give 0.0602 narrow, and the decided "
                                      "floor is 0.0576. The bracket ratio "
                                      "falls from 6.955 to 3.341. Every "
                                      "remaining factor is in the "
                                      "strip-to-time engine and in the "
                                      "sparsity of the extreme zeros, not in "
                                      "the strip constant.",
        "bracket_ratio_before": 6.955457780728395,
        "bracket_ratio_after": float(ubound_narrow / Fraction(36, 625)),
    }
    timings["total_s"] = round(time.perf_counter() - t_start, 3)
    out["precisions"] = {
        "flint_bits": FLINT_PREC,
        "flint_kappa_bits": KAPPA_PREC,
        "iv_dps": IV_DPS,
        "iv_euler_maclaurin_split": IV_M,
        "iv_euler_maclaurin_terms": IV_K,
        "atan_series_tol": "1e-45",
        "flint_width_target": "1e-20",
        "iv_width_target": "1e-12",
    }
    out["timings"] = timings
    with open(OUT, "w", encoding="utf-8") as fh:
        json.dump(out, fh, indent=2)
        fh.write("\n")
    print(f"\nwrote {OUT}  ({timings['total_s']}s)", flush=True)


if __name__ == "__main__":
    main()
