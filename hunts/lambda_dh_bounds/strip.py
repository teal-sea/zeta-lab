"""Zero-strip constant sigma_0 for the completed Davenport-Heilbronn function.

Decides, on both in-tree directed-rounding backends, the unique root
sigma_0 > 1 of

    g(sigma) := sum_{n>=2} |a_n| n^{-sigma} - 1,

with a_n the period-5 Davenport-Heilbronn pattern (1, kappa, -kappa, -1, 0).
For any sigma* with g(sigma*) < 0 decided, |f(s)| >= 1 - sum_{n>=2} |a_n|
n^{-sigma*} > 0 on Re s >= sigma*, so f has no zero there; the functional
equation F(s) = F(1-s) of the completed F(s) = (pi/5)^{-(s+1)/2}
Gamma((s+1)/2) f(s) reflects that into Re s <= 1 - sigma*.  All zeros of F
therefore lie in the strip 1 - sigma_0 < Re s < sigma_0 (the boundary lines
are excluded by an exact phase argument written in STRIP.md).  This feeds
WP2: every zero of H_0 = Xi_DH has |Im z| < Delta = sigma_0 - 1/2.

Identity used (verified numerically below before it is trusted in
intervals): splitting the sum over residue classes mod 5,

    sum_{n>=1} |a_n| n^{-s}
        = 5^{-s} [zeta(s, 1/5) + zeta(s, 4/5)]
        + kappa 5^{-s} [zeta(s, 2/5) + zeta(s, 3/5)],

because 5^{-s} zeta(s, c/5) = sum_{j>=0} (5j + c)^{-s} and |a_n| is 1 on
n = 1, 4 (mod 5), kappa on n = 2, 3 (mod 5), 0 on n = 0 (mod 5).  The n = 1
term of the right side is 1 (the j = 0 term of the c = 1 class), so
g(sigma) = (right side) - 2.

Backends:

* python-flint (Arb): acb Hurwitz zeta balls, bisection on exact dyadic
  endpoints to width < 1e-25 at 192 bits.  kappa enters as the Arb ball of
  the hunt instrument's linear solve (``instrument.kappa_ball``, 500 bits),
  never a remembered constant.
* mpmath.iv: the iv context has no Hurwitz zeta.  Each residue-class sum
  sum_{j>=0} (5j+c)^{-sigma} is a finite sum j < M plus an Euler-Maclaurin
  tail enclosure for sum_{j>=M} f(j), f(x) = (5x+c)^{-sigma}:

      integral_M^inf f + f(M)/2
        + sum_{j=1}^{K} B_{2j}/(2j)! (sigma)_{2j-1} 5^{2j-1} (5M+c)^{-sigma-2j+1}
        + R_K,

  with the remainder enclosed symmetrically by twice the magnitude of the
  first omitted correction term.  That remainder bound is the classical
  Euler-Maclaurin statement for integrands whose relevant derivative keeps
  one sign (DLMF 2.10(i); f here is completely monotone, every derivative
  of x^{-s} has constant sign), and it is not trusted on citation alone:
  ``check_em_tail`` requires the iv enclosure to CONTAIN an independent
  high-precision mpmath.mp Hurwitz zeta reference at a grid of points
  before the bisection runs.  The plain integral-test tail
  [0, N^{1-sigma}/(sigma-1) + N^{-sigma}] is an enclosure too, but its width
  N^{1-sigma}/(sigma-1) decays like N^{-0.395} near sigma_0, which cannot
  reach the 1e-15 target at any feasible N (about 1.7e-3 at N = 1e8); the
  Euler-Maclaurin form is the same integral-test skeleton with decidable
  correction terms and reaches ~1e-36 at M = 100.  kappa enters as the
  interval KAPPA_REF +/- 1e-39 with outward rounding, which the flint ball
  is checked to lie inside (so the iv input is an enclosure by the flint
  leg, exactly as in validate.py check 2).

Vocabulary per MISSION.md: decided values carry backend and precision;
float cross-checks are labeled measured.  Run from the repo root:

    .venv/bin/python hunts/lambda_dh_bounds/strip.py

Writes ``strip_results.json`` next to this file.  Intervals are serialized
as decimal strings with outward rounding, never as floats.
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
from flint import acb, arb, ctx, fmpq  # noqa: E402
from mpmath import bernfrac, iv, mp  # noqa: E402

import instrument as ins  # noqa: E402
from zeta.epstein import KAPPA_REF  # noqa: E402

OUT = os.path.join(HERE, "strip_results.json")

SCOUT = Fraction("1.39513615823511")   # scouted float value (14 decimals)
SCOUT_TOL = Fraction(1, 2 * 10 ** 14)  # half-ulp of the scout's last digit
BRACKET = (Fraction("1.39"), Fraction("1.40"))
FLINT_PREC = 192                        # bits, bisection evaluations
KAPPA_PREC = 500                        # bits, instrument.kappa_ball
FLINT_WIDTH = Fraction(1, 10 ** 25)
IV_DPS = 40
IV_WIDTH = Fraction(1, 10 ** 15)
IV_M = 100                              # finite terms per residue class
IV_K = 8                                # Euler-Maclaurin correction terms
TARGET = Fraction(4007, 10000)          # the Delta^2/2 comparison target


# ---------------------------------------------------------------------------
# exact decimal serialization with outward rounding
# ---------------------------------------------------------------------------


def _dec(q: Fraction, digits: int, mode: str) -> str:
    """Decimal string of q with ``digits`` places, rounded down or up."""
    scaled = q * 10 ** digits
    if mode == "down":
        m = scaled.numerator // scaled.denominator
    elif mode == "up":
        m = -((-scaled.numerator) // scaled.denominator)
    else:
        raise ValueError(mode)
    sign = "-" if m < 0 else ""
    s = str(abs(m)).rjust(digits + 1, "0")
    return sign + s[:-digits] + "." + s[-digits:]


def _out_interval(lo: Fraction, hi: Fraction, digits: int) -> list[str]:
    """[lo rounded down, hi rounded up]: the printed interval contains the
    exact rational one."""
    if lo > hi:
        raise ValueError("interval endpoints out of order")
    return [_dec(lo, digits, "down"), _dec(hi, digits, "up")]


def _arb_exact_frac(x: arb) -> Fraction:
    """Exact rational value of an exact (zero-radius) arb bound."""
    if float(x.rad()) != 0.0:
        raise ValueError("arb value is not exact")
    man, exp = x.man_exp()
    return Fraction(int(man)) * Fraction(2) ** int(exp)


def _arb_ball_fracs(x: arb, prec: int = 800) -> tuple[Fraction, Fraction]:
    """Exact rational [lower, upper] of an arb ball.

    Arb rounds the bounds outward at the ambient precision, so they are
    extracted under a high-precision guard (the default 53 bits would
    inflate a 1e-148 ball to width 5.6e-17; observed before this guard
    was added).
    """
    with ins._prec_guard(prec):
        return _arb_exact_frac(x.lower()), _arb_exact_frac(x.upper())


def _iv_fracs(x) -> tuple[Fraction, Fraction]:
    """Exact rational endpoints of an mpmath.iv value (bit-exact _mpi_)."""
    lo_t, hi_t = x._mpi_

    def q(t: tuple) -> Fraction:
        sign, man, exp, _bc = t
        if man == 0:
            return Fraction(0)
        out = Fraction(int(man)) * Fraction(2) ** int(exp)
        return -out if sign else out

    return q(lo_t), q(hi_t)


# ---------------------------------------------------------------------------
# g(sigma) on the flint backend: acb Hurwitz zeta balls
# ---------------------------------------------------------------------------


def g_ball(sigma_q: Fraction, kap: arb, prec: int) -> arb:
    """Arb ball enclosing g(sigma) = full |a_n|-sum via Hurwitz zeta, minus 2.

    Valid for sigma > 1 (absolute convergence; the bisection bracket stays
    inside (1, inf)).  The four Hurwitz values are computed as acb balls at
    real sigma; the true values are real, so the imaginary balls must
    contain 0 (checked) and the real parts are enclosures.
    """
    if sigma_q <= 1:
        raise ValueError("g_ball requires sigma > 1")
    with ins._prec_guard(prec):
        s_arb = arb(fmpq(sigma_q.numerator, sigma_q.denominator))
        s = acb(s_arb)
        h = []
        for c in (1, 2, 3, 4):
            z = s.zeta(acb(fmpq(c, 5)))
            if not z.imag.contains(arb(0)):
                raise ArithmeticError(
                    f"Hurwitz zeta({sigma_q}, {c}/5): imaginary ball "
                    "excludes 0; instrument fault")
            h.append(z.real)
        five = arb(5) ** (-s_arb)
        return five * (h[0] + h[3]) + kap * (five * (h[1] + h[2])) - 2


# ---------------------------------------------------------------------------
# g(sigma) on the mpmath.iv backend: progression sums + Euler-Maclaurin tail
# ---------------------------------------------------------------------------


def _iv_frac(q: Fraction):
    return iv.mpf(q.numerator) / iv.mpf(q.denominator)


def _em_tail_iv(sigma, c: int, M: int, K: int):
    """iv enclosure of sum_{j>=M} (5j+c)^{-sigma}, sigma > 1 an iv interval.

    Euler-Maclaurin for f(x) = (5x+c)^{-sigma} on [M, inf), with
    f^{(m)}(x) = (-1)^m (sigma)_m 5^m (5x+c)^{-sigma-m}:

        sum_{j>=M} f(j) = integral_M^inf f + f(M)/2
            - sum_{j=1}^{K} B_{2j}/(2j)! f^{(2j-1)}(M) + R_K
          = (5M+c)^{1-sigma} / (5 (sigma-1)) + (5M+c)^{-sigma} / 2
            + sum_{j=1}^{K} B_{2j}/(2j)! (sigma)_{2j-1} 5^{2j-1}
                            (5M+c)^{-sigma-2j+1} + R_K.

    |R_K| is at most the magnitude of the first omitted correction term
    when f^{(2K+2)} keeps one sign on [M, inf) (DLMF 2.10(i)); x^{-s} is
    completely monotone for s > 0, so that holds.  The remainder is
    enclosed here by TWICE that magnitude, symmetrically, and the whole
    formula is verified by containment against mpmath.mp references in
    ``check_em_tail`` before any decision uses it.
    """
    base = iv.mpf(5 * M + c)
    total = base ** (1 - sigma) / (5 * (sigma - 1)) + base ** (-sigma) / 2
    poch = iv.mpf(1)   # running (sigma)_m
    m = 0
    for j in range(1, K + 1):
        while m < 2 * j - 1:
            poch = poch * (sigma + m)
            m += 1
        p, qd = bernfrac(2 * j)
        term = ((iv.mpf(int(p)) / iv.mpf(int(qd)))
                / iv.mpf(math.factorial(2 * j))
                * poch * iv.mpf(5) ** (2 * j - 1)
                * base ** (-sigma - (2 * j - 1)))
        total = total + term
    while m < 2 * K + 1:
        poch = poch * (sigma + m)
        m += 1
    p, qd = bernfrac(2 * K + 2)
    bmag = (abs(iv.mpf(int(p)) / iv.mpf(int(qd)))
            / iv.mpf(math.factorial(2 * K + 2))
            * poch * iv.mpf(5) ** (2 * K + 1)
            * base ** (-sigma - (2 * K + 1)))
    return total + iv.mpf([-1, 1]) * (2 * bmag)


def _class_sum_iv(sigma, c: int, M: int, K: int):
    """iv enclosure of sum_{j>=0} (5j+c)^{-sigma} = 5^{-sigma} zeta(sigma, c/5)."""
    s = iv.mpf(0)
    for j in range(M):
        s = s + iv.mpf(5 * j + c) ** (-sigma)
    return s + _em_tail_iv(sigma, c, M, K)


def g_iv(sigma_q: Fraction, kap_iv, M: int = IV_M, K: int = IV_K):
    """iv enclosure of g(sigma), sigma an exact rational > 1."""
    if sigma_q <= 1:
        raise ValueError("g_iv requires sigma > 1")
    sigma = _iv_frac(sigma_q)
    S = {c: _class_sum_iv(sigma, c, M, K) for c in (1, 2, 3, 4)}
    return (S[1] + S[4]) + kap_iv * (S[2] + S[3]) - 2


# ---------------------------------------------------------------------------
# bisection on exact dyadic endpoints, sign decided or refused
# ---------------------------------------------------------------------------


def _sign_arb(v: arb) -> int:
    if v > 0:
        return 1
    if v < 0:
        return -1
    return 0


def _sign_iv(v) -> int:
    if v.a > 0:
        return 1
    if v.b < 0:
        return -1
    return 0


def bisect_root(evalf, signf, lo: Fraction, hi: Fraction,
                width: Fraction) -> tuple[Fraction, Fraction, int]:
    """Bisect the decreasing g to a bracket of width < ``width``.

    Endpoints stay exact rationals; every sign is decided by an enclosure
    that excludes 0, and an undecided sign aborts loudly (never a guess).
    """
    n_evals = 0
    s_lo = signf(evalf(lo)); n_evals += 1
    s_hi = signf(evalf(hi)); n_evals += 1
    if s_lo != 1 or s_hi != -1:
        raise ArithmeticError(
            f"bracket not decided: sign(g({lo})) = {s_lo}, "
            f"sign(g({hi})) = {s_hi}")
    while hi - lo >= width:
        mid = (lo + hi) / 2
        s = signf(evalf(mid)); n_evals += 1
        if s == 1:
            lo = mid
        elif s == -1:
            hi = mid
        else:
            raise ArithmeticError(
                f"sign of g({mid}) undecided at bracket width "
                f"{float(hi - lo):.3e}; raise precision")
    return lo, hi, n_evals


# ---------------------------------------------------------------------------
# cross-checks run before anything is decided
# ---------------------------------------------------------------------------


def check_identity(kap_float: float, g_flint) -> dict:
    """Measured cross-check of the Hurwitz-zeta identity.

    Direct float64 sum of |a_n| n^{-sigma} over n <= N versus the
    Hurwitz-form full sum (g + 2, flint midpoint).  The difference must be
    positive (the discarded tail) and below the integral-test tail bound
    N^{1-sigma}/(sigma-1) plus a float round-off allowance.  A wrong
    residue-class split or a wrong n = 1 accounting would miss by O(1).
    """
    N = 10 ** 6
    n = np.arange(1, N + 1, dtype=np.float64)
    r = np.arange(1, N + 1) % 5
    coef = np.zeros(N)
    coef[r == 1] = 1.0
    coef[r == 4] = 1.0
    coef[r == 2] = kap_float
    coef[r == 3] = kap_float
    rows = []
    all_ok = True
    for sig_s in ("1.5", "2", "3"):
        sig_q = Fraction(sig_s)
        sig_f = float(sig_q)
        direct = float(np.sum(coef * n ** (-sig_f)))
        full_mid = float((g_flint(sig_q) + 2).mid())
        diff = full_mid - direct
        tail_bound = N ** (1.0 - sig_f) / (sig_f - 1.0)
        ok = bool(0.0 < diff < tail_bound * 1.001 + 1e-9)
        all_ok = all_ok and ok
        rows.append({
            "sigma": sig_s,
            "direct_float_sum_N": N,
            "direct_float_sum": direct,
            "hurwitz_full_sum_mid": full_mid,
            "difference": diff,
            "integral_test_tail_bound": tail_bound,
            "grade": "measured (float64 direct sum vs flint midpoint)",
            "ok": ok,
        })
        print(f"  identity sigma={sig_s}: diff={diff:.3e} "
              f"in (0, {tail_bound:.3e}]: {ok}", flush=True)
    return {"all_ok": all_ok, "rows": rows}


def check_em_tail(kap_iv) -> dict:
    """Containment check for the iv Euler-Maclaurin class sums.

    The iv enclosure of 5^{-sigma} zeta(sigma, c/5) must contain an
    independent mpmath.mp reference at dps 60 (allowance 1e-50 for the
    reference's own rounding), for every residue class and a sigma grid
    spanning the bracket and the coarse point sigma = 2.
    """
    rows = []
    all_ok = True
    for sig_s in ("6/5", "1.3951361582", "1.4", "2", "3"):
        sig_q = Fraction(sig_s)
        sigma = _iv_frac(sig_q)
        for c in (1, 2, 3, 4):
            enc = _class_sum_iv(sigma, c, IV_M, IV_K)
            lo_q, hi_q = _iv_fracs(enc)
            with mp.workdps(60):
                ref = (mp.power(5, -mp.mpf(sig_q.numerator) / sig_q.denominator)
                       * mp.zeta(mp.mpf(sig_q.numerator) / sig_q.denominator,
                                 mp.mpf(c) / 5))
                cushion = mp.mpf(10) ** (-50)
                lo_m = mp.mpf(lo_q.numerator) / lo_q.denominator
                hi_m = mp.mpf(hi_q.numerator) / hi_q.denominator
                ok = bool(lo_m - cushion <= ref <= hi_m + cushion)
            all_ok = all_ok and ok
            rows.append({
                "sigma": sig_s, "class": c,
                "enclosure_width": float(hi_q - lo_q),
                "mp_reference_dps": 60,
                "contained": ok,
            })
    print(f"  em tail containment: {sum(r['contained'] for r in rows)}"
          f"/{len(rows)} contained", flush=True)
    return {"all_contained": all_ok, "n_points": len(rows), "rows": rows}


# ---------------------------------------------------------------------------


def main() -> None:
    t_start = time.perf_counter()
    timings: dict[str, float] = {}

    # kappa: the honest way, the instrument's Arb linear solve
    t0 = time.perf_counter()
    kap = ins.kappa_ball(KAPPA_PREC)
    timings["kappa_ball_s"] = round(time.perf_counter() - t0, 3)
    kap_lo, kap_hi = _arb_ball_fracs(kap)
    ref_q = Fraction(KAPPA_REF)
    eps39 = Fraction(1, 10 ** 39)
    kappa_inside_ref = bool(ref_q - eps39 <= kap_lo and kap_hi <= ref_q + eps39)
    print(f"kappa ball (flint, {KAPPA_PREC} bits): width "
          f"{float(kap_hi - kap_lo):.3e}, inside KAPPA_REF +/- 1e-39: "
          f"{kappa_inside_ref}", flush=True)
    if not kappa_inside_ref:
        raise SystemExit("kappa ball escaped KAPPA_REF +/- 1e-39")

    # iv kappa input: the decimal interval the flint ball was just decided
    # to lie inside (outward by construction)
    iv.dps = IV_DPS
    kap_iv = (_iv_frac(ref_q) + _iv_frac(eps39) * iv.mpf([-1, 1]))

    def g_flint(sq: Fraction) -> arb:
        return g_ball(sq, kap, FLINT_PREC)

    def g_ivb(sq: Fraction):
        return g_iv(sq, kap_iv)

    # cross-checks before deciding anything
    print("[1/4] Hurwitz identity vs direct float sum (measured)", flush=True)
    t0 = time.perf_counter()
    identity = check_identity(float(kap.mid()), g_flint)
    timings["identity_check_s"] = round(time.perf_counter() - t0, 3)
    if not identity["all_ok"]:
        raise SystemExit("Hurwitz identity cross-check failed")

    print("[2/4] iv Euler-Maclaurin tail containment vs mpmath.mp", flush=True)
    t0 = time.perf_counter()
    em_check = check_em_tail(kap_iv)
    timings["em_tail_check_s"] = round(time.perf_counter() - t0, 3)
    if not em_check["all_contained"]:
        raise SystemExit("iv Euler-Maclaurin containment check failed")

    # bisections
    print("[3/4] bisection, python-flint (Arb), 192 bits, width < 1e-25",
          flush=True)
    t0 = time.perf_counter()
    f_lo, f_hi, f_evals = bisect_root(g_flint, _sign_arb, *BRACKET,
                                      FLINT_WIDTH)
    timings["flint_bisect_s"] = round(time.perf_counter() - t0, 3)
    print(f"  sigma_0 in [{_dec(f_lo, 28, 'down')}, {_dec(f_hi, 28, 'up')}] "
          f"({f_evals} sign decisions)", flush=True)

    print("[4/4] bisection, mpmath.iv, dps 40, width < 1e-15", flush=True)
    t0 = time.perf_counter()
    i_lo, i_hi, i_evals = bisect_root(g_ivb, _sign_iv, *BRACKET, IV_WIDTH)
    timings["iv_bisect_s"] = round(time.perf_counter() - t0, 3)
    print(f"  sigma_0 in [{_dec(i_lo, 18, 'down')}, {_dec(i_hi, 18, 'up')}] "
          f"({i_evals} sign decisions)", flush=True)

    # agreement requirements.  The scout is a 14-decimal-place rounding, so
    # the decided interval (width 1e-25) cannot contain the rounded string
    # itself; the correct containment runs the other way: the decided
    # interval must lie inside scout +/- half an ulp of its last digit.
    overlap = bool(max(f_lo, i_lo) <= min(f_hi, i_hi))
    scout_in_flint = bool(SCOUT - SCOUT_TOL <= f_lo and f_hi <= SCOUT + SCOUT_TOL)
    scout_in_iv = bool(SCOUT - SCOUT_TOL <= i_lo and i_hi <= SCOUT + SCOUT_TOL)
    print(f"backend intervals overlap: {overlap}; decided intervals inside "
          f"scout +/- 5e-15: flint {scout_in_flint}, iv {scout_in_iv}",
          flush=True)
    if not (overlap and scout_in_flint and scout_in_iv):
        raise SystemExit("backend agreement or scout containment failed")

    # coarse in-tree strip: g(2) < 0 on both backends
    g2_f = g_flint(Fraction(2))
    g2_f_lo, g2_f_hi = _arb_ball_fracs(g2_f)
    g2_i_lo, g2_i_hi = _iv_fracs(g_ivb(Fraction(2)))
    g2_neg_flint = bool(g2_f_hi < 0)
    g2_neg_iv = bool(g2_i_hi < 0)
    print(f"g(2) < 0 decided: flint {g2_neg_flint}, iv {g2_neg_iv} "
          f"(mid ~ {float((g2_f_lo + g2_f_hi) / 2):.6f})", flush=True)
    if not (g2_neg_flint and g2_neg_iv):
        raise SystemExit("g(2) < 0 not decided")

    # Delta and Delta^2/2, exact rational arithmetic on the endpoints
    half = Fraction(1, 2)
    d_f = (f_lo - half, f_hi - half)
    d_i = (i_lo - half, i_hi - half)
    dsq_f = (d_f[0] ** 2 / 2, d_f[1] ** 2 / 2)   # monotone: 0 < d
    dsq_i = (d_i[0] ** 2 / 2, d_i[1] ** 2 / 2)
    lt_target_flint = bool(dsq_f[1] < TARGET)
    lt_target_iv = bool(dsq_i[1] < TARGET)
    print(f"Delta^2/2 < 0.4007 decided: flint {lt_target_flint}, "
          f"iv {lt_target_iv}", flush=True)
    if not (lt_target_flint and lt_target_iv):
        raise SystemExit("Delta^2/2 < 0.4007 not decided")

    timings["total_s"] = round(time.perf_counter() - t_start, 3)

    out = {
        "instrument": "hunts/lambda_dh_bounds/strip.py",
        "quantity": "sigma_0: unique root > 1 of "
                    "sum_{n>=2} |a_n| n^{-sigma} = 1 for the "
                    "Davenport-Heilbronn coefficients (1, kappa, -kappa, "
                    "-1, 0); all zeros of the completed F lie in "
                    "1 - sigma_0 < Re s < sigma_0 (argument in STRIP.md)",
        "interval_convention": "decimal strings, outward rounding: printed "
                               "intervals contain the exact rational "
                               "bisection endpoints",
        "sigma0": {
            "flint": _out_interval(f_lo, f_hi, 28),
            "iv": _out_interval(i_lo, i_hi, 18),
        },
        "delta": {
            "definition": "Delta = sigma_0 - 1/2 (zeros of Xi_DH satisfy "
                          "|Im z| < Delta)",
            "flint": _out_interval(*d_f, 28),
            "iv": _out_interval(*d_i, 18),
        },
        "upper_bound_delta_sq_over_2": {
            "flint": _out_interval(*dsq_f, 28),
            "iv": _out_interval(*dsq_i, 18),
            "decided_lt_0.4007": {"flint": lt_target_flint,
                                  "iv": lt_target_iv},
            "comparison": "exact rational comparison of the outward upper "
                          "endpoint against 4007/10000",
        },
        "kappa_ball": {
            "backend": "python-flint (Arb), linear solve of "
                       "instrument.kappa_ball, prec 500 bits",
            "interval": _out_interval(kap_lo, kap_hi, 45),
            "inside_KAPPA_REF_pm_1e-39": kappa_inside_ref,
            "iv_input": "KAPPA_REF +/- 1e-39 (an enclosure because the "
                        "flint ball lies inside it; exact rational check)",
        },
        "coarse_strip_g2": {
            "statement": "g(2) < 0 decided on both backends; hence f has "
                         "no zero in Re s >= 2 and, by the functional "
                         "equation, F none in Re s <= -1: the in-tree "
                         "coarse strip -1 < Re s < 2 of zeta/epstein.py",
            "flint": _out_interval(g2_f_lo, g2_f_hi, 28),
            "iv": _out_interval(g2_i_lo, g2_i_hi, 18),
            "decided_negative": {"flint": g2_neg_flint, "iv": g2_neg_iv},
        },
        "agreement": {
            "backend_intervals_overlap": overlap,
            "scout_value": "1.39513615823511",
            "scout_note": "the scout is a 14-decimal rounding; the check is "
                          "that each decided interval lies inside scout +/- "
                          "5e-15 (half an ulp of its last digit)",
            "decided_inside_scout_pm_5e-15": {"flint": scout_in_flint,
                                              "iv": scout_in_iv},
        },
        "identity_check": identity,
        "em_tail_check": {
            "all_contained": em_check["all_contained"],
            "n_points": em_check["n_points"],
            "note": "full rows omitted from disk only for size; rerun "
                    "check_em_tail to reproduce",
        },
        "precisions": {
            "flint_bisection_bits": FLINT_PREC,
            "flint_kappa_bits": KAPPA_PREC,
            "iv_dps": IV_DPS,
            "iv_finite_terms_per_class": IV_M,
            "iv_euler_maclaurin_terms": IV_K,
            "flint_width_target": "1e-25",
            "iv_width_target": "1e-15",
            "sign_decisions": {"flint": f_evals, "iv": i_evals},
        },
        "timings": timings,
    }
    with open(OUT, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=2)
        f.write("\n")
    print(f"\nwrote {OUT}  ({timings['total_s']}s)", flush=True)


if __name__ == "__main__":
    main()
