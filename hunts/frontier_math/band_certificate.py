"""A finite rational certificate for the paper-field band-dual verdict.

WHAT THIS MODULE IS.  :mod:`paper_chain` (float) and :mod:`hardened_paper`
(arb/acb balls) both reach the same per-depth verdict at the paper field
Phi2(z) = s(z + sqrt2) + s(z - sqrt2), s(u) = sin(u/2)/u:

    cap(theta, y) <= slack(y)   at theta = 995/1000,
    for y in {1/50, 1/10, 3/10, 49/100}.

This module re-expresses that verdict as a FINITE CERTIFICATE: a list of
cells with rational endpoints plus a handful of rational scalars, such that
a checker needing only exact rational arithmetic and elementary Taylor
enclosures of sin/cos/sinh/cosh can re-derive every inequality.  The shape
is the one Lean 4 formalizations use for computational steps (the
zeta-23-lean LawN256 pattern: integer/rational enclosures recorded as
data, everything downstream checked by decide/norm_num).  The Lean draft
statement lives in the operator's PROBLEM.md; this file is the working
instrument and its own auditor.

THE CERTIFICATE, PER DEPTH y (exact rational):

* ``G`` — the resolved region (0, G], here G = 98, chosen mid-gap so no
  band straddles it.  Beyond G the closed-form tail majorant takes over.
* ``neg_segments`` — lists of strictly increasing rational boundaries;
  consecutive pairs are cells on which the checker must find that the
  damage-field enclosure has a nonpositive upper endpoint: f <= 0
  THROUGHOUT the cell, where f = -2 W = 4 (Im^2 - Re^2) Phi2(g+iy) / A^2.
  These cells and the band intervals must exactly tile (0, G], so "no band
  hides between cells" is a property of the cover, not an inference.
* ``bands`` — records (lo, hi, n_cells, F_up, K_lo, B_up):
  - F_up   is an UPPER bound for max f over the band: the checker splits
    [lo, hi] into n_cells equal cells and demands cell-enclosure upper
    endpoints <= F_up (an interval-argument enclosure covers the
    continuum, so no separate slope margin is owed);
  - K_lo   is a LOWER bound for the same-band repulsion charge
    min_{[0, hi-lo]} omega^2, omega = Re Phi2 / A, justified against the
    shared ``omega_cover`` (uniform rational cells on [0, w_max]);
  - B_up   is an UPPER bound for the square completion
    max_m [m F - c m (m-1) K] <= (F + cK)^2 / (4cK) (or F when
    F <= 2cK), c = 1 - theta, exact in Q.
* ``sigma2_lo`` <= sigma^2(y) = (Phi2(2iy) - A) / (2A)  (DOWN), whence
  ``slack_lo`` = 8 sigma2_lo + 8 sigma2_lo^2 <= slack(y)  (DOWN).
* ``C_up``   >= C_im(y)/A  (UP), the 1/g Im-majorant constant, with
  C_im = 2 edge sinh(y/2) + TV sinh(y/2) + y cosh(y/2) A,
  edge = cos(sqrt2/2), TV = 2(1 - edge)  (paper_chain.c_im_sharp).
* ``P_lo``   <= every recorded inter-band gap  (DOWN).
* ``tail2_up`` >= 8 C_up^2 (1/G^2 + 1/(P_lo G))  (UP) — the two-sided
  closed-form majorant of the band sum beyond G at single occupancy.
* ``cap_up`` >= 2 * sum_i B_up_i + tail2_up  (UP), and
  ``margin_lo`` <= slack_lo - cap_up, with margin_lo >= 0 the verdict.

EVERY DIRECTION IS ONE-SIDED IN THE ADVERSARY'S FAVOUR: anything entering
the cap rounds UP, anything entering the slack rounds DOWN, and the
square-completion bound dominates the integer maximum for any F' >= F,
K' <= K, so recording slop can only weaken the conclusion, never
manufacture it.  (The word this repo reserves for zeta/rigor.py is not
used here: the certificate is *checked*, in the sense of the finite list
of inequalities above, and nothing more.)

THE CHECKER'S ANALYTIC LEAVES (Part 1, pure rational — imports nothing
numerical beyond ``fractions`` and ``math.isqrt``):

1. sin/cos on a point: Taylor to N = 26 pair-terms with the Lagrange
   remainder |R| <= |m|^(2N+1)/(2N+1)! (every derivative of sin/cos is
   bounded by 1), valid for the asserted range |m| <= 4.  The leftover
   Taylor term computed by the loop IS an enclosure of that remainder
   magnitude, so the bound is read off the loop state (+ ulp guards).
2. sin/cos on an interval: enclosure at the midpoint widened by the
   half-width — the Lipschitz fact |sin'| <= 1, |cos'| <= 1.
3. Argument reduction: sin(x) = sin(x - 2 pi k) with integer k chosen by
   nearest-integer division against a 2 pi enclosure; the reduced
   argument's containment in (-4, 4) is ASSERTED, never assumed.  The
   2 pi enclosure comes from Machin's formula (16 atan 1/5 - 4 atan 1/239,
   alternating series with the first-omitted-term tail bound).
4. sinh/cosh on [-1, 1]: same Taylor scheme, tail <= 2 * first dropped
   term (term ratio < 1/2 there), interval widening by 2 * half-width
   (|cosh|, |sinh| <= 2 on [-1, 1]).
5. sqrt2 from math.isqrt: n = isqrt(2 * 4^S) gives n/2^S <= sqrt2 <=
   (n+1)/2^S exactly.
6. s(u) near its removable singularity (|u| <= 1, entered whenever the
   cell puts z - sqrt2 near 0): the even series
   s(u) = sum_n (-1)^n u^(2n) / (2 * 4^n (2n+1)!), 12 terms, tail
   <= 2 / (2 * 4^12 * 25!)  (term ratio <= 1/24 for |u| <= 1).  This is
   the same branch hardened_paper uses, in rational form.

All interval arithmetic is integer fixed-point at scale 2^128 with
directed rounding (lo floors, hi ceils) — every interval is a pair of
integers, i.e. a pair of rationals with denominator 2^128, and the whole
check is a finite sequence of integer comparisons: exactly the shape a
Lean ``decide``/``norm_num`` layer consumes.

STRUCTURAL LEAVES CARRIED FROM THE PARENT INSTRUMENTS (named, not
hidden — the checker cannot and does not establish these):

* the tail lemma |Im Phi2(g+iy)| <= C_im(y)/|g| (one integration by
  parts; paper_chain.c_im_sharp's derivation),
* bands beyond G spaced >= P_lo and with repulsion >= K_min (measured in
  the resolved region, extrapolated beyond it, as in
  hardened_paper.period_lo — the certificate makes the extrapolation
  explicit instead of implicit),
* the band-dual inequality itself (cap bounds the single-pair adversary;
  the transplant-lemma layer above this certificate).

Nothing here computes a proportion and nothing here is evidence about RH.

Run:
    .venv/bin/python hunts/frontier_math/band_certificate.py              # audit
    .venv/bin/python hunts/frontier_math/band_certificate.py --generate   # rebuild JSON
    .venv/bin/python hunts/frontier_math/band_certificate.py --check-only # pure-rational path
"""

from __future__ import annotations

import json
import sys
from fractions import Fraction
from math import isqrt
from pathlib import Path

_HERE = Path(__file__).resolve().parent
CERT_PATH = _HERE / "data_band_certificate.json"

# ===========================================================================
# PART 1 — THE CHECKER.  Pure rational: integers, Fraction, math.isqrt.
# Nothing below this line up to PART 2 may touch a float, numpy, mpmath or
# flint; ``--check-only`` runs only this part and reports what was imported.
# ===========================================================================

S = 128
ONE = 1 << S

# -- directed fixed-point interval primitives -------------------------------


def _shr_floor(p: int) -> int:
    return p >> S                       # arithmetic shift floors negatives too


def _shr_ceil(p: int) -> int:
    return -((-p) >> S)


def iv_add(a, b):
    return a[0] + b[0], a[1] + b[1]


def iv_sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def iv_mul(a, b):
    p1, p2 = a[0] * b[0], a[0] * b[1]
    p3, p4 = a[1] * b[0], a[1] * b[1]
    return _shr_floor(min(p1, p2, p3, p4)), _shr_ceil(max(p1, p2, p3, p4))


def iv_sqr(a):
    lo, hi = a
    if lo >= 0:
        return _shr_floor(lo * lo), _shr_ceil(hi * hi)
    if hi <= 0:
        return _shr_floor(hi * hi), _shr_ceil(lo * lo)
    return 0, _shr_ceil(max(lo * lo, hi * hi))


def iv_scale(a, k: int):
    """Multiply by an exact integer (no rounding)."""
    return (a[0] * k, a[1] * k) if k >= 0 else (a[1] * k, a[0] * k)


def _div_floor(x: int, y: int) -> int:
    return (x << S) // y


def _div_ceil(x: int, y: int) -> int:
    return -(((-x) << S) // y)


def iv_div(a, b):
    """a / b for an interval b with b_lo > 0 (asserted)."""
    if b[0] <= 0:
        raise CheckFailure("interval denominator not strictly positive")
    lo = min(_div_floor(a[0], b[0]), _div_floor(a[0], b[1]),
             _div_floor(a[1], b[0]), _div_floor(a[1], b[1]))
    hi = max(_div_ceil(a[0], b[0]), _div_ceil(a[0], b[1]),
             _div_ceil(a[1], b[0]), _div_ceil(a[1], b[1]))
    return lo, hi


def iv_div_int(a, d: int):
    """a / d for an exact positive integer d."""
    return a[0] // d, -((-a[1]) // d)


def _half(a):
    return a[0] >> 1, -((-a[1]) >> 1)


def fp_lo(fr: Fraction) -> int:
    return (fr.numerator << S) // fr.denominator


def fp_hi(fr: Fraction) -> int:
    return -(((-fr.numerator) << S) // fr.denominator)


def fp_iv(fr: Fraction):
    return fp_lo(fr), fp_hi(fr)


def iv_lo_fr(a) -> Fraction:
    return Fraction(a[0], ONE)


def iv_hi_fr(a) -> Fraction:
    return Fraction(a[1], ONE)


class CheckFailure(AssertionError):
    """A certificate inequality that did not hold under re-derivation."""


# -- constants: sqrt2 by isqrt, 2 pi by Machin ------------------------------

_n_s2 = isqrt(2 << (2 * S))
SQRT2 = (_n_s2, _n_s2 + 1)


def _atan_inv(m: int, bits: int):
    """Interval for arctan(1/m) at scale 2^bits (alternating series; the
    tail after a term of magnitude <= 1 ulp is below the next term)."""
    one = 1 << bits
    acc_lo = acc_hi = 0
    j, sign = 0, 1
    while True:
        den = (2 * j + 1) * m ** (2 * j + 1)
        t_f, t_c = one // den, -((-one) // den)
        if sign > 0:
            acc_lo += t_f
            acc_hi += t_c
        else:
            acc_lo -= t_c
            acc_hi -= t_f
        if t_c <= 1:
            return acc_lo - 2, acc_hi + 2
        j += 1
        sign = -sign


_G_BITS = S + 32
_a5 = _atan_inv(5, _G_BITS)
_a239 = _atan_inv(239, _G_BITS)
_pi_g = (16 * _a5[0] - 4 * _a239[1], 16 * _a5[1] - 4 * _a239[0])
PI2 = ((2 * _pi_g[0]) >> 32, -((-(2 * _pi_g[1])) >> 32))

# -- elementary enclosures --------------------------------------------------

N_SIN = 26      # Lagrange remainder |m|^53/53! < 1e-42 at |m| = 3.3
N_SH = 14       # cosh/sinh tail at |m| <= 1: invisible at scale 2^-128


def sin_point(m: int):
    """Enclosure of sin(m/2^S), |m/2^S| <= 4 asserted (leaf 1)."""
    if not -4 * ONE <= m <= 4 * ONE:
        raise CheckFailure("sin argument left (-4, 4) after reduction")
    m2 = iv_sqr((m, m))
    t, s_lo, s_hi, sign = (m, m), 0, 0, 1
    for k in range(N_SIN):
        if sign > 0:
            s_lo += t[0]
            s_hi += t[1]
        else:
            s_lo -= t[1]
            s_hi -= t[0]
        t = iv_div_int(iv_mul(t, m2), (2 * k + 2) * (2 * k + 3))
        sign = -sign
    r = max(abs(t[0]), abs(t[1])) + 4
    return s_lo - r, s_hi + r


def cos_point(m: int):
    if not -4 * ONE <= m <= 4 * ONE:
        raise CheckFailure("cos argument left (-4, 4) after reduction")
    m2 = iv_sqr((m, m))
    t, s_lo, s_hi, sign = (ONE, ONE), 0, 0, 1
    for k in range(N_SIN):
        if sign > 0:
            s_lo += t[0]
            s_hi += t[1]
        else:
            s_lo -= t[1]
            s_hi -= t[0]
        t = iv_div_int(iv_mul(t, m2), (2 * k + 1) * (2 * k + 2))
        sign = -sign
    r = max(abs(t[0]), abs(t[1])) + 4
    return s_lo - r, s_hi + r


def sinh_point(m: int):
    """Enclosure of sinh(m/2^S), |m/2^S| <= 1 asserted (leaf 4)."""
    if not -ONE <= m <= ONE:
        raise CheckFailure("sinh argument left [-1, 1]")
    m2 = iv_sqr((m, m))
    t, s_lo, s_hi = (m, m), 0, 0
    for k in range(N_SH):
        s_lo += t[0]
        s_hi += t[1]
        t = iv_div_int(iv_mul(t, m2), (2 * k + 2) * (2 * k + 3))
    r = 2 * max(abs(t[0]), abs(t[1])) + 4
    return s_lo - r, s_hi + r


def cosh_point(m: int):
    if not -ONE <= m <= ONE:
        raise CheckFailure("cosh argument left [-1, 1]")
    m2 = iv_sqr((m, m))
    t, s_lo, s_hi = (ONE, ONE), 0, 0
    for k in range(N_SH):
        s_lo += t[0]
        s_hi += t[1]
        t = iv_div_int(iv_mul(t, m2), (2 * k + 1) * (2 * k + 2))
    r = 2 * max(abs(t[0]), abs(t[1])) + 4
    return s_lo - r, s_hi + r


def _reduce(a):
    """Shift by an integer multiple of the 2 pi enclosure (leaf 3)."""
    mid = (a[0] + a[1]) >> 1
    p2m = (PI2[0] + PI2[1]) >> 1
    k = (2 * mid + p2m) // (2 * p2m)
    if k == 0:
        return a
    if k > 0:
        return a[0] - k * PI2[1], a[1] - k * PI2[0]
    return a[0] - k * PI2[0], a[1] - k * PI2[1]


def sin_iv(a):
    """sin over an interval: midpoint enclosure widened by the half-width
    (|sin'| <= 1, leaf 2)."""
    red = _reduce(a)
    m = (red[0] + red[1]) >> 1
    r = ((red[1] - red[0] + 1) >> 1) + 1
    base = sin_point(m)
    return base[0] - r, base[1] + r


def cos_iv(a):
    red = _reduce(a)
    m = (red[0] + red[1]) >> 1
    r = ((red[1] - red[0] + 1) >> 1) + 1
    base = cos_point(m)
    return base[0] - r, base[1] + r


def sinh_iv(a):
    m = (a[0] + a[1]) >> 1
    r = ((a[1] - a[0] + 1) >> 1) + 1
    base = sinh_point(m)
    return base[0] - 2 * r, base[1] + 2 * r


def cosh_iv(a):
    m = (a[0] + a[1]) >> 1
    r = ((a[1] - a[0] + 1) >> 1) + 1
    base = cosh_point(m)
    return base[0] - 2 * r, base[1] + 2 * r


# -- s(u) = sin(u/2)/u as a complex interval, two branches ------------------

N_SER = 12
_SER_DENS = []
for _n in range(N_SER + 1):
    _f = 1
    for _i in range(1, 2 * _n + 2):
        _f *= _i
    _SER_DENS.append(2 * 4 ** _n * _f)     # d_n = 2 * 4^n * (2n+1)!


def _cmul(a, b):
    re = iv_sub(iv_mul(a[0], b[0]), iv_mul(a[1], b[1]))
    im = iv_add(iv_mul(a[0], b[1]), iv_mul(a[1], b[0]))
    return re, im


def s_eval(X, Y):
    """Complex enclosure of s(u) = sin(u/2)/u on the box X + iY.

    Series branch (leaf 6) whenever the |u|^2 enclosure stays <= 1; else
    the closed form sin(u/2) * conj(u) / |u|^2 with sin(a+bi) =
    sin a cosh b + i cos a sinh b, |u|^2 bounded away from 0 (asserted).
    """
    n2 = iv_add(iv_sqr(X), iv_sqr(Y))
    if n2[1] <= ONE:
        u2 = (iv_sub(iv_sqr(X), iv_sqr(Y)), iv_scale(iv_mul(X, Y), 2))
        t = ((ONE, ONE), (0, 0))
        acc_re, acc_im, sign = (0, 0), (0, 0), 1
        for n in range(N_SER):
            tr = iv_div_int(t[0], _SER_DENS[n])
            ti = iv_div_int(t[1], _SER_DENS[n])
            if sign > 0:
                acc_re, acc_im = iv_add(acc_re, tr), iv_add(acc_im, ti)
            else:
                acc_re, acc_im = iv_sub(acc_re, tr), iv_sub(acc_im, ti)
            t = _cmul(t, u2)
            sign = -sign
        rem = (2 * ONE) // _SER_DENS[N_SER] + 4
        return ((acc_re[0] - rem, acc_re[1] + rem),
                (acc_im[0] - rem, acc_im[1] + rem))
    hx, hy = _half(X), _half(Y)
    wr = iv_mul(sin_iv(hx), cosh_iv(hy))
    wi = iv_mul(cos_iv(hx), sinh_iv(hy))
    num_re = iv_add(iv_mul(wr, X), iv_mul(wi, Y))
    num_im = iv_sub(iv_mul(wi, X), iv_mul(wr, Y))
    return iv_div(num_re, n2), iv_div(num_im, n2)


def phi2_eval(X, Y):
    """Enclosure of Phi2 = s(z + sqrt2) + s(z - sqrt2) on the box X + iY."""
    r1, i1 = s_eval(iv_add(X, SQRT2), Y)
    r2, i2 = s_eval(iv_sub(X, SQRT2), Y)
    return iv_add(r1, r2), iv_add(i1, i2)


A_IV = phi2_eval((0, 0), (0, 0))[0]        # A = Phi2(0), width ~2e-37
A2_IV = iv_sqr(A_IV)

# -- the certificate-facing quantities --------------------------------------


def f_cell(lo: Fraction, hi: Fraction, y: Fraction):
    """Enclosure of f = -2W = 4 (Im^2 - Re^2)/A^2 on [lo, hi] x {y}."""
    Re, Im = phi2_eval((fp_lo(lo), fp_hi(hi)), fp_iv(y))
    q = iv_sub(iv_sqr(Re), iv_sqr(Im))
    return iv_div(iv_scale(q, -4), A2_IV)


def f_upper_cell(lo: Fraction, hi: Fraction, y: Fraction) -> Fraction:
    return iv_hi_fr(f_cell(lo, hi, y))


def omega_lower_cell(lo: Fraction, hi: Fraction) -> Fraction:
    """Lower endpoint of omega = Re Phi2 / A on [lo, hi] x {0}."""
    Re, _ = phi2_eval((fp_lo(lo), fp_hi(hi)), (0, 0))
    return iv_lo_fr(iv_div(Re, A_IV))


def sigma2_lower(y: Fraction) -> Fraction:
    """Lower endpoint of sigma^2 = (Phi2(2iy) - A) / (2A)."""
    Re, _ = phi2_eval((0, 0), fp_iv(2 * y))
    return iv_lo_fr(iv_div(iv_sub(Re, A_IV), iv_scale(A_IV, 2)))


def c_over_a_upper(y: Fraction) -> Fraction:
    """Upper endpoint of C_im(y)/A (paper_chain.c_im_sharp / A)."""
    edge = cos_iv(_half(SQRT2))
    hy = fp_iv(y / 2)
    sh, ch = sinh_iv(hy), cosh_iv(hy)
    tv = iv_sub((2 * ONE, 2 * ONE), iv_scale(edge, 2))
    c_im = iv_add(iv_add(iv_mul(iv_scale(edge, 2), sh), iv_mul(tv, sh)),
                  iv_mul(iv_mul(fp_iv(y), ch), A_IV))
    return iv_hi_fr(iv_div(c_im, A_IV))


def l1_upper() -> Fraction:
    """Upper endpoint of L1 = sin(sqrt2/2)/sqrt2 + cos(sqrt2/2) - 1, the
    closed form of int |t| phi^2 dt (recorded for the Lean statement's
    optional Lipschitz lemma; the cell bounds above do not use it)."""
    h = _half(SQRT2)
    v = iv_add(iv_div(sin_iv(h), SQRT2), cos_iv(h))
    return iv_hi_fr(iv_sub(v, (ONE, ONE)))


def square_completion(F: Fraction, K: Fraction, c: Fraction) -> Fraction:
    """max over integers m >= 1 of  m F - c m (m-1) K, bounded above by the
    real-m completion (F + cK)^2 / (4cK) when F > 2cK, else by F.  Exact
    in Q; monotone UP in F and DOWN in K, so recorded one-sided F/K keep
    the bound one-sided."""
    if F <= 2 * c * K:
        return F
    if K <= 0 or c <= 0:
        raise CheckFailure("completion branch needs K > 0 and theta < 1")
    return (F + c * K) ** 2 / (4 * c * K)


def _frac(s) -> Fraction:
    return Fraction(s)


def check_certificate(cert: dict) -> list[dict]:
    """Re-derive every inequality the certificate claims.  Raises
    :class:`CheckFailure` naming the first inequality that does not hold;
    returns per-depth report dicts on success."""
    theta = _frac(cert["theta"])
    if not 0 < theta < 1:
        raise CheckFailure("theta outside (0, 1)")
    c = 1 - theta
    reports = []
    for d in cert["depths"]:
        y, G = _frac(d["y"]), _frac(d["G"])
        if not 0 < y < 1:
            raise CheckFailure("depth outside (0, 1)")
        bands = [{"lo": _frac(b["lo"]), "hi": _frac(b["hi"]),
                  "n_cells": int(b["n_cells"]), "F_up": _frac(b["F_up"]),
                  "K_lo": _frac(b["K_lo"]), "B_up": _frac(b["B_up"])}
                 for b in d["bands"]]
        segs = [[_frac(x) for x in seg] for seg in d["neg_segments"]]

        # 1. geometry: neg cells and band intervals exactly tile (0, G]
        pieces = []
        for seg in segs:
            if len(seg) < 2 or any(seg[i] >= seg[i + 1]
                                   for i in range(len(seg) - 1)):
                raise CheckFailure("neg segment boundaries not increasing")
            pieces.append((seg[0], seg[-1]))
        for b in bands:
            if not b["lo"] < b["hi"]:
                raise CheckFailure("empty band interval")
            pieces.append((b["lo"], b["hi"]))
        pieces.sort()
        if pieces[0][0] != 0 or pieces[-1][1] != G:
            raise CheckFailure("cover does not span [0, G]")
        for (l1_, h1), (l2, _) in zip(pieces, pieces[1:]):
            if h1 != l2:
                raise CheckFailure(f"cover gap or overlap at {h1} vs {l2}")

        # 2. negativity cells: f <= 0 throughout each cell
        n_neg = 0
        for seg in segs:
            for lo, hi in zip(seg, seg[1:]):
                if f_upper_cell(lo, hi, y) > 0:
                    raise CheckFailure(
                        f"y={y}: negativity cell [{lo}, {hi}] not <= 0")
                n_neg += 1

        # 3. band maxima: every band cell's upper endpoint <= F_up
        n_bandcells = 0
        for b in bands:
            lo, hi, n = b["lo"], b["hi"], b["n_cells"]
            step = (hi - lo) / n
            for i in range(n):
                fu = f_upper_cell(lo + i * step, lo + (i + 1) * step, y)
                if fu > b["F_up"]:
                    raise CheckFailure(
                        f"y={y}: band [{lo},{hi}] cell {i}: {fu} > F_up")
                n_bandcells += 1
            if b["F_up"] <= 0:
                raise CheckFailure("band recorded with nonpositive F_up")

        # 4. same-band repulsion floors against the shared omega cover
        oc = d["omega_cover"]
        h_om, n_om = _frac(oc["h"]), int(oc["n"])
        w_max = max(b["hi"] - b["lo"] for b in bands)
        if n_om * h_om < w_max:
            raise CheckFailure("omega cover shorter than the widest band")
        om_lo = [omega_lower_cell(i * h_om, (i + 1) * h_om)
                 for i in range(n_om)]
        prefix = []
        cur = None
        for v in om_lo:
            cur = v if cur is None else min(cur, v)
            prefix.append(cur)
        for b in bands:
            w = b["hi"] - b["lo"]
            idx = -((-w.numerator * h_om.denominator) //
                    (w.denominator * h_om.numerator))       # ceil(w / h)
            floor_om = prefix[min(idx, n_om) - 1]
            K_dr = floor_om ** 2 if floor_om > 0 else Fraction(0)
            if b["K_lo"] > K_dr:
                raise CheckFailure(
                    f"y={y}: K_lo {b['K_lo']} above derived floor {K_dr}")
        K_min = min(b["K_lo"] for b in bands)
        if _frac(d["K_min_lo"]) > K_min:
            raise CheckFailure("K_min_lo above the recorded band floors")
        K_min = _frac(d["K_min_lo"])
        if K_min <= 0:
            raise CheckFailure("K_min_lo must be positive")

        # 5. sigma^2 and slack, both DOWN
        s2_lo = _frac(d["sigma2_lo"])
        if s2_lo < 0:
            raise CheckFailure("sigma2_lo negative")
        if s2_lo > sigma2_lower(y):
            raise CheckFailure(f"y={y}: sigma2_lo above the derived bound")
        slack_lo = _frac(d["slack_lo"])
        if slack_lo > 8 * s2_lo + 8 * s2_lo ** 2:
            raise CheckFailure(f"y={y}: slack_lo above 8 s + 8 s^2")

        # 6. the tail majorant, UP, and its regime checks
        C_up = _frac(d["C_up"])
        if C_up < c_over_a_upper(y):
            raise CheckFailure(f"y={y}: C_up below the derived bound")
        P_lo = _frac(d["P_lo"])
        if P_lo <= 0:
            raise CheckFailure("P_lo must be positive")
        for b1, b2 in zip(bands, bands[1:]):
            if b2["lo"] - b1["hi"] < P_lo:
                raise CheckFailure(f"y={y}: recorded band gap below P_lo")
        tail2 = _frac(d["tail2_up"])
        if tail2 < 8 * C_up ** 2 * (1 / G ** 2 + 1 / (P_lo * G)):
            raise CheckFailure(f"y={y}: tail2_up below the closed form")
        if 4 * C_up ** 2 / G ** 2 > 2 * c * K_min:
            raise CheckFailure(
                f"y={y}: tail bands would leave single occupancy")

        # 7. per-band square completion and the final inequality
        m_star = 1
        for b in bands:
            B = square_completion(b["F_up"], b["K_lo"], c)
            if b["B_up"] < B:
                raise CheckFailure(f"y={y}: B_up below the completion value")
            if b["F_up"] > 2 * c * b["K_lo"]:
                m = int((b["F_up"] + c * b["K_lo"]) / (2 * c * b["K_lo"])
                        + Fraction(1, 2))
                m_star = max(m_star, m)
        cap_up = _frac(d["cap_up"])
        cap_derived = 2 * sum(b["B_up"] for b in bands) + tail2
        if cap_up < cap_derived:
            raise CheckFailure(f"y={y}: cap_up below 2 sum B + tail")
        margin_lo = _frac(d["margin_lo"])
        if margin_lo > slack_lo - cap_up:
            raise CheckFailure(f"y={y}: margin_lo above slack_lo - cap_up")
        if margin_lo < 0:
            raise CheckFailure(f"y={y}: the verdict does not close "
                               f"(margin {margin_lo})")

        reports.append({
            "y": y, "G": G, "bands": len(bands), "n_neg_cells": n_neg,
            "n_band_cells": n_bandcells, "n_omega_cells": n_om,
            "sigma2_lo": s2_lo, "slack_lo": slack_lo, "C_up": C_up,
            "P_lo": P_lo, "tail2_up": tail2, "K_min_lo": K_min,
            "cap_up": cap_up, "margin_lo": margin_lo, "m_star": m_star,
        })
    return reports


def theta_scan_on_certificate(cert: dict, thetas=None) -> dict:
    """Re-run only the exact-in-Q part (completion + final inequality) at
    other theta values, against the SAME recorded F/K/tail data.  The cell
    inequalities are theta-free, so this is a pure Fraction computation."""
    if thetas is None:
        thetas = [Fraction(995, 1000), Fraction(996, 1000),
                  Fraction(997, 1000), Fraction(998, 1000),
                  Fraction(9985, 10000), Fraction(999, 1000),
                  Fraction(9995, 10000)]
    out = {}
    for theta in thetas:
        c = 1 - theta
        worst = None
        closes = True
        for d in cert["depths"]:
            G = _frac(d["G"])
            K_min = _frac(d["K_min_lo"])
            C_up = _frac(d["C_up"])
            if 4 * C_up ** 2 / G ** 2 > 2 * c * K_min:
                closes = False
                worst = None
                break
            total = sum(square_completion(_frac(b["F_up"]), _frac(b["K_lo"]),
                                          c) for b in d["bands"])
            margin = _frac(d["slack_lo"]) - (2 * total + _frac(d["tail2_up"]))
            if worst is None or margin < worst:
                worst = margin
            if margin < 0:
                closes = False
        out[theta] = (closes, worst)
    return out


# ===========================================================================
# PART 2 — THE GENERATOR.  Uses the float instruments (paper_chain) only to
# decide WHERE to put cells; every recorded number is produced by the
# checker's own rational arithmetic with explicit one-sided rounding.
# ===========================================================================

GRAIN = 1 << 48         # recorded scalars live on the 2^-48 grid


def _up(fr: Fraction) -> Fraction:
    return Fraction(-((-fr.numerator * GRAIN) // fr.denominator), GRAIN)


def _down(fr: Fraction) -> Fraction:
    return Fraction((fr.numerator * GRAIN) // fr.denominator, GRAIN)


class GenerationStall(RuntimeError):
    """The cover could not be built at the requested resolution."""


def _neg_cover(seg_lo: Fraction, seg_hi: Fraction, y: Fraction,
               den: int, k_max: int = 11, cell_cap: int = 6000):
    """Greedy adaptive cover of [seg_lo, seg_hi] by cells with f <= 0.

    Dyadic widths 2^k/den; on failure the width halves, on success it
    doubles (capped).  Raises GenerationStall if even the finest width
    cannot pass — reported honestly, never papered over."""
    bounds = [seg_lo]
    p, k = seg_lo, 7
    while p < seg_hi:
        while True:
            q = min(p + Fraction(1 << k, den), seg_hi)
            if f_upper_cell(p, q, y) <= 0:
                break
            k -= 1
            if k < 0:
                raise GenerationStall(
                    f"y={y}: cell at {float(p):.4f} not <= 0 at width 1/{den}")
        p = q
        bounds.append(p)
        if k < k_max:
            k += 1
        if len(bounds) > cell_cap:
            raise GenerationStall(f"y={y}: segment needs > {cell_cap} cells")
    return bounds


#: per-depth cover tuning: (pad numerator over 4096, band cells)
_TUNING = {
    Fraction(1, 50): (8, 32),
    Fraction(1, 10): (12, 32),
    Fraction(3, 10): (16, 32),
    Fraction(49, 100): (24, 48),
}


def generate_certificate(depths=(Fraction(1, 50), Fraction(1, 10),
                                 Fraction(3, 10), Fraction(49, 100)),
                         theta: Fraction = Fraction(995, 1000),
                         G: int = 98, den: int = 4096,
                         verbose: bool = True) -> dict:
    """Build the certificate.  Slow path: float band hints from
    paper_chain, then rational bounds from the Part 1 arithmetic."""
    sys.path.insert(0, str(_HERE))
    from paper_chain import PaperBandDual        # lazy: numpy lives here

    c = 1 - theta
    bd = PaperBandDual(G=float(G))
    Gf = Fraction(G)
    h_om = Fraction(1, 256)
    out_depths = []
    for y in depths:
        pad_num, n_cells = _TUNING[y]
        pad = Fraction(pad_num, den)
        hint = bd.bands(float(y))
        if verbose:
            print(f"[gen] y={y}: {len(hint)} float band hints", flush=True)
        recs = []
        for lo_f, hi_f, _F in hint:
            lo = Fraction(int((Fraction(lo_f).limit_denominator(10 ** 6)
                               - pad) * den) - 1, den)
            hi = Fraction(-int(-(Fraction(hi_f).limit_denominator(10 ** 6)
                                 + pad) * den) + 1, den)
            recs.append([lo, hi])
        for r1, r2 in zip(recs, recs[1:]):
            if r1[1] >= r2[0]:
                raise GenerationStall("padded bands overlap; reduce pad")
        if recs[0][0] <= 0 or recs[-1][1] >= Gf:
            raise GenerationStall("a padded band touches 0 or G")

        # negativity segments between the padded bands
        segs = []
        edges = [Fraction(0)]
        for lo, hi in recs:
            edges.append(lo)
            edges.append(hi)
        edges.append(Gf)
        for i in range(0, len(edges), 2):
            segs.append(_neg_cover(edges[i], edges[i + 1], y, den))

        # band records: F_up from the checker's own cells, UP
        omega_needed = max(hi - lo for lo, hi in recs)
        n_om = -((-omega_needed.numerator * h_om.denominator)
                 // (omega_needed.denominator * h_om.numerator)) + 1
        om_lo = [omega_lower_cell(i * h_om, (i + 1) * h_om)
                 for i in range(n_om)]
        prefix = []
        cur = None
        for v in om_lo:
            cur = v if cur is None else min(cur, v)
            prefix.append(cur)

        bands = []
        for lo, hi in recs:
            step = (hi - lo) / n_cells
            fmax = max(f_upper_cell(lo + i * step, lo + (i + 1) * step, y)
                       for i in range(n_cells))
            F_up = _up(fmax)
            w = hi - lo
            idx = -((-w.numerator * h_om.denominator) //
                    (w.denominator * h_om.numerator))
            floor_om = prefix[min(idx, n_om) - 1]
            if floor_om <= 0:
                raise GenerationStall("omega floor not positive on a band")
            K_lo = _down(floor_om ** 2)
            B_up = _up(square_completion(F_up, K_lo, c))
            bands.append({"lo": str(lo), "hi": str(hi), "n_cells": n_cells,
                          "F_up": str(F_up), "K_lo": str(K_lo),
                          "B_up": str(B_up)})

        # scalars, each rounded the safe way
        s2_lo = _down(sigma2_lower(y))
        if s2_lo <= 0:
            raise GenerationStall("sigma2 lower bound not positive")
        slack_lo = 8 * s2_lo + 8 * s2_lo ** 2
        C_up = _up(c_over_a_upper(y))
        gaps = [r2[0] - r1[1] for r1, r2 in zip(recs, recs[1:])]
        P_lo = Fraction(int(min(gaps) * 64), 64)
        tail2_up = _up(8 * C_up ** 2 * (1 / Gf ** 2 + 1 / (P_lo * Gf)))
        K_min_lo = min(_frac(b["K_lo"]) for b in bands)
        if 4 * C_up ** 2 / Gf ** 2 > 2 * c * K_min_lo:
            raise GenerationStall("tail bands leave single occupancy")
        cap_up = _up(2 * sum(_frac(b["B_up"]) for b in bands) + tail2_up)
        margin_lo = slack_lo - cap_up
        n_neg = sum(len(seg) - 1 for seg in segs)
        if verbose:
            print(f"[gen] y={y}: {n_neg} neg cells, "
                  f"{len(bands)} bands x {n_cells} cells, "
                  f"margin {float(margin_lo):+.3e}", flush=True)
        if margin_lo < 0:
            raise GenerationStall(
                f"y={y}: does not close at theta={theta} "
                f"(margin {float(margin_lo):.3e}); refine the cover")
        out_depths.append({
            "y": str(y), "G": str(Gf), "P_lo": str(P_lo), "C_up": str(C_up),
            "sigma2_lo": str(s2_lo), "slack_lo": str(slack_lo),
            "tail2_up": str(tail2_up), "K_min_lo": str(K_min_lo),
            "cap_up": str(cap_up), "margin_lo": str(margin_lo),
            "omega_cover": {"h": str(h_om), "n": n_om},
            "bands": bands,
            "neg_segments": [[str(x) for x in seg] for seg in segs],
        })

    return {
        "format": "band-certificate-v1",
        "comment": (
            "Finite rational certificate for the paper-field band-dual "
            "verdict cap(theta, y) <= slack(y). Directions: F_up/B_up/C_up/"
            "tail2_up/cap_up round UP, K_lo/sigma2_lo/slack_lo/P_lo/"
            "margin_lo round DOWN. Negativity cells and band intervals "
            "tile (0, G]; each negativity cell has f <= 0 throughout "
            "(interval-argument enclosure). Checked by "
            "band_certificate.check_certificate in pure rational "
            "arithmetic (fractions + math.isqrt only)."),
        "field": "Phi2(z) = s(z+sqrt2) + s(z-sqrt2), s(u) = sin(u/2)/u; "
                 "W = 2(Re^2-Im^2)Phi2/A^2; f = -2W; A = Phi2(0)",
        "theta": str(theta),
        "scale_bits": S,
        "L1_up": str(_up(l1_upper())),
        "depths": out_depths,
    }


# ===========================================================================
# PART 3 — AUDIT AND CONTROLS.
# ===========================================================================


def _mp_point_control(cert: dict, samples_per_depth: int = 4) -> list[dict]:
    """mpmath (dps 40) point values at exact rational cell midpoints must
    lie inside the checker's cell enclosures.  A reference outside its
    enclosure is a critical defect, reported, never widened away."""
    from mpmath import mp, mpc, sqrt as msqrt

    out = []
    with mp.workdps(40):
        s2m = msqrt(2)
        for d in cert["depths"]:
            y = _frac(d["y"])
            cells = []
            b0 = d["bands"][0]
            lo, hi = _frac(b0["lo"]), _frac(b0["hi"])
            cells.append((lo, hi))
            seg = d["neg_segments"][0]
            cells.append((_frac(seg[len(seg) // 2]),
                          _frac(seg[len(seg) // 2 + 1])))
            seg = d["neg_segments"][-1]
            cells.append((_frac(seg[0]), _frac(seg[1])))
            cells = cells[:samples_per_depth]
            for lo, hi in cells:
                mid = (lo + hi) / 2
                fl, fh = (Fraction(v, ONE)
                          for v in f_cell(lo, hi, y))
                z = mpc(mp.mpf(mid.numerator) / mid.denominator,
                        mp.mpf(y.numerator) / y.denominator)
                v = (mp.sin((z + s2m) / 2) / (z + s2m)
                     + mp.sin((z - s2m) / 2) / (z - s2m))
                a = 2 * mp.sin(s2m / 2) / s2m
                f_ref = -4 * ((v.real ** 2 - v.imag ** 2) / a ** 2)
                inside = (mp.mpf(fl.numerator) / fl.denominator <= f_ref
                          <= mp.mpf(fh.numerator) / fh.denominator)
                out.append({"y": float(y), "cell": (float(lo), float(hi)),
                            "inside": bool(inside)})
    return out


def _flint_cell_control(cert: dict) -> list[dict]:
    """The rational cell enclosure and hardened_paper's acb ball enclosure
    of the same cell both contain the true range, so they must intersect."""
    try:
        from flint import acb, arb
        from hardened_paper import phipap_ball, A_BALL, f_lo as bf_lo, \
            f_up as bf_up
    except Exception as exc:                      # pragma: no cover
        return [{"skipped": repr(exc)}]

    out = []
    for d in cert["depths"]:
        y = _frac(d["y"])
        b0 = d["bands"][0]
        lo, hi = _frac(b0["lo"]), _frac(b0["hi"])
        seg = d["neg_segments"][2]
        cells = [(lo, hi), (_frac(seg[0]), _frac(seg[1]))]
        for lo, hi in cells:
            fl, fh = (Fraction(v, ONE) for v in f_cell(lo, hi, y))
            mid, rad = float((lo + hi) / 2), float((hi - lo) / 2)
            v = phipap_ball(acb(arb(mid, rad), arb(float(y))))
            q = v.real * v.real - v.imag * v.imag
            fb = -4 * q / (A_BALL * A_BALL)
            b_lo, b_hi = bf_lo(fb), bf_up(fb)
            meet = max(float(fl), b_lo) <= min(float(fh), b_hi)
            out.append({"y": float(y), "cell": (float(lo), float(hi)),
                        "intersects": bool(meet),
                        "rational_width": float(fh - fl),
                        "ball_width": b_hi - b_lo})
    return out


def _float_comparison(cert: dict) -> list[dict]:
    """Rational bounds vs the float instrument at matched (theta, y):
    the rational cap must land above the float cap minus its own tail
    replacement (G differs), the slack below the float slack."""
    sys.path.insert(0, str(_HERE))
    from paper_chain import PaperBandDual

    theta = float(_frac(cert["theta"]))
    bd = PaperBandDual(G=float(_frac(cert["depths"][0]["G"])))
    out = []
    for d in cert["depths"]:
        y = float(_frac(d["y"]))
        sl_f = bd.pc.slack(y)
        cap_f = bd.cap(theta, y)["cap"]
        out.append({"y": y, "slack_float": sl_f,
                    "slack_lo": float(_frac(d["slack_lo"])),
                    "cap_float": cap_f,
                    "cap_up": float(_frac(d["cap_up"])),
                    "slack_ok": float(_frac(d["slack_lo"])) <= sl_f,
                    "F1_float": bd.bands(y)[0][2],
                    "F1_up": float(_frac(d["bands"][0]["F_up"]))})
    return out


def audit(regenerate: bool = True):
    import time

    t0 = time.monotonic()
    if regenerate or not CERT_PATH.exists():
        print("= generating the certificate (float hints -> rational "
              "bounds, one-sided) =", flush=True)
        cert = generate_certificate()
        CERT_PATH.write_text(json.dumps(cert, indent=1) + "\n",
                             encoding="utf-8")
        print(f"  wrote {CERT_PATH.name}: "
              f"{CERT_PATH.stat().st_size / 1024:.1f} KiB")
    t_gen = time.monotonic() - t0

    cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
    print("= checking the certificate (pure rational arithmetic) =",
          flush=True)
    t1 = time.monotonic()
    reports = check_certificate(cert)
    t_chk = time.monotonic() - t1
    print(f"  theta = {cert['theta']}   (checked in {t_chk:.1f} s; "
          f"generation {t_gen:.1f} s)")
    print("    y      cells(neg/band/omega)  bands  m*  cap_up      "
          "slack_lo    margin_lo")
    for r in reports:
        print(f"  {str(r['y']):>6}   {r['n_neg_cells']:4d}/"
              f"{r['n_band_cells']:4d}/{r['n_omega_cells']:3d}      "
              f"{r['bands']:2d}   {r['m_star']}  "
              f"{float(r['cap_up']):.6e}  {float(r['slack_lo']):.6e}  "
              f"{float(r['margin_lo']):+.6e}")
    print("  exact margins:")
    for r in reports:
        print(f"    y={r['y']}: {r['margin_lo']}")

    print("= theta scan on the SAME recorded data (exact in Q) =",
          flush=True)
    scan = theta_scan_on_certificate(cert)
    star = None
    for theta, (closes, worst) in scan.items():
        note = "closes" if closes else "FAILS"
        wtxt = f"worst margin {float(worst):+.3e}" if worst is not None \
            else "single-occupancy check breaks"
        print(f"  theta={theta}: {note}  ({wtxt})")
        if closes:
            star = theta
    print(f"  largest scanned theta closing on this certificate: {star}")

    print("= control: mpmath point values inside the rational cell "
          "enclosures =", flush=True)
    mpc_rows = _mp_point_control(cert)
    bad = [r for r in mpc_rows if not r["inside"]]
    print(f"  {len(mpc_rows)} sampled cells, all inside: {not bad}"
          + (f"  OFFENDERS: {bad}" if bad else ""))

    print("= control: rational cells vs hardened_paper acb balls "
          "(must intersect) =", flush=True)
    fl_rows = _flint_cell_control(cert)
    if fl_rows and "skipped" in fl_rows[0]:
        print(f"  skipped (flint unavailable): {fl_rows[0]['skipped']}")
    else:
        bad = [r for r in fl_rows if not r["intersects"]]
        print(f"  {len(fl_rows)} cells, all intersect: {not bad}"
              + (f"  OFFENDERS: {bad}" if bad else ""))
        w = fl_rows[0]
        print(f"  sample widths at the first band: rational "
              f"{w['rational_width']:.3e} vs ball {w['ball_width']:.3e}")

    print("= control: rational bounds vs the float instrument =",
          flush=True)
    for row in _float_comparison(cert):
        print(f"  y={row['y']}: slack_lo {row['slack_lo']:.6e} <= float "
              f"{row['slack_float']:.6e}: {row['slack_ok']}   "
              f"F1 up/float = {row['F1_up'] / row['F1_float']:.4f}   "
              f"cap up/float = {row['cap_up'] / row['cap_float']:.4f}")

    print("= control: a planted corruption must be caught =", flush=True)
    import copy
    broken = copy.deepcopy(cert)
    d0 = broken["depths"][0]
    F = _frac(d0["bands"][0]["F_up"])
    d0["bands"][0]["F_up"] = str(F / 2)          # claim a smaller max
    try:
        check_certificate(broken)
        print("  !! the checker accepted a halved F_up: CRITICAL DEFECT")
    except CheckFailure as exc:
        print(f"  halved F_up rejected: {exc}")
    broken = copy.deepcopy(cert)
    seg = broken["depths"][0]["neg_segments"][1]
    del seg[len(seg) // 2]                        # widen one negativity cell
    try:
        check_certificate(broken)
        print("  (a merged negativity cell can legitimately still pass; "
              "geometry stays tiled)")
    except CheckFailure as exc:
        print(f"  merged negativity cell rejected: {exc}")
    broken = copy.deepcopy(cert)
    broken["depths"][0]["neg_segments"][1][0] = str(
        _frac(broken["depths"][0]["neg_segments"][1][0]) + Fraction(1, 4096))
    try:
        check_certificate(broken)
        print("  !! the checker accepted a cover gap: CRITICAL DEFECT")
    except CheckFailure as exc:
        print(f"  cover gap rejected: {exc}")

    print(f"= total audit time {time.monotonic() - t0:.1f} s =")


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--check-only" in argv:
        cert = json.loads(CERT_PATH.read_text(encoding="utf-8"))
        reports = check_certificate(cert)
        for r in reports:
            print(f"y={r['y']}: margin_lo = {r['margin_lo']} "
                  f"({float(r['margin_lo']):+.6e})  cells "
                  f"{r['n_neg_cells']}+{r['n_band_cells']}+"
                  f"{r['n_omega_cells']}")
        loaded = [m for m in ("numpy", "mpmath", "flint") if m in sys.modules]
        print(f"numerical modules imported by this path: {loaded or 'none'}")
        return
    if "--generate" in argv:
        cert = generate_certificate()
        CERT_PATH.write_text(json.dumps(cert, indent=1) + "\n",
                             encoding="utf-8")
        print(f"wrote {CERT_PATH} "
              f"({CERT_PATH.stat().st_size / 1024:.1f} KiB)")
        return
    audit(regenerate="--reuse" not in argv)


if __name__ == "__main__":
    main()
