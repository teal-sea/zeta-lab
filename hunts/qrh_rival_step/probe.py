"""Hunt #120: where the quasi-Riemann argument spends its Euler product, and a rival that cannot pay.

The written analysis of the papers is in RESULTS.md.  This file is the
measurement side: it locates zeros with Re s > 7/8 of Epstein zeta functions of
class number above one (the paper's object class with the Euler product
removed), by independent evaluation routes, and it computes the exact Dirichlet
inverse of the rival's coefficients, which is what the paper's twisted Moebius
sum becomes once there is no Euler product to invert.

Routes, chosen for sharing no code:

  A. ``zeta.epstein.epstein_zeta``: the lattice incomplete-gamma split of the
     Mellin transform of the form's theta series.  Slow, about 0.7 digits of
     working precision per unit height.
  B. The Fourier-Bessel expansion of the Eisenstein series.  With
     tau = (b + i sqrt(|D|)) / (2a) = x + i y and Q(m, n) = a |m + n tau|^2,

         zeta_Q(s) = a^{-s} y^{-s} [ 2 zeta(2s) y^s
                     + 2 sqrt(pi) Gamma(s - 1/2) / Gamma(s) zeta(2s - 1) y^{1-s}
                     + 8 pi^s sqrt(y) / Gamma(s)
                       sum_{n>=1} n^{s-1/2} sigma_{1-2s}(n) K_{s-1/2}(2 pi n y) cos(2 pi n x) ].

     The constants were derived by matching route A at four points (measured
     agreement 1e-22 at twenty digits, pinned in test_rival_step.py), not
     taken from a reference.  Implemented twice: on mpmath, and on python-flint
     balls with the Bessel tail bounded in closed form (see ``route_b_ball``).
     The mpmath version loses accuracy above height about 100 at fifteen
     digits (measured in RUNS.md); the ball version reports its own radius.
  C. For discriminant -15 only, the genus-character factorization
     zeta_Q0(s) = zeta(s) L(s, chi_-15) + L(s, chi_-3) L(s, chi_5), with each
     Dirichlet L-function a Hurwitz-zeta sum.  Cheap at any height, and the
     statement of the rival in the paper's own vocabulary: a sum of two
     products of Dirichlet L-functions, each of which the paper's Theorem 1.1
     says is zero-free in Re s > 7/8.

Every number this file writes is a measurement.  Nothing here assigns
evidentiary status; RESULTS.md says what grade each statement carries.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction

import mpmath
from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
if REPO not in sys.path:  # pragma: no cover - import bootstrap
    sys.path.insert(0, REPO)

from zeta import epstein  # noqa: E402

FORMS = {"d15": (1, 1, 4), "d15b": (2, 1, 2), "d23": (1, 1, 6), "h1": (1, 1, 5)}
SEVEN_EIGHTHS = 0.875
GAMMA_1 = "14.134725141734694"

# ---------------------------------------------------------------------------
# routes
# ---------------------------------------------------------------------------


def route_a(s, form, dps=20):
    """The lab's lattice route, unchanged."""
    return epstein.epstein_zeta(s, form, dps=dps)


def _divisors(n: int) -> list[int]:
    return [d for d in range(1, n + 1) if n % d == 0]


def route_b(s, form, dps=20, scale=8, use_cos=True):
    """Fourier-Bessel expansion on mpmath.  ``scale`` and ``use_cos`` exist only
    so a planted fault can be made (the correct values are 8 and True)."""
    a, b, c = form
    with mp.workdps(dps + 10):
        s = mp.mpc(s)
        D = b * b - 4 * a * c
        y = mp.sqrt(-D) / (2 * a)
        x = mp.mpf(b) / (2 * a)
        terms = int(mp.ceil((dps + 10) * mp.log(10) / (2 * mp.pi * y))) + 3
        half = mp.mpf(1) / 2
        E = 2 * mp.zeta(2 * s) * y**s
        E += 2 * mp.sqrt(mp.pi) * mp.gamma(s - half) / mp.gamma(s) * mp.zeta(2 * s - 1) * y ** (1 - s)
        tail = mp.mpf(0)
        for n in range(1, terms + 1):
            sig = mp.fsum(mp.mpf(d) ** (1 - 2 * s) for d in _divisors(n))
            osc = mp.cos(2 * mp.pi * n * x) if use_cos else mp.sin(2 * mp.pi * n * x)
            tail += n ** (s - half) * sig * mp.besselk(s - half, 2 * mp.pi * n * y) * osc
        E += scale * mp.pi**s * mp.sqrt(y) / mp.gamma(s) * tail
        return (a ** (-s)) * y ** (-s) * E


_CHARS: dict = {}


def _kronecker(D: int, q: int) -> dict:
    from sympy import kronecker_symbol

    key = (D, q)
    if key not in _CHARS:
        _CHARS[key] = {r: int(kronecker_symbol(D, r)) for r in range(q)}
    return _CHARS[key]


def dirichlet_L(s, D: int, q: int):
    """L(s, chi_D) for the Kronecker character of conductor q, as a Hurwitz sum.
    Caller sets the precision."""
    chi = _kronecker(D, q)
    return mp.mpf(q) ** (-s) * mp.fsum(chi[r] * mp.zeta(s, mp.mpf(r) / q) for r in range(1, q) if chi[r] != 0)


def route_c(s, dps=20, which=0, parts=False):
    """Genus-character factorization for discriminant -15: the principal form
    (which=0) is zeta L(chi_-15) + L(chi_-3) L(chi_5), the other form (which=1)
    takes the difference.  With ``parts`` the two products are returned too."""
    with mp.workdps(dps + 10):
        s = mp.mpc(s)
        A = mp.zeta(s) * dirichlet_L(s, -15, 15)
        B = dirichlet_L(s, -3, 3) * dirichlet_L(s, 5, 5)
        v = A + B if which == 0 else A - B
        return (v, A, B) if parts else v


def dh(s, dps=20):
    return epstein.dh_f(s, dps=dps)


def evaluator(name: str, dps: int):
    """The mpmath evaluator a census uses, by name."""
    if name == "c15":
        return lambda z: route_c(z, dps=dps)
    if name.startswith("b:"):
        form = FORMS[name[2:]]
        return lambda z: route_b(z, form, dps=dps)
    if name.startswith("a:"):
        form = FORMS[name[2:]]
        return lambda z: route_a(z, form, dps=dps)
    if name == "dh":
        return lambda z: dh(z, dps=dps)
    if name == "zeta":
        return lambda z: mp.zeta(z)
    raise ValueError(name)


# ---------------------------------------------------------------------------
# route B on balls
# ---------------------------------------------------------------------------

_FLINT: tuple | None = None


def flint_ctx():
    """python-flint, with the orientation of ``bessel_k`` derived at first use.

    Its docstring says the order is ``self``; measured against mpmath the order
    is the argument.  Neither reading is trusted: both are tried at one point
    and the one agreeing with mpmath to 1e-12 is kept, or a RuntimeError is
    raised.  (Derive conventions, never remember them.)
    """
    global _FLINT
    if _FLINT is None:
        from flint import acb, arb, ctx

        with ctx.workprec(128):
            ref = complex(mp.besselk(mp.mpc("0.3", "2"), mp.mpf(5)))
            cand_a = acb(5).bessel_k(acb(arb("0.3"), 2))
            cand_b = acb(arb("0.3"), 2).bessel_k(acb(5))

        def close(v):
            return abs(complex(float(v.real.mid()), float(v.imag.mid())) - ref) < 1e-12

        if close(cand_a) and not close(cand_b):
            orient = "z_first"
        elif close(cand_b) and not close(cand_a):
            orient = "order_first"
        else:  # pragma: no cover - would mean an unusable flint
            raise RuntimeError("python-flint bessel_k orientation could not be calibrated against mpmath")
        _FLINT = (acb, arb, ctx, orient)
    return _FLINT


def _bessel_k_ball(nu, z):
    acb, arb, ctx, orient = flint_ctx()
    return z.bessel_k(nu) if orient == "z_first" else nu.bessel_k(z)


def route_b_ball(form, re_mid, im_mid, prec: int, re_rad="0", im_rad="0"):
    """Route B as an acb enclosure of zeta_Q over the box
    [re_mid +- re_rad] x i[im_mid +- im_rad].  Inputs are decimal strings or
    Fractions (converted exactly up to the ball's own rounding).

    The Bessel sum is truncated after M terms and the tail is added as an
    error ball from the closed-form bound derived in RESULTS.md:
    for nu = s - 1/2 with Re nu = a and real t > 0,
    |K_nu(t)| <= sqrt(2 pi / t) exp(-t + a^2 / (2 t)); with
    |sigma_{1-2s}(n)| <= d(n) <= n and |cos| <= 1 each term is at most
    n^sigma y^(-1/2) exp(a^2 / (4 pi y)) exp(-lambda n), lambda = 2 pi y, and
    sum_{n > M} of that is at most M^sigma exp(-lambda M) / (lambda - sigma)
    for M >= 1 and lambda > sigma (the summand is decreasing there, so the sum
    is bounded by the integral, and x^sigma <= M^sigma exp(sigma (x - M)) for
    x >= M >= 1).
    """
    acb, arb, ctx, _ = flint_ctx()
    a, b, c = form

    def ball(v, r="0"):
        if isinstance(v, Fraction):
            mid = arb(v.numerator) / arb(v.denominator)
        else:
            mid = arb(str(v))
        if isinstance(r, Fraction):
            rad = arb(r.numerator) / arb(r.denominator)
        else:
            rad = arb(str(r))
        return mid + arb(0, 1) * rad if float(rad) != 0 else mid

    with ctx.workprec(prec):
        s = acb(ball(re_mid, re_rad), ball(im_mid, im_rad))
        D = b * b - 4 * a * c
        y = arb(-D).sqrt() / (2 * a)
        x = arb(b) / (2 * a)
        pi = arb.pi()
        half = arb(1) / 2
        sigma_hi = float(s.real.upper())
        sigma_lo = float(s.real.lower())
        t_hi = abs(float(s.imag.upper()))
        lam = float(2 * pi * y)
        # enough terms that the tail is far below 2^-prec even after the
        # exp(pi t / 2) growth of 1 / Gamma(s)
        M = int(math.ceil((prec * math.log(2) + math.pi * t_hi / 2 + 80) / lam)) + 2
        E = 2 * (2 * s).zeta() * y**s
        E += 2 * pi.sqrt() * (s - half).gamma() / s.gamma() * (2 * s - 1).zeta() * y ** (1 - s)
        tail = acb(0)
        for n in range(1, M + 1):
            sig = acb(0)
            for d in _divisors(n):
                sig += acb(d) ** (1 - 2 * s)
            tail += acb(n) ** (s - half) * sig * _bessel_k_ball(s - half, acb(2 * pi * n * y)) * (2 * pi * n * x).cos()
        pref = 8 * pi**s * y.sqrt() / s.gamma()
        a_max = max(abs(sigma_lo - 0.5), abs(sigma_hi - 0.5))
        if lam <= sigma_hi:  # pragma: no cover - never for |D| >= 3
            raise ValueError("tail bound needs lambda > sigma")
        tail_bound = (
            float(y) ** -0.5
            * math.exp(a_max * a_max / (4 * math.pi * float(y)))
            * (M**sigma_hi)
            * math.exp(-lam * M)
            / (lam - sigma_hi)
        )
        err = float(pref.abs_upper()) * tail_bound
        E += pref * tail + acb(arb(0, 1) * arb(str(err)), arb(0, 1) * arb(str(err)))
        return (acb(a) ** (-s)) * y ** (-s) * E


def _ball_arg(acb, arb, re_mid, im_mid, re_rad, im_rad):
    def ball(v, r):
        mid = arb(v.numerator) / arb(v.denominator) if isinstance(v, Fraction) else arb(str(v))
        rad = arb(r.numerator) / arb(r.denominator) if isinstance(r, Fraction) else arb(str(r))
        return mid + arb(0, 1) * rad if float(rad) != 0 else mid

    return acb(ball(re_mid, re_rad), ball(im_mid, im_rad))


def zeta_ball(re_mid, im_mid, prec: int, re_rad="0", im_rad="0"):
    """Riemann zeta on balls, for the positive control of the winding routine."""
    acb, arb, ctx, _ = flint_ctx()
    with ctx.workprec(prec):
        return _ball_arg(acb, arb, re_mid, im_mid, re_rad, im_rad).zeta()


_FLINT_CHARS: dict | None = None


def flint_chars():
    """The three Kronecker characters chi_-15, chi_-3, chi_5 as python-flint
    ``dirichlet_char`` objects, found by matching L(2, chi) against the
    mpmath Hurwitz-sum route to 1e-20 over every Conrey index of the modulus
    (derived, not remembered)."""
    global _FLINT_CHARS
    if _FLINT_CHARS is None:
        from flint import acb, ctx, dirichlet_char

        found = {}
        with mp.workdps(30), ctx.workprec(128):
            for key, (D, q) in {"chi15": (-15, 15), "chi3": (-3, 3), "chi5": (5, 5)}.items():
                ref = complex(dirichlet_L(mp.mpf(2), D, q))
                hits = []
                for n in range(1, q):
                    if math.gcd(n, q) != 1:
                        continue
                    chi = dirichlet_char(q, n)
                    v = chi.l(acb(2))
                    if abs(complex(float(v.real.mid()), float(v.imag.mid())) - ref) < 1e-20:
                        hits.append(n)
                if len(hits) != 1:  # pragma: no cover - would mean a broken calibration
                    raise RuntimeError(f"{key}: {len(hits)} Conrey indices match L(2)")
                found[key] = dirichlet_char(q, hits[0])
        _FLINT_CHARS = found
    return _FLINT_CHARS


def route_c_ball(re_mid, im_mid, prec: int, re_rad="0", im_rad="0"):
    """Route C on balls: zeta(s) L(s, chi_-15) + L(s, chi_-3) L(s, chi_5),
    every factor an Arb enclosure.  Usable on segment balls, where route B
    is not (measured: an input radius of 1e-4 gives route B a radius of
    1e67 at height 15, because the Bessel order is then inexact)."""
    acb, arb, ctx, _ = flint_ctx()
    chars = flint_chars()
    with ctx.workprec(prec):
        s = _ball_arg(acb, arb, re_mid, im_mid, re_rad, im_rad)
        return s.zeta() * chars["chi15"].l(s) + chars["chi3"].l(s) * chars["chi5"].l(s)


def point_winding(eval_ball, center_re: Fraction, center_im: Fraction, half: Fraction, prec: int, segs: int = 64):
    """Winding from tight point balls only, without segment enclosures: the
    sum of principal arguments of consecutive quotients around the square.
    Measured, not enclosure-carrying: it also reports the largest increment,
    and is only read as a winding when that is well below pi."""
    acb, arb, ctx, _ = flint_ctx()
    h = half
    step = 2 * h / segs
    points = []
    for k in range(segs):
        points.append((center_re - h + step * k, center_im - h))
    for k in range(segs):
        points.append((center_re + h, center_im - h + step * k))
    for k in range(segs):
        points.append((center_re + h - step * k, center_im + h))
    for k in range(segs):
        points.append((center_re - h, center_im + h - step * k))
    with ctx.workprec(prec):
        pts = [eval_ball(r, i, prec, Fraction(0), Fraction(0)) for (r, i) in points]
        total = arb(0)
        max_inc = 0.0
        for k in range(len(pts)):
            q = pts[(k + 1) % len(pts)] / pts[k]
            inc = q.arg()
            max_inc = max(max_inc, abs(float(inc.mid())))
            total += inc
        wind = total / (2 * arb.pi())
        return {
            "points": len(pts),
            "winding_ball": [float(wind.lower()), float(wind.upper())],
            "winding": int(round(float(wind.mid()))),
            "max_abs_increment": max_inc,
            "max_point_radius": max(float(z.real.rad()) for z in pts),
            "prec_bits": prec,
        }


def ball_winding(eval_ball, center_re: Fraction, center_im: Fraction, half: Fraction, prec: int, segs: int = 16, max_segs: int = 256):
    """Winding number of eval_ball around the square of half-side ``half``
    centred at (center_re, center_im), with every step enclosed.

    Each side is cut into ``segs`` closed segments; the function is evaluated
    on the whole segment as a ball (the varying coordinate is a ball covering
    the segment).  The returned dict reports whether every segment ball
    excluded zero, whether every quotient of consecutive balls had positive
    real part (so the argument increment along a segment is its principal
    argument), and the winding as a ball with its integer value.  The integer
    is reported only when the ball around it has width below one half.

    A segment ball is wider than the segment image (ball evaluation of a sum
    of many terms inflates the radius, measured about 25-fold for zeta at
    height 14 over a segment of length 0.006), so the side is subdivided
    further, doubling ``segs`` up to ``max_segs``, until every segment ball
    excludes zero or the budget is spent.
    """
    attempt = None
    while segs <= max_segs:
        attempt = _ball_winding_once(eval_ball, center_re, center_im, half, prec, segs)
        if attempt["winding"] is not None:
            return attempt
        segs *= 2
    return attempt


def _ball_winding_once(eval_ball, center_re: Fraction, center_im: Fraction, half: Fraction, prec: int, segs: int):
    acb, arb, ctx, _ = flint_ctx()
    h = half
    step = 2 * h / segs
    segments = []  # (re_mid, re_rad, im_mid, im_rad), counterclockwise
    for k in range(segs):  # bottom edge, x increasing
        segments.append((center_re - h + step * (k + Fraction(1, 2)), step / 2, center_im - h, Fraction(0)))
    for k in range(segs):  # right edge, y increasing
        segments.append((center_re + h, Fraction(0), center_im - h + step * (k + Fraction(1, 2)), step / 2))
    for k in range(segs):  # top edge, x decreasing
        segments.append((center_re + h - step * (k + Fraction(1, 2)), step / 2, center_im + h, Fraction(0)))
    for k in range(segs):  # left edge, y decreasing
        segments.append((center_re - h, Fraction(0), center_im + h - step * (k + Fraction(1, 2)), step / 2))
    # the start point of each segment, evaluated as a tight point ball
    points = []
    for k in range(segs):
        points.append((center_re - h + step * k, center_im - h))
    for k in range(segs):
        points.append((center_re + h, center_im - h + step * k))
    for k in range(segs):
        points.append((center_re + h - step * k, center_im + h))
    for k in range(segs):
        points.append((center_re - h, center_im + h - step * k))
    with ctx.workprec(prec):
        # segment balls: enclose the image of the whole closed segment.  If one
        # excludes zero, the argument varies by less than pi along that segment
        # (the image lies in a disc not containing zero), so the increment is
        # the principal argument of the endpoint quotient.
        balls = [eval_ball(r, i, prec, rr, ir) for (r, rr, i, ir) in segments]
        excludes = [not z.contains(acb(0)) for z in balls]
        # point balls at the segment start points: the increments come from
        # these, whose radii are at the working precision, so the sum of the
        # increments has a width that does not grow with the subdivision
        pts = [eval_ball(r, i, prec, Fraction(0), Fraction(0)) for (r, i) in points]
        total = arb(0)
        positive = []
        max_rad = 0.0
        max_point_rad = 0.0
        for k in range(len(pts)):
            z0 = pts[k]
            z1 = pts[(k + 1) % len(pts)]
            max_rad = max(max_rad, float(balls[k].real.rad()), float(balls[k].imag.rad()))
            max_point_rad = max(max_point_rad, float(z0.real.rad()), float(z0.imag.rad()))
            if not excludes[k] or z0.contains(acb(0)) or z1.contains(acb(0)):
                positive.append(False)
                continue
            q = z1 / z0
            pos = float(q.real.lower()) > 0
            positive.append(pos)
            if pos:
                total += q.arg()
        wind = total / (2 * arb.pi())
        ok = all(excludes) and all(positive)
        lo, hi = float(wind.lower()), float(wind.upper())
        n = int(round(float(wind.mid())))
        decided = ok and (hi - lo) < 0.5 and lo > n - 0.5 and hi < n + 0.5
        return {
            "segments": len(balls),
            "all_segments_exclude_zero": all(excludes),
            "all_quotients_right_half_plane": all(positive),
            "winding_ball": [lo, hi],
            "winding": n if decided else None,
            "max_segment_radius": max_rad,
            "max_point_radius": max_point_rad,
            "prec_bits": prec,
        }


# ---------------------------------------------------------------------------
# census
# ---------------------------------------------------------------------------


def count_box(fn, re_lo, re_hi, t0, t1, dps=15):
    """Argument-principle count with the lab's routine, nudging the left edge
    off a zero that sits on it.  Returns (count, re_lo_used)."""
    last = None
    for nudge in (0.0, 0.0131, -0.0117, 0.0271, -0.0233):
        try:
            n = epstein.count_zeros_box(mp.mpc(re_lo + nudge, t0), mp.mpc(re_hi, t1), dps=dps, fn=fn)
            return n, re_lo + nudge
        except ArithmeticError as exc:  # a zero on or hugging the contour
            last = exc
    raise ArithmeticError(f"count_box: every nudge failed on [{re_lo},{re_hi}]x[{t0},{t1}]: {last}")


def locate_zeros(fn, re_lo, re_hi, t0, t1, count, dps=20, grid=(9, 25)):
    """Grid-seeded Newton (mpmath findroot) with deflation by zeros already
    found, ``count`` times.  Returns a list of mpc at ``dps`` digits."""
    found: list = []
    with mp.workdps(dps + 5):

        def deflated(z):
            v = fn(z)
            for r in found:
                v = v / (z - r)
            return v

        for _ in range(count):
            seeds = []
            for i in range(grid[0]):
                sig = re_lo + (re_hi - re_lo) * (i + 0.5) / grid[0]
                for j in range(grid[1]):
                    t = t0 + (t1 - t0) * (j + 0.5) / grid[1]
                    z = mp.mpc(sig, t)
                    seeds.append((abs(deflated(z)), z))
            seeds.sort(key=lambda p: p[0])
            root = None
            tol = mp.mpf(10) ** (-(dps + 2))
            for _, seed in seeds[:8]:
                for solver in ("secant", "muller"):
                    try:
                        cand = mp.findroot(deflated, seed, solver=solver, tol=tol, maxsteps=80)
                    except (ValueError, ZeroDivisionError):
                        continue
                    inside = (re_lo - 1e-9 <= mp.re(cand) <= re_hi + 1e-9) and (t0 - 1e-9 <= mp.im(cand) <= t1 + 1e-9)
                    if (
                        inside
                        and abs(deflated(cand)) < mp.mpf(10) ** (-(dps - 4))
                        and all(abs(cand - r) > mp.mpf("1e-6") for r in found)
                    ):
                        root = cand
                        break
                if root is not None:
                    break
            if root is None:
                raise ArithmeticError(
                    f"locate_zeros: no seed converged in [{re_lo},{re_hi}]x[{t0},{t1}] after {len(found)} of {count}"
                )
            found.append(root)
    return found


def refine(fn, seed, dps=30):
    """Newton polish of a seed on one route, returning the root at dps digits."""
    with mp.workdps(dps + 5):
        return mp.findroot(fn, mp.mpc(seed), tol=mp.mpf(10) ** (-(dps + 2)), maxsteps=80)


def _mpc_to_str(z, digits=25):
    return [mp.nstr(mp.re(z), digits), mp.nstr(mp.im(z), digits)]


def census(args):
    """Windows of height ``win`` from t0 to t1; count zeros in
    [re_lo, re_hi] x window; locate them when asked."""
    fn = evaluator(args.route, args.dps)
    out = {
        "route": args.route,
        "box_re": [args.re_lo, args.re_hi],
        "t_range": [args.t0, args.t1],
        "window": args.win,
        "dps_count": args.dps,
        "windows": [],
        "zeros": [],
        "elapsed_s": None,
    }
    started = time.time()
    t = args.t0
    while t < args.t1 - 1e-9:
        t_hi = min(t + args.win, args.t1)
        tt = time.time()
        n, re_used = count_box(fn, args.re_lo, args.re_hi, t, t_hi, dps=args.dps)
        rec = {"t": [t, t_hi], "re_lo_used": re_used, "count": n, "seconds": round(time.time() - tt, 1)}
        print(f"{args.route} [{re_used:.4f},{args.re_hi}] x [{t},{t_hi}]: {n} zeros ({rec['seconds']}s)", flush=True)
        out["windows"].append(rec)
        if n > 0 and args.locate:
            try:
                roots = locate_zeros(fn, re_used, args.re_hi, t, t_hi, n, dps=args.locate_dps)
            except ArithmeticError as exc:
                rec["locate_failed"] = str(exc)
                print(f"   locate failed: {exc}", flush=True)
                roots = []
            for r in roots:
                z = {"seed_window": [t, t_hi], "root": _mpc_to_str(r), "re": float(mp.re(r)), "im": float(mp.im(r))}
                with mp.workdps(args.locate_dps + 5):
                    z["abs_f"] = mp.nstr(abs(fn(r)), 5)
                    inside = re_used <= float(mp.re(r)) <= args.re_hi and t <= float(mp.im(r)) <= t_hi
                z["inside_window"] = bool(inside)
                try:
                    w, _ = count_box(fn, float(mp.re(r)) - 0.05, float(mp.re(r)) + 0.05, float(mp.im(r)) - 0.05, float(mp.im(r)) + 0.05, dps=args.dps)
                except ArithmeticError as exc:
                    w = f"failed: {exc}"
                z["winding_square_0.1_mpmath"] = w
                print(f"   located {z['root']} |f|={z['abs_f']} inside={inside} winding={w}", flush=True)
                out["zeros"].append(z)
        t = t_hi
    out["elapsed_s"] = round(time.time() - started, 1)
    out["max_re_located"] = max((z["re"] for z in out["zeros"]), default=None)
    out["total_count"] = sum(w["count"] for w in out["windows"])
    _dump(args.out, out)


# ---------------------------------------------------------------------------
# confirmation of located zeros on the other routes and on balls
# ---------------------------------------------------------------------------


def confirm(args):
    """For each zero in a census file: Newton-polish on two routes, compare,
    evaluate the lattice route A at it (when cheap enough), check the mirror
    point 1 - conj(rho), and run the ball winding on route B."""
    src = json.load(open(args.census))
    form = FORMS[args.form]
    out = {"form": list(form), "source": os.path.basename(args.census), "zeros": []}
    for z in src["zeros"]:
        rec = {"census_root": z["root"], "im": z["im"], "re_census": z["re"]}
        seed = mp.mpc(z["root"][0], z["root"][1])
        tt = time.time()
        if args.form == "d15":
            r_c = refine(lambda s: route_c(s, dps=args.dps), seed, dps=args.dps)
            rec["root_route_c"] = _mpc_to_str(r_c, args.dps)
            with mp.workdps(args.dps + 5):
                v, A, B = route_c(r_c, dps=args.dps, parts=True)
                rec["abs_f_route_c"] = mp.nstr(abs(v), 5)
                rec["abs_zeta_L15_at_root"] = mp.nstr(abs(A), 12)
                rec["abs_L3_L5_at_root"] = mp.nstr(abs(B), 12)
                rec["abs_sum_of_parts_over_abs_part"] = mp.nstr(abs(A + B) / abs(A), 5)
                mirror = 1 - mp.conj(r_c)
                rec["abs_f_at_mirror_route_c"] = mp.nstr(abs(route_c(mirror, dps=args.dps)), 5)
        else:
            r_c = None
        low = abs(z["im"]) <= args.route_a_max_t
        b_dps = max(args.dps, int(20 + 0.8 * abs(z["im"])))
        if low or r_c is None:
            # route B on mpmath needs about 0.8 digits per unit height, so it
            # polishes only the low zeros; above that the second route is the
            # route B ball value at the route C root (below)
            r_b = refine(lambda s: route_b(s, form, dps=b_dps), seed, dps=args.dps)
            rec["root_route_b"] = _mpc_to_str(r_b, args.dps)
            rec["route_b_dps"] = b_dps
            with mp.workdps(args.dps + 5):
                rec["abs_f_route_b"] = mp.nstr(abs(route_b(r_b, form, dps=b_dps)), 5)
                if r_c is not None:
                    rec["abs_root_c_minus_root_b"] = mp.nstr(abs(r_c - r_b), 5)
                # planted fault: the same route with a wrong constant does not vanish there
                rec["abs_route_b_scale4_at_root"] = mp.nstr(abs(route_b(r_b, form, dps=b_dps, scale=4)), 5)
                rec["abs_route_b_sin_at_root"] = mp.nstr(abs(route_b(r_b, form, dps=b_dps, use_cos=False)), 5)
                # perturbed zero
                rec["abs_f_route_b_at_root_plus_1e-3"] = mp.nstr(abs(route_b(r_b + mp.mpf("1e-3"), form, dps=b_dps)), 5)
        else:
            r_b = r_c
            rec["route_b_mpmath_polish"] = "not run: height above the route A / route B limit"
            with mp.workdps(args.dps + 5):
                rec["abs_f_route_c_at_root_plus_1e-3"] = mp.nstr(abs(route_c(r_c + mp.mpf("1e-3"), dps=args.dps)), 5)
        if low:
            a_dps = int(20 + abs(z["im"]) * 0.7) + 5
            ta = time.time()
            with mp.workdps(a_dps + 5):
                rec["abs_f_route_a"] = mp.nstr(abs(route_a(r_b, form, dps=a_dps)), 5)
                rec["abs_f_route_a_at_root_plus_1e-3"] = mp.nstr(abs(route_a(r_b + mp.mpf("1e-3"), form, dps=a_dps)), 5)
            rec["route_a_dps"] = a_dps
            rec["route_a_seconds"] = round(time.time() - ta, 1)
        cre = Fraction(mp.nstr(mp.re(r_b), 12)).limit_denominator(10**12)
        cim = Fraction(mp.nstr(mp.im(r_b), 12)).limit_denominator(10**12)
        # segment-enclosed winding on route C balls (discriminant -15 only),
        # square of side 0.1 around the root, and a displaced square
        if args.form == "d15":
            bw = ball_winding(route_c_ball, cre, cim, Fraction(1, 20), 256, segs=args.segs)
            rec["ball_winding_route_c"] = bw
            bw0 = ball_winding(route_c_ball, cre + Fraction(3, 20), cim, Fraction(1, 20), 256, segs=args.segs)
            rec["ball_winding_route_c_displaced_by_0.15"] = bw0
        # point-sampled winding on route B balls, the second backend and the
        # second route at once; measured, not segment-enclosed; low zeros only
        # (256 points at 2500 bits would cost about forty minutes a zero)
        prec_b = int(256 + 8 * abs(z["im"]))
        if low:
            rec["point_winding_route_b_balls"] = point_winding(
                lambda r, i, p, rr, ir: route_b_ball(form, r, i, p, rr, ir), cre, cim, Fraction(1, 20), prec_b, segs=64
            )
        # a tight point enclosure at the root with its radius
        pb = route_b_ball(form, cre, cim, prec_b)
        rec["ball_value_at_root_route_b"] = {
            "abs_upper": float(pb.abs_upper()),
            "re_rad": float(pb.real.rad()),
            "prec_bits": prec_b,
        }
        if args.form == "d15":
            pc = route_c_ball(cre, cim, prec_b)
            rec["ball_value_at_root_route_c"] = {"abs_upper": float(pc.abs_upper()), "re_rad": float(pc.real.rad())}
            rec["ball_routes_overlap_at_root"] = bool(pb.overlaps(pc))
        rec["seconds"] = round(time.time() - tt, 1)
        print(json.dumps(rec, indent=None)[:600], flush=True)
        out["zeros"].append(rec)
    _dump(args.out, out)


# ---------------------------------------------------------------------------
# the Dirichlet inverse: what the Moebius sum becomes without an Euler product
# ---------------------------------------------------------------------------


def rep_counts(form, N: int) -> list[int]:
    """r_Q(n) for 1 <= n <= N by lattice enumeration, exact integers."""
    a, b, c = form
    r = [0] * (N + 1)
    disc4 = 4 * a * c - b * b
    kmax = math.isqrt(4 * a * N // disc4) + 2
    for k in range(-kmax, kmax + 1):
        disc = b * b * k * k - 4 * a * (c * k * k - N)
        if disc < 0:
            continue
        sd = math.isqrt(disc)
        mlo = (-b * k - sd - 2 * a) // (2 * a)
        mhi = (-b * k + sd + 2 * a) // (2 * a)
        for m in range(mlo, mhi + 1):
            q = a * m * m + b * m * k + c * k * k
            if 0 < q <= N:
                r[q] += 1
    return r


def dirichlet_inverse(a: list[int]) -> list[int]:
    """Exact Dirichlet inverse of a with a[1] = 1 (a[0] unused)."""
    N = len(a) - 1
    if a[1] != 1:
        raise ValueError("needs a(1) = 1")
    b = [0] * (N + 1)
    b[1] = 1
    for m in range(1, N + 1):
        bm = b[m]
        if bm == 0:
            continue
        k = 2
        while m * k <= N:
            if a[k]:
                b[m * k] -= a[k] * bm
            k += 1
    return b


def inverse(args):
    form = FORMS[args.form]
    N = args.nmax
    tt = time.time()
    r = rep_counts(form, N)
    a = [0] + [r[n] // 2 for n in range(1, N + 1)]
    if any(r[n] % 2 for n in range(1, N + 1)):
        raise ArithmeticError("representation numbers should be even")
    b = dirichlet_inverse(a)
    out = {"form": list(form), "nmax": N, "a_first_12": a[1:13], "b_first_12": b[1:13]}
    out["max_abs_b"] = max(abs(x) for x in b[1:])
    out["argmax_abs_b"] = max(range(1, N + 1), key=lambda n: abs(b[n]))
    # multiplicativity: count coprime pairs (m, n) with mn <= 2000 where b(mn) != b(m) b(n)
    fails = 0
    pairs = 0
    for m in range(2, 60):
        for n in range(m + 1, 2000 // m + 1):
            if math.gcd(m, n) == 1:
                pairs += 1
                if b[m * n] != b[m] * b[n]:
                    fails += 1
    out["coprime_pairs_checked"] = pairs
    out["multiplicativity_failures"] = fails
    out["b4_vs_b2_squared"] = [b[4], b[2] ** 2]
    out["b6_vs_b2_b3"] = [b[6], b[2] * b[3]]
    out["max_divisor_count_below_nmax"] = _max_divisor_count(N)
    # partial sums on a log grid
    xs = sorted({int(round(10 ** (3 + 3 * j / 90))) for j in range(91)})
    xs = [x for x in xs if x <= N]
    partial = []
    run = 0
    idx = 0
    targets = set(xs)
    sums = {}
    for n in range(1, N + 1):
        run += b[n]
        if n in targets:
            sums[n] = run
    out["partial_sums"] = [[x, sums[x]] for x in xs]
    # envelope exponent: slope of log(max |B| per half-decade bin) against log x
    bins = {}
    for x, Bx in out["partial_sums"]:
        key = int(math.floor(2 * math.log10(x)))
        bins[key] = max(bins.get(key, 0), abs(Bx))
    pts = [(math.log(10 ** (k / 2)), math.log(v)) for k, v in sorted(bins.items()) if v > 0]
    if len(pts) >= 2:
        n_ = len(pts)
        sx = sum(p[0] for p in pts)
        sy = sum(p[1] for p in pts)
        sxx = sum(p[0] ** 2 for p in pts)
        sxy = sum(p[0] * p[1] for p in pts)
        out["envelope_exponent"] = (n_ * sxy - sx * sy) / (n_ * sxx - sx * sx)
    # prediction from located zeros: 2 Re sum x^rho / (rho F'(rho)), route C derivative
    if args.zeros:
        zs = []
        seen = set()
        for path in args.zeros:
            for z in json.load(open(path))["zeros"]:
                key = (round(z["re"], 6), round(z["im"], 6))
                if key not in seen and z.get("inside_window", True):
                    seen.add(key)
                    zs.append(z)
        preds = []
        with mp.workdps(30):
            terms = []
            for z in zs:
                rho = mp.mpc(z["root"][0], z["root"][1])
                if args.form == "d15":
                    fp = mp.diff(lambda s: route_c(s, dps=25), rho)
                else:
                    fp = mp.diff(lambda s: route_b(s, form, dps=max(25, int(20 + 0.8 * float(mp.im(rho))))), rho)
                terms.append((rho, fp))
            out["zeros_used"] = [[mp.nstr(mp.re(r), 12), mp.nstr(mp.im(r), 12), mp.nstr(abs(1 / (r * fp)), 6)] for r, fp in terms]
            for x, Bx in out["partial_sums"]:
                P = 2 * mp.re(mp.fsum(mp.mpf(x) ** r / (r * fp) for r, fp in terms))
                preds.append([x, float(P)])
        out["predicted_partial_sums"] = preds
        # how much of B the located zeros explain, in units of sqrt(x), over the top decade
        top = [(x, Bx, P) for (x, Bx), (_, P) in zip(out["partial_sums"], preds) if x >= N / 10]
        if top:
            rms_b = math.sqrt(sum((Bx / math.sqrt(x)) ** 2 for x, Bx, _ in top) / len(top))
            rms_res = math.sqrt(sum(((Bx - P) / math.sqrt(x)) ** 2 for x, Bx, P in top) / len(top))
            out["top_decade_rms_B_over_sqrt_x"] = rms_b
            out["top_decade_rms_residual_over_sqrt_x"] = rms_res
            out["top_decade_residual_ratio"] = rms_res / rms_b if rms_b else None
    out["elapsed_s"] = round(time.time() - tt, 1)
    _dump(args.out, out)


def _max_divisor_count(N: int) -> int:
    d = [0] * (N + 1)
    for k in range(1, N + 1):
        for m in range(k, N + 1, k):
            d[m] += 1
    return max(d[1:])


# ---------------------------------------------------------------------------
# controls
# ---------------------------------------------------------------------------


def controls(args):
    out = {}
    tt = time.time()
    # 1. positive control: the same finder on zeta recovers gamma_1
    fz = evaluator("zeta", 20)
    n, _ = count_box(fz, 0.3, 0.9, 10.0, 20.0, dps=15)
    out["zeta_box_count_[0.3,0.9]x[10,20]"] = n
    roots = locate_zeros(fz, 0.3, 0.9, 10.0, 20.0, n, dps=25)
    with mp.workdps(30):
        g1 = roots[0]
        out["zeta_located_root"] = _mpc_to_str(g1, 20)
        out["abs_im_minus_gamma_1"] = mp.nstr(abs(mp.im(g1) - mp.mpf(GAMMA_1)), 5)
        out["abs_re_minus_half"] = mp.nstr(abs(mp.re(g1) - mp.mpf(1) / 2), 5)
    bw = ball_winding(zeta_ball, Fraction(1, 2), Fraction(GAMMA_1).limit_denominator(10**12), Fraction(1, 20), 256, segs=16)
    out["zeta_ball_winding_at_gamma_1"] = bw
    bw0 = ball_winding(zeta_ball, Fraction(1, 2) + Fraction(3, 20), Fraction(GAMMA_1).limit_denominator(10**12), Fraction(1, 20), 256, segs=16)
    out["zeta_ball_winding_displaced"] = bw0
    # 2. the routes agree where they should and a planted fault shows
    pts = [mp.mpf(3), mp.mpc("2.5", "5"), mp.mpc("1.1", "12"), mp.mpc("0.9", "30")]
    agree = {}
    for key, form in (("d15", FORMS["d15"]), ("d23", FORMS["d23"])):
        with mp.workdps(30):
            diffs_ab = []
            diffs_bc = []
            faults = []
            for s in pts:
                va = route_a(s, form, dps=20)
                vb = route_b(s, form, dps=20)
                diffs_ab.append(float(abs(va - vb)))
                faults.append(float(abs(va - route_b(s, form, dps=20, scale=4))))
                if key == "d15":
                    diffs_bc.append(float(abs(vb - route_c(s, dps=20))))
            agree[key] = {
                "max_abs_a_minus_b": max(diffs_ab),
                "min_abs_a_minus_b_fault_scale4": min(faults),
            }
            if diffs_bc:
                agree[key]["max_abs_b_minus_c"] = max(diffs_bc)
    out["route_agreement_at_four_points"] = agree
    # 3. the class-number-one control: an Euler product, same detector, same box
    fh = evaluator("b:h1", 15)
    wins = []
    t = 0.5
    while t < args.h1_t_max:
        n, re_used = count_box(fh, 0.8751, 1.6, t, t + 10, dps=15)
        wins.append({"t": [t, t + 10], "count": n})
        print(f"h1 control [{re_used},1.6] x [{t},{t+10}]: {n}", flush=True)
        t += 10
    out["h1_control_windows"] = wins
    out["h1_control_total"] = sum(w["count"] for w in wins)
    # and its inverse coefficients are bounded by the divisor function
    N = 10**5
    r = rep_counts(FORMS["h1"], N)
    a = [0] + [r[n] // 2 for n in range(1, N + 1)]
    b = dirichlet_inverse(a)
    out["h1_inverse_max_abs_b_below_1e5"] = max(abs(x) for x in b[1:])
    out["h1_inverse_max_divisor_count_below_1e5"] = _max_divisor_count(N)
    fails = 0
    pairs = 0
    for m in range(2, 60):
        for n in range(m + 1, 2000 // m + 1):
            if math.gcd(m, n) == 1:
                pairs += 1
                if b[m * n] != b[m] * b[n]:
                    fails += 1
    out["h1_inverse_multiplicativity_failures"] = [fails, pairs]
    # 4. zero-free abscissae: zeta_Q(sigma) = 4 (triangle inequality, see RESULTS.md)
    with mp.workdps(20):
        out["sigma_1_d15_zeta_Q_equals_4"] = mp.nstr(mp.findroot(lambda sg: mp.re(route_b(mp.mpf(sg), FORMS["d15"], dps=15)) - 4, 1.5), 12)
        out["sigma_1_d23_zeta_Q_equals_4"] = mp.nstr(mp.findroot(lambda sg: mp.re(route_b(mp.mpf(sg), FORMS["d23"], dps=15)) - 4, 1.4), 12)
        out["zeta_Q_d15_at_2"] = mp.nstr(mp.re(route_b(mp.mpf(2), FORMS["d15"], dps=15)), 12)
    out["elapsed_s"] = round(time.time() - tt, 1)
    _dump(args.out, out)


# ---------------------------------------------------------------------------
# the Davenport-Heilbronn function: its known off-line zeros against 7/8
# ---------------------------------------------------------------------------


def dh_census(args):
    fn = evaluator("dh", 15)
    out = {"box_re": [0.8751, 2.0], "t_range": [0.0, args.t_max], "windows": []}
    tt = time.time()
    t = 0.0
    while t < args.t_max - 1e-9:
        t_hi = min(t + 10, args.t_max)
        n, re_used = count_box(fn, 0.8751, 2.0, t, t_hi, dps=15)
        out["windows"].append({"t": [t, t_hi], "re_lo_used": re_used, "count": n})
        print(f"DH [{re_used},2.0] x [{t},{t_hi}]: {n}", flush=True)
        t = t_hi
    out["total_count"] = sum(w["count"] for w in out["windows"])
    # the battery's pinned zero and the deepest pair in the lab's census (hunts/flow_repair, height 240.4)
    out["pinned_offline_zero_re"] = str(epstein.OFFLINE_ZERO_RE)[:24]
    out["pinned_offline_zero_below_7_8"] = float(epstein.OFFLINE_ZERO_RE) < SEVEN_EIGHTHS
    with mp.workdps(25):
        r = refine(lambda s: dh(s, dps=20), mp.mpc("0.86953", "240.4046"), dps=20)
        out["flow_repair_pair_root"] = _mpc_to_str(r, 18)
        out["flow_repair_pair_abs_f"] = mp.nstr(abs(dh(r, dps=20)), 5)
        out["flow_repair_pair_re"] = float(mp.re(r))
        out["flow_repair_pair_below_7_8"] = float(mp.re(r)) < SEVEN_EIGHTHS
        w, _ = count_box(fn, float(mp.re(r)) - 0.05, float(mp.re(r)) + 0.05, float(mp.im(r)) - 0.05, float(mp.im(r)) + 0.05, dps=15)
        out["flow_repair_pair_winding_square_0.1"] = w
    out["elapsed_s"] = round(time.time() - tt, 1)
    _dump(args.out, out)


# ---------------------------------------------------------------------------
# assembly
# ---------------------------------------------------------------------------


def assemble(args):
    out = {"hunt": "qrh_rival_step", "seven_eighths": SEVEN_EIGHTHS, "parts": {}}
    for path in args.inputs:
        key = os.path.basename(path).replace("results_", "").replace(".json", "")
        out["parts"][key] = json.load(open(path))
    p = out["parts"]
    # the numbers RESULTS.md quotes, in one place, pinned by test_rival_step.py
    out["pins"] = {
        "d15_count_beyond_7_8_below_300": p["census_d15"]["total_count"],
        "d15_max_re_below_300": p["census_d15"]["max_re_located"],
        "d15_count_beyond_1_below_300": p["census_d15_re1"]["total_count"],
        "d23_count_beyond_7_8_below_60": p["census_d23"]["total_count"],
        "d23_max_re_below_60": p["census_d23"]["max_re_located"],
        "d15_inverse_max_abs_b_below_1e6": p["inverse_d15"]["max_abs_b"],
        "d15_inverse_envelope_exponent": p["inverse_d15"]["envelope_exponent"],
    }
    _dump(args.out, out)


def _dump(path, obj):
    with open(path, "w") as fh:
        json.dump(obj, fh, indent=1)
    print("wrote", path, flush=True)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("census")
    c.add_argument("--route", required=True, help="c15 | b:d15 | b:d23 | a:d15 | dh | zeta")
    c.add_argument("--re-lo", type=float, default=0.8751)
    c.add_argument("--re-hi", type=float, default=1.6)
    c.add_argument("--t0", type=float, default=0.5)
    c.add_argument("--t1", type=float, default=60.5)
    c.add_argument("--win", type=float, default=10.0)
    c.add_argument("--dps", type=int, default=15)
    c.add_argument("--locate", action="store_true")
    c.add_argument("--locate-dps", type=int, default=20)
    c.add_argument("--out", required=True)
    c.set_defaults(func=census)

    k = sub.add_parser("confirm")
    k.add_argument("--census", required=True)
    k.add_argument("--form", required=True, choices=sorted(FORMS))
    k.add_argument("--dps", type=int, default=30)
    k.add_argument("--route-a-max-t", type=float, default=100.0)
    k.add_argument("--segs", type=int, default=16)
    k.add_argument("--out", required=True)
    k.set_defaults(func=confirm)

    i = sub.add_parser("inverse")
    i.add_argument("--form", required=True, choices=sorted(FORMS))
    i.add_argument("--nmax", type=int, default=10**6)
    i.add_argument("--zeros", nargs="*", default=[])
    i.add_argument("--out", required=True)
    i.set_defaults(func=inverse)

    ctl = sub.add_parser("controls")
    ctl.add_argument("--h1-t-max", type=float, default=60.5)
    ctl.add_argument("--out", required=True)
    ctl.set_defaults(func=controls)

    d = sub.add_parser("dh")
    d.add_argument("--t-max", type=float, default=300.0)
    d.add_argument("--out", required=True)
    d.set_defaults(func=dh_census)

    asm = sub.add_parser("assemble")
    asm.add_argument("--inputs", nargs="+", required=True)
    asm.add_argument("--out", required=True)
    asm.set_defaults(func=assemble)

    args = p.parse_args(argv)
    args.func(args)


if __name__ == "__main__":
    main()
