"""Arb evaluators and the segment-argument primitive for hunt #151.

Every function returns a python-flint ball that encloses the named quantity.
Inputs are exact: rationals go in through ``fmpq``, and a segment or a box goes
in as a rectangle ball built from exact endpoints, so a returned ball encloses
the function over the whole segment or box, not only at a sample point.

The objects (normalisation of ``zeta.epstein``):

    f(s) = 5^{-s} [ zeta(s,1/5) + kappa zeta(s,2/5) - kappa zeta(s,3/5) - zeta(s,4/5) ],
    G(s) = (pi/5)^{-(s+1)/2} Gamma((s+1)/2),       F = G f,   F(s) = F(1 - s),
    log G(s) = -((s+1)/2) log(pi/5) + lgamma((s+1)/2),

with ``lgamma`` Arb's principal log-gamma, analytic off (-inf, 0], so log G is
analytic on Re s > -1 and real on the real axis there.  kappa is the Arb
linear-solve ball of ``hunts/lambda_dh_bounds/instrument.kappa_ball``, solved at
twice the working precision because the solve loses about 40 per cent of its bits.

The Dirichlet tail bound.  With a_n the period-5 pattern (1, kappa, -kappa, -1, 0),

    S(sigma) = sum_{n>=2} |a_n| n^{-sigma}
             = 5^{-sigma} [ zeta(sigma,6/5) + kappa (zeta(sigma,2/5) + zeta(sigma,3/5))
                            + zeta(sigma,4/5) ],

and |f(s) - 1| <= S(Re s).  Where S < 1, f has no zero and Re f > 0.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import os
import sys
from fractions import Fraction

from flint import acb, arb, ctx, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "hunts", "lambda_dh_bounds"))

from instrument import kappa_ball  # noqa: E402


class prec_guard:
    """Set ``ctx.prec`` for a block and restore it after."""

    def __init__(self, prec: int):
        self.prec = int(prec)

    def __enter__(self):
        self.old = ctx.prec
        ctx.prec = self.prec
        return self

    def __exit__(self, *exc):
        ctx.prec = self.old
        return False


def q_arb(q) -> arb:
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def point(re, im) -> acb:
    """Exact complex point from two rationals."""
    return acb(q_arb(re), q_arb(im))


def rect(re_lo, re_hi, im_lo, im_hi) -> acb:
    """A rectangle ball containing [re_lo, re_hi] x [im_lo, im_hi] (exact ends)."""
    re_lo, re_hi, im_lo, im_hi = map(Fraction, (re_lo, re_hi, im_lo, im_hi))
    mr, rr = (re_lo + re_hi) / 2, (re_hi - re_lo) / 2
    mi, ri = (im_lo + im_hi) / 2, (im_hi - im_lo) / 2
    return acb(arb(q_arb(mr), q_arb(rr)), arb(q_arb(mi), q_arb(ri)))


_CONST: dict[int, tuple] = {}


def _const(prec: int) -> tuple:
    c = _CONST.get(prec)
    if c is None:
        k = kappa_ball(2 * prec)          # the linear solve loses about 40 per cent
        with prec_guard(prec):
            k = +k                        # round once to the working precision
            shifts = [acb(fmpq(j, 5)) for j in (1, 2, 3, 4)]
            logpi5 = (arb.pi() / 5).log()
            c = (k, shifts, logpi5)
        _CONST[prec] = c
    return c


def f_ball(s: acb, prec: int, kappa_override=None) -> acb:
    """f(s) enclosed.  ``kappa_override`` exists only for planted faults."""
    k, shifts, _ = _const(prec)
    if kappa_override is not None:
        k = kappa_override
    with prec_guard(prec):
        h = [s.zeta(a) for a in shifts]
        return acb(5) ** (-s) * (h[0] + k * h[1] - k * h[2] - h[3])


def logG_ball(s: acb, prec: int) -> acb:
    """log G(s) on Re s > -1, the analytic branch real on the real axis."""
    _, _, logpi5 = _const(prec)
    with prec_guard(prec):
        h = (s + 1) / 2
        return -h * logpi5 + h.lgamma()


def F_ball(s: acb, prec: int) -> acb:
    with prec_guard(prec):
        return logG_ball(s, prec).exp() * f_ball(s, prec)


def S_tail(sigma, prec: int) -> arb:
    """S(sigma) = sum_{n>=2} |a_n| n^{-sigma}, enclosed (sigma > 1)."""
    k, _, _ = _const(prec)
    with prec_guard(prec):
        sg = q_arb(sigma)
        z = lambda a: acb(sg).zeta(acb(q_arb(a))).real
        total = z(Fraction(6, 5)) + k * (z(Fraction(2, 5)) + z(Fraction(3, 5))) \
            + z(Fraction(4, 5))
        return arb(5) ** (-sg) * total


# ---------------------------------------------------------------------------
# argument change along a segment
# ---------------------------------------------------------------------------

_ROT = {0: (1, 0), 1: (0, -1), 2: (-1, 0), 3: (0, 1)}  # multiply by e^{-i phi}


def _half_plane(w: acb):
    """k in 0..3 with w e^{-i k pi/2} in the open right half-plane, or None."""
    if w.real > 0:
        return 0
    if w.imag > 0:
        return 1
    if w.real < 0:
        return 2
    if w.imag < 0:
        return 3
    return None


def _rot(w: acb, k: int) -> acb:
    a, b = _ROT[k]
    return w * acb(a, b)


def _arg_right(u: acb):
    """Arg u for u proven in Re > 0, as an arb; None if not proven."""
    if not (u.real > 0):
        return None
    return (u.imag / u.real).atan()


def segment_arg_change(fn, a: tuple, b: tuple, prec: int, depth: int = 0,
                       max_depth: int = 40, stats: dict | None = None) -> arb:
    """Continuous change of arg fn along the straight segment a -> b.

    ``a``, ``b`` are exact (re, im) pairs of Fractions; ``fn(ball, prec)`` must
    return an enclosure of an analytic function over the ball.  If the image of
    the whole segment's rectangle ball lies in one open half-plane through 0,
    the continuous argument varies by less than pi on the segment and equals
    Arg(fn(b) e^{-i phi}) - Arg(fn(a) e^{-i phi}), both taken in (-pi/2, pi/2).
    Otherwise the segment is bisected.  Raises if max_depth is reached
    (a zero on or too near the segment).
    """
    if stats is not None:
        stats["evals"] = stats.get("evals", 0) + 1
    (ar, ai), (br, bi) = a, b
    with prec_guard(prec):              # build the rectangle at the working precision
        box = rect(min(ar, br), max(ar, br), min(ai, bi), max(ai, bi))
        img = fn(box, prec)
        k = _half_plane(img)
        if k is not None:
            ua = _rot(fn(point(ar, ai), prec), k)
            ub = _rot(fn(point(br, bi), prec), k)
            pa, pb = _arg_right(ua), _arg_right(ub)
            if pa is not None and pb is not None:
                if stats is not None:
                    stats["leaves"] = stats.get("leaves", 0) + 1
                return pb - pa
    if depth >= max_depth:
        raise RuntimeError(f"segment {a} -> {b} not resolved at depth {depth}")
    m = ((ar + br) / 2, (ai + bi) / 2)
    left = segment_arg_change(fn, a, m, prec, depth + 1, max_depth, stats)
    right = segment_arg_change(fn, m, b, prec, depth + 1, max_depth, stats)
    with prec_guard(prec):
        return left + right


def box_zero_count(fn, re_lo, re_hi, im_lo, im_hi, prec: int, pieces: int = 4,
                   stats: dict | None = None) -> arb:
    """(1/2 pi) times the arg change of fn around the box, counterclockwise."""
    re_lo, re_hi, im_lo, im_hi = map(Fraction, (re_lo, re_hi, im_lo, im_hi))
    corners = [(re_lo, im_lo), (re_hi, im_lo), (re_hi, im_hi), (re_lo, im_hi)]
    total = arb(0)
    for i in range(4):
        p, q = corners[i], corners[(i + 1) % 4]
        for j in range(pieces):
            u = (p[0] + (q[0] - p[0]) * Fraction(j, pieces),
                 p[1] + (q[1] - p[1]) * Fraction(j, pieces))
            v = (p[0] + (q[0] - p[0]) * Fraction(j + 1, pieces),
                 p[1] + (q[1] - p[1]) * Fraction(j + 1, pieces))
            piece = segment_arg_change(fn, u, v, prec, stats=stats)
            with prec_guard(prec):
                total = total + piece
    with prec_guard(prec):
        return total / (2 * arb.pi())


def unique_integer(x: arb):
    """The integer inside the ball x if it is unique and x has radius < 1/2."""
    if not (x.rad() < 0.5):
        return None
    n = int(round(float(x.mid())))
    return n if x.contains(arb(n)) else None
