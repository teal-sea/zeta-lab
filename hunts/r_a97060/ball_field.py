"""Ball-arithmetic enclosures for the k=2 tau-table's field quantities.

The representation is Arb's: a complex ball, centre plus radius, exactly the
shape `lean/ZetaLean/Ball.lean` fixes and `scripts/63_rung3_ball_mirror.py`
mirrors.  Rung 3 measured the rectangle representation losing 13.7x of width
to the ball on precisely this shape of quantity, a squared rotating complex
value, and `Dam(y,s) = -Re ghat(y+is)^2` is one, so the rectangle route is not
taken here.  `python-flint` is the same Arb the repository's `zeta/rigor.py`
uses for its enclosure-carrying paths; the `mpmath.iv` rectangle context is
kept only as the cross-check backend, never as the producer.

Everything public returns OUTWARD bounds: `*_upper` is >= the true supremum
over the whole box, `*_lower` is <= the true infimum.  These are enclosures
feeding a hunt's table and nothing stronger; the reserved word of
`zeta/rigor.py` does not appear here, disclaimers included, because the
lexical guard reads the bytes rather than the intent.

The one formula subtlety: `ghat(z) = phi((z+i*sqrt2)/2) + phi((z-i*sqrt2)/2)`
with `phi(w) = sinh(w)/w`.  `phi` is entire but the quotient form divides by
zero at `w = 0`, which the box `u in [0,u1], tau near sqrt2` actually contains.
Ball division by a ball straddling zero is not defined, so `phi`, `phi'` and
`phi''` switch to their (rigorously truncated) Taylor series for small `|w|`.
The double-precision scan dodged this by never landing on the point.
"""
from __future__ import annotations

import math

from flint import arb, acb, ctx

ctx.prec = 96

_SQRT2 = arb(2).sqrt()
_I = acb(0, 1)

# phi(w) = sinh(w)/w = sum w^(2k)/(2k+1)!  -- series branch for |w| <= _SMALL.
_SMALL = 1.0
_NSER = 14
_ODDFAC = [math.factorial(2 * k + 1) for k in range(_NSER + 2)]


def _small(w: acb) -> bool:
    return bool(w.abs_upper() <= _SMALL)


def _tail(n: int) -> acb:
    """A complex ball containing `sum_{k>=n} w^(2k)/(2k+1)!` for `|w| <= 1`."""
    r = 2.0 / _ODDFAC[n]
    return acb(arb(0, r), arb(0, r))


def _phi(w: acb) -> acb:
    if _small(w):
        w2, acc, p = w * w, acb(0), acb(1)
        for k in range(_NSER):
            acc += p / _ODDFAC[k]
            p = p * w2
        return acc + _tail(_NSER)
    return w.sinh() / w


def _dphi(w: acb) -> acb:
    if _small(w):
        w2, acc, p = w * w, acb(0), w
        for k in range(1, _NSER):
            acc += p * (2 * k) / _ODDFAC[k]
            p = p * w2
        return acc + _tail(_NSER)
    return w.cosh() / w - w.sinh() / (w * w)


def _ddphi(w: acb) -> acb:
    if _small(w):
        w2, acc, p = w * w, acb(0), acb(1)
        for k in range(1, _NSER):
            acc += p * (2 * k * (2 * k - 1)) / _ODDFAC[k]
            p = p * w2
        return acc + _tail(_NSER)
    s, c = w.sinh(), w.cosh()
    return s / w - 2 * c / (w * w) + 2 * s / (w * w * w)


# `k2_closure._ghat` is `sinh(zp/2)/zp + sinh(zm/2)/zm` = `(phi(w+) + phi(w-))/2`
# with `w+- = (z +- i*sqrt2)/2`.  The halving is the whole convention; getting it
# wrong scales `D` by 4 and every margin with it.
def ghat(z: acb) -> acb:
    return (_phi((z + _I * _SQRT2) / 2) + _phi((z - _I * _SQRT2) / 2)) / 2


def dghat(z: acb) -> acb:
    return (_dphi((z + _I * _SQRT2) / 2) + _dphi((z - _I * _SQRT2) / 2)) / 4


def ddghat(z: acb) -> acb:
    return (_ddphi((z + _I * _SQRT2) / 2) + _ddphi((z - _I * _SQRT2) / 2)) / 8


def _ball(lo: float, hi: float) -> arb:
    """The real ball covering [lo, hi], outward at double precision."""
    mid = 0.5 * (lo + hi)
    rad = max(hi - mid, mid - lo)
    return arb(mid, rad * (1 + 1e-15) + 1e-300)


def D_enclosure(y_lo: float, y_hi: float, s_lo: float, s_hi: float) -> arb:
    """A ball containing every `D(y,s) = -Re ghat(y+is)^2` on the box."""
    g = ghat(acb(_ball(y_lo, y_hi), _ball(s_lo, s_hi)))
    return -(g * g).real


def D_upper(y_lo, y_hi, s_lo, s_hi) -> float:
    return float(D_enclosure(y_lo, y_hi, s_lo, s_hi).upper())


def D_lower(y_lo, y_hi, s_lo, s_hi) -> float:
    return float(D_enclosure(y_lo, y_hi, s_lo, s_hi).lower())


def ddD_absupper(y_lo, y_hi, s_lo, s_hi) -> float:
    """Upper bound on `|d^2/dy^2 D(y,s)|` over the box.

    `D = -Re g^2` along the real direction, so `D'' = -Re(2 g'^2 + 2 g g'')`.
    """
    z = acb(_ball(y_lo, y_hi), _ball(s_lo, s_hi))
    g, g1, g2 = ghat(z), dghat(z), ddghat(z)
    v = -(2 * g1 * g1 + 2 * g * g2).real
    return float(v.abs_upper())


def kpair_enclosure(u_lo: float, u_hi: float) -> arb:
    """A ball containing every `Kpair(u) = Re ghat(i u)^2` on `[u_lo, u_hi]`."""
    G = ghat(acb(arb(0), _ball(u_lo, u_hi))).real
    return G * G


def kpair_lower(u_lo, u_hi) -> float:
    v = float(kpair_enclosure(u_lo, u_hi).lower())
    return max(0.0, v)


def kpair_upper(u_lo, u_hi) -> float:
    return float(kpair_enclosure(u_lo, u_hi).upper())


def G_abs_lower(u_lo: float, u_hi: float) -> float:
    """`min |G(tau)|` on the tau-interval, `G(tau) = ghat(i tau)` (real).

    Used by the small-depth lemma.  `ghat` is EVEN with real Taylor
    coefficients, so `ghat'(i tau)` is purely imaginary and the depth-LINEAR
    term of `D` vanishes identically:

        D(u,tau) = -G(tau)^2 + O(u^2),      d/du D(0,tau) = -2 G Re ghat'(i tau) = 0.

    That is what makes the `u -> 0` corner of the depth sup closable by a
    second-order bound instead of a scan.
    """
    G = ghat(acb(arb(0), _ball(u_lo, u_hi))).real
    return max(0.0, float(G.abs_lower()))
