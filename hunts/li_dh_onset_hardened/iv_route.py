"""The second route: f and log G in mpmath's interval context, no Arb anywhere.

Shares no evaluator code with ``balls.py``.  Hurwitz zeta by Euler-Maclaurin,

    zeta(s, a) = sum_{n<K} (n+a)^{-s} + (K+a)^{1-s}/(s-1) + (K+a)^{-s}/2
                 + sum_{j=1}^{J} B_{2j}/(2j)! (s)_{2j-1} (K+a)^{-s-2j+1} + E,

with |E| <= |s + 2J + 1| / (sigma + 2J + 1) times the first omitted term (the
bound ``zeta.rigor`` uses for a = 1, Edwards section 6.4; the derivation is the
same for x + a).  kappa by its own linear solve at s0 = 3/4 + 3i/2 in intervals;
log Gamma by ``mpmath.iv.loggamma``.  The node itself is built in intervals from
c and k, not converted from a ball.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import math
from fractions import Fraction as Q

import mpmath
from mpmath import iv

_BERN: dict[int, Q] = {}


class _ivprec:
    """Set ``iv.prec`` for a block and restore it (mpmath's iv has no workprec)."""

    def __init__(self, prec: int):
        self.prec = prec

    def __enter__(self):
        self.old = iv.prec
        iv.prec = self.prec

    def __exit__(self, *exc):
        iv.prec = self.old
        return False


def _bern(j: int) -> Q:
    c = _BERN.get(j)
    if c is None:
        p, q = mpmath.bernfrac(2 * j)
        c = Q(int(p), int(q) * math.factorial(2 * j))
        _BERN[j] = c
    return c


def _q(x: Q):
    x = Q(x)
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


def hurwitz(s, a: Q, prec: int):
    sig = s.real
    abs_s = float(abs(s).b)
    dps = int(prec / 3.32) + 5
    J = max(8, int(0.55 * dps))
    K = max(2 * J, int(abs_s) + 4, dps)
    aa = _q(a)
    total = iv.mpc(0)
    for n in range(K):
        total += iv.exp(-s * iv.log(n + aa))
    lK = iv.log(K + aa)
    total += iv.exp(-s * lK) / 2
    total += iv.exp((1 - s) * lK) / (s - 1)
    poch = s
    for j in range(1, J + 1):
        c = _bern(j)
        total += _q(c) * poch * iv.exp((-s - (2 * j - 1)) * lK)
        poch = poch * (s + (2 * j - 1)) * (s + 2 * j)
    c = _bern(J + 1)
    first = _q(abs(c)) * abs(poch) * abs(iv.exp((-s - (2 * J + 1)) * lK))
    bound = abs(s + (2 * J + 1)) / abs(sig + (2 * J + 1)) * first
    e = bound.b
    return total + iv.mpc(iv.mpf([-e, e]), iv.mpf([-e, e]))


def _lam(s, conj: bool, prec: int):
    i = iv.mpc(0, -1) if conj else iv.mpc(0, 1)
    h = [hurwitz(s, Q(j, 5), prec) for j in (1, 2, 3, 4)]
    L = iv.exp(-s * iv.log(5)) * (h[0] + i * h[1] - i * h[2] - h[3])
    w = (s + 1) / 2
    return iv.exp(-w * iv.log(iv.pi / 5) + iv.loggamma(w)) * L


def kappa(prec: int):
    with _ivprec(prec):
        s0 = iv.mpc(_q(Q(3, 4)), _q(Q(3, 2)))
        A = _lam(s0, False, prec) + _lam(s0, True, prec) \
            - _lam(1 - s0, False, prec) - _lam(1 - s0, True, prec)
        B = _lam(s0, False, prec) - _lam(s0, True, prec) \
            - _lam(1 - s0, False, prec) + _lam(1 - s0, True, prec)
        k = A / (iv.mpc(0, 1) * B)
        if not (k.imag.a <= 0 <= k.imag.b):
            raise ValueError("iv kappa: imaginary part excludes 0")
        return k.real


def node_s(c: int, k: int, N: int, prec: int):
    """s_k = 1/(1 - z_k), z_k = sqrt(1 - 1/c) e^{2 pi i k/N}, in intervals."""
    with _ivprec(prec):
        r = iv.sqrt(1 - _q(Q(1, c)))
        th = 2 * iv.pi * _q(Q(k, N))
        z = iv.mpc(r * iv.cos(th), r * iv.sin(th))
        return 1 / (1 - z)


def f_iv(s, prec: int, kap=None):
    with _ivprec(prec):
        kap = kappa(prec) if kap is None else kap
        h = [hurwitz(s, Q(j, 5), prec) for j in (1, 2, 3, 4)]
        return iv.exp(-s * iv.log(5)) * (h[0] + kap * h[1] - kap * h[2] - h[3])


def logG_iv(s, prec: int):
    with _ivprec(prec):
        w = (s + 1) / 2
        return -w * iv.log(iv.pi / 5) + iv.loggamma(w)


def _exact(raw) -> Q:
    sign, man, exp, _bc = raw
    v = Q(int(man)) * (Q(2) ** int(exp))
    return -v if sign else v


def bounds(z) -> tuple:
    """(re_lo, re_hi, im_lo, im_hi) of a complex interval, as exact Fractions."""
    (a, b), (c, d) = z.real._mpi_, z.imag._mpi_
    return (_exact(a), _exact(b), _exact(c), _exact(d))
