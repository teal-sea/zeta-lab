"""The independent evaluator, made fast enough for every node: mpmath.iv only.

Same mathematics as ``iv_route.py`` (Euler-Maclaurin for each Hurwitz value,
the same rigorous remainder bound), rearranged so that a node costs about 90
complex interval exponentials instead of about 540:

    f(s) = sum_{m < 5K, 5 does not divide m} a_m m^{-s}
           + 5^{-s} sum_{j=1}^{4} c_j E_j(s),           c = (1, kappa, -kappa, -1),

where the first sum is the four partial sums sum_{n<K} (n + j/5)^{-s} times 5^{-s}
(since (n + j/5)^{-s} = 5^s (5n + j)^{-s}), and E_j is the Euler-Maclaurin tail of
zeta(s, j/5) from n = K: x^{1-s}/(s-1) + x^{-s}/2 + sum_{i<=J} B_{2i}/(2i)! (s)_{2i-1}
x^{-s-2i+1} + R, x = K + j/5, |R| <= |s + 2J + 1|/(sigma + 2J + 1) times the
first omitted term.  m^{-s} is built multiplicatively: p^{-s} = exp(-s log p) for
primes p, and m^{-s} = p^{-s} (m/p)^{-s} with p the smallest prime factor of m.
x^{-s} is one exponential per j and the Bernoulli terms use the real powers
x^{-2i}.  log G uses ``mpmath.iv.loggamma``; a node with an exactly real s goes
through the real interval loggamma (mpmath's complex interval loggamma crashes
when the imaginary part is exactly zero, the defect ``zeta.rigor`` records).

Nothing in this file calls Arb or python-flint.  ``to_arb``/``from_arb`` in
``ivpipe.py`` convert boxes to balls exactly, outward, after the evaluation.

Nothing here is evidence about the Riemann Hypothesis.
"""

from __future__ import annotations

import math
from fractions import Fraction as Q

import mpmath
from mpmath import iv

from iv_route import _bern, _ivprec, _q
from iv_route import kappa as kappa_iv


class Ctx:
    """Precomputed constants for one precision and one K."""

    def __init__(self, prec: int, K: int | None = None, J: int | None = None):
        self.prec = prec
        dps = int(prec / 3.32) + 5
        self.J = J or max(8, int(0.55 * dps))
        self.Kmin = K or max(2 * self.J, dps)
        with _ivprec(prec):
            self.kappa = kappa_iv(prec)
            self.c = [iv.mpf(1), self.kappa, -self.kappa, iv.mpf(-1)]
            self.bern = [None] + [_q(_bern(i)) for i in range(1, self.J + 2)]
            self.log5 = iv.log(5)
            self.logpi5 = iv.log(iv.pi / 5)
        self._sieves: dict[int, tuple] = {}

    def sieve(self, M: int) -> tuple:
        """(smallest prime factor list, {p: log p}) for m < M."""
        got = self._sieves.get(M)
        if got is None:
            spf = list(range(M))
            for p in range(2, int(M ** 0.5) + 1):
                if spf[p] == p:
                    for q in range(p * p, M, p):
                        if spf[q] == q:
                            spf[q] = p
            with _ivprec(self.prec):
                logs = {p: iv.log(p) for p in range(2, M) if spf[p] == p}
            got = (spf, logs)
            self._sieves[M] = got
        return got


def f_fast(s, C: Ctx):
    """f(s) as a complex interval; s a complex interval with Re s > 0."""
    with _ivprec(C.prec):
        abs_s = float(abs(s).b)
        K = max(C.Kmin, int(abs_s) + 4)
        M = 5 * K
        spf, logs = C.sieve(M)
        pw = [None, iv.mpc(1)] + [None] * (M - 2)
        for m in range(2, M):
            p = spf[m]
            if p == m:
                pw[m] = iv.exp(-s * logs[p])
            else:
                pw[m] = pw[p] * pw[m // p]
        total = iv.mpc(0)
        for m in range(1, M):
            r = m % 5
            if r:
                total += C.c[r - 1] * pw[m]
        tail = iv.mpc(0)
        J = C.J
        for j in range(1, 5):
            x = _q(Q(K * 5 + j, 5))
            xs = iv.exp(-s * iv.log(x))              # x^{-s}
            e = xs * x / (s - 1) + xs / 2
            inv_x = 1 / x
            inv_x2 = inv_x * inv_x
            poch = s
            xpow = inv_x                              # x^{-(2i-1)}
            for i in range(1, J + 1):
                e += C.bern[i] * poch * xs * xpow
                poch = poch * (s + (2 * i - 1)) * (s + 2 * i)
                xpow = xpow * inv_x2
            first = abs(C.bern[J + 1]) * abs(poch) * abs(xs) * xpow
            bound = (abs(s + (2 * J + 1)) / abs(s.real + (2 * J + 1)) * first).b
            e += iv.mpc(iv.mpf([-bound, bound]), iv.mpf([-bound, bound]))
            tail += C.c[j - 1] * e
        return total + iv.exp(-s * C.log5) * tail


def logG_fast(s, C: Ctx):
    with _ivprec(C.prec):
        w = (s + 1) / 2
        (a, b) = w.imag._mpi_
        if a == b and a[1] == 0:                     # exactly real: real loggamma
            lg = iv.mpc(iv.loggamma(w.real), 0)
        else:
            lg = iv.loggamma(w)
        return -w * C.logpi5 + lg
