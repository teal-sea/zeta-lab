"""Bit-exact Fraction mirror of the ZetaLean rational interval arithmetic.

Mirrors Rigor.lean / IntervalExp.lean / IntervalCExp.lean / DHCertSupport.lean
definitions exactly, so the generator can emit literal box values whose
equality with the Lean expressions the kernel then verifies.  A mismatch here
cannot weaken the certificate — the emitted equality lemma simply fails.
"""
from __future__ import annotations

import math
from fractions import Fraction as F


class I:
    __slots__ = ("lo", "hi")

    def __init__(self, lo, hi):
        self.lo, self.hi = F(lo), F(hi)
        assert self.lo <= self.hi


def iexact(q): q = F(q); return I(q, q)
def iadd(x, y): return I(x.lo + y.lo, x.hi + y.hi)
def ineg(x): return I(-x.hi, -x.lo)
def isub(x, y): return iadd(x, ineg(y))


def imul(x, y):
    c = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
    return I(min(c[0], c[1], c[2], c[3]), max(c[0], c[1], c[2], c[3]))


def ihalve(x): return I(x.lo / 2, x.hi / 2)
def iinv(x): assert x.lo > 0; return I(1 / x.hi, 1 / x.lo)


def icoarsen(p, x):
    tp = F(2) ** p
    return I(F(math.floor(x.lo * tp)) / tp, F(math.ceil(x.hi * tp)) / tp)


def expSum(n, q): return sum((F(q) ** i) / math.factorial(i) for i in range(n))
def expRem(n, q): return abs(F(q)) ** n * F(n + 1, math.factorial(n) * n)


def exp1(n, x):
    lo = expSum(n, x.lo) - expRem(n, x.lo)
    return I(lo, max(expSum(n, x.hi) + expRem(n, x.hi), lo))


def logSum(n, q): return sum(F(q) ** (i + 1) / (i + 1) for i in range(n))
def logRem(n, q): q = abs(F(q)); return q ** (n + 1) / (1 - q)


def log1(n, x):
    lo = -logSum(n, 1 - x.lo) - logRem(n, 1 - x.lo)
    return I(lo, max(-logSum(n, 1 - x.hi) + logRem(n, 1 - x.hi), lo))


def log2I(n): return ineg(log1(n, iexact(F(1, 2))))


def logQ(n, k, q):
    return iadd(imul(iexact(F(k)), log2I(n)), log1(n, iexact(F(q) / F(2) ** k)))


class C:
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re, self.im = re, im


def cexact(q, r): return C(iexact(q), iexact(r))
def cadd(x, y): return C(iadd(x.re, y.re), iadd(x.im, y.im))
def cneg(x): return C(ineg(x.re), ineg(x.im))


def cmul(x, y):
    return C(isub(imul(x.re, y.re), imul(x.im, y.im)),
             iadd(imul(x.re, y.im), imul(x.im, y.re)))


def chalve(x): return C(ihalve(x.re), ihalve(x.im))
def ccoarsen(p, x): return C(icoarsen(p, x.re), icoarsen(p, x.im))


def normBound(x):
    return max(abs(x.re.lo), abs(x.re.hi)) + max(abs(x.im.lo), abs(x.im.hi))


def powI(x, m):
    r = cexact(1, 0)
    for _ in range(m):
        r = cmul(r, x)
    return r


def smulQ(q, x): return cmul(cexact(q, 0), x)


def expSumC(x, m):
    acc = cexact(0, 0)
    for i in range(m):
        acc = cadd(acc, smulQ(F(1, math.factorial(i)), powI(x, i)))
    return acc


def cinflate(x, r):
    r = abs(F(r))
    return C(I(x.re.lo - r, x.re.hi + r), I(x.im.lo - r, x.im.hi + r))


def expSmall(n, x):
    return cinflate(expSumC(x, n), normBound(x) ** n * F(n + 1, math.factorial(n) * n))


def expCr(n, p, k, x):
    if k == 0:
        return ccoarsen(p, expSmall(n, x))
    y = expCr(n, p, k - 1, chalve(x))
    return ccoarsen(p, cmul(y, y))


def dirichletTermBox(n, p, kL, kE, m, S):
    return expCr(n, p, kE, cmul(cneg(S), C(logQ(n, kL, F(m)), iexact(0))))


def distToZero(x): return max(F(0), x.lo, -x.hi)
def normLower(B): return max(distToZero(B.re), distToZero(B.im))
def normSqI(x): return iadd(imul(x.re, x.re), imul(x.im, x.im))
def invC(x): d = iinv(normSqI(x)); return C(imul(x.re, d), imul(ineg(x.im), d))
def inv5sBox(S): return cmul(cexact(5, 0), cadd(cexact(1, 0), cneg(S)))


KAPPA_I = I(F(2840788, 10**7), F(2840794, 10**7))
KAPPA_C = C(KAPPA_I, iexact(0))


def coeffBox(m):
    j = m % 5
    if j == 1: return cexact(1, 0)
    if j == 2: return KAPPA_C
    if j == 3: return C(ineg(KAPPA_I), iexact(0))
    if j == 4: return cexact(-1, 0)
    return cexact(0, 0)


def term(m, S, n=20, p=64, kE=10):
    if m % 5 == 0:
        return cexact(0, 0)
    return cmul(coeffBox(m), dirichletTermBox(n, p, m.bit_length(), kE, m, S))
