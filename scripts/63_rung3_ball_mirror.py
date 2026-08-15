"""Ball-arithmetic mirror: the same interval layer, centre+radius instead of a box.

`docs/25` §4.3 isolated the boxed-`s` width constant `rho_W` as the thing that
makes plan v2 infeasible, and named its cause: "the rectangle representation of
a rotating complex value under repeated squaring".  A rectangle is not
rotation-invariant, so every one of `expCr`'s `kE` squarings pays for the
wrapping; a ball is, so it does not.

This module mirrors `61_rung3_mirror.py` operation for operation with a ball
representation, exposing the *same names* so a measurement harness can swap the
two and compare like for like.  It is a measurement instrument, not a
certificate producer: nothing here emits Lean.  But every operation is written
in the shape a Lean soundness lemma would take, so the measurement is a fair
prediction of what the Lean change would buy.

Representation: a ball is an exact Gaussian-rational centre `(cre, cim)` plus an
exact non-negative rational radius `r`, denoting `{z : |z - c| <= r}`.
Soundness rules, all outward:

* add/neg  — centres exact, radii add.  Exact, no rounding.
* mul      — centre `c1*c2` exact; radius `|c1|r2 + |c2|r1 + r1r2`, with every
             modulus replaced by a rational UPPER bound.
* inv      — for `r < |c|`, `1/B` is contained in the ball about `1/c` (exact,
             a Gaussian rational) of radius `r / (|c|(|c| - r))`, upper-bounded.
* coarsen  — round the centre to `p` bits and ADD the displacement to the
             radius; round the radius up.  Keeps bit-length flat, as
             `Interval.coarsen` does for boxes.
* normBound / normLower — `|c| + r` and `max(0, |c| - r)`, the second with a
             LOWER bound on `|c|`.  Both are tighter than the box forms, which
             carry the L1 norm `max|re| + max|im|` and, after `inflate r`, count
             the radius twice (`docs/25` §4.3 defect 1).

Rational moduli come from `isqrt` at `SQRT_P` bits, the primitive Lean already
has in `contains_sqrt_of_sq` (`DHAssembly.lean`).
"""
from __future__ import annotations

import math
from fractions import Fraction as F

SQRT_P = 96  # bits for the rational modulus bounds; well below the coarsening cost


# --- rational square-root bounds ----------------------------------------------

def sqrt_upper(x: F, p: int = SQRT_P) -> F:
    """Smallest `k / 2^p` whose square is >= `x >= 0`."""
    if x <= 0:
        return F(0)
    a, b = x.numerator, x.denominator
    scale = 1 << (2 * p)
    k = math.isqrt((a * scale + b - 1) // b)
    while k * k * b < a * scale:
        k += 1
    return F(k, 1 << p)


def sqrt_lower(x: F, p: int = SQRT_P) -> F:
    """Largest `k / 2^p` whose square is <= `x`."""
    if x <= 0:
        return F(0)
    a, b = x.numerator, x.denominator
    scale = 1 << (2 * p)
    k = math.isqrt((a * scale) // b)
    while (k + 1) * (k + 1) * b <= a * scale:
        k += 1
    return F(k, 1 << p)


def _ceil_bits(q: F, p: int) -> F:
    tp = F(2) ** p
    return F(math.ceil(q * tp)) / tp


# --- the ball -----------------------------------------------------------------

class C:
    """A complex ball: exact Gaussian-rational centre, exact rational radius."""

    __slots__ = ("cre", "cim", "rad")

    def __init__(self, cre, cim, rad=0):
        self.cre, self.cim, self.rad = F(cre), F(cim), F(rad)
        assert self.rad >= 0

    def __repr__(self):
        return f"Ball({float(self.cre):.6g}+{float(self.cim):.6g}i, r={float(self.rad):.3g})"


def _absc_upper(x: C) -> F:
    return sqrt_upper(x.cre * x.cre + x.cim * x.cim)


def _absc_lower(x: C) -> F:
    return sqrt_lower(x.cre * x.cre + x.cim * x.cim)


def cexact(q, r) -> C:
    return C(q, r, 0)


def cadd(x: C, y: C) -> C:
    return C(x.cre + y.cre, x.cim + y.cim, x.rad + y.rad)


def cneg(x: C) -> C:
    return C(-x.cre, -x.cim, x.rad)


def cmul(x: C, y: C) -> C:
    """`|c1|r2 + |c2|r1 + r1r2`, every modulus an upper bound.

    This is the whole point of the change: the radius grows by the true
    first-order rate and carries no rotation penalty, so `powI`'s repeated
    squaring does not wrap.
    """
    cre = x.cre * y.cre - x.cim * y.cim
    cim = x.cre * y.cim + x.cim * y.cre
    rad = F(0)
    if y.rad:
        rad += _absc_upper(x) * y.rad
    if x.rad:
        rad += _absc_upper(y) * x.rad
    if x.rad and y.rad:
        rad += x.rad * y.rad
    return C(cre, cim, rad)


def chalve(x: C) -> C:
    return C(x.cre / 2, x.cim / 2, x.rad / 2)


def ccoarsen(p: int, x: C) -> C:
    """Round the centre to `p` bits; the displacement goes into the radius."""
    tp = F(2) ** p
    nre = F(round(x.cre * tp)) / tp
    nim = F(round(x.cim * tp)) / tp
    disp = sqrt_upper((nre - x.cre) ** 2 + (nim - x.cim) ** 2)
    return C(nre, nim, _ceil_bits(x.rad + disp, p))


def cinflate(x: C, r) -> C:
    return C(x.cre, x.cim, x.rad + abs(F(r)))


def smulQ(q, x: C) -> C:
    q = F(q)
    return C(q * x.cre, q * x.cim, abs(q) * x.rad)


def normBound(x: C) -> F:
    """`|c| + r` — no L1 slop, and the radius is counted once, not twice."""
    return _absc_upper(x) + x.rad


def normLower(x: C) -> F:
    lo = _absc_lower(x) - x.rad
    return lo if lo > 0 else F(0)


def invC(x: C) -> C:
    """`1/B` for a ball not containing 0: centre `1/c`, radius `r/(|c|(|c|-r))`."""
    d = x.cre * x.cre + x.cim * x.cim
    assert d > 0
    centre = C(x.cre / d, -x.cim / d, 0)
    if not x.rad:
        return centre
    lo = _absc_lower(x)
    assert lo > x.rad, "ball contains 0; inverse is unbounded"
    gap_lo = lo - x.rad
    centre.rad = sqrt_upper((x.rad / (lo * gap_lo)) ** 2)
    return centre


def inv5sBox(S: C) -> C:
    return cmul(cexact(5, 0), cadd(cexact(1, 0), cneg(S)))


# --- real intervals, kept as-is, converted to balls on entry -------------------
#
# `logQ` is a real-interval computation with no rotation in it, so there is
# nothing for a ball to buy there; it is imported from the box mirror unchanged
# and converted once.

import importlib
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
_box = importlib.import_module("61_rung3_mirror")

logQ = _box.logQ


def from_interval(iv) -> C:
    """A real interval as a ball on the real axis: centre the midpoint, radius
    the half-width.  Exact — no enclosure is lost."""
    mid = (iv.lo + iv.hi) / 2
    return C(mid, 0, (iv.hi - iv.lo) / 2)


def from_box(relo, rehi, imlo, imhi) -> C:
    """The minimal ball around a rectangle.

    For a degenerate rectangle — which every big box and grid site is, being a
    segment of the frontier — this is exact in radius: the enclosing ball of a
    segment has radius half its length.
    """
    relo, rehi, imlo, imhi = F(relo), F(rehi), F(imlo), F(imhi)
    hre, him = (rehi - relo) / 2, (imhi - imlo) / 2
    centre = ((relo + rehi) / 2, (imlo + imhi) / 2)
    # Degenerate in one direction — which every frontier site is — needs no
    # square root, so the conversion is exact rather than rounded outward.
    if not hre:
        return C(*centre, him)
    if not him:
        return C(*centre, hre)
    return C(*centre, sqrt_upper(hre * hre + him * him))


# --- the exp tower, in balls --------------------------------------------------

def powI(x: C, m: int) -> C:
    r = cexact(1, 0)
    for _ in range(m):
        r = cmul(r, x)
    return r


def expSumC(x: C, m: int) -> C:
    acc = cexact(0, 0)
    for i in range(m):
        acc = cadd(acc, smulQ(F(1, math.factorial(i)), powI(x, i)))
    return acc


def expSmall(n: int, x: C) -> C:
    return cinflate(expSumC(x, n),
                    normBound(x) ** n * F(n + 1, math.factorial(n) * n))


def expCr(n: int, p: int, k: int, x: C) -> C:
    if k == 0:
        return ccoarsen(p, expSmall(n, x))
    y = expCr(n, p, k - 1, chalve(x))
    return ccoarsen(p, cmul(y, y))


def dirichletTermBox2(nLog, nExp, p, kL, kE, m, S: C) -> C:
    return expCr(nExp, p, kE,
                 cmul(cneg(S), from_interval(logQ(nLog, kL, F(m)))))


KAPPA_I = _box.KAPPA_I
KAPPA_C = from_interval(KAPPA_I)


def coeffBox(m: int) -> C:
    j = m % 5
    if j == 1:
        return cexact(1, 0)
    if j == 2:
        return KAPPA_C
    if j == 3:
        return cneg(KAPPA_C)
    if j == 4:
        return cexact(-1, 0)
    return cexact(0, 0)


_spf = _box._spf


def cpowBox(m, S: C, nLog=32, nExp=20, p=64, kE=10, cache=None) -> C:
    if cache is None:
        cache = {}
    if m in cache:
        return cache[m]
    f = _spf(m) if m > 1 else m
    if m <= 1 or f == m:
        v = dirichletTermBox2(nLog, nExp, p, m.bit_length(), kE, m, S)
    else:
        a, b = f, m // f
        v = ccoarsen(p, cmul(cpowBox(a, S, nLog, nExp, p, kE, cache),
                             cpowBox(b, S, nLog, nExp, p, kE, cache)))
    cache[m] = v
    return v


def term_chain(m, S: C, nLog=32, nExp=20, p=64, kE=10, cache=None) -> C:
    if m % 5 == 0:
        return cexact(0, 0)
    return cmul(coeffBox(m), cpowBox(m, S, nLog, nExp, p, kE, cache))
