"""`Leaves.lean`, mirrored operation for operation in integers.

## Why this module exists

`o9_leaf.py` mirrors `Iv.lean` and `Phi.lean` faithfully, but computes the
*transcendental leaves* — `sin`, `cos`, `sinh`, `cosh`, `√2`, `sin(√2/2)`,
`cos(√2/2)` — with Arb at 300 bits, rounded outward onto the `2^-64` grid with
a 4-ulp pad.  That is not what the kernel does.  `BandCert/Leaves.lean` builds
them from truncated Taylor series with `hornerI`, widens by one ulp, and for
arguments outside `[-1,1]` reduces modulo a `2^-64` enclosure of `2π` and
doubles twice.  Lean's leaves are **wider**, so its enclosures are wider, so
cells the Arb model decides the kernel need not.

That gap was written down as a caveat before any Lean build existed.  The first
build (2026-08-13) measured it: `decide +kernel` returned `false` on 7 of 9
chunks of a table the model predicted would pass 344 of 344.  The mathematics
is unaffected — `Dam ≤ c·y²` is true at Arb grade — but the *table* was an
artifact of a too-narrow model.

So this module computes leaves the way the kernel computes them, with no Arb
anywhere in the path.  Every function below corresponds to one definition in
`Leaves.lean` and is named after it.

## The control that makes this worth anything

A generator that only checks itself can only ever confirm itself.  The
round-trip in `tests/test_o9_leaves_kernel.py` emits `#eval` for a sample of
leaves, runs Lean, and asserts the **integers are identical** to the ones
produced here.  Without that, "mirrors Lean" is a claim about intent.

Nothing in this module is a result, and nothing here is evidence about RH.
"""

from __future__ import annotations

from fractions import Fraction as F

from o9_leaf import SO, Iv, ofInt, ofQ

__all__ = [
    "SQ2",
    "coshL",
    "cosL",
    "hornerI",
    "piqa",
    "piqb",
    "PI2iv",
    "sinCosIv",
    "sinCosSmall",
    "sinhCoshSmall",
    "sinhL",
    "sinL",
    "shcSmall",
    "kernel_leaves",
]

# ---------------------------------------------------------------------------
# Coefficient lists — Leaves.lean §"Coefficient lists", verbatim
# ---------------------------------------------------------------------------

sinL: list[tuple[int, int]] = [
    (1, 1), (-1, 6), (1, 120), (-1, 5040), (1, 362880), (-1, 39916800),
    (1, 6227020800), (-1, 1307674368000), (1, 355687428096000),
    (-1, 121645100408832000), (1, 51090942171709440000),
]

cosL: list[tuple[int, int]] = [
    (1, 1), (-1, 2), (1, 24), (-1, 720), (1, 40320), (-1, 3628800),
    (1, 479001600), (-1, 87178291200), (1, 20922789888000),
    (-1, 6402373705728000), (1, 2432902008176640000),
]

sinhL: list[tuple[int, int]] = [
    (1, 1), (1, 6), (1, 120), (1, 5040), (1, 362880), (1, 39916800),
    (1, 6227020800), (1, 1307674368000), (1, 355687428096000),
    (1, 121645100408832000), (1, 51090942171709440000),
]

coshL: list[tuple[int, int]] = [
    (1, 1), (1, 2), (1, 24), (1, 720), (1, 40320), (1, 3628800),
    (1, 479001600), (1, 87178291200), (1, 20922789888000),
    (1, 6402373705728000), (1, 2432902008176640000),
]


def hornerI(cs: list[tuple[int, int]], x: Iv) -> Iv:
    """`Leaves.lean`'s `hornerI`: `[] ↦ ofInt 0`, `(n,d)::cs ↦ ofQ n d + hornerI cs x * x`."""
    if not cs:
        return ofInt(0)
    n, d = cs[0]
    return ofQ(n, d).add(hornerI(cs[1:], x).mul(x))


# ---------------------------------------------------------------------------
# The small-argument leaves — valid for |v| <= 1, exactly as in Leaves.lean
# ---------------------------------------------------------------------------

def sinCosSmall(a: Iv) -> tuple[Iv, Iv]:
    x2 = a.sqr()
    return (hornerI(sinL, x2).mul(a).widen(1), hornerI(cosL, x2).widen(1))


def sinhCoshSmall(a: Iv) -> tuple[Iv, Iv]:
    x2 = a.sqr()
    return (hornerI(sinhL, x2).mul(a).widen(1), hornerI(coshL, x2).widen(1))


def shcSmall(a: Iv) -> Iv:
    """`sinh(v)/v` enclosure — the removable branch the 2-D route needs.

    `O9-2D-STATUS.md` §3: this expression is already evaluated inside
    `sinhCoshSmall` on its way to `sinh`, so no new *arithmetic* is required;
    only its truncation lemma is new on the Lean side.  Here it is the same
    integers either way.
    """
    return hornerI(sinhL, a.sqr()).widen(1)


# ---------------------------------------------------------------------------
# Constants — Leaves.lean, verbatim integers (NOT recomputed with Arb)
# ---------------------------------------------------------------------------

sq2n = 26087635650665564424
SQ2 = Iv(sq2n, sq2n + 1)

piqa = 14488038916154245652
piqb = 14488038916154245716
PI2iv = Iv(8 * piqa, 8 * piqb)


# ---------------------------------------------------------------------------
# Argument reduction — Leaves.lean `dbl` and `sinCosIv`
# ---------------------------------------------------------------------------

def dbl(sc: tuple[Iv, Iv]) -> tuple[Iv, Iv]:
    """`(sin 2t, cos 2t)` from `(sin t, cos t)`, exactly `Leaves.lean`'s `dbl`."""
    s, c = sc
    return (s.mul(c).mulInt(2), ofInt(1).sub(s.sqr().mulInt(2)))


def _ediv(a: int, b: int) -> int:
    """Lean's `Int./` on `ℤ` is T-division truncating toward zero.

    `sinCosIv` divides by `ps > 0` and by `4 > 0`.  `Iv.divInt` in
    `o9_leaf.py` already models the directed rounding used for intervals; the
    scalar `k` here is a plain quotient and must match Lean's, so it is
    written out rather than left to Python's floor semantics for negatives.
    """
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b >= 0) else -q


#: Sentinel for the `(topI, topI)` branch — the enclosure that gives up.
topI = Iv(-SO, SO)


def sinCosIv(a: Iv) -> tuple[Iv, Iv]:
    """`(sin, cos)` for an arbitrary argument, `Leaves.lean`'s `sinCosIv`.

    Reduce modulo `2π`, quarter, evaluate the series, double twice.  Returns
    the `topI` pair when the reduced quarter-argument leaves `[-1,1]`, exactly
    as the Lean does — a caller that gets `topI` has learned nothing, which is
    the honest outcome and not an error.
    """
    m = a.lo + a.hi
    ps = PI2iv.lo + PI2iv.hi
    k = _ediv(m + _ediv(ps, 2), ps)
    r = a.sub(PI2iv.mulInt(k))
    t = r.divInt(4)
    if -SO <= t.lo and t.hi <= SO:
        return dbl(dbl(sinCosSmall(t)))
    return (topI, topI)


# ---------------------------------------------------------------------------
# The leaf bundle `phiC` consumes
# ---------------------------------------------------------------------------

def _cell_iv(lo: F, hi: F) -> Iv:
    """The cell `[lo,hi]` as an `Iv`, rounded outward onto the grid."""
    return Iv((lo.numerator * SO) // lo.denominator,
              -((-(hi.numerator * SO)) // hi.denominator))


def _rat_iv(q: F) -> Iv:
    return ofQ(q.numerator, q.denominator)


def kernel_leaves(lo: F, hi: F, y: F) -> dict[str, Iv]:
    """Everything `phiC` needs, computed the way the kernel computes it.

    Drop-in replacement for `o9_leaf.leaves`.  The keys are identical; the
    difference is entirely in how the transcendental entries are produced.

    `sin(s/2)` and `cos(s/2)` go through `sinCosIv` because `s` reaches 60 and
    the small-argument series is only valid on `[-1,1]`.  `sinh(y/2)` and
    `cosh(y/2)` use `sinhCoshSmall` directly: `y ≤ 1/2`, so `y/2 ≤ 1/4` is
    inside the small range and no reduction is needed — which is also why the
    hyperbolic leaves were never the problem.
    """
    X = _cell_iv(lo, hi)
    Y = _rat_iv(y)
    half = X.divInt(2)
    sinX2, cosX2 = sinCosIv(half)
    yhalf = Y.divInt(2)
    sh, ch = sinhCoshSmall(yhalf)
    # sin(√2/2) and cos(√2/2): √2/2 < 1, so the small-argument series applies
    # to the enclosure of √2/2 obtained from SQ2 by the same halving.
    sinc, cosc = sinCosSmall(SQ2.divInt(2))
    return {
        "X": X, "Y": Y,
        "sinh": sh, "cosh": ch,
        "sinX2": sinX2, "cosX2": cosX2,
        "SQ2": SQ2, "SINC": sinc, "COSC": cosc,
    }
