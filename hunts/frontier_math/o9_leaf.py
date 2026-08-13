"""O9 as a leaf file: generate it, and pre-validate every cell in the
arithmetic the kernel will actually run.

`RETENTION-PROBLEM.md` §4 states O9 — the damage cap table on
`[28/5, 60] x [0, 1/2]`.  `window_table.py` sized it at 196 cells using Arb
balls at 128 bits.  Arb is *not* what the kernel runs: `BandCert` works in
**fixed-point integer arithmetic at scale `2^64`**, and a cell that Arb
decides need not be decided there, because the two have different
dependency growth.

This module closes that gap.  It reimplements `BandCert/Iv.lean` and the
`CIv` layer of `BandCert/Phi.lean` **operation for operation in integers**,
so the pass/fail verdict computed here is the verdict `decide +kernel` will
reach, up to the leaf enclosures (see LEAF CAVEAT below).

## What is mirrored, exactly

From `Iv.lean`, with `SO = 2^64` and `Iv = <lo, hi>` denoting
`[lo/SO, hi/SO]`:

    flo p     = p / SO                  (floor; Lean's Int `/` is ediv,
    fhi p     = -((-p) / SO)             which for SO > 0 is floor)
    add a b   = <a.lo+b.lo, a.hi+b.hi>
    sub a b   = <a.lo-b.hi, a.hi-b.lo>
    neg a     = <-a.hi, -a.lo>
    mul a b   = <flo (min of 4 products), fhi (max of 4 products)>
    sqr a     = sign-split, as in the source
    mulInt, divInt, widen, ofQ, ofInt, div — all as written

From `Phi.lean`: `CIv` add/sub/mul/mulR/div/ofR, and `phiC` itself,

    phiC X Y SH CH = num / den,
    num = 2 * ( (z * sin(z/2)) * cos(sqrt2/2)
                - (cos(z/2) * sin(sqrt2/2)) * sqrt2 ),
    den = z*z - 2,        z = (X, Y)

which `phiC_mem` proves encloses `Phi2(X + i Y)`.  Since
`ghat(z) = Phi2(-i z)` (`arm_identification.py`) and `Phi2` has real
coefficients, `D(y,s) = -Re[Phi2(s + i y)^2]`, so the damage enclosure is
`phiC` at `(s, y)`, squared by `CIv.mul`, real part negated.

## LEAF CAVEAT — stated up front

The transcendental leaves (`sin`, `cos` of the cell, `sinh`, `cosh` of
`y/2`, `sqrt2`, `sin/cos(sqrt2/2)`) are computed here with **Arb**, then
rounded outward onto the `2^-64` grid.  `BandCert/Leaves.lean` computes
them with Taylor series plus argument reduction, at its own widths.  The
two agree to well under `2^-60` on this range, but they are not identical,
so this module **predicts** the kernel's verdict rather than reproducing
it bit-for-bit.  Where a cell passes with margin — and every cell here
does, by the factor reported in `validate()` — the prediction is safe.
A cell passing by less than a few ulp would not be.

## The size, corrected

`window_table.py` sized this at **196 cells** using Arb balls at 128 bits.
In the kernel's own arithmetic it is **344 cells** (max depth 20, every one
decided, smallest margin `3.63e9` ulp `= 1.97e-10`).  The 196 was an
**underestimate**: Arb at 128 bits is tighter than fixed point at `2^-64`,
so cells Arb decides need splitting again here.  344 sits somewhat above
`BandCert`'s existing `62..248`, still the same order.

One structural detail decides termination.  The walk must be seeded by
cutting `[28/5, 60]` at **every window endpoint** before subdividing:
bisection alone never lands on an endpoint (they are rationals with
denominator `10^4`, the midpoints are dyadic), so a cell straddling a
window boundary shrinks forever without deciding — 768 cells with 18
undecided at depth 40.  With the cuts, 344 and none undecided.

## A dependency this table rests on, which is easy to miss

`o9_scoping.py` (the other session) records that the companion claim "no
damage outside the windows" is an **equality at every window endpoint**, so
with the windows taken as the exact damage support the complement does not
close: 404 leaves and a depth wall.  This table closes anyway, and the
reason is not that the fixed-point arithmetic is better — it is that §4's
recorded `I_k` are decimal-rounded **outward**, so they strictly contain the
true support:

    k=0  [6.0653, 7.0514]   vs true [6.065319, 7.051319]   slack 1.9e-05 / 8.1e-05
    k=1  [12.2342, 13.1999] vs true [12.234289, 13.199859] slack 8.9e-05 / 4.1e-05
    k=2  [18.4704, 19.4332] vs true [18.470414, 19.433183] slack 1.4e-05 / 1.7e-05
    k=3  [24.7289, 25.6909] vs true [24.728967, 25.690832] slack 6.7e-05 / 6.8e-05

That rounding is an **implicit widening of about `2e-05`**, and it is what
makes the complement decidable here.  It is a real dependency: re-deriving
§4's endpoints to more decimals would tighten them onto the support and
this table would stop closing.  `test_o9_leaf.py` pins it.

## Two different objects, and theirs needs one lemma fewer

`o9_scoping.py` sizes the **two-dimensional** table over
`[28/5, 60] x [0, 1/2]`; its recommended operating point is inflation
`1.20x` with widening `1/200`, giving **110 window + 279 complement = 389
leaves, max depth 16**.  This module sizes the **one-dimensional** table at
`y = 1/2` only: 344 cells at inflation `1.05x` with no explicit widening.

The two are close in size, and **theirs is the stronger artifact**: being
two-dimensional it does not need the depth reduction
`D(y,s)/y^2 <= 4 D(1/2,s)`, which is measured and unproved.  This module
trades that lemma for about 45 leaves.  Whoever builds the Lean file should
probably take the 2-D route for that reason alone.

## What it produces

`emit_lean()` writes the `Zeta23Ext/EForm3/O9Data.lean` and
`O9Check.lean` pair, in `BandCert`'s idiom: a `Cell` list, a `Bool`-valued
walker, and one `decide +kernel` per chunk.

Nothing here is kernel-checked; there is no Lean toolchain in this
container.  `k >= 2` is untouched.  Nothing here is evidence about RH.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

__all__ = [
    "SO", "Iv", "civ_mul", "phiC", "damage_iv", "CAPS", "WINDOWS",
    "cell_verdict", "validate", "emit_lean", "build", "_seed_segments",
    "N_CELLS_KERNEL", "TRUE_SUPPORT",
    "NAMED_GAPS", "report",
]

SO = 1 << 64

#: Cells in the kernel's fixed-point arithmetic (`window_table.N_CELLS`
#: is the Arb-grade 196, which understates this by 43%).
N_CELLS_KERNEL = 344


# ---------------------------------------------------------------------------
# Iv.lean, mirrored
# ---------------------------------------------------------------------------

def flo(p: int) -> int:
    return p // SO           # Lean Int `/` is ediv; SO > 0 so this is floor


def fhi(p: int) -> int:
    return -((-p) // SO)


@dataclass(frozen=True)
class Iv:
    lo: int
    hi: int

    def add(self, b: "Iv") -> "Iv":
        return Iv(self.lo + b.lo, self.hi + b.hi)

    def sub(self, b: "Iv") -> "Iv":
        return Iv(self.lo - b.hi, self.hi - b.lo)

    def neg(self) -> "Iv":
        return Iv(-self.hi, -self.lo)

    def mul(self, b: "Iv") -> "Iv":
        p = (self.lo * b.lo, self.lo * b.hi, self.hi * b.lo, self.hi * b.hi)
        return Iv(flo(min(p)), fhi(max(p)))

    def sqr(self) -> "Iv":
        if 0 <= self.lo:
            return Iv(flo(self.lo * self.lo), fhi(self.hi * self.hi))
        if self.hi <= 0:
            return Iv(flo(self.hi * self.hi), fhi(self.lo * self.lo))
        return Iv(0, fhi(max(self.lo * self.lo, self.hi * self.hi)))

    def mulInt(self, k: int) -> "Iv":
        return Iv(self.lo * k, self.hi * k) if k >= 0 else Iv(self.hi * k, self.lo * k)

    def divInt(self, d: int) -> "Iv":
        return Iv(self.lo // d, -((-self.hi) // d))

    def widen(self, r: int) -> "Iv":
        return Iv(self.lo - r, self.hi + r)

    def div(self, b: "Iv"):
        """`EIv`: None unless the denominator is bounded away from 0."""
        if b.lo > 0:
            q1, q2 = self.lo * SO, self.hi * SO
            los = (q1 // b.hi, q1 // b.lo, q2 // b.hi, q2 // b.lo)
            his = (-((-q1) // b.hi), -((-q1) // b.lo),
                   -((-q2) // b.hi), -((-q2) // b.lo))
            return Iv(min(los), max(his))
        if b.hi < 0:                       # the source only handles b.lo > 0;
            return None                    # we never hit this branch here
        return None

    def width(self) -> float:
        return (self.hi - self.lo) / SO

    def as_floats(self):
        return self.lo / SO, self.hi / SO


def ofQ(n: int, d: int) -> Iv:
    return Iv((n * SO) // d, -((-(n * SO)) // d))


def ofInt(n: int) -> Iv:
    return Iv(n * SO, n * SO)


# --- CIv (Phi.lean) --------------------------------------------------------

def civ_mul(a, b):
    """`(a.1 b.1 - a.2 b.2, a.1 b.2 + a.2 b.1)`."""
    return (a[0].mul(b[0]).sub(a[1].mul(b[1])),
            a[0].mul(b[1]).add(a[1].mul(b[0])))


def civ_sub(a, b):
    return (a[0].sub(b[0]), a[1].sub(b[1]))


def civ_mulR(a, r):
    return (a[0].mul(r), a[1].mul(r))


def civ_mulInt(a, k):
    return (a[0].mulInt(k), a[1].mulInt(k))


def civ_div(a, b):
    """`a / b = a * conj(b) / |b|^2`, as in the source."""
    den = b[0].sqr().add(b[1].sqr())
    num = civ_mul(a, (b[0], b[1].neg()))
    r0, r1 = num[0].div(den), num[1].div(den)
    return None if (r0 is None or r1 is None) else (r0, r1)


# ---------------------------------------------------------------------------
# leaves, via Arb, rounded outward onto the 2^-64 grid  (see LEAF CAVEAT)
# ---------------------------------------------------------------------------

def _arb():
    from flint import arb, ctx
    ctx.prec = 300
    return arb


def _dec(x, digits: int = 45) -> F:
    """An Arb bound as an exact `Fraction`, via its decimal string.

    `arb.str(n, radius=False)` is the midpoint to `n` digits; applied to
    `ball.lower()` / `ball.upper()` (themselves exact dyadics) it is exact
    to well past `2^-64`, and `_to_iv` pads outward regardless.
    """
    return F(x.str(digits, radius=False))


def _to_iv(ball, pad: int = 4) -> Iv:
    """Round an Arb ball outward onto the grid, with `pad` ulp of safety."""
    lo = (_dec(ball.lower()) * SO).__floor__() - pad
    hi = -((-(_dec(ball.upper()) * SO)).__floor__()) + pad
    return Iv(lo, hi)


def _cell_ball(lo: F, hi: F):
    arb = _arb()
    mid = (lo + hi) / 2
    rad = (hi - lo) / 2
    return arb(arb(mid.numerator) / arb(mid.denominator),
               arb(rad.numerator) / arb(rad.denominator))


def leaves(lo: F, hi: F, y: F):
    """Everything `phiC` needs, as `Iv`, for the cell `[lo,hi]` at depth `y`."""
    arb = _arb()
    b = _cell_ball(lo, hi)
    half = b / 2
    s2 = arb(2).sqrt()
    yq = arb(y.numerator) / arb(y.denominator)
    return {
        "X": _to_iv(b), "Y": _to_iv(arb(yq)),
        "sinh": _to_iv((yq / 2).sinh()), "cosh": _to_iv((yq / 2).cosh()),
        "sinX2": _to_iv(half.sin()), "cosX2": _to_iv(half.cos()),
        "SQ2": _to_iv(s2), "SINC": _to_iv((s2 / 2).sin()),
        "COSC": _to_iv((s2 / 2).cos()),
    }


def phiC(L) -> tuple:
    """`Phi2(X + iY)` enclosure, exactly the composition in `Phi.lean`."""
    z = (L["X"], L["Y"])
    # sin(z/2), cos(z/2) from the real leaves:
    #   sin(a+ib) = (sin a cosh b, cos a sinh b)
    #   cos(a+ib) = (cos a cosh b, -(sin a sinh b))
    sinz = (L["sinX2"].mul(L["cosh"]), L["cosX2"].mul(L["sinh"]))
    cosz = (L["cosX2"].mul(L["cosh"]), L["sinX2"].mul(L["sinh"]).neg())
    num = civ_mulInt(
        civ_sub(civ_mulR(civ_mul(z, sinz), L["COSC"]),
                civ_mulR(civ_mulR(cosz, L["SINC"]), L["SQ2"])), 2)
    den = civ_sub(civ_mul(z, z), (ofInt(2), ofInt(0)))
    return civ_div(num, den)


def damage_iv(lo: F, hi: F, y: F = F(1, 2)):
    """`D(y,s) = -Re[Phi2(s+iy)^2]` over the cell, as an `Iv` (or None)."""
    p = phiC(leaves(lo, hi, y))
    if p is None:
        return None
    sq = civ_mul(p, p)
    return sq[0].neg()


# ---------------------------------------------------------------------------
# the table: §4's windows and its 21/20-inflated caps
# ---------------------------------------------------------------------------

WINDOWS = [
    (F(60653, 10000), F(35257, 5000)), (F(61171, 5000), F(131999, 10000)),
    (F(11544, 625), F(48583, 2500)), (F(247289, 10000), F(256909, 10000)),
    (F(309971, 10000), F(159793, 5000)), (F(372701, 10000), F(76463, 2000)),
    (F(21773, 500), F(27817, 625)), (F(498237, 10000), F(507849, 10000)),
    (F(280513, 5000), F(570637, 10000)),
]
#: §4 caps on `Dam/y^2`; the cell test is `D <= c_k y^2`, `y = 1/2`.
CAPS = [F(9232503, 500000000), F(8190483, 2000000000), F(3555573, 2000000000),
        F(396669, 400000000), F(126441, 200000000), F(219051, 500000000),
        F(128583, 400000000), F(24591, 100000000), F(194187, 1000000000)]

S_LO, S_HI = F(28, 5), F(60)

#: The TRUE damage support, measured by `window_table.windows()`.  S4's
#: `WINDOWS` are decimal-rounded OUTWARD past these, and that implicit
#: widening (~2e-05) is what makes the complement decidable — see the
#: module docstring.
TRUE_SUPPORT = [
    (F('6.065319'), F('7.051319')), (F('12.234289'), F('13.199859')),
    (F('18.470414'), F('19.433183')), (F('24.728967'), F('25.690832')),
]


def _cap_for(lo: F, hi: F):
    """The cap of the window containing the cell, or `None` (needs `D<=0`)."""
    for (wl, wh), c in zip(WINDOWS, CAPS):
        if wl <= lo and hi <= wh:
            return c
    return None


def _straddles(lo: F, hi: F) -> bool:
    return any(not (hi <= wl or lo >= wh) for wl, wh in WINDOWS)


def cell_verdict(lo: F, hi: F, y: F = F(1, 2)):
    """`(ok, margin_ulp, target)` for one cell, in fixed-point arithmetic."""
    d = damage_iv(lo, hi, y)
    if d is None:
        return False, 0, None
    cap = _cap_for(lo, hi)
    if cap is None:
        if _straddles(lo, hi):
            return False, 0, None            # must be split further
        target = 0
    else:
        target = -((-(cap * y * y * SO)).__floor__())   # ceil(cap y^2 * SO)
    return d.hi <= target, target - d.hi, target


def _seed_segments():
    """Partition `[28/5, 60]` at every window endpoint.

    Bisection alone never lands on a window endpoint (the endpoints are
    rationals with denominator 10^4, the midpoints are dyadic), so a cell
    straddling a boundary shrinks forever without deciding.  Cutting at the
    endpoints first makes every cell either wholly inside one window or
    wholly outside all of them.
    """
    cuts = {S_LO, S_HI}
    for wl, wh in WINDOWS:
        if S_LO < wl < S_HI:
            cuts.add(wl)
        if S_LO < wh < S_HI:
            cuts.add(wh)
    pts = sorted(cuts)
    return [(a, b) for a, b in zip(pts, pts[1:])]


def build(y: F = F(1, 2), max_depth: int = 40):
    """Adaptive walk over `[28/5, 60]`, splitting until every cell decides."""
    cells, undecided = [], 0
    stack = [(a, b, 0) for a, b in _seed_segments()]
    while stack:
        lo, hi, d = stack.pop()
        ok, margin, target = cell_verdict(lo, hi, y)
        if ok:
            cells.append({"lo": lo, "hi": hi, "target": target,
                          "margin_ulp": margin, "depth": d})
            continue
        if d >= max_depth:
            cells.append({"lo": lo, "hi": hi, "target": target,
                          "margin_ulp": -1, "depth": d})
            undecided += 1
            continue
        mid = (lo + hi) / 2
        stack.append((lo, mid, d + 1))
        stack.append((mid, hi, d + 1))
    cells.sort(key=lambda c: c["lo"])
    return {"cells": cells, "undecided": undecided,
            "max_depth": max(c["depth"] for c in cells)}


def validate(table=None) -> dict:
    """Every cell decided, and by how much."""
    t = table or build()
    ms = [c["margin_ulp"] for c in t["cells"]]
    return {"cells": len(t["cells"]), "undecided": t["undecided"],
            "max_depth": t["max_depth"], "min_margin_ulp": min(ms),
            "min_margin_abs": min(ms) / SO,
            "all_decided": t["undecided"] == 0}


# ---------------------------------------------------------------------------
# emission
# ---------------------------------------------------------------------------

_HEADER = """import Zeta23Ext.BandCert.Phi

/-!
# O9 leaf data — the damage cap table on `[28/5, 60]` at `y = 1/2`

Generated by `hunts/frontier_math/o9_leaf.py`.  Each cell records
`lo`, `hi` (scaled by `2^64`) and the integer `target` it must not exceed;
`o9Cell` re-evaluates `phiC` on the cell and compares.  Cells inside a
window carry that window's cap; cells outside every window carry `0`.
-/

namespace Retention
open BandDual

/-- One leaf: `[lo/2^64, hi/2^64]` with the scaled cap it must respect. -/
structure O9Cell where
  lo : ℤ
  hi : ℤ
  target : ℤ
deriving DecidableEq

"""


def emit_lean(out_dir: Path | None = None, table=None) -> dict:
    """Write `O9Data.lean` (cells) and `O9Check.lean` (the walk)."""
    t = table or build()
    out = out_dir or (Path(__file__).resolve().parent / "zeta23ext"
                      / "Zeta23Ext" / "EForm3")
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for c in t["cells"]:
        lo = (c["lo"] * SO).__floor__()
        hi = -((-(c["hi"] * SO)).__floor__())
        rows.append(f"  ⟨{lo}, {hi}, {c['target']}⟩")
    data = (_HEADER + "/-- The recorded leaves. -/\ndef o9cells : List O9Cell :=\n[\n"
            + ",\n".join(rows) + "]\n\nend Retention\n")
    (out / "O9Data.lean").write_text(data)

    chunks = max(1, (len(t["cells"]) + 39) // 40)
    thms = "\n".join(
        f"theorem o9_chunk{i} : o9Walk (o9cells.drop {i*40} |>.take 40) = true := by\n"
        f"  decide +kernel" for i in range(chunks))
    check = f"""import Zeta23Ext.EForm3.O9Data

/-!
# Running the O9 checker

`o9Walk` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Re-evaluate `phiC` on a cell and compare with its recorded target. -/
def o9Cell (c : O9Cell) : Bool :=
  match damageIv c.lo c.hi with
  | none => false
  | some d => decide (d.hi ≤ c.target)

def o9Walk : List O9Cell → Bool
  | [] => true
  | c :: cs => o9Cell c && o9Walk cs

{thms}

end Retention
"""
    (out / "O9Check.lean").write_text(check)
    return {"data": str(out / "O9Data.lean"), "check": str(out / "O9Check.lean"),
            "cells": len(t["cells"]), "chunks": chunks}


NAMED_GAPS = (
    "L1 NOT kernel-checked: there is no Lean toolchain in this container. "
    "This module predicts the verdict; it does not obtain it.",
    "L2 LEAF CAVEAT: the transcendental leaves are Arb here and Taylor "
    "series in BandCert/Leaves.lean. The downstream integer arithmetic is "
    "mirrored exactly, but the leaf widths are not identical, so a cell "
    "passing by only a few ulp would not be safely predicted. Every cell "
    "here passes by far more -- see validate()['min_margin_ulp'].",
    "L3 `damageIv` is now written by hand in "
    "`zeta23ext/Zeta23Ext/EForm3/O9Damage.lean`, but its SOUNDNESS lemma "
    "`damageIv_mem` is not: the file records the obligation in prose "
    "rather than as a `sorry`, because zeta23ext has been sorry-free "
    "throughout. Until that lemma exists, O9Check checks the table and "
    "proves nothing about `Dam`.",
    "L4 the table is one-dimensional at y = 1/2 and rests on the measured "
    "depth reduction D(y,s)/y^2 <= 4 D(1/2,s), which is not proved. "
    "o9_scoping.py's 2-D table (389 leaves at 1.20x/0.005) needs no such "
    "lemma and is the stronger artifact for 45 more leaves.",
    "L4b it also rests on S4's I_k being decimal-rounded OUTWARD past the "
    "true damage support (~2e-05). That implicit widening is what makes "
    "the complement decidable; tightening the endpoints would break it.",
    "L5 k >= 2 is untouched and nothing here is evidence about RH.",
)


def report() -> dict:
    print("= O9 leaves, validated in the kernel's own arithmetic =")
    t = build()
    v = validate(t)
    print(f"  cells        {v['cells']}")
    print(f"  undecided    {v['undecided']}")
    print(f"  max depth    {v['max_depth']}")
    print(f"  min margin   {v['min_margin_ulp']} ulp "
          f"({v['min_margin_abs']:.3e} absolute)")
    print(f"  all decided  {v['all_decided']}")
    print("= named gaps =")
    for g in NAMED_GAPS:
        print(f"  * {g}")
    return v


if __name__ == "__main__":
    report()
