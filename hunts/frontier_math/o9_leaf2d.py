"""O9 as a **two-dimensional** leaf file, in the arithmetic the kernel runs.

`o9_leaf.py` builds the O9 table at the single depth `y = 1/2` and reaches
every other depth through

    D(y,s) / y^2  <=  4 * D(1/2,s),

which is **measured and unproved**.  `O9-SCOPING.md` prices the alternative:
bisect the full box `[28/5, 60] x [0, 1/2]` and drop that lemma.  At Arb grade
it costs 389 leaves against the 1-D route's 344 -- 45 extra leaves to remove an
unproved hypothesis.  This module builds that 2-D table.

## The removable branch, which is the whole trick

Testing `Qim^2 - Qre^2 <= cap * y^2` literally forces every box touching
`y = 0` to establish `Qim^2 <= Qre^2`, which is false at the zeros of
`Qre(0,.)`; the bisection then refines forever along `y = 0`.  Writing it
through `R = Qim/y`,

    Qim^2 - Qre^2 <= cap y^2   <=>   y^2 (R^2 - cap) <= Qre^2,

makes `y = 0` an ordinary point.  `R` is analytic there because `Qim` is odd
in `y`, and the enclosure needs exactly one leaf the package does not already
carry: `shc(x) = sinh(x)/x` at `x = y/2`.  Everything else is the composition
`Phi.lean` already runs.  Concretely, with `z = s + iy`,

    Im(z sin(z/2)) / y = s cos(s/2) shc(y/2)/2 + sin(s/2) cosh(y/2)
    Im(cos(z/2))   / y = -sin(s/2) shc(y/2)/2
    Im(z^2 - 2)    / y = 2 s

so `Im(num)/y` and `Im(den)/y` are elementary, and

    R = ( (Im num / y) * Re den  -  Re num * (Im den / y) ) / |den|^2.

Each of those three identities is checked against a direct high-precision
evaluation in `test_o9_leaf2d.py`.

## What is mirrored

The integer layer (`Iv`, `CIv`) is imported from `o9_leaf.py` unchanged, so
the *arithmetic* is the fixed-point arithmetic at scale `2^64` that
`decide +kernel` runs.

**The leaves are not.**  `o9_leaf.py`'s LEAF CAVEAT applies here verbatim and
is no longer hypothetical: on 2026-08-13 the Lean arm was built for the first
time and `decide +kernel` returned `false` on 7 of the 9 chunks of the 1-D
table that the same leaf layer had declared 344-for-344 with margin to spare
(`O9-2D-STATUS.md` §0).  The transcendental leaves here come from Arb rounded
outward with a 4-ulp pad; `Leaves.lean` builds them from truncated series with
`EIv.widen` and an argument reduction carrying a `2^-64` enclosure of pi, and
is wider.  **A cell count from this module therefore does not predict a kernel
outcome**, and the table below is a table of *candidate* cells.  Making it
predictive means computing the leaves the way `Leaves.lean` does.

## What it is not

Nothing here is kernel-checked; this module *generates* a table and
pre-validates it, which is not the same as Lean accepting it.  `k >= 2` is
untouched.  Nothing here is evidence about RH.
"""

from __future__ import annotations

from fractions import Fraction as F
from pathlib import Path

from o9_leaf import (
    SO,
    Iv,
    _arb,
    _to_iv,
    civ_mul,
    ofInt,
    ofQ,
)

__all__ = [
    "WINDOWS_SUP",
    "WIDEN",
    "INFLATION",
    "O3_CEILING",
    "widened_windows",
    "gaps",
    "leaves2d",
    "qre_iv",
    "r_iv",
    "cell_verdict",
    "build",
    "validate",
    "emit_lean",
    "report",
]

# ---------------------------------------------------------------------------
# The recorded table: windows with their *suprema* (not yet inflated)
# ---------------------------------------------------------------------------

#: `(lo, hi, sup of Dam/y^2)` -- `O9-SCOPING.md` §1, which recomputes each
#: supremum and finds it attained at an interior point (always at `y = 1/2`),
#: which is why an inflation is mandatory rather than cosmetic.
WINDOWS_SUP: list[tuple[F, F, F]] = [
    (F(60653, 10000), F(35257, 5000), F(439643, 25000000)),
    (F(61171, 5000), F(131999, 10000), F(390023, 100000000)),
    (F(11544, 625), F(48583, 2500), F(169313, 100000000)),
    (F(247289, 10000), F(256909, 10000), F(18889, 20000000)),
    (F(309971, 10000), F(159793, 5000), F(6021, 10000000)),
    (F(372701, 10000), F(76463, 2000), F(10431, 25000000)),
    (F(21773, 500), F(27817, 625), F(6123, 20000000)),
    (F(498237, 10000), F(507849, 10000), F(1171, 5000000)),
    (F(280513, 5000), F(570637, 10000), F(9247, 50000000)),
]

#: The operating point recommended by `O9-SCOPING.md` §3.
WIDEN = F(1, 200)
INFLATION = F(6, 5)

#: The widening ceiling O3 imposes: `Kpair >= 39/50` only on `|u| <= 1`, and
#: the widest recorded window is `0.9861`.  Asserted, not remembered.
O3_CEILING = (F(1) - max(hi - lo for lo, hi, _ in WINDOWS_SUP)) / 2

S_LO, S_HI = F(28, 5), F(60)
Y_LO, Y_HI = F(0), F(1, 2)


def widened_windows(
    widen: F = WIDEN, inflation: F = INFLATION
) -> list[tuple[F, F, F]]:
    """`(lo - widen, hi + widen, inflation * sup)` for each recorded window."""
    if widen > O3_CEILING:
        raise ValueError(
            f"widening {widen} exceeds the O3 ceiling {O3_CEILING}; "
            "see O9-SCOPING.md §2, knob B"
        )
    return [(lo - widen, hi + widen, inflation * c) for lo, hi, c in WINDOWS_SUP]


def gaps(widen: F = WIDEN) -> list[tuple[F, F]]:
    """The complement of the widened windows inside `[28/5, 60]`."""
    out: list[tuple[F, F]] = []
    cursor = S_LO
    for lo, hi, _ in widened_windows(widen):
        if lo > cursor:
            out.append((cursor, lo))
        cursor = hi
    if cursor < S_HI:
        out.append((cursor, S_HI))
    return out


# ---------------------------------------------------------------------------
# leaves, including the one new one
# ---------------------------------------------------------------------------

#: Terms of the `sinh(x)/x` series.  On `|x| <= 1/4` the tail after 14 terms
#: is below `2^-160`, far under the `2^-64` grid this table lands on.
_SHC_TERMS = 14
_SHC_TAIL = 160


def _ball(lo: F, hi: F):
    """The Arb ball enclosing `[lo, hi]`."""
    arb = _arb()
    mid, rad = (lo + hi) / 2, (hi - lo) / 2
    return arb(
        arb(mid.numerator) / arb(mid.denominator),
        arb(rad.numerator) / arb(rad.denominator),
    )


def _shc(x):
    """`sinh(x)/x` on a ball, through its series, so `x = 0` is ordinary."""
    arb = _arb()
    total = arb(0)
    fact = 1
    for n in range(_SHC_TERMS):
        if n:
            fact *= (2 * n) * (2 * n + 1)
        total += x ** (2 * n) / fact
    return total + arb(0, arb(2) ** -_SHC_TAIL)


def leaves2d(s_lo: F, s_hi: F, y_lo: F, y_hi: F) -> dict:
    """Every leaf the two compositions need, over the box, as `Iv`.

    **Kernel-grade since 2026-08-13.**  This used to build its leaves with Arb
    at 300 bits and a 4-ulp outward pad, which is not what `Leaves.lean` does;
    the first Lean build refuted a table generated that way on 7 of 9 chunks
    (`O9-2D-STATUS.md` §0).  The leaves now come from `o9_leaves_kernel`, which
    mirrors `Leaves.lean` operation for operation and is pinned against Lean's
    own `#eval` output integer for integer by
    `tests/test_o9_leaves_kernel.py`.

    The Arb path is retained below as `leaves2d_arb` for the width comparison
    only.  It must never feed a table again.
    """
    from o9_leaves_kernel import kernel_leaves2d

    return kernel_leaves2d(s_lo, s_hi, y_lo, y_hi)


def leaves2d_arb(s_lo: F, s_hi: F, y_lo: F, y_hi: F) -> dict:
    """The superseded Arb-plus-pad leaves, kept only to measure the gap.

    Retained because "the model was too narrow" is a claim that should stay
    measurable rather than becoming folklore.  Not for generating tables.
    """
    arb = _arb()
    S = _ball(s_lo, s_hi)
    Y = _ball(y_lo, y_hi)
    half_s, half_y = S / 2, Y / 2
    s2 = arb(2).sqrt()
    return {
        "X": _to_iv(S),
        "Y": _to_iv(Y),
        "sinh": _to_iv(half_y.sinh()),
        "cosh": _to_iv(half_y.cosh()),
        "shc": _to_iv(_shc(half_y)),
        "sinX2": _to_iv(half_s.sin()),
        "cosX2": _to_iv(half_s.cos()),
        "SQ2": _to_iv(s2),
        "SINC": _to_iv((s2 / 2).sin()),
        "COSC": _to_iv((s2 / 2).cos()),
    }


# ---------------------------------------------------------------------------
# the two compositions
# ---------------------------------------------------------------------------


def _parts(L: dict) -> dict:
    """`Re num`, `Im num / y`, `Re den`, `Im den / y`, `|den|^2`, as `Iv`.

    `num` and `den` are exactly `Phi.lean`'s, so `Re(num/den)` below is the
    same `Qre` that `phiC` computes; the `/y` variants are the removable
    branch derived in the module docstring.
    """
    X, Y = L["X"], L["Y"]
    sh, ch, shc = L["sinh"], L["cosh"], L["shc"]
    sn, cs = L["sinX2"], L["cosX2"]

    # sinh(y/2)/y = shc(y/2)/2
    sh_over_y = shc.divInt(2)

    # z*sin(z/2), with z = X + iY and sin(z/2) = (sn*ch, cs*sh)
    re_zsin = X.mul(sn).mul(ch).sub(Y.mul(cs).mul(sh))
    im_zsin_over_y = X.mul(cs).mul(sh_over_y).add(sn.mul(ch))

    # cos(z/2) = (cs*ch, -(sn*sh))
    re_cos = cs.mul(ch)
    im_cos_over_y = sn.mul(sh_over_y).neg()

    # num = 2 * ( z*sin(z/2)*COSC - cos(z/2)*SINC*SQ2 )
    re_num = re_zsin.mul(L["COSC"]).sub(re_cos.mul(L["SINC"]).mul(L["SQ2"])).mulInt(2)
    im_num_over_y = (
        im_zsin_over_y.mul(L["COSC"])
        .sub(im_cos_over_y.mul(L["SINC"]).mul(L["SQ2"]))
        .mulInt(2)
    )

    # den = z^2 - 2 = (X^2 - Y^2 - 2, 2XY)
    re_den = X.sqr().sub(Y.sqr()).sub(ofInt(2))
    im_den_over_y = X.mulInt(2)
    im_den = im_den_over_y.mul(Y)
    den_abs2 = re_den.sqr().add(im_den.sqr())

    return {
        "re_num": re_num,
        "im_num_over_y": im_num_over_y,
        "im_num": im_num_over_y.mul(Y),
        "re_den": re_den,
        "im_den": im_den,
        "im_den_over_y": im_den_over_y,
        "den_abs2": den_abs2,
    }


def qre_iv(L: dict):
    """`Qre = Re(num/den)`, or `None` if the denominator is not separated."""
    p = _parts(L)
    return p["re_num"].mul(p["re_den"]).add(p["im_num"].mul(p["im_den"])).div(
        p["den_abs2"]
    )


def r_iv(L: dict):
    """`R = Qim/y`, or `None`.

    Sign, because it is easy to get wrong and the enclosure is only ever used
    squared, so a wrong sign would never show up in the table: the package's
    `Phi2(s + iy)` has real part `Qre` and imaginary part **`-Qim`** (`Qim` is
    odd in `s` and enters `Dam` only through `Qim^2`).  The composition below
    computes `Im(num/den)/y`, which is therefore `-Qim/y`, and the negation
    puts it back.  `test_o9_leaf2d.py` pins both signs against an independent
    evaluation.
    """
    p = _parts(L)
    return p["im_num_over_y"].mul(p["re_den"]).sub(
        p["re_num"].mul(p["im_den_over_y"])
    ).div(p["den_abs2"]).neg() if _parts_ok(p) else None


def _parts_ok(p: dict) -> bool:
    return p["den_abs2"].lo > 0


# ---------------------------------------------------------------------------
# the cell test
# ---------------------------------------------------------------------------


def cell_verdict(s_lo: F, s_hi: F, y_lo: F, y_hi: F, cap: F):
    """`(ok, mode, margin_ulp)` for one box, in fixed-point arithmetic.

    mode 1: `sup R^2 <= cap`, so `y^2(R^2 - cap) <= 0 <= Qre^2` whatever
            `Qre` does -- the branch that carries every box touching `y = 0`.
    mode 2: `y_hi^2 * (sup R^2 - cap) <= inf Qre^2`.
    """
    L = leaves2d(s_lo, s_hi, y_lo, y_hi)
    R = r_iv(L)
    if R is None:
        return False, 0, 0
    capIv = ofQ(cap.numerator, cap.denominator)
    excess = R.sqr().sub(capIv)
    if excess.hi <= 0:
        return True, 1, -excess.hi
    Q = qre_iv(L)
    if Q is None:
        return False, 0, 0
    qre2 = Q.sqr()
    ysq = y_hi * y_hi
    dsq = ofQ(ysq.numerator, ysq.denominator)
    lhs = dsq.mul(Iv(excess.hi, excess.hi)).hi
    return lhs <= qre2.lo, 2, qre2.lo - lhs


# ---------------------------------------------------------------------------
# the walk
# ---------------------------------------------------------------------------


def _segments(widen: F, inflation: F):
    """`(s_lo, s_hi, cap)` covering `[28/5, 60]`: widened windows, then gaps.

    Cutting at the window endpoints first matters for the same reason it does
    in the 1-D module: bisection midpoints are dyadic and the endpoints are
    not, so a box straddling a boundary would shrink forever without ever
    being wholly inside or wholly outside a window.
    """
    segs = [(lo, hi, c) for lo, hi, c in widened_windows(widen, inflation)]
    segs += [(a, b, F(0)) for a, b in gaps(widen)]
    return sorted(segs)


def build(widen: F = WIDEN, inflation: F = INFLATION, max_depth: int = 40):
    """Adaptive 2-D bisection until every box decides.  Splits the longer side."""
    cells, undecided = [], 0
    stack = [(a, b, Y_LO, Y_HI, c, 0) for a, b, c in _segments(widen, inflation)]
    while stack:
        a, b, c, d, cap, depth = stack.pop()
        ok, mode, margin = cell_verdict(a, b, c, d, cap)
        if ok:
            cells.append(
                {
                    "s_lo": a, "s_hi": b, "y_lo": c, "y_hi": d,
                    "cap": cap, "mode": mode, "margin_ulp": margin,
                    "depth": depth,
                }
            )
            continue
        if depth >= max_depth:
            cells.append(
                {
                    "s_lo": a, "s_hi": b, "y_lo": c, "y_hi": d,
                    "cap": cap, "mode": 0, "margin_ulp": -1, "depth": depth,
                }
            )
            undecided += 1
            continue
        if (b - a) >= (d - c):
            m = (a + b) / 2
            stack.append((a, m, c, d, cap, depth + 1))
            stack.append((m, b, c, d, cap, depth + 1))
        else:
            m = (c + d) / 2
            stack.append((a, b, c, m, cap, depth + 1))
            stack.append((a, b, m, d, cap, depth + 1))
    cells.sort(key=lambda z: (z["s_lo"], z["y_lo"]))
    return {
        "cells": cells,
        "undecided": undecided,
        "max_depth": max(z["depth"] for z in cells),
        "widen": widen,
        "inflation": inflation,
    }


def validate(table=None) -> dict:
    t = table or build()
    ms = [z["margin_ulp"] for z in t["cells"]]
    modes = [z["mode"] for z in t["cells"]]
    return {
        "cells": len(t["cells"]),
        "undecided": t["undecided"],
        "max_depth": t["max_depth"],
        "mode1": modes.count(1),
        "mode2": modes.count(2),
        "min_margin_ulp": min(ms),
        "all_decided": t["undecided"] == 0,
    }


# ---------------------------------------------------------------------------
# emission
# ---------------------------------------------------------------------------

_DATA_HEADER = '''import Zeta23Ext.BandCert.Phi

/-!
# O9 leaf data -- the damage cap table on `[28/5, 60] x [0, 1/2]`

Generated by `hunts/frontier_math/o9_leaf2d.py`.  Unlike the `y = 1/2` table
it replaces, this one carries every depth, so it needs **no** depth-reduction
lemma.  Each leaf records the box (all four endpoints scaled by `2^64`), the
scaled cap, and which of the two tests decides it:

* `mode = 1`: `sup R^2 <= cap` on the box, `R = Qim/y`;
* `mode = 2`: `y_hi^2 * (sup R^2 - cap) <= inf Qre^2`.

Both are the inequality `Qim^2 - Qre^2 <= cap * y^2` written through the
removable branch `R = Qim/y`, which is what makes `y = 0` an ordinary point.
-/

namespace Retention
open BandDual

/-- One leaf of the two-dimensional table. -/
structure O9Box where
  sLo : ℤ
  sHi : ℤ
  yLo : ℤ
  yHi : ℤ
  cap : ℤ
  mode : ℕ
deriving DecidableEq

/-- The recorded leaves. -/
def o9boxes : List O9Box :=
[
'''

_DATA_FOOTER = """]

end Retention
"""


def _scale_lo(q: F) -> int:
    return (q * SO).__floor__()


def _scale_hi(q: F) -> int:
    return -((-(q * SO)).__floor__())


def emit_lean(out_dir: Path | None = None, table=None, chunk: int = 40) -> dict:
    """Write `O9Data2.lean` / `O9Check2.lean`.  Returns what it wrote."""
    t = table or build()
    if t["undecided"]:
        raise ValueError(f"{t['undecided']} undecided cells; refusing to emit")
    out = out_dir or Path(__file__).parent / "zeta23ext" / "Zeta23Ext" / "EForm3"
    out.mkdir(parents=True, exist_ok=True)

    rows = []
    for z in t["cells"]:
        rows.append(
            "  ⟨{}, {}, {}, {}, {}, {}⟩,".format(
                _scale_lo(z["s_lo"]),
                _scale_hi(z["s_hi"]),
                _scale_lo(z["y_lo"]),
                _scale_hi(z["y_hi"]),
                _scale_hi(z["cap"]),
                z["mode"],
            )
        )
    (out / "O9Data2.lean").write_text(
        _DATA_HEADER + "\n".join(rows) + "\n" + _DATA_FOOTER, encoding="utf-8"
    )

    n = len(t["cells"])
    chunks = [
        f"theorem o9_box_chunk{i} : "
        f"o9Walk2 (o9boxes.drop {i * chunk} |>.take {chunk}) = true := by\n"
        f"  decide +kernel"
        for i in range((n + chunk - 1) // chunk)
    ]
    (out / "O9Check2.lean").write_text(
        _CHECK_HEADER + "\n".join(chunks) + "\n\nend Retention\n", encoding="utf-8"
    )
    return {"cells": n, "chunks": len(chunks), "dir": str(out)}


_CHECK_HEADER = '''import Zeta23Ext.EForm3.O9Data2
import Zeta23Ext.EForm3.O9Comp

/-!
# Running the two-dimensional O9 checker

`o9Walk2` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.

`rIv`, `qreIv` and `sqrScaled` come from `O9Comp.lean`, whose integers are
pinned against this generator's own composition by
`tests/test_o9_leaves_kernel.py`.  A green `decide +kernel` here says the
recorded table is consistent with the kernel's arithmetic; it does **not** yet
say anything about `Dam`, because the `_mem` seam lemmas are not written.  The
two claims are different and the difference is the point.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Re-evaluate the box and check whichever test it claims. -/
def o9Box (b : O9Box) : Bool :=
  match rIv b.sLo b.sHi b.yLo b.yHi, qreIv b.sLo b.sHi b.yLo b.yHi with
  | some r, some q =>
      let excess := (EIv.sqr (some r)).sub (some ⟨b.cap, b.cap⟩)
      match excess with
      | none => false
      | some e =>
        if b.mode = 1 then decide (e.hi ≤ 0)
        else
          match EIv.mul (EIv.sqrScaled b.yHi) (some ⟨e.hi, e.hi⟩),
                EIv.sqr (some q) with
          | some l, some q2 => decide (l.hi ≤ q2.lo)
          | _, _ => false
  | _, _ => false

def o9Walk2 : List O9Box → Bool
  | [] => true
  | b :: bs => o9Box b && o9Walk2 bs

'''


# ---------------------------------------------------------------------------
# report
# ---------------------------------------------------------------------------


def report() -> dict:
    print("=" * 74)
    print("O9 as a 2-D leaf table, in the kernel's fixed-point arithmetic")
    print("=" * 74)
    print(f"\n  widening   {WIDEN}   (O3 ceiling {O3_CEILING})")
    print(f"  inflation  {INFLATION}")
    t = build()
    v = validate(t)
    print(f"\n  cells          {v['cells']}")
    print(f"  undecided      {v['undecided']}")
    print(f"  max depth      {v['max_depth']}")
    print(f"  mode 1 / 2     {v['mode1']} / {v['mode2']}")
    print(f"  min margin     {v['min_margin_ulp']} ulp")
    return v


if __name__ == "__main__":
    report()
