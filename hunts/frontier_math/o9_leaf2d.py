"""O9 as a genuinely two-variable leaf table, with no depth-reduction lemma.

`o9_leaf.py` builds the damage table at the single depth `y = 1/2` and needs

    D(y,s) / y^2  <=  4 * D(1/2, s)        for all y in [0,1/2]

to reach the other depths.  That lemma is **measured, not proved**, and it is
the only unproved step in that route.  This module removes it by checking the
whole rectangle `[28/5, 60] x [0, 1/2]` directly.

## Why a naive 2-D table cannot work

The obligation is `Dam y s <= c_k y^2`.  Evaluating that on a box whose `y`
range touches `0` compares an upper bound for `Qim^2 - Qre^2` against
`c_k * lo(y^2) = 0`, so it demands `Qim^2 <= Qre^2`, which is false at the
zeros of `Qre(0, .)` — and those zeros sit **inside** the windows (measured:
`s* = 6.6431, 12.7553, 18.9767, ...`, one per window).  The failure is not
one of resolution: interval arithmetic has decorrelated `Qim^2 ~ y^2 R^2`
from `c_k y^2`, two quantities of the same order in `y`, and bisection in `y`
refines forever.

Nor can layering in `y` avoid it.  Measured here, the `y -> 0` limit of
`sup_s Dam/y^2` is `0.936 x c_0` and `0.970-0.979 x c_k` for `k >= 1`: the
supremum is very nearly attained at *every* depth, so a layer `[y_lo, y_hi]`
checked against `lo(y^2)` needs `y_hi/y_lo <= sqrt(1.20) = 1.0954`, and
covering `(0, 1/2]` in such layers takes infinitely many.

## What this module does instead

Factor the removable zero out.  `Qim` is odd in `y`, so `Qim = y * R` with

    R(y,s) = 2 * (Ntil * ReD - s * ReN) / |D|^2

explicit and analytic across `y = 0`, where (writing `C = cos(sqrt2/2)`,
`S = sin(sqrt2/2)`, `r = sqrt 2`, `sn = sin(s/2)`, `cs = cos(s/2)`,
`sh = sinh(y/2)`, `ch = cosh(y/2)`, and `shq = sinh(y/2)/y`)

    ReN  = 2 * (C*(s*sn*ch - y*cs*sh) - r*S*cs*ch)
    Ntil = shq*(C*s*cs + r*S*sn) + C*sn*ch          (so that ImN = 2*y*Ntil)
    ReD  = s^2 - y^2 - 2 ,   ImD = 2*s*y ,   |D|^2 = ReD^2 + ImD^2
    Qre  = (ReN*ReD + 4*s*y^2*Ntil) / |D|^2

and then the obligation `Qim^2 - Qre^2 <= c y^2` is checked in the equivalent
factored form

    y^2 * (R^2 - c)  <=  Qre^2                                          (*)

whose two sides are `O(1)` in `y` where the original two were `O(y^2)`.  The
`y = 0` degeneracy is gone: at `y = 0` the left side is `0` and the right side
is `Qre(0,s)^2 >= 0`.

`(*)` also covers the complement.  "No damage between the windows" is
`Qim^2 <= Qre^2`, which is `(*)` with `c = 0` — so one cell shape and one
check serve the whole rectangle, windows and gaps alike.

The one new leaf this needs beyond `Phi.lean` is `shq = sinh(y/2)/y`, the
removable branch of `sinh`.  `Leaves.lean` already carries the same device for
`sin(u/2)/u` (its `sfnL` series), so it is a copy of an existing pattern.

## Operating point

Windows widened by `WIDEN = 1/200` and caps inflated by `INFLATION = 6/5`,
the point `O9-SCOPING.md` §3 recommends and whose surplus §7 absorbs
(`1.3945x` is the wall).  The widening is capped at `0.00695` by O3's
`|u| <= 1` radius; `1/200` is inside it.

## LEAF CAVEAT

Inherited verbatim from `o9_leaf.py`: the transcendental leaves are computed
with Arb and rounded outward onto the `2^-64` grid, whereas
`BandCert/Leaves.lean` computes them by Taylor series at its own widths.  The
two agree far inside the margins reported by `validate()`, so this module
**predicts** the kernel's verdict rather than reproducing it bit for bit.

Run:

    .venv/bin/python hunts/frontier_math/o9_leaf2d.py
    .venv/bin/python -m pytest -q hunts/frontier_math/test_o9_leaf2d.py
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

from o9_leaf import (  # the kernel's own fixed-point arithmetic, already mirrored
    SO,
    Iv,
    civ_mul,
    ofInt,
    ofQ,
    _arb,
    _cell_ball,
    _to_iv,
)

__all__ = [
    "WINDOWS_RAW", "CAPS_SUP", "WIDEN", "INFLATION",
    "widened_windows", "inflated_caps",
    "field_iv", "cell_verdict", "build", "validate", "emit_lean", "report",
]

# ---------------------------------------------------------------------------
# the recorded windows (RETENTION-PROBLEM.md §4) and their attained suprema
# ---------------------------------------------------------------------------

#: `(lo, hi)` of each recorded damage window `I_k`.
WINDOWS_RAW = [
    (F(60653, 10000), F(35257, 5000)), (F(61171, 5000), F(131999, 10000)),
    (F(11544, 625), F(48583, 2500)), (F(247289, 10000), F(256909, 10000)),
    (F(309971, 10000), F(159793, 5000)), (F(372701, 10000), F(76463, 2000)),
    (F(21773, 500), F(27817, 625)), (F(498237, 10000), F(507849, 10000)),
    (F(280513, 5000), F(570637, 10000)),
]

#: `sup Dam(y,s)/y^2` over each window, as recorded by `o9_scoping.WINDOWS`.
#: These are *attained*, which is why they must be inflated before use.
CAPS_SUP = [
    F(439643, 25000000), F(390023, 100000000), F(169313, 100000000),
    F(18889, 20000000), F(6021, 10000000), F(10431, 25000000),
    F(6123, 20000000), F(1171, 5000000), F(9247, 50000000),
]

#: Window widening.  Bounded above by `0.00695` — O3 supplies
#: `Kpair >= 39/50` only on `|u| <= 1` and the widest window is `0.9861`.
WIDEN = F(1, 200)

#: Cap inflation.  §7 absorbs up to `1.3945x`; this is the recommended point.
INFLATION = F(6, 5)

#: A cell must clear its check by at least this many `2^-64` ulp before it is
#: accepted, so that the LEAF CAVEAT cannot decide a cell.  The Arb leaves used
#: here and the Taylor leaves `Leaves.lean` computes agree to well under
#: `2^-60`, i.e. ~`16` ulp; `2^24` leaves six orders of magnitude of room.
MIN_MARGIN_ULP = 1 << 24

S_LO, S_HI = F(28, 5), F(60)
Y_LO, Y_HI = F(0), F(1, 2)


def widened_windows() -> list[tuple[F, F]]:
    return [(lo - WIDEN, hi + WIDEN) for lo, hi in WINDOWS_RAW]


def inflated_caps() -> list[F]:
    return [c * INFLATION for c in CAPS_SUP]


def _o3_ceiling_ok() -> bool:
    """The widening may not push a window past the O3 radius `|u| <= 1`."""
    widest = max(hi - lo for lo, hi in WINDOWS_RAW)
    return widest + 2 * WIDEN <= F(1)


# ---------------------------------------------------------------------------
# the field, in the kernel's fixed-point arithmetic, with `y` an interval
# ---------------------------------------------------------------------------


# --- Leaves.lean, mirrored exactly ------------------------------------------
#
# The first version of this module took its `sin`/`cos`/`sinh`/`cosh` leaves
# from Arb and rounded them outward, as `o9_leaf.py` does, on the strength of
# that module's LEAF CAVEAT ("the two agree to well under 2^-60").
#
# **That caveat is false on wide cells, and the kernel said so.**  Arb encloses
# `sin` over a wide interval by its actual range; `Leaves.sinCosIv` reduces mod
# 2*pi, quarters, evaluates a 22-term Taylor interval, and then applies the
# double-angle map twice -- and `dbl` squares an interval, so width grows.  On
# the very first cell (`s` in [5.6, 6.0603]) Arb gives `sin` width 0.224 and
# the kernel gives 0.366.  Predicting with Arb was therefore optimistic, and 14
# of 15 `decide +kernel` chunks failed on a table this module had called sound.
#
# So the leaves below are Lean's own algorithms, in Lean's own integer
# arithmetic, rather than Arb rounded outward.  There is nothing left to
# caveat: `_leaves` now computes what the kernel computes.

PIQA = 14488038916154245652
PIQB = 14488038916154245716
SQ2N = 26087635650665564424

SINL = [(1, 1), (-1, 6), (1, 120), (-1, 5040), (1, 362880), (-1, 39916800),
        (1, 6227020800), (-1, 1307674368000), (1, 355687428096000),
        (-1, 121645100408832000), (1, 51090942171709440000)]
COSL = [(1, 1), (-1, 2), (1, 24), (-1, 720), (1, 40320), (-1, 3628800),
        (1, 479001600), (-1, 87178291200), (1, 20922789888000),
        (-1, 6402373705728000), (1, 2432902008176640000)]
SINHL = [(n, d) if n > 0 else (-n, d) for n, d in SINL]
COSHL = [(n, d) if n > 0 else (-n, d) for n, d in COSL]
#: `sinh(u/2)/u`: `SINHL` halved, exactly as `sfnL` is `sinL` halved.
SHFNL = [(n, 2 * d) for n, d in SINHL]


def _horner(cs: list[tuple[int, int]], x: Iv) -> Iv:
    """`hornerI`: `c0 + (horner cs' x) * x`, folded from the right."""
    acc = ofInt(0)
    for n, d in reversed(cs):
        acc = ofQ(n, d).add(acc.mul(x))
    return acc


def _sin_cos_small(a: Iv) -> tuple[Iv, Iv]:
    x2 = a.sqr()
    return (_horner(SINL, x2).mul(a).widen(1), _horner(COSL, x2).widen(1))


def _dbl(sc: tuple[Iv, Iv]) -> tuple[Iv, Iv]:
    s, c = sc
    return (s.mul(c).mulInt(2), ofInt(1).sub(s.sqr().mulInt(2)))


_TOPI = Iv(-SO, SO)
_PI2 = Iv(8 * PIQA, 8 * PIQB)


def _sin_cos_iv(a: Iv) -> tuple[Iv, Iv]:
    """`sinCosIv`: reduce mod 2pi, quarter, evaluate, double twice."""
    m = a.lo + a.hi
    ps = _PI2.lo + _PI2.hi
    k = (m + ps // 2) // ps          # Lean's Int `/` is ediv; floor for ps > 0
    r = a.sub(_PI2.mulInt(k))
    t = r.divInt(4)
    if -SO <= t.lo and t.hi <= SO:
        return _dbl(_dbl(_sin_cos_small(t)))
    return (_TOPI, _TOPI)


def _sinh_cosh_small(a: Iv) -> tuple[Iv, Iv]:
    x2 = a.sqr()
    return (_horner(SINHL, x2).mul(a).widen(1), _horner(COSHL, x2).widen(1))


def _shfn_iv(u: Iv) -> Iv | None:
    """`shfnIv`: the series branch of `sinh(u/2)/u`, valid on `|u| <= 2`."""
    if -(2 * SO) <= u.lo and u.hi <= 2 * SO:
        return _horner(SHFNL, u.divInt(2).sqr()).widen(1)
    return None


_SQ2 = Iv(SQ2N, SQ2N + 1)
_HSQ2 = _SQ2.divInt(2)
_SINC, _COSC = _sin_cos_small(_HSQ2)


def _leaves(slo: F, shi: F, ylo: F, yhi: F) -> dict[str, Iv] | None:
    """The leaves over the 2-D cell, computed the way the kernel computes them."""
    def dn(x: F) -> int:
        return (x * SO).__floor__()

    def up(x: F) -> int:
        return -((-(x * SO)).__floor__())

    X = Iv(dn(slo), up(shi))
    Y = Iv(dn(ylo), up(yhi))
    sn, cs = _sin_cos_iv(X.divInt(2))
    sh, ch = _sinh_cosh_small(Y.divInt(2))
    shq = _shfn_iv(Y)
    if shq is None:
        return None
    return {"X": X, "Y": Y, "sn": sn, "cs": cs, "sh": sh, "ch": ch,
            "shq": shq, "SQ2": _SQ2, "SINC": _SINC, "COSC": _COSC}


@dataclass(frozen=True)
class Field:
    R: Iv        # Qim / y
    Qre: Iv
    Y: Iv


def field_iv(slo: F, shi: F, ylo: F, yhi: F) -> Field | None:
    """`R = Qim/y` and `Qre` over the cell, in the kernel's arithmetic."""
    L = _leaves(slo, shi, ylo, yhi)
    if L is None:
        return None
    X, Y = L["X"], L["Y"]
    sn, cs, sh, ch, shq = L["sn"], L["cs"], L["sh"], L["ch"], L["shq"]
    C, S, r = L["COSC"], L["SINC"], L["SQ2"]

    rS = r.mul(S)
    # ReN = 2 (C (s sn ch - y cs sh) - r S cs ch)
    ReN = (C.mul(X.mul(sn).mul(ch).sub(Y.mul(cs).mul(sh)))
           .sub(rS.mul(cs).mul(ch))).mulInt(2)
    # Ntil = shq (C s cs + r S sn) + C sn ch          [ImN = 2 y Ntil]
    Ntil = shq.mul(C.mul(X).mul(cs).add(rS.mul(sn))).add(C.mul(sn).mul(ch))
    # ReD = s^2 - y^2 - 2 ; ImD = 2 s y
    ReD = X.sqr().sub(Y.sqr()).sub(ofInt(2))
    ImD = X.mul(Y).mulInt(2)
    D2 = ReD.sqr().add(ImD.sqr())
    if D2.lo <= 0:
        return None
    # R = 2 (Ntil ReD - s ReN) / |D|^2
    Rnum = Ntil.mul(ReD).sub(X.mul(ReN)).mulInt(2)
    R = Rnum.div(D2)
    # Qre = (ReN ReD + 4 s y^2 Ntil) / |D|^2
    Qnum = ReN.mul(ReD).add(X.mul(Y.sqr()).mul(Ntil).mulInt(4))
    Qre = Qnum.div(D2)
    if R is None or Qre is None:
        return None
    return Field(R=R, Qre=Qre, Y=Y)


# ---------------------------------------------------------------------------
# the cell test:  y^2 (R^2 - c) <= Qre^2
# ---------------------------------------------------------------------------


def _cap_for(slo: F, shi: F) -> tuple[F | None, bool]:
    """`(cap, straddles)`; cap `0` outside every widened window."""
    wins, caps = widened_windows(), inflated_caps()
    for (wl, wh), c in zip(wins, caps):
        if wl <= slo and shi <= wh:
            return c, False
    if any(not (shi <= wl or slo >= wh) for wl, wh in wins):
        return None, True          # must be split onto one side
    return F(0), False


def cell_verdict(slo: F, shi: F, ylo: F, yhi: F):
    """`(ok, margin_ulp, scaled_cap)` for one 2-D cell.

    A cell can be carried by either of two slacks, and the reported margin is
    the larger, because either alone suffices:

    * **structural** — `R^2 <= cap` on the cell, so `y^2 (R^2 - cap) <= 0 <=
      Qre^2` whatever `Qre` does.  Its slack is `cap - hi(R^2)`.
    * **general** — `hi(lhs) <= lo(rhs)` with both sides live.  Its slack is
      `lo(rhs) - hi(lhs)`.

    Reporting only the second understates the first badly: on a cell holding a
    zero of `Qre(0, .)` the general slack is *exactly* `0` (both sides vanish)
    while the structural slack is ~`1e12` ulp.  Nine cells — one per window —
    are in that position, so this distinction is not academic.
    """
    cap, straddles = _cap_for(slo, shi)
    if straddles:
        return False, 0, None
    f = field_iv(slo, shi, ylo, yhi)
    if f is None:
        return False, 0, None
    # cap as a grid interval, rounded DOWN (weakening the claim safely)
    cs = (cap * SO).__floor__()
    cIv = Iv(cs, cs)
    r2 = f.R.sqr()
    lhs = r2.sub(cIv).mul(f.Y.sqr())
    rhs = f.Qre.sqr()
    ok = lhs.hi <= rhs.lo
    general = rhs.lo - lhs.hi
    structural = cs - r2.hi          # meaningful only when positive
    return ok, max(general, structural), cs


# ---------------------------------------------------------------------------
# the adaptive walk
# ---------------------------------------------------------------------------


def _seed_segments() -> list[tuple[F, F]]:
    """Cut `[28/5,60]` at every widened-window endpoint before bisecting.

    Bisection alone never lands on an endpoint (they are rationals with
    denominator `2*10^4`, the midpoints are dyadic), so a straddling cell
    would shrink forever without deciding.
    """
    cuts = {S_LO, S_HI}
    for wl, wh in widened_windows():
        if S_LO < wl < S_HI:
            cuts.add(wl)
        if S_LO < wh < S_HI:
            cuts.add(wh)
    pts = sorted(cuts)
    return [(a, b) for a, b in zip(pts, pts[1:])]


def build(max_depth: int = 26):
    """Adaptive 2-D walk; splits the longer normalised side of each cell."""
    if not _o3_ceiling_ok():
        raise AssertionError("widening exceeds the O3 |u| <= 1 ceiling")
    cells, undecided = [], 0
    stack = [(a, b, Y_LO, Y_HI, 0) for a, b in _seed_segments()]
    while stack:
        slo, shi, ylo, yhi, d = stack.pop()
        ok, margin, cap = cell_verdict(slo, shi, ylo, yhi)
        if ok and margin >= MIN_MARGIN_ULP:
            cells.append({"slo": slo, "shi": shi, "ylo": ylo, "yhi": yhi,
                          "cap": cap, "margin_ulp": margin, "depth": d})
            continue
        if d >= max_depth:
            cells.append({"slo": slo, "shi": shi, "ylo": ylo, "yhi": yhi,
                          "cap": cap, "margin_ulp": -1, "depth": d})
            undecided += 1
            continue
        # split the longer side, measuring y against its full range so the
        # two variables are compared on a common scale
        if (shi - slo) >= (yhi - ylo) * 4:
            m = (slo + shi) / 2
            stack.append((slo, m, ylo, yhi, d + 1))
            stack.append((m, shi, ylo, yhi, d + 1))
        else:
            m = (ylo + yhi) / 2
            stack.append((slo, shi, ylo, m, d + 1))
            stack.append((slo, shi, m, yhi, d + 1))
    cells.sort(key=lambda c: (c["slo"], c["ylo"]))
    return {"cells": cells, "undecided": undecided,
            "max_depth": max(c["depth"] for c in cells)}


def validate(table=None) -> dict:
    t = table or build()
    ms = [c["margin_ulp"] for c in t["cells"]]
    return {"cells": len(t["cells"]), "undecided": t["undecided"],
            "max_depth": t["max_depth"], "min_margin_ulp": min(ms),
            "min_margin_abs": min(ms) / SO,
            "all_decided": t["undecided"] == 0}


# ---------------------------------------------------------------------------
# emission
# ---------------------------------------------------------------------------

_HEADER = """import Zeta23Ext.EForm3.O9Field

/-!
# O9 leaf data — the damage cap table on `[28/5, 60] x [0, 1/2]`

Generated by `hunts/frontier_math/o9_leaf2d.py`.  Each leaf records a
rectangle `[slo,shi] x [ylo,yhi]` (all scaled by `2^64`) and the scaled cap
`cap` it must respect; `o9Cell` re-evaluates the field on the rectangle and
checks

    y^2 * (R^2 - cap)  <=  Qre^2 .

Leaves inside a widened window carry that window's inflated cap; leaves
outside every window carry `0`, which is the "no damage between the windows"
claim in the same shape.

Unlike `O9Data.lean` this table is two-variable, so it needs **no**
depth-reduction lemma to reach `y < 1/2`.
-/

namespace Retention
open BandDual

/-- One leaf: `[slo,shi] x [ylo,yhi]` (scaled by `2^64`) with its scaled cap. -/
structure O9Cell2 where
  slo : ℤ
  shi : ℤ
  ylo : ℤ
  yhi : ℤ
  cap : ℤ
deriving DecidableEq

"""


def emit_lean(out_dir: Path | None = None, table=None, chunk: int = 40) -> dict:
    """Write `O9Data2.lean` (leaves) and `O9Check2.lean` (the walk)."""
    t = table or build()
    out = out_dir or (Path(__file__).resolve().parent / "zeta23ext"
                      / "Zeta23Ext" / "EForm3")
    out.mkdir(parents=True, exist_ok=True)

    def dn(x: F) -> int:
        return (x * SO).__floor__()

    def up(x: F) -> int:
        return -((-(x * SO)).__floor__())

    rows = [f"  ⟨{dn(c['slo'])}, {up(c['shi'])}, {dn(c['ylo'])}, "
            f"{up(c['yhi'])}, {c['cap']}⟩" for c in t["cells"]]
    (out / "O9Data2.lean").write_text(
        _HEADER + "/-- The recorded leaves. -/\ndef o9cells2 : List O9Cell2 :=\n[\n"
        + ",\n".join(rows) + "]\n\nend Retention\n")

    n = len(t["cells"])
    chunks = max(1, (n + chunk - 1) // chunk)
    thms = "\n".join(
        f"theorem o9_2_chunk{i} : o9Walk2 (o9cells2.drop {i*chunk} |>.take {chunk}) "
        f"= true := by\n  decide +kernel" for i in range(chunks))
    (out / "O9Check2.lean").write_text(f"""import Zeta23Ext.EForm3.O9Data2

/-!
# Running the two-variable O9 checker

`o9Walk2` is `Bool`-valued and total; each chunk is one `decide +kernel`,
mirroring `BandCert/Verify.lean`.
-/

namespace Retention
open BandDual

set_option maxRecDepth 100000

/-- Check one leaf: `y^2 (R^2 - cap) <= Qre^2`. -/
def o9Cell2 (c : O9Cell2) : Bool :=
  match o9Field c.slo c.shi c.ylo c.yhi with
  | none => false
  | some f =>
      match EIv.mul (EIv.sub (EIv.sqr f.R) (some ⟨c.cap, c.cap⟩)) (EIv.sqr f.Y),
            EIv.sqr f.Qre with
      | some l, some r => decide (l.hi ≤ r.lo)
      | _, _ => false

def o9Walk2 : List O9Cell2 → Bool
  | [] => true
  | c :: cs => o9Cell2 c && o9Walk2 cs

{thms}

end Retention
""")
    return {"cells": n, "chunks": chunks,
            "data_kb": (out / "O9Data2.lean").stat().st_size / 1024}


def report() -> dict:
    t = build()
    v = validate(t)
    print("O9, two-variable leaf table on [28/5,60] x [0,1/2]")
    print(f"  widening      {WIDEN}   (O3 ceiling 0.00695: "
          f"{'ok' if _o3_ceiling_ok() else 'BROKEN'})")
    print(f"  inflation     {INFLATION}  (§7 wall 1.3945x)")
    print(f"  leaves        {v['cells']}")
    print(f"  max depth     {v['max_depth']}")
    print(f"  undecided     {v['undecided']}")
    print(f"  min margin    {v['min_margin_ulp']} ulp "
          f"= {v['min_margin_abs']:.3e}")
    print(f"  all decided   {v['all_decided']}")
    return v


if __name__ == "__main__":
    report()
