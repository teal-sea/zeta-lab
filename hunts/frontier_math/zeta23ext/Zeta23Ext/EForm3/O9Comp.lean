import Zeta23Ext.BandCert.Leaves

/-!
# The O9 box compositions, in the kernel's arithmetic

`rIv` and `qreIv` are the two enclosures the two-dimensional O9 checker
evaluates on each box: the removable branch `R = Qim/y` and the real part
`Qre`.  They are the same composition `Phi.lean` performs, carried through the
`/y` variants so that `y = 0` is an ordinary point rather than a removable
singularity — which is what lets the 2-D route cover the full
`[28/5, 60] × [0, 1/2]` box without the depth-reduction lemma.

**These are `Bool`/`EIv`-level definitions only.**  They compute enclosures;
they do not yet claim anything about `Dam`.  The `_mem` seam lemmas that
connect them to the real quantities are not written, and until they are, a
`decide +kernel` over a table built from these proves the table internally
consistent and nothing more.  That distinction is the whole reason
`O9-2D-STATUS.md` §0 exists: a checker that elaborates is not a checker that
means something.

The leaves come from `Leaves.lean` unchanged.  `shcSmall` is `sinh v / v`,
which `sinhCoshSmall` already evaluates internally on its way to `sinh`
(`O9-2D-STATUS.md` §3), so the removable branch needs no new arithmetic here —
only a new truncation lemma later, on the soundness side.
-/

namespace BandDual
namespace EIv

/-- `y²` as an enclosure, from `y`'s raw grid integer.

The `mode = 2` test needs `y_hi²` where `y_hi` arrives as the box's stored
integer at scale `2^-64`, so the square lands at scale `2^-128` and has to come
back to the grid. Written as `Iv.ofQ (n*n) (SO*SO)` rather than by hand, so it
is the same rounding the rest of the package uses and matches
`o9_leaf2d.cell_verdict`'s `ofQ(ysq.numerator, ysq.denominator)` by
construction rather than by coincidence. -/
def sqrScaled (n : ℤ) : EIv := some (Iv.ofQ (n * n) (SO * SO))

end EIv
end BandDual

namespace Retention

open BandDual

/-- `sinh v / v` on the small range — the removable branch's leaf. -/
def shcSmall (a : EIv) : EIv := EIv.widen (hornerI sinhL (EIv.sqr a)) 1

/-- The shared sub-expressions of both compositions over one box.

Mirrors `o9_leaf2d._parts` operation for operation.  Field order is fixed and
load-bearing: the Python round-trip compares these integers positionally.
-/
structure Parts where
  reNum : EIv
  imNumOverY : EIv
  imNum : EIv
  reDen : EIv
  imDen : EIv
  imDenOverY : EIv
  denAbs2 : EIv

/-- Leaves for one box, straight from `Leaves.lean`. -/
def boxParts (sLo sHi yLo yHi : ℤ) : Parts :=
  let X : EIv := some ⟨sLo, sHi⟩
  let Y : EIv := some ⟨yLo, yHi⟩
  let halfS := EIv.divInt X 2
  let halfY := EIv.divInt Y 2
  let sc := sinCosIv halfS
  let sn := sc.1
  let cs := sc.2
  let hc := sinhCoshSmall halfY
  let sh := hc.1
  let ch := hc.2
  let shc := shcSmall halfY
  let sq2 := sinCosSmall (EIv.divInt SQ2 2)
  let SINC := sq2.1
  let COSC := sq2.2
  -- sinh(y/2)/y = shc(y/2)/2
  let shOverY := EIv.divInt shc 2
  -- z*sin(z/2) with z = X + iY, sin(z/2) = (sn*ch, cs*sh)
  let reZsin := EIv.sub (EIv.mul (EIv.mul X sn) ch) (EIv.mul (EIv.mul Y cs) sh)
  let imZsinOverY := EIv.add (EIv.mul (EIv.mul X cs) shOverY) (EIv.mul sn ch)
  -- cos(z/2) = (cs*ch, -(sn*sh))
  let reCos := EIv.mul cs ch
  let imCosOverY := EIv.neg (EIv.mul sn shOverY)
  -- num = 2 * ( z*sin(z/2)*COSC - cos(z/2)*SINC*SQ2 )
  let reNum := EIv.mulInt
    (EIv.sub (EIv.mul reZsin COSC) (EIv.mul (EIv.mul reCos SINC) SQ2)) 2
  let imNumOverY := EIv.mulInt
    (EIv.sub (EIv.mul imZsinOverY COSC) (EIv.mul (EIv.mul imCosOverY SINC) SQ2)) 2
  -- den = z^2 - 2 = (X^2 - Y^2 - 2, 2XY)
  let reDen := EIv.sub (EIv.sub (EIv.sqr X) (EIv.sqr Y)) (EIv.ofInt 2)
  let imDenOverY := EIv.mulInt X 2
  let imDen := EIv.mul imDenOverY Y
  { reNum := reNum
    imNumOverY := imNumOverY
    imNum := EIv.mul imNumOverY Y
    reDen := reDen
    imDen := imDen
    imDenOverY := imDenOverY
    denAbs2 := EIv.add (EIv.sqr reDen) (EIv.sqr imDen) }

/-- `Qre = Re(num/den)` over the box, or `none` if the denominator is not
separated from zero. -/
def qreIv (sLo sHi yLo yHi : ℤ) : EIv :=
  let p := boxParts sLo sHi yLo yHi
  EIv.div (EIv.add (EIv.mul p.reNum p.reDen) (EIv.mul p.imNum p.imDen)) p.denAbs2

/-- `R = Qim / y` over the box, or `none`.

The negation is not cosmetic.  `Phi2 (s + iy)` has real part `Qre` and
imaginary part **`-Qim`**, so `Im(num/den)/y` is `-Qim/y` and the negation puts
it back.  `O9-2D-STATUS.md` §6 records that the first draft had this sign
wrong, that no cell verdict could ever have detected it — `R` enters only
squared — and that it was caught only by an independent evaluation.  A quantity
that enters only squared has no self-check, so it needs an external one.
-/
def rIv (sLo sHi yLo yHi : ℤ) : EIv :=
  let p := boxParts sLo sHi yLo yHi
  EIv.neg (EIv.div
    (EIv.sub (EIv.mul p.imNumOverY p.reDen) (EIv.mul p.reNum p.imDenOverY))
    p.denAbs2)

end Retention
