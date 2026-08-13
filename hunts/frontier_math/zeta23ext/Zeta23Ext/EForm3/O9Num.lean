import Zeta23Ext.EForm3.O9Parts
import Zeta23Ext.EForm3.O9Shc

/-!
# `boxParts`, the numerator half

The denominator (`O9Parts`) needed no transcendental leaves. The numerator needs
all four: `sinCosIv` for `sin`/`cos` of `s/2` (which reaches 30, so it goes
through the argument reduction), `sinhCoshSmall` for `sinh`/`cosh` of `y/2`
(which stays inside the small range because `y ≤ 1/2`), `sinCosSmall` for the
`√2/2` constants, and `shcSmall` for the removable branch.

The targets are written in the shape the interval composition computes rather
than as `Re num` and `Im num / y`. Relating those two shapes is
`O9Real.re_div_eq` / `im_div_over_y`, already proved; keeping the two steps
apart is what let the arithmetic identities be stated over plain reals with no
package dependency at all.
-/

namespace Retention

open BandDual

variable {sLo sHi yLo yHi : ℤ} {s y : ℝ}

/-- The four leaves the numerator consumes, at one box. -/
theorem leaves_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) :
    EIv.mem (sinCosIv (EIv.divInt (some ⟨sLo, sHi⟩) 2)).1 (Real.sin (s / ((2:ℤ):ℝ)))
    ∧ EIv.mem (sinCosIv (EIv.divInt (some ⟨sLo, sHi⟩) 2)).2 (Real.cos (s / ((2:ℤ):ℝ)))
    ∧ EIv.mem (sinhCoshSmall (EIv.divInt (some ⟨yLo, yHi⟩) 2)).1
        (Real.sinh (y / ((2:ℤ):ℝ)))
    ∧ EIv.mem (sinhCoshSmall (EIv.divInt (some ⟨yLo, yHi⟩) 2)).2
        (Real.cosh (y / ((2:ℤ):ℝ))) := by
  have hhs : EIv.mem (EIv.divInt (some ⟨sLo, sHi⟩) 2) (s / ((2:ℤ):ℝ)) :=
    EIv.divInt_mem (by norm_num) hs
  have hhy : EIv.mem (EIv.divInt (some ⟨yLo, yHi⟩) 2) (y / ((2:ℤ):ℝ)) :=
    EIv.divInt_mem (by norm_num) hy
  obtain ⟨h1, h2⟩ := sinCosIv_mem hhs
  obtain ⟨h3, h4⟩ := sinhCoshSmall_mem hhy hy1
  exact ⟨h1, h2, h3, h4⟩

/-- **`reNum` is sound.**

`Re(z · sin(z/2)) = s·sin(s/2)·cosh(y/2) − y·cos(s/2)·sinh(y/2)` and
`Re(cos(z/2)) = cos(s/2)·cosh(y/2)`, so the numerator's real part is the
expression below. -/
theorem reNum_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1)
    {sc ss cc : ℝ}
    (hsc : EIv.mem (sinCosSmall (EIv.divInt SQ2 2)).1 ss)
    (hcc : EIv.mem (sinCosSmall (EIv.divInt SQ2 2)).2 cc)
    (hq : EIv.mem SQ2 sc) :
    EIv.mem (boxParts sLo sHi yLo yHi).reNum
      (((s * Real.sin (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ))
          - y * Real.cos (s / ((2:ℤ):ℝ)) * Real.sinh (y / ((2:ℤ):ℝ))) * cc
        - Real.cos (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ)) * ss * sc)
        * ((2:ℤ):ℝ)) := by
  obtain ⟨hsn, hcs, hsh, hch⟩ := leaves_mem hs hy hy1
  unfold boxParts
  refine EIv.mulInt_mem (EIv.sub_mem (EIv.mul_mem ?_ hcc) (EIv.mul_mem (EIv.mul_mem ?_ hsc) hq))
  · exact EIv.sub_mem (EIv.mul_mem (EIv.mul_mem hs hsn) hch)
      (EIv.mul_mem (EIv.mul_mem hy hcs) hsh)
  · exact EIv.mul_mem hcs hch

/-- **`imNumOverY` is sound**, and nothing in it divides by `y`.

`Im(z · sin(z/2))/y = s·cos(s/2)·(sinh(y/2)/y) + sin(s/2)·cosh(y/2)` and
`Im(cos(z/2))/y = −sin(s/2)·(sinh(y/2)/y)`, and the factor `sinh(y/2)/y` is
carried by `shcSmall`, whose soundness lemma has no nonzero hypothesis. So this
lemma has none either — which is exactly what makes the boxes reaching `y = 0`
ordinary. -/
theorem imNumOverY_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1)
    {sc ss cc : ℝ}
    (hsc : EIv.mem (sinCosSmall (EIv.divInt SQ2 2)).1 ss)
    (hcc : EIv.mem (sinCosSmall (EIv.divInt SQ2 2)).2 cc)
    (hq : EIv.mem SQ2 sc) :
    EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY
      (((s * Real.cos (s / ((2:ℤ):ℝ))
            * ((if y / ((2:ℤ):ℝ) = 0 then 1
                else Real.sinh (y / ((2:ℤ):ℝ)) / (y / ((2:ℤ):ℝ))) / ((2:ℤ):ℝ))
          + Real.sin (s / ((2:ℤ):ℝ)) * Real.cosh (y / ((2:ℤ):ℝ))) * cc
        - -(Real.sin (s / ((2:ℤ):ℝ))
            * ((if y / ((2:ℤ):ℝ) = 0 then 1
                else Real.sinh (y / ((2:ℤ):ℝ)) / (y / ((2:ℤ):ℝ))) / ((2:ℤ):ℝ)))
            * ss * sc)
        * ((2:ℤ):ℝ)) := by
  obtain ⟨hsn, hcs, hsh, hch⟩ := leaves_mem hs hy hy1
  have hhy : EIv.mem (EIv.divInt (some ⟨yLo, yHi⟩) 2) (y / ((2:ℤ):ℝ)) :=
    EIv.divInt_mem (by norm_num) hy
  have hshc := shcSmall_mem hhy hy1
  have hsov : EIv.mem (EIv.divInt (shcSmall (EIv.divInt (some ⟨yLo, yHi⟩) 2)) 2)
      ((if y / ((2:ℤ):ℝ) = 0 then 1
        else Real.sinh (y / ((2:ℤ):ℝ)) / (y / ((2:ℤ):ℝ))) / ((2:ℤ):ℝ)) :=
    EIv.divInt_mem (by norm_num) hshc
  unfold boxParts
  refine EIv.mulInt_mem (EIv.sub_mem (EIv.mul_mem ?_ hcc)
    (EIv.mul_mem (EIv.mul_mem ?_ hsc) hq))
  · exact EIv.add_mem (EIv.mul_mem (EIv.mul_mem hs hcs) hsov) (EIv.mul_mem hsn hch)
  · exact EIv.neg_mem (EIv.mul_mem hsn hsov)

end Retention

#print axioms Retention.leaves_mem
#print axioms Retention.reNum_mem
#print axioms Retention.imNumOverY_mem
