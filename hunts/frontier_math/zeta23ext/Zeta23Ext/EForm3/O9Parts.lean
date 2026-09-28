import Zeta23Ext.EForm3.O9Comp
import Zeta23Ext.EForm3.O9Real

/-!
# `boxParts`, field by field

`O9Seam` proves the composition sound *given* that the seven fields of
`boxParts` enclose the right quantities. This file supplies that, starting with
the denominator, which needs no transcendental leaves at all.

With `z = s + i y`, the denominator is `z² − 2`, so

* `Re den = s² − y² − 2`
* `Im den = 2 s y`, hence `Im den / y = 2 s`: and *that* is what the table
  carries, which is why the removable branch never divides by anything.

The numerator side needs the trig and hyperbolic leaves and is the remaining
step; it is not in this file and no `sorry` stands in for it.
-/

namespace Retention

open BandDual

variable {sLo sHi yLo yHi : ℤ} {s y : ℝ}

/-- `reDen` encloses `Re(z² − 2) = s·s − y·y − 2`. -/
theorem reDen_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y) :
    (boxParts sLo sHi yLo yHi).reDen.mem (s * s - y * y - ((2:ℤ):ℝ)) := by
  unfold boxParts
  exact EIv.sub_mem (EIv.sub_mem (EIv.sqr_mem hs) (EIv.sqr_mem hy)) (EIv.ofInt_mem 2)

/-- `imDenOverY` encloses `Im(z² − 2)/y = 2 s`, with no division performed. -/
theorem imDenOverY_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y) :
    (boxParts sLo sHi yLo yHi).imDenOverY.mem (s * ((2:ℤ):ℝ)) := by
  unfold boxParts
  exact EIv.mulInt_mem hs

/-- `imDen` encloses `Im(z² − 2) = 2 s y`. -/
theorem imDen_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y) :
    (boxParts sLo sHi yLo yHi).imDen.mem (s * ((2:ℤ):ℝ) * y) := by
  unfold boxParts
  exact EIv.mul_mem (EIv.mulInt_mem hs) hy

/-- `denAbs2` encloses `|z² − 2|²`, in the `c*c + d*d` form `O9Seam` consumes. -/
theorem denAbs2_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y) :
    (boxParts sLo sHi yLo yHi).denAbs2.mem
      ((s * s - y * y - ((2:ℤ):ℝ)) * (s * s - y * y - ((2:ℤ):ℝ))
        + (s * ((2:ℤ):ℝ) * y) * (s * ((2:ℤ):ℝ) * y)) := by
  unfold boxParts
  exact EIv.add_mem
    (EIv.sqr_mem (EIv.sub_mem (EIv.sub_mem (EIv.sqr_mem hs) (EIv.sqr_mem hy))
      (EIv.ofInt_mem 2)))
    (EIv.sqr_mem (EIv.mul_mem (EIv.mulInt_mem hs) hy))

/-- The `X` and `Y` fields are the box itself. -/
theorem X_mem (hs : EIv.mem (some ⟨sLo, sHi⟩) s) :
    EIv.mem (some ⟨sLo, sHi⟩) s := hs

end Retention

#print axioms Retention.reDen_mem
#print axioms Retention.imDenOverY_mem
#print axioms Retention.imDen_mem
#print axioms Retention.denAbs2_mem
