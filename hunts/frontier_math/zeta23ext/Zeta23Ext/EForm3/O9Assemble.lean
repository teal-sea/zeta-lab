import Zeta23Ext.EForm3.O9Num
import Zeta23Ext.EForm3.ClosedForm

/-!
# `qreIv` and `rIv` are sound

The seven `boxParts` fields are enclosures (`O9Parts`, `O9Num`); the
compositions built on them are sound given that (`O9Seam`). This file joins the
two, which is the last structural step: after it, the only thing between the
kernel-checked table and O9 is the arithmetic of the two modes.

Both lemmas are stated with the components abstracted — `a`, `b`, `c`, `d` for
the four parts — rather than with the trigonometric expressions written out.
That is deliberate and it is the same choice `O9Seam` made: the composition's
soundness does not depend on *which* reals the fields enclose, only that they
enclose them, so writing the expressions in would couple this file to the leaf
layer for no benefit and force a reproof the next time the leaves move.
-/

namespace Retention

open BandDual

variable {sLo sHi yLo yHi : ℤ}

/-- **`qreIv` encloses the componentwise real quotient.**

With `a = Re num`, `b = Im num`, `c = Re den`, `d = Im den`, this is
`(a c + b d)/(c² + d²)`, which `O9Real.re_div_eq` identifies with
`Re(num/den)`. -/
theorem qreIv_mem {a b c d : ℝ}
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNum b)
    (hC : EIv.mem (boxParts sLo sHi yLo yHi).reDen c)
    (hD : EIv.mem (boxParts sLo sHi yLo yHi).imDen d)
    (hE : EIv.mem (boxParts sLo sHi yLo yHi).denAbs2 (c * c + d * d)) :
    EIv.mem (qreIv sLo sHi yLo yHi) ((a * c + b * d) / (c * c + d * d)) := by
  unfold qreIv
  exact O9Seam.qre_comp_mem hA hB hC hD hE

/-- **`rIv` encloses the removable branch.**

With `bOverY = Im num / y` and `dOverY = Im den / y`, this is
`−(bOverY·c − a·dOverY)/(c² + dOverY²·y²)`. Nothing here divides by `y`:
`O9Real.im_div_over_y` is the identity that says this equals `Qim/y`, and it is
why the enclosure exists at `y = 0` at all. -/
theorem rIv_mem {a bOverY c dOverY : ℝ}
    {y : ℝ}
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY)
    (hC : EIv.mem (boxParts sLo sHi yLo yHi).reDen c)
    (hD : EIv.mem (boxParts sLo sHi yLo yHi).imDenOverY dOverY)
    (hE : EIv.mem (boxParts sLo sHi yLo yHi).denAbs2
      (c * c + (dOverY * y) * (dOverY * y))) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((bOverY * c - a * dOverY) / (c * c + (dOverY * y) * (dOverY * y)))) := by
  unfold rIv
  exact O9Seam.r_comp_mem hA hB hC hD hE

/-! ## Identification with the analytic quantities -/

/-- The componentwise real quotient assembled by `qreIv` is exactly `Qre`.

This is the algebraic bridge from the closed form proved in `ClosedForm.lean`
to the single complex quotient evaluated by the interval table. -/
theorem reNum_quotient_eq_Qre {s y : ℝ} (hy : y ≠ 0)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    (reNumValue s y * (s * s - y * y - 2)
        + (imNumOverYValue s y * y) * (s * 2 * y))
        / ((s * s - y * y - 2) * (s * s - y * y - 2)
          + (s * 2 * y) * (s * 2 * y)) = Qre y s := by
  rw [Qre_closed y s hp hm]
  unfold reNumValue imNumOverYValue
  have hy2 : y / ((2:ℤ):ℝ) ≠ 0 := div_ne_zero hy (by norm_num)
  rw [if_neg hy2]
  rw [show (s + Real.sqrt 2) / 2 = s / 2 + Real.sqrt 2 / 2 by ring,
    show (s - Real.sqrt 2) / 2 = s / 2 - Real.sqrt 2 / 2 by ring,
    Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsqrt]
  have hsqrt4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrt]
    norm_num
  have hprod : (y ^ 2 + (s + Real.sqrt 2) ^ 2)
      * (y ^ 2 + (s - Real.sqrt 2) ^ 2)
      = (s * s - y * y - 2) * (s * s - y * y - 2)
        + (s * 2 * y) * (s * 2 * y) := by
    ring_nf
    rw [hsqrt4, hsqrt]
    ring
  rw [← hprod]
  field_simp [hp, hm]
  ring_nf
  rw [hsqrt3, hsqrt]
  ring

/-- The signed removable quotient assembled by `rIv` is exactly `Qim / y`. -/
theorem imNum_quotient_eq_Qim_over_y {s y : ℝ} (hy : y ≠ 0)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    -((imNumOverYValue s y * (s * s - y * y - 2)
        - reNumValue s y * (s * 2))
        / ((s * s - y * y - 2) * (s * s - y * y - 2)
          + (s * 2 * y) * (s * 2 * y))) = Qim y s / y := by
  rw [Qim_closed y s hp hm]
  unfold reNumValue imNumOverYValue
  have hy2 : y / ((2:ℤ):ℝ) ≠ 0 := div_ne_zero hy (by norm_num)
  rw [if_neg hy2]
  rw [show (s + Real.sqrt 2) / 2 = s / 2 + Real.sqrt 2 / 2 by ring,
    show (s - Real.sqrt 2) / 2 = s / 2 - Real.sqrt 2 / 2 by ring,
    Real.sin_add, Real.sin_sub, Real.cos_add, Real.cos_sub]
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by
    rw [show Real.sqrt 2 ^ 3 = Real.sqrt 2 ^ 2 * Real.sqrt 2 by ring, hsqrt]
  have hsqrt4 : Real.sqrt 2 ^ 4 = 4 := by
    rw [show Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 by ring, hsqrt]
    norm_num
  have hprod : (y ^ 2 + (s + Real.sqrt 2) ^ 2)
      * (y ^ 2 + (s - Real.sqrt 2) ^ 2)
      = (s * s - y * y - 2) * (s * s - y * y - 2)
        + (s * 2 * y) * (s * 2 * y) := by
    ring_nf
    rw [hsqrt4, hsqrt]
    ring
  rw [← hprod]
  field_simp [hp, hm, hy]
  ring_nf
  rw [hsqrt3, hsqrt]
  ring

/-- At nonzero depth, the computed real enclosure contains `Qre`. -/
theorem qreIv_mem_Qre {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hyBox : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy : y ≠ 0) :
    EIv.mem (qreIv sLo sHi yLo yHi) (Qre y s) := by
  have hySq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0 := by positivity
  have hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0 := by positivity
  rw [← reNum_quotient_eq_Qre hy hp hm]
  exact qreIv_mem (reNum_mem hs hyBox hy1) (imNum_mem hs hyBox hy1)
    (reDen_mem hs hyBox) (imDen_mem hs hyBox) (denAbs2_mem hs hyBox)

/-- At nonzero depth, the removable enclosure contains `Qim / y`. -/
theorem rIv_mem_Qim_over_y {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hyBox : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy : y ≠ 0) :
    EIv.mem (rIv sLo sHi yLo yHi) (Qim y s / y) := by
  have hySq : 0 < y ^ 2 := sq_pos_of_ne_zero hy
  have hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0 := by positivity
  have hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0 := by positivity
  rw [← imNum_quotient_eq_Qim_over_y hy hp hm]
  exact rIv_mem (reNum_mem hs hyBox hy1) (imNumOverY_mem hs hyBox hy1)
    (reDen_mem hs hyBox) (imDenOverY_mem hs hyBox) (denAbs2_mem hs hyBox)

/-! ## What remains

`qreIv_mem` and `rIv_mem` now consume the same denominator:
`c*c + (dOverY*y)*(dOverY*y)`, with `d = dOverY*y`. The apparent mismatch was
an abstraction defect in the old `r_comp_mem` statement. Its interval
composition never required the denominator to be reconstructed from the
components used in the numerator.

The exact quotient identities and their enclosure consequences are now proved.
What remains is to extract the inequalities checked by each `o9Box` mode and
feed them into the two mode lemmas. No `sorry` stands in for that assembly.
-/

end Retention

#print axioms Retention.qreIv_mem
#print axioms Retention.rIv_mem
#print axioms Retention.reNum_quotient_eq_Qre
#print axioms Retention.imNum_quotient_eq_Qim_over_y
#print axioms Retention.qreIv_mem_Qre
#print axioms Retention.rIv_mem_Qim_over_y
