import Zeta23Ext.EForm3.O9Num

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
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY)
    (hC : EIv.mem (boxParts sLo sHi yLo yHi).reDen c)
    (hD : EIv.mem (boxParts sLo sHi yLo yHi).imDenOverY dOverY)
    (hE : EIv.mem (boxParts sLo sHi yLo yHi).denAbs2 (c * c + dOverY * dOverY)) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((bOverY * c - a * dOverY) / (c * c + dOverY * dOverY))) := by
  unfold rIv
  exact O9Seam.r_comp_mem hA hB hC hD hE

/-! ## The same two, with every hypothesis discharged

The two lemmas above are conditional on the seven field enclosures. All seven
now exist (`O9Parts`, `O9Num`), so the conditions can be discharged and the
compositions stated at one box against the box's own reals. Only the numerator
components stay abstract, because those are the ones the trig and hyperbolic
leaves fix and there is no benefit to writing them out here.

The denominator is written out, because it is small and because it is what the
discharged hypothesis is about: `c = s² − y² − 2`, `d = 2sy`, `dOverY = 2s`.
-/

variable {s y : ℝ}

/-- **`qreIv` encloses `Re(num/den)` over the box**, conditional now only on
the two numerator components. The `denAbs2` hypothesis that `qreIv_mem` carried
is discharged by `O9Parts.denAbs2_mem`, and the `imNum` one by
`O9Num.imNum_mem`, which is why this closes and did not before. -/
theorem qreIv_mem_box {a bOverY : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s) (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY) :
    EIv.mem (qreIv sLo sHi yLo yHi)
      ((a * (s * s - y * y - ((2:ℤ):ℝ)) + bOverY * y * (s * ((2:ℤ):ℝ) * y))
        / ((s * s - y * y - ((2:ℤ):ℝ)) * (s * s - y * y - ((2:ℤ):ℝ))
            + s * ((2:ℤ):ℝ) * y * (s * ((2:ℤ):ℝ) * y))) :=
  qreIv_mem hA (imNum_mem hy hB) (reDen_mem hs hy) (imDen_mem hs hy)
    (denAbs2_mem hs hy)

/-- **`rIv` encloses the removable branch over the box.**

This one goes through `O9Seam.r_comp_mem'` rather than `r_comp_mem`. The
difference is the real under the quotient: `rIv` divides by `denAbs2`, which
encloses `c*c + d*d`, and `O9Real.im_div_over_y` writes `c² + (dOverY·y)²`
there as well. `r_comp_mem` instead writes `c*c + dOverY*dOverY` into both its
hypothesis and its conclusion, which is self-consistent and provable but asks
`denAbs2` for a real it does not enclose, so it cannot be instantiated at a
box. Nothing here divides by `y`. -/
theorem rIv_mem_box {a bOverY : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s) (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((bOverY * (s * s - y * y - ((2:ℤ):ℝ)) - a * (s * ((2:ℤ):ℝ)))
        / ((s * s - y * y - ((2:ℤ):ℝ)) * (s * s - y * y - ((2:ℤ):ℝ))
            + s * ((2:ℤ):ℝ) * y * (s * ((2:ℤ):ℝ) * y)))) := by
  unfold rIv
  exact O9Seam.r_comp_mem' hA hB (reDen_mem hs hy) (imDenOverY_mem hs hy)
    (denAbs2_mem hs hy)

/-! ## What remains

With all seven fields supplied and both compositions instantiated, what stands
between the kernel-checked table and O9 is the arithmetic of the two modes.
`dam_le_of_mode1` is proved; `dam_le_of_mode2` needs the enclosures above read
back against `Qre` and `Qim` through `BandDual.phiC_mem`, whose `y ≠ 0`
hypothesis `O9Sound.dam_zero_le` already routes around. No `sorry` stands in
for any of it.
-/

end Retention

#print axioms Retention.qreIv_mem
#print axioms Retention.rIv_mem
#print axioms Retention.qreIv_mem_box
#print axioms Retention.rIv_mem_box
