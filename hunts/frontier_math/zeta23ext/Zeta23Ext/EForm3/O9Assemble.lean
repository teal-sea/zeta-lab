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
`−(bOverY·c − a·dOverY)/(c² + d²)` — note the denominator is the *undivided*
`|den|²`, matching `denAbs2`. Only the numerator's terms carry the `/y`, which
is what `O9Real.im_div_over_y` states and what makes the enclosure exist at
`y = 0` at all.

The first version of this lemma put `dOverY * dOverY` in the denominator. It
compiled and was true, because `E` is a parameter — and it was uninstantiable,
because no `denAbs2` encloses that quantity. A lemma can be true, well-typed,
and still say something other than what is needed; only trying to apply it
finds out. -/
theorem rIv_mem {a bOverY c d dOverY : ℝ}
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY)
    (hC : EIv.mem (boxParts sLo sHi yLo yHi).reDen c)
    (hD : EIv.mem (boxParts sLo sHi yLo yHi).imDenOverY dOverY)
    (hE : EIv.mem (boxParts sLo sHi yLo yHi).denAbs2 (c * c + d * d)) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((bOverY * c - a * dOverY) / (c * c + d * d))) := by
  unfold rIv
  exact O9Seam.r_comp_mem hA hB hC hD hE

/-! ## Instantiated at a real box

The statements above are parametric, and the previous version of `rIv_mem` was
true and uninstantiable in exactly that gap. So both are now applied at an
actual box, with the denominator supplied by `O9Parts.denAbs2_mem` rather than
assumed. If a statement drifts from what `denAbs2` provides again, this fails
to elaborate.
-/

/-- `rIv` at a real box, with every hypothesis discharged from `O9Parts`. -/
theorem rIv_mem_box {s y : ℝ} {a bOverY : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s) (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNumOverY bOverY) :
    EIv.mem (rIv sLo sHi yLo yHi)
      (-((bOverY * (s * s - y * y - ((2:ℤ):ℝ)) - a * (s * ((2:ℤ):ℝ)))
        / ((s * s - y * y - ((2:ℤ):ℝ)) * (s * s - y * y - ((2:ℤ):ℝ))
          + (s * ((2:ℤ):ℝ) * y) * (s * ((2:ℤ):ℝ) * y)))) :=
  rIv_mem hA hB (reDen_mem hs hy) (imDenOverY_mem hs hy) (denAbs2_mem hs hy)

/-- `qreIv` at a real box, likewise. -/
theorem qreIv_mem_box {s y : ℝ} {a b : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s) (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hA : EIv.mem (boxParts sLo sHi yLo yHi).reNum a)
    (hB : EIv.mem (boxParts sLo sHi yLo yHi).imNum b) :
    EIv.mem (qreIv sLo sHi yLo yHi)
      ((a * (s * s - y * y - ((2:ℤ):ℝ)) + b * (s * ((2:ℤ):ℝ) * y))
        / ((s * s - y * y - ((2:ℤ):ℝ)) * (s * s - y * y - ((2:ℤ):ℝ))
          + (s * ((2:ℤ):ℝ) * y) * (s * ((2:ℤ):ℝ) * y))) :=
  qreIv_mem hA hB (reDen_mem hs hy) (imDen_mem hs hy) (denAbs2_mem hs hy)

/-! ## What remains

`qreIv_mem` and `rIv_mem` take the denominator enclosure at `c*c + d*d` and at
`c*c + dOverY*dOverY` respectively. Those are different reals — the second is
the first divided by `y²` — so a box using **mode 2** needs both forms, related
by `y ≠ 0`. `O9Parts.denAbs2_mem` supplies the first directly.

That relation, and the two mode arithmetics that consume it
(`dam_le_of_mode1` is already proved; mode 2 is not), are the last step. No
`sorry` stands in for them.
-/

end Retention

#print axioms Retention.qreIv_mem
#print axioms Retention.rIv_mem
#print axioms Retention.qreIv_mem_box
#print axioms Retention.rIv_mem_box
