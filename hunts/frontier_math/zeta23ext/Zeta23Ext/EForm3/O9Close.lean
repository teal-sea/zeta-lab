import Zeta23Ext.EForm3.O9Final
import Zeta23Ext.EForm3.O9Bridge

/-!
# The closing quotient: componentwise parts give `Qre`

Step 1 of the closing chain, stated so the enormous explicit expression never
appears. Naming `Phi2_closed`'s numerator and denominator as `numC` and `denC`
lets the join be said in one line each:

* the four field values are `(numC).re`, `(numC).im`, `(denC).re`, `(denC).im`;
* `O9Real.re_div_eq` turns the componentwise quotient into `Re (numC / denC)`;
* `Phi2_closed` says `numC / denC` is `Phi2 (s + i y)`;
* `re_Phi2_eq_Qre` says its real part is `Qre y s`.

A first draft wrote the trigonometric expression inline on both sides and grew
past the point where either could be read. Binding the parts by hypothesis
instead keeps the statement the size of the idea.
-/

namespace Retention

open Complex BandDual

/-- `Phi2_closed`'s numerator at `z = s + i y`. -/
noncomputable def numC (s y : ℝ) : ℂ :=
  2 * (((s : ℂ) + (y : ℝ) * I) * Complex.sin (((s : ℂ) + (y : ℝ) * I) / 2)
      * ((Real.cos (Real.sqrt 2 / 2) : ℝ) : ℂ)
    - ((Real.sqrt 2 : ℝ) : ℂ) * Complex.cos (((s : ℂ) + (y : ℝ) * I) / 2)
      * ((Real.sin (Real.sqrt 2 / 2) : ℝ) : ℂ))

/-- `Phi2_closed`'s denominator, `z² − 2`. -/
noncomputable def denC (s y : ℝ) : ℂ := ((s : ℂ) + (y : ℝ) * I) ^ 2 - 2

/-- `Re (z² − 2) = s·s − y·y − 2`, the value `reDen_mem` encloses. -/
theorem denC_re (s y : ℝ) : (denC s y).re = s * s - y * y - ((2:ℤ):ℝ) := by
  simp [denC, pow_two, Complex.mul_re, Complex.sub_re]

/-- `Im (z² − 2) = 2 s y`, the value `imDen_mem` encloses. -/
theorem denC_im (s y : ℝ) : (denC s y).im = s * ((2:ℤ):ℝ) * y := by
  simp [denC, pow_two, Complex.mul_im, Complex.sub_im]
  ring

/-- **The closing quotient.**

Given that the four field values are the parts of `numC` and `denC`, the
componentwise real quotient is `Qre y s`. This is the whole of step 1; the
`boxParts` lemmas supply the four hypotheses and `qreIv_mem_box` supplies the
enclosure of the left-hand side. -/
theorem qre_quotient_eq {s y a b c d : ℝ}
    (ha : a = (numC s y).re) (hb : b = (numC s y).im)
    (hc : c = (denC s y).re) (hd : d = (denC s y).im)
    (hden : 0 < c * c + d * d)
    (hz : ((s : ℂ) + (y : ℝ) * I) ^ 2 ≠ 2)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    (a * c + b * d) / (c * c + d * d) = Qre y s := by
  have hsq : (0:ℝ) < c ^ 2 + d ^ 2 := by nlinarith [hden]
  have hquot : (a * c + b * d) / (c * c + d * d)
      = ((⟨a, b⟩ : ℂ) / (⟨c, d⟩ : ℂ)).re := by
    rw [O9Real.re_div_eq a b c d hsq]
    ring_nf
  rw [hquot]
  have hnum : (⟨a, b⟩ : ℂ) = numC s y := by
    apply Complex.ext <;> simp [ha, hb]
  have hdenC : (⟨c, d⟩ : ℂ) = denC s y := by
    apply Complex.ext <;> simp [hc, hd]
  rw [hnum, hdenC]
  have hPhi : numC s y / denC s y = Phi2 ((s : ℂ) + (y : ℝ) * I) := by
    rw [Phi2_closed _ hz, numC, denC]
  rw [hPhi, re_Phi2_eq_Qre y s hp hm]

/-- **The removable-branch quotient.**

Step 2. Same join as `qre_quotient_eq`, through the `/y` variants: with
`bOverY = Im(numC)/y` and `dOverY = Im(denC)/y`, the componentwise quotient is
`Qim y s / y`.

The negation is `rIv`'s own — `Phi2 (s + i y)` has imaginary part `−Qim`, so the
composition computes `−Qim/y` and negating puts it back. The denominator is the
undivided `c·c + d·d`, since only the numerator's terms carry the `/y`. -/
theorem r_quotient_eq {s y a bOverY c d dOverY : ℝ}
    (hy : y ≠ 0)
    (ha : a = (numC s y).re) (hb : bOverY * y = (numC s y).im)
    (hc : c = (denC s y).re) (hd : dOverY * y = (denC s y).im)
    (hden : 0 < c * c + d * d)
    (hdd : d = dOverY * y)
    (hz : ((s : ℂ) + (y : ℝ) * I) ^ 2 ≠ 2)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    -((bOverY * c - a * dOverY) / (c * c + d * d)) = Qim y s / y := by
  -- Eliminate `d` outright. Without this the final cancellation is invisible:
  -- the numerator's `y` only cancels once `d` is known to carry one.
  subst hdd
  have hsq : (0:ℝ) < c ^ 2 + (dOverY * y) ^ 2 := by nlinarith [hden]
  have hIm : ((⟨a, bOverY * y⟩ : ℂ) / (⟨c, dOverY * y⟩ : ℂ)).im
      = (bOverY * y * c - a * (dOverY * y)) / (c ^ 2 + (dOverY * y) ^ 2) :=
    O9Real.im_div_eq a (bOverY * y) c (dOverY * y) hsq
  have hnum : (⟨a, bOverY * y⟩ : ℂ) = numC s y := by
    apply Complex.ext <;> simp [ha, hb]
  have hdenC : (⟨c, dOverY * y⟩ : ℂ) = denC s y := by
    apply Complex.ext <;> simp [hc, hd]
  rw [hnum, hdenC] at hIm
  have hPhi : numC s y / denC s y = Phi2 ((s : ℂ) + (y : ℝ) * I) := by
    rw [Phi2_closed _ hz, numC, denC]
  rw [hPhi, im_Phi2_eq_neg_Qim y s hp hm] at hIm
  have hQ : Qim y s
      = -((bOverY * y * c - a * (dOverY * y)) / (c ^ 2 + (dOverY * y) ^ 2)) := by
    rw [← hIm]; ring
  rw [hQ]
  have hy2 : c ^ 2 + (dOverY * y) ^ 2 ≠ 0 := ne_of_gt hsq
  field_simp

end Retention

#print axioms Retention.denC_re
#print axioms Retention.denC_im
#print axioms Retention.qre_quotient_eq
#print axioms Retention.r_quotient_eq
