import Zeta23Ext.EForm3.O9NumShape
import Zeta23Ext.EForm3.ClosedForm

/-!
# `BandDual.Phi2` and the retention integrals `Qre`, `Qim`

`O9NumShape` reaches `BandDual.Phi2`: `qreIv` encloses `Re Phi2 (s + i y)` and
`rIv` encloses `-Im Phi2 (s + i y) / y`. `O9Sound` states the damage obligation
in terms of `Retention.Qre` and `Retention.Qim`, which are integrals against the
window `g`. Those are two different definitions of the same two numbers and
nothing in the package had connected them, so the enclosure chain stopped one
step short of the quantities the obligation is about.

This file is that step:

* `phi2_re_eq_Qre`  : `Re Phi2 (s + i y) = Qre y s`
* `phi2_im_eq_neg_Qim` : `Im Phi2 (s + i y) = -Qim y s`

Both for `y ≠ 0`, which is where the whole O9 chain lives (`O9Sound.dam_zero_le`
handles `y = 0` without any of this).

The route is closed forms on both sides, not an integral manipulation.
`BandDual.Phi2 z = s(z + √2) + s(z - √2)` with `s(u) = sin(u/2)/u`, and
`Retention.Qre_closed` / `Qim_closed` give the same two-term shape from explicit
antiderivatives. Splitting `sin(u/2)/u` into real and imaginary parts is
`O9Real.re_div_eq` / `im_div_eq`, already proved. So the bridge is an identity
between two elementary expressions and needs no new analysis.

The sign on the imaginary side is the one `O9Comp.rIv` carries and the one the
1-D route got wrong once: `Phi2 (s + i y)` has imaginary part `-Qim`, so the
removable branch `R = Qim y s / y` is `-Im Phi2 / y`, which is what `rIv`
encloses.

Nothing here is evidence for or against the Riemann hypothesis.
-/

namespace Retention

open BandDual

/-- `sin` at a point of the upper half plane, componentwise. Same computation
as `BandDual.sinCosC_mem`'s first half, in the form this file consumes. -/
theorem sin_pt_re_im (a b : ℝ) :
    (Complex.sin ((a : ℂ) + (b : ℝ) * Complex.I)).re = Real.sin a * Real.cosh b
    ∧ (Complex.sin ((a : ℂ) + (b : ℝ) * Complex.I)).im = Real.cos a * Real.sinh b := by
  constructor
  · rw [Complex.sin_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]
  · rw [Complex.sin_add_mul_I]
    simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
      Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
      Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-- `p ^ 2 + y ^ 2` is positive off the real axis. -/
theorem sq_add_sq_pos {p y : ℝ} (hy : y ≠ 0) : 0 < p ^ 2 + y ^ 2 := by
  have hy2 : 0 < y ^ 2 := by
    rcases lt_or_gt_of_ne hy with h | h <;> nlinarith
  nlinarith [sq_nonneg p]

/-- **`s(u) = sin(u/2)/u`, componentwise**, at `u = p + i y` with `y ≠ 0`. -/
theorem sfunC_re_im (p y : ℝ) (hy : y ≠ 0) :
    (sfunC ((p : ℂ) + (y : ℝ) * Complex.I)).re
        = (Real.sin (p / 2) * Real.cosh (y / 2) * p
            + Real.cos (p / 2) * Real.sinh (y / 2) * y) / (p ^ 2 + y ^ 2)
      ∧ (sfunC ((p : ℂ) + (y : ℝ) * Complex.I)).im
        = (Real.cos (p / 2) * Real.sinh (y / 2) * p
            - Real.sin (p / 2) * Real.cosh (y / 2) * y) / (p ^ 2 + y ^ 2) := by
  have hpos : 0 < p ^ 2 + y ^ 2 := sq_add_sq_pos hy
  have hne : ((p : ℂ) + (y : ℝ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((p : ℂ) + (y : ℝ) * Complex.I).im = 0 := by rw [h]; simp
    simp at him
    exact hy him
  rw [sfunC, if_neg hne]
  have hhalf : ((p : ℂ) + (y : ℝ) * Complex.I) / 2
      = ((p / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℝ) * Complex.I := by
    push_cast
    ring
  rw [hhalf]
  obtain ⟨h1, h2⟩ := sin_pt_re_im (p / 2) (y / 2)
  have hnum : Complex.sin (((p / 2 : ℝ) : ℂ) + ((y / 2 : ℝ) : ℝ) * Complex.I)
      = (⟨Real.sin (p / 2) * Real.cosh (y / 2),
          Real.cos (p / 2) * Real.sinh (y / 2)⟩ : ℂ) := by
    apply Complex.ext
    · simpa using h1
    · simpa using h2
  have hden : ((p : ℂ) + (y : ℝ) * Complex.I) = (⟨p, y⟩ : ℂ) := by
    apply Complex.ext <;> simp
  rw [hnum, hden]
  exact ⟨O9Real.re_div_eq _ _ _ _ hpos, O9Real.im_div_eq _ _ _ _ hpos⟩

/-- The two half-plane points `Phi2` is the sum over. -/
theorem shift_pt (s y c : ℝ) :
    (s : ℂ) + (y : ℝ) * Complex.I + ((c : ℝ) : ℂ)
      = ((s + c : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
  push_cast
  ring

theorem shift_pt' (s y c : ℝ) :
    (s : ℂ) + (y : ℝ) * Complex.I - ((c : ℝ) : ℂ)
      = ((s - c : ℝ) : ℂ) + (y : ℝ) * Complex.I := by
  push_cast
  ring

/-- **The real bridge**: `Re Phi2 (s + i y) = Qre y s`, off the real axis. -/
theorem phi2_re_eq_Qre (s y : ℝ) (hy : y ≠ 0) :
    (Phi2 ((s : ℂ) + (y : ℝ) * Complex.I)).re = Qre y s := by
  have hy2 : 0 < y ^ 2 := by
    rcases lt_or_gt_of_ne hy with h | h <;> nlinarith
  have hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s + Real.sqrt 2)]
  have hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s - Real.sqrt 2)]
  have hp' : (s + Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s + Real.sqrt 2)]
  have hm' : (s - Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s - Real.sqrt 2)]
  obtain ⟨hr1, -⟩ := sfunC_re_im (s + Real.sqrt 2) y hy
  obtain ⟨hr2, -⟩ := sfunC_re_im (s - Real.sqrt 2) y hy
  rw [Qre_closed y s hp hm, Phi2, shift_pt, shift_pt', Complex.add_re, hr1, hr2]
  field_simp
  ring

/-- **The imaginary bridge**: `Im Phi2 (s + i y) = -Qim y s`, off the real axis.

The sign is the content. `rIv` encloses `-Im Phi2 / y`, and this is why that
equals the removable branch `R = Qim y s / y` the O9 table is built on. -/
theorem phi2_im_eq_neg_Qim (s y : ℝ) (hy : y ≠ 0) :
    (Phi2 ((s : ℂ) + (y : ℝ) * Complex.I)).im = -Qim y s := by
  have hy2 : 0 < y ^ 2 := by
    rcases lt_or_gt_of_ne hy with h | h <;> nlinarith
  have hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s + Real.sqrt 2)]
  have hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s - Real.sqrt 2)]
  have hp' : (s + Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s + Real.sqrt 2)]
  have hm' : (s - Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (s - Real.sqrt 2)]
  obtain ⟨-, hi1⟩ := sfunC_re_im (s + Real.sqrt 2) y hy
  obtain ⟨-, hi2⟩ := sfunC_re_im (s - Real.sqrt 2) y hy
  rw [Qim_closed y s hp hm, Phi2, shift_pt, shift_pt', Complex.add_im, hi1, hi2]
  field_simp
  ring

/-! ## The enclosures, read against `Qre` and `Qim`

The two lemmas `O9NumShape` ends on, with `Phi2` replaced by the quantities the
damage obligation is stated in. -/

/-- **`qreIv` encloses `Qre y s`.** -/
theorem qreIv_mem_Qre {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy0 : y ≠ 0) :
    EIv.mem (qreIv sLo sHi yLo yHi) (Qre y s) := by
  rw [← phi2_re_eq_Qre s y hy0]
  exact qreIv_mem_phi2 hs hy hy1 hy0

/-- **`rIv` encloses the removable branch `R = Qim y s / y`.** -/
theorem rIv_mem_R {sLo sHi yLo yHi : ℤ} {s y : ℝ}
    (hs : EIv.mem (some ⟨sLo, sHi⟩) s)
    (hy : EIv.mem (some ⟨yLo, yHi⟩) y)
    (hy1 : |y / ((2:ℤ):ℝ)| ≤ 1) (hy0 : y ≠ 0) :
    EIv.mem (rIv sLo sHi yLo yHi) (Qim y s / y) := by
  have h := rIv_mem_phi2 hs hy hy1 hy0
  rw [phi2_im_eq_neg_Qim s y hy0] at h
  have heq : -(-Qim y s / y) = Qim y s / y := by ring
  rwa [heq] at h

end Retention

#print axioms Retention.sfunC_re_im
#print axioms Retention.phi2_re_eq_Qre
#print axioms Retention.phi2_im_eq_neg_Qim
#print axioms Retention.qreIv_mem_Qre
#print axioms Retention.rIv_mem_R
