import Mathlib

/-!
# The real-arithmetic content of `qreIv` and `rIv`

`qreIv` does not compute a complex quotient and take its real part. It computes
the real part directly, as

    Re((a + b i)/(c + d i)) = (a c + b d) / (c² + d²)

and the imaginary part as `(b c − a d) / (c² + d²)`. That is why it is narrower
than `CIv.div`'s real part — measured on three boxes, by about 1% on the widest
— and it is why the soundness seam cannot be borrowed from `phiC_mem`.

This file isolates the mathematical content of that choice: two identities
about real and imaginary parts of a complex quotient, stated over plain reals
so they need nothing from the package. The interval seam then composes these
with the `_mem` lemmas already in `Iv.lean`.

Stated with `0 < c^2 + d^2` rather than `c + d*I ≠ 0` on purpose: the interval
side establishes positivity of the enclosure of `denAbs2` (`o9_leaf2d._parts_ok`
is exactly `den_abs2.lo > 0`), so this is the hypothesis that will actually be
available, and phrasing it any other way would just move work to the caller.
-/

namespace O9Real

open Complex

/-- **The real part of a complex quotient, componentwise.** -/
theorem re_div_eq (a b c d : ℝ) (h : 0 < c ^ 2 + d ^ 2) :
    ((⟨a, b⟩ : ℂ) / (⟨c, d⟩ : ℂ)).re = (a * c + b * d) / (c ^ 2 + d ^ 2) := by
  have hne : (⟨c, d⟩ : ℂ) ≠ 0 := by
    intro hz
    have hc : c = 0 := congrArg Complex.re hz
    have hd : d = 0 := congrArg Complex.im hz
    rw [hc, hd] at h; norm_num at h
  rw [Complex.div_re]
  have hnorm : Complex.normSq (⟨c, d⟩ : ℂ) = c ^ 2 + d ^ 2 := by
    simp [Complex.normSq_apply]; ring
  rw [hnorm]
  simp only []
  ring

/-- **The imaginary part of a complex quotient, componentwise.** -/
theorem im_div_eq (a b c d : ℝ) (h : 0 < c ^ 2 + d ^ 2) :
    ((⟨a, b⟩ : ℂ) / (⟨c, d⟩ : ℂ)).im = (b * c - a * d) / (c ^ 2 + d ^ 2) := by
  have hne : (⟨c, d⟩ : ℂ) ≠ 0 := by
    intro hz
    have hc : c = 0 := congrArg Complex.re hz
    have hd : d = 0 := congrArg Complex.im hz
    rw [hc, hd] at h; norm_num at h
  rw [Complex.div_im]
  have hnorm : Complex.normSq (⟨c, d⟩ : ℂ) = c ^ 2 + d ^ 2 := by
    simp [Complex.normSq_apply]; ring
  rw [hnorm]
  simp only []
  ring

/-- **The removable branch, divided out.**

`rIv` carries `Im(num/den)/y` and negates it, because `Phi2 (s + i y)` has
imaginary part `−Qim`. Writing the division by `y` inside each factor — as
`imNumOverY` and `imDenOverY` do — is what keeps `y = 0` an ordinary point:
the quotient below never divides by `y` at all.
-/
theorem im_div_over_y (a bOverY c dOverY y : ℝ) (hy : y ≠ 0)
    (h : 0 < c ^ 2 + (dOverY * y) ^ 2) :
    ((⟨a, bOverY * y⟩ : ℂ) / (⟨c, dOverY * y⟩ : ℂ)).im / y
      = (bOverY * c - a * dOverY) / (c ^ 2 + (dOverY * y) ^ 2) := by
  rw [im_div_eq a (bOverY * y) c (dOverY * y) h]
  field_simp

end O9Real

#print axioms O9Real.re_div_eq
#print axioms O9Real.im_div_eq
#print axioms O9Real.im_div_over_y
