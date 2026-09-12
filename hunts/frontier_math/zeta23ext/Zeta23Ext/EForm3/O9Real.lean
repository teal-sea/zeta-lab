import Zeta23Ext.BandCert.Iv

/-!
# The real-arithmetic content of `qreIv` and `rIv`

`qreIv` does not compute a complex quotient and take its real part. It computes
the real part directly, as

    Re((a + b i)/(c + d i)) = (a c + b d) / (c² + d²)

and the imaginary part as `(b c − a d) / (c² + d²)`. That is why it is narrower
than `CIv.div`'s real part, measured on three boxes, by about 1% on the widest,
and it is why the soundness seam cannot be borrowed from `phiC_mem`.

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
imaginary part `−Qim`. Writing the division by `y` inside each factor, as
`imNumOverY` and `imDenOverY` do, is what keeps `y = 0` an ordinary point:
the quotient below never divides by `y` at all.
-/
theorem im_div_over_y (a bOverY c dOverY y : ℝ) (hy : y ≠ 0)
    (h : 0 < c ^ 2 + (dOverY * y) ^ 2) :
    ((⟨a, bOverY * y⟩ : ℂ) / (⟨c, dOverY * y⟩ : ℂ)).im / y
      = (bOverY * c - a * dOverY) / (c ^ 2 + (dOverY * y) ^ 2) := by
  rw [im_div_eq a (bOverY * y) c (dOverY * y) h]
  field_simp

end O9Real

/-! ## The interval seam

The identities above say what the componentwise formulas compute. These say the
interval expressions `qreIv` and `rIv` are built from enclose it, given
enclosures of the four components. They are stated on the *shape* of the
composition rather than on `boxParts`, so they are independent of how the
leaves are assembled and stay true if the leaf layer is rebuilt again.
-/

namespace O9Seam

open BandDual

/-- The composition `qreIv` performs, sound. -/
theorem qre_comp_mem {A B C D E : EIv} {a b c d : ℝ}
    (hA : A.mem a) (hB : B.mem b) (hC : C.mem c) (hD : D.mem d)
    (hE : E.mem (c * c + d * d)) :
    (EIv.div (EIv.add (EIv.mul A C) (EIv.mul B D)) E).mem
      ((a * c + b * d) / (c * c + d * d)) :=
  EIv.div_mem (EIv.add_mem (EIv.mul_mem hA hC) (EIv.mul_mem hB hD)) hE

/-- **The composition `rIv` performs, with the denominator left abstract.**

This lemma replaced a version (`r_comp_mem`, retired 2026-08-18) that wrote
`c*c + dOverY*dOverY` into both its `E` hypothesis and its conclusion. That was
self-consistent, so it was provable, but it was the wrong real for the box:
`rIv` divides by `denAbs2`, which encloses `c*c + d*d` with `d = dOverY * y`
(`O9Comp.boxParts`), and `O9Real.im_div_over_y` puts `c ^ 2 + (dOverY * y) ^ 2`
under the quotient too. Instantiating the old lemma at a box therefore asked
`denAbs2` to enclose a real it does not, and it went through vacuously rather
than usefully: zero sorrys, standard axioms, and about nothing.

Leaving the denominator's real as a variable `e` removes the mismatch without
weakening anything: the retired statement is the case
`e = c*c + dOverY*dOverY`, and `rIv_mem_box` uses the case `e = c*c + d*d`,
which `denAbs2_mem` discharges. -/
theorem r_comp_mem' {A B C D E : EIv} {a bOverY c dOverY e : ℝ}
    (hA : A.mem a) (hB : B.mem bOverY) (hC : C.mem c) (hD : D.mem dOverY)
    (hE : E.mem e) :
    (EIv.neg (EIv.div (EIv.sub (EIv.mul B C) (EIv.mul A D)) E)).mem
      (-((bOverY * c - a * dOverY) / e)) :=
  EIv.neg_mem (EIv.div_mem (EIv.sub_mem (EIv.mul_mem hB hC) (EIv.mul_mem hA hD)) hE)

/-- The same for `qreIv`, denominator abstract. `qre_comp_mem`'s own `E`
hypothesis is already the right real, so this adds reach rather than a fix. -/
theorem qre_comp_mem' {A B C D E : EIv} {a b c d e : ℝ}
    (hA : A.mem a) (hB : B.mem b) (hC : C.mem c) (hD : D.mem d)
    (hE : E.mem e) :
    (EIv.div (EIv.add (EIv.mul A C) (EIv.mul B D)) E).mem
      ((a * c + b * d) / e) :=
  EIv.div_mem (EIv.add_mem (EIv.mul_mem hA hC) (EIv.mul_mem hB hD)) hE

/-- `denAbs2`'s shape is sound: it encloses `c*c + d*d`. -/
theorem denAbs2_mem {C D : EIv} {c d : ℝ} (hC : C.mem c) (hD : D.mem d) :
    (EIv.add (EIv.sqr C) (EIv.sqr D)).mem (c * c + d * d) :=
  EIv.add_mem (EIv.sqr_mem hC) (EIv.sqr_mem hD)

end O9Seam

#print axioms O9Real.re_div_eq
#print axioms O9Real.im_div_eq
#print axioms O9Real.im_div_over_y
#print axioms O9Seam.qre_comp_mem
#print axioms O9Seam.qre_comp_mem'
#print axioms O9Seam.r_comp_mem'
#print axioms O9Seam.denAbs2_mem
