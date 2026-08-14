import Zeta23Ext.BandCert.Phi
import Zeta23Ext.EForm3.ClosedForm

/-!
# The bridge: `Phi2`'s parts are `Qre` and `−Qim`

`O9-MISSING-BRIDGE.md` records that the O9 chain had two halves that never met
in Lean. `Qre` and `Qim` are integrals in `EForm3`; `Phi2` is a closed form in
`BandCert`; the identity relating them lived in a Python script and in
docstrings, and in no proof.

This file proves it. The route is not through the integrals at all — both sides
already have closed forms, so the identity is algebra:

* `Qre_closed` / `Qim_closed` give `Qre a b` and `Qim a b` as a sum over the two
  poles `b ± √2`, each term a fraction over `a² + (b ± √2)²`;
* `Phi2 z = sfunC (z + √2) + sfunC (z − √2)`, and `sfunC u = sin(u/2)/u`.

So it suffices to split one `sfunC` at a complex argument into real and
imaginary parts and match it against one term. That is `sfunC_parts` below; the
two-pole sum then follows by adding.
-/

namespace Retention

open Complex BandDual

/-- `Re (sin (x + i b)) = sin x · cosh b`.

Stated on atomic reals rather than inline: with the argument written as `↑(p/2)`
the cast gets pushed inward by `simp` and the `ofReal` lemmas stop matching,
which is a Lean detail rather than a mathematical one but costs a proof either
way. `Phi.lean` proves the same split inline where its arguments are already
atomic. -/
private theorem csin_re (x b : ℝ) :
    (Complex.sin ((x : ℂ) + (b : ℝ) * I)).re = Real.sin x * Real.cosh b := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-- `Im (sin (x + i b)) = cos x · sinh b`. -/
private theorem csin_im (x b : ℝ) :
    (Complex.sin ((x : ℂ) + (b : ℝ) * I)).im = Real.cos x * Real.sinh b := by
  rw [Complex.sin_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re, Complex.sinh_ofReal_re,
    Complex.cosh_ofReal_re, Complex.sin_ofReal_im, Complex.cos_ofReal_im,
    Complex.sinh_ofReal_im, Complex.cosh_ofReal_im]

/-- One pole, split into real and imaginary parts.

`sin((p + i a)/2) = sin(p/2) cosh(a/2) + i cos(p/2) sinh(a/2)` and
`1/(p + i a) = (p − i a)/(p² + a²)`, so multiplying out gives the two
fractions below — which are exactly one term of `Qre_closed` and minus one term
of `Qim_closed`. -/
theorem sfunC_parts (p a : ℝ) (h : p ^ 2 + a ^ 2 ≠ 0) :
    (sfunC ((p : ℂ) + (a : ℝ) * I)).re
        = (a * Real.sinh (a / 2) * Real.cos (p / 2)
            + p * Real.cosh (a / 2) * Real.sin (p / 2)) / (a ^ 2 + p ^ 2)
      ∧ (sfunC ((p : ℂ) + (a : ℝ) * I)).im
        = -((a * Real.cosh (a / 2) * Real.sin (p / 2)
            - p * Real.sinh (a / 2) * Real.cos (p / 2)) / (a ^ 2 + p ^ 2)) := by
  have hz : ((p : ℂ) + (a : ℝ) * I) ≠ 0 := by
    intro hz0
    have hre : p = 0 := by simpa using congrArg Complex.re hz0
    have him : a = 0 := by simpa using congrArg Complex.im hz0
    rw [hre, him] at h; norm_num at h
  have hne : (a ^ 2 + p ^ 2) ≠ 0 := by
    intro h0; exact h (by linarith [h0])
  unfold sfunC
  rw [if_neg hz]
  have hhalf : ((p : ℂ) + (a : ℝ) * I) / 2
      = ((p / 2 : ℝ) : ℂ) + ((a / 2 : ℝ) : ℝ) * I := by
    push_cast; ring
  have hre := csin_re (p / 2) (a / 2)
  have him := csin_im (p / 2) (a / 2)
  have hnsq : Complex.normSq ((p : ℂ) + (a : ℝ) * I) = p ^ 2 + a ^ 2 := by
    simp [Complex.normSq_apply]; ring
  rw [hhalf]
  constructor
  · rw [Complex.div_re, hre, him, hnsq]
    simp
    field_simp
    ring
  · rw [Complex.div_im, hre, him, hnsq]
    simp
    field_simp
    ring

/-- **The bridge, real part.**  `Re (Phi2 (s + i y)) = Qre y s`.

Both sides are sums over the two poles `s ± √2`. `Qre_closed` gives the left
term of each; `sfunC_parts` gives the right. The identity that was recorded in
`arm_identification.py` and in docstrings, and proved nowhere, is this. -/
theorem re_Phi2_eq_Qre (y s : ℝ)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    (Phi2 ((s : ℂ) + (y : ℝ) * I)).re = Qre y s := by
  have hsplit : (Phi2 ((s : ℂ) + (y : ℝ) * I))
      = sfunC (((s + Real.sqrt 2 : ℝ) : ℂ) + (y : ℝ) * I)
        + sfunC (((s - Real.sqrt 2 : ℝ) : ℂ) + (y : ℝ) * I) := by
    unfold Phi2
    congr 1 <;> · push_cast; ring_nf
  have hp' : (s + Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    intro h0; exact hp (by linarith [h0])
  have hm' : (s - Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    intro h0; exact hm (by linarith [h0])
  rw [hsplit, Complex.add_re, (sfunC_parts _ _ hp').1, (sfunC_parts _ _ hm').1,
    Qre_closed y s hp hm]

/-- **The bridge, imaginary part.**  `Im (Phi2 (s + i y)) = − Qim y s`.

The sign is the one `rIv` carries and `O9-2D-STATUS.md` §6 records a defect
about: `R` enters the table only squared, so a wrong sign here would be
invisible to every cell verdict. -/
theorem im_Phi2_eq_neg_Qim (y s : ℝ)
    (hp : y ^ 2 + (s + Real.sqrt 2) ^ 2 ≠ 0)
    (hm : y ^ 2 + (s - Real.sqrt 2) ^ 2 ≠ 0) :
    (Phi2 ((s : ℂ) + (y : ℝ) * I)).im = -Qim y s := by
  have hsplit : (Phi2 ((s : ℂ) + (y : ℝ) * I))
      = sfunC (((s + Real.sqrt 2 : ℝ) : ℂ) + (y : ℝ) * I)
        + sfunC (((s - Real.sqrt 2 : ℝ) : ℂ) + (y : ℝ) * I) := by
    unfold Phi2
    congr 1 <;> · push_cast; ring_nf
  have hp' : (s + Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    intro h0; exact hp (by linarith [h0])
  have hm' : (s - Real.sqrt 2) ^ 2 + y ^ 2 ≠ 0 := by
    intro h0; exact hm (by linarith [h0])
  rw [hsplit, Complex.add_im, (sfunC_parts _ _ hp').2, (sfunC_parts _ _ hm').2,
    Qim_closed y s hp hm]
  ring

end Retention

#print axioms Retention.sfunC_parts
#print axioms Retention.re_Phi2_eq_Qre
#print axioms Retention.im_Phi2_eq_neg_Qim
