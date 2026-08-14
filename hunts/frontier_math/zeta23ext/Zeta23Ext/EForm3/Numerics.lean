import Zeta23Ext.EForm3.Taylor
import Zeta23Ext.EForm3.ClosedForm

/-!
# Numerical constants

Explicit rational enclosures for `√2`, `cos (1/√2)`, `sin (1/√2)`, `A = √2 sin (1/√2)`,
together with the elementary hyperbolic inequalities
`sinh t ≤ t cosh t`, `cosh t - 1 ≤ (t²/2) cosh t` and hence `cosh t ≤ 32/31` for `|t| ≤ 1/4`.
-/

open scoped Real

namespace Retention

/-! ### `√2` -/

lemma sqrt2_lb : (1.4142135 : ℝ) ≤ Real.sqrt 2 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

lemma sqrt2_ub : Real.sqrt 2 ≤ 1.4142136 := by
  nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

lemma sqrt2_ne_zero : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos

/-- `(1/√2)^2 = 1/2`. -/
lemma inv_sqrt2_sq : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, sqrt2_sq]

lemma sqrt2_mul_inv_sqrt2 : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
  field_simp

/-! ### `cos (1/√2)` and `sin (1/√2)` -/

/-- `cos (1/√2) ≥ 1 - 1/4 + 1/96 - 1/5760 = 0.7602430...`. -/
lemma cos_inv_sqrt2_lb : (0.760243 : ℝ) ≤ Real.cos (1 / Real.sqrt 2) := by
  have h := cos_ge_taylor6 (1 / Real.sqrt 2)
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1/2 := inv_sqrt2_sq
  have h4 : (1 / Real.sqrt 2) ^ 4 = 1/4 := by
    have e : (1 / Real.sqrt 2) ^ 4 = ((1 / Real.sqrt 2) ^ 2) ^ 2 := by ring
    rw [e, h2]; norm_num
  have h6 : (1 / Real.sqrt 2) ^ 6 = 1/8 := by
    have e : (1 / Real.sqrt 2) ^ 6 = ((1 / Real.sqrt 2) ^ 2) ^ 3 := by ring
    rw [e, h2]; norm_num
  rw [h2, h4, h6] at h
  linarith

/-- `cos (1/√2) ≤ 1 - 1/4 + 1/96 = 0.7604166...`. -/
lemma cos_inv_sqrt2_ub : Real.cos (1 / Real.sqrt 2) ≤ 0.7604167 := by
  have h := cos_le_taylor4 (1 / Real.sqrt 2)
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1/2 := inv_sqrt2_sq
  have h4 : (1 / Real.sqrt 2) ^ 4 = 1/4 := by
    have e : (1 / Real.sqrt 2) ^ 4 = ((1 / Real.sqrt 2) ^ 2) ^ 2 := by ring
    rw [e, h2]; norm_num
  rw [h2, h4] at h
  linarith

lemma inv_sqrt2_nonneg : (0:ℝ) ≤ 1 / Real.sqrt 2 := by positivity

/-- `A = √2 sin (1/√2) ≥ 11/12`. -/
lemma Aconst_lb : (11/12 : ℝ) ≤ Aconst := by
  have h := sin_ge_taylor3 inv_sqrt2_nonneg
  have h3 : (1 / Real.sqrt 2) ^ 3 = (1/2) * (1 / Real.sqrt 2) := by
    have e : (1 / Real.sqrt 2) ^ 3 = ((1 / Real.sqrt 2) ^ 2) * (1 / Real.sqrt 2) := by ring
    rw [e, inv_sqrt2_sq]
  rw [h3] at h
  have hm : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := sqrt2_mul_inv_sqrt2
  unfold Aconst
  nlinarith [sqrt2_pos, h, hm]

/-- `A = √2 sin (1/√2) ≤ 441/480`. -/
lemma Aconst_ub : Aconst ≤ 441/480 := by
  have h := sin_le_taylor5 inv_sqrt2_nonneg
  have h3 : (1 / Real.sqrt 2) ^ 3 = (1/2) * (1 / Real.sqrt 2) := by
    have e : (1 / Real.sqrt 2) ^ 3 = ((1 / Real.sqrt 2) ^ 2) * (1 / Real.sqrt 2) := by ring
    rw [e, inv_sqrt2_sq]
  have h5 : (1 / Real.sqrt 2) ^ 5 = (1/4) * (1 / Real.sqrt 2) := by
    have e : (1 / Real.sqrt 2) ^ 5 = ((1 / Real.sqrt 2) ^ 2) ^ 2 * (1 / Real.sqrt 2) := by ring
    rw [e, inv_sqrt2_sq]; norm_num
  rw [h3, h5] at h
  have hm : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := sqrt2_mul_inv_sqrt2
  unfold Aconst
  nlinarith [sqrt2_pos, h, hm]

/-! ### Hyperbolic bounds -/

lemma sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have key : ∀ z : ℝ, 0 ≤ z → 0 ≤ z * Real.cosh z - Real.sinh z := by
    refine nonneg_of_deriv_nonneg (F := fun z => z * Real.sinh z) ?_ (by simp) ?_
    · intro z
      have h1 : HasDerivAt (fun z : ℝ => z * Real.cosh z)
          (1 * Real.cosh z + z * Real.sinh z) z :=
        (hasDerivAt_id z).mul (Real.hasDerivAt_cosh z)
      exact (h1.sub (Real.hasDerivAt_sinh z)).congr_deriv (by ring)
    · intro z hz
      exact mul_nonneg hz (Real.sinh_nonneg_iff.2 hz)
  linarith [key t ht]

lemma cosh_sub_one_le (t : ℝ) : Real.cosh t - 1 ≤ t^2/2 * Real.cosh t := by
  have main : ∀ z : ℝ, 0 ≤ z → Real.cosh z - 1 ≤ z^2/2 * Real.cosh z := by
    intro z hz
    have hid : Real.cosh z = 1 + 2 * Real.sinh (z/2)^2 := by
      have h := Real.cosh_two_mul (z/2)
      rw [show 2 * (z/2) = z by ring] at h
      have h2 := Real.cosh_sq_sub_sinh_sq (z/2)
      linarith
    have hs : Real.sinh (z/2) ≤ (z/2) * Real.cosh (z/2) := sinh_le_mul_cosh (by linarith)
    have hs0 : 0 ≤ Real.sinh (z/2) := Real.sinh_nonneg_iff.2 (by linarith)
    have hsq : Real.sinh (z/2)^2 ≤ (z/2)^2 * Real.cosh (z/2)^2 := by
      have := mul_self_le_mul_self hs0 hs
      nlinarith [Real.cosh_pos (z/2)]
    have hch : Real.cosh (z/2)^2 ≤ Real.cosh z := by
      nlinarith [Real.cosh_sq_sub_sinh_sq (z/2), sq_nonneg (Real.sinh (z/2)), hid, hs0]
    nlinarith [Real.cosh_pos (z/2), sq_nonneg (z/2), Real.cosh_pos z]
  rcases le_total 0 t with h | h
  · exact main t h
  · have := main (-t) (by linarith)
    rw [Real.cosh_neg] at this
    have : (-t)^2 = t^2 := by ring
    nlinarith [main (-t) (by linarith), Real.cosh_neg t]

/-- `cosh t ≤ 32/31` for `|t| ≤ 1/4`. -/
lemma cosh_le_of_abs_le_quarter {t : ℝ} (ht : |t| ≤ 1/4) : Real.cosh t ≤ 32/31 := by
  have h1 := cosh_sub_one_le t
  have h2 : t^2 ≤ 1/16 := by
    have := abs_le.1 ht
    nlinarith [this.1, this.2]
  nlinarith [Real.cosh_pos t, Real.one_le_cosh t]

lemma one_le_cosh' (t : ℝ) : 1 ≤ Real.cosh t := Real.one_le_cosh t

/-- `1 + t^2/2 ≤ cosh t`. -/
lemma cosh_ge_one_add_sq (t : ℝ) : 1 + t^2/2 ≤ Real.cosh t := by
  have main : ∀ z : ℝ, 0 ≤ z → 0 ≤ Real.cosh z - (1 + z^2/2) := by
    refine nonneg_of_deriv_nonneg (F := fun z => Real.sinh z - z) ?_ (by simp) ?_
    · intro z
      have h1 : HasDerivAt (fun z : ℝ => 1 + z^2/2) z z :=
        ((hasDerivAt_const z (1:ℝ)).add
          ((hasDerivAt_pow 2 z).div_const 2)).congr_deriv (by norm_num)
      exact ((Real.hasDerivAt_cosh z).sub h1).congr_deriv (by ring)
    · intro z hz
      have := Real.self_le_sinh_iff.mpr hz
      linarith
  rcases le_total 0 t with h | h
  · linarith [main t h]
  · have h2 := main (-t) (by linarith)
    rw [Real.cosh_neg] at h2
    have e : (-t)^2 = t^2 := by ring
    rw [e] at h2
    linarith

end Retention
