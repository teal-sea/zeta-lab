import Mathlib

/-!
# The windowed-cosine kernel and its autocorrelation

This file sets up the objects of `PROBLEM.md`:

* `g u = cos (√2 * u)` for `|u| ≤ 1/2` and `0` otherwise;
* `A = √2 * sin (1/√2)`, which is `∫ g` (see `integral_g`);
* `c2`, the autocorrelation of `g`, defined here by its closed form and proved
  in `c2_eq_autocorrelation` to be the autocorrelation integral;
* the first two derivatives `d1c2`, `d2c2` of the closed form, and crude
  uniform bounds for them on `[0,1]`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace TruncEst

/-- The windowed cosine `g`. -/
def g (u : ℝ) : ℝ := if |u| ≤ 1 / 2 then Real.cos (Real.sqrt 2 * u) else 0

/-- `A = ∫ g = √2 * sin (1 / √2)`. -/
def A : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)

/-- The closed form of the autocorrelation `c2` on `[0, 1]`. -/
def c2core (w : ℝ) : ℝ :=
  Real.sin (Real.sqrt 2 * (1 - w)) / (2 * Real.sqrt 2) + (1 - w) * Real.cos (Real.sqrt 2 * w) / 2

/-- The autocorrelation `c2` of `g`: even, continuous, supported in `[-1,1]`. -/
def c2 (w : ℝ) : ℝ := if |w| ≤ 1 then c2core |w| else 0

/-- First derivative of `c2core`. -/
def d1c2 (w : ℝ) : ℝ :=
  -Real.cos (Real.sqrt 2 * (1 - w)) / 2 - Real.cos (Real.sqrt 2 * w) / 2
    - (Real.sqrt 2 / 2) * (1 - w) * Real.sin (Real.sqrt 2 * w)

/-- Second derivative of `c2core`. -/
def d2c2 (w : ℝ) : ℝ :=
  -(Real.sqrt 2 / 2) * Real.sin (Real.sqrt 2 * (1 - w)) + Real.sqrt 2 * Real.sin (Real.sqrt 2 * w)
    - (1 - w) * Real.cos (Real.sqrt 2 * w)

/-! ### Elementary numeric facts -/

lemma sqrt2_mul : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

lemma sqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

lemma sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt2_lb : (1.41 : ℝ) < Real.sqrt 2 := by
  nlinarith [sqrt2_sq, Real.sqrt_nonneg 2]

lemma sqrt2_ub : Real.sqrt 2 < 1.415 := by
  nlinarith [sqrt2_sq, Real.sqrt_nonneg 2]

/-- `A² > 3/4`; in particular `4 / A² ≤ 6`. -/
lemma A_sq_gt : (3:ℝ)/4 < A^2 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := sqrt2_pos
  have h1 : (0:ℝ) < 1 / Real.sqrt 2 := by positivity
  have h3 : 1 / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one h2]; nlinarith [sqrt2_lb]
  have key := Real.sin_gt_sub_cube h1 h3
  have hcube : (1 / Real.sqrt 2)^3 = (1/Real.sqrt 2) / 2 := by
    field_simp
    nlinarith [sqrt2_sq]
  rw [hcube] at key
  have hval : (7/8) * (1/Real.sqrt 2) = 7 * Real.sqrt 2 / 16 := by
    have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
    field_simp
    nlinarith [sqrt2_mul]
  have hs : 7 * Real.sqrt 2 / 16 < Real.sin (1/Real.sqrt 2) := by rw [← hval]; linarith
  have hpos : (0:ℝ) < 7 * Real.sqrt 2 / 16 := by positivity
  have hsq : (7 * Real.sqrt 2 / 16)^2 = 49/128 := by
    rw [div_pow, mul_pow, sqrt2_sq]; norm_num
  have hlt : (7 * Real.sqrt 2 / 16)^2 < Real.sin (1/Real.sqrt 2)^2 :=
    by nlinarith [hs, hpos]
  have hA : A^2 = 2 * Real.sin (1/Real.sqrt 2)^2 := by
    unfold A; rw [mul_pow, sqrt2_sq]
  rw [hA, hsq] at *
  linarith

lemma A_sq_pos : (0:ℝ) < A^2 := lt_trans (by norm_num) A_sq_gt

lemma four_div_A_sq_le : 4 / A^2 ≤ 6 := by
  rw [div_le_iff₀ A_sq_pos]; nlinarith [A_sq_gt]

lemma four_div_A_sq_pos : 0 < 4 / A^2 := div_pos (by norm_num) A_sq_pos

lemma A_ne_zero : A ≠ 0 := by
  intro h
  have := A_sq_pos
  rw [h] at this
  simp at this

/-! ### Basic properties of `c2` -/

@[simp] lemma c2core_one : c2core 1 = 0 := by simp [c2core]

lemma c2_of_nonneg {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : c2 w = c2core w := by
  rw [c2, if_pos (by rwa [abs_of_nonneg h0]), abs_of_nonneg h0]

lemma c2_neg (w : ℝ) : c2 (-w) = c2 w := by simp [c2]

lemma c2_eq_zero_of_one_lt {w : ℝ} (h : 1 < |w|) : c2 w = 0 := by
  rw [c2, if_neg (by linarith)]

lemma c2_eq_zero_of_one_le {w : ℝ} (h : 1 ≤ |w|) : c2 w = 0 := by
  rcases eq_or_lt_of_le h with he | hlt
  · rw [c2, if_pos (by rw [← he]), ← he, c2core_one]
  · exact c2_eq_zero_of_one_lt hlt

lemma continuous_c2core : Continuous c2core := by
  unfold c2core
  fun_prop

lemma continuous_c2 : Continuous c2 := by
  unfold c2
  exact (continuous_c2core.comp continuous_abs).if_le continuous_const continuous_abs
    continuous_const (by intro x hx; simp only [Function.comp_apply, hx, c2core_one])

/-! ### Crude uniform bounds on `[0,1]` -/

lemma abs_one_sub_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : |1 - w| ≤ 1 := by
  rw [abs_le]; constructor <;> linarith

lemma abs_c2core_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : |c2core w| ≤ 1 := by
  have hw := abs_one_sub_le h0 h1
  have t1 : |Real.sin (Real.sqrt 2 * (1 - w)) / (2 * Real.sqrt 2)| ≤ 1/2 := by
    rw [abs_div, abs_of_pos (show (0:ℝ) < 2 * Real.sqrt 2 by positivity),
      div_le_iff₀ (by positivity)]
    nlinarith [Real.abs_sin_le_one (Real.sqrt 2 * (1 - w)), sqrt2_lb]
  have t2 : |(1 - w) * Real.cos (Real.sqrt 2 * w) / 2| ≤ 1/2 := by
    rw [abs_div, abs_mul, abs_two, div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_one₀ hw (abs_nonneg (Real.cos (Real.sqrt 2 * w)))
      (Real.abs_cos_le_one (Real.sqrt 2 * w))]
  calc |c2core w| ≤ |Real.sin (Real.sqrt 2 * (1 - w)) / (2 * Real.sqrt 2)|
        + |(1 - w) * Real.cos (Real.sqrt 2 * w) / 2| := abs_add_le _ _
    _ ≤ 1 := by linarith

lemma abs_d1c2_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : |d1c2 w| ≤ 7/4 := by
  have hw := abs_one_sub_le h0 h1
  have hP : |(1 - w) * Real.sin (Real.sqrt 2 * w)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hw (abs_nonneg _) (Real.abs_sin_le_one _)
  obtain ⟨hP1, hP2⟩ := abs_le.1 hP
  have h1s := Real.neg_one_le_cos (Real.sqrt 2 * (1 - w))
  have h2s := Real.cos_le_one (Real.sqrt 2 * (1 - w))
  have h3s := Real.neg_one_le_cos (Real.sqrt 2 * w)
  have h4s := Real.cos_le_one (Real.sqrt 2 * w)
  rw [abs_le]
  unfold d1c2
  constructor <;> nlinarith [sqrt2_lb, sqrt2_ub]

lemma abs_d2c2_le {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : |d2c2 w| ≤ 13/4 := by
  have hw := abs_one_sub_le h0 h1
  have hP : |(1 - w) * Real.cos (Real.sqrt 2 * w)| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hw (abs_nonneg _) (Real.abs_cos_le_one _)
  obtain ⟨hP1, hP2⟩ := abs_le.1 hP
  have h1s := Real.neg_one_le_sin (Real.sqrt 2 * (1 - w))
  have h2s := Real.sin_le_one (Real.sqrt 2 * (1 - w))
  have h3s := Real.neg_one_le_sin (Real.sqrt 2 * w)
  have h4s := Real.sin_le_one (Real.sqrt 2 * w)
  rw [abs_le]
  unfold d2c2
  constructor <;> nlinarith [sqrt2_lb, sqrt2_ub]

/-! ### Derivatives -/

lemma hd_lin (w : ℝ) : HasDerivAt (fun w : ℝ => Real.sqrt 2 * (1 - w)) (-Real.sqrt 2) w := by
  simpa using ((hasDerivAt_const w (1:ℝ)).sub (hasDerivAt_id w)).const_mul (Real.sqrt 2)

lemma hd_lin2 (w : ℝ) : HasDerivAt (fun w : ℝ => Real.sqrt 2 * w) (Real.sqrt 2) w := by
  simpa using (hasDerivAt_id w).const_mul (Real.sqrt 2)

lemma hasDerivAt_c2core (w : ℝ) : HasDerivAt c2core (d1c2 w) w := by
  have h1 := hd_lin w
  have h2 := hd_lin2 w
  have hA : HasDerivAt (fun w : ℝ => Real.sin (Real.sqrt 2 * (1 - w)) / (2 * Real.sqrt 2))
      (Real.cos (Real.sqrt 2 * (1-w)) * (-Real.sqrt 2) / (2 * Real.sqrt 2)) w :=
    (h1.sin).div_const _
  have hB0 : HasDerivAt (fun w : ℝ => (1 - w) * Real.cos (Real.sqrt 2 * w))
      ((-1) * Real.cos (Real.sqrt 2 * w)
        + (1-w) * (-Real.sin (Real.sqrt 2 * w) * Real.sqrt 2)) w := by
    have := ((hasDerivAt_const w (1:ℝ)).sub (hasDerivAt_id w)).mul (h2.cos)
    simpa using this
  have h := hA.add (hB0.div_const 2)
  convert h using 1
  unfold d1c2
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  field_simp
  nlinarith [sqrt2_sq]

lemma hasDerivAt_d1c2 (w : ℝ) : HasDerivAt d1c2 (d2c2 w) w := by
  have h1 := hd_lin w
  have h2 := hd_lin2 w
  have hA : HasDerivAt (fun w : ℝ => -Real.cos (Real.sqrt 2 * (1 - w)) / 2)
      (-(-Real.sin (Real.sqrt 2 * (1-w)) * (-Real.sqrt 2)) / 2) w := (h1.cos.neg).div_const _
  have hB : HasDerivAt (fun w : ℝ => Real.cos (Real.sqrt 2 * w) / 2)
      ((-Real.sin (Real.sqrt 2 * w) * Real.sqrt 2) / 2) w := (h2.cos).div_const _
  have hC0 : HasDerivAt (fun w : ℝ => (Real.sqrt 2 / 2) * ((1 - w) * Real.sin (Real.sqrt 2 * w)))
      ((Real.sqrt 2 / 2) * ((-1) * Real.sin (Real.sqrt 2 * w)
        + (1-w) * (Real.cos (Real.sqrt 2 * w) * Real.sqrt 2))) w := by
    have := (((hasDerivAt_const w (1:ℝ)).sub (hasDerivAt_id w)).mul
      (h2.sin)).const_mul (Real.sqrt 2 / 2)
    simpa using this
  have h4 : HasDerivAt d1c2
      ((-(-Real.sin (Real.sqrt 2 * (1-w)) * (-Real.sqrt 2)) / 2)
        - ((-Real.sin (Real.sqrt 2 * w) * Real.sqrt 2) / 2)
        - ((Real.sqrt 2 / 2) * ((-1) * Real.sin (Real.sqrt 2 * w)
            + (1-w) * (Real.cos (Real.sqrt 2 * w) * Real.sqrt 2)))) w := by
    have h := (hA.sub hB).sub hC0
    convert h using 1
    funext x; simp only [Pi.sub_apply]; unfold d1c2; ring
  convert h4 using 1
  unfold d2c2
  linear_combination ((1 - w) * Real.cos (Real.sqrt 2 * w) / 2) * sqrt2_mul

end TruncEst
