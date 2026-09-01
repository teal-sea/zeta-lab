import Mathlib

/-!
# Setting for the retention problem

`g u = cos (√2 u)` on `|u| ≤ 1/2`, extended by zero; `c2` is its autocorrelation;
`A = √2 sin (1/√2) = ∫ g`; `E G = (1/A²) ∫_{-1}^{1} c2 w ‖G w‖² dw`.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

/-- The window `g u = cos (√2 u)` for `|u| ≤ 1/2`, zero elsewhere. -/
noncomputable def g (u : ℝ) : ℝ := if |u| ≤ 1/2 then Real.cos (Real.sqrt 2 * u) else 0

/-- `A = √2 sin (1/√2) = ∫ g`. -/
noncomputable def Aconst : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)

/-- The autocorrelation `c2 w = ∫ g u * g (u + w) du`. -/
noncomputable def c2 (w : ℝ) : ℝ := ∫ u : ℝ, g u * g (u + w)

/-- The energy functional `E G = (1/A²) ∫_{-1}^1 c2 w ‖G w‖² dw`. -/
noncomputable def Eng (G : ℝ → ℂ) : ℝ :=
  (1 / Aconst ^ 2) * ∫ w in (-1 : ℝ)..1, c2 w * ‖G w‖ ^ 2

/-- `Qre a b = ∫ g u cosh (a u) cos (b u) du`, the real part of `ĝ (a + i b)`. -/
noncomputable def Qre (a b : ℝ) : ℝ := ∫ u : ℝ, g u * Real.cosh (a * u) * Real.cos (b * u)

/-- `Qim a b = ∫ g u sinh (a u) sin (b u) du`, the imaginary part of `ĝ (a + i b)`. -/
noncomputable def Qim (a b : ℝ) : ℝ := ∫ u : ℝ, g u * Real.sinh (a * u) * Real.sin (b * u)

/-- The gain term `Shq y = ĝ(2y)² - A²`. -/
noncomputable def Shq (y : ℝ) : ℝ := Qre (2 * y) 0 ^ 2 - Aconst ^ 2

/-- `F w = ∑_{j<n} exp (I x_j w)`. -/
noncomputable def Fsum (n : ℕ) (x : ℕ → ℝ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range n, Complex.exp (Complex.I * (x j * w))

/-- `P w = 2 cosh (y w) exp (I t w)`. -/
noncomputable def Pfun (y t : ℝ) (w : ℝ) : ℂ :=
  2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * (t * w))

/-! ### Basic properties of `g` -/

lemma g_of_mem {u : ℝ} (h : |u| ≤ 1/2) : g u = Real.cos (Real.sqrt 2 * u) := if_pos h

lemma g_of_not_mem {u : ℝ} (h : ¬ |u| ≤ 1/2) : g u = 0 := if_neg h

lemma g_zero_of_lt {u : ℝ} (h : 1/2 < |u|) : g u = 0 := if_neg (not_le.2 h)

lemma sqrt2_pos : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt2_lt_two : Real.sqrt 2 < 2 := by
  have : Real.sqrt 2 < Real.sqrt 4 := by
    apply Real.sqrt_lt_sqrt <;> norm_num
  simpa using this.trans_le (by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq]; norm_num)

lemma g_nonneg (u : ℝ) : 0 ≤ g u := by
  unfold g
  split
  · next h =>
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : Real.sqrt 2 * |u| ≤ Real.sqrt 2 * (1/2) := by
        exact mul_le_mul_of_nonneg_left h (le_of_lt sqrt2_pos)
      have h1 : |Real.sqrt 2 * u| ≤ 1 := by
        rw [abs_mul, abs_of_pos sqrt2_pos]
        have := sqrt2_lt_two
        nlinarith [abs_nonneg u]
      have := abs_le.1 h1
      nlinarith [Real.pi_gt_three]
    · have h1 : |Real.sqrt 2 * u| ≤ 1 := by
        rw [abs_mul, abs_of_pos sqrt2_pos]
        have := sqrt2_lt_two
        nlinarith [abs_nonneg u, h]
      have := abs_le.1 h1
      nlinarith [Real.pi_gt_three]
  · exact le_refl _

lemma g_le_one (u : ℝ) : g u ≤ 1 := by
  unfold g
  split
  · exact Real.cos_le_one _
  · norm_num

lemma g_abs_le_one (u : ℝ) : |g u| ≤ 1 := by
  rw [abs_of_nonneg (g_nonneg u)]; exact g_le_one u

lemma g_even (u : ℝ) : g (-u) = g u := by
  unfold g
  rw [abs_neg]
  split
  · rw [mul_neg, Real.cos_neg]
  · rfl

lemma g_measurable : Measurable g := by
  unfold g
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (measurable_norm.comp measurable_id) measurable_const
  · exact Real.measurable_cos.comp (measurable_const.mul measurable_id)

lemma g_support {u : ℝ} (h : g u ≠ 0) : |u| ≤ 1/2 := by
  by_contra hc
  exact h (g_of_not_mem hc)

end Retention
