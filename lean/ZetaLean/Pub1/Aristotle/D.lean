import Mathlib

namespace AristotleD

/-!
Aristotle project `8199d0e7-3da2-4778-ab3a-c9f550907300` (ramp integrals).

The returned artifact proved both statements by expanding the integrand and
calling `norm_num` with the interval-integral simp set.  That closes on the
service's Mathlib but makes no progress on this repository's pin
(`v4.33.0-rc2`), so both endings are replaced here by explicit antiderivatives
plus `intervalIntegral.integral_eq_sub_of_hasDerivAt`, which is version-stable.
The statements are unchanged.
-/

theorem integral_ramp_deriv_sq :
    (∫ x in (0:ℝ)..1, (140 * x ^ 3 * (1 - x) ^ 3) ^ 2) = 700 / 429 := by
  have hd : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => 2800 * t ^ 7 - 14700 * t ^ 8 + (98000 / 3) * t ^ 9 - 39200 * t ^ 10
        + (294000 / 11) * t ^ 11 - 9800 * t ^ 12 + (19600 / 13) * t ^ 13)
      ((140 * y ^ 3 * (1 - y) ^ 3) ^ 2) y := by
    intro y
    have h := (((((((hasDerivAt_pow 7 y).const_mul (2800 : ℝ)).sub
      ((hasDerivAt_pow 8 y).const_mul (14700 : ℝ))).add
      ((hasDerivAt_pow 9 y).const_mul (98000 / 3 : ℝ))).sub
      ((hasDerivAt_pow 10 y).const_mul (39200 : ℝ))).add
      ((hasDerivAt_pow 11 y).const_mul (294000 / 11 : ℝ))).sub
      ((hasDerivAt_pow 12 y).const_mul (9800 : ℝ))).add
      ((hasDerivAt_pow 13 y).const_mul (19600 / 13 : ℝ))
    exact h.congr_deriv (by push_cast; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  · norm_num
  · apply Continuous.intervalIntegrable
    fun_prop

theorem integral_abs_ramp_second_deriv :
    (∫ x in (0:ℝ)..1, |420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)|) = 35 / 8 := by
  have hc : Continuous (fun x : ℝ => |420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)|) := by
    fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := (1/2:ℝ)) (c := (1:ℝ))
    (f := fun x : ℝ => |420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)|)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
    (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)
  have h1 : (∫ x in (0:ℝ)..(1/2:ℝ), |420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)|)
      = ∫ x in (0:ℝ)..(1/2:ℝ),
        (420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨hx0, hx2⟩ := hx
    have hnn : (0:ℝ) ≤ 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) := by
      have : (0:ℝ) ≤ 1 - 2 * x := by linarith
      positivity
    simp only
    rw [abs_of_nonneg hnn]; ring
  have h2 : (∫ x in (1/2:ℝ)..1, |420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x)|)
      = ∫ x in (1/2:ℝ)..1,
        (840 * x ^ 5 - 2100 * x ^ 4 + 1680 * x ^ 3 - 420 * x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hnp : 420 * x ^ 2 * (1 - x) ^ 2 * (1 - 2 * x) ≤ 0 := by
      have h : (1:ℝ) - 2 * x ≤ 0 := by linarith
      nlinarith [mul_nonneg (sq_nonneg x) (sq_nonneg (1 - x))]
    simp only
    rw [abs_of_nonpos hnp]; ring
  -- the two halves, by explicit antiderivatives
  have hdL : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => 140 * t ^ 3 - 420 * t ^ 4 + 420 * t ^ 5 - 140 * t ^ 6)
      (420 * y ^ 2 - 1680 * y ^ 3 + 2100 * y ^ 4 - 840 * y ^ 5) y := by
    intro y
    have h := ((((hasDerivAt_pow 3 y).const_mul (140 : ℝ)).sub
      ((hasDerivAt_pow 4 y).const_mul (420 : ℝ))).add
      ((hasDerivAt_pow 5 y).const_mul (420 : ℝ))).sub
      ((hasDerivAt_pow 6 y).const_mul (140 : ℝ))
    exact h.congr_deriv (by push_cast; ring)
  have hdR : ∀ y : ℝ, HasDerivAt
      (fun t : ℝ => 140 * t ^ 6 - 420 * t ^ 5 + 420 * t ^ 4 - 140 * t ^ 3)
      (840 * y ^ 5 - 2100 * y ^ 4 + 1680 * y ^ 3 - 420 * y ^ 2) y := by
    intro y
    have h := ((((hasDerivAt_pow 6 y).const_mul (140 : ℝ)).sub
      ((hasDerivAt_pow 5 y).const_mul (420 : ℝ))).add
      ((hasDerivAt_pow 4 y).const_mul (420 : ℝ))).sub
      ((hasDerivAt_pow 3 y).const_mul (140 : ℝ))
    exact h.congr_deriv (by push_cast; ring)
  have e1 : (∫ x in (0:ℝ)..(1/2:ℝ),
      (420 * x ^ 2 - 1680 * x ^ 3 + 2100 * x ^ 4 - 840 * x ^ 5)) = 35 / 16 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdL y)]
    · norm_num
    · apply Continuous.intervalIntegrable
      fun_prop
  have e2 : (∫ x in (1/2:ℝ)..1,
      (840 * x ^ 5 - 2100 * x ^ 4 + 1680 * x ^ 3 - 420 * x ^ 2)) = 35 / 16 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdR y)]
    · norm_num
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [h1, h2, e1, e2] at hsplit
  rw [← hsplit]
  norm_num


end AristotleD