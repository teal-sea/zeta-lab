/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

namespace QRH125

/-- The rational inequality in hunt 125, Lemma 4. The zero-sum identity and
the real part bounds on the zeros are separate analytic obligations. -/
theorem lorentzian_domination {A B t : ℝ}
    (hB : 0 < B) (hBA : B ≤ A) (ht : 0 ≤ t) :
    (A ^ 2 + t) / (A * (B ^ 2 + t)) ≤ A / B ^ 2 := by
  have hA : 0 < A := lt_of_lt_of_le hB hBA
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hden : 0 < A * (B ^ 2 + t) := mul_pos hA (by linarith)
  apply (div_le_div_iff₀ hden hB2).2
  have hsq : 0 ≤ A ^ 2 - B ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hBA) (show 0 ≤ A + B by linarith)]
  nlinarith [mul_nonneg hsq ht]

/-- Substitute theta = 7/8, c = 1/4, sigma0 = 2 in the preceding lemma. -/
theorem lorentzian_domination_seven_eighths {β γ : ℝ}
    (hlo : (1 / 8 : ℝ) ≤ β) (hhi : β ≤ (7 / 8 : ℝ)) :
    ((2 - β) ^ 2 + γ ^ 2) / ((2 - β) * ((β + 1 / 4) ^ 2 + γ ^ 2)) ≤
      (2 - β) / (β + 1 / 4) ^ 2 := by
  exact lorentzian_domination (by linarith) (by linarith) (sq_nonneg γ)

/-- Exact endpoint arithmetic used by Lemma 4. This does not assert the
convexity or the monotonicity needed to take the supremum over beta. -/
theorem kernel_endpoint_constants :
    max (1 / (3 * (7 / 8 : ℝ) + 1 / 4 - 1) + 2 / (1 - 7 / 8 + 1 / 4))
        (3 / (7 / 8 + 1 / 4)) = 88 / 15 ∧
      (1 : ℝ) / (7 / 8 + 1 / 4) = 8 / 9 := by
  norm_num

end QRH125
