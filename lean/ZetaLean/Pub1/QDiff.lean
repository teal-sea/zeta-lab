/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.TruncKernel
import ZetaLean.Pub1.QBound
import ZetaLean.Pub1.Aristotle.V

/-!
# Pub 1 strong closure: `q - q_M`, the truncation error in the second derivative

`fKerM` is a polynomial, so its second derivative is the finite sum
`-8 + ∑_{j<20} d_j y^(2j+1)`, and `q - q_M` is the geometric tail
`∑_{j≥20} d_j y^(2j+1)`, bounded on `[-1,1]` by `2.90e-17`.
-/

open Finset

namespace ZetaLean.Pub1

noncomputable def fKerMD1 (y : ℝ) : ℝ :=
  -8 * y + ∑ k ∈ range 21, aK k * ((2 * k + 1 : ℕ) * y ^ (2 * k))

noncomputable def fKerMD2 (y : ℝ) : ℝ :=
  -8 + ∑ k ∈ range 21, aK k * ((2 * k + 1 : ℕ) * ((2 * k : ℕ) * y ^ (2 * k - 1)))

theorem hasDerivAt_fKerM' (y : ℝ) : HasDerivAt fKerM (fKerMD1 y) y := by
  have h1 : HasDerivAt (fun z : ℝ => -4 * z ^ 2) (-4 * ((2 : ℕ) * y ^ 1)) y :=
    (hasDerivAt_pow 2 y).const_mul (-4 : ℝ)
  have h2 : HasDerivAt (fun z : ℝ => ∑ k ∈ range 21, aK k * z ^ (2 * k + 1))
      (∑ k ∈ range 21, aK k * ((2 * k + 1 : ℕ) * y ^ (2 * k + 1 - 1))) y :=
    HasDerivAt.fun_sum (fun k _ => (hasDerivAt_pow (2 * k + 1) y).const_mul (aK k))
  have h := HasDerivAt.fun_add h1 h2
  refine h.congr_deriv ?_
  unfold fKerMD1
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

theorem hasDerivAt_fKerMD1 (y : ℝ) : HasDerivAt fKerMD1 (fKerMD2 y) y := by
  have h1 : HasDerivAt (fun z : ℝ => -8 * z) (-8 * (1 : ℝ)) y := by
    simpa using (hasDerivAt_id y).const_mul (-8 : ℝ)
  have h2 : HasDerivAt
      (fun z : ℝ => ∑ k ∈ range 21, aK k * ((2 * k + 1 : ℕ) * z ^ (2 * k)))
      (∑ k ∈ range 21, aK k * ((2 * k + 1 : ℕ) * ((2 * k : ℕ) * y ^ (2 * k - 1)))) y := by
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    exact ((hasDerivAt_pow (2 * k) y).const_mul ((2 * k + 1 : ℕ) : ℝ)).const_mul (aK k)
  have h := HasDerivAt.fun_add h1 h2
  refine h.congr_deriv ?_
  unfold fKerMD2
  ring

theorem deriv_deriv_fKerM (y : ℝ) : deriv (deriv fKerM) y = fKerMD2 y := by
  have h1 : deriv fKerM = fKerMD1 := funext fun z => (hasDerivAt_fKerM' z).deriv
  rw [h1]
  exact (hasDerivAt_fKerMD1 y).deriv

/-- `q_M` as the finite part of `q`'s series. -/
theorem fKerMD2_eq (y : ℝ) :
    fKerMD2 y = -8 + ∑ j ∈ range 20, dCoefR j * y ^ (2 * j + 1) := by
  unfold fKerMD2
  rw [Finset.sum_range_succ']
  simp only [dCoefR, aK, AristotleS.aCoef, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

/-- **The truncation error in the second derivative**, bounded by the tail. -/
theorem q_sub_qM_abs_le {y : ℝ} (hy : |y| ≤ 1) :
    |deriv (deriv AristotleS.fKer) y - deriv (deriv fKerM) y|
      ≤ 666953056256 / 23065890935073171953452059375 := by
  rw [AristotleS.fKer_second_deriv y, deriv_deriv_fKerM, fKerMD2_eq]
  have hshape : (∑' k : ℕ, AristotleS.aCoef k * ((2 * k + 3) * (2 * k + 2) : ℝ)
      * y ^ (2 * k + 1)) = ∑' k : ℕ, dCoefR k * y ^ (2 * k + 1) :=
    tsum_congr (fun k => by unfold dCoefR; ring)
  have hsum : Summable fun k : ℕ => dCoefR k * y ^ (2 * k + 1) := by
    refine Summable.of_norm_bounded dCoefR_summable (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (dCoefR_nonneg k)]
    have h1 : |y| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    nlinarith [dCoefR_nonneg k, abs_nonneg y, pow_nonneg (abs_nonneg y) (2 * k + 1)]
  have hsplit := hsum.sum_add_tsum_nat_add 20
  rw [hshape, ← hsplit]
  have hterm : ∀ j : ℕ, |dCoefR (j + 20) * y ^ (2 * (j + 20) + 1)| ≤ dCoefR (j + 20) := by
    intro j
    rw [abs_mul, abs_pow, abs_of_nonneg (dCoefR_nonneg _)]
    have h1 : |y| ^ (2 * (j + 20) + 1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    nlinarith [dCoefR_nonneg (j + 20), pow_nonneg (abs_nonneg y) (2 * (j + 20) + 1)]
  have htail : Summable fun j : ℕ => dCoefR (j + 20) :=
    (summable_nat_add_iff 20).mpr dCoefR_summable
  have hs2 : Summable fun j : ℕ => dCoefR (j + 20) * y ^ (2 * (j + 20) + 1) := by
    refine Summable.of_norm_bounded htail (fun j => ?_)
    simpa [Real.norm_eq_abs] using hterm j
  have hnorm : Summable fun j : ℕ => ‖dCoefR (j + 20) * y ^ (2 * (j + 20) + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) htail
    simpa [Real.norm_eq_abs] using hterm j
  have hb : |∑' j : ℕ, dCoefR (j + 20) * y ^ (2 * (j + 20) + 1)| ≤ ∑' j : ℕ, dCoefR (j + 20) := by
    have h1 := norm_tsum_le_tsum_norm hnorm
    have h2 : ∑' j : ℕ, ‖dCoefR (j + 20) * y ^ (2 * (j + 20) + 1)‖ ≤ ∑' j : ℕ, dCoefR (j + 20) :=
      Summable.tsum_le_tsum (fun j => by simpa [Real.norm_eq_abs] using hterm j) hnorm htail
    simpa [Real.norm_eq_abs] using h1.trans h2
  have hV : ∑' j : ℕ, dCoefR (j + 20) ≤ 666953056256 / 23065890935073171953452059375 := by
    rw [dCoefR_eq]; exact AristotleV.dCoef_tail_le
  have harith : ((-8 : ℝ) + (∑ j ∈ range 20, dCoefR j * y ^ (2 * j + 1)
      + ∑' j : ℕ, dCoefR (j + 20) * y ^ (2 * (j + 20) + 1)))
      - (-8 + ∑ j ∈ range 20, dCoefR j * y ^ (2 * j + 1))
      = ∑' j : ℕ, dCoefR (j + 20) * y ^ (2 * (j + 20) + 1) := by ring
  rw [harith]
  exact hb.trans hV

end ZetaLean.Pub1
