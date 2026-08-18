/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Aristotle.S
import ZetaLean.Pub1.Aristotle.V
import ZetaLean.Pub1.Regularity

/-!
# Pub 1 strong closure: the sup bound on `q = F₁''`'s ordinary part

`q(y) = -8 + ∑ d_k y^(2k+1)` with `d_k = a_k(2k+3)(2k+2)` in the shifted
indexing.  On `[-1,1]` every power is at most `1`, so

```
      ‖q‖_∞ ≤ 8 + ∑_k d_k = 8 + (finite part, k < 20) + (tail, k ≥ 20)
```

The finite part is an exact rational; the tail is `Aristotle/V`'s geometric
bound.  The total is `< 80.963`, the figure the evidence document records.
-/

open Finset

namespace ZetaLean.Pub1

/-- `d_k`, the coefficients of the ordinary part of `F₁''`. -/
noncomputable def dCoefR (k : ℕ) : ℝ :=
  AristotleS.aCoef k * ((2 * k + 3) * (2 * k + 2) : ℝ)

theorem dCoefR_eq : dCoefR = AristotleV.dCoef := rfl

theorem dCoefR_nonneg (k : ℕ) : 0 ≤ dCoefR k := by
  unfold dCoefR AristotleS.aCoef
  positivity

theorem dCoefR_summable : Summable dCoefR := by
  rw [dCoefR_eq]; exact AristotleV.dCoef_summable

/-- The exact finite part `∑_{k<20} d_k`. -/
theorem dCoefR_finite_sum :
    ∑ k ∈ range 20, dCoefR k
      = 23335671895968028334772392 / 319830986772877770815625 := by
  simp only [dCoefR, AristotleS.aCoef, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]

/-- **The total mass of `q`'s coefficients**, finite part plus geometric tail. -/
theorem tsum_dCoefR_le :
    ∑' k, dCoefR k
      ≤ 23335671895968028334772392 / 319830986772877770815625
        + 666953056256 / 23065890935073171953452059375 := by
  have hsum := dCoefR_summable
  have hsplit := hsum.sum_add_tsum_nat_add 20
  rw [← hsplit, dCoefR_finite_sum]
  have htail : ∑' j : ℕ, dCoefR (j + 20)
      ≤ 666953056256 / 23065890935073171953452059375 := by
    rw [dCoefR_eq]; exact AristotleV.dCoef_tail_le
  linarith

/-- **`‖q‖_∞ ≤ 80.963` on `[-1,1]`.** -/
theorem q_abs_le {y : ℝ} (hy : |y| ≤ 1) :
    |deriv (deriv AristotleS.fKer) y|
      ≤ 8 + (23335671895968028334772392 / 319830986772877770815625
        + 666953056256 / 23065890935073171953452059375) := by
  rw [AristotleS.fKer_second_deriv y]
  have hterm : ∀ k : ℕ, |dCoefR k * y ^ (2 * k + 1)| ≤ dCoefR k := by
    intro k
    rw [abs_mul, abs_pow]
    have h1 : |y| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg y) hy
    have h2 : |dCoefR k| = dCoefR k := abs_of_nonneg (dCoefR_nonneg k)
    calc |dCoefR k| * |y| ^ (2 * k + 1) ≤ |dCoefR k| * 1 :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = dCoefR k := by rw [mul_one, h2]
  have hsummable : Summable fun k : ℕ => dCoefR k * y ^ (2 * k + 1) := by
    refine Summable.of_norm_bounded dCoefR_summable (fun k => ?_)
    simpa [Real.norm_eq_abs] using hterm k
  have hnorm : Summable fun k : ℕ => ‖dCoefR k * y ^ (2 * k + 1)‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) dCoefR_summable
    simpa [Real.norm_eq_abs] using hterm k
  have hbound : |∑' k : ℕ, dCoefR k * y ^ (2 * k + 1)| ≤ ∑' k, dCoefR k := by
    have h1 : ‖∑' k : ℕ, dCoefR k * y ^ (2 * k + 1)‖
        ≤ ∑' k : ℕ, ‖dCoefR k * y ^ (2 * k + 1)‖ := norm_tsum_le_tsum_norm hnorm
    have h2 : ∑' k : ℕ, ‖dCoefR k * y ^ (2 * k + 1)‖ ≤ ∑' k, dCoefR k :=
      Summable.tsum_le_tsum (fun k => by simpa [Real.norm_eq_abs] using hterm k)
        hnorm dCoefR_summable
    simpa [Real.norm_eq_abs] using h1.trans h2
  have htot := tsum_dCoefR_le
  have hshape : (∑' k : ℕ, AristotleS.aCoef k * ((2 * k + 3) * (2 * k + 2) : ℝ)
      * y ^ (2 * k + 1)) = ∑' k : ℕ, dCoefR k * y ^ (2 * k + 1) := by
    refine tsum_congr (fun k => ?_)
    unfold dCoefR
    ring
  rw [hshape]
  have hstep : |(-8 : ℝ) + ∑' k : ℕ, dCoefR k * y ^ (2 * k + 1)|
      ≤ 8 + ∑' k, dCoefR k := by
    rw [abs_le]
    have hb := abs_le.mp hbound
    constructor <;> linarith [hb.1, hb.2]
  linarith [hstep, htot]

end ZetaLean.Pub1
