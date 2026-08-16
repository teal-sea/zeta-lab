/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.TailBound
import ZetaLean.Pub1.ZResolvent
import ZetaLean.Pub1.CertArith

/-!
# Pub 1 strong closure: bounds on the tail term `E u`

`E u` is the trial polynomial convolved against the tail `F₁ - F₁^(M)`, so
`|E u| ≤ ρ‖u‖_∞` pointwise, with `ρ < 1.6e-20`.  The `L²` bound is the same
number because the interval has length one.

The sup bound on `u` is the coefficient absolute sum on `[-1/2,1/2]`, which is
`‖u‖_∞ ≤ usupC = 1.2705…`; the evidence document uses `‖u‖₂ = 0.888` here, but
`ρ` is so small that the cruder constant costs nothing downstream.
-/

open Finset MeasureTheory

namespace ZetaLean.Pub1

/-- `|u| ≤ usupC` on `I`, by the coefficient absolute sum. -/
theorem uPoly_abs_le {t : ℝ} (ht : |t| ≤ 1 / 2) : |uPoly t| ≤ (usupC : ℝ) := by
  have h1 : |t| ^ 2 ≤ (1 / 4 : ℝ) := by
    nlinarith [abs_nonneg t, ht, sq_abs t]
  have hpow : ∀ j : ℕ, |t ^ (2 * j)| ≤ (1 / 4 : ℝ) ^ j := by
    intro j
    calc |t ^ (2 * j)| = (|t| ^ 2) ^ j := by rw [abs_pow, pow_mul]
      _ ≤ (1 / 4 : ℝ) ^ j := pow_le_pow_left₀ (by positivity) h1 j
  calc |uPoly t| = |∑ j ∈ range 6, cK j * t ^ (2 * j)| := by rw [uPoly]
    _ ≤ ∑ j ∈ range 6, |cK j * t ^ (2 * j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range 6, |cK j| * (1 / 4 : ℝ) ^ j := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hpow j) (abs_nonneg _)
    _ ≤ (usupC : ℝ) := by
        norm_num [cK, usupC, Finset.sum_range_succ]

/-- **The tail term is uniformly tiny.** -/
theorem EuTail_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |EuTail s| ≤ (rhoC : ℝ) * (usupC : ℝ) := by
  have hsabs := abs_le.mp hs
  have hbound : ∀ t ∈ Set.uIoc (-(1:ℝ)/2) ((1:ℝ)/2),
      ‖(F1 (s - t) - truncKernel (s - t)) * uPoly t‖ ≤ (rhoC : ℝ) * (usupC : ℝ) := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htabs : |t| ≤ (1:ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htabs' := abs_le.mp htabs
    have harg : |s - t| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hsabs.1, hsabs.2, htabs'.1, htabs'.2]
    have h1 := F1_sub_truncKernel_abs_le harg
    have h2 := uPoly_abs_le htabs
    have hrho : (rhoC : ℝ) = 45088768 / 2828846926917599723269509375 := by
      norm_num [rhoC]
    rw [Real.norm_eq_abs, abs_mul, hrho]
    have hnn1 : (0:ℝ) ≤ |F1 (s - t) - truncKernel (s - t)| := abs_nonneg _
    have hnn2 : (0:ℝ) ≤ |uPoly t| := abs_nonneg _
    have husup : (0:ℝ) ≤ (usupC : ℝ) := by norm_num [usupC]
    nlinarith [h1, h2, hnn1, hnn2, husup]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show |(1:ℝ)/2 - (-(1:ℝ)/2)| = 1 by norm_num, mul_one, Real.norm_eq_abs] at h
  exact h

end ZetaLean.Pub1
