/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.QBound
import ZetaLean.Pub1.Aristotle.F
import ZetaLean.Pub1.TruncKernel
import ZetaLean.Pub1.Setting

/-!
# Pub 1 strong closure: the tail kernel `F₁ - F₁^(M)`

`truncKernel` keeps the terms `k < 20` of the series, so the difference is the
geometric tail, bounded on `[-1,1]` by `∑_{k≥20} a_k = ρ < 1.6e-20`.
-/

open Finset

namespace ZetaLean.Pub1

/-- The truncation written with the same coefficients as `F₁`. -/
theorem truncKernel_eq_partial (x : ℝ) :
    truncKernel x
      = |x| - 4 * x ^ 2 + ∑ j ∈ range 20, AristotleS.aCoef j * |x| ^ (2 * j + 3) := by
  rw [truncKernel, Finset.sum_range_succ']
  simp only [aK, AristotleS.aCoef, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.factorial]
  ring

/-- The tail is exactly the terms from `k = 20` on. -/
theorem F1_sub_truncKernel (x : ℝ) :
    F1 x - truncKernel x = ∑' j : ℕ, AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3) := by
  have hsum : Summable fun k : ℕ => AristotleS.aCoef k * |x| ^ (2 * k + 3) :=
    AristotleF.F1_summable_global x
  have hsplit := hsum.sum_add_tsum_nat_add 20
  have hF : F1 x = |x| - 4 * x ^ 2 + ∑' k : ℕ, AristotleS.aCoef k * |x| ^ (2 * k + 3) := rfl
  rw [hF, truncKernel_eq_partial, ← hsplit]
  ring

theorem aCoef_nonneg (k : ℕ) : 0 ≤ AristotleS.aCoef k := by
  unfold AristotleS.aCoef; positivity

/-- **The tail bound.**  `|F₁ - F₁^(M)| ≤ ρ` on `[-1,1]`. -/
theorem F1_sub_truncKernel_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    |F1 x - truncKernel x| ≤ 45088768 / 2828846926917599723269509375 := by
  rw [F1_sub_truncKernel]
  have hterm : ∀ j : ℕ,
      |AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3)| ≤ AristotleS.aCoef (j + 20) := by
    intro j
    rw [abs_mul, abs_pow, abs_abs, abs_of_nonneg (aCoef_nonneg _)]
    have h1 : |x| ^ (2 * (j + 20) + 3) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx
    have := mul_le_mul_of_nonneg_left h1 (aCoef_nonneg (j + 20))
    linarith [this]
  have htailsum : Summable fun j : ℕ => AristotleS.aCoef (j + 20) := by
    have : Summable AristotleS.aCoef := by
      have h := AristotleF.F1_summable_global 1
      have h' : Summable fun k : ℕ => AristotleF.aCoef k := by simpa using h
      exact h' 
    exact (summable_nat_add_iff 20).mpr this
  have hs2 : Summable fun j : ℕ => AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3) := by
    refine Summable.of_norm_bounded htailsum (fun j => ?_)
    simpa [Real.norm_eq_abs] using hterm j
  have hb : |∑' j : ℕ, AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3)|
      ≤ ∑' j : ℕ, AristotleS.aCoef (j + 20) := by
    have hnorm : Summable fun j : ℕ => ‖AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3)‖ := by
      refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) htailsum
      simpa [Real.norm_eq_abs] using hterm j
    have h1 := norm_tsum_le_tsum_norm hnorm
    have h2 : ∑' j : ℕ, ‖AristotleS.aCoef (j + 20) * |x| ^ (2 * (j + 20) + 3)‖
        ≤ ∑' j : ℕ, AristotleS.aCoef (j + 20) :=
      Summable.tsum_le_tsum (fun j => by simpa [Real.norm_eq_abs] using hterm j) hnorm htailsum
    simpa [Real.norm_eq_abs] using h1.trans h2
  exact hb.trans AristotleV.aCoef_tail_le

end ZetaLean.Pub1
