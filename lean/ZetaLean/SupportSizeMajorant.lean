/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.MatchingCount

/-!
# Arithmetic support-size majorants

This file records the explicit finite arithmetic object from section 6 of
`hunts/higher_xi/RAMS2-CLUSTER.md` and an entire factorial-denominator envelope
for its later support-size summation.

The exact finite sum uses `matchingCount`.  The envelope has successive ratio
`O(1/r)` and remains summable after multiplication by any fixed exponential
weight.  Connecting the exact sum to the envelope requires the local rooted
matching-weight estimate from the analytic cluster expansion; that estimate,
the prime-simplex asymptotic, and RAMS2 are not asserted here.
-/

namespace ZetaLean.HigherXi

open Finset

/-- The exact one-colour rooted matching summand
`N(r,a) 2^{-a} (r-a-1)!`, interpreted in `ℝ`. -/
noncomputable def rootedMatchingSummand (r a : ℕ) : ℝ :=
  (matchingCount r a : ℝ) * ((r - a - 1).factorial : ℝ) / (2 : ℝ) ^ a

/-- The exact finite arithmetic sum `S_r` from the squarefree cluster bound. -/
noncomputable def rootedMatchingSum (r : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (r / 2 + 1), rootedMatchingSummand r a

/-- The exact arithmetic support-size coefficient
`4^r S_r^2 / (r! (2r-1)!)`. -/
noncomputable def exactSupportSizeCoefficient (r : ℕ) : ℝ :=
  (4 : ℝ) ^ r * rootedMatchingSum r ^ 2 /
    ((r.factorial : ℝ) * ((2 * r - 1).factorial : ℝ))

theorem rootedMatchingSummand_nonneg (r a : ℕ) :
    0 ≤ rootedMatchingSummand r a := by
  unfold rootedMatchingSummand
  positivity

theorem rootedMatchingSum_nonneg (r : ℕ) : 0 ≤ rootedMatchingSum r := by
  unfold rootedMatchingSum
  exact Finset.sum_nonneg fun a _ ↦ rootedMatchingSummand_nonneg r a

theorem exactSupportSizeCoefficient_nonneg (r : ℕ) :
    0 ≤ exactSupportSizeCoefficient r := by
  unfold exactSupportSizeCoefficient
  positivity

/-- The first exact coefficient is the section-6 value `4`. -/
theorem exactSupportSizeCoefficient_one : exactSupportSizeCoefficient 1 = 4 := by
  norm_num [exactSupportSizeCoefficient, rootedMatchingSum,
    rootedMatchingSummand, matchingCount, pairingCount]

/-- The second exact coefficient is the section-6 value `3`. -/
theorem exactSupportSizeCoefficient_two : exactSupportSizeCoefficient 2 = 3 := by
  norm_num [exactSupportSizeCoefficient, rootedMatchingSum,
    rootedMatchingSummand, matchingCount, pairingCount, Finset.sum_range_succ]

/-- Real-valued factorial formula for the exact labelled matching count. -/
theorem matchingCount_cast_eq_factorial_div {r a : ℕ} (h : 2 * a ≤ r) :
    (matchingCount r a : ℝ) =
      (r.factorial : ℝ) /
        ((2 : ℝ) ^ a * (a.factorial : ℝ) * ((r - 2 * a).factorial : ℝ)) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast matchingCount_mul_denominator_eq_factorial h

/-- Each exact finite summand has the displayed factorial-denominator form on
its natural range. -/
theorem rootedMatchingSummand_eq_factorial_div {r a : ℕ} (h : 2 * a ≤ r) :
    rootedMatchingSummand r a =
      (r.factorial : ℝ) * ((r - a - 1).factorial : ℝ) /
        ((2 : ℝ) ^ (2 * a) * (a.factorial : ℝ) *
          ((r - 2 * a).factorial : ℝ)) := by
  rw [rootedMatchingSummand, matchingCount_cast_eq_factorial_div h]
  field_simp
  ring

/-! ## A summable factorial-denominator envelope -/

/-- A rational envelope slightly larger than the report's
`4^r exp(r/2) (r-1)! / (r (2r-1)!)`: replacing `sqrt(e)` by `2` gives the
fully arithmetic numerator `8^r`. -/
noncomputable def supportSizeFactorialMajorant (r : ℕ) : ℝ :=
  (8 : ℝ) ^ r * ((r - 1).factorial : ℝ) /
    ((r : ℝ) * ((2 * r - 1).factorial : ℝ))

theorem supportSizeFactorialMajorant_nonneg (r : ℕ) :
    0 ≤ supportSizeFactorialMajorant r := by
  unfold supportSizeFactorialMajorant
  positivity

private theorem factorial_eq_mul_factorial_pred {n : ℕ} (hn : 1 ≤ n) :
    n.factorial = n * (n - 1).factorial := by
  calc
    n.factorial = ((n - 1) + 1).factorial := by congr 1; omega
    _ = ((n - 1) + 1) * (n - 1).factorial := Nat.factorial_succ _
    _ = n * (n - 1).factorial := by rw [Nat.sub_add_cancel hn]

/-- Exact successive ratio of the arithmetic envelope. -/
theorem supportSizeFactorialMajorant_succ {r : ℕ} (hr : 1 ≤ r) :
    supportSizeFactorialMajorant (r + 1) =
      supportSizeFactorialMajorant r *
        (4 * r / ((r + 1) * (2 * r + 1)) : ℝ) := by
  unfold supportSizeFactorialMajorant
  rw [show r + 1 - 1 = r by omega,
    show 2 * (r + 1) - 1 = (2 * r + 1) by omega]
  have hrfac : r.factorial = r * (r - 1).factorial :=
    factorial_eq_mul_factorial_pred hr
  have htwofac : (2 * r + 1).factorial =
      (2 * r + 1) * (2 * r) * (2 * r - 1).factorial := by
    rw [factorial_eq_mul_factorial_pred (show 1 ≤ 2 * r + 1 by omega),
      show 2 * r + 1 - 1 = 2 * r by omega,
      factorial_eq_mul_factorial_pred (show 1 ≤ 2 * r by omega)]
    ring
  rw [hrfac, htwofac]
  push_cast
  field_simp
  ring

/-- Quantitative `O(1/r)` form of the successive-ratio bound. -/
theorem supportSizeFactorialMajorant_ratio_le {r : ℕ} (hr : 1 ≤ r) :
    (4 * r / ((r + 1) * (2 * r + 1)) : ℝ) ≤ 2 / (r + 1) := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- The central factorial product is bounded by the larger factorial. -/
theorem factorial_mul_factorial_pred_le_factorial_two_mul_pred
    {r : ℕ} (hr : 1 ≤ r) :
    r.factorial * (r - 1).factorial ≤ (2 * r - 1).factorial := by
  have hle : r ≤ 2 * r - 1 := by omega
  have hfac := Nat.choose_mul_factorial_mul_factorial hle
  have hchoose : 1 ≤ (2 * r - 1).choose r := Nat.choose_pos hle
  rw [show 2 * r - 1 - r = r - 1 by omega] at hfac
  nlinarith

/-- The arithmetic envelope is itself bounded by the exponential-series term
`8^r/r!`. -/
theorem supportSizeFactorialMajorant_le_pow_div_factorial
    {r : ℕ} (hr : 1 ≤ r) :
    supportSizeFactorialMajorant r ≤ (8 : ℝ) ^ r / (r.factorial : ℝ) := by
  have hfac := factorial_mul_factorial_pred_le_factorial_two_mul_pred hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hfac' :
      (r.factorial : ℝ) * ((r - 1).factorial : ℝ) ≤
        ((2 * r - 1).factorial : ℝ) := by exact_mod_cast hfac
  have hfac'' :
      (r.factorial : ℝ) * ((r - 1).factorial : ℝ) ≤
        (r : ℝ) * ((2 * r - 1).factorial : ℝ) := by
    calc
      _ ≤ ((2 * r - 1).factorial : ℝ) := hfac'
      _ ≤ (r : ℝ) * ((2 * r - 1).factorial : ℝ) := by
        exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hr)
  unfold supportSizeFactorialMajorant
  rw [div_le_div_iff₀ (mul_pos hr0 (by positivity)) (by positivity)]
  calc
    (8 : ℝ) ^ r * (r - 1).factorial * r.factorial =
        8 ^ r * (r.factorial * (r - 1).factorial) := by ring
    _ ≤ 8 ^ r * (r * (2 * r - 1).factorial) :=
      mul_le_mul_of_nonneg_left hfac'' (by positivity)
    _ = 8 ^ r * (r * (2 * r - 1).factorial) := rfl

/-- The support-size envelope remains summable after every fixed exponential
weight.  This is the usable order-uniform support-size conclusion; it is
independent of any prime-simplex estimate. -/
theorem summable_supportSizeFactorialMajorant_mul_pow (K : ℝ) :
    Summable (fun r : ℕ ↦ supportSizeFactorialMajorant r * K ^ r) := by
  apply Summable.of_norm_bounded (Real.summable_pow_div_factorial (8 * |K|))
  intro r
  rcases r with _ | r
  · simp [supportSizeFactorialMajorant]
  · rw [Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg (supportSizeFactorialMajorant_nonneg (r + 1))]
    calc
      supportSizeFactorialMajorant (r + 1) * |K| ^ (r + 1) ≤
          ((8 : ℝ) ^ (r + 1) / ((r + 1).factorial : ℝ)) *
            |K| ^ (r + 1) := by
        gcongr
        exact supportSizeFactorialMajorant_le_pow_div_factorial (by omega)
      _ = (8 * |K|) ^ (r + 1) / ((r + 1).factorial : ℝ) := by ring

/-- Once the remaining arithmetic comparison from the exact coefficient to
the factorial envelope is supplied, the exact support-size series is summable
for every fixed exponential weight.  The comparison is deliberately visible
as a hypothesis. -/
theorem summable_exactSupportSizeCoefficient_mul_pow_of_le
    (K : ℝ)
    (hmajorant : ∀ r, exactSupportSizeCoefficient r ≤
      supportSizeFactorialMajorant r) :
    Summable (fun r : ℕ ↦ exactSupportSizeCoefficient r * K ^ r) := by
  apply Summable.of_norm_bounded
    (summable_supportSizeFactorialMajorant_mul_pow |K|)
  intro r
  rw [Real.norm_eq_abs, abs_mul, abs_pow,
    abs_of_nonneg (exactSupportSizeCoefficient_nonneg r)]
  exact mul_le_mul_of_nonneg_right (hmajorant r) (by positivity)

end ZetaLean.HigherXi
