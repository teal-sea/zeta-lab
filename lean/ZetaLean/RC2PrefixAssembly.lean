/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.AristotleRAMS2
import ZetaLean.MeanSquareAssembly

/-!
# Conditional RC2 assembly from a RAMS2 prefix bound

This file connects the generic prefix estimate isolated in
`AristotleRAMS2` to the exact two-range endpoint energy and finite mean-square
remainder.  The arithmetic prefix estimate remains an explicit hypothesis.
No RAMS2 asymptotic or contour-transfer statement is asserted here.
-/

namespace ZetaLean.HigherXi

open Complex Finset

/-! ## Natural breakpoint ranges -/

theorem lowerTwoRangeIndices_natCast {X W : ℕ} (hXW : X ≤ W) :
    lowerTwoRangeIndices (X : ℝ) W = Finset.Icc 1 X := by
  ext n
  simp only [lowerTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc,
    Nat.cast_le]
  omega

theorem upperTwoRangeIndices_natCast {X W : ℕ} (hX : 1 ≤ X) :
    upperTwoRangeIndices (X : ℝ) W = Finset.Ioc X W := by
  ext n
  simp only [upperTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc,
    Finset.mem_Ioc, Nat.cast_lt]
  omega

/-! ## Prefix estimate to endpoint energy -/

/-- A RAMS2-shaped prefix square-density bound controls the complete two-range
endpoint energy uniformly in the upper cutoff.  The lower range contributes
constant `1`, while the cutoff-independent inverse-square tail contributes
constant `10`.

The coefficient sequence is still arbitrary.  In the intended application
`a` is the exact level-two arithmetic resolvent coefficient sequence, and the
prefix hypothesis is the missing connected-cluster input.
-/
theorem twoRangeEndpointEnergy_le_of_prefixMass_le
    {a : ℕ → ℂ} {C : ℝ} {X W : ℕ}
    (hX : 1 ≤ X) (hXW : X ≤ W) (hC : 0 ≤ C)
    (hpre : ∀ n, 1 ≤ n →
      prefixMass (fun k ↦ ‖a k‖ ^ 2) n ≤
        C * n * (1 + Real.log n)) :
    twoRangeEndpointEnergy (X : ℝ) W a ≤
      11 * C * X * (1 + Real.log X) := by
  let b : ℕ → ℝ := fun n ↦ ‖a n‖ ^ 2
  have hb : ∀ n, 0 ≤ b n := fun n ↦ sq_nonneg _
  have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hX)
  have hlower := sum_mul_sq_le_of_prefixMass_le (b := b) (C := C) X hb hpre
  have hupper := tail_div_sq_le_of_prefixMass_le (b := b) (C := C) W
    hX hC hb hpre
  rw [twoRangeEndpointEnergy_eq (X : ℝ) W a hX0,
    lowerTwoRangeIndices_natCast hXW, upperTwoRangeIndices_natCast hX]
  change (X : ℝ)⁻¹ ^ 2 * (∑ n ∈ Finset.Icc 1 X, b n * (n : ℝ) ^ 2) +
      (X : ℝ) ^ 2 * (∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2) ≤
        11 * C * X * (1 + Real.log X)
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hlower' : (X : ℝ)⁻¹ ^ 2 *
      (∑ n ∈ Finset.Icc 1 X, b n * (n : ℝ) ^ 2) ≤
        C * X * (1 + Real.log X) := by
    calc
      (X : ℝ)⁻¹ ^ 2 * (∑ n ∈ Finset.Icc 1 X, b n * (n : ℝ) ^ 2)
          ≤ (X : ℝ)⁻¹ ^ 2 * (C * (X : ℝ) ^ 3 * (1 + Real.log X)) :=
            mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = C * X * (1 + Real.log X) := by field_simp
  have hupper' : (X : ℝ) ^ 2 *
      (∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2) ≤
        10 * C * X * (1 + Real.log X) := by
    calc
      (X : ℝ) ^ 2 * (∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2)
          ≤ (X : ℝ) ^ 2 * (10 * C * (1 + Real.log X) / (X : ℝ)) :=
            mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = 10 * C * X * (1 + Real.log X) := by field_simp
  linarith

/-! ## Conditional finite RC2 mean-square bound -/

/-- The exact finite RC2 off-diagonal remainder under the same RAMS2 prefix
hypothesis.  This theorem assembles the arithmetic endpoint-energy estimate
with the logarithmic-frequency mean-value theorem. -/
theorem norm_twoRange_mean_square_sub_diagonal_le_of_prefixMass_le
    (U : ℝ) {a : ℕ → ℂ} {C : ℝ} {X W : ℕ}
    (hX : 1 ≤ X) (hXW : X ≤ W) (hC : 0 ≤ C)
    (hpre : ∀ n, 1 ≤ n →
      prefixMass (fun k ↦ ‖a k‖ ^ 2) n ≤
        C * n * (1 + Real.log n)) :
    ‖(∫ t in U..2 * U,
        starRingEnd ℂ
            (logarithmicDirichletPolynomial W (twoRangeCoefficient X a) t) *
          logarithmicDirichletPolynomial W (twoRangeCoefficient X a) t) -
        (U : ℂ) * ∑ n ∈ Finset.Icc 1 W,
          starRingEnd ℂ (twoRangeCoefficient X a n) *
            twoRangeCoefficient X a n‖ ≤
      66 * realHarmonicMass W * C * X * (1 + Real.log X) := by
  have hmean := norm_twoRange_mean_square_sub_diagonal_le U (X : ℝ) W a
  have henergy := twoRangeEndpointEnergy_le_of_prefixMass_le
    hX hXW hC hpre
  calc
    _ ≤ 6 * realHarmonicMass W * twoRangeEndpointEnergy X W a := hmean
    _ ≤ 6 * realHarmonicMass W * (11 * C * X * (1 + Real.log X)) :=
      mul_le_mul_of_nonneg_left henergy (mul_nonneg (by norm_num) (realHarmonicMass_nonneg W))
    _ = 66 * realHarmonicMass W * C * X * (1 + Real.log X) := by ring

end ZetaLean.HigherXi
