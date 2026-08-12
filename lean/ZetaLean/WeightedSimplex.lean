/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# A factorial-denominator weighted simplex induction

The order-uniform prime-simplex bound used by the RAMS arguments has the
denominator `j! (2j-1)!`.  This file isolates the induction that creates that
denominator.  If adjoining one new label costs at most `B` after division by
the three new factors `(j+1)(2j)(2j+1)`, then every order is bounded by the
first-order mass times `B^(j-1) / (j! (2j-1)!)`.

The theorem is deliberately abstract.  It does not define primes or assert
the analytic one-step insertion estimate for their logarithmic weights.
-/

namespace ZetaLean.HigherXi

/-- The factorial denominator in the weighted prime-simplex majorant. -/
noncomputable def simplexFactorialDenominator (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * ((2 * j - 1).factorial : ℝ)

theorem simplexFactorialDenominator_pos (j : ℕ) :
    0 < simplexFactorialDenominator j := by
  unfold simplexFactorialDenominator
  positivity

@[simp]
theorem simplexFactorialDenominator_one :
    simplexFactorialDenominator 1 = 1 := by
  norm_num [simplexFactorialDenominator]

/-- Advancing the simplex order introduces exactly the three factors used in
the insertion recurrence. -/
theorem simplexFactorialDenominator_succ {j : ℕ} (hj : 1 ≤ j) :
    simplexFactorialDenominator (j + 1) =
      simplexFactorialDenominator j *
        ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) := by
  unfold simplexFactorialDenominator
  have htwo0 : (2 * j).factorial =
      (2 * j) * (2 * j - 1).factorial := by
    calc
      (2 * j).factorial = ((2 * j - 1) + 1).factorial := by
        congr 1
        omega
      _ = ((2 * j - 1) + 1) * (2 * j - 1).factorial :=
        Nat.factorial_succ _
      _ = (2 * j) * (2 * j - 1).factorial := by
        rw [Nat.sub_add_cancel (by omega)]
  have htwo : (2 * j + 1).factorial =
      (2 * j + 1) * (2 * j) * (2 * j - 1).factorial := by
    rw [Nat.factorial_succ, htwo0]
    ring
  rw [Nat.factorial_succ,
    show 2 * (j + 1) - 1 = (2 * j + 1) by omega,
    htwo]
  push_cast
  ring

/-- Weighted-simplex induction in denominator-cleared form.

`mass j` may be any nonnegative order-`j` mass.  The only analytic input is
`hstep`, the uniform one-label insertion estimate. -/
theorem simplexFactorialDenominator_mul_mass_le
    (mass : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hstep : ∀ j, 1 ≤ j →
      ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ) * mass (j + 1) ≤
        B * mass j) :
    ∀ j, 1 ≤ j →
      simplexFactorialDenominator j * mass j ≤
        mass 1 * B ^ (j - 1) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
      have hs := hstep j hj
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
        Nat.cast_ofNat] at hs
      rw [simplexFactorialDenominator_succ hj,
        show j + 1 - 1 = j by omega]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_mul,
        Nat.cast_ofNat]
      calc
        simplexFactorialDenominator j * ((j : ℝ) + 1) * (2 * (j : ℝ)) *
              (2 * (j : ℝ) + 1) * mass (j + 1) =
            simplexFactorialDenominator j *
              (((j : ℝ) + 1) * (2 * (j : ℝ)) *
                (2 * (j : ℝ) + 1) * mass (j + 1)) := by ring
        _ ≤ simplexFactorialDenominator j * (B * mass j) :=
          mul_le_mul_of_nonneg_left hs
            (simplexFactorialDenominator_pos j).le
        _ = B * (simplexFactorialDenominator j * mass j) := by ring
        _ ≤ B * (mass 1 * B ^ (j - 1)) :=
          mul_le_mul_of_nonneg_left ih hB
        _ = mass 1 * (B ^ (j - 1) * B) := by ring
        _ = mass 1 * B ^ j := by
          rw [← pow_succ, Nat.sub_add_cancel hj]

/-- Explicit factorial-denominator form of the weighted-simplex induction. -/
theorem mass_le_pow_div_simplexFactorialDenominator
    (mass : ℕ → ℝ) (B : ℝ)
    (hB : 0 ≤ B)
    (hstep : ∀ j, 1 ≤ j →
      ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ) * mass (j + 1) ≤
        B * mass j)
    {j : ℕ} (hj : 1 ≤ j) :
    mass j ≤ mass 1 * B ^ (j - 1) /
      simplexFactorialDenominator j := by
  rw [le_div_iff₀ (simplexFactorialDenominator_pos j)]
  simpa [mul_comm] using
    simplexFactorialDenominator_mul_mass_le mass B hB hstep j hj

/-- A directly usable specialization: a first-order bound and the insertion
recurrence give an order-uniform factorial majorant. -/
theorem mass_le_base_mul_pow_div_simplexFactorialDenominator
    (mass : ℕ → ℝ) (base B : ℝ)
    (hbase : mass 1 ≤ base) (hB : 0 ≤ B)
    (hstep : ∀ j, 1 ≤ j →
      ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ) * mass (j + 1) ≤
        B * mass j)
    {j : ℕ} (hj : 1 ≤ j) :
    mass j ≤ base * B ^ (j - 1) /
      simplexFactorialDenominator j := by
  calc
    mass j ≤ mass 1 * B ^ (j - 1) /
        simplexFactorialDenominator j :=
      mass_le_pow_div_simplexFactorialDenominator mass B hB hstep hj
    _ ≤ base * B ^ (j - 1) / simplexFactorialDenominator j := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase (pow_nonneg hB _))
        (simplexFactorialDenominator_pos j).le

end ZetaLean.HigherXi
