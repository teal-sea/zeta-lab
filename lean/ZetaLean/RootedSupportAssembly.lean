/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.RootedMatchingBound

/-!
# Rooted fixed-support assembly

This file combines the local rooted matching bound with the exact arithmetic
support-size coefficient.  An arbitrary scalar `globalWeight` is kept visible:
in the squarefree application it contains the single global logarithmic mark,
the power of `z`, and the product of the prime logarithms.

The result is finite and support-local.  It does not estimate a prime simplex,
sum over supports, handle repeated primes, or assert RAMS2.
-/

namespace ZetaLean.HigherXi

variable {α : Type*} [DecidableEq α]

/-- After factoring an arbitrary global weight, the squared rooted coefficient
is bounded by the exact support-size coefficient.  Every factorial and every
power of the global weight remains explicit. -/
theorem abs_globalWeight_mul_rootedMatchingCoefficient_sq_div_factorials_le_exact
    (S : Finset α) (monomer : α → ℝ) (dimer : Finset α → ℝ)
    (globalWeight : ℝ)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ 2)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ 2) :
    |globalWeight * rootedMatchingCoefficient S monomer dimer| ^ 2 /
        ((S.card.factorial : ℝ) *
          ((2 * S.card - 1).factorial : ℝ)) ≤
      |globalWeight| ^ 2 * exactSupportSizeCoefficient S.card := by
  have hroot := abs_rootedMatchingCoefficient_le_two_pow_mul_rootedMatchingSum
    S monomer dimer hmonomer hdimer
  have hsq :
      |rootedMatchingCoefficient S monomer dimer| ^ 2 ≤
        ((2 : ℝ) ^ S.card * rootedMatchingSum S.card) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hroot 2
  rw [abs_mul, mul_pow]
  unfold exactSupportSizeCoefficient
  calc
    |globalWeight| ^ 2 *
          |rootedMatchingCoefficient S monomer dimer| ^ 2 /
        ((S.card.factorial : ℝ) *
          ((2 * S.card - 1).factorial : ℝ)) ≤
      |globalWeight| ^ 2 *
          (((2 : ℝ) ^ S.card * rootedMatchingSum S.card) ^ 2) /
        ((S.card.factorial : ℝ) *
          ((2 * S.card - 1).factorial : ℝ)) := by
      gcongr
    _ = |globalWeight| ^ 2 *
        ((4 : ℝ) ^ S.card * rootedMatchingSum S.card ^ 2 /
          ((S.card.factorial : ℝ) *
            ((2 * S.card - 1).factorial : ℝ))) := by
      rw [mul_pow, ← pow_mul]
      rw [show (2 : ℝ) ^ (S.card * 2) = 4 ^ S.card by
        rw [mul_comm S.card 2, pow_mul]
        norm_num]
      ring

/-- On a nonempty support, the same scaled square is bounded by the summable
factorial envelope. -/
theorem abs_globalWeight_mul_rootedMatchingCoefficient_sq_div_factorials_le_majorant
    (S : Finset α) (monomer : α → ℝ) (dimer : Finset α → ℝ)
    (globalWeight : ℝ) (hS : S.Nonempty)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ 2)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ 2) :
    |globalWeight * rootedMatchingCoefficient S monomer dimer| ^ 2 /
        ((S.card.factorial : ℝ) *
          ((2 * S.card - 1).factorial : ℝ)) ≤
      |globalWeight| ^ 2 * supportSizeFactorialMajorant S.card := by
  calc
    |globalWeight * rootedMatchingCoefficient S monomer dimer| ^ 2 /
          ((S.card.factorial : ℝ) *
            ((2 * S.card - 1).factorial : ℝ)) ≤
        |globalWeight| ^ 2 * exactSupportSizeCoefficient S.card :=
      abs_globalWeight_mul_rootedMatchingCoefficient_sq_div_factorials_le_exact
        S monomer dimer globalWeight hmonomer hdimer
    _ ≤ |globalWeight| ^ 2 * supportSizeFactorialMajorant S.card := by
      gcongr
      exact exactSupportSizeCoefficient_le_supportSizeFactorialMajorant
        (Finset.one_le_card.mpr hS)

end ZetaLean.HigherXi
