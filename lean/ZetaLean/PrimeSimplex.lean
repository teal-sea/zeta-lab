/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.WeightedSimplex

/-!
# Finite distinct-prime logarithmic simplex masses

This file defines the concrete squarefree support mass appearing in the RAMS2
prime-simplex estimate.  The cutoff is a natural number `X`; supports consist
of distinct primes with product at most `X`.  Their weight is

`(log (product S))^2 * product p in S, (log p)^2`,

written as a sum of logarithms so no logarithm-of-product identity is assumed.

Deleting one marked prime from an order-`j+1` support counts that support
exactly `j+1` times.  This gives the complete combinatorial normalization.  A
single explicit hypothesis, `hprime`, contains the remaining weighted-prime
insertion estimate.  Under it, `WeightedSimplex` supplies the exact
`j! (2j-1)!` denominator.  No Chebyshev estimate is asserted here.
-/

namespace ZetaLean.HigherXi

open Finset

/-- Primes available below the finite cutoff. -/
def primeCandidates (X : ℕ) : Finset ℕ :=
  (Finset.range (X + 1)).filter Nat.Prime

/-- Distinct-prime supports of order `j` whose product is at most `X`. -/
def distinctPrimeSupports (X j : ℕ) : Finset (Finset ℕ) :=
  (primeCandidates X).powersetCard j |>.filter fun S ↦
    (∏ p ∈ S, p) ≤ X

/-- The RAMS squarefree logarithmic weight of one distinct-prime support. -/
noncomputable def distinctPrimeLogWeight (S : Finset ℕ) : ℝ :=
  (∑ p ∈ S, Real.log p) ^ 2 * ∏ p ∈ S, Real.log p ^ 2

/-- The finite order-`j` distinct-prime logarithmic support mass. -/
noncomputable def distinctPrimeLogMass (X j : ℕ) : ℝ :=
  ∑ S ∈ distinctPrimeSupports X j, distinctPrimeLogWeight S

/-- The mass with one support prime marked for deletion.  This is the exact
finite object to which a one-label insertion estimate applies. -/
noncomputable def distinctPrimeDeletionMass (X j : ℕ) : ℝ :=
  ∑ T ∈ distinctPrimeSupports X (j + 1),
    ∑ _p ∈ T, distinctPrimeLogWeight T

theorem distinctPrimeLogWeight_nonneg (S : Finset ℕ) :
    0 ≤ distinctPrimeLogWeight S := by
  unfold distinctPrimeLogWeight
  positivity

theorem distinctPrimeLogMass_nonneg (X j : ℕ) :
    0 ≤ distinctPrimeLogMass X j := by
  unfold distinctPrimeLogMass
  exact Finset.sum_nonneg fun S _ ↦ distinctPrimeLogWeight_nonneg S

/-- Every admissible support has the declared order. -/
theorem card_eq_of_mem_distinctPrimeSupports
    {X j : ℕ} {S : Finset ℕ} (hS : S ∈ distinctPrimeSupports X j) :
    S.card = j := by
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1).2

/-- Marking one prime counts each order-`j+1` support exactly `j+1` times. -/
theorem distinctPrimeDeletionMass_eq
    (X j : ℕ) :
    distinctPrimeDeletionMass X j =
      ((j + 1 : ℕ) : ℝ) * distinctPrimeLogMass X (j + 1) := by
  unfold distinctPrimeDeletionMass distinctPrimeLogMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hcard := card_eq_of_mem_distinctPrimeSupports hT
  calc
    (∑ _p ∈ T, distinctPrimeLogWeight T) =
        (T.card : ℝ) * distinctPrimeLogWeight T := by simp
    _ = ((j + 1 : ℕ) : ℝ) * distinctPrimeLogWeight T := by rw [hcard]

/-- The prime-specific deletion estimate implies exactly the insertion
recurrence expected by `WeightedSimplex`.

The hypothesis is the remaining analytic gate.  Its two factors `(2j)` and
`(2j+1)` are separated from the combinatorial marking factor `j+1`. -/
theorem distinctPrimeLogMass_insertion_recurrence
    (X : ℕ) (B : ℝ)
    (hprime : ∀ j, 1 ≤ j →
      ((2 * j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) *
          distinctPrimeDeletionMass X j ≤
        B * distinctPrimeLogMass X j) :
    ∀ j, 1 ≤ j →
      ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ) * distinctPrimeLogMass X (j + 1) ≤
        B * distinctPrimeLogMass X j := by
  intro j hj
  have hp := hprime j hj
  rw [distinctPrimeDeletionMass_eq] at hp
  nlinarith

/-- The concrete distinct-prime mass inherits the full order-uniform
factorial denominator from a first-order bound and the one explicit
prime-insertion hypothesis. -/
theorem distinctPrimeLogMass_le_factorial_majorant
    (X : ℕ) (base B : ℝ)
    (hbase : distinctPrimeLogMass X 1 ≤ base) (hB : 0 ≤ B)
    (hprime : ∀ j, 1 ≤ j →
      ((2 * j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) *
          distinctPrimeDeletionMass X j ≤
        B * distinctPrimeLogMass X j)
    {j : ℕ} (hj : 1 ≤ j) :
    distinctPrimeLogMass X j ≤
      base * B ^ (j - 1) / simplexFactorialDenominator j := by
  apply mass_le_base_mul_pow_div_simplexFactorialDenominator
    (mass := distinctPrimeLogMass X) (base := base) (B := B)
    hbase hB
  · exact distinctPrimeLogMass_insertion_recurrence X B hprime
  · exact hj

end ZetaLean.HigherXi
