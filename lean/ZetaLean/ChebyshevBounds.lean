/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.PrimeSimplex

/-!
# Elementary Chebyshev bounds for the prime-simplex estimate

`LEAN-FRONTIER.md` item 19 names "a weighted Chebyshev estimate" as the
analytic input still missing from the formal tree.  This file supplies the
two elementary bounds every candidate route needs:

* `theta_le_mul_log_four`: the classical bound
  `θ(X) = ∑_{p ≤ X} log p ≤ X · log 4`, re-expressed over this tree's index
  set from Mathlib's `Chebyshev.theta_le_log4_mul_x` (reuse, not
  re-derivation: Mathlib already owns the Erdős primorial argument);
* `theta_sq_le`: the weighted form
  `∑_{p ≤ X} (log p)² ≤ log X · (X · log 4)`, which Mathlib does not have.

Both sums run over `primeCandidates X`, the exact index set of
`PrimeSimplex.lean`, which is definitionally Mathlib's `primesLE`.  Nothing
here touches the insertion recurrence itself; these are its raw materials.
-/

namespace ZetaLean.HigherXi

open Finset

/-- The prime-candidate set is the primorial's index set. -/
theorem prod_primeCandidates_eq_primorial (X : ℕ) :
    ∏ p ∈ primeCandidates X, p = primorial X := rfl

/-- Every prime candidate is at least `2`. -/
theorem two_le_of_mem_primeCandidates {X p : ℕ}
    (hp : p ∈ primeCandidates X) : 2 ≤ p :=
  (Finset.mem_filter.mp hp).2.two_le

/-- Every prime candidate is at most the cutoff. -/
theorem le_of_mem_primeCandidates {X p : ℕ}
    (hp : p ∈ primeCandidates X) : p ≤ X :=
  Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)

/-- Chebyshev's `θ` bound over this tree's index set,
`∑_{p ≤ X} log p ≤ X · log 4`, from Mathlib's
`Chebyshev.theta_le_log4_mul_x`. -/
theorem theta_le_mul_log_four (X : ℕ) :
    ∑ p ∈ primeCandidates X, Real.log p ≤ (X : ℝ) * Real.log 4 := by
  have hsum : ∑ p ∈ primeCandidates X, Real.log p = Chebyshev.theta X := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    rfl
  rw [hsum, mul_comm]
  exact Chebyshev.theta_le_log4_mul_x (by positivity)

/-- The weighted Chebyshev bound:
`∑_{p ≤ X} (log p)² ≤ log X · (X · log 4)`.

For `X ∈ {0, 1}` both sides are zero (the candidate set is empty and
`Real.log` of `0` and `1` is `0`), so no side condition is needed. -/
theorem theta_sq_le (X : ℕ) :
    ∑ p ∈ primeCandidates X, Real.log p ^ 2 ≤
      Real.log X * ((X : ℝ) * Real.log 4) := by
  rcases Nat.lt_or_ge X 2 with hX | hX
  · -- the candidate set is empty below 2
    have hempty : primeCandidates X = ∅ := by
      apply Finset.filter_false_of_mem
      intro p hp
      have hpX := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      intro hprime
      exact absurd (hprime.two_le.trans hpX) (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    interval_cases X
    · simp
    · simp
  · -- log X ≥ 0 and each (log p)² ≤ log X · log p
    have hlogX : 0 ≤ Real.log X := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_of_lt hX
    calc
      ∑ p ∈ primeCandidates X, Real.log p ^ 2 ≤
          ∑ p ∈ primeCandidates X, Real.log X * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have h2p : (2 : ℕ) ≤ p := two_le_of_mem_primeCandidates hp
        have hpX : p ≤ X := le_of_mem_primeCandidates hp
        have hlogp : 0 ≤ Real.log p := by
          apply Real.log_nonneg
          exact_mod_cast Nat.one_le_of_lt h2p
        have hmono : Real.log p ≤ Real.log X := by
          apply Real.log_le_log
          · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h2p
          · exact_mod_cast hpX
        calc
          Real.log p ^ 2 = Real.log p * Real.log p := sq (Real.log p) ▸ by ring
          _ ≤ Real.log X * Real.log p := by
            exact mul_le_mul_of_nonneg_right hmono hlogp
      _ = Real.log X * ∑ p ∈ primeCandidates X, Real.log p := by
        rw [Finset.mul_sum]
      _ ≤ Real.log X * ((X : ℝ) * Real.log 4) := by
        exact mul_le_mul_of_nonneg_left (theta_le_mul_log_four X) hlogX

/-- The general weighted form: `∑_{p ≤ X} (log p)^(k+1) ≤ (log X)^k · X log 4`.
Same termwise argument as `theta_sq_le`, at every power at once. -/
theorem theta_pow_succ_le (X k : ℕ) :
    ∑ p ∈ primeCandidates X, Real.log p ^ (k + 1) ≤
      Real.log X ^ k * ((X : ℝ) * Real.log 4) := by
  rcases Nat.lt_or_ge X 2 with hX | hX
  · have hempty : primeCandidates X = ∅ := by
      apply Finset.filter_false_of_mem
      intro p hp
      have hpX := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      intro hprime
      exact absurd (hprime.two_le.trans hpX) (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have hXlog : 0 ≤ Real.log X := by
      interval_cases X
      · simp
      · simp
    positivity
  · have hlogX : 0 ≤ Real.log X :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hX)
    calc
      ∑ p ∈ primeCandidates X, Real.log p ^ (k + 1) ≤
          ∑ p ∈ primeCandidates X, Real.log X ^ k * Real.log p := by
        apply Finset.sum_le_sum
        intro p hp
        have h2p : (2 : ℕ) ≤ p := two_le_of_mem_primeCandidates hp
        have hpX : p ≤ X := le_of_mem_primeCandidates hp
        have hlogp : 0 ≤ Real.log p :=
          Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt h2p)
        have hmono : Real.log p ≤ Real.log X := by
          apply Real.log_le_log
          · exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two h2p
          · exact_mod_cast hpX
        calc
          Real.log p ^ (k + 1) = Real.log p ^ k * Real.log p := by ring
          _ ≤ Real.log X ^ k * Real.log p := by
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hlogp hmono k) hlogp
      _ = Real.log X ^ k * ∑ p ∈ primeCandidates X, Real.log p := by
        rw [Finset.mul_sum]
      _ ≤ Real.log X ^ k * ((X : ℝ) * Real.log 4) := by
        exact mul_le_mul_of_nonneg_left (theta_le_mul_log_four X)
          (pow_nonneg hlogX k)

/-- Order-1 supports are exactly the singleton primes: the product filter is
vacuous at order 1, since a prime candidate already satisfies `p ≤ X`. -/
theorem distinctPrimeSupports_one (X : ℕ) :
    distinctPrimeSupports X 1 =
      (primeCandidates X).map ⟨_, Finset.singleton_injective⟩ := by
  unfold distinctPrimeSupports
  rw [Finset.powersetCard_one]
  apply Finset.filter_true_of_mem
  intro S hS
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hS
  simpa using le_of_mem_primeCandidates hp

/-- The first-order mass is the fourth log moment:
`A_1(X) = ∑_{p ≤ X} (log p)^4`. -/
theorem distinctPrimeLogMass_one (X : ℕ) :
    distinctPrimeLogMass X 1 =
      ∑ p ∈ primeCandidates X, Real.log p ^ 4 := by
  unfold distinctPrimeLogMass
  rw [distinctPrimeSupports_one, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro p _
  unfold distinctPrimeLogWeight
  simp only [Function.Embedding.coeFn_mk, Finset.sum_singleton,
    Finset.prod_singleton]
  ring

/-- The base bound the factorial majorant consumes:
`A_1(X) ≤ (log X)³ · X log 4`. -/
theorem distinctPrimeLogMass_one_le (X : ℕ) :
    distinctPrimeLogMass X 1 ≤ Real.log X ^ 3 * ((X : ℝ) * Real.log 4) := by
  rw [distinctPrimeLogMass_one]
  exact theta_pow_succ_le X 3

/-- Admissible supports have logarithmic size at most `log X`. -/
theorem logSum_le_log_of_mem_distinctPrimeSupports
    {X j : ℕ} {S : Finset ℕ}
    (hS : S ∈ distinctPrimeSupports X j) :
    ∑ p ∈ S, Real.log p ≤ Real.log X := by
  have hsub : S ⊆ primeCandidates X :=
    Finset.mem_powersetCard.mp (Finset.mem_filter.mp hS).1 |>.1
  have hprodX : (∏ p ∈ S, p) ≤ X := (Finset.mem_filter.mp hS).2
  have hpos : ∀ p ∈ S, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    have := two_le_of_mem_primeCandidates (hsub hp)
    positivity
  calc
    ∑ p ∈ S, Real.log p = Real.log (∏ p ∈ S, (p : ℝ)) := by
      rw [Real.log_prod]
      intro p hp
      exact (hpos p hp).ne'
    _ ≤ Real.log X := by
      apply Real.log_le_log
      · exact Finset.prod_pos hpos
      · calc
          (∏ p ∈ S, (p : ℝ)) = ((∏ p ∈ S, p : ℕ) : ℝ) := by push_cast; rfl
          _ ≤ (X : ℝ) := by exact_mod_cast hprodX

end ZetaLean.HigherXi
