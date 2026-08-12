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

* `theta_le_mul_log_four` — the classical bound
  `θ(X) = ∑_{p ≤ X} log p ≤ X · log 4`, re-expressed over this tree's index
  set from Mathlib's `Chebyshev.theta_le_log4_mul_x` (reuse, not
  re-derivation: Mathlib already owns the Erdős primorial argument);
* `theta_sq_le` — the weighted form
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

end ZetaLean.HigherXi
