/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterMajorant
import ZetaLean.SupportSizeMajorant

/-!
# Rooted matching coefficient bound

This file inserts the root-factorial weight from the exact squarefree
`Q(S)` formula into the finite matching interface. It proves the local
all-matching bound before any prime-support summation. No prime-simplex
estimate, repeated-prime estimate, or RAMS2 statement occurs here.
-/

namespace ZetaLean.HigherXi

open Finset

variable {α : Type*} [DecidableEq α]

/-- The rooted finite matching coefficient. The factor
`(S.card - M.card - 1)!` is the Laplace root weight in the exact squarefree
coefficient formula. -/
noncomputable def rootedMatchingCoefficient (S : Finset α)
    (monomer : α → ℝ) (dimer : Finset α → ℝ) : ℝ :=
  ∑ M ∈ matchingFamily S,
    ((S.card - M.card - 1).factorial : ℝ) *
      matchingTerm M S monomer dimer

/-- The one-matching weight after replacing every monomer and dimer by `2`. -/
noncomputable def rootedMatchingWeight (r a : ℕ) : ℝ :=
  ((r - a - 1).factorial : ℝ) * (2 : ℝ) ^ (r - a)

theorem rootedMatchingWeight_nonneg (r a : ℕ) :
    0 ≤ rootedMatchingWeight r a := by
  unfold rootedMatchingWeight
  positivity

/-- A concrete matching on `S` has exactly `S.card - 2*M.card` uncovered
vertices. -/
theorem card_support_sdiff_coveredVertices {S : Finset α}
    {M : Finset (Finset α)} (hM : M ∈ matchingFamily S) :
    (S \ coveredVertices M).card = S.card - 2 * M.card := by
  rw [Finset.card_sdiff,
    Finset.inter_eq_left.mpr
      (coveredVertices_subset_of_mem_matchingFamily hM),
    card_coveredVertices_of_mem_matchingFamily hM]

/-- With every local weight equal to `2`, a matching with `a` edges has
weight `2^(r-a)`: each edge removes two monomers and contributes one dimer. -/
theorem matchingTerm_const_two {S : Finset α} {M : Finset (Finset α)}
    (hM : M ∈ matchingFamily S) :
    matchingTerm M S (fun _ ↦ (2 : ℝ)) (fun _ ↦ (2 : ℝ)) =
      (2 : ℝ) ^ (S.card - M.card) := by
  rw [matchingTerm]
  simp only [Finset.prod_const]
  rw [card_support_sdiff_coveredVertices hM]
  have hcard : 2 * M.card ≤ S.card := by
    rw [← card_coveredVertices_of_mem_matchingFamily hM]
    exact Finset.card_le_card
      (coveredVertices_subset_of_mem_matchingFamily hM)
  rw [← pow_add]
  congr 1
  omega

/-- The absolute rooted coefficient is bounded by the explicit all-matching
polynomial with weight `(r-a-1)! 2^(r-a)`. -/
theorem abs_rootedMatchingCoefficient_le_matchingCountPolynomial
    (S : Finset α) (monomer : α → ℝ) (dimer : Finset α → ℝ)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ 2)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ 2) :
    |rootedMatchingCoefficient S monomer dimer| ≤
      matchingCountPolynomial S.card (rootedMatchingWeight S.card) := by
  classical
  unfold rootedMatchingCoefficient
  calc
    |∑ M ∈ matchingFamily S,
        ((S.card - M.card - 1).factorial : ℝ) *
          matchingTerm M S monomer dimer| ≤
        ∑ M ∈ matchingFamily S,
          |((S.card - M.card - 1).factorial : ℝ) *
            matchingTerm M S monomer dimer| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ M ∈ matchingFamily S, rootedMatchingWeight S.card M.card := by
      apply Finset.sum_le_sum
      intro M hM
      rw [abs_mul, abs_of_nonneg (by positivity :
        0 ≤ ((S.card - M.card - 1).factorial : ℝ))]
      have hterm := abs_matchingTerm_le_of_pointwise
        (M := M) (S := S)
        (monomerMajorant := fun _ ↦ (2 : ℝ))
        (dimerMajorant := fun _ ↦ (2 : ℝ))
        (fun _ _ ↦ by norm_num) hmonomer
        (fun e he ↦ hdimer e ((mem_matchingFamily_iff.mp hM).1 he))
      rw [matchingTerm_const_two hM] at hterm
      unfold rootedMatchingWeight
      exact mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = matchingCountPolynomial S.card (rootedMatchingWeight S.card) :=
      sum_matching_weight_eq_matchingCountPolynomial S
        (rootedMatchingWeight S.card)

/-- The matching-count polynomial with rooted local weight is exactly
`2^r S_r`, the finite coefficient used by the squarefree cluster majorant. -/
theorem matchingCountPolynomial_rootedMatchingWeight_eq (r : ℕ) :
    matchingCountPolynomial r (rootedMatchingWeight r) =
      (2 : ℝ) ^ r * rootedMatchingSum r := by
  unfold matchingCountPolynomial rootedMatchingSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have har : a ≤ r := by
    have ha' := Finset.mem_range.mp ha
    omega
  have hpow : (2 : ℝ) ^ (r - a) = (2 : ℝ) ^ r / (2 : ℝ) ^ a := by
    rw [pow_sub₀ _ (by norm_num) har]
    rfl
  unfold rootedMatchingWeight rootedMatchingSummand
  rw [hpow]
  ring

/-- Direct local form of the report's `2^r S_r` bound. -/
theorem abs_rootedMatchingCoefficient_le_two_pow_mul_rootedMatchingSum
    (S : Finset α) (monomer : α → ℝ) (dimer : Finset α → ℝ)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ 2)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ 2) :
    |rootedMatchingCoefficient S monomer dimer| ≤
      (2 : ℝ) ^ S.card * rootedMatchingSum S.card := by
  rw [← matchingCountPolynomial_rootedMatchingWeight_eq]
  exact abs_rootedMatchingCoefficient_le_matchingCountPolynomial
    S monomer dimer hmonomer hdimer

end ZetaLean.HigherXi
