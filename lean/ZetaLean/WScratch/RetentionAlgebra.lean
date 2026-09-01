import Mathlib

open scoped BigOperators
open Finset

namespace RetentionAlgebra

/-- Split a square double sum into its strictly-lower, strictly-upper and diagonal parts,
using symmetry to identify the two off-diagonal halves. -/
private lemma sum_sq_split (n : ℕ) (R : ℕ → ℕ → ℝ) (hsym : ∀ j k, R j k = R k j) :
    ∑ j ∈ range n, ∑ k ∈ range n, R j k
      = 2 * ∑ j ∈ range n, ∑ k ∈ range n, (if j < k then R j k else 0)
        + ∑ j ∈ range n, R j j := by
  have key : ∀ j k : ℕ,
      R j k = (if j < k then R j k else 0) + (if k < j then R j k else 0)
              + (if j = k then R j k else 0) := by
    intro j k
    rcases lt_trichotomy j k with h | h | h
    · simp [h, h.ne, Nat.not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne', Nat.not_lt.2 h.le]
  have hlow : ∑ j ∈ range n, ∑ k ∈ range n, (if k < j then R j k else 0)
      = ∑ j ∈ range n, ∑ k ∈ range n, (if j < k then R j k else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases h : j < k
    · simp [h, hsym k j]
    · simp [h]
  have hdiag : ∑ j ∈ range n, ∑ k ∈ range n, (if j = k then R j k else 0)
      = ∑ j ∈ range n, R j j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [hj]
  calc ∑ j ∈ range n, ∑ k ∈ range n, R j k
      = ∑ j ∈ range n, ∑ k ∈ range n,
          ((if j < k then R j k else 0) + (if k < j then R j k else 0)
            + (if j = k then R j k else 0)) := by
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => key j k
    _ = (∑ j ∈ range n, ∑ k ∈ range n, (if j < k then R j k else 0))
        + (∑ j ∈ range n, ∑ k ∈ range n, (if k < j then R j k else 0))
        + ∑ j ∈ range n, ∑ k ∈ range n, (if j = k then R j k else 0) := by
        simp [Finset.sum_add_distrib]
    _ = 2 * ∑ j ∈ range n, ∑ k ∈ range n, (if j < k then R j k else 0)
        + ∑ j ∈ range n, R j j := by rw [hlow, hdiag]; ring

/-- **The exact retention margin.**  Purely from the gap identity (G1): the
amount by which the retention inequality `(199/200) * EF + n/200 + 4 <= EFP`
holds is `(1/200) * (EF - n)` plus the damage budget.  `A` is the constant
`Aconst` (nonzero), `EF` is `Eng (Fsum n x)`, `EFP` is `Eng (F + P)`, `D j` is
the damage `Qim ^ 2 - Qre ^ 2` at site `j`, and `S` is `Shq y`. -/
theorem margin_eq (n : ℕ) (A EF EFP S : ℝ) (D : ℕ -> ℝ) (hA : A ≠ 0)
    (hgap : EFP = EF + 4 + (1 / A ^ 2) * (4 * ∑ j ∈ range n, (- D j) + 2 * S)) :
    EFP - ((199/200) * EF + (n : ℝ)/200 + 4)
      = (1/200) * (EF - (n : ℝ))
        + (1 / A ^ 2) * (2 * S - 4 * ∑ j ∈ range n, D j) := by
  have hneg : ∑ j ∈ range n, (- D j) = - ∑ j ∈ range n, D j := by
    simp [Finset.sum_neg_distrib]
  rw [hgap, hneg]
  ring

/-- **The repulsion is exactly the slack in `n <= EF`.**  From the energy
identity (G2) together with the diagonal normalisation `R j j = A ^ 2`: the
excess of `EF` over `n` is twice the strictly-upper-triangular sum, i.e. the
repulsion term that the weaker bound `n <= EF` discards.  `R j k` is
`Qre 0 (x j - x k) ^ 2`, symmetric in its arguments. -/
theorem energy_sub_card (n : ℕ) (A : ℝ) (R : ℕ -> ℕ -> ℝ) (hA : A ≠ 0)
    (hsym : ∀ j k, R j k = R k j) (hdiag : ∀ j, R j j = A ^ 2)
    (EF : ℝ) (hEF : EF = (1 / A ^ 2) * ∑ j ∈ range n, ∑ k ∈ range n, R j k) :
    EF - (n : ℝ)
      = (2 / A ^ 2) * ∑ j ∈ range n, ∑ k ∈ range n, (if j < k then R j k else 0) := by
  have hA2 : A ^ 2 ≠ 0 := pow_ne_zero _ hA
  have hd : ∑ j ∈ range n, R j j = (n : ℝ) * A ^ 2 := by
    simp [hdiag]
  rw [hEF, sum_sq_split n R hsym, hd]
  field_simp
  ring

end RetentionAlgebra

#print axioms RetentionAlgebra.margin_eq
#print axioms RetentionAlgebra.energy_sub_card
