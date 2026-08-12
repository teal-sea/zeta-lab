/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterPrefix

/-!
# Finite majorants for connected matching clusters

`ClusterPrefix` isolates the connected part of the two-colour matching square.
This file supplies the next finite inequality: signed monomer and dimer weights
may be replaced by pointwise nonnegative majorants inside that connected sum.

The result is deliberately finite.  It does not count connected matching
pairs, estimate a prime-support sum, or assert the RAMS2 prefix asymptotic.
Those remain separate inputs.
-/

namespace ZetaLean.HigherXi

open Finset

variable {α : Type*} [DecidableEq α]

/-- A monomer-dimer term with nonnegative local weights is nonnegative. -/
theorem matchingTerm_nonneg {M : Finset (Finset α)} {S : Finset α}
    {monomer : α → ℝ} {dimer : Finset α → ℝ}
    (hmonomer : ∀ p ∈ S, 0 ≤ monomer p)
    (hdimer : ∀ e ∈ M, 0 ≤ dimer e) :
    0 ≤ matchingTerm M S monomer dimer := by
  unfold matchingTerm
  apply mul_nonneg
  · exact Finset.prod_nonneg fun e he ↦ hdimer e he
  · exact Finset.prod_nonneg fun p hp ↦ hmonomer p (Finset.mem_sdiff.mp hp).1

/-- Pointwise nonnegative bounds on the local weights majorize one complete
matching term after taking its absolute value. -/
theorem abs_matchingTerm_le_of_pointwise
    {M : Finset (Finset α)} {S : Finset α}
    {monomer monomerMajorant : α → ℝ}
    {dimer dimerMajorant : Finset α → ℝ}
    (hdimer_nonneg : ∀ e ∈ M, 0 ≤ dimerMajorant e)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ monomerMajorant p)
    (hdimer : ∀ e ∈ M, |dimer e| ≤ dimerMajorant e) :
    |matchingTerm M S monomer dimer| ≤
      matchingTerm M S monomerMajorant dimerMajorant := by
  unfold matchingTerm
  rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
  apply mul_le_mul
  · exact Finset.prod_le_prod
      (fun _ _ ↦ abs_nonneg _)
      (fun e he ↦ hdimer e he)
  · exact Finset.prod_le_prod
      (fun _ _ ↦ abs_nonneg _)
      (fun p hp ↦ hmonomer p (Finset.mem_sdiff.mp hp).1)
  · exact Finset.prod_nonneg fun _ _ ↦ abs_nonneg _
  · exact Finset.prod_nonneg fun e he ↦ hdimer_nonneg e he

/-- The absolute value of the connected signed mass is bounded by the same
connected sum formed from pointwise nonnegative majorants. -/
theorem abs_connectedMatchingMass_le_of_pointwise
    (S : Finset α) (monomer monomerMajorant : α → ℝ)
    (dimer dimerMajorant : Finset α → ℝ)
    (hmonomer_nonneg : ∀ p ∈ S, 0 ≤ monomerMajorant p)
    (hdimer_nonneg : ∀ e ∈ S.powersetCard 2, 0 ≤ dimerMajorant e)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ monomerMajorant p)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ dimerMajorant e) :
    |connectedMatchingMass S monomer dimer| ≤
      connectedMatchingMass S monomerMajorant dimerMajorant := by
  classical
  unfold connectedMatchingMass
  calc
    |∑ MN ∈ (matchingFamily S ×ˢ matchingFamily S).filter
        (fun MN ↦ MatchingPairConnected S MN.1 MN.2),
        matchingTerm MN.1 S monomer dimer *
          matchingTerm MN.2 S monomer dimer| ≤
        ∑ MN ∈ (matchingFamily S ×ˢ matchingFamily S).filter
          (fun MN ↦ MatchingPairConnected S MN.1 MN.2),
          |matchingTerm MN.1 S monomer dimer *
            matchingTerm MN.2 S monomer dimer| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ MN ∈ (matchingFamily S ×ˢ matchingFamily S).filter
          (fun MN ↦ MatchingPairConnected S MN.1 MN.2),
          matchingTerm MN.1 S monomerMajorant dimerMajorant *
            matchingTerm MN.2 S monomerMajorant dimerMajorant := by
      apply Finset.sum_le_sum
      intro MN hMN
      rw [abs_mul]
      have hM₁ : MN.1 ∈ matchingFamily S := by
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hMN).1).1
      have hM₂ : MN.2 ∈ matchingFamily S := by
        exact (Finset.mem_product.mp (Finset.mem_filter.mp hMN).1).2
      have hsub₁ := (mem_matchingFamily_iff.mp hM₁).1
      have hsub₂ := (mem_matchingFamily_iff.mp hM₂).1
      have hterm₁ := abs_matchingTerm_le_of_pointwise
        (M := MN.1) (S := S)
        (fun e he ↦ hdimer_nonneg e (hsub₁ he)) hmonomer
        (fun e he ↦ hdimer e (hsub₁ he))
      have hterm₂ := abs_matchingTerm_le_of_pointwise
        (M := MN.2) (S := S)
        (fun e he ↦ hdimer_nonneg e (hsub₂ he)) hmonomer
        (fun e he ↦ hdimer e (hsub₂ he))
      exact mul_le_mul hterm₁ hterm₂ (abs_nonneg _)
        (matchingTerm_nonneg hmonomer_nonneg
          (fun e he ↦ hdimer_nonneg e (hsub₁ he)))

/-- Prefix-level form of the connected majorant.  The analytic problem is now
isolated in the nonnegative sum on the right. -/
theorem abs_sum_connectedMatchingMass_le_of_pointwise
    (support : ℕ → Finset α)
    (monomer monomerMajorant : ℕ → α → ℝ)
    (dimer dimerMajorant : ℕ → Finset α → ℝ) (N : ℕ)
    (hmonomer_nonneg : ∀ n p, p ∈ support n → 0 ≤ monomerMajorant n p)
    (hdimer_nonneg : ∀ n e, e ∈ (support n).powersetCard 2 →
      0 ≤ dimerMajorant n e)
    (hmonomer : ∀ n p, p ∈ support n →
      |monomer n p| ≤ monomerMajorant n p)
    (hdimer : ∀ n e, e ∈ (support n).powersetCard 2 →
      |dimer n e| ≤ dimerMajorant n e) :
    |∑ n ∈ Finset.Icc 1 N,
        connectedMatchingMass (support n) (monomer n) (dimer n)| ≤
      ∑ n ∈ Finset.Icc 1 N,
        connectedMatchingMass (support n) (monomerMajorant n)
          (dimerMajorant n) := by
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        |connectedMatchingMass (support n) (monomer n) (dimer n)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      exact abs_connectedMatchingMass_le_of_pointwise
        (support n) (monomer n) (monomerMajorant n)
        (dimer n) (dimerMajorant n)
        (hmonomer_nonneg n) (hdimer_nonneg n)
        (hmonomer n) (hdimer n)

end ZetaLean.HigherXi
