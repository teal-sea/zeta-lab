/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.MatchingCount

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

/-- The finite all-matching weight polynomial on `r` labelled vertices.  The
coefficient of `weight a` is the exact arithmetic matching count with `a`
edges. -/
noncomputable def matchingCountPolynomial (r : ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Finset.range (r / 2 + 1), (matchingCount r a : ℝ) * weight a

omit [DecidableEq α] in
/-- Group a weight depending only on the number of matching edges into the
explicit `matchingCount` coefficients.  `card_matchingSlice` supplies the
finite bridge from the concrete matching-family fibres to the arithmetic
count. -/
theorem sum_matching_weight_eq_matchingCountPolynomial
    (S : Finset α) (weight : ℕ → ℝ) :
    (∑ M ∈ matchingFamily S, weight M.card) =
      matchingCountPolynomial S.card weight := by
  classical
  have hcount : ∀ a,
      ((matchingFamily S).filter fun M ↦ M.card = a).card =
        matchingCount S.card a := by
    intro a
    simpa [matchingSlice] using card_matchingSlice S a
  have hcard : (matchingFamily S : Set (Finset (Finset α))).MapsTo
      Finset.card (Finset.range (S.card / 2 + 1)) := by
    intro M hM
    have hbound : M.card < S.card / 2 + 1 := by
      rw [Nat.lt_add_one_iff]
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      by_contra hle
      have hlt : S.card < 2 * M.card := by omega
      have hzero := matchingCount_eq_zero_of_lt hlt
      have hfiber := hcount M.card
      have hmem : M ∈ (matchingFamily S).filter fun L ↦ L.card = M.card :=
        Finset.mem_filter.mpr ⟨hM, rfl⟩
      have hpos : 0 < ((matchingFamily S).filter fun L ↦ L.card = M.card).card :=
        Finset.card_pos.mpr ⟨M, hmem⟩
      rw [hfiber, hzero] at hpos
      omega
    exact Finset.mem_range.mpr hbound
  rw [matchingCountPolynomial,
    ← Finset.sum_fiberwise_of_maps_to
      (s := matchingFamily S)
      (t := Finset.range (S.card / 2 + 1))
      (g := Finset.card)
      hcard
      (fun M ↦ weight M.card)]
  apply Finset.sum_congr rfl
  intro a ha
  have hinner : (∑ M ∈ matchingFamily S with M.card = a, weight M.card) =
      (((matchingFamily S).filter fun M ↦ M.card = a).card : ℝ) * weight a := by
    calc
      _ = ∑ _M ∈ matchingFamily S with _M.card = a, weight a := by
        apply Finset.sum_congr rfl
        intro M hM
        exact congrArg weight (Finset.mem_filter.mp hM).2
      _ = _ := by simp
  rw [hinner]
  rw [hcount a]

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

/-- The connected nonnegative matching mass is at most the full two-colour
matching mass. -/
theorem connectedMatchingMass_le_matchingPairMass
    (S : Finset α) (monomer : α → ℝ) (dimer : Finset α → ℝ)
    (hmonomer : ∀ p ∈ S, 0 ≤ monomer p)
    (hdimer : ∀ e ∈ S.powersetCard 2, 0 ≤ dimer e) :
    connectedMatchingMass S monomer dimer ≤
      matchingPairMass S monomer dimer := by
  classical
  unfold connectedMatchingMass matchingPairMass
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro MN hMN _
  have hM₁ : MN.1 ∈ matchingFamily S := (Finset.mem_product.mp hMN).1
  have hM₂ : MN.2 ∈ matchingFamily S := (Finset.mem_product.mp hMN).2
  have hsub₁ := (mem_matchingFamily_iff.mp hM₁).1
  have hsub₂ := (mem_matchingFamily_iff.mp hM₂).1
  exact mul_nonneg
    (matchingTerm_nonneg hmonomer (fun e he ↦ hdimer e (hsub₁ he)))
    (matchingTerm_nonneg hmonomer (fun e he ↦ hdimer e (hsub₂ he)))

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

/-- A finite connected two-colour mass is bounded by the square of an explicit
one-colour matching-count polynomial.

`card_matchingSlice` supplies the exact finite labelled enumeration. `hterm`
is the remaining local weight estimate for one matching. No support-density
or prime-sum estimate occurs in this theorem. -/
theorem abs_connectedMatchingMass_le_matchingCountPolynomial_sq
    (S : Finset α) (monomer monomerMajorant : α → ℝ)
    (dimer dimerMajorant : Finset α → ℝ) (weight : ℕ → ℝ)
    (hmonomer_nonneg : ∀ p ∈ S, 0 ≤ monomerMajorant p)
    (hdimer_nonneg : ∀ e ∈ S.powersetCard 2, 0 ≤ dimerMajorant e)
    (hmonomer : ∀ p ∈ S, |monomer p| ≤ monomerMajorant p)
    (hdimer : ∀ e ∈ S.powersetCard 2, |dimer e| ≤ dimerMajorant e)
    (hweight : ∀ a ∈ Finset.range (S.card / 2 + 1), 0 ≤ weight a)
    (hterm : ∀ M ∈ matchingFamily S,
      matchingTerm M S monomerMajorant dimerMajorant ≤ weight M.card) :
    |connectedMatchingMass S monomer dimer| ≤
      matchingCountPolynomial S.card weight ^ 2 := by
  classical
  have hpoint := abs_connectedMatchingMass_le_of_pointwise
    S monomer monomerMajorant dimer dimerMajorant
    hmonomer_nonneg hdimer_nonneg hmonomer hdimer
  have hfull := connectedMatchingMass_le_matchingPairMass
    S monomerMajorant dimerMajorant hmonomer_nonneg hdimer_nonneg
  have hcoefficient : monomerDimerCoefficient S monomerMajorant dimerMajorant ≤
      matchingCountPolynomial S.card weight := by
    calc
      monomerDimerCoefficient S monomerMajorant dimerMajorant =
          ∑ M ∈ matchingFamily S,
            matchingTerm M S monomerMajorant dimerMajorant := rfl
      _ ≤ ∑ M ∈ matchingFamily S, weight M.card :=
        Finset.sum_le_sum hterm
      _ = matchingCountPolynomial S.card weight :=
        sum_matching_weight_eq_matchingCountPolynomial S weight
  have hcoefficient_nonneg :
      0 ≤ monomerDimerCoefficient S monomerMajorant dimerMajorant := by
    unfold monomerDimerCoefficient
    exact Finset.sum_nonneg fun M hM ↦
      matchingTerm_nonneg hmonomer_nonneg
        (fun e he ↦ hdimer_nonneg e
          ((mem_matchingFamily_iff.mp hM).1 he))
  have hpolynomial_nonneg : 0 ≤ matchingCountPolynomial S.card weight := by
    unfold matchingCountPolynomial
    exact Finset.sum_nonneg fun a ha ↦
      mul_nonneg (Nat.cast_nonneg _) (hweight a ha)
  calc
    |connectedMatchingMass S monomer dimer| ≤
        connectedMatchingMass S monomerMajorant dimerMajorant := hpoint
    _ ≤ matchingPairMass S monomerMajorant dimerMajorant := hfull
    _ = monomerDimerCoefficient S monomerMajorant dimerMajorant ^ 2 :=
      (monomerDimerCoefficient_sq_eq_matchingPairMass
        S monomerMajorant dimerMajorant).symm
    _ ≤ matchingCountPolynomial S.card weight ^ 2 := by nlinarith

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
