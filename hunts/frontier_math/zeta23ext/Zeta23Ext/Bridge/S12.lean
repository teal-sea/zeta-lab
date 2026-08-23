/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# S12: the block defect bound  ([A] Lemma 4.3, eq:block-defect)

`tr Psi(G) ≥ min{1, 2 Σ_{i<j} |G_{ij}|²}` for `G ⪰ 0`.  Since `Psi = gc 2 + 1`
(`Zeta23Ext/StableRankTrace.lean`), this is a statement about upstream's `gc 2`.

Proved here (bridge/finite), by the two cases of the paper: if every eigenvalue is `≤ 2` then
`Psi(G) = (G − I)²` so `tr Psi(G) = ‖G − I‖_F² ≥ Σ_{i≠j}|G_{ij}|²`; if some eigenvalue exceeds `2`
its `Psi`-value alone exceeds `1` and the remaining terms are nonnegative.  Note that the
hypothesis `G ⪰ 0` is never used: the bound holds for every Hermitian `G`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace

namespace Zeta23Ext.Bridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `specMap` of the constant function `1` is the identity matrix (`U Uᴴ = I`). -/
lemma specMap_const_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun _ => 1) = 1 := by
  unfold specMap
  simp

/-- `specMap hA (t ↦ t − 1) = A − I`. -/
lemma specMap_sub_one {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    specMap hA (fun t => t - 1) = A - 1 := by
  have h : (fun t : ℝ => t - 1) = id - fun _ => 1 := rfl
  rw [h, specMap_sub, specMap_id, specMap_const_one]

/-- The off-diagonal mass is dominated by the full Frobenius mass of `A − I`. -/
lemma offDiagSqOn_le_frobSq_sub_one (A : Matrix ι ι ℂ) :
    offDiagSqOn A univ ≤ frobSq (A - 1) := by
  rw [Zeta23.Assembly.frobSq_eq_sum_norm_sq]
  unfold offDiagSqOn
  refine sum_le_sum fun i _ => sum_le_sum fun j _ => ?_
  split_ifs with h
  · positivity
  · rw [Matrix.sub_apply, Matrix.one_apply_ne h, sub_zero]

/-- **S12, Hermitian form.**  `min{1, Σ_{i≠j} |A_{ij}|²} ≤ tr Psi(A)` for every Hermitian `A`. -/
theorem block_defect_of_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    min 1 (offDiagSqOn A univ) ≤ defect hA := by
  unfold defect
  rw [rtrace_specMap]
  by_cases hall : ∀ i, hA.eigenvalues i ≤ 2
  · -- every eigenvalue `≤ 2`: `Psi = (· − 1)²` on the spectrum
    have hsum : ∑ i, Psi (hA.eigenvalues i) = ∑ i, (hA.eigenvalues i - 1) ^ 2 :=
      sum_congr rfl fun i _ => by simp [Psi, hall i]
    have hfrob := frobSq_specMap hA (fun t => t - 1)
    rw [specMap_sub_one] at hfrob
    rw [hsum, ← hfrob]
    exact (min_le_right _ _).trans (offDiagSqOn_le_frobSq_sub_one A)
  · -- some eigenvalue `> 2`: its `Psi`-value alone exceeds `1`
    push Not at hall
    obtain ⟨i, hi⟩ := hall
    refine (min_le_left _ _).trans ?_
    calc (1 : ℝ) ≤ Psi (hA.eigenvalues i) := by
          unfold Psi; rw [if_neg (not_le.mpr hi)]; linarith
      _ ≤ ∑ j, Psi (hA.eigenvalues j) :=
          single_le_sum (fun j _ => Psi_nonneg (hA.eigenvalues j)) (mem_univ i)

/-- **S12** ([A] Lemma 4.3).  `min{1, Σ_{i≠j} |G_{ij}|²} ≤ tr Psi(G)` for `G ⪰ 0`.
PROVED (bridge/finite); positivity of `G` is not needed, see `block_defect_of_isHermitian`. -/
theorem block_defect {G : Matrix ι ι ℂ} (hG : G.PosSemidef) :
    min 1 (offDiagSqOn G univ) ≤ defect hG.1 :=
  block_defect_of_isHermitian hG.1

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms specMap_const_one
#print axioms block_defect_of_isHermitian
#print axioms block_defect

end Zeta23Ext.Bridge
