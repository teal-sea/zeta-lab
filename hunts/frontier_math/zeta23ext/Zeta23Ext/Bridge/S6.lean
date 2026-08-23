/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23Ext.Bridge.Defs

/-!
# S6: regrouping `Â = P₁ + Q'` with `n₊(Q') ≤ s₂ + p`  ([A] eq:index, [C26] Prop 4.4 proof body)

`[L23]` collects *all* on-line zeros into one positive block (`blockP`, rank `≤ s₁ + s₂`) and
bounds `n₊(blockQ) ≤ p`.  Ainta needs the simple zeros alone as the positive factor
`P₁ = V Vᴴ` and everything else in `Q' = Â − P₁`.  The ingredients are all upstream
(`posIndex_add_le`, `posIndex_sub_le_rank`, `rank_sum_le`, `onLine_eq_S₁_union_S₂`,
`posIndex_blockQ_le`); the seam itself is not a named upstream declaration (TRUST-MAP S6).

Proved here (bridge/finite): `blockP c − P₁ c = c⁻¹ Σ_{ρ ∈ 𝒮₂} m_ρ u_ρ u_ρᵀ` (on `𝒮₁` the
multiplicity is `1` and `u_ρ` is real, so `m u uᵀ = c · v vᴴ`), which is positive semidefinite of
rank `≤ s₂`; then `n₊(Q') ≤ rank(blockP − P₁) + n₊(blockQ) ≤ s₂ + p`.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23 Zeta23.ZeroSide

namespace Zeta23Ext.Bridge

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : ZeroBlockData ι d)

/-- The multiple-zero part of `blockP`: `c⁻¹ Σ_{ρ ∈ 𝒮₂} m_ρ u_ρ u_ρᵀ`. -/
def multPart (c : ℝ) : Matrix d d ℂ :=
  ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₂, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)

lemma mem_S₂_σ {z : ι} (hz : z ∈ D.S₂) : D.σ z = z := by
  simp only [ZeroBlockData.S₂, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_σ {z : ι} (hz : z ∈ D.S₁) : D.σ z = z := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.1

lemma mem_S₁_m {z : ι} (hz : z ∈ D.S₁) : D.m z = 1 := by
  simp only [ZeroBlockData.S₁, mem_filter, mem_univ, true_and] at hz
  exact hz.2

lemma multPart_posSemidef {c : ℝ} (hc : 0 < c) : (multPart D c).PosSemidef := by
  unfold multPart
  refine (posSemidef_sum _ fun z hz => ?_).smul (Complex.zero_le_real.mpr (inv_nonneg.mpr hc.le))
  have := ZeroBlockData.posSemidef_smul_vecMulVec (D.star_v_of_onLine (mem_S₂_σ D hz)) (Nat.cast_nonneg (D.m z))
  simpa using this

lemma rank_multPart_le {c : ℝ} (hc : 0 < c) : (multPart D c).rank ≤ D.s₂ := by
  unfold multPart
  rw [rank_smul_of_ne_zero _ (by exact_mod_cast (inv_ne_zero hc.ne'))]
  refine (rank_sum_le _ _ (fun _ => 1) fun z _ => rank_smul_vecMulVec_le _ _ _).trans ?_
  simp [ZeroBlockData.s₂]

/-- `P₁ = V Vᴴ = c⁻¹ Σ_{ρ ∈ 𝒮₁} m_ρ u_ρ u_ρᵀ`: on `𝒮₁`, `m_ρ = 1` and `u_ρ` is real. -/
lemma P₁_eq_simplePart {c : ℝ} (hc : 0 < c) :
    P₁ D c = ((c⁻¹ : ℝ) : ℂ) • ∑ z ∈ D.S₁, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z) := by
  ext k l
  simp only [P₁, Vsimple, mul_apply, conjTranspose_apply, Matrix.smul_apply, Matrix.sum_apply,
    vecMulVec_apply, smul_eq_mul]
  rw [← Finset.sum_coe_sort D.S₁, mul_sum]
  refine sum_congr rfl fun z _ => ?_
  have hσ := mem_S₁_σ D z.2
  have hm := mem_S₁_m D z.2
  have hstar : star (D.v z l) = D.v z l := congrFun (D.star_v_of_onLine hσ) l
  rw [hm, star_div₀, hstar, Nat.cast_one, one_mul, Complex.star_def, Complex.conj_ofReal]
  have hsq : ((Real.sqrt c : ℂ)) * (Real.sqrt c : ℂ) = (c : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
  rw [div_mul_div_comm, hsq, Complex.ofReal_inv, inv_mul_eq_div]

/-- `Q' = (blockP − P₁) + blockQ` with `blockP − P₁ = multPart`. -/
lemma Q'_eq_multPart_add_blockQ {c : ℝ} (hc : 0 < c) :
    Q' D c = multPart D c + D.blockQ c := by
  unfold Q' ZeroBlockData.blockP ZeroBlockData.onPart multPart
  rw [P₁_eq_simplePart D hc, D.onLine_eq_S₁_union_S₂, sum_union D.disjoint_S₁_S₂, smul_add]
  abel

/-- **S6.**  `n₊(Q') ≤ s₂ + p` for `Q' = blockP + blockQ − P₁`, `c > 0`.
PROVED (bridge/finite); see the module docstring. -/
theorem regroup_posIndex (Pr : D.PairReps) {c : ℝ} (hc : 0 < c) :
    posIndex (Q'_isHermitian D c) ≤ D.s₂ + Pr.p := by
  have hR := multPart_posSemidef D hc
  have hH : (multPart D c + D.blockQ c).IsHermitian := hR.isHermitian.add (D.blockQ_isHermitian c)
  rw [ZeroBlockData.posIndex_congr (Q'_isHermitian D c) hH (Q'_eq_multPart_add_blockQ D hc)]
  calc posIndex hH
      ≤ posIndex hR.isHermitian + posIndex (D.blockQ_isHermitian c) := posIndex_add_le _ _
    _ ≤ D.s₂ + Pr.p := by
        rw [posIndex_eq_rank_of_posSemidef hR]
        exact Nat.add_le_add (rank_multPart_le D hc) (D.posIndex_blockQ_le Pr hc)

/-! ### Standing axiom audit (idiom of `Zeta23Ext/StableRankTrace.lean`) -/

#print axioms P₁_eq_simplePart
#print axioms regroup_posIndex

end Zeta23Ext.Bridge
