/-
Copyright (c) 2026 Zeta Lab. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ZeroSide.RankTraceMult

/-!
# The stability-enhanced rank–trace inequality (Ainta, §2)

This file states and proves S2 of `hunts/ainta_seven_point/TRUST-MAP.md` §4: the one
piece of linear algebra that the `ainta/zeta-simple-zeros` note adds to the rank–trace
lemma of `[L23]` §3.  It carries a nonnegative *spectral defect* `tr Psi(VᴴV)` through
the inequality, where

  `Psi t = (t − 1)²` for `t ≤ 2`,   `Psi t = 2t − 3` for `t > 2`.

## What this file found, and it changes the picture

`Psi` is not new to this Lean development.  It is upstream's own `gc 2`, shifted:

  `Psi = fun t => gc 2 t + 1`   (`Psi_eq_gc_two_add_one`, kernel-checked below),

where `gc c x = x² − cx − ((x − c)⁺)²` is
`Zeta23.ZeroSide.RankTraceMult.gc`.  The additive `1` is exactly `Psi 0`, and it is
what converts a defect summed over the *nonzero* spectrum against a rank count into a
defect summed over *all* of `r` against `Fintype.card r`.  Everything else Ainta's
lemma needs, the sharpened termwise estimate (`sq_sub_ge_gc`) and the transfer of the
nonzero spectrum between `V Vᴴ` and `VᴴV` (`sum_eigenvalues_comm`), is already a
kernel-checked declaration upstream.

So `stable_rank_trace` is proved here as a **corollary** of the upstream multiplicity-aware
`rank_trace_mult`, evaluated at the eigenbasis presentation of `P = V Vᴴ` (which is the
presentation at which upstream's Schur–Jensen step `sum_gc_eigenvalues_ge` is an equality).
No new analysis, no new scalar estimate, and no copied proof skeleton.

## The two forms

* `stable_rank_trace_sharp`: no hypothesis on the columns of `V` at all,
    `2·tr(V Vᴴ) + 4·tr Q − card r − 4b + tr Psi(VᴴV) ≤ ‖V Vᴴ + Q‖_F²`.
* `stable_rank_trace`: the trust map's statement, which is the sharp form weakened by
  `2·(card r − tr(V Vᴴ)) ≥ 0`.  That is the only place the column bound `hV` is used.

## Non-vacuity

`stable_rank_trace_collapse` is the trust map's built-in test: with the defect set to `0`
the statement is `stable_rank_trace_no_defect`, which is proved independently from
`RHLinalg.rank_trace_ineq_two`.  The defect is nonnegative (`Psi_nonneg`), so the
enhanced form really is a strengthening of the existing theorem and not a different one.
-/

noncomputable section
set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open Zeta23.ZeroSide.RankTraceMult
open scoped ComplexOrder

namespace Zeta23Ext.StableRankTrace

/-! ### The scalar profile `Psi` -/

/-- Ainta's spectral-defect profile: `Psi t = (t−1)²` for `t ≤ 2`, `2t − 3` beyond. -/
def Psi (t : ℝ) : ℝ := if t ≤ 2 then (t - 1) ^ 2 else 2 * t - 3

/-- **The identification.**  `Psi` is upstream's `gc 2` shifted by `Psi 0 = 1`. -/
lemma Psi_eq_gc_two_add_one (t : ℝ) : Psi t = gc 2 t + 1 := by
  unfold Psi
  split_ifs with h
  · rw [gc_of_le h]; ring
  · rw [gc_of_ge (le_of_lt (not_le.mp h))]; ring

@[simp] lemma Psi_zero : Psi 0 = 1 := by norm_num [Psi]

lemma Psi_nonneg (t : ℝ) : 0 ≤ Psi t := by
  unfold Psi
  split_ifs with h
  · positivity
  · have : (2 : ℝ) < t := not_le.mp h
    linarith

/-- The sharpened termwise estimate, in Ainta's own form: for `p, ν ≥ 0`,
`(p − ν)² + 4ν ≥ 2p − 1 + Psi p`.  This is upstream's `sq_sub_ge_gc` at `c = 2`. -/
lemma two_mul_sub_one_add_Psi_le {p nu : ℝ} (hp : 0 ≤ p) (hnu : 0 ≤ nu) :
    2 * p - 1 + Psi p ≤ (p - nu) ^ 2 + 4 * nu := by
  have h := sq_sub_ge_gc (c := 2) hp hnu (by norm_num)
  rw [Psi_eq_gc_two_add_one]
  linarith

/-- … and the estimate is exact: the minimum over `ν ≥ 0` is attained at `ν = (p − 2)⁺`,
so `Psi p = min_{ν ≥ 0} ((p − ν)² + 4ν) − 2p + 1`.  (This is the one-variable calculus
fact the trust map names; it is recorded because the sharpness is the whole point of the
defect term, and an inequality with no attainment claim would not pin it.) -/
lemma Psi_attained (p : ℝ) :
    (p - max (p - 2) 0) ^ 2 + 4 * max (p - 2) 0 = 2 * p - 1 + Psi p := by
  unfold Psi
  rcases le_or_gt p 2 with h | h
  · rw [max_eq_right (by linarith), if_pos h]; ring
  · rw [max_eq_left (by linarith), if_neg (not_le.mpr h)]; ring

/-! ### The eigenbasis presentation of a PSD matrix -/

section Eigen

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The eigenvector columns of a Hermitian matrix, in the `Wmat`/`Pmat` column indexing. -/
def eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) : n → n → 𝕜 :=
  fun j a => (hP.1.eigenvectorUnitary : Matrix n n 𝕜) a j

lemma wmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Wmat hP.1.eigenvalues (eigCols hP)
      = (hP.1.eigenvectorUnitary : Matrix n n 𝕜)
        * diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
  ext a j
  simp only [Wmat, eigCols, Matrix.mul_diagonal]
  ring

/-- **`P` is `Pmat` of its own spectral data.**  This is the presentation at which the
Schur–Jensen step of `rank_trace_mult` is an equality, so it is the one that exposes the
full spectral defect rather than its diagonal shadow. -/
lemma pmat_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) :
    Pmat hP.1.eigenvalues (eigCols hP) = P := by
  have hdd : (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)
        * ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜))
      = RCLike.ofReal ∘ hP.1.eigenvalues := by
    funext j
    simp only [Function.comp_apply, ← RCLike.ofReal_mul]
    rw [Real.mul_self_sqrt (hP.eigenvalues_nonneg j)]
  have hstar : (diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)))ᴴ
      = diagonal (fun j => ((Real.sqrt (hP.1.eigenvalues j) : ℝ) : 𝕜)) := by
    rw [diagonal_conjTranspose]
    simp [RCLike.star_def]
  unfold Pmat
  rw [wmat_eigCols hP, conjTranspose_mul, hstar, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ (diagonal _) (diagonal _), diagonal_mul_diagonal, hdd]
  conv_rhs => rw [hP.1.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rfl

/-- The eigenvector columns are unit vectors, so the `Pmat` weight `m j * x_j` is `λ j`. -/
lemma xsq_eigCols {P : Matrix n n 𝕜} (hP : P.PosSemidef) (j : n) :
    xsq (eigCols hP) j = 1 := by
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary (hP.1.eigenvectorUnitary).2
  rw [mem_doublyStochastic_iff_sum] at hDS
  simpa [xsq, eigCols, normSqMatrix] using hDS.2.2 j

end Eigen

/-! ### The theorem -/

section Main

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n]
  [Fintype r] [DecidableEq r]

/-- `tr(V Vᴴ)` is the total squared column mass of `V`. -/
lemma rtrace_self_mul_conjTranspose (V : Matrix n r 𝕜) :
    rtrace (V * Vᴴ) = ∑ j, ∑ i, ‖V i j‖ ^ 2 := by
  unfold rtrace
  rw [trace_mul_comm, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_mul]
  simp

/-- The `Psi`-trace on the Gram side, in terms of upstream's `gc 2` on the `V Vᴴ` side. -/
lemma rtrace_specMap_Psi (V : Matrix n r 𝕜) :
    rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      = (∑ i, gc 2 ((Matrix.posSemidef_self_mul_conjTranspose V).1.eigenvalues i))
        + (Fintype.card r : ℝ) := by
  rw [rtrace_specMap]
  have hshift : ∀ x : ℝ, Psi x = gc 2 x + 1 := Psi_eq_gc_two_add_one
  simp only [hshift]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ]
  congr 1
  exact (sum_eigenvalues_comm V (gc 2) (gc_zero (by norm_num))).symm

/-- **Stability-enhanced rank–trace inequality, sharp form.**  No hypothesis on the
columns of `V`.  Strengthens `RHLinalg.rank_trace_ineq` at `c = 2` by the spectral defect
`tr Psi(VᴴV) − card r`, which by `rtrace_specMap_Psi` is `∑ᵢ gc 2 (λᵢ(V Vᴴ))`. -/
theorem stable_rank_trace_sharp (V : Matrix n r 𝕜)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  classical
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hm : ∀ j, 0 ≤ hP.1.eigenvalues j := fun j => hP.eigenvalues_nonneg j
  have hR := rank_trace_mult hm (eigCols hP) hQ hb (c := 2) (by norm_num)
  rw [pmat_eigCols hP] at hR
  have hx : ∀ j, hP.1.eigenvalues j * xsq (eigCols hP) j = hP.1.eigenvalues j := by
    intro j; rw [xsq_eigCols hP j, mul_one]
  simp only [hx] at hR
  rw [rtrace_specMap_Psi V]
  have hcast : ((2 : ℝ) ^ 2) * (b : ℝ) = 4 * b := by norm_num
  linarith [hR]

/-- **Stability-enhanced rank–trace inequality** (the trust map's statement, S2).
Strengthens `RHLinalg.rank_trace_ineq_two` by the spectral defect `tr Psi(VᴴV)`.

The column bound `hV` is used for exactly one thing: `tr(V Vᴴ) ≤ card r`, which is what
turns the sharp form's `2·tr(V Vᴴ) − card r` into `4·tr(V Vᴴ) − 3·card r`. -/
theorem stable_rank_trace (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
        + rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi)
      ≤ frobSq (V * Vᴴ + Q) := by
  have hsharp := stable_rank_trace_sharp V hQ hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

/-! ### Non-vacuity: the `Psi = 0` collapse -/

/-- The `Psi := 0` shadow of `stable_rank_trace`, proved **independently** from the
existing `RHLinalg.rank_trace_ineq_two`.  This is the trust map's built-in test: the
enhanced statement must reduce to the existing theorem when the defect is dropped. -/
theorem stable_rank_trace_no_defect (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have hP : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hr : (V * Vᴴ).rank ≤ Fintype.card r := by
    rw [Matrix.rank_self_mul_conjTranspose]
    exact Matrix.rank_le_card_width V
  have h := rank_trace_ineq_two hP hQ hr hb
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

/-- … and `stable_rank_trace` implies it, because the defect is nonnegative.  Together
with `stable_rank_trace_no_defect` this is the statement-level check that S2 is a
strengthening of `rank_trace_ineq_two` and not a different inequality. -/
theorem stable_rank_trace_collapse (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) {b : ℕ} (hb : posIndex hQ ≤ b) :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ) - 4 * b
      ≤ frobSq (V * Vᴴ + Q) := by
  have h := stable_rank_trace V hV hQ hb
  have hpos : 0 ≤ rtrace (specMap (isHermitian_conjTranspose_mul_self V) Psi) := by
    rw [rtrace_specMap]
    exact Finset.sum_nonneg fun j _ => Psi_nonneg _
  linarith

/-- The sharp form is strictly stronger than the trust map's form: their difference is
`2·(card r − tr(V Vᴴ)) ≥ 0`, and that gap is the whole content of `hV` here. -/
theorem sharp_le_stable (V : Matrix n r 𝕜) (hV : ∀ j, ∑ i, ‖V i j‖ ^ 2 ≤ 1)
    {Q : Matrix n n 𝕜} :
    4 * rtrace (V * Vᴴ + Q) - 3 * (Fintype.card r : ℝ)
      ≤ 2 * rtrace (V * Vᴴ) + 4 * rtrace Q - (Fintype.card r : ℝ) := by
  have hle : rtrace (V * Vᴴ) ≤ (Fintype.card r : ℝ) := by
    rw [rtrace_self_mul_conjTranspose V]
    calc ∑ j, ∑ i, ‖V i j‖ ^ 2 ≤ ∑ _j : r, (1 : ℝ) := Finset.sum_le_sum fun j _ => hV j
      _ = (Fintype.card r : ℝ) := by simp
  rw [rtrace_add]
  linarith

end Main

/-! ### Standing axiom audit

Same idiom as `Zeta23Ext/TruncEst/Axioms.lean`: the audit runs on every `lake build`
rather than living in a document that can drift from the tree. Anything other than
`propext`, `Classical.choice`, `Quot.sound` is a defect. -/

#print axioms Psi_eq_gc_two_add_one
#print axioms Psi_attained
#print axioms two_mul_sub_one_add_Psi_le
#print axioms pmat_eigCols
#print axioms xsq_eigCols
#print axioms rtrace_specMap_Psi
#print axioms stable_rank_trace_sharp
#print axioms stable_rank_trace
#print axioms stable_rank_trace_no_defect
#print axioms stable_rank_trace_collapse
#print axioms sharp_le_stable

end Zeta23Ext.StableRankTrace
