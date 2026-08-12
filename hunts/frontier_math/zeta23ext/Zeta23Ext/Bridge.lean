import Mathlib

open scoped BigOperators Matrix
open Finset

namespace Bridge

variable {n ι 𝕜 : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
variable [RCLike 𝕜]

-- (`Real.sqrt` has no executable code, so the definitions below are noncomputable;
-- the definitions themselves are reproduced verbatim.)
noncomputable section

/-- Real part of the trace (source: `Zeta23/LinAlg/PosIndex.lean`). -/
def rtrace (A : Matrix n n 𝕜) : ℝ := RCLike.re A.trace

/-- Squared Frobenius norm (source: `Zeta23/LinAlg/PosIndex.lean`). -/
def frobSq (A : Matrix n n 𝕜) : ℝ := RCLike.re (Aᴴ * A).trace

/-- the d×s matrix with columns √m_j · v_j (source: `RankTraceMult.lean`). -/
def Wmat (m : ι → ℝ) (v : ι → n → 𝕜) : Matrix n ι 𝕜 :=
  fun a j => (Real.sqrt (m j) : 𝕜) * v j a

/-- P := W Wᴴ = Σ_j m_j v_j v_j* (source: `RankTraceMult.lean`). -/
def Pmat (m : ι → ℝ) (v : ι → n → 𝕜) : Matrix n n 𝕜 := Wmat m v * (Wmat m v)ᴴ

/-- ‖v_j‖² (source: `RankTraceMult.lean`, `xsq`). -/
def xsq (v : ι → n → 𝕜) (j : ι) : ℝ := ∑ a, ‖v j a‖ ^ 2

/-- The Gram inner product ⟪v i, v j⟫ used below. -/
def ipC (v : ι → n → 𝕜) (i j : ι) : 𝕜 := ∑ a, (starRingEnd 𝕜) (v i a) * v j a

/-- The off-diagonal Gram mass `R = Σ_{i ≠ j} m_i m_j ‖⟪v_i,v_j⟫‖²`. -/
def offDiagSum (m : ι → ℝ) (v : ι → n → 𝕜) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, m i * m j * ‖ipC v i j‖ ^ 2

/-! ### Auxiliary lemmas -/

omit [Fintype n] [DecidableEq n] [DecidableEq ι] in
/-- Entrywise formula for `P = W Wᴴ`. -/
private lemma Pmat_apply (m : ι → ℝ) (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) (a b : n) :
    Pmat m v a b = ∑ i, ((m i : ℝ) : 𝕜) * (v i a * (starRingEnd 𝕜) (v i b)) := by
  simp only [Pmat, Wmat, Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
    map_mul, RCLike.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ((Real.sqrt (m i) : ℝ) : 𝕜) * ((Real.sqrt (m i) : ℝ) : 𝕜) = ((m i : ℝ) : 𝕜) := by
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (hm i)]
  linear_combination (v i a * (starRingEnd 𝕜) (v i b)) * h

omit [DecidableEq n] in
private lemma trace_conjTranspose_mul_self (A : Matrix n n 𝕜) :
    (Aᴴ * A).trace = ∑ b, ∑ a, (starRingEnd 𝕜) (A a b) * A a b := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]

private lemma sum4_swap {A B C D M : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [AddCommMonoid M] (f : A → B → C → D → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  rw [show (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ p : A × B, ∑ q : C × D, f p.1 p.2 q.1 q.2 from by
      simp [Fintype.sum_prod_type],
    show (∑ c, ∑ d, ∑ a, ∑ b, f a b c d) = ∑ q : C × D, ∑ p : A × B, f p.1 p.2 q.1 q.2 from by
      simp [Fintype.sum_prod_type]]
  exact Finset.sum_comm

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
private lemma ipC_self (v : ι → n → 𝕜) (j : ι) : ipC v j j = ((xsq v j : ℝ) : 𝕜) := by
  simp only [ipC, xsq, RCLike.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [RCLike.conj_mul, RCLike.ofReal_pow]

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
private lemma xsq_nonneg (v : ι → n → 𝕜) (j : ι) : 0 ≤ xsq v j :=
  Finset.sum_nonneg fun a _ => by positivity

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
private lemma norm_ipC_self (v : ι → n → 𝕜) (j : ι) : ‖ipC v j j‖ = xsq v j := by
  rw [ipC_self, RCLike.norm_ofReal, abs_of_nonneg (xsq_nonneg v j)]

/-- **(1) The Hermitian expansion.**  For Hermitian `P` and `Q`,
`‖P+Q‖²_F = ‖P‖²_F + 2·Re tr(P Q) + ‖Q‖²_F`. -/
theorem frobSq_add_of_isHermitian {P Q : Matrix n n 𝕜}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    frobSq (P + Q) = frobSq P + 2 * rtrace (P * Q) + frobSq Q := by
  simp only [frobSq, rtrace]
  rw [Matrix.conjTranspose_add, hP.eq, hQ.eq]
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_mul_comm Q P]
  simp only [map_add]
  ring

/-- **(2) The Gram identity.**  `‖P‖²_F = Σ_i Σ_j m_i m_j ‖⟪v_i,v_j⟫‖²`. -/
theorem frobSq_Pmat (m : ι → ℝ) (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜) :
    frobSq (Pmat m v) = ∑ i, ∑ j, m i * m j * ‖ipC v i j‖ ^ 2 := by
  have step1 : ((Pmat m v)ᴴ * Pmat m v).trace
      = ∑ b, ∑ a, ∑ i, ∑ j, ((m i : ℝ) : 𝕜) * ((m j : ℝ) : 𝕜) *
          (v i a * (starRingEnd 𝕜) (v i b) * ((starRingEnd 𝕜) (v j a) * v j b)) := by
    rw [trace_conjTranspose_mul_self]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Pmat_apply m hm v a b]
    simp only [map_sum, map_mul, RCLike.conj_ofReal, RCLike.conj_conj, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have step2 : ((∑ i, ∑ j, m i * m j * ‖ipC v i j‖ ^ 2 : ℝ) : 𝕜)
      = ∑ i, ∑ j, ∑ a, ∑ b, ((m i : ℝ) : 𝕜) * ((m j : ℝ) : 𝕜) *
          (v i a * (starRingEnd 𝕜) (v i b) * ((starRingEnd 𝕜) (v j a) * v j b)) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h : ((‖ipC v i j‖ : ℝ) : 𝕜) ^ 2 = (starRingEnd 𝕜) (ipC v i j) * ipC v i j :=
      (RCLike.conj_mul _).symm
    rw [h]
    simp only [ipC, map_sum, map_mul, RCLike.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have step3 : ((Pmat m v)ᴴ * Pmat m v).trace
      = ((∑ i, ∑ j, m i * m j * ‖ipC v i j‖ ^ 2 : ℝ) : 𝕜) := by
    rw [step1, step2, sum4_swap]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
  rw [frobSq, step3, RCLike.ofReal_re]

/-- The Gram identity split on the diagonal: with unit vectors the diagonal contributes
`∑ j, m j ^ 2`. -/
private lemma frobSq_Pmat_split (m : ι → ℝ) (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    (hunit : ∀ j, xsq v j = 1) :
    frobSq (Pmat m v) = (∑ j, (m j) ^ 2) + offDiagSum m v := by
  rw [frobSq_Pmat m hm v, offDiagSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), norm_ipC_self, hunit i]
  ring

/-- **(3) The bridge.**  With unit evaluation vectors, the quantity
`D := ‖P+Q‖²_F − Σ_j m_j²` decomposes as `R + 2·Re tr(P Q) + ‖Q‖²_F`.
This is the identity that lets a composition keeping the cross term be
compared against a pipeline that only ever forms `tr Q`. -/
theorem bridge_D_eq (m : ι → ℝ) (hm : ∀ j, 0 ≤ m j) (v : ι → n → 𝕜)
    (hunit : ∀ j, xsq v j = 1) {Q : Matrix n n 𝕜} (hQ : Q.IsHermitian) :
    frobSq (Pmat m v + Q) - ∑ j, (m j) ^ 2
      = offDiagSum m v + 2 * rtrace (Pmat m v * Q) + frobSq Q := by
  have hP : (Pmat m v).IsHermitian := Matrix.isHermitian_mul_conjTranspose_self (Wmat m v)
  rw [frobSq_add_of_isHermitian hP hQ, frobSq_Pmat_split m hm v hunit]
  ring

end

end Bridge

#print axioms Bridge.frobSq_add_of_isHermitian
#print axioms Bridge.frobSq_Pmat
#print axioms Bridge.bridge_D_eq
