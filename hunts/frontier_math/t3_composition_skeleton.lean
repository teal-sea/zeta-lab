import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CompositionSkeleton

open scoped Matrix

/-- The squared Frobenius norm of a real matrix: the sum of the squares of its entries. -/
def fro2 {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := ∑ a, ∑ b, (M a b) ^ 2

/-- The Euclidean inner product of the `i`-th and `j`-th vector of a family `u`. -/
def ip {s d : ℕ} (u : Fin s → Fin d → ℝ) (i j : Fin s) : ℝ := ∑ k, u i k * u j k

/-- `gram m u = ∑ i, m i • (u i) (u i)ᵀ`. -/
def gram {s d : ℕ} (m : Fin s → ℕ) (u : Fin s → Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => ∑ i, (m i : ℝ) * u i a * u i b

/-- `R = ∑_{i ≠ j} m i * m j * ⟪u i, u j⟫ ^ 2`. -/
def offDiagSum {s d : ℕ} (m : Fin s → ℕ) (u : Fin s → Fin d → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, (m i : ℝ) * (m j : ℝ) * (ip u i j) ^ 2

/-- Auxiliary: a fourfold sum may be reordered, moving the outer pair of indices inside. -/
lemma sum_comm4 {A B : Type*} [Fintype A] [Fintype B] (F : A → A → B → B → ℝ) :
    ∑ a, ∑ b, ∑ i, ∑ j, F a b i j = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, F a b i j
      = ∑ a, ∑ i, ∑ j, ∑ b, F a b i j := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- For a symmetric matrix `Q`, `trace (P * Q)` is the entrywise inner product of `P` and `Q`. -/
lemma trace_mul_of_symm {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ = Q) :
    Matrix.trace (P * Q) = ∑ a, ∑ b, P a b * Q a b := by
  have hQs : ∀ a b, Q b a = Q a b := fun a b => congrArg (fun M => M a b) hQ
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hQs]

/-- `‖P + Q‖_F ^ 2 = ‖P‖_F ^ 2 + 2 * trace (P * Q) + ‖Q‖_F ^ 2` for symmetric `Q`. -/
lemma fro2_add {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Qᵀ = Q) :
    fro2 (P + Q) = fro2 P + 2 * Matrix.trace (P * Q) + fro2 Q := by
  rw [trace_mul_of_symm P Q hQ]
  simp only [fro2, Matrix.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum,
    mul_assoc]

/-- The squared Frobenius norm of `P = ∑ i, m i • u i u iᵀ` is the double sum
`∑ i, ∑ j, m i * m j * ⟪u i, u j⟫ ^ 2`. -/
lemma fro2_gram {s d : ℕ} (m : Fin s → ℕ) (u : Fin s → Fin d → ℝ) :
    fro2 (gram m u) = ∑ i, ∑ j, (m i : ℝ) * (m j : ℝ) * (ip u i j) ^ 2 := by
  have h1 : fro2 (gram m u)
      = ∑ a, ∑ b, ∑ i, ∑ j, ((m i : ℝ) * u i a * u i b) * ((m j : ℝ) * u j a * u j b) := by
    simp only [fro2, gram, Matrix.of_apply, sq, Finset.sum_mul_sum]
  have h2 : ∀ i j : Fin s, (m i : ℝ) * (m j : ℝ) * (ip u i j) ^ 2
      = ∑ a, ∑ b, ((m i : ℝ) * u i a * u i b) * ((m j : ℝ) * u j a * u j b) := by
    intro i j
    have h : (ip u i j) ^ 2 = ∑ a, ∑ b, (u i a * u j a) * (u i b * u j b) := by
      simp only [ip, sq, Finset.sum_mul_sum]
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, sum_comm4]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (h2 i j).symm

/-- Splitting off the diagonal: for unit vectors `u i`,
`‖P‖_F ^ 2 = ∑ i, (m i) ^ 2 + R`. -/
lemma fro2_gram_split {s d : ℕ} (m : Fin s → ℕ) (u : Fin s → Fin d → ℝ)
    (hu : ∀ i, ip u i i = 1) :
    fro2 (gram m u) = (∑ i, (m i : ℝ) ^ 2) + offDiagSum m u := by
  rw [fro2_gram, offDiagSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hu i]
  ring

/-- Each positive integer `m` satisfies `2 * m - m ^ 2 ≤ 1`. -/
lemma two_mul_sub_sq_le_one {k : ℕ} (hk : 0 < k) : 2 * (k : ℝ) - (k : ℝ) ^ 2 ≤ 1 := by
  have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ) - 1)]

/-- **Result 1 (exact composition skeleton).**
Let `u 1, …, u s` be unit vectors in `ℝ ^ d`, let `m 1, …, m s` be positive integers with
`N = ∑ i, m i`, let `P = ∑ i, m i • u i u iᵀ`, and let `Q` be a symmetric matrix.
With `R = ∑_{i ≠ j} m i * m j * ⟪u i, u j⟫ ^ 2` and
`D = R + 2 * trace (P * Q) + ‖Q‖_F ^ 2` one has
`s ≥ 2 * N - ‖P + Q‖_F ^ 2 + D`.
(The hypotheses `1 ≤ s` and `1 ≤ d` are part of the stated setting; the proof does not
need them.) -/
theorem result1_exact_skeleton {s d : ℕ} (hs : 1 ≤ s) (hd : 1 ≤ d)
    (u : Fin s → Fin d → ℝ) (hu : ∀ i, ip u i i = 1)
    (m : Fin s → ℕ) (hm : ∀ i, 0 < m i)
    (P Q : Matrix (Fin d) (Fin d) ℝ) (hP : P = gram m u) (hQ : Qᵀ = Q)
    (N Rv D : ℝ) (hN : N = ∑ i, (m i : ℝ)) (hR : Rv = offDiagSum m u)
    (hD : D = Rv + 2 * Matrix.trace (P * Q) + fro2 Q) :
    (s : ℝ) ≥ 2 * N - fro2 (P + Q) + D := by
  have hsplit : fro2 P = (∑ i, (m i : ℝ) ^ 2) + Rv := by
    rw [hP, hR, fro2_gram_split m u hu]
  have hexp : fro2 (P + Q) = fro2 P + 2 * Matrix.trace (P * Q) + fro2 Q := fro2_add P Q hQ
  have hkey : 2 * N - fro2 (P + Q) + D = ∑ i, (2 * (m i : ℝ) - (m i : ℝ) ^ 2) := by
    rw [hexp, hsplit, hD, hN, Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  have hbound : ∑ i, (2 * (m i : ℝ) - (m i : ℝ) ^ 2) ≤ ∑ _i : Fin s, (1 : ℝ) :=
    Finset.sum_le_sum fun i _ => two_mul_sub_sq_le_one (hm i)
  have hcard : ∑ _i : Fin s, (1 : ℝ) = (s : ℝ) := by simp
  rw [ge_iff_le, hkey]
  linarith [hbound, hcard.le, hcard.ge]

/-- **Result 2 (conditional composition).** If moreover `‖P + Q‖_F ^ 2 ≤ C * N` and
`D ≥ theta * R0`, then `s ≥ (2 - C) * N + theta * R0`. -/
theorem result2_conditional {s d : ℕ} (hs : 1 ≤ s) (hd : 1 ≤ d)
    (u : Fin s → Fin d → ℝ) (hu : ∀ i, ip u i i = 1)
    (m : Fin s → ℕ) (hm : ∀ i, 0 < m i)
    (P Q : Matrix (Fin d) (Fin d) ℝ) (hP : P = gram m u) (hQ : Qᵀ = Q)
    (N Rv D : ℝ) (hN : N = ∑ i, (m i : ℝ)) (hR : Rv = offDiagSum m u)
    (hD : D = Rv + 2 * Matrix.trace (P * Q) + fro2 Q)
    (C theta R0 : ℝ) (hC : fro2 (P + Q) ≤ C * N) (hDR : D ≥ theta * R0) :
    (s : ℝ) ≥ (2 - C) * N + theta * R0 := by
  have h := result1_exact_skeleton hs hd u hu m hm P Q hP hQ N Rv D hN hR hD
  have hCN : (2 - C) * N = 2 * N - C * N := by ring
  rw [ge_iff_le, hCN]
  linarith

/-- Sanity check: the hypotheses of the two results are satisfiable, so the statements are
not vacuous. Here `s = d = 1`, `u 0 = (1)`, `m 0 = 1`, `Q = 0`. -/
example : ∃ (u : Fin 1 → Fin 1 → ℝ) (m : Fin 1 → ℕ) (P Q : Matrix (Fin 1) (Fin 1) ℝ),
    (∀ i, ip u i i = 1) ∧ (∀ i, 0 < m i) ∧ P = gram m u ∧ Qᵀ = Q := by
  refine ⟨fun _ _ => 1, fun _ => 1, gram (fun _ => 1) (fun _ _ => 1), 0, ?_, ?_, rfl, ?_⟩
  · intro i; simp [ip]
  · intro i; norm_num
  · simp

end CompositionSkeleton

#print axioms CompositionSkeleton.result1_exact_skeleton
#print axioms CompositionSkeleton.result2_conditional
