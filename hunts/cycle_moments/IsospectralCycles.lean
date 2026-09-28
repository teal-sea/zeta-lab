/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Equal power traces do not determine the distinct fourth cycle

The columns of `squareFrame c s` are two orthonormal pairs whenever
`c^2+s^2=1`. Their unit Gram matrix satisfies `K^2=2K`, which determines every
positive power trace independently of the chosen pair `(c,s)`.

The pairwise-distinct-index fourth cycle is evaluated directly from its finite
sum. The two rational frames below have unequal values despite equality of all
power traces. No fourth-cycle identity is assumed as a hypothesis.

This is a complete finite example. No claim of novelty or zeta asymptotic
improvement is made by these declarations.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open Matrix Finset
open scoped BigOperators

namespace CycleMoments

def squareFrame (c s : ℝ) : Matrix (Fin 2) (Fin 4) ℝ :=
  !![1, 0, c, -s; 0, 1, s, c]

def squareFrameGram (c s : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, c, -s; 0, 1, s, c; c, s, 1, 0; -s, c, 0, 1]

@[simp] private theorem gram_entry_00 (c s : ℝ) : squareFrameGram c s 0 0 = 1 := rfl
@[simp] private theorem gram_entry_01 (c s : ℝ) : squareFrameGram c s 0 1 = 0 := rfl
@[simp] private theorem fin4_ne_01 : (0 : Fin 4) ≠ 1 := by decide
@[simp] private theorem gram_entry_02 (c s : ℝ) : squareFrameGram c s 0 2 = c := rfl
@[simp] private theorem fin4_ne_02 : (0 : Fin 4) ≠ 2 := by decide
@[simp] private theorem gram_entry_03 (c s : ℝ) : squareFrameGram c s 0 3 = -s := rfl
@[simp] private theorem fin4_ne_03 : (0 : Fin 4) ≠ 3 := by decide
@[simp] private theorem gram_entry_10 (c s : ℝ) : squareFrameGram c s 1 0 = 0 := rfl
@[simp] private theorem fin4_ne_10 : (1 : Fin 4) ≠ 0 := by decide
@[simp] private theorem gram_entry_11 (c s : ℝ) : squareFrameGram c s 1 1 = 1 := rfl
@[simp] private theorem gram_entry_12 (c s : ℝ) : squareFrameGram c s 1 2 = s := rfl
@[simp] private theorem fin4_ne_12 : (1 : Fin 4) ≠ 2 := by decide
@[simp] private theorem gram_entry_13 (c s : ℝ) : squareFrameGram c s 1 3 = c := rfl
@[simp] private theorem fin4_ne_13 : (1 : Fin 4) ≠ 3 := by decide
@[simp] private theorem gram_entry_20 (c s : ℝ) : squareFrameGram c s 2 0 = c := rfl
@[simp] private theorem fin4_ne_20 : (2 : Fin 4) ≠ 0 := by decide
@[simp] private theorem gram_entry_21 (c s : ℝ) : squareFrameGram c s 2 1 = s := rfl
@[simp] private theorem fin4_ne_21 : (2 : Fin 4) ≠ 1 := by decide
@[simp] private theorem gram_entry_22 (c s : ℝ) : squareFrameGram c s 2 2 = 1 := rfl
@[simp] private theorem gram_entry_23 (c s : ℝ) : squareFrameGram c s 2 3 = 0 := rfl
@[simp] private theorem fin4_ne_23 : (2 : Fin 4) ≠ 3 := by decide
@[simp] private theorem gram_entry_30 (c s : ℝ) : squareFrameGram c s 3 0 = -s := rfl
@[simp] private theorem fin4_ne_30 : (3 : Fin 4) ≠ 0 := by decide
@[simp] private theorem gram_entry_31 (c s : ℝ) : squareFrameGram c s 3 1 = c := rfl
@[simp] private theorem fin4_ne_31 : (3 : Fin 4) ≠ 1 := by decide
@[simp] private theorem gram_entry_32 (c s : ℝ) : squareFrameGram c s 3 2 = 0 := rfl
@[simp] private theorem fin4_ne_32 : (3 : Fin 4) ≠ 2 := by decide
@[simp] private theorem gram_entry_33 (c s : ℝ) : squareFrameGram c s 3 3 = 1 := rfl

/-- Direct pairwise-distinct-index fourth cycle. -/
def distinctFourth (K : Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l,
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l
    then K i j * K j k * K k l * K l i else 0

theorem squareFrame_gram (c s : ℝ) (h : c^2+s^2=1) :
    (squareFrame c s)ᵀ * squareFrame c s = squareFrameGram c s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [squareFrame, squareFrameGram, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals nlinarith

theorem squareFrame_unit_columns (c s : ℝ) (h : c^2+s^2=1) (j : Fin 4) :
    (∑ i : Fin 2, (squareFrame c s i j)^2) = 1 := by
  fin_cases j <;> norm_num [squareFrame, Fin.sum_univ_succ]
  all_goals nlinarith

theorem squareFrameGram_square (c s : ℝ) (h : c^2+s^2=1) :
    (squareFrameGram c s)^2 = (2 : ℝ) • squareFrameGram c s := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, squareFrameGram, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals nlinarith

@[simp] theorem squareFrameGram_trace (c s : ℝ) :
    Matrix.trace (squareFrameGram c s) = 4 := by
  norm_num [Matrix.trace, Fin.sum_univ_four]

theorem power_of_square_eq_two_smul {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (hK : K^2 = (2 : ℝ) • K) (m : ℕ) :
    K^(m+1) = (2 : ℝ)^m • K := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Matrix.smul_mul, ← pow_two, hK, smul_smul, pow_succ]

theorem squareFrameGram_power_trace (c s : ℝ) (h : c^2+s^2=1) (m : ℕ) :
    Matrix.trace ((squareFrameGram c s)^(m+1)) = (2 : ℝ)^(m+2) := by
  rw [power_of_square_eq_two_smul _ (squareFrameGram_square c s h), Matrix.trace_smul,
    squareFrameGram_trace]
  simp only [smul_eq_mul]
  rw [pow_add]
  norm_num

/-- All 256 ordered tuples are evaluated; only pairwise-distinct tuples survive. -/
theorem squareFrameGram_distinctFourth (c s : ℝ) :
    distinctFourth (squareFrameGram c s) = -8*c^2*s^2 := by
  norm_num [distinctFourth, Fin.sum_univ_four]
  ring

def gramThreeFive : Matrix (Fin 4) (Fin 4) ℝ := squareFrameGram (3/5) (4/5)
def gramFiveThirteen : Matrix (Fin 4) (Fin 4) ℝ := squareFrameGram (5/13) (12/13)

theorem concrete_grams_have_unit_frames :
    ((squareFrame (3/5) (4/5))ᵀ * squareFrame (3/5) (4/5) = gramThreeFive) ∧
    ((squareFrame (5/13) (12/13))ᵀ * squareFrame (5/13) (12/13) = gramFiveThirteen) ∧
    (∀ j, (∑ i : Fin 2, (squareFrame (3/5) (4/5) i j)^2) = 1) ∧
    (∀ j, (∑ i : Fin 2, (squareFrame (5/13) (12/13) i j)^2) = 1) := by
  refine ⟨squareFrame_gram _ _ (by norm_num), squareFrame_gram _ _ (by norm_num), ?_, ?_⟩
  · exact squareFrame_unit_columns _ _ (by norm_num)
  · exact squareFrame_unit_columns _ _ (by norm_num)

theorem concrete_all_power_traces_equal (m : ℕ) :
    Matrix.trace (gramThreeFive^m) = Matrix.trace (gramFiveThirteen^m) := by
  cases m with
  | zero => rfl
  | succ m =>
    exact (squareFrameGram_power_trace (3/5) (4/5) (by norm_num) m).trans
      (squareFrameGram_power_trace (5/13) (12/13) (by norm_num) m).symm

theorem concrete_distinctFourth_values :
    distinctFourth gramThreeFive = -1152/625 ∧
    distinctFourth gramFiveThirteen = -28800/28561 := by
  constructor
  · change distinctFourth (squareFrameGram (3/5) (4/5)) = -1152/625
    rw [squareFrameGram_distinctFourth]
    norm_num
  · change distinctFourth (squareFrameGram (5/13) (12/13)) = -28800/28561
    rw [squareFrameGram_distinctFourth]
    norm_num

theorem concrete_distinctFourth_unequal :
    distinctFourth gramThreeFive ≠ distinctFourth gramFiveThirteen := by
  rw [concrete_distinctFourth_values.1, concrete_distinctFourth_values.2]
  norm_num

/-- Equal power traces of every order do not determine the distinct fourth cycle. -/
theorem all_power_traces_do_not_determine_distinctFourth :
    (∀ m : ℕ, Matrix.trace (gramThreeFive^m) = Matrix.trace (gramFiveThirteen^m)) ∧
    distinctFourth gramThreeFive ≠ distinctFourth gramFiveThirteen :=
  ⟨concrete_all_power_traces_equal, concrete_distinctFourth_unequal⟩

/-- info: 'CycleMoments.squareFrame_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squareFrame_gram
/-- info: 'CycleMoments.squareFrame_unit_columns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squareFrame_unit_columns
/-- info: 'CycleMoments.squareFrameGram_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squareFrameGram_square
/-- info: 'CycleMoments.squareFrameGram_power_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squareFrameGram_power_trace
/-- info: 'CycleMoments.squareFrameGram_distinctFourth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms squareFrameGram_distinctFourth
/-- info: 'CycleMoments.concrete_grams_have_unit_frames' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concrete_grams_have_unit_frames
/-- info: 'CycleMoments.all_power_traces_do_not_determine_distinctFourth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms all_power_traces_do_not_determine_distinctFourth

end CycleMoments
