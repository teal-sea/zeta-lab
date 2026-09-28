import Mathlib

/-!
# A fixed-kernel counting distinction invisible to all spectral moments

The two integer-label multisets use the same explicitly defined rational
integer kernel. `kernel_values_one` and `kernel_values_two` check every entry.
`simpleCount` computes multiplicities from the labels and excludes every index
whose label occurs more than once.

Complementary idempotents prove equality of every power trace, while the simple
counts and entrywise fourth-power sums differ. The row-energy sums are computed
too. These are exact finite statements over the rationals.

The analytic identification of `integerKernel` as the integer Fourier samples
of the positive trigonometric density belongs to the accompanying ordinary
proof. It is not assumed or formalized in this file.
-/

open Matrix Finset
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace CycleMoments.CountingOverlap

def labelsOne : Fin 5 → ℤ := ![0,0,0,3,6]
def labelsTwo : Fin 5 → ℤ := ![0,0,1,1,4]

def integerKernel (d : ℤ) : ℚ :=
  if d = 0 then 1 else if d.natAbs = 1 then 1/2 else if d.natAbs = 2 then 1/8 else 0

def KOne : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1,1,1,0,0; 1,1,1,0,0; 1,1,1,0,0; 0,0,0,1,0; 0,0,0,0,1]
def KTwo : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1,1,1/2,1/2,0; 1,1,1/2,1/2,0; 1/2,1/2,1,1,0; 1/2,1/2,1,1,0; 0,0,0,0,1]

def simpleCount (z : Fin 5 → ℤ) : ℕ :=
  (Finset.univ.filter (fun i => (Finset.univ.filter (fun j => z j = z i)).card = 1)).card

def entryFourth (K : Matrix (Fin 5) (Fin 5) ℚ) : ℚ := ∑ i, ∑ j, (K i j)^4

def squaredRowEnergy (K : Matrix (Fin 5) (Fin 5) ℚ) : ℚ :=
  ∑ i, (∑ j, (K i j)^2)^2

private def POne : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3,1/3,1/3,0,0; 1/3,1/3,1/3,0,0; 1/3,1/3,1/3,0,0;
     0,0,0,0,0; 0,0,0,0,0]
private def QOne : Matrix (Fin 5) (Fin 5) ℚ :=
  !![0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0; 0,0,0,1,0; 0,0,0,0,1]
private def PTwo : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/4,1/4,1/4,1/4,0; 1/4,1/4,1/4,1/4,0;
     1/4,1/4,1/4,1/4,0; 1/4,1/4,1/4,1/4,0; 0,0,0,0,0]
private def QTwo : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/4,1/4,-1/4,-1/4,0; 1/4,1/4,-1/4,-1/4,0;
     -1/4,-1/4,1/4,1/4,0; -1/4,-1/4,1/4,1/4,0; 0,0,0,0,1]

theorem kernel_values_one : ∀ i j, KOne i j = integerKernel (labelsOne i - labelsOne j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [KOne, labelsOne, integerKernel]
theorem kernel_values_two : ∀ i j, KTwo i j = integerKernel (labelsTwo i - labelsTwo j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [KTwo, labelsTwo, integerKernel]

theorem simple_counts : simpleCount labelsOne = 2 ∧ simpleCount labelsTwo = 1 := by decide

theorem overlap_values :
    entryFourth KOne = 11 ∧ entryFourth KTwo = 19/2 ∧
    squaredRowEnergy KOne = 29 ∧ squaredRowEnergy KTwo = 26 := by
  norm_num [entryFourth, squaredRowEnergy, KOne, KTwo, Fin.sum_univ_succ]

private theorem projections_one :
    POne*POne=POne ∧ QOne*QOne=QOne ∧ POne*QOne=0 ∧ QOne*POne=0 ∧
    KOne=(3:ℚ) • POne+QOne ∧ Matrix.trace POne=1 ∧ Matrix.trace QOne=2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [POne, QOne, KOne, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [POne, QOne, KOne, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [POne, QOne, KOne, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [POne, QOne, KOne, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [POne, QOne, KOne, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.trace, POne, QOne, Fin.sum_univ_succ]
  · norm_num [Matrix.trace, POne, QOne, Fin.sum_univ_succ]
private theorem projections_two :
    PTwo*PTwo=PTwo ∧ QTwo*QTwo=QTwo ∧ PTwo*QTwo=0 ∧ QTwo*PTwo=0 ∧
    KTwo=(3:ℚ) • PTwo+QTwo ∧ Matrix.trace PTwo=1 ∧ Matrix.trace QTwo=2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PTwo, QTwo, KTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PTwo, QTwo, KTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PTwo, QTwo, KTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PTwo, QTwo, KTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [PTwo, QTwo, KTwo, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.trace, PTwo, QTwo, Fin.sum_univ_succ]
  · norm_num [Matrix.trace, PTwo, QTwo, Fin.sum_univ_succ]

theorem projection_power {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℚ) (hPP : P*P=P) (hQQ : Q*Q=Q)
    (hPQ : P*Q=0) (hQP : Q*P=0) (m : ℕ) :
    ((3:ℚ) • P+Q)^(m+1) = (3:ℚ)^(m+1) • P+Q := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hPP, hQQ, hPQ, hQP, smul_zero, zero_add, add_zero]
    have hp : (3:ℚ) * 3^(m+1) = 3^(m+1+1) := by
      simp only [pow_succ]
      ring
    rw [hp]

theorem projection_power_trace {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℚ) (hPP : P*P=P) (hQQ : Q*Q=Q)
    (hPQ : P*Q=0) (hQP : Q*P=0) (hP : Matrix.trace P=1) (hQ : Matrix.trace Q=2)
    (m : ℕ) : Matrix.trace (((3:ℚ) • P+Q)^(m+1)) = (3:ℚ)^(m+1)+2 := by
  rw [projection_power P Q hPP hQQ hPQ hQP, Matrix.trace_add, Matrix.trace_smul, hP, hQ]
  simp

theorem all_positive_power_traces (m : ℕ) :
    Matrix.trace (KOne^(m+1)) = (3:ℚ)^(m+1)+2 ∧
    Matrix.trace (KTwo^(m+1)) = (3:ℚ)^(m+1)+2 := by
  rcases projections_one with ⟨h11,h12,h13,h14,h15,h16,h17⟩
  rcases projections_two with ⟨h21,h22,h23,h24,h25,h26,h27⟩
  constructor
  · rw [h15]
    exact projection_power_trace _ _ h11 h12 h13 h14 h16 h17 m
  · rw [h25]
    exact projection_power_trace _ _ h21 h22 h23 h24 h26 h27 m

theorem all_power_traces_equal (m : ℕ) : Matrix.trace (KOne^m) = Matrix.trace (KTwo^m) := by
  cases m with
  | zero => rfl
  | succ m => exact (all_positive_power_traces m).1.trans (all_positive_power_traces m).2.symm

/-- Full spectral moments do not determine the simple count for this fixed integer kernel. -/
theorem moments_equal_counts_and_overlap_different :
    (∀ m : ℕ, Matrix.trace (KOne^m) = Matrix.trace (KTwo^m)) ∧
    simpleCount labelsOne = 2 ∧ simpleCount labelsTwo = 1 ∧
    entryFourth KOne ≠ entryFourth KTwo := by
  refine ⟨all_power_traces_equal, simple_counts.1, simple_counts.2, ?_⟩
  rw [overlap_values.1, overlap_values.2.1]
  norm_num

#print axioms kernel_values_one
#print axioms kernel_values_two
#print axioms simple_counts
#print axioms overlap_values
#print axioms all_positive_power_traces
#print axioms moments_equal_counts_and_overlap_different

end CycleMoments.CountingOverlap
