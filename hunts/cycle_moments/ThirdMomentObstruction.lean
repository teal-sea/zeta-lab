import Mathlib

namespace CycleMoments.ThirdMomentObstruction

def eigenvalues (b : ℝ) : Fin 3 → ℝ := ![b + 2, b + 2, -2*b]

def moment (b : ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin 3, eigenvalues b i ^ j

def discrepancy (b : ℝ) : ℝ := moment b 3 - 3*moment b 2 + 8

def slack (b : ℝ) : ℝ := moment b 2 - 8

theorem pair_norm_difference (b : ℝ) (hb : 0 ≤ b) :
    Real.sqrt (1 + b/2) ^ 2 - Real.sqrt (b/2) ^ 2 = 1 := by
  rw [Real.sq_sqrt (by linarith : 0 ≤ 1 + b/2),
    Real.sq_sqrt (by linarith : 0 ≤ b/2)]
  ring

theorem first_moment (b : ℝ) : moment b 1 = 4 := by
  simp [moment, eigenvalues, Fin.sum_univ_three]
  ring

theorem second_moment (b : ℝ) : moment b 2 = 6*b^2 + 8*b + 8 := by
  simp [moment, eigenvalues, Fin.sum_univ_three]
  ring

theorem third_moment (b : ℝ) :
    moment b 3 = -6*b^3 + 12*b^2 + 24*b + 16 := by
  simp [moment, eigenvalues, Fin.sum_univ_three]
  ring

theorem fourth_moment (b : ℝ) :
    moment b 4 = 18*b^4 + 16*b^3 + 48*b^2 + 64*b + 32 := by
  simp [moment, eigenvalues, Fin.sum_univ_three]
  ring

theorem discrepancy_formula (b : ℝ) : discrepancy b = -6*b^2*(b+1) := by
  rw [discrepancy, second_moment, third_moment]
  ring

theorem slack_formula (b : ℝ) : slack b = 6*b^2 + 8*b := by
  rw [slack, second_moment]
  ring

theorem discrepancy_negative (b : ℝ) (hb : 0 < b) : discrepancy b < 0 := by
  rw [discrepancy_formula]
  have hsq : 0 < b^2 := sq_pos_of_pos hb
  have hnext : 0 < b+1 := by linarith
  nlinarith [mul_pos hsq hnext]

theorem slack_positive (b : ℝ) (hb : 0 < b) : 0 < slack b := by
  rw [slack_formula]
  positivity

theorem cubic_dominates_slack (b : ℝ) (hb : 0 ≤ b) :
    b/2 * slack b ≤ -discrepancy b := by
  rw [slack_formula, discrepancy_formula]
  have hnonneg : 0 ≤ b^2*(3*b+2) := by positivity
  nlinarith

#print axioms pair_norm_difference
#print axioms first_moment
#print axioms second_moment
#print axioms third_moment
#print axioms fourth_moment
#print axioms discrepancy_formula
#print axioms slack_formula
#print axioms discrepancy_negative
#print axioms slack_positive
#print axioms cubic_dominates_slack

end CycleMoments.ThirdMomentObstruction
