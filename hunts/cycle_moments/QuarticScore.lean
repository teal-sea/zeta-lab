import Mathlib
noncomputable section

/-!
# The normalized quartic spectral score

This file proves the scalar conditions needed by the concave counting theorem:
global concavity, roots at zero and two, and the bound by one after normalization.
The derivative identities are connected to actual `HasDerivAt` declarations.
The admissibility condition is written as `8*t^2 <= 5` to avoid a square root.
-/

namespace CycleMoments

def score (t x : ℝ) : ℝ :=
  x * (2 - x) * (1 + t * (x - 1) + t ^ 2 * (x - 1) ^ 2)

theorem score_expansion (t x : ℝ) :
    score t x = (2 - 2*t + 2*t^2)*x + (-1 + 3*t - 5*t^2)*x^2
      + (-t + 4*t^2)*x^3 - t^2*x^4 := by
  unfold score
  ring

theorem score_second_derivative_certificate (t y : ℝ) :
    -12*t^2*y^2 - 6*t*y + 2*t^2 - 2 =
      -12*(t*y + 1/4)^2 + 2*t^2 - 5/4 := by ring

theorem score_second_derivative_nonpos (t y : ℝ) (ht : 8*t^2 ≤ 5) :
    -12*t^2*y^2 - 6*t*y + 2*t^2 - 2 ≤ 0 := by
  rw [score_second_derivative_certificate]
  nlinarith [sq_nonneg (t*y + 1/4)]


def scoreDeriv (t x : ℝ) : ℝ :=
  (2 - 2*t + 2*t^2) + 2*(-1 + 3*t - 5*t^2)*x
    + 3*(-t + 4*t^2)*x^2 - 4*t^2*x^3

theorem score_hasDerivAt (t x : ℝ) : HasDerivAt (score t) (scoreDeriv t x) x := by
  have h := (((((hasDerivAt_id x).const_mul (2 - 2*t + 2*t^2)).add
    (((hasDerivAt_id x).pow 2).const_mul (-1 + 3*t - 5*t^2))).add
    (((hasDerivAt_id x).pow 3).const_mul (-t + 4*t^2))).sub
    (((hasDerivAt_id x).pow 4).const_mul (t^2)))
  convert h using 1 <;> try rfl
  · funext y
    dsimp [score]
    ring
  · norm_num [scoreDeriv]
    ring

theorem scoreDeriv_hasDerivAt (t x : ℝ) :
    HasDerivAt (scoreDeriv t)
      (-12*t^2*(x-1)^2 - 6*t*(x-1) + 2*t^2 - 2) x := by
  have h := (((hasDerivAt_const x (2 - 2*t + 2*t^2)).add
    ((hasDerivAt_id x).const_mul (2*(-1 + 3*t - 5*t^2)))).add
    (((hasDerivAt_id x).pow 2).const_mul (3*(-t + 4*t^2)))).sub
    (((hasDerivAt_id x).pow 3).const_mul (4*t^2))
  convert h using 1 <;> try rfl
  norm_num [scoreDeriv]
  ring

theorem score_concave (t : ℝ) (ht : 8*t^2 ≤ 5) :
    ConcaveOn ℝ Set.univ (score t) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := scoreDeriv t)
    (f'' := fun x => -12*t^2*(x-1)^2 - 6*t*(x-1) + 2*t^2 - 2) convex_univ
  · unfold score
    fun_prop
  · intro x hx
    exact (score_hasDerivAt t x).hasDerivWithinAt
  · intro x hx
    exact (scoreDeriv_hasDerivAt t x).hasDerivWithinAt
  · intro x hx
    exact score_second_derivative_nonpos t (x-1) ht

@[simp] theorem score_zero (t : ℝ) : score t 0 = 0 := by simp [score]
@[simp] theorem score_two (t : ℝ) : score t 2 = 0 := by simp [score]

def scoreDenom (t : ℝ) : ℝ := 1 + t^2 / (4*(1-t^2))

def normalizedScore (t x : ℝ) : ℝ := score t x / scoreDenom t

theorem scoreDenom_pos (t : ℝ) (ht : 8*t^2 ≤ 5) : 0 < scoreDenom t := by
  have h : 0 < 4*(1-t^2) := by nlinarith
  have hp : 0 ≤ t^2 / (4*(1-t^2)) := div_nonneg (sq_nonneg t) h.le
  unfold scoreDenom
  linarith

theorem score_le_denom (t x : ℝ) (ht : 8*t^2 ≤ 5) : score t x ≤ scoreDenom t := by
  let y := x-1
  let a := 1-t^2
  have ha : 0 < a := by dsimp [a]; nlinarith
  have hden : 0 < 4*a := by positivity
  have hD : scoreDenom t = 1 + t^2 / (4*a) := rfl
  have hD1 : 1 ≤ scoreDenom t := by
    have hz := div_nonneg (sq_nonneg t) hden.le
    rw [hD]
    linarith
  have hq : score t x = (1-y^2)*(1+t*y+t^2*y^2) := by
    dsimp [score, y]
    ring
  have hq' : score t x = 1+t*y-a*y^2-t*y^3-t^2*y^4 := by
    dsimp [score, y, a]
    ring
  by_cases hy : y^2 ≤ 1
  · by_cases hty : 0 ≤ t*y
    · have hc : 0 ≤ t*y^3 := by
        nlinarith [mul_nonneg hty (sq_nonneg y)]
      have hd : 0 ≤ t^2*y^4 := by positivity
      have hupper : score t x ≤ 1+t*y-a*y^2 := by linarith [hq']
      have hmul := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 4*a by positivity)
      have hbound : 4*a*(score t x-1) ≤ t^2 := by
        nlinarith [sq_nonneg (2*a*y-t)]
      have hquot : score t x-1 ≤ t^2/(4*a) := by
        apply (le_div_iff₀ hden).mpr
        nlinarith [hbound]
      rw [hD]
      linarith
    · have hty' : t*y ≤ 0 := le_of_not_ge hty
      have hcross : t*y*(1-y^2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hty' (by linarith)
      have hsq : 0 ≤ a*y^2 := mul_nonneg ha.le (sq_nonneg y)
      have hfour : 0 ≤ t^2*y^4 := by positivity
      have hupper : score t x ≤ 1 := by nlinarith [hq']
      exact hupper.trans hD1
  · have hy' : 1 < y^2 := lt_of_not_ge hy
    have hfactor : 0 ≤ 1+t*y+t^2*y^2 := by nlinarith [sq_nonneg (t*y+1/2)]
    have hupper : score t x ≤ 0 := by
      rw [hq]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hfactor
    exact hupper.trans (le_trans (by norm_num) hD1)

theorem normalizedScore_le_one (t x : ℝ) (ht : 8*t^2 ≤ 5) :
    normalizedScore t x ≤ 1 := by
  unfold normalizedScore
  exact (div_le_one (scoreDenom_pos t ht)).mpr (score_le_denom t x ht)

@[simp] theorem normalizedScore_zero (t : ℝ) : normalizedScore t 0 = 0 := by
  simp [normalizedScore]

@[simp] theorem normalizedScore_two (t : ℝ) : normalizedScore t 2 = 0 := by
  simp [normalizedScore]

theorem normalizedScore_concave (t : ℝ) (ht : 8*t^2 ≤ 5) :
    ConcaveOn ℝ Set.univ (normalizedScore t) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := (score_concave t ht).2 hx hy ha hb hab
  simp only [smul_eq_mul] at h ⊢
  unfold normalizedScore
  calc
    a * (score t x / scoreDenom t) + b * (score t y / scoreDenom t) =
        (a * score t x + b * score t y) / scoreDenom t := by ring
    _ ≤ score t (a*x+b*y) / scoreDenom t :=
      div_le_div_of_nonneg_right h (scoreDenom_pos t ht).le

theorem discrepancy_factorization (k : ℝ) :
    3*(k+1/2)*((2*k^2+2*k+1)/4) - 2*(k^2+1/3) - 3*(k+1/2) + 2 =
      (6*k-5)*(6*k^2+6*k-1)/24 := by ring

theorem discrepancy_neg (k : ℝ) (hlo : 3/4 < k) (hhi : k < 5/6) :
    (6*k-5)*(6*k^2+6*k-1)/24 < 0 := by
  have ha : 6*k-5 < 0 := by linarith
  have hb : 0 < 6*k^2+6*k-1 := by nlinarith [sq_nonneg k]
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos ha hb) (by norm_num)

/-- info: 'CycleMoments.score_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms score_expansion
/-- info: 'CycleMoments.score_second_derivative_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms score_second_derivative_nonpos
/-- info: 'CycleMoments.score_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms score_hasDerivAt
/-- info: 'CycleMoments.scoreDeriv_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms scoreDeriv_hasDerivAt
/-- info: 'CycleMoments.score_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms score_concave
/-- info: 'CycleMoments.score_le_denom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms score_le_denom
/-- info: 'CycleMoments.normalizedScore_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normalizedScore_le_one
/-- info: 'CycleMoments.normalizedScore_concave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normalizedScore_concave
/-- info: 'CycleMoments.normalizedScore_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normalizedScore_zero
/-- info: 'CycleMoments.normalizedScore_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms normalizedScore_two
/-- info: 'CycleMoments.discrepancy_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms discrepancy_neg

end CycleMoments
