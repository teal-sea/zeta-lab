/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib

/-!
# Concave spectral scores and adapted scalar blocks

The spectral Jensen theorem is derived from the real matrix spectral theorem
and scalar Jensen, with the unitary row and column sums established directly.
The scalar counting lemmas prove the three-block step of the proof note.

`count_of_adapted_diagonal` combines these results. Its diagonal block
hypotheses remain explicit: this file does not yet construct an adapted basis
from the signed vector data in the full finite counting theorem.
-/

open Matrix Finset
open scoped BigOperators

namespace CycleMoments

theorem spectral_concave_jensen {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) :
    (∑ i, f (hA.eigenvalues i)) ≤ ∑ i, f (A i i) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  have hrow (i : n) : ∑ j, (U i j)^2 = 1 := by
    have hu := congrArg (fun B : Matrix n n ℝ => B i i)
      (Matrix.mem_unitaryGroup_iff.mp hA.eigenvectorUnitary.property)
    simpa [U, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      sq] using hu
  have hcol (j : n) : ∑ i, (U i j)^2 = 1 := by
    have hu := congrArg (fun B : Matrix n n ℝ => B j j)
      (Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.property)
    simpa [U, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
      sq] using hu
  have hdiag (i : n) : A i i = ∑ j, (U i j)^2 * hA.eigenvalues j := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j hj
    simp [U, Matrix.mul_diagonal, sq, mul_comm, mul_left_comm]
  have hpoint (i : n) :
      (∑ j, (U i j)^2 * f (hA.eigenvalues j)) ≤ f (A i i) := by
    have h := hf.le_map_sum (t := Finset.univ) (w := fun j => (U i j)^2)
      (p := hA.eigenvalues) (by intro j hj; positivity)
      (by simpa using hrow i) (by simp)
    simpa [smul_eq_mul, ← hdiag i] using h
  calc
    (∑ j, f (hA.eigenvalues j)) =
        ∑ j, ∑ i, (U i j)^2 * f (hA.eigenvalues j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_mul, hcol j, one_mul]
    _ = ∑ i, ∑ j, (U i j)^2 * f (hA.eigenvalues j) := Finset.sum_comm
    _ ≤ ∑ i, f (A i i) := Finset.sum_le_sum (fun i hi => hpoint i)

theorem concave_score_nonpos_ge_two (f : ℝ → ℝ)
    (hf : ConcaveOn ℝ Set.univ f) (h0 : f 0 = 0) (h2 : f 2 = 0)
    {x : ℝ} (hx : 2 ≤ x) : f x ≤ 0 := by
  have hxp : 0 < x := by linarith
  have ha : 0 < 2 / x := by positivity
  have hb : 0 ≤ 1 - 2 / x := by
    exact sub_nonneg.mpr ((div_le_one hxp).mpr hx)
  have hj := hf.2 (Set.mem_univ x) (Set.mem_univ 0) ha.le hb
    (show 2 / x + (1 - 2 / x) = 1 by ring)
  have he : 2 / x * x = 2 := div_mul_cancel₀ 2 hxp.ne'
  simp only [smul_eq_mul, h0, mul_zero, add_zero, he, h2] at hj
  nlinarith

theorem concave_score_nonpos_le_zero (f : ℝ → ℝ)
    (hf : ConcaveOn ℝ Set.univ f) (h0 : f 0 = 0) (h2 : f 2 = 0)
    {x : ℝ} (hx : x ≤ 0) : f x ≤ 0 := by
  have hp : 0 < 2 - x := by linarith
  have ha : 0 < 2 / (2 - x) := by positivity
  have hb : 0 ≤ -x / (2 - x) := div_nonneg (neg_nonneg.mpr hx) hp.le
  have hab : 2 / (2 - x) + -x / (2 - x) = 1 := by field_simp; ring
  have he : 2 / (2 - x) * x + (-x / (2 - x)) * 2 = 0 := by ring
  have hj := hf.2 (Set.mem_univ x) (Set.mem_univ 2) ha.le hb hab
  simp only [smul_eq_mul, h2, mul_zero, add_zero, he, h0] at hj
  nlinarith

theorem concave_score_sum_le_zero {u : Type*} [Fintype u]
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) (h0 : f 0 = 0) (h2 : f 2 = 0)
    (a : u → ℝ) (ha : 2 * (Fintype.card u : ℝ) ≤ ∑ i, a i) :
    (∑ i, f (a i)) ≤ 0 := by
  cases isEmpty_or_nonempty u with
  | inl he => simp
  | inr hn =>
    let m : ℝ := Fintype.card u
    have hm : 0 < m := by
      change (0 : ℝ) < (Fintype.card u : ℝ)
      exact_mod_cast (Fintype.card_pos (α := u))
    have hw : ∑ _i : u, (1 / m) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change m * (1 / m) = 1
      field_simp
    have hj := hf.le_map_sum (t := Finset.univ) (w := fun _i : u => 1 / m)
      (p := a) (by intro i hi; positivity) (by simpa using hw) (by simp)
    have havg : 2 ≤ (1 / m) * ∑ i, a i := by
      change 2 * m ≤ ∑ i, a i at ha
      apply (le_div_iff₀ hm).mpr at ha
      simpa [div_eq_mul_inv, mul_comm] using ha
    have hscore := concave_score_nonpos_ge_two f hf h0 h2 havg
    have hj' : (1 / m) * (∑ i, f (a i)) ≤ f ((1 / m) * ∑ i, a i) := by
      simpa [smul_eq_mul, ← Finset.mul_sum] using hj
    have hprod : (1 / m) * (∑ i, f (a i)) ≤ 0 := hj'.trans hscore
    have hinv : 0 < 1 / m := by positivity
    nlinarith

theorem adapted_scalar_block_count {u v w : Type*}
    [Fintype u] [Fintype v] [Fintype w]
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) (h0 : f 0 = 0) (h2 : f 2 = 0)
    (hmax : ∀ x, f x ≤ 1)
    (a : u → ℝ) (b : v → ℝ) (c : w → ℝ)
    (ha : 2 * (Fintype.card u : ℝ) ≤ ∑ i, a i)
    (hc : ∀ i, c i ≤ 0) :
    (∑ i, f (a i)) + (∑ i, f (b i)) + (∑ i, f (c i)) ≤ (Fintype.card v : ℝ) := by
  have hu := concave_score_sum_le_zero f hf h0 h2 a ha
  have hv : (∑ i, f (b i)) ≤ (Fintype.card v : ℝ) := by
    calc
      (∑ i, f (b i)) ≤ ∑ _i : v, (1 : ℝ) := Finset.sum_le_sum (fun i hi => hmax (b i))
      _ = (Fintype.card v : ℝ) := by simp
  have hw : (∑ i, f (c i)) ≤ 0 := by
    exact Finset.sum_nonpos (fun i hi => concave_score_nonpos_le_zero f hf h0 h2 (hc i))
  linarith

/-- Spectral counting once the adapted diagonal block conditions have been established. -/
theorem count_of_adapted_diagonal {u v w : Type*}
    [Fintype u] [Fintype v] [Fintype w]
    [DecidableEq u] [DecidableEq v] [DecidableEq w]
    (A : Matrix (u ⊕ (v ⊕ w)) (u ⊕ (v ⊕ w)) ℝ) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) (h0 : f 0 = 0) (h2 : f 2 = 0)
    (hmax : ∀ x, f x ≤ 1)
    (hu : 2 * (Fintype.card u : ℝ) ≤ ∑ i, A (Sum.inl i) (Sum.inl i))
    (hw : ∀ i, A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) ≤ 0) :
    (∑ i, f (hA.eigenvalues i)) ≤ (Fintype.card v : ℝ) := by
  apply (spectral_concave_jensen A hA f hf).trans
  have h := adapted_scalar_block_count f hf h0 h2 hmax
    (fun i => A (Sum.inl i) (Sum.inl i))
    (fun i => A (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inl i)))
    (fun i => A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i))) hu hw
  simpa [Fintype.sum_sum_type, add_assoc] using h

/-- info: 'CycleMoments.spectral_concave_jensen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms spectral_concave_jensen
/-- info: 'CycleMoments.concave_score_nonpos_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concave_score_nonpos_ge_two
/-- info: 'CycleMoments.concave_score_nonpos_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concave_score_nonpos_le_zero
/-- info: 'CycleMoments.concave_score_sum_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms concave_score_sum_le_zero
/-- info: 'CycleMoments.adapted_scalar_block_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms adapted_scalar_block_count
/-- info: 'CycleMoments.count_of_adapted_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms count_of_adapted_diagonal

end CycleMoments

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


namespace CycleMoments

/-- The normalized quartic score applied to the checked adapted-block count. -/
theorem quartic_count_of_adapted_diagonal {u v w : Type*}
    [Fintype u] [Fintype v] [Fintype w]
    [DecidableEq u] [DecidableEq v] [DecidableEq w]
    (A : Matrix (u ⊕ (v ⊕ w)) (u ⊕ (v ⊕ w)) ℝ) (hA : A.IsHermitian)
    (t : ℝ) (ht : 8*t^2 ≤ 5)
    (hu : 2 * (Fintype.card u : ℝ) ≤ ∑ i, A (Sum.inl i) (Sum.inl i))
    (hw : ∀ i, A (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) ≤ 0) :
    (∑ i, normalizedScore t (hA.eigenvalues i)) ≤ (Fintype.card v : ℝ) := by
  exact count_of_adapted_diagonal A hA (normalizedScore t)
    (normalizedScore_concave t ht) (normalizedScore_zero t) (normalizedScore_two t)
    (fun x => normalizedScore_le_one t x ht) hu hw

/-- info: 'CycleMoments.quartic_count_of_adapted_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms quartic_count_of_adapted_diagonal

end CycleMoments
