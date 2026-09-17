/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.BallTerm
import ZetaLean.DHCertSupport

/-!
# Ball support for the generated rung-3 certificate

The existing certificate support layer proves the analytic tail reduction using
rectangles.  This file keeps the input geometry as a rectangle, where it is
exactly the square-frontier segment from the plan, but carries every evaluated
value in `ComplexBall`.  Generated multiplication sites supply rational modulus
bounds as literals.
-/

open Complex Finset

namespace ZetaLean

namespace ComplexBall

/-- The DH coefficient represented as a ball. -/
def coeffBall (m : ℕ) : ComplexBall :=
  match m % 5 with
  | 1 => exact 1 0
  | 2 => kappaBall
  | 3 => kappaBall.neg
  | 4 => exact (-1) 0
  | _ => exact 0 0

theorem contains_exact_real (q : ℚ) : (exact q 0).contains (((q : ℝ) : ℂ)) := by
  have h := contains_exact q 0
  rw [show (⟨(q : ℝ), ((0 : ℚ) : ℝ)⟩ : ℂ) = (((q : ℝ) : ℂ)) by
    apply Complex.ext <;> norm_num] at h
  exact h

theorem contains_oneBall : (exact 1 0).contains ((1 : ℝ) : ℂ) := by
  simpa using contains_exact_real (1 : ℚ)

theorem contains_negOneBall : (exact (-1) 0).contains ((-1 : ℝ) : ℂ) := by
  simpa using contains_exact_real (-1 : ℚ)

theorem contains_negKappaBall : kappaBall.neg.contains ((-dh_kappa : ℝ) : ℂ) := by
  have h := contains_neg contains_kappaBall
  rwa [show -((dh_kappa : ℝ) : ℂ) = ((-dh_kappa : ℝ) : ℂ) by push_cast; ring] at h

theorem contains_coeff_term_zero {s : ℂ} (m : ℕ) (h : dh_coeff m = 0) :
    (exact 0 0).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s)) := by
  rw [h]
  simpa using contains_exact_real (0 : ℚ)

/-- A nonzero DH series term.  The generated caller supplies both centre-modulus
bounds as literals. -/
theorem contains_coeff_term_ne {s : ℂ} (m : ℕ) (h : m % 5 ≠ 0)
    {t : ComplexBall} {uc ut : ℚ}
    (hc : ‖(coeffBall m).centre‖ ≤ (uc : ℝ))
    (htc : ‖t.centre‖ ≤ (ut : ℝ))
    (ht : t.contains ((m : ℂ) ^ (-s))) :
    ((coeffBall m).mul t uc ut).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s)) := by
  have hm5 : m % 5 < 5 := Nat.mod_lt m (by norm_num)
  have hj : m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by omega
  rcases hj with h1 | h1 | h1 | h1
  · have hv : (coeffBall m).contains ((1 : ℝ) : ℂ) := by
      simpa [coeffBall, h1] using contains_oneBall
    have hm : dh_coeff m = 1 := by unfold dh_coeff; rw [h1]; rfl
    rw [hm]
    exact contains_mul hc htc hv ht
  · have hv : (coeffBall m).contains ((dh_kappa : ℝ) : ℂ) := by
      simpa [coeffBall, h1] using contains_kappaBall
    have hm : dh_coeff m = dh_kappa := by unfold dh_coeff; rw [h1]; rfl
    rw [hm]
    exact contains_mul hc htc hv ht
  · have hv : (coeffBall m).contains ((-dh_kappa : ℝ) : ℂ) := by
      simpa [coeffBall, h1] using contains_negKappaBall
    have hm : dh_coeff m = -dh_kappa := by unfold dh_coeff; rw [h1]; rfl
    rw [hm]
    exact contains_mul hc htc hv ht
  · have hv : (coeffBall m).contains ((-1 : ℝ) : ℂ) := by
      simpa [coeffBall, h1] using contains_negOneBall
    have hm : dh_coeff m = -1 := by unfold dh_coeff; rw [h1]; rfl
    rw [hm]
    exact contains_mul hc htc hv ht

/-- Left fold of term balls over `range N`. -/
def dhSumBalls (t : ℕ → ComplexBall) : ℕ → ComplexBall
  | 0 => exact 0 0
  | N + 1 => (dhSumBalls t N).add (t N)

theorem dhSumBalls_zero (t : ℕ → ComplexBall) : dhSumBalls t 0 = exact 0 0 := rfl

theorem dhSumBalls_succ (t : ℕ → ComplexBall) (N : ℕ) :
    dhSumBalls t (N + 1) = (dhSumBalls t N).add (t N) := rfl

theorem contains_dhSumBalls {s : ℂ} {t : ℕ → ComplexBall} (N : ℕ)
    (ht : ∀ m < N, (t m).contains ((dh_coeff m : ℂ) * (m : ℂ) ^ (-s))) :
    (dhSumBalls t N).contains
      (∑ n ∈ range N, (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)) := by
  induction N with
  | zero => simpa [dhSumBalls] using contains_exact_real (0 : ℚ)
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact contains_add (ih fun m hm => ht m (by omega)) (ht N (by omega))

/-- Halving a contained value without paying for a general product. -/
theorem contains_half_of {X : ComplexBall} {z : ℂ} (h : X.contains z) :
    (smulQ (1 / 2) X).contains (z / 2) := by
  have h2 := contains_smulQ (q := (1 / 2 : ℚ)) h
  rwa [show (((1 / 2 : ℚ) : ℂ)) * z = z / 2 by push_cast; ring] at h2

/-- The corrected centre `p + b - a` from three ball enclosures. -/
theorem contains_corrected {P B A : ComplexBall} {p b a : ℂ}
    (hP : P.contains p) (hB : B.contains b) (hA : A.contains a) :
    ((P.add B).add A.neg).contains (p + b - a) := by
  have h := contains_add (contains_add hP hB) (contains_neg hA)
  rwa [show p + b + -a = p + b - a by ring] at h

/-- The ball for `5(1-s)`.  `u` bounds the centre of `1-S`. -/
def fiveOneSubBall (S : ComplexBall) (u : ℚ) : ComplexBall :=
  mul (exact 5 0) ((exact 1 0).add S.neg) 5 u

theorem contains_fiveOneSubBall {S : ComplexBall} {s : ℂ} {u : ℚ}
    (hS : S.contains s)
    (hu : ‖((exact 1 0).add S.neg).centre‖ ≤ (u : ℝ)) :
    (fiveOneSubBall S u).contains (5 * (1 - s)) := by
  have h5 : (exact 5 0).contains ((5 : ℕ) : ℂ) := by
    simpa using contains_exact_real (5 : ℚ)
  have h1 : (exact 1 0).contains ((1 : ℕ) : ℂ) := by
    simpa using contains_exact_real (1 : ℚ)
  have hsub := contains_add h1 (contains_neg hS)
  have h := contains_mul (ux := (5 : ℚ)) (uy := u)
    (norm_centre_le (x := exact 5 0) (u := 5) (by norm_num)
      (by norm_num [exact])) hu h5 hsub
  rwa [show ((5 : ℕ) : ℂ) * (((1 : ℕ) : ℂ) + -s) = 5 * (1 - s) by push_cast; ring] at h

/-- Reciprocal enclosure for `5(1-s)`, with all irrational modulus work replaced
by generated rational literals. -/
theorem contains_inv5sBall {S : ComplexBall} {s : ℂ} {u l R : ℚ}
    (hS : S.contains s)
    (hu : ‖((exact 1 0).add S.neg).centre‖ ≤ (u : ℝ))
    (hl0 : 0 ≤ l)
    (hl : (l : ℝ) ≤ ‖(fiveOneSubBall S u).centre‖)
    (hgap : (fiveOneSubBall S u).rad < l)
    (hR : (fiveOneSubBall S u).rad /
      (l * (l - (fiveOneSubBall S u).rad)) ≤ R) :
    ((fiveOneSubBall S u).inv R).contains ((5 * (1 - s))⁻¹) :=
  contains_inv (contains_fiveOneSubBall hS hu) hl0 hl hgap hR

/-! ### The order-2 correction from four power balls -/

/-- The `K`-th block from four `n^{-s}` balls. -/
theorem contains_dhBlock_of_terms_ball {s : ℂ} (K : ℕ)
    {t1 t2 t3 t4 : ComplexBall} {uκ up : ℚ}
    (h1 : t1.contains (((K * 5 + 1 : ℕ) : ℂ) ^ (-s)))
    (h2 : t2.contains (((K * 5 + 2 : ℕ) : ℂ) ^ (-s)))
    (h3 : t3.contains (((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
    (h4 : t4.contains (((K * 5 + 4 : ℕ) : ℂ) ^ (-s)))
    (hκ : ‖kappaBall.centre‖ ≤ (uκ : ℝ))
    (hp : ‖((t2.add t3.neg).centre)‖ ≤ (up : ℝ)) :
    ((t1.add t4.neg).add (ComplexBall.mul kappaBall (t2.add t3.neg) uκ up)).contains
      (DH.dhBlock s K) := by
  rw [DH.dhBlock_eq_pair]
  have hp1 := contains_add h1 (contains_neg h4)
  have hp2 := contains_add h2 (contains_neg h3)
  have h := contains_add hp1 (contains_mul hκ hp contains_kappaBall hp2)
  rwa [show ((K * 5 + 1 : ℕ) : ℂ) ^ (-s) + -(((K * 5 + 4 : ℕ) : ℂ) ^ (-s))
      + ((dh_kappa : ℝ) : ℂ)
        * (((K * 5 + 2 : ℕ) : ℂ) ^ (-s) + -(((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
      = (((K * 5 + 1 : ℕ) : ℂ) ^ (-s) - ((K * 5 + 4 : ℕ) : ℂ) ^ (-s))
        + (dh_kappa : ℂ)
          * (((K * 5 + 2 : ℕ) : ℂ) ^ (-s) - ((K * 5 + 3 : ℕ) : ℂ) ^ (-s)) by
    ring] at h

/-- The antiderivative correction from four `n^{-s}` balls and a reciprocal ball. -/
theorem contains_dhAnti_of_terms_ball {s : ℂ} (K : ℕ)
    {t1 t2 t3 t4 V : ComplexBall} {uκ up us uV : ℚ}
    (h1 : t1.contains (((K * 5 + 1 : ℕ) : ℂ) ^ (-s)))
    (h2 : t2.contains (((K * 5 + 2 : ℕ) : ℂ) ^ (-s)))
    (h3 : t3.contains (((K * 5 + 3 : ℕ) : ℂ) ^ (-s)))
    (h4 : t4.contains (((K * 5 + 4 : ℕ) : ℂ) ^ (-s)))
    (hV : V.contains ((5 * (1 - s))⁻¹))
    (hκ : ‖kappaBall.centre‖ ≤ (uκ : ℝ))
    (hp : ‖((smulQ (K * 5 + 2 : ℚ) t2).add
      (smulQ (K * 5 + 3 : ℚ) t3).neg).centre‖ ≤ (up : ℝ))
    (hs : ‖(((smulQ (K * 5 + 1 : ℚ) t1).add
      (smulQ (K * 5 + 4 : ℚ) t4).neg).add
      (ComplexBall.mul kappaBall
        ((smulQ (K * 5 + 2 : ℚ) t2).add
          (smulQ (K * 5 + 3 : ℚ) t3).neg) uκ up)).centre‖ ≤ (us : ℝ))
    (hVc : ‖V.centre‖ ≤ (uV : ℝ)) :
    (ComplexBall.mul
      (((smulQ (K * 5 + 1 : ℚ) t1).add
        (smulQ (K * 5 + 4 : ℚ) t4).neg).add
        (ComplexBall.mul kappaBall
          ((smulQ (K * 5 + 2 : ℚ) t2).add
            (smulQ (K * 5 + 3 : ℚ) t3).neg) uκ up))
      V us uV).contains (DH.dhAnti s (K : ℝ)) := by
  rw [DH.dhAnti_eq_terms]
  have e1 := contains_smulQ (q := (K * 5 + 1 : ℚ)) h1
  have e2 := contains_smulQ (q := (K * 5 + 2 : ℚ)) h2
  have e3 := contains_smulQ (q := (K * 5 + 3 : ℚ)) h3
  have e4 := contains_smulQ (q := (K * 5 + 4 : ℚ)) h4
  have hp0 := contains_add e2 (contains_neg e3)
  have hk := contains_mul hκ hp contains_kappaBall hp0
  have hsum := contains_add (contains_add e1 (contains_neg e4)) hk
  have h := contains_mul hs hVc hsum hV
  convert h using 1 <;> push_cast <;> ring

/-- Read a strict upper norm bound from a ball with a literal centre bound. -/
theorem norm_lt_of_ball_enclosure {B : ComplexBall} {z : ℂ} {u q : ℚ}
    (hB : B.contains z) (hu : ‖B.centre‖ ≤ (u : ℝ)) (h : u + B.rad < q) :
    ‖z‖ < (q : ℝ) :=
  lt_of_le_of_lt (norm_le_normBound hu hB) (by exact_mod_cast h)

/-- Read a weak upper norm bound from a ball with a literal centre bound. -/
theorem norm_le_of_ball_enclosure {B : ComplexBall} {z : ℂ} {u q : ℚ}
    (hB : B.contains z) (hu : ‖B.centre‖ ≤ (u : ℝ)) (h : u + B.rad ≤ q) :
    ‖z‖ ≤ (q : ℝ) :=
  le_trans (norm_le_normBound hu hB) (by exact_mod_cast h)

/-- Read a lower norm bound from a ball with a literal centre lower bound. -/
theorem le_norm_of_ball_enclosure {B : ComplexBall} {z : ℂ} {l q : ℚ}
    (hB : B.contains z) (hl : (l : ℝ) ≤ ‖B.centre‖) (h : q ≤ l - B.rad) :
    (q : ℝ) ≤ ‖z‖ :=
  le_norm_of_normLower hl hB h

end ComplexBall

namespace DH

open ComplexBall

/-- Order-2 tail assembly with the evaluated value carried by a ball.  The input
rectangle remains the plan's exact site geometry and supplies the strip and norm
bounds used by the analytic tail estimate. -/
theorem DH_mem_of_partial_enclosure_order2_ball
    {SI : ComplexInterval} {s : ℂ} (hSI : SI.contains s)
    (hσ0 : 0 < SI.re.lo) (him : 0 < SI.im.lo)
    {K : ℕ} (hK : 1 ≤ K) {B : ComplexBall}
    (hB : B.contains (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
      + dhBlock s K / 2 - dhAnti s (K : ℝ)))
    {σlo : ℚ} (hσlo : 0 < σlo) (hσle : σlo ≤ SI.re.lo)
    {a b : ℕ} (hb : 0 < b) (hab : σlo + 2 = (a : ℚ) / (b : ℚ))
    {P : ℚ} (hP : 0 < P) (hpow : 1 ≤ P ^ b * (5 * (K : ℚ) + 1) ^ a)
    {NS NS1 NS2 : ℚ}
    (hNS : ComplexInterval.normBound SI ≤ NS)
    (hNS1 : ComplexInterval.normBound (SI.add (ComplexInterval.exact 1 0)) ≤ NS1)
    (hNS2 : ComplexInterval.normBound (SI.add (ComplexInterval.exact 2 0)) ≤ NS2)
    {r : ℚ}
    (hr : 5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P / (σlo + 2) ≤ r) :
    (B.inflate r).contains (DH s) := by
  have hsre : 0 < s.re := lt_of_lt_of_le (by exact_mod_cast hσ0) hSI.1.1
  have hsim : 0 < s.im := lt_of_lt_of_le (by exact_mod_cast him) hSI.2.1
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsim
    simp at hsim
  have htail := DH_tail_bound_order2 hsre hs1 hK
  have hNSr : ‖s‖ ≤ (NS : ℝ) :=
    (ComplexInterval.norm_le_normBound hSI).trans (by exact_mod_cast hNS)
  have hS1 : (SI.add (ComplexInterval.exact 1 0)).contains (s + 1) := by
    have h := ComplexInterval.contains_add hSI (contains_natCBox 1)
    rwa [show s + ((1 : ℕ) : ℂ) = s + 1 by push_cast; ring] at h
  have hS2 : (SI.add (ComplexInterval.exact 2 0)).contains (s + 2) := by
    have h := ComplexInterval.contains_add hSI (contains_natCBox 2)
    rwa [show s + ((2 : ℕ) : ℂ) = s + 2 by push_cast; ring] at h
  have hNS1r : ‖s + 1‖ ≤ (NS1 : ℝ) :=
    (ComplexInterval.norm_le_normBound hS1).trans (by exact_mod_cast hNS1)
  have hNS2r : ‖s + 2‖ ≤ (NS2 : ℝ) :=
    (ComplexInterval.norm_le_normBound hS2).trans (by exact_mod_cast hNS2)
  have hκ : dh_kappa ≤ ((2840794 / 10000000 : ℚ) : ℝ) := contains_kappaI.2
  have hbase : (1 : ℝ) ≤ 5 * (K : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    linarith
  have hPr : (5 * (K : ℝ) + 1) ^ (-((a : ℝ) / (b : ℝ))) ≤ (P : ℝ) := by
    refine rpow_neg_div_le hbase hb hP ?_
    have h := hpow
    have hcast : ((P ^ b * (5 * (K : ℚ) + 1) ^ a : ℚ) : ℝ)
        = (P : ℝ) ^ b * (5 * (K : ℝ) + 1) ^ a := by push_cast; ring
    calc (1 : ℝ) = ((1 : ℚ) : ℝ) := by norm_num
      _ ≤ ((P ^ b * (5 * (K : ℚ) + 1) ^ a : ℚ) : ℝ) := by exact_mod_cast h
      _ = _ := hcast
  have hab' : ((σlo : ℝ)) + 2 = (a : ℝ) / (b : ℝ) := by
    have h := congrArg (Rat.cast (K := ℝ)) hab
    push_cast at h
    exact h
  have hexp : -s.re - 2 ≤ -((a : ℝ) / (b : ℝ)) := by
    have hσler : (σlo : ℝ) ≤ (SI.re.lo : ℝ) := by exact_mod_cast hσle
    have := hSI.1.1
    linarith
  have hrpow : (5 * (K : ℝ) + 1) ^ (-s.re - 2) ≤ (P : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans hPr
  have hden : ((σlo : ℝ)) + 2 ≤ s.re + 2 := by
    have hσler : (σlo : ℝ) ≤ (SI.re.lo : ℝ) := by exact_mod_cast hσle
    have := hSI.1.1
    linarith
  have hσ2 : (0 : ℝ) < (σlo : ℝ) + 2 := by
    have : (0 : ℝ) < (σlo : ℝ) := by exact_mod_cast hσlo
    linarith
  have hnn : (0 : ℝ) ≤ 3 + dh_kappa := by linarith [dh_kappa_nonneg]
  have hκh : (0 : ℝ) ≤ 3 + ((2840794 / 10000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hNS0 : (0 : ℝ) ≤ (NS : ℝ) := le_trans (norm_nonneg s) hNSr
  have hNS10 : (0 : ℝ) ≤ (NS1 : ℝ) := le_trans (norm_nonneg _) hNS1r
  have hNS20 : (0 : ℝ) ≤ (NS2 : ℝ) := le_trans (norm_nonneg _) hNS2r
  have hP0 : (0 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP.le
  have hA : (3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖
      ≤ (3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ) * (NS2 : ℝ) := by
    have h1 : 3 + dh_kappa ≤ 3 + ((2840794 / 10000000 : ℚ) : ℝ) := by linarith
    have m1 := mul_le_mul h1 hNSr (norm_nonneg _) hκh
    have m2 := mul_le_mul m1 hNS1r (norm_nonneg _) (mul_nonneg hκh hNS0)
    exact mul_le_mul m2 hNS2r (norm_nonneg _)
      (mul_nonneg (mul_nonneg hκh hNS0) hNS10)
  have hnum : 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
      * (5 * (K : ℝ) + 1) ^ (-s.re - 2)
      ≤ 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) := by
    have h := mul_le_mul hA hrpow (Real.rpow_nonneg (by linarith) _)
      (mul_nonneg (mul_nonneg (mul_nonneg hκh hNS0) hNS10) hNS20)
    calc 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
          * (5 * (K : ℝ) + 1) ^ (-s.re - 2)
        = 5 / 8 * (((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
            * (5 * (K : ℝ) + 1) ^ (-s.re - 2)) := by ring
      _ ≤ 5 / 8 * (((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
            * (NS2 : ℝ)) * (P : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h (by norm_num)
      _ = 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
            * (NS2 : ℝ)) * (P : ℝ) := by ring
  have hchain : 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
      * (5 * (K : ℝ) + 1) ^ (-s.re - 2) / (s.re + 2)
      ≤ 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2) := by
    refine div_le_div₀ ?_ hnum hσ2 hden
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5 / 8)
      (mul_nonneg (mul_nonneg (mul_nonneg hκh hNS0) hNS10) hNS20)) hP0
  have hrr : 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
      * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2) ≤ (r : ℝ) := by
    have h := hr
    have hcast : ((5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P /
        (σlo + 2) : ℚ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
    calc 5 / 8 * ((3 + ((2840794 / 10000000 : ℚ) : ℝ)) * (NS : ℝ) * (NS1 : ℝ)
          * (NS2 : ℝ)) * (P : ℝ) / ((σlo : ℝ) + 2)
        = ((5 / 8 * ((3 + 2840794 / 10000000) * NS * NS1 * NS2) * P /
          (σlo + 2) : ℚ) : ℝ) := by push_cast; ring
      _ ≤ (r : ℝ) := hcast
  exact ComplexBall.contains_inflate_of_dist r hB (htail.trans (hchain.trans hrr))

end DH

end ZetaLean
