import Zeta23Ext.EForm2.Expand
import Zeta23Ext.EForm2.Estimates
import Zeta23Ext.EForm2.Counting

/-!
# Single-pair bandlimited retention

Main results.

* `retention_of_damage` : the retention inequality holds as soon as the total damage
  `∑ j Qim y (x j - t)^2` of the on-line points stays inside the budget `2 A Shq y`.
* `retention_le_three` : the inequality at the exact constants for `n ≤ 3`, with no
  hypothesis on the configuration.
* `retention_separated` : the inequality at the exact constants for **every** `n`, provided
  the on-line points have consecutive gaps at least `26`.
-/

open scoped BigOperators
open MeasureTheory

namespace Retention.EForm2

/-- If the damage of the on-line points is inside the budget, retention holds. -/
theorem retention_of_damage (n : ℕ) (x : ℕ → ℝ) (t y : ℝ)
    (hdam : ∑ j ∈ Finset.range n, (Qim y (x j - t)) ^ 2 ≤ 2 * Aconst * Shq y) :
    (199/200) * Ener (Fsum n x) + (1/200) * n + 4
      ≤ Ener (fun w => Fsum n x w + Ppair t y w) := by
  have hgap := retention_gap n x t y
  have hA : 0 < Aconst := Aconst_pos
  have hShq : 0 ≤ Shq y := Shq_nonneg y
  -- the on-line interaction energy is at least `n A²`
  have hR : (n : ℝ) * Aconst ^ 2
      ≤ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2 := by
    have h1 : ∀ j ∈ Finset.range n,
        (Aconst ^ 2 : ℝ) ≤ ∑ k ∈ Finset.range n, (phiR (x j - x k)) ^ 2 := by
      intro j hj
      have h2 := Finset.single_le_sum (f := fun k => (phiR (x j - x k)) ^ 2)
        (fun k _ => sq_nonneg _) hj
      simpa [phiR_zero] using h2
    calc (n : ℝ) * Aconst ^ 2 = ∑ _j ∈ Finset.range n, Aconst ^ 2 := by
          simp
      _ ≤ _ := Finset.sum_le_sum h1
  -- the damage term
  have hdmg : -(∑ j ∈ Finset.range n, (Qim y (x j - t)) ^ 2)
      ≤ ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2) := by
    have h1 : ∑ j ∈ Finset.range n, (-((Qim y (x j - t)) ^ 2))
        ≤ ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2) :=
      Finset.sum_le_sum (fun i _ => by nlinarith [sq_nonneg (Pre y (x i - t))])
    simpa using h1
  have hbracket : 0 ≤ (1/200) * ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n,
        (phiR (x j - x k)) ^ 2) - n * Aconst ^ 2)
      + 4 * ∑ j ∈ Finset.range n, ((Pre y (x j - t)) ^ 2 - (Qim y (x j - t)) ^ 2)
      + 8 * Aconst * Shq y + 8 * (Shq y) ^ 2 := by
    nlinarith [sq_nonneg (Shq y)]
  have hinv : 0 < 1 / Aconst ^ 2 := by positivity
  nlinarith [mul_nonneg hinv.le hbracket]

/-- **Retention for `n ≤ 3`**, uniformly in the configuration, in `t` and in `y`. -/
theorem retention_le_three (n : ℕ) (hn : n ≤ 3) (x : ℕ → ℝ) (t y : ℝ) :
    (199/200) * Ener (Fsum n x) + (1/200) * n + 4
      ≤ Ener (fun w => Fsum n x w + Ppair t y w) := by
  refine retention_of_damage n x t y ?_
  have hShq : 0 ≤ Shq y := Shq_nonneg y
  have hA : (11:ℝ)/12 ≤ Aconst := Aconst_ge
  have hstep : ∑ j ∈ Finset.range n, (Qim y (x j - t)) ^ 2
      ≤ ∑ _j ∈ Finset.range n, ((Aconst + 27/100)/2) * Shq y :=
    Finset.sum_le_sum (fun i _ => Qim_sq_le_unif y (x i - t))
  have hcard : ∑ _j ∈ Finset.range n, ((Aconst + 27/100)/2) * Shq y
      = (n : ℝ) * (((Aconst + 27/100)/2) * Shq y) := by
    simp [Finset.sum_const]
  have hn' : (n : ℝ) ≤ 3 := by exact_mod_cast hn
  have hnonneg : 0 ≤ ((Aconst + 27/100)/2) * Shq y := by positivity
  nlinarith [hstep, hcard, hn', hnonneg]

/-- **Retention for every `n`, for separated on-line points.** -/
theorem retention_separated (n : ℕ) (x : ℕ → ℝ) (t y δ : ℝ) (hδ : 26 ≤ δ)
    (hsep : ∀ i, i + 1 < n → x i + δ ≤ x (i + 1)) (hy0 : 0 < y) (hy1 : y ≤ 1/2) :
    (199/200) * Ener (Fsum n x) + (1/200) * n + 4
      ≤ Ener (fun w => Fsum n x w + Ppair t y w) := by
  refine retention_of_damage n x t y ?_
  have hShq : 0 ≤ Shq y := Shq_nonneg y
  have hA : (11:ℝ)/12 ≤ Aconst := Aconst_ge
  have hδ0 : (0:ℝ) < δ := by linarith
  have hbound := sum_le_of_separated (n := n) (fun i => x i - t) δ
    (((Aconst + 27/100)/2) * Shq y) ((3136/25) * Shq y)
    (fun i => (Qim y (x i - t)) ^ 2) hδ0 (by positivity) (by positivity)
    (fun i hi => by have := hsep i hi; simpa using by linarith)
    (fun i _ => Qim_sq_le_unif y (x i - t))
    (fun i _ hs => Qim_sq_far hy0.le hy1 hs)
  have hδ2 : (676:ℝ) ≤ δ ^ 2 := by nlinarith
  have htail : (10/3) * ((3136/25) * Shq y) / δ ^ 2 ≤ (1568/2535) * Shq y := by
    have h := div_le_div_of_nonneg_left
      (show (0:ℝ) ≤ (10/3) * ((3136/25) * Shq y) by positivity)
      (by norm_num : (0:ℝ) < 676) hδ2
    calc (10/3) * ((3136/25) * Shq y) / δ ^ 2 ≤ (10/3) * ((3136/25) * Shq y) / 676 := h
      _ = (1568/2535) * Shq y := by ring
  nlinarith [hbound, htail, mul_nonneg (by linarith : (0:ℝ) ≤ Aconst - 11/12) hShq]

end Retention.EForm2
