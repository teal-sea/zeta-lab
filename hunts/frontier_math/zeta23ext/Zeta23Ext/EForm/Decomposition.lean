import Zeta23Ext.EForm.Energy

open scoped BigOperators
open scoped Real
open MeasureTheory

namespace Retention

/-- The on-line exponential sum `F(w) = ∑_j exp (I x_j w)`. -/
noncomputable def Fsum {n : ℕ} (x : Fin n → ℝ) (w : ℝ) : ℂ :=
  ∑ j, Complex.exp (Complex.I * ((x j * w : ℝ) : ℂ))

/-- The cosh-weighted pair term `P(w) = 2 cosh (y w) exp (I t w)`. -/
noncomputable def Pterm (t y : ℝ) (w : ℝ) : ℂ :=
  2 * (Real.cosh (y * w) : ℂ) * Complex.exp (Complex.I * ((t * w : ℝ) : ℂ))

lemma c2_total : ∫ w : ℝ, c2 w = Aconst ^ 2 := by
  have h := Icos_zero
  rw [Icos] at h
  simpa using h

lemma re_F {n : ℕ} (x : Fin n → ℝ) (w : ℝ) :
    (Fsum x w).re = ∑ j, Real.cos (x j * w) := by
  simp [Fsum, Complex.re_sum, Complex.exp_re]

lemma im_F {n : ℕ} (x : Fin n → ℝ) (w : ℝ) :
    (Fsum x w).im = ∑ j, Real.sin (x j * w) := by
  simp [Fsum, Complex.im_sum, Complex.exp_im]

lemma re_FP {n : ℕ} (x : Fin n → ℝ) (t y w : ℝ) :
    (Fsum x w + Pterm t y w).re
      = (∑ j, Real.cos (x j * w)) + 2 * Real.cosh (y * w) * Real.cos (t * w) := by
  simp [Fsum, Pterm, Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.exp_re,
    Complex.exp_im, -Complex.ofReal_cosh]

lemma im_FP {n : ℕ} (x : Fin n → ℝ) (t y w : ℝ) :
    (Fsum x w + Pterm t y w).im
      = (∑ j, Real.sin (x j * w)) + 2 * Real.cosh (y * w) * Real.sin (t * w) := by
  simp [Fsum, Pterm, Complex.add_im, Complex.im_sum, Complex.mul_im, Complex.mul_re,
    Complex.exp_re, Complex.exp_im, -Complex.ofReal_cosh]

lemma normSq_F {n : ℕ} (x : Fin n → ℝ) (w : ℝ) :
    ‖Fsum x w‖ ^ 2 = ∑ j, ∑ k, Real.cos ((x j - x k) * w) := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_F, im_F]
  have h1 : ∀ j k : Fin n, Real.cos ((x j - x k) * w)
      = Real.cos (x j * w) * Real.cos (x k * w) + Real.sin (x j * w) * Real.sin (x k * w) := by
    intro j k; rw [sub_mul, Real.cos_sub]
  simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

lemma normSq_FP {n : ℕ} (x : Fin n → ℝ) (t y w : ℝ) :
    ‖Fsum x w + Pterm t y w‖ ^ 2
      = (∑ j, ∑ k, Real.cos ((x j - x k) * w))
        + ((∑ j, 4 * (Real.cosh (y * w) * Real.cos ((x j - t) * w)))
          + (2 * (Real.cosh (2 * y * w) - 1) + 4)) := by
  rw [Complex.sq_norm, Complex.normSq_apply, re_FP, im_FP]
  have h1 : ∀ j k : Fin n, Real.cos ((x j - x k) * w)
      = Real.cos (x j * w) * Real.cos (x k * w) + Real.sin (x j * w) * Real.sin (x k * w) := by
    intro j k; rw [sub_mul, Real.cos_sub]
  have h2 : ∀ j : Fin n, 4 * (Real.cosh (y * w) * Real.cos ((x j - t) * w))
      = (4 * Real.cosh (y * w) * Real.cos (t * w)) * Real.cos (x j * w)
        + (4 * Real.cosh (y * w) * Real.sin (t * w)) * Real.sin (x j * w) := by
    intro j; rw [sub_mul, Real.cos_sub]; ring
  have hch : Real.cosh (2 * y * w) = Real.cosh (y * w) ^ 2 + Real.sinh (y * w) ^ 2 := by
    rw [show 2 * y * w = 2 * (y * w) by ring, Real.cosh_two_mul]
  have hps : Real.cosh (y * w) ^ 2 - Real.sinh (y * w) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hpc : Real.cos (t * w) ^ 2 + Real.sin (t * w) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
  simp_rw [h1, h2, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  nlinarith [hch, hps, hpc, sq_nonneg (Real.cosh (y * w))]

lemma En_F {n : ℕ} (x : Fin n → ℝ) :
    En (Fsum x) = (1 / Aconst ^ 2) * ∑ j, ∑ k, Icos (x j - x k) := by
  rw [En]
  congr 1
  have hpt : ∀ w : ℝ, c2 w * ‖Fsum x w‖ ^ 2
      = c2 w * ∑ j, ∑ k, Real.cos ((x j - x k) * w) := by
    intro w; rw [normSq_F]
  rw [show (∫ w in (-1:ℝ)..1, c2 w * ‖Fsum x w‖ ^ 2)
      = ∫ w in (-1:ℝ)..1, c2 w * ∑ j, ∑ k, Real.cos ((x j - x k) * w) by
    exact intervalIntegral.integral_congr (fun w _ => hpt w)]
  rw [interval_to_full, c2_int_sum _ (fun j => by fun_prop)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [c2_int_sum _ (fun k => by fun_prop)]
  rfl

lemma En_FP {n : ℕ} (x : Fin n → ℝ) (t y : ℝ) :
    En (fun w => Fsum x w + Pterm t y w)
      = (1 / Aconst ^ 2) * ((∑ j, ∑ k, Icos (x j - x k))
          + ((∑ j, 4 * Icross y (x j - t)) + (2 * Ichy (2 * y) + 4 * Aconst ^ 2))) := by
  rw [En]
  congr 1
  have hpt : ∀ w : ℝ, c2 w * ‖Fsum x w + Pterm t y w‖ ^ 2
      = c2 w * ((∑ j, ∑ k, Real.cos ((x j - x k) * w))
        + ((∑ j, 4 * (Real.cosh (y * w) * Real.cos ((x j - t) * w)))
          + (2 * (Real.cosh (2 * y * w) - 1) + 4))) := by
    intro w; rw [normSq_FP]
  rw [intervalIntegral.integral_congr (g := fun w => c2 w * ((∑ j, ∑ k, Real.cos ((x j - x k) * w))
        + ((∑ j, 4 * (Real.cosh (y * w) * Real.cos ((x j - t) * w)))
          + (2 * (Real.cosh (2 * y * w) - 1) + 4)))) (fun w _ => hpt w)]
  rw [interval_to_full, c2_int_add (by fun_prop) (by fun_prop),
    c2_int_add (by fun_prop) (by fun_prop), c2_int_add (by fun_prop) (by fun_prop)]
  congr 1
  · rw [c2_int_sum _ (fun j => by fun_prop)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [c2_int_sum _ (fun k => by fun_prop)]
    rfl
  congr 1
  · rw [c2_int_sum _ (fun j => by fun_prop)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [c2_int_const_mul]
    rfl
  congr 1
  · rw [c2_int_const_mul]
    rfl
  · have : ∀ w : ℝ, c2 w * (4:ℝ) = 4 * c2 w := fun w => by ring
    simp_rw [this]
    rw [integral_const_mul, c2_total]

/-- The diagonal lower bound `∑_{j,k} Icos (x j - x k) ≥ n * A²`: the off-diagonal terms of the
on-line interaction energy are nonnegative. -/
lemma diag_bound {n : ℕ} (x : Fin n → ℝ) :
    (n : ℝ) * Aconst ^ 2 ≤ ∑ j, ∑ k, Icos (x j - x k) := by
  have hterm : ∀ j : Fin n, Aconst ^ 2 ≤ ∑ k, Icos (x j - x k) := by
    intro j
    have hmem : j ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ j
    have := Finset.single_le_sum (f := fun k => Icos (x j - x k))
      (fun k _ => Icos_nonneg _) hmem
    simpa [Icos_zero] using this
  calc (n : ℝ) * Aconst ^ 2 = ∑ _j : Fin n, Aconst ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ ∑ j, ∑ k, Icos (x j - x k) := Finset.sum_le_sum (fun j _ => hterm j)

end Retention
