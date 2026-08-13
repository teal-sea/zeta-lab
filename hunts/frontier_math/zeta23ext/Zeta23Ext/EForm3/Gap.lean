import Zeta23Ext.EForm3.ClosedForm

/-!
# The retention gap identity

We expand `E[F + P] - E[F]` into the diagonal gain `2 ĝ(2y)^2 + 2 A^2` and the cross terms
`4 ∑_j (Qre y s_j ^ 2 - Qim y s_j ^ 2)`, and deduce the retention inequality from a bound
on the total damage `∑_j Qim y s_j ^ 2`.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

/-! ### More on `c2` -/

lemma c2_zero_of_one_le {w : ℝ} (hw : 1 ≤ |w|) : c2 w = 0 := by
  unfold c2
  have hsub : {u : ℝ | g u * g (u + w) ≠ 0} ⊆ {(-w/2)} := by
    intro u hu
    simp only [Set.mem_setOf_eq, ne_eq, mul_eq_zero, not_or] at hu
    have h1 : |u| ≤ 1/2 := g_support hu.1
    have h2 : |u + w| ≤ 1/2 := g_support hu.2
    have h3 : |w| ≤ |u| + |u + w| := by
      have hrw : w = -u + (u + w) := by ring
      calc |w| = |-u + (u + w)| := by rw [← hrw]
        _ ≤ |-u| + |u + w| := abs_add_le _ _
        _ = |u| + |u + w| := by rw [abs_neg]
    have h4 : |u| = 1/2 := by
      rcases abs_le.1 h1 with ⟨_, _⟩
      rcases abs_le.1 h2 with ⟨_, _⟩
      linarith [le_abs_self u, neg_abs_le u]
    have h5 : |u + w| = 1/2 := by linarith
    -- from |u| = |u+w| = 1/2 and |w| = 1 we get u = -w/2
    simp only [Set.mem_singleton_iff]
    have hw1 : |w| = 1 := le_antisymm (by linarith) hw
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hw1 with hwe | hwe <;>
      rcases abs_eq (by norm_num : (0:ℝ) ≤ 1/2) |>.1 h4 with hue | hue <;>
        rw [hwe, hue] at h5 ⊢ <;> (try norm_num at h5) <;> (try norm_num)
  have : ∀ᵐ u : ℝ, g u * g (u + w) = 0 := by
    rw [ae_iff]
    exact measure_mono_null hsub (by simp)
  rw [integral_eq_zero_of_ae this]

lemma c2_le_one (w : ℝ) : c2 w ≤ 1 := by
  unfold c2
  have hmaj : ∀ u : ℝ, g u * g (u + w) ≤ Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℝ)) u := by
    intro u
    by_cases h : u ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [Set.indicator_of_mem h]
      calc g u * g (u + w) ≤ 1 * 1 :=
            mul_le_mul (g_le_one u) (g_le_one _) (g_nonneg _) zero_le_one
        _ = 1 := by norm_num
    · rw [Set.indicator_of_notMem h]
      have : ¬ |u| ≤ 1/2 := by
        rw [Set.mem_Icc] at h
        push_neg at h
        rw [abs_le]; push_neg; intro hh; exact h (by linarith)
      rw [g_of_not_mem this, zero_mul]
  have hint : Integrable (Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := (1:ℝ)) (hs := volume_Icc_ne_top _ _))
  have hgi : Integrable (fun u => g u * g (u + w)) := by
    refine integrable_of_bound (g_measurable.mul (g_measurable.comp (measurable_id.add_const w)))
      (1/2) 1 (fun u => ?_) (fun u hu => ?_)
    · rw [abs_mul, abs_of_nonneg (g_nonneg _), abs_of_nonneg (g_nonneg _)]
      calc g u * g (u + w) ≤ 1 * 1 :=
            mul_le_mul (g_le_one u) (g_le_one _) (g_nonneg _) zero_le_one
        _ = 1 := by norm_num
    · rw [g_zero_of_lt hu, zero_mul]
  calc ∫ u, g u * g (u + w) ≤ ∫ u, Set.indicator (Set.Icc (-(1/2):ℝ) (1/2)) (fun _ => (1:ℝ)) u :=
        integral_mono hgi hint hmaj
    _ = 1 := by
        rw [integral_indicator measurableSet_Icc]
        simp
        norm_num

lemma c2_abs_le_one (w : ℝ) : |c2 w| ≤ 1 := by
  rw [abs_of_nonneg (c2_nonneg w)]; exact c2_le_one w

/-- `c2` times a continuous function is integrable. -/
lemma integrable_c2_mul {k : ℝ → ℝ} (hk : Continuous k) : Integrable (fun w => c2 w * k w) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hk.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by norm_num))
  refine integrable_of_bound (c2_measurable.mul hk.measurable) 1 C (fun w => ?_) (fun w hw => ?_)
  · by_cases h : |w| ≤ 1
    · have : w ∈ Set.Icc (-1:ℝ) 1 := by rw [Set.mem_Icc]; rw [abs_le] at h; exact h
      rw [abs_mul]
      calc |c2 w| * |k w| ≤ 1 * C :=
            mul_le_mul (c2_abs_le_one w) (by simpa using hC w this) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · rw [c2_zero_of_one_le (le_of_lt (not_le.1 h)), zero_mul]; simpa using hC0
  · rw [c2_zero_of_one_le (le_of_lt hw), zero_mul]

/-- The energy is a full-line integral. -/
lemma Eng_eq (G : ℝ → ℂ) :
    Eng G = (1 / Aconst ^ 2) * ∫ w : ℝ, c2 w * ‖G w‖ ^ 2 := by
  unfold Eng
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro w hw
  have : 1 ≤ |w| := by
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hw
    rcases hw with h | h
    · calc (1:ℝ) ≤ -w := by linarith
        _ ≤ |w| := neg_le_abs w
    · calc (1:ℝ) ≤ w := le_of_lt h
        _ ≤ |w| := le_abs_self w
  rw [c2_zero_of_one_le this, zero_mul]

/-! ### Complex algebra -/

lemma exp_I_re (θ : ℝ) : (Complex.exp (Complex.I * θ)).re = Real.cos θ := by
  rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re θ

lemma norm_exp_I (θ : ℝ) : ‖Complex.exp (Complex.I * θ)‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma exp_mul_conj_re (a b : ℝ) :
    (Complex.exp (Complex.I * a) * (starRingEnd ℂ) (Complex.exp (Complex.I * b))).re
      = Real.cos (a - b) := by
  rw [← Complex.exp_conj, ← Complex.exp_add,
    show (Complex.I * (a:ℂ)) + (starRingEnd ℂ) (Complex.I * (b:ℂ)) = Complex.I * ((a - b : ℝ) : ℂ) by
      simp [Complex.ext_iff]; ring]
  exact exp_I_re _

lemma normsq_re (z : ℂ) : ‖z‖^2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj]
  simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

lemma normSq_add_re (z p : ℂ) : ‖z + p‖^2 = ‖z‖^2 + 2*(z * (starRingEnd ℂ) p).re + ‖p‖^2 := by
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_add]; ring

lemma norm_P_sq (y t w : ℝ) : ‖Pfun y t w‖^2 = 4 * Real.cosh (y*w)^2 := by
  unfold Pfun
  rw [norm_mul, norm_mul, Complex.norm_exp]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.cosh_pos _))]
  simp
  ring

lemma norm_F_sq (n : ℕ) (x : ℕ → ℝ) (w : ℝ) :
    ‖Fsum n x w‖^2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Real.cos ((x j - x k) * w) := by
  unfold Fsum
  rw [normsq_re, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show ((x j : ℂ) * w) = (((x j * w : ℝ)) : ℂ) by push_cast; ring,
      show ((x k : ℂ) * w) = (((x k * w : ℝ)) : ℂ) by push_cast; ring, exp_mul_conj_re]
  congr 1; ring

lemma cross_re (n : ℕ) (x : ℕ → ℝ) (y t w : ℝ) :
    (Fsum n x w * (starRingEnd ℂ) (Pfun y t w)).re
      = 2 * Real.cosh (y*w) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w) := by
  unfold Fsum Pfun
  rw [Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_mul, map_mul, Complex.conj_ofReal,
    show Complex.exp (Complex.I * ((x j : ℂ) * w)) * ((starRingEnd ℂ) 2 * ((Real.cosh (y*w) : ℝ) : ℂ)
      * (starRingEnd ℂ) (Complex.exp (Complex.I * ((t:ℂ) * w))))
      = ((2 * Real.cosh (y*w) : ℝ) : ℂ) * (Complex.exp (Complex.I * (((x j * w : ℝ)) : ℂ))
        * (starRingEnd ℂ) (Complex.exp (Complex.I * (((t * w : ℝ)) : ℂ)))) by
      simp only [map_ofNat]; push_cast; ring,
    Complex.re_ofReal_mul, exp_mul_conj_re]
  congr 2
  ring

/-! ### Consequences of the master identity -/

lemma integral_c2_cosh_cos (a b : ℝ) :
    ∫ w : ℝ, c2 w * (Real.cosh (a*w) * Real.cos (b*w)) = Qre a b ^ 2 - Qim a b ^ 2 := master a b

lemma integral_c2_cos (b : ℝ) : ∫ w : ℝ, c2 w * Real.cos (b * w) = Qre 0 b ^ 2 := by
  have := master 0 b
  simp only [zero_mul, Real.cosh_zero, one_mul, Qim_zero_left] at this
  simpa using this

lemma integral_c2_cosh (a : ℝ) : ∫ w : ℝ, c2 w * Real.cosh (a * w) = Qre a 0 ^ 2 := by
  have := master a 0
  simp only [zero_mul, Real.cos_zero, mul_one, Qim_zero_right] at this
  simpa using this

lemma integral_c2 : ∫ w : ℝ, c2 w = Aconst ^ 2 := by
  have := integral_c2_cos 0
  simp only [zero_mul, Real.cos_zero, mul_one] at this
  rw [this, Qre_zero_zero]

lemma integrable_c2_cos (b : ℝ) : Integrable (fun w => c2 w * Real.cos (b * w)) :=
  integrable_c2_mul (by fun_prop)

lemma integrable_c2_cosh_cos (a b : ℝ) :
    Integrable (fun w => c2 w * (Real.cosh (a*w) * Real.cos (b*w))) :=
  integrable_c2_mul (by fun_prop)

/-! ### The energy of `F` -/

theorem energy_F (n : ℕ) (x : ℕ → ℝ) :
    Eng (Fsum n x)
      = (1 / Aconst ^ 2) * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2 := by
  rw [Eng_eq]
  congr 1
  have hpt : ∀ w : ℝ, c2 w * ‖Fsum n x w‖ ^ 2
      = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c2 w * Real.cos ((x j - x k) * w) := by
    intro w
    rw [norm_F_sq, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [Finset.mul_sum])
  simp_rw [hpt]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _
    (fun k _ => integrable_c2_cos (x j - x k)))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finset_sum _ (fun k _ => integrable_c2_cos (x j - x k))]
  exact Finset.sum_congr rfl (fun k _ => integral_c2_cos _)

theorem energy_F_ge (n : ℕ) (x : ℕ → ℝ) : (n : ℝ) ≤ Eng (Fsum n x) := by
  rw [energy_F]
  have hA := Aconst_ne_zero
  have hA2 : (0:ℝ) < Aconst ^ 2 := pow_pos Aconst_pos 2
  have hdiag : (n : ℝ) * Aconst ^ 2
      ≤ ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2 := by
    have hstep : ∀ j ∈ Finset.range n,
        Aconst ^ 2 ≤ ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2 := by
      intro j hj
      have h0 : Qre 0 (x j - x j) ^ 2 ≤ ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2 :=
        Finset.single_le_sum (f := fun k => Qre 0 (x j - x k) ^ 2)
          (fun k _ => sq_nonneg _) hj
      rwa [sub_self, Qre_zero_zero] at h0
    calc (n : ℝ) * Aconst ^ 2
        = ∑ _j ∈ Finset.range n, Aconst ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hstep
  have : (1 / Aconst ^ 2) * ((n:ℝ) * Aconst ^ 2)
      ≤ (1 / Aconst ^ 2) * ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2 :=
    mul_le_mul_of_nonneg_left hdiag (one_div_nonneg.2 hA2.le)
  calc (n:ℝ) = (1 / Aconst ^ 2) * ((n:ℝ) * Aconst ^ 2) := by field_simp
    _ ≤ _ := this

/-! ### The energy of `F + P` -/

theorem energy_FP (n : ℕ) (x : ℕ → ℝ) (y t : ℝ) :
    Eng (fun w => Fsum n x w + Pfun y t w)
      = (1 / Aconst ^ 2) * ((∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Qre 0 (x j - x k) ^ 2)
          + 4 * ∑ j ∈ Finset.range n, (Qre y (x j - t) ^ 2 - Qim y (x j - t) ^ 2)
          + (2 * Aconst ^ 2 + 2 * Qre (2*y) 0 ^ 2)) := by
  rw [Eng_eq]
  congr 1
  have hpt : ∀ w : ℝ, c2 w * ‖Fsum n x w + Pfun y t w‖ ^ 2
      = (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c2 w * Real.cos ((x j - x k) * w))
        + (∑ j ∈ Finset.range n,
            4 * (c2 w * (Real.cosh (y*w) * Real.cos ((x j - t) * w))))
        + (2 * c2 w + 2 * (c2 w * Real.cosh ((2*y)*w))) := by
    intro w
    have hch : 4 * Real.cosh (y*w)^2 = 2 + 2 * Real.cosh ((2*y)*w) := by
      have h := Real.cosh_two_mul (y*w)
      rw [show (2*y)*w = 2*(y*w) by ring, h]
      have := Real.cosh_sq_sub_sinh_sq (y*w)
      linarith
    have e1 : c2 w * (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Real.cos ((x j - x k) * w))
        = ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c2 w * Real.cos ((x j - x k) * w) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => Finset.mul_sum _ _ _)
    have e2 : c2 w * (2 * (2 * Real.cosh (y*w) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w)))
        = ∑ j ∈ Finset.range n, 4 * (c2 w * (Real.cosh (y*w) * Real.cos ((x j - t) * w))) := by
      rw [show c2 w * (2 * (2 * Real.cosh (y*w) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w)))
            = (4 * (c2 w * Real.cosh (y*w))) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w) by
          ring, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [normSq_add_re, norm_F_sq, cross_re, norm_P_sq, hch]
    rw [show c2 w * (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Real.cos ((x j - x k) * w)
          + 2 * (2 * Real.cosh (y*w) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w))
          + (2 + 2 * Real.cosh ((2*y)*w)))
        = c2 w * (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, Real.cos ((x j - x k) * w))
          + c2 w * (2 * (2 * Real.cosh (y*w) * ∑ j ∈ Finset.range n, Real.cos ((x j - t) * w)))
          + (2 * c2 w + 2 * (c2 w * Real.cosh ((2*y)*w))) by ring]
    rw [e1, e2]
  simp_rw [hpt]
  have i1 : Integrable (fun w : ℝ =>
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c2 w * Real.cos ((x j - x k) * w)) :=
    integrable_finset_sum _ (fun j _ => integrable_finset_sum _
      (fun k _ => integrable_c2_cos (x j - x k)))
  have i2 : Integrable (fun w : ℝ =>
      ∑ j ∈ Finset.range n, 4 * (c2 w * (Real.cosh (y*w) * Real.cos ((x j - t) * w)))) :=
    integrable_finset_sum _ (fun j _ => (integrable_c2_cosh_cos y (x j - t)).const_mul 4)
  have i3 : Integrable (fun w : ℝ => 2 * c2 w + 2 * (c2 w * Real.cosh ((2*y)*w))) := by
    refine Integrable.add ?_ ?_
    · exact (integrable_c2_mul (k := fun _ => (1:ℝ)) continuous_const).congr
        (Filter.Eventually.of_forall (fun w => by ring)) |>.const_mul 2
    · exact ((integrable_c2_mul (k := fun w => Real.cosh ((2*y)*w)) (by fun_prop))).const_mul 2
  have i12 : Integrable (fun w : ℝ =>
      (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range n, c2 w * Real.cos ((x j - x k) * w))
      + ∑ j ∈ Finset.range n, 4 * (c2 w * (Real.cosh (y*w) * Real.cos ((x j - t) * w)))) :=
    i1.add i2
  rw [integral_add i12 i3, integral_add i1 i2]
  congr 1
  · congr 1
    · rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _
        (fun k _ => integrable_c2_cos (x j - x k)))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_finset_sum _ (fun k _ => integrable_c2_cos (x j - x k))]
      exact Finset.sum_congr rfl (fun k _ => integral_c2_cos _)
    · rw [integral_finset_sum _ (fun j _ => (integrable_c2_cosh_cos y (x j - t)).const_mul 4),
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, integral_c2_cosh_cos]
  · rw [integral_add ((integrable_c2_mul (k := fun _ => (1:ℝ)) continuous_const).congr
        (Filter.Eventually.of_forall (fun w => by ring)) |>.const_mul 2)
      (((integrable_c2_mul (k := fun w => Real.cosh ((2*y)*w)) (by fun_prop))).const_mul 2),
      integral_const_mul, integral_const_mul, integral_c2, integral_c2_cosh]

end Retention
