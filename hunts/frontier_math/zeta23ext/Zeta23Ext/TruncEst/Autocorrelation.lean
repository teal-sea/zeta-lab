import Zeta23Ext.TruncEst.Kernel

/-!
# `c2` really is the autocorrelation of `g`, and `A = ∫ g`

`PROBLEM.md` defines `c2` as the autocorrelation `c2 w = ∫ g u * g (u - w) du`
of the windowed cosine `g`, and states its closed form on `[0,1]`.  Here we
close that loop: the closed-form definition `TruncEst.c2` used throughout the
development agrees with the autocorrelation integral, and `A = ∫ g`.
-/

noncomputable section

open Real MeasureTheory intervalIntegral

namespace TruncEst

lemma g_even (u : ℝ) : g (-u) = g u := by
  simp [g, abs_neg, mul_neg, Real.cos_neg]

lemma g_eq_zero {u : ℝ} (h : 1/2 < |u|) : g u = 0 := by
  rw [g, if_neg (by linarith)]

lemma g_eq_cos {u : ℝ} (h : |u| ≤ 1/2) : g u = Real.cos (Real.sqrt 2 * u) := by
  rw [g, if_pos h]

/-- The autocorrelation integral of `g`. -/
def AC (w : ℝ) : ℝ := ∫ u : ℝ, g u * g (u - w)

lemma AC_even (w : ℝ) : AC (-w) = AC w := by
  have h1 : (∫ u : ℝ, g u * g (u - -w)) = ∫ u : ℝ, (fun v : ℝ => g (v - w) * g v) (u + w) := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    simp only [sub_neg_eq_add, add_sub_cancel_right]
  rw [AC, h1, integral_add_right_eq_self (fun v : ℝ => g (v - w) * g v) w, AC]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))

/-- Off the diagonal band the integrand vanishes. -/
lemma autocorr_integrand_eq_zero {w u : ℝ} (hu : u ∉ Set.Icc (w - 1/2) (1/2)) :
    g u * g (u - w) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  rcases hu with h | h
  · have : g (u - w) = 0 := by
      apply g_eq_zero
      rw [abs_of_nonpos (by linarith)]
      linarith
    rw [this, mul_zero]
  · have : g u = 0 := by
      apply g_eq_zero
      rw [abs_of_nonneg (by linarith)]
      linarith
    rw [this, zero_mul]

lemma hasDerivAt_antideriv (w u : ℝ) :
    HasDerivAt (fun u : ℝ => u * Real.cos (Real.sqrt 2 * w) / 2
        + Real.sin (Real.sqrt 2 * (2 * u - w)) / (4 * Real.sqrt 2))
      (Real.cos (Real.sqrt 2 * u) * Real.cos (Real.sqrt 2 * (u - w))) u := by
  have h1 : HasDerivAt (fun u : ℝ => u * Real.cos (Real.sqrt 2 * w) / 2)
      (Real.cos (Real.sqrt 2 * w) / 2) u := by
    simpa using ((hasDerivAt_id u).mul_const (Real.cos (Real.sqrt 2 * w))).div_const 2
  have hlin : HasDerivAt (fun u : ℝ => Real.sqrt 2 * (2 * u - w)) (Real.sqrt 2 * 2) u := by
    have : HasDerivAt (fun u : ℝ => 2 * u - w) 2 u := by
      simpa using ((hasDerivAt_id u).const_mul (2:ℝ)).sub_const w
    simpa using this.const_mul (Real.sqrt 2)
  have h2 : HasDerivAt (fun u : ℝ => Real.sin (Real.sqrt 2 * (2 * u - w)) / (4 * Real.sqrt 2))
      (Real.cos (Real.sqrt 2 * (2 * u - w)) * (Real.sqrt 2 * 2) / (4 * Real.sqrt 2)) u :=
    (hlin.sin).div_const _
  -- the function parts are defeq (`Pi.add` against the lambda); only the
  -- derivative differs, so `congr_deriv` replaces `convert`, and `symm`
  -- restores the orientation the rest of this block was written for.
  refine (h1.add h2).congr_deriv ?_
  symm
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  have hprod : Real.cos (Real.sqrt 2 * u) * Real.cos (Real.sqrt 2 * (u - w))
      = (Real.cos (Real.sqrt 2 * w) + Real.cos (Real.sqrt 2 * (2 * u - w))) / 2 := by
    have e1 : Real.sqrt 2 * w = Real.sqrt 2 * u - Real.sqrt 2 * (u - w) := by ring
    have e2 : Real.sqrt 2 * (2 * u - w) = Real.sqrt 2 * u + Real.sqrt 2 * (u - w) := by ring
    rw [e1, e2, Real.cos_sub, Real.cos_add]
    ring
  rw [hprod]
  field_simp
  ring

lemma autocorr_of_mem {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : AC w = c2core w := by
  have hle : w - 1/2 ≤ 1/2 := by linarith
  have hset : AC w = ∫ u in Set.Icc (w - 1/2) (1/2), g u * g (u - w) :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => autocorr_integrand_eq_zero hu)).symm
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  have hcongr : (∫ u in (w - 1/2)..(1/2), g u * g (u - w))
      = ∫ u in (w - 1/2)..(1/2),
          Real.cos (Real.sqrt 2 * u) * Real.cos (Real.sqrt 2 * (u - w)) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le hle, Set.mem_Icc] at hu
    have hu1 : |u| ≤ 1/2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hu2 : |u - w| ≤ 1/2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    rw [g_eq_cos hu1, g_eq_cos hu2]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_antideriv w u)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  have hsin : Real.sin (Real.sqrt 2 * (2 * (w - 1/2) - w)) = -Real.sin (Real.sqrt 2 * (1 - w)) := by
    rw [show Real.sqrt 2 * (2 * (w - 1/2) - w) = -(Real.sqrt 2 * (1 - w)) by ring, Real.sin_neg]
  rw [hsin, show Real.sqrt 2 * (2 * (1/2 : ℝ) - w) = Real.sqrt 2 * (1 - w) by ring]
  unfold c2core
  field_simp
  ring

lemma autocorr_of_one_lt {w : ℝ} (h : 1 < w) : AC w = 0 := by
  have hzero : ∀ u : ℝ, g u * g (u - w) = 0 := by
    intro u
    by_cases hu : |u| ≤ 1/2
    · have : g (u - w) = 0 := by
        apply g_eq_zero
        rw [abs_of_nonpos (by rw [abs_le] at hu; linarith [hu.1, hu.2])]
        rw [abs_le] at hu
        linarith [hu.1, hu.2]
      rw [this, mul_zero]
    · rw [g_eq_zero (by linarith [not_le.1 hu]), zero_mul]
  rw [AC]
  simp [hzero]

/-- **`c2` is the autocorrelation of `g`.** -/
theorem c2_eq_autocorrelation (w : ℝ) : c2 w = ∫ u : ℝ, g u * g (u - w) := by
  have key : ∀ v : ℝ, 0 ≤ v → c2 v = AC v := by
    intro v hv
    rcases le_or_gt v 1 with h1 | h1
    · rw [c2_of_nonneg hv h1, autocorr_of_mem hv h1]
    · rw [autocorr_of_one_lt h1, c2_eq_zero_of_one_lt (by rw [abs_of_nonneg hv]; exact h1)]
  rcases le_or_gt 0 w with hw | hw
  · exact key w hw
  · have h := key (-w) (by linarith)
    rw [c2_neg, AC_even] at h
    exact h

/-- `A = ∫ g`. -/
theorem integral_g : ∫ u : ℝ, g u = A := by
  have hsupp : ∀ u ∉ Set.Icc (-(1/2) : ℝ) (1/2), g u = 0 := by
    intro u hu
    simp only [Set.mem_Icc, not_and_or, not_le] at hu
    apply g_eq_zero
    rcases hu with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hset : (∫ u : ℝ, g u) = ∫ u in Set.Icc (-(1/2) : ℝ) (1/2), g u :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2)]
  have hcongr : (∫ u in (-(1/2) : ℝ)..(1/2), g u)
      = ∫ u in (-(1/2) : ℝ)..(1/2), Real.cos (Real.sqrt 2 * u) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le (by norm_num : (-(1/2) : ℝ) ≤ 1/2), Set.mem_Icc] at hu
    exact g_eq_cos (by rw [abs_le]; exact ⟨by linarith [hu.1], hu.2⟩)
  have hderiv : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.sin (Real.sqrt 2 * u) / Real.sqrt 2)
      (Real.cos (Real.sqrt 2 * u)) u := by
    intro u
    have hlin : HasDerivAt (fun u : ℝ => Real.sqrt 2 * u) (Real.sqrt 2) u := hd_lin2 u
    have h := (hlin.sin).div_const (Real.sqrt 2)
    refine h.congr_deriv ?_
    symm
    have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
    field_simp
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hderiv u)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt sqrt2_pos
  have hhalf : Real.sqrt 2 * (-(1/2) : ℝ) = -(Real.sqrt 2 * (1/2)) := by ring
  rw [hhalf, Real.sin_neg]
  have hval : Real.sqrt 2 * (1/2 : ℝ) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff hne]
    nlinarith [sqrt2_mul]
  rw [hval, A]
  field_simp
  rw [sqrt2_sq]
  ring

end TruncEst
