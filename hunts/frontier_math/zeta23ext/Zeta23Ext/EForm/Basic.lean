import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Retention

/-- The window `g(u) = cos (√2 u)` on `|u| ≤ 1/2`, and `0` outside. -/
noncomputable def gker (u : ℝ) : ℝ := if |u| ≤ 1/2 then Real.cos (Real.sqrt 2 * u) else 0

/-- The autocorrelation `c₂` of `gker`. -/
noncomputable def c2 (w : ℝ) : ℝ := ∫ u : ℝ, gker u * gker (u - w)

/-- `A = √2 sin (1/√2) = ∫ gker`. -/
noncomputable def Aconst : ℝ := Real.sqrt 2 * Real.sin (1 / Real.sqrt 2)

/-- The bandlimited energy functional. -/
noncomputable def En (G : ℝ → ℂ) : ℝ :=
  (1 / Aconst ^ 2) * ∫ w in (-1:ℝ)..1, c2 w * ‖G w‖ ^ 2

lemma gker_of_le {u : ℝ} (hu : |u| ≤ 1/2) : gker u = Real.cos (Real.sqrt 2 * u) := by
  rw [gker, if_pos hu]

lemma gker_of_gt {u : ℝ} (hu : 1/2 < |u|) : gker u = 0 := by
  rw [gker, if_neg (not_le.2 hu)]

lemma gker_nonneg (u : ℝ) : 0 ≤ gker u := by
  unfold gker
  split_ifs with h
  · apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have : |Real.sqrt 2 * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
        nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2, abs_nonneg u]
      have h1 : -(1:ℝ) ≤ Real.sqrt 2 * u := by
        cases' abs_le.1 this with h1 h2; linarith
      nlinarith [Real.pi_gt_three]
    · have : |Real.sqrt 2 * u| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
        nlinarith [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0), Real.sqrt_nonneg 2, abs_nonneg u]
      have h2 : Real.sqrt 2 * u ≤ 1 := (abs_le.1 this).2
      nlinarith [Real.pi_gt_three]
  · exact le_refl 0

lemma gker_le_one (u : ℝ) : gker u ≤ 1 := by
  unfold gker
  split_ifs with h
  · exact Real.cos_le_one _
  · norm_num

lemma gker_even (u : ℝ) : gker (-u) = gker u := by
  unfold gker
  simp [abs_neg, Real.cos_neg, mul_neg]

lemma c2_nonneg (w : ℝ) : 0 ≤ c2 w :=
  MeasureTheory.integral_nonneg fun u => mul_nonneg (gker_nonneg u) (gker_nonneg _)

open MeasureTheory

lemma gker_meas : Measurable gker := by
  unfold gker
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le (by fun_prop) measurable_const
  · fun_prop

lemma gker_abs_le_one (u : ℝ) : |gker u| ≤ 1 :=
  abs_le.2 ⟨by linarith [gker_nonneg u], gker_le_one u⟩

lemma indicator_half_integrable (M : ℝ) :
    Integrable ((Set.Icc (-(1/2):ℝ) (1/2)).indicator (fun _ => M)) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  refine integrableOn_const (C := M) ?_ ?_
  · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  · simp

lemma integral_indicator_half (M : ℝ) :
    ∫ u : ℝ, (Set.Icc (-(1/2):ℝ) (1/2)).indicator (fun _ => M) u = M := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const]
  simp [Real.volume_real_Icc]
  ring

lemma gker_mul_norm_le {f : ℝ → ℝ} {M : ℝ} (hM : ∀ u, |u| ≤ 1/2 → |f u| ≤ M) (hM0 : 0 ≤ M)
    (u : ℝ) : ‖gker u * f u‖ ≤ (Set.Icc (-(1/2):ℝ) (1/2)).indicator (fun _ => M) u := by
  by_cases hu : |u| ≤ 1/2
  · have humem : u ∈ Set.Icc (-(1/2):ℝ) (1/2) := by
      rcases abs_le.1 hu with ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    rw [Set.indicator_of_mem humem, Real.norm_eq_abs, abs_mul]
    calc |gker u| * |f u| ≤ 1 * M :=
          mul_le_mul (gker_abs_le_one u) (hM u hu) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  · rw [gker_of_gt (not_le.1 hu), zero_mul, norm_zero]
    by_cases hmem : u ∈ Set.Icc (-(1/2):ℝ) (1/2)
    · rw [Set.indicator_of_mem hmem]; exact hM0
    · rw [Set.indicator_of_notMem hmem]

lemma gker_mul_integrable_aux {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ u, |u| ≤ 1/2 → |f u| ≤ M) (hM0 : 0 ≤ M) : Integrable (fun u => gker u * f u) :=
  Integrable.mono' (indicator_half_integrable M) ((gker_meas.mul hf).aestronglyMeasurable)
    (Filter.Eventually.of_forall (gker_mul_norm_le hM hM0))

lemma gker_mul_integrable {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun u => gker u * f u) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-(1/2):ℝ)) (b := 1/2)).exists_bound_of_continuousOn
    hf.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0 (by norm_num))
  refine gker_mul_integrable_aux hf.measurable (M := M) (fun u hu => ?_) hM0
  rcases abs_le.1 hu with ⟨h1, h2⟩
  exact hM u ⟨by linarith, by linarith⟩

lemma gker_integrable : Integrable gker := by
  have := gker_mul_integrable (f := fun _ : ℝ => (1:ℝ)) continuous_const
  simpa using this

lemma c2_integrand_integrable (w : ℝ) : Integrable (fun u => gker u * gker (u - w)) :=
  gker_mul_integrable_aux (gker_meas.comp (measurable_id.sub_const w))
    (M := 1) (fun _ _ => gker_abs_le_one _) zero_le_one

lemma c2_le_one (w : ℝ) : c2 w ≤ 1 := by
  have h := norm_integral_le_of_norm_le (μ := volume)
    (indicator_half_integrable (1:ℝ)) (f := fun u => gker u * gker (u - w))
    (Filter.Eventually.of_forall
      (gker_mul_norm_le (f := fun u => gker (u - w)) (M := 1)
        (fun u _ => gker_abs_le_one _) zero_le_one))
  rw [integral_indicator_half] at h
  have : |c2 w| ≤ 1 := by rw [c2, ← Real.norm_eq_abs]; exact h
  exact le_trans (le_abs_self _) this

lemma c2_meas : Measurable c2 := by
  have hsm : StronglyMeasurable (fun p : ℝ × ℝ => gker p.2 * gker (p.2 - p.1)) :=
    ((gker_meas.comp measurable_snd).mul
      (gker_meas.comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right' hsm).measurable

lemma c2_zero_of_gt {w : ℝ} (hw : 1 < |w|) : c2 w = 0 := by
  rw [c2]
  have hz : ∀ u : ℝ, gker u * gker (u - w) = 0 := by
    intro u
    by_cases hu : |u| ≤ 1/2
    · have h1 : |u| - |w| ≤ |u - w| := by
        have := abs_sub_abs_le_abs_sub u w
        linarith
      have h2 : |w| - |u| ≤ |u - w| := by
        have := abs_sub_abs_le_abs_sub w u
        rw [abs_sub_comm w u] at this
        linarith
      rw [gker_of_gt (by linarith : 1/2 < |u - w|), mul_zero]
    · rw [gker_of_gt (not_le.1 hu), zero_mul]
  simp [hz]

lemma c2_mul_integrable {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun w => c2 w * f w) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0 (by norm_num))
  refine Integrable.mono' (g := (Set.Icc (-1:ℝ) 1).indicator (fun _ => M)) ?_
    ((c2_meas.mul hf.measurable).aestronglyMeasurable) ?_
  · rw [integrable_indicator_iff measurableSet_Icc]
    refine integrableOn_const (C := M) ?_ ?_
    · rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    · simp
  · filter_upwards with w
    by_cases hw : |w| ≤ 1
    · have hmem : w ∈ Set.Icc (-1:ℝ) 1 := by
        rcases abs_le.1 hw with ⟨h1, h2⟩; exact ⟨h1, h2⟩
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs, abs_mul]
      calc |c2 w| * |f w| ≤ 1 * M :=
            mul_le_mul (abs_le.2 ⟨by linarith [c2_nonneg w], c2_le_one w⟩) (hM w hmem)
              (abs_nonneg _) zero_le_one
        _ = M := one_mul M
    · rw [c2_zero_of_gt (not_le.1 hw), zero_mul, norm_zero]
      by_cases hmem : w ∈ Set.Icc (-1:ℝ) 1
      · rw [Set.indicator_of_mem hmem]; exact hM0
      · rw [Set.indicator_of_notMem hmem]

lemma interval_to_full (f : ℝ → ℝ) :
    ∫ w in (-1:ℝ)..1, c2 w * f w = ∫ w : ℝ, c2 w * f w := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
  have : 1 < |x| := by
    by_contra h
    push_neg at h
    exact hx (by rcases abs_le.1 h with ⟨h1, h2⟩; exact ⟨h1, h2⟩)
  rw [c2_zero_of_gt this, zero_mul]

end Retention
