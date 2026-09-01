import ZetaLean.WScratch.EForm3.Defs

/-!
# Integrability infrastructure

All integrands appearing in the development are bounded, measurable and supported in a
compact set, hence integrable.  This file collects the corresponding lemmas.
-/

open scoped BigOperators Real
open MeasureTheory

namespace Retention

lemma volume_Icc_ne_top (a b : ℝ) : volume (Set.Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- A measurable function bounded by `C` and supported in `[-R, R]` is integrable. -/
lemma integrable_of_bound {f : ℝ → ℝ} (hf : Measurable f) (R C : ℝ)
    (hC : ∀ u, |f u| ≤ C) (hsupp : ∀ u, R < |u| → f u = 0) : Integrable f := by
  refine Integrable.mono' (g := Set.indicator (Set.Icc (-R) R) (fun _ => C))
    ((integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := C) (hs := volume_Icc_ne_top _ _)))
    hf.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  intro u
  by_cases h : u ∈ Set.Icc (-R) R
  · rw [Set.indicator_of_mem h]
    simpa using hC u
  · rw [Set.indicator_of_notMem h, hsupp u ?_]
    · simp
    · simp only [Set.mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs u)
      · exact lt_of_lt_of_le h (le_abs_self u)

/-- Any continuous function is bounded on `[-1/2, 1/2]`. -/
lemma exists_bound_half (k : ℝ → ℝ) (hk : Continuous k) : ∃ C, ∀ u, |u| ≤ 1/2 → |k u| ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := (-1/2 : ℝ)) (b := 1/2)).exists_bound_of_continuousOn hk.continuousOn
  refine ⟨C, fun u hu => ?_⟩
  have : u ∈ Set.Icc (-1/2 : ℝ) (1/2) := by
    rw [Set.mem_Icc]; constructor <;> [linarith [neg_abs_le u]; linarith [le_abs_self u]]
  simpa using hC u this

/-- `g` multiplied by any continuous function is integrable. -/
lemma integrable_g_mul {k : ℝ → ℝ} (hk : Continuous k) : Integrable (fun u => g u * k u) := by
  obtain ⟨C, hC⟩ := exists_bound_half k hk
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 (by norm_num))
  refine integrable_of_bound (g_measurable.mul hk.measurable) (1/2) C (fun u => ?_) (fun u hu => ?_)
  · by_cases h : |u| ≤ 1/2
    · rw [abs_mul]
      calc |g u| * |k u| ≤ 1 * C :=
            mul_le_mul (g_abs_le_one u) (hC u h) (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    · rw [g_of_not_mem h]; simpa using hC0
  · rw [g_zero_of_lt hu, zero_mul]

lemma integrable_g : Integrable g := by
  have := integrable_g_mul (k := fun _ => (1:ℝ)) continuous_const
  simpa using this

/-- `g` multiplied by a bounded measurable function is integrable. -/
lemma integrable_g_mul_bdd {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ}
    (hC : ∀ u, |k u| ≤ C) : Integrable (fun u => g u * k u) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0)
  refine integrable_of_bound (g_measurable.mul hk) (1/2) C (fun u => ?_) (fun u hu => ?_)
  · rw [abs_mul]
    calc |g u| * |k u| ≤ 1 * C :=
          mul_le_mul (g_abs_le_one u) (hC u) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [g_zero_of_lt hu, zero_mul]

/-! ### The autocorrelation -/

lemma c2_nonneg (w : ℝ) : 0 ≤ c2 w :=
  integral_nonneg (fun u => mul_nonneg (g_nonneg u) (g_nonneg _))

lemma c2_zero_of_lt {w : ℝ} (hw : 1 < |w|) : c2 w = 0 := by
  unfold c2
  have : ∀ u : ℝ, g u * g (u + w) = 0 := by
    intro u
    by_cases h : |u| ≤ 1/2
    · have : 1/2 < |u + w| := by
        have h1 : |w| ≤ |u| + |u + w| := by
          have : w = -u + (u + w) := by ring
          calc |w| = |-u + (u + w)| := by rw [← this]
            _ ≤ |-u| + |u + w| := abs_add_le _ _
            _ = |u| + |u + w| := by rw [abs_neg]
        linarith
      rw [g_zero_of_lt this, mul_zero]
    · rw [g_of_not_mem h, zero_mul]
  simp [this]

lemma c2_measurable : Measurable c2 := by
  unfold c2
  have : Measurable (Function.uncurry fun (w u : ℝ) => g u * g (u + w)) := by
    apply Measurable.mul
    · exact g_measurable.comp measurable_snd
    · exact g_measurable.comp (measurable_snd.add measurable_fst)
  exact (this.stronglyMeasurable.integral_prod_right').measurable

/-- Integrability of the two-dimensional integrand used for Fubini. -/
lemma integrable_prod_c2 {k : ℝ → ℝ} (hk : Continuous k) :
    Integrable (Function.uncurry fun (w u : ℝ) => g u * g (u + w) * k w)
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hk.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (by norm_num))
  set S : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1/2 : ℝ) (1/2) with hS
  have hSmeas : MeasurableSet S := measurableSet_Icc.prod measurableSet_Icc
  have hSfin : (volume.prod volume) S ≠ ⊤ := by
    rw [hS, Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_Icc_ne_top _ _) (volume_Icc_ne_top _ _)
  have hmeas : Measurable (Function.uncurry fun (w u : ℝ) => g u * g (u + w) * k w) := by
    apply Measurable.mul
    · exact (g_measurable.comp measurable_snd).mul (g_measurable.comp (measurable_snd.add measurable_fst))
    · exact hk.measurable.comp measurable_fst
  refine Integrable.mono' (g := Set.indicator S (fun _ => C))
    ((integrable_indicator_iff hSmeas).2 (integrableOn_const (C := C) (hs := hSfin)))
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
  rintro ⟨w, u⟩
  simp only [Function.uncurry_apply_pair]
  by_cases h : (w, u) ∈ S
  · rw [Set.indicator_of_mem h]
    have hw : |w| ≤ 1 := by
      have := h.1; rw [Set.mem_Icc] at this
      rw [abs_le]; exact ⟨this.1, this.2⟩
    have hkw : |k w| ≤ C := by
      have : w ∈ Set.Icc (-1:ℝ) 1 := by rw [Set.mem_Icc]; rw [abs_le] at hw; exact hw
      simpa using hC w this
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |g u| * |g (u + w)| * |k w| ≤ 1 * 1 * C := by
          apply mul_le_mul _ hkw (abs_nonneg _) (by norm_num)
          exact mul_le_mul (g_abs_le_one u) (g_abs_le_one _) (abs_nonneg _) zero_le_one
      _ = C := by ring
  · rw [Set.indicator_of_notMem h]
    have : g u * g (u + w) * k w = 0 := by
      rw [hS, Set.mem_prod] at h
      by_cases hu : |u| ≤ 1/2
      · by_cases hw : |w| ≤ 1
        · exfalso
          refine h ⟨by rw [Set.mem_Icc]; rw [abs_le] at hw; exact hw, ?_⟩
          rw [Set.mem_Icc]; rw [abs_le] at hu; constructor <;> [linarith [hu.1]; linarith [hu.2]]
        · have huw : 1/2 < |u + w| := by
            push_neg at hw
            have h1 : |w| ≤ |u| + |u + w| := by
              have hrw : w = -u + (u + w) := by ring
              calc |w| = |-u + (u + w)| := by rw [← hrw]
                _ ≤ |-u| + |u + w| := abs_add_le _ _
                _ = |u| + |u + w| := by rw [abs_neg]
            linarith
          rw [g_zero_of_lt huw, mul_zero, zero_mul]
      · rw [g_of_not_mem hu, zero_mul, zero_mul]
    rw [this]; simp

end Retention
