import Zeta23Ext.EForm.Basic

open scoped BigOperators
open scoped Real
open MeasureTheory

namespace Retention

/-! ## The Fubini / autocorrelation identity -/

lemma prod_int (h : ℝ → ℝ) (hc : Continuous h) :
    Integrable (Function.uncurry fun (w u : ℝ) => gker u * gker (u - w) * h w)
      (volume.prod volume) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  set S : Set (ℝ × ℝ) := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-(1/2):ℝ) (1/2) with hS
  have hSmeas : MeasurableSet S := (measurableSet_Icc).prod measurableSet_Icc
  refine Integrable.mono' (g := fun p => S.indicator (fun _ => M) p) ?_ ?_ ?_
  · rw [integrable_indicator_iff hSmeas]
    refine integrableOn_const (C := M) ?_ ?_
    · rw [hS, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    · simp
  · exact (((gker_meas.comp measurable_snd).mul
      (gker_meas.comp (measurable_snd.sub measurable_fst))).mul
      (hc.measurable.comp measurable_fst)).aestronglyMeasurable
  · filter_upwards with p
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp]
      simp only [Function.uncurry]
      have h3 : ‖h p.1‖ ≤ M := hM p.1 hp.1
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc |gker p.2| * |gker (p.2 - p.1)| * |h p.1| ≤ 1 * 1 * M := by
            refine mul_le_mul (mul_le_mul (gker_abs_le_one _) (gker_abs_le_one _)
              (abs_nonneg _) zero_le_one) (by simpa using h3) (abs_nonneg _) (by norm_num)
        _ = M := by ring
    · rw [Set.indicator_of_notMem hp]
      simp only [Function.uncurry]
      have hz : gker p.2 * gker (p.2 - p.1) * h p.1 = 0 := by
        by_cases hu : |p.2| ≤ 1/2
        · have hw : ¬ (|p.1| ≤ 1) := fun hw => hp ⟨abs_le.1 hw, abs_le.1 hu⟩
          have hgt : 1/2 < |p.2 - p.1| := by
            have h1 : |p.1| - |p.2| ≤ |p.1 - p.2| := abs_sub_abs_le_abs_sub _ _
            rw [abs_sub_comm] at h1
            have := not_le.1 hw
            linarith
          rw [gker_of_gt hgt]; ring
        · rw [gker_of_gt (not_le.1 hu)]; ring
      rw [hz]; simp

/-- The autocorrelation identity: integrating against `c₂` is the same as integrating the
difference against the product measure `gker ⊗ gker`. -/
lemma master (h : ℝ → ℝ) (hc : Continuous h) :
    ∫ w : ℝ, c2 w * h w = ∫ u : ℝ, ∫ v : ℝ, gker u * gker v * h (u - v) := by
  have h1 : ∀ w : ℝ, c2 w * h w = ∫ u : ℝ, gker u * gker (u - w) * h w := by
    intro w; rw [c2, ← integral_mul_const]
  simp_rw [h1]
  rw [integral_integral_swap (prod_int h hc)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show (∫ x : ℝ, gker u * gker (u - x) * h x) = ∫ v : ℝ, gker u * gker v * h (u - v)
  rw [← integral_sub_left_eq_self (fun w : ℝ => gker u * gker (u - w) * h w) volume u]
  simp only [sub_sub_cancel]

lemma inner_factor (b : ℝ → ℝ) (c u : ℝ) :
    (∫ v : ℝ, gker u * gker v * (c * b v)) = (gker u * c) * ∫ v : ℝ, gker v * b v := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)

lemma prod_integrand_integrable {b : ℝ → ℝ} (hb : Continuous b) (c u : ℝ) :
    Integrable (fun v : ℝ => gker u * gker v * (c * b v)) := by
  have h : Integrable (fun v : ℝ => gker v * (gker u * c * b v)) := gker_mul_integrable (by fun_prop)
  exact h.congr (Filter.Eventually.of_forall fun v => by ring)

lemma master_prod (a b : ℝ → ℝ) :
    (∫ u : ℝ, ∫ v : ℝ, gker u * gker v * (a u * b v))
      = (∫ u : ℝ, gker u * a u) * (∫ v : ℝ, gker v * b v) := by
  have key : ∀ u : ℝ, (∫ v : ℝ, gker u * gker v * (a u * b v))
      = (gker u * a u) * ∫ v : ℝ, gker v * b v := by
    intro u
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)
  simp_rw [key]
  rw [integral_mul_const]

/-! ## Basic integrals -/

lemma Aconst_pos : 0 < Aconst := by
  have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hlt : 1 / Real.sqrt 2 < Real.pi := by
    have : Real.sqrt 2 ≥ 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by norm_num)
    have : 1 / Real.sqrt 2 ≤ 1 := by
      rw [div_le_one h2]; linarith
    linarith [Real.pi_gt_three]
  have := Real.sin_pos_of_pos_of_lt_pi (x := 1 / Real.sqrt 2) (by positivity) hlt
  exact mul_pos h2 this

lemma integral_gker : ∫ u : ℝ, gker u = Aconst := by
  have hsupp : ∀ x : ℝ, x ∉ Set.Icc (-(1/2):ℝ) (1/2) → gker x = 0 := by
    intro x hx
    refine gker_of_gt ?_
    by_contra h
    push_neg at h
    exact hx ⟨by linarith [(abs_le.1 h).1], (abs_le.1 h).2⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have hcongr : ∫ x in Set.Icc (-(1/2):ℝ) (1/2), gker x
      = ∫ x in Set.Icc (-(1/2):ℝ) (1/2), Real.cos (Real.sqrt 2 * x) := by
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    exact gker_of_le (abs_le.2 ⟨by linarith [hx.1], hx.2⟩)
  rw [hcongr, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1/2):ℝ) ≤ 1/2),
    intervalIntegral.integral_comp_mul_left (fun x => Real.cos x)
      (by positivity : Real.sqrt 2 ≠ 0), integral_cos, Aconst]
  have h2 : Real.sqrt 2 * (1/2) = 1 / Real.sqrt 2 := by
    rw [eq_div_iff (by positivity : Real.sqrt 2 ≠ 0)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  rw [show Real.sqrt 2 * (-(1/2)) = -(Real.sqrt 2 * (1/2)) by ring, h2, Real.sin_neg]
  rw [smul_eq_mul]
  field_simp
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [hs2]; ring

/-! ## Linearity helpers -/

lemma c2_int_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    ∫ w : ℝ, c2 w * (f w + g w) = (∫ w : ℝ, c2 w * f w) + ∫ w : ℝ, c2 w * g w := by
  rw [← integral_add (c2_mul_integrable hf) (c2_mul_integrable hg)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)

lemma c2_int_const_mul (r : ℝ) (f : ℝ → ℝ) :
    ∫ w : ℝ, c2 w * (r * f w) = r * ∫ w : ℝ, c2 w * f w := by
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun w => by ring)

lemma c2_int_sum {n : ℕ} (F : Fin n → ℝ → ℝ) (hF : ∀ j, Continuous (F j)) :
    ∫ w : ℝ, c2 w * (∑ j, F j w) = ∑ j, ∫ w : ℝ, c2 w * F j w := by
  have h1 : ∀ w : ℝ, c2 w * (∑ j, F j w) = ∑ j, c2 w * F j w := fun w => Finset.mul_sum _ _ _
  simp_rw [h1]
  exact integral_finset_sum _ (fun j _ => c2_mul_integrable (hF j))

/-! ## The three basic quantities -/

/-- `Icos s = ∫ c₂(w) cos (s w) dw`; this is `Φ₂(s)²`, in particular nonnegative. -/
noncomputable def Icos (s : ℝ) : ℝ := ∫ w : ℝ, c2 w * Real.cos (s * w)

/-- `Ichy y = ∫ c₂(w) (cosh (y w) - 1) dw ≥ 0`. -/
noncomputable def Ichy (y : ℝ) : ℝ := ∫ w : ℝ, c2 w * (Real.cosh (y * w) - 1)

/-- `Icross y s = ∫ c₂(w) cosh (y w) cos (s w) dw`. -/
noncomputable def Icross (y s : ℝ) : ℝ := ∫ w : ℝ, c2 w * (Real.cosh (y * w) * Real.cos (s * w))

lemma Icos_nonneg (s : ℝ) : 0 ≤ Icos s := by
  rw [Icos, master _ (by fun_prop)]
  have key : ∀ u : ℝ, (∫ v : ℝ, gker u * gker v * Real.cos (s * (u - v)))
      = (gker u * Real.cos (s * u)) * (∫ v : ℝ, gker v * Real.cos (s * v))
        + (gker u * Real.sin (s * u)) * (∫ v : ℝ, gker v * Real.sin (s * v)) := by
    intro u
    rw [← inner_factor (fun v => Real.cos (s * v)), ← inner_factor (fun v => Real.sin (s * v)),
      ← integral_add (prod_integrand_integrable (by fun_prop) _ _)
        (prod_integrand_integrable (by fun_prop) _ _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show gker u * gker v * Real.cos (s * (u - v)) = _
    rw [mul_sub, Real.cos_sub]; ring
  simp_rw [key]
  rw [integral_add ((gker_mul_integrable (f := fun u => Real.cos (s * u)) (by fun_prop)).mul_const _)
      ((gker_mul_integrable (f := fun u => Real.sin (s * u)) (by fun_prop)).mul_const _),
    integral_mul_const, integral_mul_const]
  exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

lemma Icos_zero : Icos 0 = Aconst ^ 2 := by
  rw [Icos]
  have : ∀ w : ℝ, c2 w * Real.cos (0 * w) = c2 w * ((1:ℝ) * (1:ℝ)) := by
    intro w; simp
  simp_rw [this]
  rw [master _ (by fun_prop)]
  have : ∀ u : ℝ, (∫ v : ℝ, gker u * gker v * ((1:ℝ) * (1:ℝ)))
      = ∫ v : ℝ, gker u * gker v * ((fun _ : ℝ => (1:ℝ)) u * (fun _ : ℝ => (1:ℝ)) v) := by
    intro u; simp
  simp_rw [this]
  rw [master_prod (fun _ => (1:ℝ)) (fun _ => (1:ℝ))]
  simp only [mul_one]
  rw [integral_gker, sq]

lemma Ichy_nonneg (y : ℝ) : 0 ≤ Ichy y := by
  refine integral_nonneg (fun w => mul_nonneg (c2_nonneg w) ?_)
  have := Real.one_le_cosh (y * w)
  linarith

lemma Icross_lower (y s : ℝ) : -Ichy y ≤ Icross y s := by
  have hsplit : Icross y s = Icos s + ∫ w : ℝ, c2 w * ((Real.cosh (y * w) - 1) * Real.cos (s * w)) := by
    rw [Icross, Icos, ← c2_int_add (by fun_prop) (by fun_prop)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    show c2 w * (Real.cosh (y * w) * Real.cos (s * w))
      = c2 w * (Real.cos (s * w) + (Real.cosh (y * w) - 1) * Real.cos (s * w))
    ring
  have hb : -Ichy y ≤ ∫ w : ℝ, c2 w * ((Real.cosh (y * w) - 1) * Real.cos (s * w)) := by
    rw [Ichy, ← integral_neg]
    refine integral_mono ((c2_mul_integrable (by fun_prop)).neg) (c2_mul_integrable (by fun_prop))
      (fun w => ?_)
    have hc : 0 ≤ c2 w := c2_nonneg w
    have hch : 0 ≤ Real.cosh (y * w) - 1 := by linarith [Real.one_le_cosh (y * w)]
    have hcos : -1 ≤ Real.cos (s * w) := Real.neg_one_le_cos _
    nlinarith [mul_nonneg hc hch]
  have := Icos_nonneg s
  linarith [hsplit ▸ (le_refl (Icross y s))]

lemma Ichy_double (y : ℝ) : 4 * Ichy y ≤ Ichy (2 * y) := by
  rw [Ichy, Ichy, ← integral_const_mul]
  refine integral_mono ((c2_mul_integrable (by fun_prop)).const_mul 4)
    (c2_mul_integrable (by fun_prop)) (fun w => ?_)
  have hc : 0 ≤ c2 w := c2_nonneg w
  have hd : Real.cosh (2 * y * w) = 2 * Real.cosh (y * w) ^ 2 - 1 := by
    rw [show 2 * y * w = 2 * (y * w) by ring, Real.cosh_two_mul]
    have := Real.cosh_sq_sub_sinh_sq (y * w)
    linarith
  rw [hd]
  have h1 : Real.cosh (y * w) ≥ 1 := Real.one_le_cosh _
  nlinarith [mul_nonneg hc (sq_nonneg (Real.cosh (y * w) - 1))]

end Retention
