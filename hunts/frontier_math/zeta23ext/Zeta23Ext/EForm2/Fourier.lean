import Zeta23Ext.EForm2.Defs

/-!
# The master Fourier identity

`∫ c2 w * exp (i z w) dw = (Phi2 z)^2` for every complex frequency `z`, together with the
support and measurability facts about the window and its autocorrelation.
-/

open scoped BigOperators
open MeasureTheory

namespace Retention.EForm2

/-! ### Basic facts about the window -/

lemma measurable_gwin : Measurable gwin := by
  unfold gwin
  refine Measurable.ite ?_ (by fun_prop) measurable_const
  exact measurableSet_le measurable_abs measurable_const

lemma gwin_abs_le (u : ℝ) : |gwin u| ≤ 1 := by
  unfold gwin
  split
  · exact Real.abs_cos_le_one _
  · simp

lemma gwin_eq_zero {u : ℝ} (h : 1/2 < |u|) : gwin u = 0 := by
  unfold gwin
  rw [if_neg (by linarith)]

lemma gwin_neg (u : ℝ) : gwin (-u) = gwin u := by
  unfold gwin
  rw [abs_neg]
  split
  · rw [show Real.sqrt 2 * -u = -(Real.sqrt 2 * u) by ring, Real.cos_neg]
  · rfl

/-- On its support the window is `≥ 3/4`; in particular it is nonnegative. -/
lemma gwin_nonneg (u : ℝ) : 0 ≤ gwin u := by
  unfold gwin
  split
  · rename_i h
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have := Real.one_sub_sq_div_two_le_cos (x := Real.sqrt 2 * u)
    have hu : u ^ 2 ≤ 1/4 := by
      have := abs_le.1 h
      nlinarith [this.1, this.2]
    nlinarith
  · exact le_refl 0

/-! ### Integrability on the product -/

lemma integrable_prod (z : ℂ) :
    Integrable (Function.uncurry
      (fun w u : ℝ => (gwin u : ℂ) * (gwin (u + w) : ℂ) * Complex.exp (Complex.I * z * w)))
      (volume.prod volume) := by
  set S : Set (ℝ × ℝ) := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-(1/2):ℝ) (1/2) with hSdef
  have hSm : MeasurableSet S := (measurableSet_Icc).prod measurableSet_Icc
  have hind : Integrable (S.indicator (fun _ => Real.exp |z.im|)) (volume.prod volume) := by
    rw [integrable_indicator_iff hSm]
    apply integrableOn_const
    · show (volume.prod volume) (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-(1/2):ℝ) (1/2)) ≠ ⊤
      rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
      exact ENNReal.mul_ne_top (by finiteness) (by finiteness)
    · finiteness
  refine hind.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    refine Measurable.mul (Measurable.mul ?_ ?_) ?_
    · exact (measurable_gwin.comp measurable_snd).complex_ofReal
    · exact (measurable_gwin.comp (measurable_snd.add measurable_fst)).complex_ofReal
    · fun_prop
  · filter_upwards with p
    rcases p with ⟨w, u⟩
    simp only [Function.uncurry_apply_pair]
    by_cases hp : (w, u) ∈ S
    · rw [Set.indicator_of_mem hp]
      have h1 : ‖(gwin u : ℂ)‖ ≤ 1 := by rw [Complex.norm_real]; exact gwin_abs_le u
      have h2 : ‖(gwin (u+w) : ℂ)‖ ≤ 1 := by rw [Complex.norm_real]; exact gwin_abs_le _
      have h3 : ‖Complex.exp (Complex.I * z * w)‖ ≤ Real.exp |z.im| := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.2
        have hw : |w| ≤ 1 := abs_le.2 ⟨(hp.1).1, (hp.1).2⟩
        simp [Complex.mul_re, Complex.mul_im]
        nlinarith [abs_le.1 hw, le_abs_self z.im, neg_abs_le z.im]
      calc ‖(gwin u : ℂ) * (gwin (u+w) : ℂ) * Complex.exp (Complex.I * z * w)‖
          = ‖(gwin u : ℂ)‖ * ‖(gwin (u+w):ℂ)‖ * ‖Complex.exp (Complex.I * z * w)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * Real.exp |z.im| := by
            apply mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 (norm_nonneg _)
            positivity
        _ = Real.exp |z.im| := by ring
    · rw [Set.indicator_of_notMem hp]
      have hz : (gwin u : ℂ) * (gwin (u+w) : ℂ) = 0 := by
        by_cases hu : 1/2 < |u|
        · rw [gwin_eq_zero hu]; simp
        · push_neg at hu
          have huw : 1/2 < |u + w| := by
            by_contra h3
            push_neg at h3
            rw [abs_le] at hu h3
            refine hp ?_
            simp only [hSdef, Set.mem_prod, Set.mem_Icc]
            exact ⟨⟨by linarith [hu.1, h3.2], by linarith [hu.2, h3.1]⟩, hu.1, hu.2⟩
          rw [gwin_eq_zero huw]; simp
      rw [hz, zero_mul, norm_zero]

/-- The autocorrelation, written as a `u`-integral with the oscillating factor inside. -/
lemma c2_exp_eq (z : ℂ) (w : ℝ) :
    (c2 w : ℂ) * Complex.exp (Complex.I * z * w)
      = ∫ u : ℝ, (gwin u : ℂ) * (gwin (u + w) : ℂ) * Complex.exp (Complex.I * z * w) := by
  rw [integral_mul_const]
  congr 1
  unfold c2
  rw [← integral_complex_ofReal]
  congr 1
  funext u
  push_cast
  ring

lemma integrable_c2_exp (z : ℂ) :
    Integrable (fun w : ℝ => (c2 w : ℂ) * Complex.exp (Complex.I * z * w)) := by
  have h := (integrable_prod z).integral_prod_left
  simpa only [Function.uncurry_apply_pair, ← c2_exp_eq z] using h

lemma Phi2_neg (z : ℂ) : Phi2 (-z) = Phi2 z := by
  unfold Phi2
  rw [← integral_neg_eq_self (fun u : ℝ => (gwin u : ℂ) * Complex.exp (Complex.I * (-z) * u))
    volume]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gwin_neg]
  congr 2
  push_cast
  ring

/-- **Master identity**: the Fourier transform of the autocorrelation is the square of the
Fourier transform of the window. -/
lemma master (z : ℂ) :
    ∫ w : ℝ, (c2 w : ℂ) * Complex.exp (Complex.I * z * w) = (Phi2 z) ^ 2 := by
  simp_rw [c2_exp_eq z]
  rw [integral_integral_swap (integrable_prod z)]
  have h2 : ∀ u : ℝ,
      (∫ w : ℝ, (gwin u : ℂ) * (gwin (u + w) : ℂ) * Complex.exp (Complex.I * z * w))
        = ((gwin u : ℂ) * Complex.exp (-(Complex.I * z * u))) * Phi2 z := by
    intro u
    have key : ∀ w : ℝ, (gwin u : ℂ) * (gwin (u + w) : ℂ) * Complex.exp (Complex.I * z * w)
        = ((gwin u : ℂ) * Complex.exp (-(Complex.I * z * u)))
          * ((fun v : ℝ => (gwin v : ℂ) * Complex.exp (Complex.I * z * v)) (u + w)) := by
      intro w
      simp only
      have e1 : Complex.exp (-(Complex.I * z * u)) * Complex.exp (Complex.I * z * ((u:ℂ) + w))
          = Complex.exp (Complex.I * z * w) := by
        rw [← Complex.exp_add]; congr 1; ring
      push_cast
      linear_combination (-(gwin u : ℂ) * (gwin (u + w) : ℂ)) * e1
    have hshift : (∫ w : ℝ, (gwin (u + w) : ℂ) * Complex.exp (Complex.I * z * ((u + w : ℝ) : ℂ)))
        = Phi2 z :=
      integral_add_left_eq_self
        (fun v : ℝ => (gwin v : ℂ) * Complex.exp (Complex.I * z * (v : ℂ))) u
    simp_rw [key]
    rw [integral_const_mul, hshift]
  simp_rw [h2]
  rw [integral_mul_const]
  have h3 : (∫ u : ℝ, (gwin u : ℂ) * Complex.exp (-(Complex.I * z * u))) = Phi2 z := by
    rw [← Phi2_neg z]
    unfold Phi2
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    show (gwin u : ℂ) * Complex.exp (-(Complex.I * z * (u:ℂ)))
        = (gwin u : ℂ) * Complex.exp (Complex.I * (-z) * (u:ℂ))
    congr 2
    ring
  rw [h3]
  ring

end Retention.EForm2
