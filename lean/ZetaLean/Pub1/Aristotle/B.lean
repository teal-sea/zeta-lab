import Mathlib

namespace AristotleB

open MeasureTheory

private lemma aux_integrable_prod (g : ℝ → ℝ → ℝ)
    (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2) (a b : ℝ) :
    Integrable (Function.uncurry g)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b))) := by
  rw [Measure.prod_restrict]
  have hcpt : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) := isCompact_Icc.prod isCompact_Icc
  have h1 : IntegrableOn (Function.uncurry g) (Set.Icc a b ×ˢ Set.Icc a b) := by
    apply ContinuousOn.integrableOn_compact hcpt
    exact (hg.continuousOn : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) _)
  exact h1.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

private lemma aux_swap (g : ℝ → ℝ → ℝ) (hg : Continuous fun p : ℝ × ℝ => g p.1 p.2)
    (a b : ℝ) (hab : a ≤ b) :
    (∫ s in a..b, ∫ t in a..b, g s t) = ∫ t in a..b, ∫ s in a..b, g s t := by
  simp_rw [intervalIntegral.integral_of_le hab]
  exact integral_integral_swap (aux_integrable_prod g hg a b)

theorem schur_quadratic_bound
    (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (hKnn : ∀ s t, 0 ≤ K s t) (hKsymm : ∀ s t, K s t = K t s)
    (θ : ℝ) (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), K s t) ≤ θ)
    (v : ℝ → ℝ) (hv : Continuous v) :
    |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (v s * v t)|
      ≤ θ * ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2 := by
  have hab : (-(1:ℝ)/2) ≤ (1:ℝ)/2 := by norm_num
  -- continuity facts
  have hKfst : Continuous fun p : ℝ × ℝ => v p.1 := hv.comp continuous_fst
  have hKsnd : Continuous fun p : ℝ × ℝ => v p.2 := hv.comp continuous_snd
  have hc1 : Continuous fun p : ℝ × ℝ => K p.1 p.2 * (v p.1 * v p.2) :=
    hK.mul (hKfst.mul hKsnd)
  have hc2 : Continuous fun p : ℝ × ℝ =>
      K p.1 p.2 * v p.1 ^ 2 / 2 + K p.1 p.2 * v p.2 ^ 2 / 2 :=
    ((hK.mul (hKfst.pow 2)).div_const 2).add ((hK.mul (hKsnd.pow 2)).div_const 2)
  have hc3 : Continuous fun p : ℝ × ℝ => K p.1 p.2 * v p.1 ^ 2 / 2 :=
    (hK.mul (hKfst.pow 2)).div_const 2
  have hc4 : Continuous fun p : ℝ × ℝ => K p.1 p.2 * v p.2 ^ 2 / 2 :=
    (hK.mul (hKsnd.pow 2)).div_const 2
  -- continuity of the parametric integrals
  have hF : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (v s * v t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => K s t * (v s * v t)) hc1 _ _
  have hG : Continuous fun s =>
      ∫ t in (-(1:ℝ)/2)..(1/2), (K s t * v s ^ 2 / 2 + K s t * v t ^ 2 / 2) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => K s t * v s ^ 2 / 2 + K s t * v t ^ 2 / 2) hc2 _ _
  have hG1 : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * v s ^ 2 / 2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => K s t * v s ^ 2 / 2) hc3 _ _
  have hG2 : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * v t ^ 2 / 2 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => K s t * v t ^ 2 / 2) hc4 _ _
  have hs1 : ∀ s : ℝ, Continuous fun t => K s t * (v s * v t) := fun s =>
    hc1.comp (continuous_const.prodMk continuous_id)
  have hs2 : ∀ s : ℝ, Continuous fun t => K s t * v s ^ 2 / 2 + K s t * v t ^ 2 / 2 := fun s =>
    hc2.comp (continuous_const.prodMk continuous_id)
  have hs3 : ∀ s : ℝ, Continuous fun t => K s t * v s ^ 2 / 2 := fun s =>
    hc3.comp (continuous_const.prodMk continuous_id)
  have hs4 : ∀ s : ℝ, Continuous fun t => K s t * v t ^ 2 / 2 := fun s =>
    hc4.comp (continuous_const.prodMk continuous_id)
  have hKrow : Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := fun s t => K s t) hK _ _
  -- notation
  set A := ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * v s ^ 2 / 2 with hAdef
  set B := ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * v t ^ 2 / 2 with hBdef
  have hBA : B = A := by
    rw [hBdef, aux_swap (fun s t => K s t * v t ^ 2 / 2) hc4 _ _ hab, hAdef]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact intervalIntegral.integral_congr (fun y _ => by rw [hKsymm])
  have hAeq : A = ∫ s in (-(1:ℝ)/2)..(1/2), (∫ t in (-(1:ℝ)/2)..(1/2), K s t) * v s ^ 2 / 2 := by
    rw [hAdef]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    have : (fun t => K s t * v s ^ 2 / 2) = fun t => K s t * (v s ^ 2 / 2) := by
      funext t; ring
    rw [this, intervalIntegral.integral_mul_const]
    ring
  calc |∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (v s * v t)|
      ≤ ∫ s in (-(1:ℝ)/2)..(1/2), |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (v s * v t)| :=
        intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ s in (-(1:ℝ)/2)..(1/2),
          (∫ t in (-(1:ℝ)/2)..(1/2), (K s t * v s ^ 2 / 2 + K s t * v t ^ 2 / 2)) := by
        refine intervalIntegral.integral_mono_on hab (hF.abs.intervalIntegrable _ _)
          (hG.intervalIntegrable _ _) (fun s _ => ?_)
        calc |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (v s * v t)|
            ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s t * (v s * v t)| :=
              intervalIntegral.abs_integral_le_integral_abs hab
          _ ≤ ∫ t in (-(1:ℝ)/2)..(1/2), (K s t * v s ^ 2 / 2 + K s t * v t ^ 2 / 2) := by
              refine intervalIntegral.integral_mono_on hab
                ((hs1 s).abs.intervalIntegrable _ _)
                ((hs2 s).intervalIntegrable _ _)
                (fun t _ => ?_)
              have habs : |v s * v t| ≤ (v s ^ 2 + v t ^ 2) / 2 := by
                rw [abs_le]
                constructor <;> nlinarith [sq_nonneg (v s + v t), sq_nonneg (v s - v t)]
              have := mul_le_mul_of_nonneg_left habs (hKnn s t)
              rw [abs_mul, abs_of_nonneg (hKnn s t)]
              nlinarith
    _ = A + B := by
        rw [hAdef, hBdef, ← intervalIntegral.integral_add (hG1.intervalIntegrable _ _)
          (hG2.intervalIntegrable _ _)]
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        exact intervalIntegral.integral_add ((hs3 s).intervalIntegrable _ _)
          ((hs4 s).intervalIntegrable _ _)
    _ = ∫ s in (-(1:ℝ)/2)..(1/2), (∫ t in (-(1:ℝ)/2)..(1/2), K s t) * v s ^ 2 := by
        have hcont : Continuous fun s => (∫ t in (-(1:ℝ)/2)..(1/2), K s t) * v s ^ 2 / 2 :=
          (hKrow.mul (hv.pow 2)).div_const 2
        rw [hBA, hAeq, ← intervalIntegral.integral_add (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)]
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        show _ = _
        ring
    _ ≤ ∫ s in (-(1:ℝ)/2)..(1/2), θ * v s ^ 2 := by
        refine intervalIntegral.integral_mono_on hab
          ((hKrow.mul (hv.pow 2)).intervalIntegrable _ _)
          ((continuous_const.mul (hv.pow 2)).intervalIntegrable _ _) (fun s _ => ?_)
        exact mul_le_mul_of_nonneg_right (hrow s) (sq_nonneg _)
    _ = θ * ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2 := intervalIntegral.integral_const_mul _ _


end AristotleB