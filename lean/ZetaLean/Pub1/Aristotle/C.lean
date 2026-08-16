import Mathlib

namespace AristotleC

open MeasureTheory
open scoped BoundedContinuousFunction

/-- The kernel is continuous in the second variable for a fixed first variable. -/
private theorem fredholm_kernel_slice_continuous
    {K : ℝ → ℝ → ℝ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) (s : ℝ) :
    Continuous fun t => K s t :=
  hK.comp (Continuous.prodMk continuous_const continuous_id)

/-- The basic bound: the integral operator maps a function bounded by `M` to one
bounded by `θ * M`. -/
private theorem fredholm_op_bound
    {K : ℝ → ℝ → ℝ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {θ : ℝ} (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ θ)
    {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ t, |g t| ≤ M) (s : ℝ) :
    |∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t| ≤ θ * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hle : (-(1:ℝ)/2) ≤ 1/2 := by norm_num
  have hKs : Continuous fun t => K s t := fredholm_kernel_slice_continuous hK s
  have h1 : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t| ≤
      ∫ t in (-(1:ℝ)/2)..(1/2), |K s t * g t| :=
    intervalIntegral.abs_integral_le_integral_abs hle
  have h2 : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t * g t|) ≤
      ∫ t in (-(1:ℝ)/2)..(1/2), |K s t| * M := by
    refine intervalIntegral.integral_mono_on hle
      ((hKs.mul hg).abs.intervalIntegrable _ _)
      ((hKs.abs.mul continuous_const).intervalIntegrable _ _) ?_
    intro t _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM t) (abs_nonneg _)
  have h3 : (∫ t in (-(1:ℝ)/2)..(1/2), |K s t| * M)
      = (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) * M :=
    intervalIntegral.integral_mul_const _ _
  calc |∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t| ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |K s t| * M :=
        h1.trans h2
    _ = (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) * M := h3
    _ ≤ θ * M := mul_le_mul_of_nonneg_right (hrow s) hM0

/-- Continuity of the parametric integral. -/
private theorem fredholm_op_continuous
    {K : ℝ → ℝ → ℝ} (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * g t := by
  have huc : Continuous (Function.uncurry fun s t => K s t * g t) := by
    have hrw : (Function.uncurry fun s t : ℝ => K s t * g t)
        = fun p : ℝ × ℝ => K p.1 p.2 * g p.2 := rfl
    rw [hrw]
    exact hK.mul (hg.comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' huc _ _

theorem exists_continuous_solution
    (K : ℝ → ℝ → ℝ) (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hrow : ∀ s, (∫ t in (-(1:ℝ)/2)..(1/2), |K s t|) ≤ θ) :
    ∃ w : ℝ → ℝ, Continuous w ∧ (∃ C, ∀ s, |w s| ≤ C) ∧
      ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t) = 1 := by
  classical
  -- the integral operator, as a self-map of the space of bounded continuous functions
  set T : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) := fun w =>
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun s => ∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t)
      (fredholm_op_continuous hK w.continuous) (θ * ‖w‖)
      (fun s => by
        simpa [Real.norm_eq_abs] using
          fredholm_op_bound hK hrow w.continuous
            (fun t => by simpa [Real.norm_eq_abs] using w.norm_coe_le_norm t) s)
    with hT
  have hTapp : ∀ (w : ℝ →ᵇ ℝ) (s : ℝ),
      T w s = ∫ t in (-(1:ℝ)/2)..(1/2), K s t * w t := by
    intro w s; rfl
  set Φ : (ℝ →ᵇ ℝ) → (ℝ →ᵇ ℝ) := fun w => BoundedContinuousFunction.const ℝ (1 : ℝ) - T w
    with hΦ
  have hlip : LipschitzWith ⟨θ, hθ0⟩ Φ := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro w₁ w₂
    have hnn : 0 ≤ θ * dist w₁ w₂ := mul_nonneg hθ0 dist_nonneg
    show dist (Φ w₁) (Φ w₂) ≤ θ * dist w₁ w₂
    rw [BoundedContinuousFunction.dist_le hnn]
    intro s
    have i1 : IntervalIntegrable (fun t => K s t * w₁ t) volume (-(1:ℝ)/2) (1/2) :=
      ((fredholm_kernel_slice_continuous hK s).mul w₁.continuous).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun t => K s t * w₂ t) volume (-(1:ℝ)/2) (1/2) :=
      ((fredholm_kernel_slice_continuous hK s).mul w₂.continuous).intervalIntegrable _ _
    have hsub : (T w₁) s - (T w₂) s
        = ∫ t in (-(1:ℝ)/2)..(1/2), K s t * (w₁ t - w₂ t) := by
      rw [hTapp, hTapp, ← intervalIntegral.integral_sub i1 i2]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    have hbound : |∫ t in (-(1:ℝ)/2)..(1/2), K s t * (w₁ t - w₂ t)| ≤ θ * dist w₁ w₂ :=
      fredholm_op_bound hK hrow (w₁.continuous.sub w₂.continuous)
        (fun t => by
          simpa [Real.dist_eq] using BoundedContinuousFunction.dist_coe_le_dist (f := w₁)
            (g := w₂) t) s
    have hneg : (Φ w₁) s - (Φ w₂) s = -((T w₁) s - (T w₂) s) := by
      simp only [hΦ, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
        BoundedContinuousFunction.const_apply]
      ring
    have hd : dist ((Φ w₁) s) ((Φ w₂) s) = |(T w₁) s - (T w₂) s| := by
      rw [Real.dist_eq, hneg, abs_neg]
    rw [hd, hsub]
    exact hbound
  have hcontr : ContractingWith ⟨θ, hθ0⟩ Φ := ⟨by exact_mod_cast hθ1, hlip⟩
  set w : ℝ →ᵇ ℝ := hcontr.fixedPoint Φ with hw
  have hfix : Φ w = w := hcontr.fixedPoint_isFixedPt
  refine ⟨fun s => w s, w.continuous, ⟨‖w‖, fun s => by
    simpa [Real.norm_eq_abs] using w.norm_coe_le_norm s⟩, ?_⟩
  intro s
  have := congrArg (fun (f : ℝ →ᵇ ℝ) => f s) hfix
  simp only [hΦ, BoundedContinuousFunction.coe_sub, Pi.sub_apply,
    BoundedContinuousFunction.const_apply, hTapp] at this
  linarith [this]


end AristotleC