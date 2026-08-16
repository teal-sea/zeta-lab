/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Profile
import ZetaLean.Pub1.Main
import ZetaLean.Pub1.Window
import ZetaLean.Pub1.Aristotle.H2
import ZetaLean.Pub1.Aristotle.M

/-!
# Pub 1 strong closure: `L²` closure of the quotient

The amplitude sandwich `1/5 ≤ w ≤ 1`, evenness of `w`, and the step that turns
`‖v_L - w‖₂ → 0` into `c(v_L) → c*`.

The quotient is continuous along the sequence because the form is bounded:
`⟨Av_L,v_L⟩ - ⟨Aw,w⟩ = ⟨A(v_L-w), v_L+w⟩` and `|⟨Af,g⟩| ≤ (13/9)‖f‖₂‖g‖₂`, while
`‖v_L+w‖₂ ≤ 2` because both profiles are bounded by `1`.  Mass converges by
Cauchy-Schwarz on an interval of length one.
-/

open Filter Topology MeasureTheory Set

namespace ZetaLean.Pub1

/-! ### Bridges between the externally proved forms and the local ones -/

theorem massI_bridge : AristotleM.massI = massI := rfl
theorem normSqI_bridge : AristotleM.normSqI = normSqI := rfl
theorem bil_bridge : AristotleM.bil = AristotleK.bil := rfl

/-! ### The amplitude sandwich -/

/-- **`1/5 ≤ w ≤ 1`.**  The row-bound argument: `‖w‖_∞ ≤ 9/5`, hence
`w ≥ 1 - (4/9)(9/5) = 1/5`, hence `w ≤ 1`. -/
theorem profile_bounds {w : ℝ → ℝ} (hw : IsProfile w) :
    (∀ s : ℝ, 1 / 5 ≤ w s) ∧ (∀ s : ℝ, w s ≤ 1) :=
  AristotleH2.solution_bounds clampedKernel clampedKernel_continuous clampedKernel_nonneg
    clampedKernel_row w hw.1 hw.2.1 hw.2.2

/-- **`w` is even**, by reflection invariance of the kernel and uniqueness. -/
theorem profile_even {w : ℝ → ℝ} (hw : IsProfile w) : ∀ s : ℝ, w (-s) = w s :=
  AristotleH2.solution_even clampedKernel clampedKernel_continuous clampedKernel_refl
    clampedKernel_row_abs w hw.1 hw.2.1 hw.2.2

/-- **Obligation C, discharged.**  The positivity the square-root taper needs.

`√(w(u/L))` is only defined and `C²` where `w > 0`, and the taper argument needs
that on an open neighbourhood of `I`, not just on `I` itself.  It comes for free:
the row-bound argument gives `1/5 ≤ w` at *every* real `s`, because the clamped
kernel makes `w` constant outside `I`.  No stronger positivity is assumed. -/
theorem profile_pos {w : ℝ → ℝ} (hw : IsProfile w) (s : ℝ) : 0 < w s :=
  lt_of_lt_of_le (by norm_num) ((profile_bounds hw).1 s)

/-- The neighbourhood form consumed by `Aristotle/J`'s taper smoothness. -/
theorem profile_pos_on (hw : IsProfile w) :
    ∀ s ∈ Set.Ioo (-(3 / 5) : ℝ) (3 / 5), 0 < w s := fun s _ => profile_pos hw s

/-- **`c* > 0`**, unconditionally. -/
theorem cStar_pos_of_profile {w : ℝ → ℝ} (hw : IsProfile w) : 0 < cStar w :=
  cStar_pos_of_lower hw.1 (fun s _ => (profile_bounds hw).1 s)

/-! ### The approximating sequence -/

variable {w : ℝ → ℝ}

/-- The sequence `L = 8, 9, 10, …` of induced profiles. -/
noncomputable def vseq (w : ℝ → ℝ) (n : ℕ) : ℝ → ℝ := profile w (8 + (n : ℝ))

theorem vseq_continuous (hw : IsProfile w) (n : ℕ) : Continuous (vseq w n) :=
  continuous_profile hw.1

theorem vseq_nonneg (hw : IsProfile w) (n : ℕ) (s : ℝ) : 0 ≤ vseq w n s := by
  have h0 : 0 ≤ w s := le_trans (by norm_num) ((profile_bounds hw).1 s)
  rw [vseq, profile]
  positivity

theorem vseq_le_one (hw : IsProfile w) (n : ℕ) (s : ℝ) : vseq w n s ≤ 1 := by
  have h1 : w s ≤ 1 := (profile_bounds hw).2 s
  have h0 : 0 ≤ w s := le_trans (by norm_num) ((profile_bounds hw).1 s)
  have he0 : 0 ≤ eta ((8 + (n : ℝ)) * (1 / 2 - |s|)) := eta_nonneg _
  have he1 : eta ((8 + (n : ℝ)) * (1 / 2 - |s|)) ≤ 1 := eta_le_one _
  rw [vseq, profile]
  nlinarith

/-- **`L²` convergence of the sequence**, from the `2/L` estimate. -/
theorem vseq_tendsto_L2 (hw : IsProfile w) :
    Tendsto (fun n : ℕ => normSqI (fun s => vseq w n s - w s)) atTop (𝓝 0) :=
  tendsto_L2_zero hw.1 (fun s _ => (profile_bounds hw).2 s)
    (fun s _ => le_trans (by norm_num) ((profile_bounds hw).1 s))

theorem sqrt_normSqI_tendsto (hw : IsProfile w) :
    Tendsto (fun n : ℕ => Real.sqrt (normSqI (fun s => vseq w n s - w s))) atTop (𝓝 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp (vseq_tendsto_L2 hw)
  simpa [Function.comp_def] using h

/-- The sum `v_L + w` has `L²` norm at most `2`, uniformly. -/
theorem normSqI_add_le (hw : IsProfile w) (n : ℕ) :
    normSqI (fun s => vseq w n s + w s) ≤ 4 := by
  have hb : ∀ s : ℝ, (vseq w n s + w s) ^ 2 ≤ 4 := by
    intro s
    have h1 := vseq_nonneg hw n s
    have h2 := vseq_le_one hw n s
    have h3 : 0 ≤ w s := le_trans (by norm_num) ((profile_bounds hw).1 s)
    have h4 : w s ≤ 1 := (profile_bounds hw).2 s
    nlinarith
  have hc : Continuous fun s => (vseq w n s + w s) ^ 2 :=
    (((vseq_continuous hw n).add hw.1).pow 2)
  have hmono := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun s : ℝ => (vseq w n s + w s) ^ 2) (g := fun _ : ℝ => (4 : ℝ))
    (a := -(1 : ℝ) / 2) (b := 1 / 2) (by norm_num)
    (hc.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    (fun x _ => hb x)
  rw [normSqI]
  have hval : ((1 : ℝ) / 2 - -(1 : ℝ) / 2) * (4 : ℝ) = 4 := by norm_num
  rw [intervalIntegral.integral_const, smul_eq_mul, hval] at hmono
  exact hmono

/-! ### Convergence of mass and energy -/

theorem massI_tendsto (hw : IsProfile w) :
    Tendsto (fun n : ℕ => massI (vseq w n)) atTop (𝓝 (massI w)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (sqrt_normSqI_tendsto hw)
  rw [Real.dist_eq]
  exact AristotleM.mass_diff_le (vseq w n) w (vseq_continuous hw n) hw.1

theorem energyA_tendsto (hw : IsProfile w) :
    Tendsto (fun n : ℕ => energyA (vseq w n)) atTop (𝓝 (energyA w)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbnd : ∀ n : ℕ, dist (energyA (vseq w n)) (energyA w)
      ≤ (13 / 9 * 2) * Real.sqrt (normSqI (fun s => vseq w n s - w s)) := by
    intro n
    have hsub := AristotleM.bil_sub clampedKernel clampedKernel_continuous
      clampedKernel_symm (vseq w n) w (vseq_continuous hw n) hw.1
    have hb := AristotleM.bil_bound clampedKernel clampedKernel_continuous
      clampedKernel_nonneg clampedKernel_symm (4 / 9) clampedKernel_row
      (fun s => vseq w n s - w s) (fun s => vseq w n s + w s)
      ((vseq_continuous hw n).sub hw.1) ((vseq_continuous hw n).add hw.1)
    rw [bil_bridge] at hsub hb
    rw [Real.dist_eq, ← bil_self_eq_energyA, ← bil_self_eq_energyA, hsub]
    have hs2 : Real.sqrt (normSqI (fun s => vseq w n s + w s)) ≤ 2 := by
      have h4 := normSqI_add_le hw n
      have : Real.sqrt (normSqI fun s => vseq w n s + w s) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt h4
      simpa [show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] using this
    have hs0 : 0 ≤ Real.sqrt (normSqI fun s => vseq w n s - w s) := Real.sqrt_nonneg _
    have hs0' : 0 ≤ Real.sqrt (normSqI fun s => vseq w n s + w s) := Real.sqrt_nonneg _
    calc |AristotleK.bil clampedKernel (fun s => vseq w n s - w s) fun s => vseq w n s + w s|
        ≤ (1 + 4 / 9) * Real.sqrt (normSqI fun s => vseq w n s - w s)
            * Real.sqrt (normSqI fun s => vseq w n s + w s) := hb
      _ ≤ (13 / 9 * 2) * Real.sqrt (normSqI fun s => vseq w n s - w s) := by nlinarith
  refine squeeze_zero (fun n => dist_nonneg) hbnd ?_
  have := (sqrt_normSqI_tendsto hw).const_mul (13 / 9 * 2 : ℝ)
  simpa using this

/-- **The quotient converges to `c*`.**  Discharges the `quot_tendsto` field of
`StrongClosureData`. -/
theorem quot_tendsto_cStar (hw : IsProfile w) :
    Tendsto (fun n : ℕ => quot (profile w (8 + (n : ℝ)))) atTop (𝓝 (massI w)) := by
  have hE : energyA w = massI w := energyA_eq_massI_of_profile hw
  have hpos : 0 < massI w := cStar_pos_of_profile hw
  have hnum : Tendsto (fun n : ℕ => massI (vseq w n) ^ 2) atTop (𝓝 (massI w ^ 2)) :=
    (massI_tendsto hw).pow 2
  have hden : Tendsto (fun n : ℕ => energyA (vseq w n)) atTop (𝓝 (massI w)) := by
    rw [← hE]; exact energyA_tendsto hw
  have hdiv := hnum.div hden (ne_of_gt hpos)
  have hval : massI w ^ 2 / massI w = massI w := by field_simp
  rw [hval] at hdiv
  exact hdiv

end ZetaLean.Pub1
