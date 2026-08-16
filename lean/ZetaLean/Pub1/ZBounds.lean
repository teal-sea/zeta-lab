/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.EuBound
import ZetaLean.Pub1.CertBounds
import ZetaLean.Pub1.CertL2
import ZetaLean.Pub1.Aristotle.Y
import ZetaLean.Pub1.Aristotle.R
import ZetaLean.Pub1.Aristotle.M

/-!
# Pub 1 strong closure: the `L^∞` and `L²` bounds on `z = w - u`

From `z + T z = g` with `g = r₀ - E u`:

* `L^∞` by a maximum principle (`Aristotle/Y`): `‖z‖_∞ ≤ (9/5)‖g‖_∞`;
* `L²` by coercivity (`Aristotle/R`): `‖z‖₂ ≤ (9/5)‖g‖₂`.

`‖g‖₂` is bounded without Minkowski, by expanding `(r₀ - Eu)²` and using
`|Eu| ≤ ρ‖u‖_∞` with `∫|r₀| ≤ ‖r₀‖_∞`.
-/

open MeasureTheory

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

/-- `z = w - u`. -/
noncomputable def zFun (w : ℝ → ℝ) : ℝ → ℝ := fun s => w s - uPoly s
/-- `g = r₀ - E u`. -/
noncomputable def gFun : ℝ → ℝ := fun s => r0Poly s - EuTail s

theorem continuous_EuTail : Continuous EuTail := by
  unfold EuTail
  have hc : Continuous (Function.uncurry
      fun s t : ℝ => (F1 (s - t) - truncKernel (s - t)) * uPoly t) := by
    have hK : Continuous truncKernel := by
      unfold truncKernel
      refine (by fun_prop : Continuous fun x : ℝ => (-4 : ℝ) * x ^ 2).add ?_
      exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_abs.pow _))
    have h1 : Continuous fun p : ℝ × ℝ => F1 (p.1 - p.2) - truncKernel (p.1 - p.2) :=
      (F1_continuous.comp (continuous_fst.sub continuous_snd)).sub
        (hK.comp (continuous_fst.sub continuous_snd))
    exact h1.mul (continuous_uPoly.comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _ _

theorem continuous_r0Poly : Continuous r0Poly := by unfold r0Poly; fun_prop

theorem continuous_gFun : Continuous gFun := continuous_r0Poly.sub continuous_EuTail

theorem continuous_zFun (hw : IsProfile w) : Continuous (zFun w) := hw.1.sub continuous_uPoly

/-- `|g| ≤ bgC` on `I`. -/
theorem gFun_abs_le {s : ℝ} (hs : |s| ≤ 1 / 2) : |gFun s| ≤ (bgC : ℝ) := by
  have h1 : |r0Poly s| ≤ (r0C : ℝ) := by
    rw [r0Poly_eq_sum]
    refine le_trans (r0Sum_abs_le s hs) ?_
    norm_num [r0C]
  have h2 : |EuTail s| ≤ (rhoC : ℝ) * (usupC : ℝ) := EuTail_abs_le hs
  have hbq : bgC = r0C + rhoC * usupC := by rw [bgC_eq, eC_eq]
  have hb : ((bgC : ℚ) : ℝ) = ((r0C : ℚ) : ℝ) + ((rhoC : ℚ) : ℝ) * ((usupC : ℚ) : ℝ) := by
    exact_mod_cast hbq
  rw [gFun, hb]
  have := abs_le.mp h1
  have := abs_le.mp h2
  rw [abs_le]
  constructor <;> [linarith [(abs_le.mp h1).1, (abs_le.mp h2).2];
    linarith [(abs_le.mp h1).2, (abs_le.mp h2).1]]

/-- The resolvent equation in the clamped-kernel form the estimates want. -/
theorem z_resolvent_clamped (hw : IsProfile w) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    zFun w s + (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * zFun w t) = gFun s := by
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * zFun w t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (w t - uPoly t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have htc : clampI t = t :=
      clampI_eq_self (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp only [clampedKernel, clampI_eq_self hs, htc, zFun]
  rw [hcongr, zFun, gFun]
  exact z_resolvent_eq hw hs

/-- **`‖z‖_∞ ≤ zinfC`.** -/
theorem zFun_linf (hw : IsProfile w) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |zFun w s| ≤ (zinfC : ℝ) := by
  have h := AristotleY.resolvent_linf_max clampedKernel clampedKernel_continuous
    clampedKernel_nonneg clampedKernel_row (zFun w) gFun (continuous_zFun hw) continuous_gFun
    (bgC : ℝ) (fun σ hσ => gFun_abs_le hσ) (fun σ hσ => z_resolvent_clamped hw hσ) s hs
  have hz : ((zinfC : ℚ) : ℝ) = 9 / 5 * ((bgC : ℚ) : ℝ) := by
    rw [zinfC_eq]; push_cast; ring
  rw [hz]
  exact h

/-! ### The `L²` bound -/

/-- `∫ z·g = ⟪Az, z⟫`, which is what coercivity applies to. -/
theorem integral_z_mul_g (hw : IsProfile w) :
    (∫ s in (-(1:ℝ)/2)..(1/2), zFun w s * gFun s) = energyA (zFun w) := by
  have hz := continuous_zFun hw
  have hcongr : (∫ s in (-(1:ℝ)/2)..(1/2), zFun w s * gFun s)
      = ∫ s in (-(1:ℝ)/2)..(1/2),
          (zFun w s * zFun w s
            + ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (zFun w s * zFun w t)) := by
    refine intervalIntegral.integral_congr ?_
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hsabs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have heq := z_resolvent_eq hw hsabs
    have hpull : (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * ((w s - uPoly s) * (w t - uPoly t)))
        = (w s - uPoly s) * ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (w t - uPoly t) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun t _ => by ring)
    simp only [zFun, gFun]
    rw [hpull, ← heq]
    ring
  rw [hcongr, energyA, normSqI, kerForm]
  rw [← intervalIntegral.integral_add]
  · exact intervalIntegral.integral_congr (fun s _ => by ring)
  · exact ((hz.pow 2).intervalIntegrable (μ := volume) _ _)
  · have hc : Continuous (Function.uncurry fun s t : ℝ => F1 (s - t) * (zFun w s * zFun w t)) := by
      have h1 : Continuous fun p : ℝ × ℝ => F1 (p.1 - p.2) :=
        F1_continuous.comp (continuous_fst.sub continuous_snd)
      exact h1.mul ((hz.comp continuous_fst).mul (hz.comp continuous_snd))
    exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _
      _).intervalIntegrable (μ := volume) _ _

/-- `∫ g² ≤ gl2sqC`, by expanding the square: no Minkowski needed. -/
theorem normSqI_gFun_le : normSqI gFun ≤ ((gl2sqC : ℚ) : ℝ) := by
  set E : ℝ := ((eC : ℚ) : ℝ) with hEdef
  set R : ℝ := ((r0C : ℚ) : ℝ) with hRdef
  have hEnn : (0:ℝ) ≤ E := by rw [hEdef]; norm_num [eC]
  have hRnn : (0:ℝ) ≤ R := by rw [hRdef]; norm_num [r0C]
  have hE : ∀ s : ℝ, |s| ≤ 1 / 2 → |EuTail s| ≤ E := by
    intro s hs
    have h := EuTail_abs_le hs
    have he : E = ((rhoC : ℚ) : ℝ) * ((usupC : ℚ) : ℝ) := by
      rw [hEdef, eC_eq]; push_cast; ring
    rw [he]; exact h
  have hr : ∀ s : ℝ, |s| ≤ 1 / 2 → |r0Poly s| ≤ R := by
    intro s hs
    rw [r0Poly_eq_sum]
    refine le_trans (r0Sum_abs_le s hs) ?_
    rw [hRdef]; norm_num [r0C]
  have hpt : ∀ s ∈ Set.uIcc (-(1:ℝ)/2) ((1:ℝ)/2),
      gFun s ^ 2 ≤ r0Poly s ^ 2 + (2 * E * R + E * E) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num)] at hs
    have hsabs : |s| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h1 := abs_le.mp (hE s hsabs)
    have h2 := abs_le.mp (hr s hsabs)
    rw [gFun]
    nlinarith [h1.1, h1.2, h2.1, h2.2, hEnn, hRnn]
  have hint : normSqI gFun
      ≤ ∫ s in (-(1:ℝ)/2)..(1/2), (r0Poly s ^ 2 + (2 * E * R + E * E)) := by
    rw [normSqI]
    refine intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_gFun.pow 2).intervalIntegrable _ _)
      (((continuous_r0Poly.pow 2).add continuous_const).intervalIntegrable _ _) ?_
    intro s hs
    exact hpt s (by rwa [Set.uIcc_of_le (by norm_num)])
  have hi1 : IntervalIntegrable (fun s : ℝ => r0Poly s ^ 2) volume (-(1:ℝ)/2) ((1:ℝ)/2) :=
    (continuous_r0Poly.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun _ : ℝ => (2 * E * R + E * E)) volume
      (-(1:ℝ)/2) ((1:ℝ)/2) := continuous_const.intervalIntegrable _ _
  have hsplit : (∫ s in (-(1:ℝ)/2)..(1/2), (r0Poly s ^ 2 + (2 * E * R + E * E)))
      = (∫ s in (-(1:ℝ)/2)..(1/2), r0Poly s ^ 2) + (2 * E * R + E * E) := by
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const]
    norm_num
  have hval : (∫ x in (-(1:ℝ)/2)..(1/2), r0Poly x ^ 2) = ((r0l2sqC : ℚ) : ℝ) := by
    rw [integral_r0_sq]; norm_num [r0l2sqC]
  rw [hsplit, hval] at hint
  have hgoal : ((gl2sqC : ℚ) : ℝ)
      = ((r0l2sqC : ℚ) : ℝ) + (2 * E * R + E * E) := by
    rw [hEdef, hRdef, gl2sqC_eq]; push_cast; ring
  rw [hgoal]
  exact hint

/-- **`‖z‖₂ ≤ zl2C`.** -/
theorem zFun_l2 (hw : IsProfile w) :
    Real.sqrt (normSqI (zFun w)) ≤ ((zl2C : ℚ) : ℝ) := by
  have hcoer : (5 / 9) * normSqI (zFun w)
      ≤ ∫ s in (-(1:ℝ)/2)..(1/2), zFun w s * gFun s := by
    rw [integral_z_mul_g hw]
    exact energyA_coercive (zFun w) (continuous_zFun hw)
  have hbridge : AristotleR.normSqI = normSqI := rfl
  have h := AristotleR.resolvent_l2_bound (zFun w) gFun (continuous_zFun hw)
    continuous_gFun hcoer
  rw [hbridge] at h
  have hgnn : (0:ℝ) ≤ ((gl2C : ℚ) : ℝ) := by exact_mod_cast gl2C_nonneg
  have hg : Real.sqrt (normSqI gFun) ≤ ((gl2C : ℚ) : ℝ) := by
    have h1 := normSqI_gFun_le
    have h2 : ((gl2sqC : ℚ) : ℝ) ≤ ((gl2C : ℚ) : ℝ) * ((gl2C : ℚ) : ℝ) := by
      exact_mod_cast gl2C_sq_ge
    calc Real.sqrt (normSqI gFun)
        ≤ Real.sqrt (((gl2C : ℚ) : ℝ) * ((gl2C : ℚ) : ℝ)) :=
          Real.sqrt_le_sqrt (le_trans h1 h2)
      _ = ((gl2C : ℚ) : ℝ) := Real.sqrt_mul_self hgnn
  have hz : ((zl2C : ℚ) : ℝ) = 9 / 5 * ((gl2C : ℚ) : ℝ) := by
    rw [zl2C_eq]; push_cast; ring
  rw [hz]
  linarith [h, hg]

/-- `∫|z| ≤ ‖z‖₂`, the `L¹ ⊆ L²` embedding on an interval of length one. -/
theorem integral_abs_zFun_le (hw : IsProfile w) :
    (∫ s in (-(1:ℝ)/2)..(1/2), |zFun w s|) ≤ Real.sqrt (normSqI (zFun w)) := by
  have hz := continuous_zFun hw
  have h := AristotleM.mass_diff_le (fun s => |zFun w s|) (fun _ => 0) hz.abs continuous_const
  have hm0 : AristotleM.massI (fun _ : ℝ => (0:ℝ)) = 0 := by
    simp [AristotleM.massI]
  have hns : AristotleM.normSqI (fun s => |zFun w s| - 0) = normSqI (zFun w) := by
    simp only [AristotleM.normSqI, normSqI, sub_zero]
    exact intervalIntegral.integral_congr (fun s _ => by rw [sq_abs])
  rw [hm0, hns, sub_zero] at h
  have hnn : 0 ≤ AristotleM.massI fun s => |zFun w s| := by
    refine intervalIntegral.integral_nonneg (by norm_num) ?_
    intro x _
    exact abs_nonneg _
  rw [abs_of_nonneg hnn] at h
  exact h

end ZetaLean.Pub1
