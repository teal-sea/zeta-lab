/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.WRegularity
import ZetaLean.Pub1.Window
import ZetaLean.Pub1.Aristotle.J2
import ZetaLean.Pub1.Aristotle.TU2

/-!
# Pub 1 strong closure: obligation D, discharged

With interior `C²` regularity of `w` and its two sup bounds in hand
(`ZetaLean.Pub1.WRegularity`), every hypothesis of the taper estimates is now
satisfiable, which was not true of the earlier versions: those asked for `C²` on
a neighbourhood of the closed interval, which is false for `w`.

`sourceWindow_taper_open` assembles seven of the eight source-admissibility
fields for `φ_L = √w(·/L)·η(L/2-|·|)`.  The eighth, radial monotonicity, is the
only one still open, and it reduces to strict concavity of `w`, hence to the
residual certificate.
-/

open Set MeasureTheory

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

/-- `√w` is `C²` on the interior with sup bounds, from `w ≥ 1/5` there. -/
theorem sqrtw_contDiffOn_bounds (hw : IsProfile w) :
    ContDiffOn ℝ 2 (fun s => Real.sqrt (w s)) Iint ∧
    ∃ C0 C1 C2 : ℝ, ∀ s ∈ Iint,
      |Real.sqrt (w s)| ≤ C0 ∧ |deriv (fun y => Real.sqrt (w y)) s| ≤ C1 ∧
      |deriv (deriv (fun y => Real.sqrt (w y))) s| ≤ C2 :=
  AristotleJ2.sqrt_comp_contDiffOn_bounds w (w_contDiffOn hw)
    (fun s _ => (profile_bounds hw).1 s) (fun s _ => (profile_bounds hw).2 s)
    (wB2 / 2) wB2 (fun s hs => w_deriv_bound hw hs) (fun s hs => w_second_deriv_bound hw hs)

/-- **The taper is `C²`**, unconditionally in `w`. -/
theorem taper_contDiff_of_profile (hw : IsProfile w) {L : ℝ} (hL : 8 ≤ L) :
    ContDiff ℝ 2 (taper w L) := by
  obtain ⟨hsq, C0, C1, C2, hC⟩ := sqrtw_contDiffOn_bounds hw
  have h := AristotleJ2.taper_contDiff_open (fun s => Real.sqrt (w s)) L hL hsq C0 C1 C2
    (fun y hy => (hC y hy).1) (fun y hy => (hC y hy).2.1) (fun y hy => (hC y hy).2.2)
  exact h

/-- **`‖φ_L''‖₁` is bounded uniformly in `L ≥ 8`.** -/
theorem taper_secondDeriv_L1_of_profile (hw : IsProfile w) {L : ℝ} (hL : 8 ≤ L) :
    ∃ C₁ : ℝ, ∀ L' : ℝ, 8 ≤ L' →
      (∫ u : ℝ, |iteratedDeriv 2 (taper w L') u|) ≤ C₁ := by
  obtain ⟨hsq, C0, C1, C2, hC⟩ := sqrtw_contDiffOn_bounds hw
  refine ⟨C2 / 8 + 4 * C1 / 8 + (35 / 4) * C0, fun L' hL' => ?_⟩
  have hφ : ContDiff ℝ 2 (fun u : ℝ => Real.sqrt (w (u / L')) * eta (L' / 2 - |u|)) :=
    taper_contDiff_of_profile hw hL'
  have h := AristotleTU2.taper_second_deriv_L1_bound_open (fun s => Real.sqrt (w s)) L'
    C0 C1 C2 hL' hsq hφ (fun y hy => (hC y hy).1) (fun y hy => (hC y hy).2.1)
    (fun y hy => (hC y hy).2.2)
  have hC0nn : 0 ≤ C0 := le_trans (abs_nonneg _) (hC 0 (by rw [Iint]; constructor <;> norm_num)).1
  have hC1nn : 0 ≤ C1 :=
    le_trans (abs_nonneg _) (hC 0 (by rw [Iint]; constructor <;> norm_num)).2.1
  have hC2nn : 0 ≤ C2 :=
    le_trans (abs_nonneg _) (hC 0 (by rw [Iint]; constructor <;> norm_num)).2.2
  have hmono : C2 / L' + 4 * C1 / L' + (35 / 4) * C0
      ≤ C2 / 8 + 4 * C1 / 8 + (35 / 4) * C0 := by
    have h8 : (0:ℝ) < 8 := by norm_num
    have hL8 : (0:ℝ) < L' := by linarith
    have e1 : C2 / L' ≤ C2 / 8 := div_le_div_of_nonneg_left hC2nn h8 hL'
    have e2 : 4 * C1 / L' ≤ 4 * C1 / 8 := div_le_div_of_nonneg_left (by linarith) h8 hL'
    linarith
  have heq : taper w L' = fun u : ℝ => Real.sqrt (w (u / L')) * eta (L' / 2 - |u|) := rfl
  rw [heq]
  exact le_trans h hmono

end ZetaLean.Pub1
