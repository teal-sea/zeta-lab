/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.ZppBound
import ZetaLean.Pub1.UpolyD2

/-!
# Pub 1 strong closure: strict concavity and radial monotonicity of `w`

`w'' = u'' + (w'' - u'')`, with `u'' ≤ 2c₁` and `‖w'' - u''‖_∞ < 0.006060899845`,
so `w'' < -0.59326318` on the interior.  Evenness pins `w'(0) = 0`, and strict
concavity then drives `w'` negative to the right of the origin, so `w` is
antitone in `|s|`.

Everything is stated on the *open* interval or via continuity on the closed one.
`Concavity.lean`'s earlier `radial_antitone` assumed `Differentiable ℝ w` on all
of `ℝ`, which `w` does not satisfy at `±1/2`; `w_radial` below replaces it and
needs only interior differentiability.
-/

open Set MeasureTheory

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

/-- **Strict concavity.**  `w'' < -0.59326318` on the interior. -/
theorem w_second_deriv_lt (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    deriv (deriv w) s < ((concavityBound : ℚ) : ℝ) := by
  have h1 := zpp_bound hw hs
  have h2 : deriv (deriv uPoly) s ≤ ((uSecondDerivBound : ℚ) : ℝ) := by
    rw [deriv_deriv_uPoly_sum]; exact uSum2_le s
  have hm : ((uSecondDerivBound : ℚ) : ℝ) + ((residualC2 : ℚ) : ℝ)
      < ((concavityBound : ℚ) : ℝ) := by exact_mod_cast concavity_margin
  have hres : ((residualC2 : ℚ) : ℝ) = 6060899845 / 10 ^ 12 := by norm_num [residualC2]
  rw [hres] at hm
  have h3 := (abs_lt.mp h1).2
  linarith [h2, h3, hm]

theorem concavityBound_neg' : ((concavityBound : ℚ) : ℝ) < 0 := by norm_num [concavityBound]

/-- `w'` is strictly decreasing on the interior. -/
theorem w_deriv_strictAnti (hw : IsProfile w) : StrictAntiOn (deriv w) Iint := by
  refine strictAntiOn_of_deriv_neg (by rw [Iint]; exact convex_Ioo _ _) ?_ ?_
  · exact (w_contDiffOn hw).continuousOn_deriv_of_isOpen isOpen_Iint (by norm_num)
  · intro x hx
    rw [Iint, interior_Ioo] at hx
    exact lt_trans (w_second_deriv_lt hw hx) concavityBound_neg'

/-- `w' < 0` strictly to the right of the origin. -/
theorem w_deriv_neg (hw : IsProfile w) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    deriv w s < 0 := by
  have hz : (0:ℝ) ∈ Iint := by rw [Iint]; constructor <;> norm_num
  have hsI : s ∈ Iint := by rw [Iint]; constructor <;> [linarith; linarith]
  have h := w_deriv_strictAnti hw hz hsI hs0
  rwa [deriv_w_zero hw] at h

/-- **`w` is antitone on `[0,1/2]`**, by continuity plus `w' ≤ 0` inside. -/
theorem w_antitoneOn (hw : IsProfile w) : AntitoneOn w (Icc (0:ℝ) (1/2)) := by
  have hdiff : DifferentiableOn ℝ w (interior (Icc (0:ℝ) (1/2))) := by
    rw [interior_Icc]
    intro x hx
    have hxI : x ∈ Iint := by
      rw [Iint]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
    exact ((hasDerivAt_w hw hxI).differentiableAt).differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hw.1.continuousOn hdiff
  intro x hx
  rw [interior_Icc] at hx
  exact le_of_lt (w_deriv_neg hw hx.1 hx.2)

theorem w_eq_abs (hw : IsProfile w) (s : ℝ) : w s = w |s| := by
  rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h, profile_even hw]

/-- **Radial monotonicity of `w`**, the source-admissibility field.  This is the
statement `Concavity.radial_antitone` was reaching for, with the global
differentiability hypothesis removed. -/
theorem w_radial (hw : IsProfile w) {s₁ s₂ : ℝ} (h12 : |s₁| ≤ |s₂|)
    (h2 : |s₂| ≤ 1 / 2) : w s₂ ≤ w s₁ := by
  rw [w_eq_abs hw s₁, w_eq_abs hw s₂]
  exact w_antitoneOn hw ⟨abs_nonneg s₁, le_trans h12 h2⟩ ⟨abs_nonneg s₂, h2⟩ h12

end ZetaLean.Pub1
