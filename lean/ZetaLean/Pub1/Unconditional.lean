/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Assembly
import ZetaLean.Pub1.TaperAdmissible

/-!
# Pub 1 strong closure: the source-admissible sequence, unconditionally

Every field of `SourceWindow` now has an unconditional proof for the taper:

* `smooth` from `taper_contDiff_of_profile`;
* `even`, `nonneg`, `le_one`, `support` from `1/5 ≤ w ≤ 1` and evenness;
* `radial` from `w_radial`, i.e. from strict concavity, i.e. from the residual
  certificate;
* the two `L¹` fields from `TaperAdmissible`.

So the constructed sequence lies in the class, `member` is discharged, and the
principal theorems lose their last hypothesis.
-/

open Set MeasureTheory

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

/-- **The taper is a source window**, unconditionally. -/
theorem sourceWindow_taper_final (hw : IsProfile w) (C₁ C₂ : ℝ)
    (h1 : ∀ L : ℝ, 8 ≤ L → (∫ u : ℝ, |iteratedDeriv 2 (taper w L) u|) ≤ C₁)
    (h2 : ∀ L : ℝ, 8 ≤ L →
      (∫ u : ℝ, |iteratedDeriv 2 (fun y : ℝ => taper w L y ^ 2) u|) ≤ C₂)
    {L : ℝ} (hL : 8 ≤ L) :
    SourceWindow (taper w L) L C₁ C₂ where
  scale := hL
  smooth := taper_contDiff_of_profile hw hL
  even := taper_even hL (profile_even hw)
  nonneg := taper_nonneg hL (fun s _ => (profile_bounds hw).1 s)
  le_one := taper_le_one hL (fun s _ => (profile_bounds hw).2 s)
  support := taper_support hL (fun s _ => (profile_bounds hw).1 s)
  radial := taper_radial hL (fun s _ => (profile_bounds hw).1 s)
    (fun s₁ s₂ h12 hs2 => w_radial hw h12 hs2)
  secondDerivL1 := h1 L hL
  sqSecondDerivL1 := h2 L hL

/-- **The constructed sequence lies in the source-admissible class.** -/
theorem member_final (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, ∀ n : ℕ, profile w (8 + (n : ℝ)) ∈ sourceAdmissible C₁ C₂ := by
  obtain ⟨C₁, h1⟩ := taper_secondDeriv_L1_of_profile hw (L := 8) le_rfl
  obtain ⟨C₂, h2⟩ := taper_sq_secondDeriv_L1_of_profile hw
  refine ⟨C₁, C₂, fun n => ?_⟩
  have hL : (8 : ℝ) ≤ 8 + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact ⟨taper w (8 + (n : ℝ)), 8 + (n : ℝ),
    sourceWindow_taper_final hw C₁ C₂ h1 h2 hL, inducedProfile_taper hw hL⟩

/-- **`StrongClosureData` holds unconditionally.** -/
theorem strongClosureData_final (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, StrongClosureData w C₁ C₂ := by
  obtain ⟨C₁, C₂, hmem⟩ := member_final hw
  exact ⟨C₁, C₂, strongClosureData_of_member hw hmem⟩

/-- **PUB 1 SOURCE-ADMISSIBLE STRONG CLOSURE, unconditional.**

`sup_{v ∈ 𝒜_source} ⟨1,v⟩²/⟨Av,v⟩ = ⟨1, A⁻¹1⟩ = c*`, with no analytic or
membership hypothesis: the only assumption is `IsProfile w`, which says that `w`
is the profile `A⁻¹1` the statement is about. -/
theorem pub1_strong_closure (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) := by
  obtain ⟨C₁, C₂, hdata⟩ := strongClosureData_final hw
  exact ⟨C₁, C₂, pub1_strong_closure_of_data hdata⟩

/-- **The reciprocal orientation, unconditional.** -/
theorem pub1_strong_closure_reciprocal (hw : IsProfile w) :
    ∃ C₁ C₂ : ℝ, IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  obtain ⟨C₁, C₂, hdata⟩ := strongClosureData_final hw
  refine ⟨C₁, C₂, pub1_strong_closure_reciprocal_of_data hdata ?_⟩
  intro v hv
  have hpos : 0 < massI v := by
    have hc : Continuous v := sourceAdmissible_continuous hv
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) ?_
      (by norm_num)
    intro x hx
    exact sourceAdmissible_pos hv hx
  exact ne_of_gt hpos

/-- The profile exists, so the theorems are not vacuous. -/
theorem pub1_strong_closure_exists :
    ∃ (w : ℝ → ℝ) (C₁ C₂ : ℝ), IsProfile w ∧
      IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) ∧
      IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ := by
  obtain ⟨w, hw⟩ := exists_profile
  obtain ⟨C₁, C₂, hdata⟩ := strongClosureData_final hw
  have hmass : ∀ v ∈ sourceAdmissible C₁ C₂, massI v ≠ 0 := by
    intro v hv
    have hc : Continuous v := sourceAdmissible_continuous hv
    refine ne_of_gt (intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable _ _) ?_ (by norm_num))
    intro x hx
    exact sourceAdmissible_pos hv hx
  exact ⟨w, C₁, C₂, hw, pub1_strong_closure_of_data hdata,
    pub1_strong_closure_reciprocal_of_data hdata hmass⟩

end ZetaLean.Pub1
