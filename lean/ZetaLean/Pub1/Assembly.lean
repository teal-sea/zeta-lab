/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Convergence

/-!
# Pub 1 strong closure: the staged assembly

The final, unconditional assembly is `ZetaLean.Pub1.Unconditional`; this module
is the staged one it is built on, and everything here is proved.

`strongClosureData_of_member` reduces the principal theorem to a single input,
membership of the constructed sequence in the source-admissible class, and
`sourceWindow_taper` reduces *that* to three analytic facts about `w`.  All three
are now theorems:

1. `w ∈ C²` near `I` — `WRegularity.w_contDiffOn`, from
   `pub1_kernel_second_deriv`, the elementary form of `F₁'' = 2δ₀ + q`;
2. radial monotonicity — `Concave.w_radial`, from the strict concavity bound
   `w'' < -0.59326318`, itself from the residual certificate `ZppBound.zpp_bound`;
3. the uniform `L¹` bounds — `TaperAdmissible`.

`sourceWindow_taper` below keeps its hypotheses in the `Ioo (-3/5) (3/5)` form
it was first stated in.  That form is *unsatisfiable* for the real `w`, whose
second derivative jumps at `±1/2`, so the instantiated version lives in
`Unconditional.sourceWindow_taper_final`, which asks only for what `w` has.
The theorem here is retained because it is true and because the discrepancy is
worth keeping visible.
-/

open Filter Topology MeasureTheory Set

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ} {L C₁ C₂ : ℝ}

/-- **Everything but admissibility.**  Given only that the constructed sequence
lies in the source-admissible class, all the remaining inputs of the principal
theorem are supplied by this development. -/
theorem strongClosureData_of_member (hw : IsProfile w)
    (hmem : ∀ n : ℕ, profile w (8 + (n : ℝ)) ∈ sourceAdmissible C₁ C₂) :
    StrongClosureData w C₁ C₂ where
  isProfile := hw
  energy_w := energyA_eq_massI_of_profile hw
  cStar_pos := cStar_pos_of_profile hw
  upper := massI_sq_le_of_profile hw
  member := hmem
  energy_pos := fun _ hv => energyA_pos_of_admissible hv
  quot_tendsto := quot_tendsto_cStar hw

/-- The principal theorem, with the single remaining input made explicit. -/
theorem pub1_strong_closure_of_member (hw : IsProfile w)
    (hmem : ∀ n : ℕ, profile w (8 + (n : ℝ)) ∈ sourceAdmissible C₁ C₂) :
    IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) :=
  pub1_strong_closure_of_data (strongClosureData_of_member hw hmem)

/-- The reciprocal orientation, likewise. -/
theorem pub1_strong_closure_reciprocal_of_member (hw : IsProfile w)
    (hmem : ∀ n : ℕ, profile w (8 + (n : ℝ)) ∈ sourceAdmissible C₁ C₂)
    (hmass : ∀ v ∈ sourceAdmissible C₁ C₂, massI v ≠ 0) :
    IsGLB (recipQuot '' sourceAdmissible C₁ C₂) (cStar w)⁻¹ :=
  pub1_strong_closure_reciprocal_of_data (strongClosureData_of_member hw hmem) hmass

/-! ### Reducing admissibility to three analytic facts, all now proved -/

/-- **The taper is a source window**, given the three analytic facts about `w`
listed in the module header.  Six of the eight admissibility fields — scale,
evenness, amplitude floor and ceiling, exact support, and radial monotonicity —
are proved here from `1/5 ≤ w ≤ 1` and evenness, both of which are
unconditional.  Note the `Ioo (-3/5) (3/5)` smoothness hypothesis is not
satisfiable for the real `w`; see `Unconditional.sourceWindow_taper_final`. -/
theorem sourceWindow_taper (hw : IsProfile w) (hL : (8 : ℝ) ≤ L)
    (hwC2 : ContDiffOn ℝ 2 w (Ioo (-(3 / 5) : ℝ) (3 / 5)))
    (hwpos : ∀ s ∈ Ioo (-(3 / 5) : ℝ) (3 / 5), 0 < w s)
    (hwrad : ∀ s₁ s₂ : ℝ, |s₁| ≤ |s₂| → |s₂| ≤ 1 / 2 → w s₂ ≤ w s₁)
    (hC₁ : ∫ u, |iteratedDeriv 2 (taper w L) u| ≤ C₁)
    (hC₂ : ∫ u, |iteratedDeriv 2 (fun y => taper w L y ^ 2) u| ≤ C₂) :
    SourceWindow (taper w L) L C₁ C₂ where
  scale := hL
  smooth := taper_contDiff hL hwC2 hwpos
  even := taper_even hL (profile_even hw)
  nonneg := taper_nonneg hL (fun s _ => (profile_bounds hw).1 s)
  le_one := taper_le_one hL (fun s _ => (profile_bounds hw).2 s)
  support := taper_support hL (fun s _ => (profile_bounds hw).1 s)
  radial := taper_radial hL (fun s _ => (profile_bounds hw).1 s) hwrad
  secondDerivL1 := hC₁
  sqSecondDerivL1 := hC₂

/-- `v_L` is the profile induced by `φ_L`, so a source window at every `L ≥ 8`
puts the whole sequence in the class. -/
theorem inducedProfile_taper (hw : IsProfile w) (hL : (8 : ℝ) ≤ L) :
    InducedProfile (profile w L) (taper w L) L := by
  intro s
  exact (profile_eq_taper_sq (L_pos hL)
    (fun t => le_trans (by norm_num) ((profile_bounds hw).1 t)) s).symm

/-- **The last reduction step.**  If the taper is a source window at every
`L ≥ 8`, the strong-closure theorem holds outright.  Its hypothesis is
discharged in `Unconditional.sourceWindow_taper_final`. -/
theorem pub1_strong_closure_of_sourceWindow (hw : IsProfile w)
    (hwin : ∀ L : ℝ, 8 ≤ L → SourceWindow (taper w L) L C₁ C₂) :
    IsLUB (quot '' sourceAdmissible C₁ C₂) (cStar w) := by
  refine pub1_strong_closure_of_member hw ?_
  intro n
  have hL : (8 : ℝ) ≤ 8 + (n : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact ⟨taper w (8 + (n : ℝ)), 8 + (n : ℝ), hwin _ hL, inducedProfile_taper hw hL⟩

end ZetaLean.Pub1
