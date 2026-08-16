/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Numeric

/-!
# Pub 1 strong closure: strict concavity and radial decrease of `w`

The step of `hunts/wide_search/RESULTS-xiprime-admissible-closure.md` that turns
the certified `C²` residual estimate into the *geometric* property the source
admissibility class actually requires:

```
‖w'' - u''‖_∞ < 0.006060899845   and   u'' ≤ 2c₁
      ⟹   w'' < -0.59326318 < 0
      ⟹   w'(0) = 0 and w' < 0 on (0,1/2]
      ⟹   w is strictly decreasing in |s|.
```

`secondDeriv_lt_of_certificate` is the bridge from the kernel-checked rational
arithmetic of `ZetaLean.Pub1.Numeric` into `ℝ`.  Everything after it is ordinary
one-variable calculus, and none of it re-derives standard analysis: the mean
value machinery comes from Mathlib.

Note which direction the evenness is used in.  `w'(0) = 0` is *forced* by
evenness alone; strict concavity then pushes `w'` strictly negative to the right
of the origin.  Concavity without evenness would not give radial monotonicity.
-/

open Set

namespace ZetaLean.Pub1

/-! ### From the exact rational certificate to a real bound -/

/-- **The certificate bridge.**  If the trial second derivative is at most
`2c₁` and the residual-derived `C²` error is at most `0.006060899845`, then the
true second derivative is strictly below `-0.59326318`.  The arithmetic is the
kernel-checked `concavity_margin`; this lemma only casts it into `ℝ`. -/
theorem secondDeriv_lt_of_certificate {W U : ℝ}
    (hU : U ≤ (uSecondDerivBound : ℝ)) (hz : |W - U| ≤ (residualC2 : ℝ)) :
    W < (concavityBound : ℝ) := by
  have hmargin : ((uSecondDerivBound + residualC2 : ℚ) : ℝ) < ((concavityBound : ℚ) : ℝ) := by
    exact_mod_cast concavity_margin
  push_cast at hmargin
  have h1 : W - U ≤ (residualC2 : ℝ) := (abs_le.mp hz).2
  linarith

/-- The strict concavity constant is negative in `ℝ`. -/
theorem concavityBound_neg_real : ((concavityBound : ℚ) : ℝ) < 0 := by
  exact_mod_cast concavityBound_neg

/-! ### Evenness pins the derivative at the origin -/

/-- The derivative of an even differentiable function vanishes at the origin.
This is the half of the radial-decrease argument that concavity cannot supply. -/
theorem deriv_eq_zero_of_even {w : ℝ → ℝ} (hdiff : Differentiable ℝ w)
    (heven : ∀ s, w (-s) = w s) : deriv w 0 = 0 := by
  have h1 : HasDerivAt w (deriv w 0) 0 := (hdiff 0).hasDerivAt
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hzero : ((fun s : ℝ => -s) 0) = (0 : ℝ) := by norm_num
  have h1' : HasDerivAt w (deriv w 0) ((fun s : ℝ => -s) 0) := by rw [hzero]; exact h1
  have h2 : HasDerivAt (w ∘ (fun s : ℝ => -s)) (deriv w 0 * (-1)) 0 :=
    HasDerivAt.comp (0 : ℝ) h1' hneg
  have hfun : (w ∘ (fun s : ℝ => -s)) = w := funext heven
  rw [hfun] at h2
  have h3 := h1.unique h2
  linarith

/-! ### Strict concavity forces strict radial decrease -/

variable {w : ℝ → ℝ}

/-- With `w''` strictly negative on `[0,1/2]`, the derivative is strictly
decreasing there. -/
theorem strictAntiOn_deriv (_hd1 : Differentiable ℝ w) (hd2 : Differentiable ℝ (deriv w))
    (hconc : ∀ s ∈ Icc (0 : ℝ) (1 / 2), deriv (deriv w) s < 0) :
    StrictAntiOn (deriv w) (Icc (0 : ℝ) (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 (1 / 2)) hd2.continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact hconc x ⟨hx.1.le, hx.2.le⟩

/-- `w' < 0` strictly to the right of the origin. -/
theorem deriv_neg_of_pos (hd1 : Differentiable ℝ w) (hd2 : Differentiable ℝ (deriv w))
    (heven : ∀ s, w (-s) = w s)
    (hconc : ∀ s ∈ Icc (0 : ℝ) (1 / 2), deriv (deriv w) s < 0)
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) (1 / 2)) : deriv w s < 0 := by
  have h0 : deriv w 0 = 0 := deriv_eq_zero_of_even hd1 heven
  have := strictAntiOn_deriv hd1 hd2 hconc (left_mem_Icc.mpr (by norm_num))
    ⟨hs.1.le, hs.2⟩ hs.1
  rwa [h0] at this

/-- **Strict radial decrease.**  `w` is strictly decreasing on `[0,1/2]`. -/
theorem strictAntiOn_w (hd1 : Differentiable ℝ w) (hd2 : Differentiable ℝ (deriv w))
    (heven : ∀ s, w (-s) = w s)
    (hconc : ∀ s ∈ Icc (0 : ℝ) (1 / 2), deriv (deriv w) s < 0) :
    StrictAntiOn w (Icc (0 : ℝ) (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc 0 (1 / 2)) hd1.continuous.continuousOn ?_
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_neg_of_pos hd1 hd2 heven hconc ⟨hx.1, hx.2.le⟩

/-- An even function agrees with its own value at `|s|`. -/
theorem eq_abs_of_even (heven : ∀ s, w (-s) = w s) (s : ℝ) : w s = w |s| := by
  rcases abs_cases s with ⟨h, -⟩ | ⟨h, -⟩
  · rw [h]
  · rw [h, heven]

/-- **Radial monotonicity of `w`**, in the form the source admissibility class
consumes: `|s₁| ≤ |s₂| ≤ 1/2` implies `w s₂ ≤ w s₁`. -/
theorem radial_antitone (hd1 : Differentiable ℝ w) (hd2 : Differentiable ℝ (deriv w))
    (heven : ∀ s, w (-s) = w s)
    (hconc : ∀ s ∈ Icc (0 : ℝ) (1 / 2), deriv (deriv w) s < 0)
    {s₁ s₂ : ℝ} (h12 : |s₁| ≤ |s₂|) (h2 : |s₂| ≤ 1 / 2) : w s₂ ≤ w s₁ := by
  have hanti := (strictAntiOn_w hd1 hd2 heven hconc).antitoneOn
  rw [eq_abs_of_even heven s₁, eq_abs_of_even heven s₂]
  exact hanti ⟨abs_nonneg s₁, le_trans h12 h2⟩ ⟨abs_nonneg s₂, h2⟩ h12

/-- Strict version: strictly larger radius gives strictly smaller value. -/
theorem radial_strictAnti (hd1 : Differentiable ℝ w) (hd2 : Differentiable ℝ (deriv w))
    (heven : ∀ s, w (-s) = w s)
    (hconc : ∀ s ∈ Icc (0 : ℝ) (1 / 2), deriv (deriv w) s < 0)
    {s₁ s₂ : ℝ} (h12 : |s₁| < |s₂|) (h2 : |s₂| ≤ 1 / 2) : w s₂ < w s₁ := by
  have hanti := strictAntiOn_w hd1 hd2 heven hconc
  rw [eq_abs_of_even heven s₁, eq_abs_of_even heven s₂]
  exact hanti ⟨abs_nonneg s₁, le_trans h12.le h2⟩ ⟨abs_nonneg s₂, h2⟩ h12

end ZetaLean.Pub1
