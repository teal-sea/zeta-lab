/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Aristotle.B
import ZetaLean.Pub1.Aristotle.C
import ZetaLean.Pub1.Aristotle.E1
import ZetaLean.Pub1.Aristotle.E2

/-!
# Pub 1 strong closure: the interval, the kernel, the operator, and `w`

The concrete setting of `RESULTS-xiprime-global-optimality.md`:

```
I = [-1/2, 1/2],   F₁(x) = |x| - 4x² + Σ_{k≥1} ((k-1)!/(2k)!)(2|x|)^(2k+1),
(T v)(s) = ∫_I F₁(s-t) v(t) dt,   A = I + T,   w = A⁻¹1,   c* = ⟨1, w⟩.
```

Two design points.

*No `L²` quotient space.*  The theorem is stated on honest functions with
`⟪f,g⟫ = ∫_I f g`, because the whole content of the source-admissible class is
pointwise (support, evenness, radial monotonicity, `C²`) and would have to be
lifted back off representatives anyway.  Completeness is never needed: the
Cauchy-Schwarz half is algebra, and the limit half only needs boundedness.

*The clamped kernel.*  `F₁` is **not** entire, and not even differentiable at the
origin: `F₁ x = fKer |x|` for the entire half-line function `fKer`, and the `|x|`
puts a corner at `0`.  What is true, and what matters here, is that `fKer`'s
series has infinite radius, so `F₁` grows without bound off `[-1,1]`; its row
mass `∫_I F₁(s-t) dt` is therefore bounded by `4/9` only for `s ∈ I`.
The Schur and Banach-fixed-point lemmas both want a hypothesis holding for every
real `s`.  `clampedKernel s t = F₁(clamp s - clamp t)` agrees with `F₁(s-t)` on
`I × I`, is globally nonnegative, symmetric and continuous, and has globally
bounded rows.  That is what makes those two lemmas applicable without weakening
anything: the quadratic form and the equation on `I` are untouched.
-/

open MeasureTheory

namespace ZetaLean.Pub1

/-! ### The kernel `F₁` -/

/-- The Farmer-Gonek-Lee pair-correlation form factor
`F₁(x) = |x| - 4x² + Σ_{k≥1} ((k-1)!/(2k)!)(2|x|)^(2k+1)`. -/
noncomputable def F1 : ℝ → ℝ := AristotleE1.F1

theorem F1_continuous : Continuous F1 := AristotleE2.F1_continuous

theorem F1_even (x : ℝ) : F1 (-x) = F1 x := AristotleE1.F1_even x

/-- `F₁ ≥ 0` on `[-1,1]`, which is where the kernel is ever evaluated. -/
theorem F1_nonneg {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ F1 x := AristotleE1.F1_nonneg x hx

/-- `M = ∫₀¹ F₁ ≤ 4/9`. -/
theorem F1_mass_le : (∫ x in (0:ℝ)..1, F1 x) ≤ 4 / 9 := AristotleE1.F1_integral_le

/-- **The row bound.**  Every row of the kernel operator has mass at most `4/9`,
which is what makes `A = I + T` coercive with constant `5/9`. -/
theorem F1_row_bound {s : ℝ} (hs : |s| ≤ 1 / 2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t)) ≤ 4 / 9 :=
  AristotleE2.F1_row_bound s hs

/-! ### Clamping to `I` -/

/-- Clamp a real to `I = [-1/2, 1/2]`. -/
noncomputable def clampI (s : ℝ) : ℝ := max (-(1 / 2)) (min (1 / 2) s)

theorem clampI_continuous : Continuous clampI := by
  unfold clampI; fun_prop

theorem clampI_mem (s : ℝ) : |clampI s| ≤ 1 / 2 := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem clampI_eq_self {s : ℝ} (hs : |s| ≤ 1 / 2) : clampI s = s := by
  obtain ⟨h1, h2⟩ := abs_le.mp hs
  rw [clampI, min_eq_right h2, max_eq_right h1]

/-- The clamped kernel.  On `I × I` it *is* `F₁(s-t)`; off it, it repeats the
boundary values, which keeps the rows bounded everywhere. -/
noncomputable def clampedKernel (s t : ℝ) : ℝ := F1 (clampI s - clampI t)

theorem clampedKernel_continuous :
    Continuous fun p : ℝ × ℝ => clampedKernel p.1 p.2 :=
  F1_continuous.comp ((clampI_continuous.comp continuous_fst).sub
    (clampI_continuous.comp continuous_snd))

theorem clampedKernel_nonneg (s t : ℝ) : 0 ≤ clampedKernel s t := by
  refine F1_nonneg ?_
  have h1 := abs_le.mp (clampI_mem s)
  have h2 := abs_le.mp (clampI_mem t)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem clampedKernel_symm (s t : ℝ) : clampedKernel s t = clampedKernel t s := by
  rw [clampedKernel, clampedKernel, ← F1_even (clampI t - clampI s)]
  ring_nf

theorem clampI_neg (s : ℝ) : clampI (-s) = -clampI s := by
  simp only [clampI, max_def, min_def]
  split_ifs <;> linarith

/-- The clamped kernel is reflection invariant, which is what forces `w` to be
even. -/
theorem clampedKernel_refl (s t : ℝ) : clampedKernel (-s) (-t) = clampedKernel s t := by
  rw [clampedKernel, clampedKernel, clampI_neg, clampI_neg, ← F1_even (clampI s - clampI t)]
  ring_nf

/-- The clamped kernel has the `4/9` row bound at *every* real `s`. -/
theorem clampedKernel_row (s : ℝ) :
    (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t) ≤ 4 / 9 := by
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), F1 (clampI s - t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have : clampI t = t := clampI_eq_self (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp only [clampedKernel, this]
  rw [hcongr]
  exact F1_row_bound (clampI_mem s)

theorem clampedKernel_row_abs (s : ℝ) :
    (∫ t in (-(1:ℝ)/2)..(1/2), |clampedKernel s t|) ≤ 4 / 9 := by
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), |clampedKernel s t|)
      = ∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    exact abs_of_nonneg (clampedKernel_nonneg s t)
  rw [hcongr]
  exact clampedKernel_row s

/-! ### The quadratic form -/

/-- `⟪1, v⟫ = ∫_I v`. -/
noncomputable def massI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s

/-- `‖v‖₂² = ∫_I v²`. -/
noncomputable def normSqI (v : ℝ → ℝ) : ℝ := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2

/-- `⟪T v, v⟫ = ∬_{I²} F₁(s-t) v(s) v(t)`. -/
noncomputable def kerForm (v : ℝ → ℝ) : ℝ :=
  ∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (v s * v t)

/-- `⟪A v, v⟫ = ‖v‖₂² + ⟪T v, v⟫`, the energy of the source functional. -/
noncomputable def energyA (v : ℝ → ℝ) : ℝ := normSqI v + kerForm v

theorem normSqI_nonneg (v : ℝ → ℝ) : 0 ≤ normSqI v := by
  refine intervalIntegral.integral_nonneg (by norm_num) ?_
  intro x _
  positivity

/-- The kernel form computed with the clamped kernel is the same number: the two
kernels agree on the square of integration. -/
theorem kerForm_eq_clamped (v : ℝ → ℝ) :
    (∫ s in (-(1:ℝ)/2)..(1/2), ∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * (v s * v t))
      = kerForm v := by
  unfold kerForm
  refine intervalIntegral.integral_congr ?_
  intro s hs
  rw [Set.uIcc_of_le (by norm_num)] at hs
  have hsc : clampI s = s :=
    clampI_eq_self (abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩)
  simp only
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [Set.uIcc_of_le (by norm_num)] at ht
  have htc : clampI t = t :=
    clampI_eq_self (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  simp only [clampedKernel, hsc, htc]

/-- **The Schur bound for the Pub 1 kernel.**  `|⟪Tv, v⟫| ≤ (4/9)‖v‖₂²`. -/
theorem kerForm_abs_le (v : ℝ → ℝ) (hv : Continuous v) :
    |kerForm v| ≤ (4 / 9) * normSqI v := by
  have h := AristotleB.schur_quadratic_bound clampedKernel clampedKernel_continuous
    clampedKernel_nonneg clampedKernel_symm (4 / 9) clampedKernel_row v hv
  rwa [kerForm_eq_clamped v] at h

/-- **Coercivity.**  `⟪Av, v⟫ ≥ (5/9)‖v‖₂²`, from `‖T‖ ≤ 4/9`. -/
theorem energyA_coercive (v : ℝ → ℝ) (hv : Continuous v) :
    (5 / 9) * normSqI v ≤ energyA v := by
  have h := abs_le.mp (kerForm_abs_le v hv)
  unfold energyA
  linarith [h.1]

theorem energyA_nonneg (v : ℝ → ℝ) (hv : Continuous v) : 0 ≤ energyA v := by
  have h1 := energyA_coercive v hv
  have h2 := normSqI_nonneg v
  linarith

/-! ### The profile `w = A⁻¹1` -/

/-- `w` solves `w + T w = 1` on `I`.  The equation is stated with the clamped
kernel, which on `I` is the genuine one; off `I` it extends `w` boundedly. -/
def IsProfile (w : ℝ → ℝ) : Prop :=
  Continuous w ∧ (∃ C, ∀ s, |w s| ≤ C) ∧
    ∀ s : ℝ, w s + (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * w t) = 1

/-- **`w = A⁻¹1` exists.**  The kernel operator is a `4/9`-contraction on the
bounded continuous functions, so `w ↦ 1 - Tw` has a fixed point. -/
theorem exists_profile : ∃ w : ℝ → ℝ, IsProfile w :=
  AristotleC.exists_continuous_solution clampedKernel clampedKernel_continuous (4 / 9)
    (by norm_num) (by norm_num) clampedKernel_row_abs

/-- On `I` the profile solves the genuine equation `w(s) + ∫_I F₁(s-t)w(t)dt = 1`. -/
theorem IsProfile.eq_on_I {w : ℝ → ℝ} (hw : IsProfile w) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    w s + (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * w t) = 1 := by
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), clampedKernel s t * w t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * w t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    have htc : clampI t = t :=
      clampI_eq_self (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    simp only [clampedKernel, clampI_eq_self hs, htc]
  rw [← hcongr]
  exact hw.2.2 s

/-- **The constant.**  `c* = ⟨1, A⁻¹1⟩ = ∫_I w`. -/
noncomputable def cStar (w : ℝ → ℝ) : ℝ := massI w

end ZetaLean.Pub1
