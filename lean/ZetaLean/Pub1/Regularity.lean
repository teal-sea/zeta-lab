/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Aristotle.N

/-!
# Pub 1 strong closure: `C²` regularity of the kernel convolution

The bridge from `Aristotle/N` to the actual Pub 1 operator.

`N` differentiates `s ↦ ∫_{-1/2}^{s} f(s-t)v(t) + ∫_{s}^{1/2} f(t-s)v(t)` twice
and finds `2 f'(0) v(s)` from the moving endpoints.  Here we identify that split
form with the honest convolution `∫_I F(s-t) v(t) dt` whenever `F x = f |x|`,
which is exactly the shape of `F₁`.

The point is that the `2 δ₀` of the informal identity `F₁'' = 2δ₀ + q` never
appears as a distribution: it is the sum of the two moving-endpoint terms, and
`f'(0) = 1` for the Farmer-Gonek-Lee kernel.
-/

open MeasureTheory

namespace ZetaLean.Pub1

/-- On `I`, a convolution against `x ↦ f |x|` is the split integral of `N`. -/
theorem integral_eq_splitKernel (f : ℝ → ℝ) (hf : Continuous f)
    (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) (hs : |s| ≤ 1 / 2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), f |s - t| * v t)
      = AristotleN.splitKernelIntegral f v s := by
  have hab := abs_le.mp hs
  have h1 : (-(1:ℝ)/2) ≤ s := by linarith [hab.1]
  have h2 : s ≤ (1:ℝ)/2 := by linarith [hab.2]
  have hc : Continuous fun t : ℝ => f |s - t| * v t :=
    ((hf.comp ((continuous_const.sub continuous_id).abs))).mul hv
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (a := -(1:ℝ)/2) (b := s) (c := (1:ℝ)/2)
    (f := fun t : ℝ => f |s - t| * v t)
    (hc.intervalIntegrable (μ := volume) _ _) (hc.intervalIntegrable (μ := volume) _ _)
  rw [AristotleN.splitKernelIntegral, ← hsplit]
  congr 1
  · refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le h1] at ht
    simp only
    rw [abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ s - t)]
  · refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le h2] at ht
    simp only
    rw [abs_of_nonpos (by linarith [ht.1] : s - t ≤ 0), neg_sub]

/-- **The second derivative of the kernel convolution.**  With `F x = f |x|`,
`f 0 = 0` and `f` of class `C³`, the map

    σ ↦ ∫_{-1/2}^{σ} f(σ-t)v(t) dt + ∫_{σ}^{1/2} f(t-σ)v(t) dt

has second derivative `2 f'(0) v(s) + ∫_I f''(|s-t|) v(t) dt`.  The first
summand is the `2 δ₀` contribution, obtained without distribution theory. -/
theorem splitKernel_second_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (hf0 : f 0 = 0)
    (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) (hs : |s| ≤ 1 / 2)
    (hf2 : Continuous (deriv (deriv f))) :
    HasDerivAt
      (fun σ : ℝ => (∫ t in (-(1:ℝ)/2)..σ, deriv f (σ - t) * v t)
        - ∫ t in σ..(1/2:ℝ), deriv f (t - σ) * v t)
      (2 * deriv f 0 * v s
        + ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv f) |s - t| * v t) s := by
  have hmain := AristotleN.splitKernelIntegral_hasDerivAt_two f hf hf0 v hv s
  have hrw : (∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv f) |s - t| * v t)
      = (∫ t in (-(1:ℝ)/2)..s, deriv (deriv f) (s - t) * v t)
        + ∫ t in s..(1/2:ℝ), deriv (deriv f) (t - s) * v t := by
    rw [integral_eq_splitKernel (deriv (deriv f)) hf2 v hv s hs,
      AristotleN.splitKernelIntegral]
  rw [hrw]
  exact hmain

end ZetaLean.Pub1
