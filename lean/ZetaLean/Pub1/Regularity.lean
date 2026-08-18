/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Aristotle.N
import ZetaLean.Pub1.Aristotle.S
import ZetaLean.Pub1.Setting

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

/-! ### The Pub 1 kernel

`F₁ x = fKer |x|` with `fKer` the entire half-line form factor of
`Aristotle/S`, which satisfies `fKer 0 = 0` and `fKer'(0) = 1`.  Those two facts
are exactly what the split-kernel argument needs: the first makes the boundary
terms cancel at the first differentiation, the second makes them add up to
`2 v(s)` at the second.  That `2` is the delta mass, and it is not optional. -/

/-- The Pub 1 kernel is the half-line form factor composed with `|·|`. -/
theorem F1_eq_fKer (x : ℝ) : F1 x = AristotleS.fKer |x| := by
  show AristotleE1.F1 x = AristotleS.fKer |x|
  rw [AristotleE1.F1, AristotleS.fKer, sq_abs]
  exact rfl

/-- `fKer 0 = 0`: the moving-endpoint terms cancel at the first derivative. -/
theorem fKer_zero : AristotleS.fKer 0 = 0 := AristotleS.fKer_zero

/-- **`fKer'(0) = 1`.**  This is the coefficient that becomes the delta mass:
the two moving endpoints each contribute `fKer'(0) v(s)`, so the second
derivative carries `2 v(s)`, matching `F₁'' = 2δ₀ + q` exactly. -/
theorem fKer_deriv_zero : deriv AristotleS.fKer 0 = 1 := AristotleS.fKer_deriv_zero

/-- `q = fKer''` is continuous, from `fKer ∈ C³`. -/
theorem fKer_second_deriv_continuous : Continuous (deriv (deriv AristotleS.fKer)) := by
  have h3 : ContDiff ℝ 3 AristotleS.fKer := AristotleS.fKer_contDiff
  have h2 : ContDiff ℝ 2 (deriv AristotleS.fKer) := by
    have := (contDiff_succ_iff_deriv (n := 2) (f := AristotleS.fKer)).mp (by exact_mod_cast h3)
    exact this.2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv AristotleS.fKer)) := by
    have := (contDiff_succ_iff_deriv (n := 1) (f := deriv AristotleS.fKer)).mp
      (by exact_mod_cast h2)
    exact this.2.2
  exact h1.continuous

/-- **The second derivative of the Pub 1 kernel convolution.**

    (T v)''(s) = 2 v(s) + ∫_I q(|s-t|) v(t) dt,   q = fKer''.

The `2 v(s)` is the `2 δ₀` of the informal identity, and it arises here from the
two moving endpoints of the split integral, with no distribution theory. -/
theorem pub1_kernel_second_deriv (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ)
    (hs : |s| ≤ 1 / 2) :
    HasDerivAt
      (fun σ : ℝ => (∫ t in (-(1:ℝ)/2)..σ, deriv AristotleS.fKer (σ - t) * v t)
        - ∫ t in σ..(1/2:ℝ), deriv AristotleS.fKer (t - σ) * v t)
      (2 * v s
        + ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * v t) s := by
  have h := splitKernel_second_deriv AristotleS.fKer AristotleS.fKer_contDiff
    AristotleS.fKer_zero v hv s hs fKer_second_deriv_continuous
  rwa [AristotleS.fKer_deriv_zero, mul_one] at h

/-- On `I`, the Pub 1 operator is the split integral the derivative theorem
applies to. -/
theorem F1_conv_eq_split (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) (hs : |s| ≤ 1 / 2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * v t)
      = AristotleN.splitKernelIntegral AristotleS.fKer v s := by
  have hc : Continuous AristotleS.fKer :=
    AristotleS.fKer_contDiff.continuous
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * v t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), AristotleS.fKer |s - t| * v t := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [F1_eq_fKer]
  rw [hcongr, integral_eq_splitKernel AristotleS.fKer hc v hv s hs]

end ZetaLean.Pub1
