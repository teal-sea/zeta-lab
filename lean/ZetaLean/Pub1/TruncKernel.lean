/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.CertDefs
import ZetaLean.Pub1.Regularity

/-!
# Pub 1 strong closure: the truncated kernel as a half-line polynomial

`truncKernel x = fKerM |x|` with `fKerM` a *polynomial*, so the split-kernel
second-derivative theorem applies to it exactly as it does to the full kernel.

That is the trick that avoids any smoothness theory for the tail: writing
`E = A - A₀`, the second derivative of `E u` is the difference of two
applications of the same theorem,

```
      (T u)''  = 2u + q   * u
      (T₀ u)'' = 2u + q_M * u        ⟹  (E u)'' = (q - q_M) * u
```

and the `2u` delta terms cancel, because `fKer` and `fKerM` have the same `|x|`
term and hence the same `f'(0) = 1`.  Only a bound on `q - q_M` is then needed,
never its smoothness.
-/

open Finset MeasureTheory

namespace ZetaLean.Pub1

/-- The truncated kernel on the half line. -/
noncomputable def fKerM (y : ℝ) : ℝ := -4 * y ^ 2 + ∑ k ∈ range 21, aK k * y ^ (2 * k + 1)

theorem truncKernel_eq_fKerM (x : ℝ) : truncKernel x = fKerM |x| := by
  rw [truncKernel, fKerM, sq_abs]

theorem fKerM_contDiff (n : ℕ) : ContDiff ℝ n fKerM := by
  unfold fKerM
  refine ContDiff.add (by fun_prop) ?_
  exact ContDiff.sum (fun k _ => by fun_prop)

theorem fKerM_zero : fKerM 0 = 0 := by
  unfold fKerM
  simp

/-- `fKerM'(0) = 1`: the same delta coefficient as the full kernel, which is why
the `2u` terms cancel in the difference. -/
theorem fKerM_deriv_zero : deriv fKerM 0 = 1 := by
  have h : HasDerivAt fKerM (-4 * (2 * (0:ℝ) ^ 1) + ∑ k ∈ range 21,
      aK k * ((2 * k + 1 : ℕ) * (0:ℝ) ^ (2 * k))) 0 := by
    unfold fKerM
    refine HasDerivAt.add ?_ ?_
    · simpa using (((hasDerivAt_pow 2 (0:ℝ)).const_mul (-4 : ℝ)))
    · exact HasDerivAt.fun_sum (fun k _ => (hasDerivAt_pow (2 * k + 1) 0).const_mul (aK k))
  rw [h.deriv]
  rw [Finset.sum_range_succ']
  norm_num [aK]

/-- `q_M = fKerM''` is continuous (it is a polynomial). -/
theorem fKerM_second_deriv_continuous : Continuous (deriv (deriv fKerM)) := by
  have h3 : ContDiff ℝ 3 fKerM := fKerM_contDiff 3
  have h2 : ContDiff ℝ 2 (deriv fKerM) := by
    have := (contDiff_succ_iff_deriv (n := 2) (f := fKerM)).mp (by exact_mod_cast h3)
    exact this.2.2
  have h1 : ContDiff ℝ 1 (deriv (deriv fKerM)) := by
    have := (contDiff_succ_iff_deriv (n := 1) (f := deriv fKerM)).mp (by exact_mod_cast h2)
    exact this.2.2
  exact h1.continuous

/-- **The truncated operator's second derivative**, by the same theorem, with the
same `2 v(s)` delta term because `fKerM'(0) = fKer'(0) = 1`. -/
theorem truncKernel_second_deriv (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ)
    (hs : |s| ≤ 1 / 2) :
    HasDerivAt
      (fun σ : ℝ => (∫ t in (-(1:ℝ)/2)..σ, deriv fKerM (σ - t) * v t)
        - ∫ t in σ..(1/2:ℝ), deriv fKerM (t - σ) * v t)
      (2 * v s
        + ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv fKerM) |s - t| * v t) s := by
  have h := splitKernel_second_deriv fKerM (fKerM_contDiff 3) fKerM_zero v hv s hs
    fKerM_second_deriv_continuous
  rwa [fKerM_deriv_zero, mul_one] at h

/-- On `I`, the truncated convolution is the split integral. -/
theorem truncKernel_conv_eq_split (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ)
    (hs : |s| ≤ 1 / 2) :
    (∫ t in (-(1:ℝ)/2)..(1/2), truncKernel (s - t) * v t)
      = AristotleN.splitKernelIntegral fKerM v s := by
  have hc : Continuous fKerM := (fKerM_contDiff 1).continuous
  have hcongr : (∫ t in (-(1:ℝ)/2)..(1/2), truncKernel (s - t) * v t)
      = ∫ t in (-(1:ℝ)/2)..(1/2), fKerM |s - t| * v t := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    simp only [truncKernel_eq_fKerM]
  rw [hcongr, integral_eq_splitKernel fKerM hc v hv s hs]

end ZetaLean.Pub1
