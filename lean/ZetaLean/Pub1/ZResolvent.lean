/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Certificate
import ZetaLean.Pub1.WRegularity

/-!
# Pub 1 strong closure: the resolvent equation for `z = w - u`

Subtracting the two equations already proved,

```
      w + T w  = 1                      (IsProfile.eq_on_I)
      u + T₀ u = 1 - r₀                 (r0_identity)
```

gives `z + T z = r₀ - E u` with `z = w - u` and `E = T - T₀` the tail operator.
That is the equation the resolvent estimates are applied to.  Pure algebra: no
new analysis, only linearity of the integral.
-/

open MeasureTheory

namespace ZetaLean.Pub1

/-- The tail operator `E = T - T₀` applied to the trial polynomial. -/
noncomputable def EuTail (s : ℝ) : ℝ :=
  ∫ t in (-(1:ℝ)/2)..(1/2), (F1 (s - t) - truncKernel (s - t)) * uPoly t

private theorem cont_F1_mul (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    Continuous fun t : ℝ => F1 (s - t) * v t :=
  ((F1_continuous.comp (continuous_const.sub continuous_id))).mul hv

private theorem cont_trunc_mul (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    Continuous fun t : ℝ => truncKernel (s - t) * v t := by
  have hK : Continuous truncKernel := by
    unfold truncKernel
    refine (by fun_prop : Continuous fun x : ℝ => (-4 : ℝ) * x ^ 2).add ?_
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (continuous_abs.pow _))
  exact (hK.comp (continuous_const.sub continuous_id)).mul hv

/-- **The resolvent equation for `z = w - u`.**  `z + T z = r₀ - E u` on `I`. -/
theorem z_resolvent_eq {w : ℝ → ℝ} (hw : IsProfile w) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    (w s - uPoly s)
        + (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (w t - uPoly t))
      = r0Poly s - EuTail s := by
  have hwc : Continuous w := hw.1
  have huc : Continuous uPoly := continuous_uPoly
  have hw_eq := hw.eq_on_I hs
  have hu_eq := r0_identity s hs
  -- split the `z` integral
  have hsplit : (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * (w t - uPoly t))
      = (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * w t)
        - ∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * uPoly t := by
    rw [← intervalIntegral.integral_sub
      ((cont_F1_mul w hwc s).intervalIntegrable (μ := volume) _ _)
      ((cont_F1_mul uPoly huc s).intervalIntegrable (μ := volume) _ _)]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  -- the tail operator is the difference of the two kernels
  have htail : EuTail s
      = (∫ t in (-(1:ℝ)/2)..(1/2), F1 (s - t) * uPoly t)
        - ∫ t in (-(1:ℝ)/2)..(1/2), truncKernel (s - t) * uPoly t := by
    rw [EuTail, ← intervalIntegral.integral_sub
      ((cont_F1_mul uPoly huc s).intervalIntegrable (μ := volume) _ _)
      ((cont_trunc_mul uPoly huc s).intervalIntegrable (μ := volume) _ _)]
    exact intervalIntegral.integral_congr (fun t _ => by ring)
  rw [hsplit, htail]
  linarith [hw_eq, hu_eq]

end ZetaLean.Pub1
