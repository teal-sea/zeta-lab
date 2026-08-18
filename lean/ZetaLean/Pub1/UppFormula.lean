/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.QDiff
import ZetaLean.Pub1.Certificate
import ZetaLean.Pub1.CertBounds
import ZetaLean.Pub1.WRegularity

/-!
# Pub 1 strong closure: the second derivative of the trial polynomial

Differentiating the exact residual identity `u + T₀u + r₀ = 1` twice on the
interior gives

```
      u'' = -r₀'' - 2u - ∫_I q_M(|s-t|) u(t) dt,
```

the truncated counterpart of `w'' = -(2w + q*w)`.  Subtracting the two is what
produces the certificate's `z''` identity.
-/

open Set MeasureTheory Filter Topology

namespace ZetaLean.Pub1

/-- First derivative of `T₀ v`. -/
noncomputable def T0D1 (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ t in (-(1:ℝ)/2)..s, deriv fKerM (s - t) * v t)
    - ∫ t in s..(1/2:ℝ), deriv fKerM (t - s) * v t

/-- Second derivative of `T₀ v`. -/
noncomputable def T0D2 (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * v s + ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv fKerM) |s - t| * v t

theorem hasDerivAt_r0Poly (x : ℝ) : HasDerivAt r0Poly (r0Sum1 x) x := by
  have hfun : r0Poly = r0Sum := funext r0Poly_eq_sum
  rw [hfun]
  exact hasDerivAt_r0Sum x

theorem deriv_r0Poly_eq : deriv r0Poly = r0Sum1 := funext fun x => (hasDerivAt_r0Poly x).deriv

/-- On a neighbourhood of an interior point, `u = 1 - r₀ - T₀ u`. -/
theorem uPoly_eventually_eq {s : ℝ} (hs : s ∈ Iint) :
    ∀ᶠ σ in 𝓝 s, uPoly σ
      = 1 - r0Poly σ - AristotleN.splitKernelIntegral fKerM uPoly σ := by
  filter_upwards [isOpen_Iint.mem_nhds hs] with σ hσ
  have habs : |σ| ≤ 1 / 2 := mem_Iint_abs hσ
  have h := r0_identity σ habs
  rw [← truncKernel_conv_eq_split uPoly continuous_uPoly σ habs]
  linarith [h]

theorem hasDerivAt_uPoly' {s : ℝ} (hs : s ∈ Iint) :
    HasDerivAt uPoly (-r0Sum1 s - T0D1 uPoly s) s := by
  have hT := AristotleN.splitKernelIntegral_hasDerivAt fKerM
    (fKerM_contDiff 2) fKerM_zero uPoly continuous_uPoly s
  have hsub : HasDerivAt
      (fun σ : ℝ => 1 - r0Poly σ - AristotleN.splitKernelIntegral fKerM uPoly σ)
      (-r0Sum1 s - T0D1 uPoly s) s := by
    have h1 : HasDerivAt (fun σ : ℝ => (1 : ℝ) - r0Poly σ) (-r0Sum1 s) s := by
      have := HasDerivAt.fun_sub (hasDerivAt_const s (1:ℝ)) (hasDerivAt_r0Poly s)
      exact this.congr_deriv (by ring)
    exact (HasDerivAt.fun_sub h1 hT).congr_deriv (by unfold T0D1; ring)
  exact hsub.congr_of_eventuallyEq (uPoly_eventually_eq hs)

theorem deriv_uPoly_eq {s : ℝ} (hs : s ∈ Iint) :
    deriv uPoly s = -r0Sum1 s - T0D1 uPoly s := (hasDerivAt_uPoly' hs).deriv

/-- **`u'' = -r₀'' - (2u + q_M * u)` on the interior.** -/
theorem hasDerivAt_deriv_uPoly {s : ℝ} (hs : s ∈ Iint) :
    HasDerivAt (deriv uPoly) (-r0Sum2 s - T0D2 uPoly s) s := by
  have hT2 := truncKernel_second_deriv uPoly continuous_uPoly s (mem_Iint_abs hs)
  have hT2' : HasDerivAt (fun σ : ℝ => T0D1 uPoly σ) (T0D2 uPoly s) s := by
    unfold T0D1 T0D2
    exact hT2
  have hbase : HasDerivAt (fun σ : ℝ => -r0Sum1 σ - T0D1 uPoly σ)
      (-r0Sum2 s - T0D2 uPoly s) s := by
    have h1 : HasDerivAt (fun σ : ℝ => -r0Sum1 σ) (-r0Sum2 s) s :=
      HasDerivAt.fun_neg (hasDerivAt_r0Sum1 s)
    exact HasDerivAt.fun_sub h1 hT2'
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Iint.mem_nhds hs] with σ hσ
  exact deriv_uPoly_eq hσ

theorem deriv_deriv_uPoly {s : ℝ} (hs : s ∈ Iint) :
    deriv (deriv uPoly) s = -r0Sum2 s - T0D2 uPoly s := (hasDerivAt_deriv_uPoly hs).deriv

end ZetaLean.Pub1
