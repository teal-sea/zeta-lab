/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.UppFormula
import ZetaLean.Pub1.ZBounds

/-!
# Pub 1 strong closure: `‖w'' - u''‖_∞ < 0.006060899845`

Subtracting the two second-derivative formulas,

```
      w'' = -(2w + q  * w)
      u'' = -r₀'' - (2u + q_M * u)
```

gives exactly the certificate's identity

```
      z'' = r₀'' - 2z - q*z - (q - q_M)*u,        z = w - u,
```

and the four terms are bounded by the constants of `CertArith`.
-/

open Set MeasureTheory

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

private theorem cont_q_mul (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    Continuous fun t : ℝ => deriv (deriv AristotleS.fKer) |s - t| * v t :=
  (fKer_second_deriv_continuous.comp ((continuous_const.sub continuous_id).abs)).mul hv

private theorem cont_qM_mul (v : ℝ → ℝ) (hv : Continuous v) (s : ℝ) :
    Continuous fun t : ℝ => deriv (deriv fKerM) |s - t| * v t :=
  (fKerM_second_deriv_continuous.comp ((continuous_const.sub continuous_id).abs)).mul hv

/-- The convolution difference splits into `q*z` and `(q - q_M)*u`. -/
theorem conv_split (hw : IsProfile w) (s : ℝ) :
    (∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * w t)
        - ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv fKerM) |s - t| * uPoly t
      = (∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * zFun w t)
        + ∫ t in (-(1:ℝ)/2)..(1/2),
            (deriv (deriv AristotleS.fKer) |s - t| - deriv (deriv fKerM) |s - t|) * uPoly t := by
  have hu := continuous_uPoly
  have hzc := continuous_zFun hw
  have hiA : IntervalIntegrable
      (fun t : ℝ => deriv (deriv AristotleS.fKer) |s - t| * zFun w t) volume
      (-(1:ℝ)/2) ((1:ℝ)/2) := (cont_q_mul (zFun w) hzc s).intervalIntegrable _ _
  have hiB : IntervalIntegrable
      (fun t : ℝ =>
        (deriv (deriv AristotleS.fKer) |s - t| - deriv (deriv fKerM) |s - t|) * uPoly t)
      volume (-(1:ℝ)/2) ((1:ℝ)/2) := by
    apply Continuous.intervalIntegrable
    exact (((fKer_second_deriv_continuous.comp ((continuous_const.sub continuous_id).abs)).sub
      (fKerM_second_deriv_continuous.comp
        ((continuous_const.sub continuous_id).abs)))).mul hu
  have hiC : IntervalIntegrable
      (fun t : ℝ => deriv (deriv AristotleS.fKer) |s - t| * w t) volume
      (-(1:ℝ)/2) ((1:ℝ)/2) := (cont_q_mul w hw.1 s).intervalIntegrable _ _
  have hiD : IntervalIntegrable
      (fun t : ℝ => deriv (deriv fKerM) |s - t| * uPoly t) volume
      (-(1:ℝ)/2) ((1:ℝ)/2) := (cont_qM_mul uPoly hu s).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add hiA hiB, ← intervalIntegral.integral_sub hiC hiD]
  exact intervalIntegral.integral_congr (fun t _ => by simp only [zFun]; ring)

/-- **The certificate identity for `z''`.** -/
theorem zpp_identity (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    deriv (deriv w) s - deriv (deriv uPoly) s
      = r0Sum2 s - 2 * zFun w s
        - (∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * zFun w t)
        - ∫ t in (-(1:ℝ)/2)..(1/2),
            (deriv (deriv AristotleS.fKer) |s - t| - deriv (deriv fKerM) |s - t|) * uPoly t := by
  rw [(hasDerivAt_deriv_w hw hs).deriv, deriv_deriv_uPoly hs, TD2, T0D2]
  have h := conv_split hw s
  simp only [zFun] at h ⊢
  linarith [h]

/-- Bound on the `q * z` term. -/
theorem qz_bound (hw : IsProfile w) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * zFun w t|
      ≤ ((qabsC : ℚ) : ℝ) * ((zl2C : ℚ) : ℝ) := by
  have hsabs := abs_le.mp hs
  have hzc := continuous_zFun hw
  have hQ : ((qabsC : ℚ) : ℝ)
      = 8 + (23335671895968028334772392 / 319830986772877770815625
        + 666953056256 / 23065890935073171953452059375) := by norm_num [qabsC]
  have hstep : |∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * zFun w t|
      ≤ ((qabsC : ℚ) : ℝ) * ∫ t in (-(1:ℝ)/2)..(1/2), |zFun w t| := by
    have h1 : |∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * zFun w t|
        ≤ ∫ t in (-(1:ℝ)/2)..(1/2), |deriv (deriv AristotleS.fKer) |s - t| * zFun w t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    have h2 : (∫ t in (-(1:ℝ)/2)..(1/2), |deriv (deriv AristotleS.fKer) |s - t| * zFun w t|)
        ≤ ∫ t in (-(1:ℝ)/2)..(1/2), ((qabsC : ℚ) : ℝ) * |zFun w t| := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((cont_q_mul (zFun w) hzc s).abs.intervalIntegrable _ _)
        ((continuous_const.mul hzc.abs).intervalIntegrable _ _) ?_
      intro t ht
      have htabs : |t| ≤ (1:ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have htabs' := abs_le.mp htabs
      have harg : |(|s - t|)| ≤ 1 := by
        rw [abs_abs, abs_le]
        constructor <;> linarith [hsabs.1, hsabs.2, htabs'.1, htabs'.2]
      have hq := q_abs_le harg
      rw [abs_mul, hQ]
      have hnn := abs_nonneg (zFun w t)
      nlinarith [hq, hnn, abs_nonneg (deriv (deriv AristotleS.fKer) (|s - t|))]
    rw [intervalIntegral.integral_const_mul] at h2
    linarith [h1, h2]
  have hl1 := integral_abs_zFun_le hw
  have hl2 := zFun_l2 hw
  have hqnn : (0:ℝ) ≤ ((qabsC : ℚ) : ℝ) := by norm_num [qabsC]
  nlinarith [hstep, hl1, hl2, hqnn]

/-- Bound on the `(q - q_M) * u` term. -/
theorem qdiff_u_bound {s : ℝ} (hs : |s| ≤ 1 / 2) :
    |∫ t in (-(1:ℝ)/2)..(1/2),
        (deriv (deriv AristotleS.fKer) |s - t| - deriv (deriv fKerM) |s - t|) * uPoly t|
      ≤ ((stC : ℚ) : ℝ) * ((usupC : ℚ) : ℝ) := by
  have hsabs := abs_le.mp hs
  have hbound : ∀ t ∈ Set.uIoc (-(1:ℝ)/2) ((1:ℝ)/2),
      ‖(deriv (deriv AristotleS.fKer) |s - t| - deriv (deriv fKerM) |s - t|) * uPoly t‖
        ≤ ((stC : ℚ) : ℝ) * ((usupC : ℚ) : ℝ) := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htabs : |t| ≤ (1:ℝ)/2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htabs' := abs_le.mp htabs
    have harg : |(|s - t|)| ≤ 1 := by
      rw [abs_abs, abs_le]
      constructor <;> linarith [hsabs.1, hsabs.2, htabs'.1, htabs'.2]
    have h1 := q_sub_qM_abs_le harg
    have h2 := uPoly_abs_le htabs
    have hst : ((stC : ℚ) : ℝ) = 666953056256 / 23065890935073171953452059375 := by
      norm_num [stC]
    rw [Real.norm_eq_abs, abs_mul, hst]
    have hnn1 := abs_nonneg (deriv (deriv AristotleS.fKer) (|s - t|)
      - deriv (deriv fKerM) (|s - t|))
    have hnn2 := abs_nonneg (uPoly t)
    have husup : (0:ℝ) ≤ ((usupC : ℚ) : ℝ) := by norm_num [usupC]
    nlinarith [h1, h2, hnn1, hnn2, husup]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [show |(1:ℝ)/2 - (-(1:ℝ)/2)| = 1 by norm_num, mul_one, Real.norm_eq_abs] at h
  exact h

/-- **The certificate bound.**  `‖w'' - u''‖_∞ < 0.006060899845` on the interior. -/
theorem zpp_bound (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    |deriv (deriv w) s - deriv (deriv uPoly) s| < 6060899845 / 10 ^ 12 := by
  have hsabs : |s| ≤ 1 / 2 := mem_Iint_abs hs
  rw [zpp_identity hw hs]
  have h1 : |r0Sum2 s| ≤ ((r2C : ℚ) : ℝ) := by
    refine le_trans (r0Sum2_abs_le s hsabs) ?_
    norm_num [r2C]
  have h2 : |zFun w s| ≤ ((zinfC : ℚ) : ℝ) := zFun_linf hw hsabs
  have h3 := qz_bound hw hsabs
  have h4 := qdiff_u_bound hsabs
  have hR : ((r2C : ℚ) : ℝ) + ((stC : ℚ) : ℝ) * ((usupC : ℚ) : ℝ)
      + 2 * ((zinfC : ℚ) : ℝ) + ((qabsC : ℚ) : ℝ) * ((zl2C : ℚ) : ℝ)
      < 6060899845 / 10 ^ 12 := by
    have h := zpp_arith_final
    have hc : ((r2C + stC * usupC + 2 * zinfC + qabsC * zl2C : ℚ) : ℝ)
        < ((6060899845 / 10 ^ 12 : ℚ) : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith [hc]
  rw [abs_le] at h1 h2
  rw [abs_le] at h3 h4
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, hR]

end ZetaLean.Pub1
