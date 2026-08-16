/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.Convergence
import ZetaLean.Pub1.Regularity
import ZetaLean.Pub1.QBound
import ZetaLean.Pub1.Aristotle.W

/-!
# Pub 1 strong closure: interior `C²` regularity of `w`

`w = 1 - T w` on `I`, and `pub1_kernel_second_deriv` differentiates `T w` twice,
so `w` is twice differentiable on the *open* interval with

```
      w'  = -(T w)',        w'' = -(2 w + q * w).
```

Only the open interval is claimed.  Across `|s| = 1/2` the second derivative
genuinely jumps — inside, the delta mass contributes `2w(s) ≥ 2/5`; outside it
does not — so `C²` there is false and is not asserted.

The two sup bounds come out of the same formula:

* `|w''| ≤ 2‖w‖_∞ + ‖q‖_∞‖w‖₁ ≤ 2 + 80.963`, using `w ≤ 1` and `|I| = 1`;
* `|w'| ≤ B₂/2`, because `w` is even so `w'(0) = 0`, and the mean value
  inequality on `[0,s]` with `|w''| ≤ B₂` gives `|w'(s)| ≤ B₂|s| ≤ B₂/2`.

No bound on `‖fKer'‖_∞` is needed, which avoids a second series estimate.
-/

open Set MeasureTheory Filter Topology

namespace ZetaLean.Pub1

variable {w : ℝ → ℝ}

/-- The interior of `I` as an open set. -/
noncomputable def Iint : Set ℝ := Ioo (-(1/2) : ℝ) (1/2)

theorem isOpen_Iint : IsOpen Iint := isOpen_Ioo

theorem mem_Iint_abs {s : ℝ} (hs : s ∈ Iint) : |s| ≤ 1 / 2 := by
  have h := hs
  rw [Iint, mem_Ioo] at h
  exact le_of_lt (abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩)

/-- The first derivative of `T w`. -/
noncomputable def TD1 (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  (∫ t in (-(1:ℝ)/2)..s, deriv AristotleS.fKer (s - t) * w t)
    - ∫ t in s..(1/2:ℝ), deriv AristotleS.fKer (t - s) * w t

/-- The second derivative of `T w`: the delta term plus the ordinary part. -/
noncomputable def TD2 (w : ℝ → ℝ) (s : ℝ) : ℝ :=
  2 * w s + ∫ t in (-(1:ℝ)/2)..(1/2), deriv (deriv AristotleS.fKer) |s - t| * w t

/-- On a neighbourhood of an interior point, `w = 1 - T w`. -/
theorem w_eventually_eq (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    ∀ᶠ σ in 𝓝 s, w σ = 1 - AristotleN.splitKernelIntegral AristotleS.fKer w σ := by
  filter_upwards [isOpen_Iint.mem_nhds hs] with σ hσ
  have habs : |σ| ≤ 1 / 2 := mem_Iint_abs hσ
  have h := hw.eq_on_I habs
  rw [← F1_conv_eq_split w hw.1 σ habs]
  linarith [h]

/-- `w' = -(T w)'` on the interior. -/
theorem hasDerivAt_w (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    HasDerivAt w (-TD1 w s) s := by
  have hT := AristotleN.splitKernelIntegral_hasDerivAt AristotleS.fKer
    (AristotleS.fKer_contDiff.of_le (by norm_num)) AristotleS.fKer_zero w hw.1 s
  have hsub : HasDerivAt
      (fun σ : ℝ => 1 - AristotleN.splitKernelIntegral AristotleS.fKer w σ)
      (-TD1 w s) s :=
    (HasDerivAt.fun_sub (hasDerivAt_const s (1:ℝ)) hT).congr_deriv (by unfold TD1; ring)
  exact hsub.congr_of_eventuallyEq (w_eventually_eq hw hs)

theorem deriv_w_eq (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    deriv w s = -TD1 w s := (hasDerivAt_w hw hs).deriv

/-- `-(T w)'` is differentiable with derivative `-(2w + q*w)`. -/
theorem hasDerivAt_negTD1 (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    HasDerivAt (fun σ : ℝ => -TD1 w σ) (-TD2 w s) s := by
  have hT2 := pub1_kernel_second_deriv w hw.1 s (mem_Iint_abs hs)
  have hT2' : HasDerivAt (fun σ : ℝ => TD1 w σ) (TD2 w s) s := by
    unfold TD1 TD2
    exact hT2
  exact HasDerivAt.fun_neg hT2'

/-- `w'' = -(2w + q * w)` on the interior. -/
theorem hasDerivAt_deriv_w (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    HasDerivAt (deriv w) (-TD2 w s) s := by
  refine (hasDerivAt_negTD1 hw hs).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Iint.mem_nhds hs] with σ hσ
  exact deriv_w_eq hw hσ

/-- **Interior `C²` regularity of `w`.** -/
theorem w_contDiffOn (hw : IsProfile w) : ContDiffOn ℝ 2 w Iint := by
  refine AristotleW.contDiffOn_two_of_hasDerivAt w (fun s => -TD1 w s) (fun s => -TD2 w s)
    _ _ (fun s hs => hasDerivAt_w hw hs) (fun s hs => hasDerivAt_negTD1 hw hs) ?_
  refine ContinuousOn.neg ?_
  refine Continuous.continuousOn ?_
  unfold TD2
  refine (continuous_const.mul hw.1).add ?_
  have hcont : Continuous (Function.uncurry
      fun s t : ℝ => deriv (deriv AristotleS.fKer) |s - t| * w t) := by
    have h1 : Continuous fun p : ℝ × ℝ => deriv (deriv AristotleS.fKer) |p.1 - p.2| :=
      fKer_second_deriv_continuous.comp ((continuous_fst.sub continuous_snd).abs)
    exact h1.mul (hw.1.comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcont _ _

/-! ### The two sup bounds -/

/-- `B₂ = 2 + ‖q‖_∞`, the exact bound on `|w''|`. -/
noncomputable def wB2 : ℝ :=
  2 + (8 + (23335671895968028334772392 / 319830986772877770815625
    + 666953056256 / 23065890935073171953452059375))

theorem wB2_pos : 0 < wB2 := by unfold wB2; norm_num

/-- **`|w''| ≤ B₂` on the interior**, from `w'' = -(2w + q*w)`, `w ≤ 1` and
`‖q‖_∞ ≤ 80.963`. -/
theorem w_second_deriv_bound (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    |deriv (deriv w) s| ≤ wB2 := by
  have hd : deriv (deriv w) s = -TD2 w s := (hasDerivAt_deriv_w hw hs).deriv
  have hsabs := abs_le.mp (mem_Iint_abs hs)
  rw [hd, abs_neg, TD2]
  set Q : ℝ := 8 + (23335671895968028334772392 / 319830986772877770815625
      + 666953056256 / 23065890935073171953452059375) with hQdef
  set g : ℝ → ℝ := fun t => deriv (deriv AristotleS.fKer) (|s - t|) * w t with hgdef
  have hgbound : ∀ t ∈ Set.uIoc (-(1:ℝ)/2) ((1:ℝ)/2), ‖g t‖ ≤ Q := by
    intro t ht
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have htabs := abs_le.mp (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩ :
      |t| ≤ (1:ℝ)/2)
    have harg : |(|s - t|)| ≤ 1 := by
      rw [abs_abs, abs_le]
      constructor <;> linarith [hsabs.1, hsabs.2, htabs.1, htabs.2]
    have hq := q_abs_le harg
    have hw1 : |w t| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [(profile_bounds hw).1 t], (profile_bounds hw).2 t⟩
    have hnn : (0:ℝ) ≤ |deriv (deriv AristotleS.fKer) (|s - t|)| := abs_nonneg _
    have hnorm : ‖g t‖ = |deriv (deriv AristotleS.fKer) (|s - t|)| * |w t| := by
      simp only [hgdef, Real.norm_eq_abs]
      exact abs_mul _ _
    have hstep := mul_le_mul_of_nonneg_left hw1 hnn
    rw [mul_one] at hstep
    rw [hnorm, hQdef]
    linarith [hstep, hq]
  have hint : ‖∫ t in (-(1:ℝ)/2)..((1:ℝ)/2), g t‖ ≤ Q * |(1:ℝ)/2 - (-(1:ℝ)/2)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hgbound
  have hws : |w s| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [(profile_bounds hw).1 s], (profile_bounds hw).2 s⟩
  have hlen : |(1:ℝ)/2 - (-(1:ℝ)/2)| = 1 := by norm_num
  rw [hlen, mul_one, Real.norm_eq_abs] at hint
  have hintle := abs_le.mp hint
  have hwsle := abs_le.mp hws
  rw [abs_le]
  unfold wB2
  simp only [← hQdef]
  constructor <;> linarith [hintle.1, hintle.2, hwsle.1, hwsle.2]

/-- `w'(0) = 0`, from evenness and differentiability at the origin. -/
theorem deriv_w_zero (hw : IsProfile w) : deriv w 0 = 0 := by
  have h0 : (0:ℝ) ∈ Iint := by rw [Iint]; constructor <;> norm_num
  have h1 : HasDerivAt w (deriv w 0) 0 := by
    have := hasDerivAt_w hw h0
    rwa [← (hasDerivAt_w hw h0).deriv] at this
  have hneg : HasDerivAt (fun σ : ℝ => -σ) (-1 : ℝ) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hzero : ((fun σ : ℝ => -σ) 0) = (0 : ℝ) := by norm_num
  have h1' : HasDerivAt w (deriv w 0) ((fun σ : ℝ => -σ) 0) := by rw [hzero]; exact h1
  have h2 : HasDerivAt (w ∘ (fun σ : ℝ => -σ)) (deriv w 0 * (-1)) 0 :=
    HasDerivAt.comp (0 : ℝ) h1' hneg
  have hfun : (w ∘ (fun σ : ℝ => -σ)) = w := funext (profile_even hw)
  rw [hfun] at h2
  have := h1.unique h2
  linarith

/-- **`|w'| ≤ B₂/2` on the interior.**  `w` is even so `w'(0) = 0`, and the mean
value inequality with `|w''| ≤ B₂` on the convex interior gives the bound. -/
theorem w_deriv_bound (hw : IsProfile w) {s : ℝ} (hs : s ∈ Iint) :
    |deriv w s| ≤ wB2 / 2 := by
  have h0 : (0:ℝ) ∈ Iint := by rw [Iint]; constructor <;> norm_num
  have hconv : Convex ℝ Iint := by rw [Iint]; exact convex_Ioo _ _
  have hderiv : ∀ x ∈ Iint, HasDerivWithinAt (deriv w) (-TD2 w x) Iint x :=
    fun x hx => (hasDerivAt_deriv_w hw hx).hasDerivWithinAt
  have hbound : ∀ x ∈ Iint, ‖-TD2 w x‖ ≤ wB2 := by
    intro x hx
    have h := w_second_deriv_bound hw hx
    rw [(hasDerivAt_deriv_w hw hx).deriv] at h
    rwa [Real.norm_eq_abs]
  have hmvt := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound h0 hs
  rw [deriv_w_zero hw] at hmvt
  have hsabs : |s| ≤ 1 / 2 := mem_Iint_abs hs
  simp only [Real.norm_eq_abs, sub_zero] at hmvt
  calc |deriv w s| ≤ wB2 * |s| := hmvt
    _ ≤ wB2 * (1/2) := by
        exact mul_le_mul_of_nonneg_left hsabs wB2_pos.le
    _ = wB2 / 2 := by ring

end ZetaLean.Pub1
