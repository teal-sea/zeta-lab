/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.CertDefs
import ZetaLean.Pub1.CertAtoms

/-!
# Pub 1 strong closure: the exact residual identity

The load-bearing computation of `hunts/wide_search/admissible_closure.py`:

```
      A₀u = u + T_{F₁^(M)} u,      r₀ = 1 - A₀u
```

with `M = 20`.  `r0_identity` proves that the transcribed degree-52 polynomial
`r0Poly` really is `1 - A₀u`, by reducing the convolution to the 132 atomic
integrals of `CertAtoms` and closing the resulting exact rational polynomial
identity with `ring`.  Nothing is approximated and no decimal is trusted.
-/

open Finset MeasureTheory

set_option maxRecDepth 100000

namespace ZetaLean.Pub1

private theorem cont_term (m n : ℕ) (x : ℝ) :
    Continuous fun t : ℝ => |x - t| ^ m * t ^ n :=
  (((continuous_const.sub continuous_id).abs).pow m).mul (continuous_pow n)

theorem continuous_uPoly : Continuous uPoly := by
  unfold uPoly
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_pow _))

private theorem cont_uterm (m : ℕ) (x : ℝ) :
    Continuous fun t : ℝ => |x - t| ^ m * uPoly t :=
  (((continuous_const.sub continuous_id).abs).pow m).mul continuous_uPoly

/-- The convolution of one kernel power against `u`, as a combination of atoms. -/
theorem atomInt_uPoly (m : ℕ) (x : ℝ) :
    (∫ t in (-(1:ℝ)/2)..(1/2), |x - t| ^ m * uPoly t)
      = ∑ j ∈ range 6, cK j * atomInt m (2 * j) x := by
  have hcongr : Set.EqOn (fun t : ℝ => |x - t| ^ m * uPoly t)
      (fun t : ℝ => ∑ j ∈ range 6, cK j * (|x - t| ^ m * t ^ (2 * j)))
      (Set.uIcc (-(1:ℝ)/2) (1/2)) := by
    intro t _
    simp only [uPoly, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hint : ∀ j ∈ range 6,
      IntervalIntegrable (fun t : ℝ => cK j * (|x - t| ^ m * t ^ (2 * j)))
        volume (-(1:ℝ)/2) (1/2) := by
    intro j _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (cont_term m (2 * j) x)
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finsetSum hint]
  exact Finset.sum_congr rfl (fun j _ => by
    rw [intervalIntegral.integral_const_mul]; rfl)

/-- The truncated kernel convolved against `u`, split into its `22` powers. -/
theorem truncKernel_conv (x : ℝ) :
    (∫ t in (-(1:ℝ)/2)..(1/2), truncKernel (x - t) * uPoly t)
      = -4 * (∫ t in (-(1:ℝ)/2)..(1/2), |x - t| ^ 2 * uPoly t)
        + ∑ k ∈ range 21, aK k * ∫ t in (-(1:ℝ)/2)..(1/2), |x - t| ^ (2 * k + 1) * uPoly t := by
  have hcongr : Set.EqOn (fun t : ℝ => truncKernel (x - t) * uPoly t)
      (fun t : ℝ => (-4 : ℝ) * (|x - t| ^ 2 * uPoly t)
        + ∑ k ∈ range 21, aK k * (|x - t| ^ (2 * k + 1) * uPoly t))
      (Set.uIcc (-(1:ℝ)/2) (1/2)) := by
    intro t _
    simp only [truncKernel, add_mul, Finset.sum_mul]
    congr 1
    · rw [sq_abs]; ring
    · exact Finset.sum_congr rfl (fun k _ => by ring)
  have hi1 : IntervalIntegrable (fun t : ℝ => (-4 : ℝ) * (|x - t| ^ 2 * uPoly t))
      volume (-(1:ℝ)/2) (1/2) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (cont_uterm 2 x)
  have hi2 : IntervalIntegrable
      (fun t : ℝ => ∑ k ∈ range 21, aK k * (|x - t| ^ (2 * k + 1) * uPoly t))
      volume (-(1:ℝ)/2) (1/2) := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (cont_uterm (2 * k + 1) x))
  have hi3 : ∀ k ∈ range 21,
      IntervalIntegrable (fun t : ℝ => aK k * (|x - t| ^ (2 * k + 1) * uPoly t))
        volume (-(1:ℝ)/2) (1/2) := by
    intro k _
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (cont_uterm (2 * k + 1) x)
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum hi3]
  exact congrArg _ (Finset.sum_congr rfl (fun k _ => by
    rw [intervalIntegral.integral_const_mul]))

set_option maxHeartbeats 4000000 in
/-- **The exact residual identity.**  `A₀u + r₀ = 1` on `I`, with `r₀` the
transcribed degree-52 rational polynomial.  This is the computation that
`admissible_closure.py` performs in `fractions.Fraction`, done here in the
Lean kernel. -/
theorem r0_identity (x : ℝ) (hx : |x| ≤ 1/2) :
    uPoly x + (∫ t in (-(1:ℝ)/2)..(1/2), truncKernel (x - t) * uPoly t) + r0Poly x = 1 := by
  rw [truncKernel_conv]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, atomInt_uPoly]
  norm_num only
  simp only [atom_2_0 x hx,
    atom_2_2 x hx,
    atom_2_4 x hx,
    atom_2_6 x hx,
    atom_2_8 x hx,
    atom_2_10 x hx,
    atom_1_0 x hx,
    atom_1_2 x hx,
    atom_1_4 x hx,
    atom_1_6 x hx,
    atom_1_8 x hx,
    atom_1_10 x hx,
    atom_3_0 x hx,
    atom_3_2 x hx,
    atom_3_4 x hx,
    atom_3_6 x hx,
    atom_3_8 x hx,
    atom_3_10 x hx,
    atom_5_0 x hx,
    atom_5_2 x hx,
    atom_5_4 x hx,
    atom_5_6 x hx,
    atom_5_8 x hx,
    atom_5_10 x hx,
    atom_7_0 x hx,
    atom_7_2 x hx,
    atom_7_4 x hx,
    atom_7_6 x hx,
    atom_7_8 x hx,
    atom_7_10 x hx,
    atom_9_0 x hx,
    atom_9_2 x hx,
    atom_9_4 x hx,
    atom_9_6 x hx,
    atom_9_8 x hx,
    atom_9_10 x hx,
    atom_11_0 x hx,
    atom_11_2 x hx,
    atom_11_4 x hx,
    atom_11_6 x hx,
    atom_11_8 x hx,
    atom_11_10 x hx,
    atom_13_0 x hx,
    atom_13_2 x hx,
    atom_13_4 x hx,
    atom_13_6 x hx,
    atom_13_8 x hx,
    atom_13_10 x hx,
    atom_15_0 x hx,
    atom_15_2 x hx,
    atom_15_4 x hx,
    atom_15_6 x hx,
    atom_15_8 x hx,
    atom_15_10 x hx,
    atom_17_0 x hx,
    atom_17_2 x hx,
    atom_17_4 x hx,
    atom_17_6 x hx,
    atom_17_8 x hx,
    atom_17_10 x hx,
    atom_19_0 x hx,
    atom_19_2 x hx,
    atom_19_4 x hx,
    atom_19_6 x hx,
    atom_19_8 x hx,
    atom_19_10 x hx,
    atom_21_0 x hx,
    atom_21_2 x hx,
    atom_21_4 x hx,
    atom_21_6 x hx,
    atom_21_8 x hx,
    atom_21_10 x hx,
    atom_23_0 x hx,
    atom_23_2 x hx,
    atom_23_4 x hx,
    atom_23_6 x hx,
    atom_23_8 x hx,
    atom_23_10 x hx,
    atom_25_0 x hx,
    atom_25_2 x hx,
    atom_25_4 x hx,
    atom_25_6 x hx,
    atom_25_8 x hx,
    atom_25_10 x hx,
    atom_27_0 x hx,
    atom_27_2 x hx,
    atom_27_4 x hx,
    atom_27_6 x hx,
    atom_27_8 x hx,
    atom_27_10 x hx,
    atom_29_0 x hx,
    atom_29_2 x hx,
    atom_29_4 x hx,
    atom_29_6 x hx,
    atom_29_8 x hx,
    atom_29_10 x hx,
    atom_31_0 x hx,
    atom_31_2 x hx,
    atom_31_4 x hx,
    atom_31_6 x hx,
    atom_31_8 x hx,
    atom_31_10 x hx,
    atom_33_0 x hx,
    atom_33_2 x hx,
    atom_33_4 x hx,
    atom_33_6 x hx,
    atom_33_8 x hx,
    atom_33_10 x hx,
    atom_35_0 x hx,
    atom_35_2 x hx,
    atom_35_4 x hx,
    atom_35_6 x hx,
    atom_35_8 x hx,
    atom_35_10 x hx,
    atom_37_0 x hx,
    atom_37_2 x hx,
    atom_37_4 x hx,
    atom_37_6 x hx,
    atom_37_8 x hx,
    atom_37_10 x hx,
    atom_39_0 x hx,
    atom_39_2 x hx,
    atom_39_4 x hx,
    atom_39_6 x hx,
    atom_39_8 x hx,
    atom_39_10 x hx,
    atom_41_0 x hx,
    atom_41_2 x hx,
    atom_41_4 x hx,
    atom_41_6 x hx,
    atom_41_8 x hx,
    atom_41_10 x hx]
  simp only [uPoly, r0Poly, cK, aK, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring

end ZetaLean.Pub1
