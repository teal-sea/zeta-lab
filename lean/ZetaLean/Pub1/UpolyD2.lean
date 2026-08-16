/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib
import ZetaLean.Pub1.CertDefs
import ZetaLean.Pub1.CertBounds
import ZetaLean.Pub1.Numeric

/-!
# Pub 1 strong closure: the trial polynomial's second derivative

`u'' (s) = 2c₁ + ∑_{j≥2} c_j (2j)(2j-1) s^(2j-2)`, and every `c_j` with `j ≥ 1`
is negative, so on the whole interval `u'' ≤ 2c₁ = -410178/684401`.  This is the
`u`-side half of strict concavity; the `z`-side half is `zpp_bound`.
-/

open Finset

namespace ZetaLean.Pub1

noncomputable def uCoeff : ℕ → ℝ
  | 0 => (427163/446844)
  | 2 => (-(205089/684401))
  | 4 => (-(2976898/824779))
  | 6 => (-(13369/15690))
  | 8 => (-(104561/672519))
  | 10 => (-(32375/630751))
  | _ => 0

noncomputable def uCoeff1 : ℕ → ℝ
  | 1 => (-(410178/684401))
  | 3 => (-(11907592/824779))
  | 5 => (-(13369/2615))
  | 7 => (-(836488/672519))
  | 9 => (-(323750/630751))
  | _ => 0

noncomputable def uCoeff2 : ℕ → ℝ
  | 0 => (-(410178/684401))
  | 2 => (-(35722776/824779))
  | 4 => (-(13369/523))
  | 6 => (-(5855416/672519))
  | 8 => (-(2913750/630751))
  | _ => 0

noncomputable def uSum (x : ℝ) : ℝ := ∑ d ∈ range 11, uCoeff d * x ^ d
noncomputable def uSum1 (x : ℝ) : ℝ := ∑ d ∈ range 10, uCoeff1 d * x ^ d
noncomputable def uSum2 (x : ℝ) : ℝ := ∑ d ∈ range 9, uCoeff2 d * x ^ d

theorem uPoly_eq_sum (x : ℝ) : uPoly x = uSum x := by
  simp only [uPoly, uSum, uCoeff, cK, Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem hasDerivAt_uSum (x : ℝ) : HasDerivAt uSum (uSum1 x) x := by
  have h := hasDerivAt_sumPow uCoeff 10 x
  refine h.congr_deriv ?_
  simp only [uSum1, uCoeff, uCoeff1, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem hasDerivAt_uSum1 (x : ℝ) : HasDerivAt uSum1 (uSum2 x) x := by
  have h := hasDerivAt_sumPow uCoeff1 9 x
  refine h.congr_deriv ?_
  simp only [uSum2, uCoeff1, uCoeff2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

theorem hasDerivAt_uPoly_sum (x : ℝ) : HasDerivAt uPoly (uSum1 x) x := by
  have hfun : uPoly = uSum := funext uPoly_eq_sum
  rw [hfun]; exact hasDerivAt_uSum x

theorem deriv_uPoly_sum : deriv uPoly = uSum1 := funext fun x => (hasDerivAt_uPoly_sum x).deriv

theorem deriv_deriv_uPoly_sum (x : ℝ) : deriv (deriv uPoly) x = uSum2 x := by
  rw [deriv_uPoly_sum]; exact (hasDerivAt_uSum1 x).deriv

/-- **`u'' ≤ 2c₁` on the interval**: every nonconstant coefficient of `u` is
negative, so every term past the first only subtracts. -/
theorem uSum2_le (x : ℝ) : uSum2 x ≤ ((uSecondDerivBound : ℚ) : ℝ) := by
  have h2 : (0:ℝ) ≤ x ^ 2 := by positivity
  have h4 : (0:ℝ) ≤ x ^ 4 := by positivity
  have h6 : (0:ℝ) ≤ x ^ 6 := by positivity
  have h8 : (0:ℝ) ≤ x ^ 8 := by positivity
  simp only [uSum2, uCoeff2, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [uSecondDerivBound, c1]
  nlinarith [h2, h4, h6, h8]

end ZetaLean.Pub1
