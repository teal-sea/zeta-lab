/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.LogMeanValue

/-!
# The exact two-range weights at `sigma = 3/2`

This file isolates the finite algebra behind the right-line polynomial in
`URMS2-051`.  It records the common phase, the lower and upper coefficient
weights, and the exact diagonal and endpoint-weighted energies.  No
asymptotic estimate is stated here.
-/

namespace ZetaLean.HigherXi

open Complex Finset

/-! ## Phase algebra -/

/-- The phase left by `(x / n) ^ (it)` before the common `x ^ (it)` factor is
removed. -/
noncomputable def ratioPhase (x : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * Real.log (x / n)))

/-- The common phase, independent of the Dirichlet index. -/
noncomputable def commonXPhase (x t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t * Real.log x))

/-- At positive `x` and positive integer `n`, the ratio phase is a common
unit phase times the logarithmic Fourier atom of `n`.

Thus both contour ranges have frequency `log n` with the same sign after the
common phase is removed.
-/
theorem ratioPhase_eq_common_mul_fourierAtom
    (x : ℝ) (n : ℕ) (t : ℝ) (hx : 0 < x) (hn : 1 ≤ n) :
    ratioPhase x n t = commonXPhase x t * fourierAtom (Real.log n) t := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [ratioPhase, commonXPhase, fourierAtom, ← Complex.exp_add,
    Real.log_div hx.ne' hnpos.ne']
  congr 1
  push_cast
  ring

theorem norm_ratioPhase (x : ℝ) (n : ℕ) (t : ℝ) :
    ‖ratioPhase x n t‖ = 1 := by
  rw [ratioPhase, Complex.norm_exp]
  simp

theorem norm_commonXPhase (x t : ℝ) : ‖commonXPhase x t‖ = 1 := by
  rw [commonXPhase, Complex.norm_exp]
  simp

/-! ## The two coefficient weights -/

/-- The lower-range coefficient weight `sqrt(n) / x`. -/
noncomputable def lowerTwoRangeWeight (x : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt n / x

/-- The upper-range coefficient weight `x / n^(3/2)`, written without a
fractional-power convention as `x / (n * sqrt n)`. -/
noncomputable def upperTwoRangeWeight (x : ℝ) (n : ℕ) : ℝ :=
  x / ((n : ℝ) * Real.sqrt n)

/-- The coefficient weight selected by the contour breakpoint `n <= x`. -/
noncomputable def twoRangeWeight (x : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ x then lowerTwoRangeWeight x n else upperTwoRangeWeight x n

/-- The finite complex coefficient after the common phase is removed. -/
noncomputable def twoRangeCoefficient
    (x : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (twoRangeWeight x n : ℂ) * a n

/-- The finite two-range polynomial before removing the common `x` phase. -/
noncomputable def phasedTwoRangePolynomial
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 W,
    twoRangeCoefficient x a n * ratioPhase x n t

/-- Removing the common unit phase leaves one Dirichlet polynomial whose
frequency at every index, in both ranges, is `log n`.  In particular, the
cross-range terms have phase `log n - log m`, just like the within-range
terms. -/
theorem phasedTwoRangePolynomial_eq_common_mul
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) (t : ℝ) (hx : 0 < x) :
    phasedTwoRangePolynomial x W a t =
      commonXPhase x t * dirichletPolynomial (Finset.Icc 1 W)
        (twoRangeCoefficient x a) (fun n => Real.log n) t := by
  rw [phasedTwoRangePolynomial, dirichletPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_Icc] at hn
  rw [ratioPhase_eq_common_mul_fourierAtom x n t hx hn.1]
  ring

/-- The real exponent calculation on the lower contour range at
`sigma = 3/2`: `x^(-1/2) (x/n)^(-1/2) = sqrt(n)/x`. -/
theorem lower_sigma_three_halves_amplitude
    (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 1 ≤ n) :
    x ^ (-(1 / 2 : ℝ)) * (x / n) ^ (-(1 / 2 : ℝ)) =
      lowerTwoRangeWeight x n := by
  have hx0 : 0 ≤ x := hx.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Real.rpow_neg hx0, Real.div_rpow hx0 hnpos.le, Real.rpow_neg hx0,
    Real.rpow_neg hnpos.le, lowerTwoRangeWeight, Real.sqrt_eq_rpow]
  have hxhalf : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← Real.rpow_add hx]
    norm_num
  field_simp
  ring_nf at hxhalf ⊢
  nlinarith

/-- The real exponent calculation on the upper contour range at
`sigma = 3/2`: `x^(-1/2) (x/n)^(3/2) = x/n^(3/2)`. -/
theorem upper_sigma_three_halves_amplitude
    (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 1 ≤ n) :
    x ^ (-(1 / 2 : ℝ)) * (x / n) ^ (3 / 2 : ℝ) =
      upperTwoRangeWeight x n := by
  have hx0 : 0 ≤ x := hx.le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Real.rpow_neg hx0, Real.div_rpow hx0 hnpos.le]
  have hxsplit : x ^ (3 / 2 : ℝ) = x ^ (1 / 2 : ℝ) * x := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add_one hx.ne']
  have hnsplit : (n : ℝ) ^ (3 / 2 : ℝ) = Real.sqrt n * n := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
      Real.rpow_add_one hnpos.ne', ← Real.sqrt_eq_rpow]
  rw [hxsplit, hnsplit, upperTwoRangeWeight]
  have hxhalf : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp

/-! ## Exact square weights -/

theorem lowerTwoRangeWeight_sq
    (x : ℝ) (n : ℕ) :
    lowerTwoRangeWeight x n ^ 2 = (n : ℝ) / x ^ 2 := by
  rw [lowerTwoRangeWeight, div_pow, Real.sq_sqrt (by positivity)]

theorem upperTwoRangeWeight_sq
    (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    upperTwoRangeWeight x n ^ 2 = x ^ 2 / (n : ℝ) ^ 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [upperTwoRangeWeight, div_pow, mul_pow, Real.sq_sqrt hnpos.le]
  field_simp

theorem norm_twoRangeCoefficient_sq_lower
    (x : ℝ) (a : ℕ → ℂ) (n : ℕ) (hx : x ≠ 0)
    (hnx : (n : ℝ) ≤ x) :
    ‖twoRangeCoefficient x a n‖ ^ 2 =
      x⁻¹ ^ 2 * ‖a n‖ ^ 2 * n := by
  rw [twoRangeCoefficient, twoRangeWeight, if_pos hnx, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    lowerTwoRangeWeight_sq x n]
  field_simp

theorem norm_twoRangeCoefficient_sq_upper
    (x : ℝ) (a : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hnx : x < (n : ℝ)) :
    ‖twoRangeCoefficient x a n‖ ^ 2 =
      x ^ 2 * ‖a n‖ ^ 2 / (n : ℝ) ^ 3 := by
  rw [twoRangeCoefficient, twoRangeWeight, if_neg (not_le.mpr hnx), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    upperTwoRangeWeight_sq x n hn]
  ring

/-! ## Lower and upper finite ranges -/

noncomputable def lowerTwoRangeIndices (x : ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter fun n => (n : ℝ) ≤ x

noncomputable def upperTwoRangeIndices (x : ℝ) (W : ℕ) : Finset ℕ :=
  (Finset.Icc 1 W).filter fun n => x < (n : ℝ)

theorem lower_upper_indices_disjoint (x : ℝ) (W : ℕ) :
    Disjoint (lowerTwoRangeIndices x W) (upperTwoRangeIndices x W) := by
  rw [Finset.disjoint_left]
  intro n hnlow hnupper
  simp only [lowerTwoRangeIndices, upperTwoRangeIndices, Finset.mem_filter,
    Finset.mem_Icc] at hnlow hnupper
  exact (not_lt_of_ge hnlow.2) hnupper.2

theorem lower_union_upper_indices (x : ℝ) (W : ℕ) :
    lowerTwoRangeIndices x W ∪ upperTwoRangeIndices x W = Finset.Icc 1 W := by
  ext n
  simp only [lowerTwoRangeIndices, upperTwoRangeIndices, Finset.mem_union,
    Finset.mem_filter, Finset.mem_Icc]
  constructor
  · aesop
  · intro hn
    rcases le_or_gt (n : ℝ) x with hnx | hnx
    · exact Or.inl ⟨hn, hnx⟩
    · exact Or.inr ⟨hn, hnx⟩

/-- The exact finite diagonal coefficient mass. -/
noncomputable def twoRangeDiagonal
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W, ‖twoRangeCoefficient x a n‖ ^ 2

/-- The diagonal is exactly the lower `n/x^2` Stieltjes weight plus the upper
`x^2/n^3` Stieltjes weight. -/
theorem twoRangeDiagonal_eq
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) (hx : x ≠ 0) :
    twoRangeDiagonal x W a =
      x⁻¹ ^ 2 * (∑ n ∈ lowerTwoRangeIndices x W, ‖a n‖ ^ 2 * n) +
      x ^ 2 * (∑ n ∈ upperTwoRangeIndices x W,
        ‖a n‖ ^ 2 / (n : ℝ) ^ 3) := by
  rw [twoRangeDiagonal, ← lower_union_upper_indices x W,
    Finset.sum_union (lower_upper_indices_disjoint x W)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [lowerTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc] at hn
    simpa [mul_assoc] using norm_twoRangeCoefficient_sq_lower x a n hx hn.2
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [upperTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [norm_twoRangeCoefficient_sq_upper x a n hn.1.1 hn.2]
    ring

/-- The endpoint-weighted energy used by the logarithmic mean-value theorem. -/
noncomputable def twoRangeEndpointEnergy
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 W, (n : ℝ) * ‖twoRangeCoefficient x a n‖ ^ 2

/-- Direct interface to the endpoint energy used by `LogMeanValue`. -/
theorem weightedCoefficientEnergy_norm_twoRangeCoefficient
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) :
    weightedCoefficientEnergy W (fun n => ‖twoRangeCoefficient x a n‖) =
      twoRangeEndpointEnergy x W a := rfl

/-- Exact endpoint-energy decomposition: below `x` its weight is `n^2/x^2`,
while above `x` it is `x^2/n^2`. -/
theorem twoRangeEndpointEnergy_eq
    (x : ℝ) (W : ℕ) (a : ℕ → ℂ) (hx : x ≠ 0) :
    twoRangeEndpointEnergy x W a =
      x⁻¹ ^ 2 * (∑ n ∈ lowerTwoRangeIndices x W,
        ‖a n‖ ^ 2 * (n : ℝ) ^ 2) +
      x ^ 2 * (∑ n ∈ upperTwoRangeIndices x W,
        ‖a n‖ ^ 2 / (n : ℝ) ^ 2) := by
  rw [twoRangeEndpointEnergy, ← lower_union_upper_indices x W,
    Finset.sum_union (lower_upper_indices_disjoint x W)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [lowerTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [norm_twoRangeCoefficient_sq_lower x a n hx hn.2]
    ring
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [upperTwoRangeIndices, Finset.mem_filter, Finset.mem_Icc] at hn
    rw [norm_twoRangeCoefficient_sq_upper x a n hn.1.1 hn.2]
    field_simp

end ZetaLean.HigherXi
