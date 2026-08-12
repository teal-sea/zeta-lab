/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# Kernel-checked algebra for the `URMS2-051` witness

This file formalizes the closed algebraic obligations in
`hunts/higher_xi/URMS2-051.md`:

* the rational parameter witness at bandwidth `51/100` and all of its strict
  margins;
* the logarithmic nearest-neighbour spacing bound used for frequencies
  `log n`;
* the integer multiplicity inequality behind the simple-zero lower bound;
* positivity of the exact rational downstream output.

It deliberately does **not** state `URMS2-051`.  The analytic Montgomery--
Vaughan mean-value estimate, RAMS2 cluster asymptotic, height-freezing estimate,
and contour transfer are not yet formalized in this project.  Keeping those
inputs out of the statement prevents the kernel-checked arithmetic below from
being mistaken for the analytic theorem.
-/

namespace ZetaLean.HigherXi

/-! ## The exact bandwidth witness -/

def alpha : ℚ := 51 / 100
def delta : ℚ := 3 / 4
def gamma : ℚ := 21 / 20
def epsilon : ℚ := 1 / 100

theorem old_half_band_deficit : 2 * alpha - 1 = 1 / 50 := by
  norm_num [alpha]

theorem meanValueMargin : delta - alpha = 6 / 25 := by
  norm_num [delta, alpha]

theorem meanValueMargin_pos : 0 < delta - alpha := by
  norm_num [delta, alpha]

theorem farTailMargin : gamma * (1 - 2 * epsilon) - 2 * alpha = 9 / 1000 := by
  norm_num [gamma, epsilon, alpha]

theorem farTailMargin_pos : 0 < gamma * (1 - 2 * epsilon) - 2 * alpha := by
  norm_num [gamma, epsilon, alpha]

theorem initialIntervalMargin : 1 - delta = 1 / 4 := by
  norm_num [delta]

theorem initialIntervalMargin_pos : 0 < 1 - delta := by
  norm_num [delta]

theorem centralSegmentMargin : 1 - alpha * (1 / 2 + epsilon) = 7399 / 10000 := by
  norm_num [alpha, epsilon]

theorem centralSegmentMargin_pos : 0 < 1 - alpha * (1 / 2 + epsilon) := by
  norm_num [alpha, epsilon]

theorem targetRatioOnLowestBlock : 2 * alpha / delta = 34 / 25 := by
  norm_num [alpha, delta]

theorem cutoffRatioOnLowestBlock : 2 * gamma / delta = 14 / 5 := by
  norm_num [gamma, delta]

/-! ## Exact logarithmic frequency spacing -/

/-- Consecutive logarithmic frequencies have gap at least `1/(n+1)`.

This is the arithmetic specialization used after the weighted
Montgomery--Vaughan inequality.  It is independent of that analytic theorem.
-/
theorem one_div_succ_le_log_succ_sub_log (n : ℕ) (hn : 1 ≤ n) :
    (1 : ℝ) / (n + 1) ≤ Real.log (n + 1) - Real.log n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsuccpos : (0 : ℝ) < n + 1 := by positivity
  have hratio : (0 : ℝ) < (n + 1) / n := div_pos hsuccpos hnpos
  have h := Real.one_sub_inv_le_log_of_pos hratio
  rw [Real.log_div hsuccpos.ne' hnpos.ne'] at h
  convert h using 1
  field_simp
  ring

/-- The reciprocal consecutive-log spacing costs at most `n+1`. -/
theorem inv_log_succ_sub_log_le_succ (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n + 1) - Real.log n)⁻¹ ≤ n + 1 := by
  have hgap := one_div_succ_le_log_succ_sub_log n hn
  have hgap_pos : 0 < Real.log (n + 1) - Real.log n := by
    exact lt_of_lt_of_le (one_div_pos.mpr (by positivity)) hgap
  have hsucc_pos : (0 : ℝ) < n + 1 := by positivity
  have hgap' : (n + 1 : ℝ)⁻¹ ≤ Real.log (n + 1) - Real.log n := by
    simpa [one_div] using hgap
  have hinv := (inv_le_inv₀ hgap_pos (inv_pos.mpr hsucc_pos)).2 hgap'
  simpa using hinv

/-- The convenient integral majorant used in the report: `delta_n⁻¹ ≤ 2n`. -/
theorem inv_log_succ_sub_log_le_two_mul (n : ℕ) (hn : 1 ≤ n) :
    (Real.log (n + 1) - Real.log n)⁻¹ ≤ 2 * n := by
  calc
    (Real.log (n + 1) - Real.log n)⁻¹ ≤ n + 1 :=
      inv_log_succ_sub_log_le_succ n hn
    _ ≤ 2 * n := by exact_mod_cast (show n + 1 ≤ 2 * n by omega)

/-! ## The finite mean-square object before inequalities -/

open Complex Finset

/-- A unit Fourier atom with real frequency `lambda`. -/
noncomputable def fourierAtom (lambda t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (t * lambda))

theorem norm_fourierAtom (lambda t : ℝ) : ‖fourierAtom lambda t‖ = 1 := by
  rw [fourierAtom, Complex.norm_exp]
  simp

theorem conj_fourierAtom (lambda t : ℝ) :
    starRingEnd ℂ (fourierAtom lambda t) = fourierAtom (-lambda) t := by
  rw [fourierAtom, fourierAtom, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

theorem fourierAtom_mul (lambda mu t : ℝ) :
    fourierAtom lambda t * fourierAtom mu t = fourierAtom (lambda + mu) t := by
  rw [fourierAtom, fourierAtom, fourierAtom, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The finite Dirichlet polynomial with arbitrary distinctness-free real
frequencies.  The weighted Montgomery--Vaughan input will later specialize
`lambda n` to `log n`. -/
noncomputable def dirichletPolynomial {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (lambda : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ s, c n * fourierAtom (lambda n) t

/-- Exact diagonal/off-diagonal expansion before integration or estimation. -/
theorem dirichletPolynomial_conj_mul {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (lambda : ι → ℝ) (t : ℝ) :
    starRingEnd ℂ (dirichletPolynomial s c lambda t) *
        dirichletPolynomial s c lambda t =
      ∑ m ∈ s, ∑ n ∈ s,
        starRingEnd ℂ (c m) * c n * fourierAtom (lambda n - lambda m) t := by
  simp only [dirichletPolynomial, map_sum, map_mul, conj_fourierAtom]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    starRingEnd ℂ (c m) * fourierAtom (-lambda m) t *
        (c n * fourierAtom (lambda n) t) =
      starRingEnd ℂ (c m) * c n *
        (fourierAtom (-lambda m) t * fourierAtom (lambda n) t) := by ring
    _ = starRingEnd ℂ (c m) * c n *
        fourierAtom (lambda n - lambda m) t := by
      rw [fourierAtom_mul]
      congr 2
      ring

/-- The exact sharp-block kernel used by the RC2 calculation. -/
noncomputable def sharpBlockKernel (U theta : ℝ) : ℂ :=
  ∫ t in U..2 * U, fourierAtom theta t

theorem sharpBlockKernel_zero (U : ℝ) : sharpBlockKernel U 0 = U := by
  simp [sharpBlockKernel, fourierAtom]
  ring

theorem sharpBlockKernel_of_ne_zero (U theta : ℝ) (htheta : theta ≠ 0) :
    sharpBlockKernel U theta =
      (Complex.exp ((-Complex.I * theta) * (2 * U)) -
        Complex.exp ((-Complex.I * theta) * U)) / (-Complex.I * theta) := by
  have hc : (-Complex.I * (theta : ℂ)) ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (ofReal_ne_zero.mpr htheta)
  unfold sharpBlockKernel fourierAtom
  rw [show (fun t : ℝ ↦ Complex.exp (-Complex.I * (t * theta))) =
      fun t : ℝ ↦ Complex.exp ((-Complex.I * theta) * t) by
    funext t
    congr 1
    ring]
  convert integral_exp_mul_complex (a := U) (b := 2 * U) hc using 1 <;>
    push_cast <;> ring

/-- Exact integrated finite mean square.  This theorem includes lower/upper
cross terms automatically.  No spacing or coefficient bound has been used. -/
theorem dirichletPolynomial_integral_expansion {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (lambda : ι → ℝ) (U : ℝ) :
    (∫ t in U..2 * U,
        starRingEnd ℂ (dirichletPolynomial s c lambda t) *
          dirichletPolynomial s c lambda t) =
      ∑ m ∈ s, ∑ n ∈ s,
        starRingEnd ℂ (c m) * c n *
          sharpBlockKernel U (lambda n - lambda m) := by
  simp_rw [dirichletPolynomial_conj_mul]
  have hterm (m n : ι) : IntervalIntegrable
      (fun t ↦ starRingEnd ℂ (c m) * c n *
        fourierAtom (lambda n - lambda m) t) MeasureTheory.volume U (2 * U) := by
    apply Continuous.intervalIntegrable
    unfold fourierAtom
    fun_prop
  have hinner (m : ι) : IntervalIntegrable
      (fun t ↦ ∑ n ∈ s, starRingEnd ℂ (c m) * c n *
        fourierAtom (lambda n - lambda m) t) MeasureTheory.volume U (2 * U) := by
    apply Continuous.intervalIntegrable
    unfold fourierAtom
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun m hm ↦ hinner m)]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n hn ↦ hterm m n)]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_const_mul]
      rfl

/-! ## Multiplicity normalization -/

/-- For a zero of positive multiplicity `m`, the simple-zero indicator
dominates `2m-m²`. -/
theorem multiplicity_inequality (m : ℕ) (hm : 1 ≤ m) :
    (2 * (m : ℤ) - (m : ℤ) ^ 2) ≤ if m = 1 then 1 else 0 := by
  by_cases h : m = 1
  · simp [h]
  · simp [h]
    have hm2 : 2 ≤ m := by omega
    have hm0z : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
    have hm2z : (2 : ℤ) ≤ m := by exact_mod_cast hm2
    nlinarith [mul_nonneg hm0z (sub_nonneg.mpr hm2z)]

/-- The pointwise multiplicity inequality summed over a finite zero set. -/
theorem multiplicity_sum_inequality {ι : Type*} (s : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 1 ≤ m i) :
    2 * ∑ i ∈ s, (m i : ℤ) - ∑ i ∈ s, (m i : ℤ) ^ 2 ≤
      ∑ i ∈ s, if m i = 1 then (1 : ℤ) else 0 := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i hi ↦ multiplicity_inequality (m i) (hm i hi)

/-! ## Exact downstream rational output -/

set_option linter.style.longLine false in
def simplicityNumerator : ℕ :=
  31992243856157335833672729563348202871458080141196704748863890953093858791514176160465935996895558460591033191860272196966422672990681271832100185951157368812755050540392996343087803634476968073290229341576097081065077834468522917662055328212577240812519915537582112158705012184995718757492483869055249

set_option linter.style.longLine false in
def simplicityDenominator : ℕ :=
  2165608429987347592941818086575432193566556506962129164608418643087071174197923420491008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def simplicityLowerBound : ℚ := simplicityNumerator / simplicityDenominator

theorem simplicityDenominator_pos : 0 < simplicityDenominator := by
  norm_num [simplicityDenominator]

theorem simplicityLowerBound_pos : 0 < simplicityLowerBound := by
  norm_num [simplicityLowerBound, simplicityNumerator, simplicityDenominator]

theorem simplicityLowerBound_gt_01477 : 1477 / 100000 < simplicityLowerBound := by
  norm_num [simplicityLowerBound, simplicityNumerator, simplicityDenominator]

theorem simplicityLowerBound_lt_01478 : simplicityLowerBound < 1478 / 100000 := by
  norm_num [simplicityLowerBound, simplicityNumerator, simplicityDenominator]

end ZetaLean.HigherXi
