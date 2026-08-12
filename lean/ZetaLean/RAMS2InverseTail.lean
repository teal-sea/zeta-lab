/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite inverse-square tails from prefix bounds

This file isolates the cutoff-independent upper-tail estimate needed by the
two-range RC2 endpoint energy.  The input is a nonnegative sequence whose
positive-index prefix sums are bounded by `C N (1 + log N)`.
-/

namespace ZetaLean.HigherXi

open Finset MeasureTheory

/-- Positive-index prefix mass. -/
noncomputable def positivePrefix (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, b n

/-- The finite inverse-square tail on `X < n ≤ W`. -/
noncomputable def inverseSquareTail (b : ℕ → ℝ) (X W : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc X W, b n / (n : ℝ) ^ 2

theorem positivePrefix_nonneg
    (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n) (N : ℕ) :
    0 ≤ positivePrefix b N := by
  exact Finset.sum_nonneg fun n _ ↦ hb n

/-- Removing the zero coefficient turns the standard zero-based prefix into
the positive-index prefix used in the arithmetic application. -/
theorem sum_Icc_zero_positivePart (b : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 0 N, if n = 0 then 0 else b n) = positivePrefix b N := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
  simp only [ite_true, zero_add, positivePrefix]
  apply Finset.sum_congr
  · ext n
    simp [Nat.one_le_iff_ne_zero]
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    simp [hn.1.ne']

/-- Derivative of the inverse-square weight away from zero. -/
theorem hasDerivAt_inv_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ u⁻²) (-2 * t⁻³) t := by
  convert (hasDerivAt_inv ht).mul (hasDerivAt_inv ht) using 1 <;> field_simp <;> ring

/-- Exact finite Abel identity for the inverse-square tail. -/
theorem inverseSquareTail_abel
    (b : ℕ → ℝ) (X W : ℕ) (hX : 1 ≤ X) (hXW : X ≤ W) :
    inverseSquareTail b X W =
      (W : ℝ)⁻² * positivePrefix b W -
        (X : ℝ)⁻² * positivePrefix b X +
          ∫ t in Set.Ioc (X : ℝ) W,
            2 * t⁻³ * positivePrefix b ⌊t⌋₊ := by
  let c : ℕ → ℝ := fun n ↦ if n = 0 then 0 else b n
  have hpos {t : ℝ} (ht : t ∈ Set.Icc (X : ℝ) W) : 0 < t := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hX.trans (by exact_mod_cast ht.1))
  have hdiff : ∀ t ∈ Set.Icc (X : ℝ) W,
      DifferentiableAt ℝ (fun u : ℝ ↦ u⁻²) t := by
    intro t ht
    exact (hasDerivAt_inv_sq (ne_of_gt (hpos ht))).differentiableAt
  have hint : IntegrableOn (deriv (fun u : ℝ ↦ u⁻²))
      (Set.Icc (X : ℝ) W) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ -2 * t⁻³) (Set.Icc (X : ℝ) W) := by
      fun_prop
    apply hcont.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul'
    (c := c) (f := fun t : ℝ ↦ t⁻²) hXW hdiff hint
  rw [show (∑ k ∈ Finset.Ioc X W, (k : ℝ)⁻² * c k) = inverseSquareTail b X W by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Ioc] at hk
    simp [c, hk.1.ne', inverseSquareTail, div_eq_mul_inv]
    ring] at habel
  rw [sum_Icc_zero_positivePart b W, sum_Icc_zero_positivePart b X] at habel
  rw [habel]
  congr 1
  · ring
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with t ht
    by_cases htmem : t ∈ Set.Ioc (X : ℝ) W
    · have ht0 : t ≠ 0 := by
        have : 0 < t := lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_one) htmem.1.le
        exact ne_of_gt this
      rw [(hasDerivAt_inv_sq ht0).deriv]
      ring
    · simp [htmem]

/-- Elementary antiderivative for the logarithmic inverse-square envelope. -/
theorem hasDerivAt_logInverseSquarePrimitive
    (C t : ℝ) (ht : t ≠ 0) :
    HasDerivAt
      (fun u : ℝ ↦ -2 * C * (2 + Real.log u) / u)
      (2 * C * (1 + Real.log t) / t ^ 2) t := by
  convert (((hasDerivAt_const t 2).add (Real.hasDerivAt_log ht)).div
    (hasDerivAt_id t) ht).const_mul (-2 * C) using 1 <;> field_simp <;> ring

/-- Exact integral of the logarithmic inverse-square envelope on a positive
finite interval. -/
theorem integral_log_inverse_sq
    (C X W : ℝ) (hX : 0 < X) (hXW : X ≤ W) :
    ∫ t in Set.Ioc X W, 2 * C * (1 + Real.log t) / t ^ 2 =
      2 * C * ((2 + Real.log X) / X - (2 + Real.log W) / W) := by
  rw [← intervalIntegral.integral_of_le hXW]
  have hderiv : ∀ t ∈ Set.uIcc X W,
      HasDerivAt
        (fun u : ℝ ↦ -2 * C * (2 + Real.log u) / u)
        (2 * C * (1 + Real.log t) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hXW] at ht
    exact hasDerivAt_logInverseSquarePrimitive C t
      (ne_of_gt (lt_of_lt_of_le hX ht.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  ring

/-- A prefix estimate of order `N (1 + log N)` gives a finite inverse-square
tail bound independent of the remote cutoff.  The explicit constant is four.
-/
theorem inverseSquareTail_le_four
    (b : ℕ → ℝ) (C : ℝ) (X W : ℕ)
    (hb : ∀ n, 0 ≤ b n) (hC : 0 ≤ C)
    (hprefix : ∀ N, positivePrefix b N ≤
      C * (N : ℝ) * (1 + Real.log N))
    (hX : 1 ≤ X) (hXW : X ≤ W) :
    inverseSquareTail b X W ≤
      4 * C * (1 + Real.log X) / X := by
  have hW : 1 ≤ W := hX.trans hXW
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hWpos : (0 : ℝ) < W := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hW)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hlogW : 0 ≤ Real.log W := Real.log_nonneg (by exact_mod_cast hW)
  have hendpoint : (W : ℝ)⁻² * positivePrefix b W ≤
      C * (1 + Real.log W) / W := by
    have hw2 : 0 ≤ (W : ℝ)⁻² := by positivity
    calc
      (W : ℝ)⁻² * positivePrefix b W ≤
          (W : ℝ)⁻² * (C * (W : ℝ) * (1 + Real.log W)) :=
        mul_le_mul_of_nonneg_left (hprefix W) hw2
      _ = C * (1 + Real.log W) / W := by field_simp; ring
  have hintegral :
      (∫ t in Set.Ioc (X : ℝ) W,
        2 * t⁻³ * positivePrefix b ⌊t⌋₊) ≤
      ∫ t in Set.Ioc (X : ℝ) W,
        2 * C * (1 + Real.log t) / t ^ 2 := by
    apply MeasureTheory.integral_mono_of_nonneg
    · filter_upwards with t ht
      by_cases htmem : t ∈ Set.Ioc (X : ℝ) W
      · have hprefix0 : 0 ≤ positivePrefix b ⌊t⌋₊ :=
          positivePrefix_nonneg b hb ⌊t⌋₊
        positivity
      · simp [htmem]
    · have hcont : ContinuousOn
          (fun t : ℝ ↦ 2 * C * (1 + Real.log t) / t ^ 2)
          (Set.Icc (X : ℝ) W) := by
          apply ContinuousOn.div
          · fun_prop
          · fun_prop
          · intro t ht
            have htpos : 0 < t := lt_of_lt_of_le hXpos ht.1
            positivity
        exact hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    · filter_upwards with t ht
      by_cases htmem : t ∈ Set.Ioc (X : ℝ) W
      · have htpos : 0 < t := lt_of_lt_of_le hXpos htmem.1.le
        have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff _).mpr htmem.1.le
        have hfloorpos : (0 : ℝ) < ⌊t⌋₊ := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor1)
        have hfloort : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le htpos.le
        have hlogfloor : Real.log ⌊t⌋₊ ≤ Real.log t :=
          Real.strictMonoOn_log.monotoneOn hfloorpos htpos hfloort
        have henv : positivePrefix b ⌊t⌋₊ ≤
            C * t * (1 + Real.log t) := by
          calc
            positivePrefix b ⌊t⌋₊ ≤
                C * (⌊t⌋₊ : ℝ) * (1 + Real.log ⌊t⌋₊) := hprefix ⌊t⌋₊
            _ ≤ C * t * (1 + Real.log t) := by
              have hlogfloor0 : 0 ≤ Real.log ⌊t⌋₊ :=
                Real.log_nonneg (by exact_mod_cast hfloor1)
              gcongr
        have hfactor : 0 ≤ 2 * t⁻³ := by positivity
        calc
          2 * t⁻³ * positivePrefix b ⌊t⌋₊ ≤
              2 * t⁻³ * (C * t * (1 + Real.log t)) :=
            mul_le_mul_of_nonneg_left henv hfactor
          _ = 2 * C * (1 + Real.log t) / t ^ 2 := by field_simp; ring
      · simp [htmem]
  rw [inverseSquareTail_abel b X W hX hXW]
  calc
    (W : ℝ)⁻² * positivePrefix b W -
          (X : ℝ)⁻² * positivePrefix b X +
            ∫ t in Set.Ioc (X : ℝ) W,
              2 * t⁻³ * positivePrefix b ⌊t⌋₊
        ≤ (W : ℝ)⁻² * positivePrefix b W +
            ∫ t in Set.Ioc (X : ℝ) W,
              2 * t⁻³ * positivePrefix b ⌊t⌋₊ := by
          have hnonneg := positivePrefix_nonneg b hb X
          have : 0 ≤ (X : ℝ)⁻² * positivePrefix b X := mul_nonneg (by positivity) hnonneg
          linarith
    _ ≤ C * (1 + Real.log W) / W +
          ∫ t in Set.Ioc (X : ℝ) W,
            2 * C * (1 + Real.log t) / t ^ 2 := add_le_add hendpoint hintegral
    _ = C * (1 + Real.log W) / W +
          2 * C * ((2 + Real.log X) / X - (2 + Real.log W) / W) := by
        rw [integral_log_inverse_sq C X W hXpos (by exact_mod_cast hXW)]
    _ ≤ 2 * C * (2 + Real.log X) / X := by
        have : 0 ≤ C * (3 + Real.log W) / W := by positivity
        field_simp
        field_simp at this
        nlinarith
    _ ≤ 4 * C * (1 + Real.log X) / X := by
        apply div_le_div_of_nonneg_right _ hXpos.le
        nlinarith

/-- RC2 endpoint-energy form of `inverseSquareTail_le_four`: multiplying by
the breakpoint square leaves order `X (1 + log X)`, uniformly in `W`. -/
theorem sq_mul_inverseSquareTail_le_four
    (b : ℕ → ℝ) (C : ℝ) (X W : ℕ)
    (hb : ∀ n, 0 ≤ b n) (hC : 0 ≤ C)
    (hprefix : ∀ N, positivePrefix b N ≤
      C * (N : ℝ) * (1 + Real.log N))
    (hX : 1 ≤ X) (hXW : X ≤ W) :
    (X : ℝ) ^ 2 * inverseSquareTail b X W ≤
      4 * C * X * (1 + Real.log X) := by
  have htail := inverseSquareTail_le_four b C X W hb hC hprefix hX hXW
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hsq : 0 ≤ (X : ℝ) ^ 2 := sq_nonneg X
  calc
    (X : ℝ) ^ 2 * inverseSquareTail b X W ≤
        (X : ℝ) ^ 2 * (4 * C * (1 + Real.log X) / X) :=
      mul_le_mul_of_nonneg_left htail hsq
    _ = 4 * C * X * (1 + Real.log X) := by field_simp; ring

/-- Direct complex-coefficient specialization used by the two-range energy:
`b n = ‖a n‖²` is automatically nonnegative. -/
theorem sq_mul_norm_inverseSquareTail_le_four
    (a : ℕ → ℂ) (C : ℝ) (X W : ℕ)
    (hC : 0 ≤ C)
    (hprefix : ∀ N, positivePrefix (fun n ↦ ‖a n‖ ^ 2) N ≤
      C * (N : ℝ) * (1 + Real.log N))
    (hX : 1 ≤ X) (hXW : X ≤ W) :
    (X : ℝ) ^ 2 *
        (∑ n ∈ Finset.Ioc X W, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤
      4 * C * X * (1 + Real.log X) := by
  simpa [inverseSquareTail] using
    sq_mul_inverseSquareTail_le_four (fun n ↦ ‖a n‖ ^ 2) C X W
      (fun n ↦ sq_nonneg ‖a n‖) hC hprefix hX hXW

end ZetaLean.HigherXi
