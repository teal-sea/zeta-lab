/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# Sum versus integral: the steeper tail exponent

`ZetaLean/DHTailBound.lean` bounds the DH tail by summing per-block
estimates, which decays like `K^{-σ}` with `σ ≈ 0.81` — too slow to
instantiate rung 3 at the oracle point (`HANDOFF.md` prices that route at
~230 days of kernel compute).  Comparing the sum to an *integral* instead
trades one power of `K` for one derivative, which is what drops the
instantiation to a few days.

This file is the domain-independent half of that trade: the elementary
per-step comparison, for any `C¹` function into a normed space, proved from
the fundamental theorem of calculus.  No Bernoulli numbers and no general
Euler–Maclaurin are involved — Mathlib has neither, and neither is needed.

* `norm_sub_le_integral_norm_deriv` — travel bound: a `C¹` function moves
  no further than the integral of its derivative's norm.
* `norm_sub_integral_le` — **rectangle rule with a derivative remainder**:
  `‖(b − a) • g a − ∫_a^b g‖ ≤ |b − a| · ∫_a^b ‖g'‖`.  Applied on unit
  steps and summed, this is what turns `K^{-σ}` into `K^{-(σ+1)}`.

**The next two steps**, in order, are recorded here so the route is not
re-derived:

1. *The trapezoid refinement*, `K^{-(σ+2)}` and ~1 day of compute, from the
   identity `∫_a^b g = (b−a)(g a + g b)/2 − ½∫_a^b (t−a)(b−t) g''(t) dt` —
   integration by parts twice against the weight `(t−a)(b−t)`
   (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`).  The first-order
   Euler–Maclaurin correction is exactly the trapezoid's endpoint average,
   which is why no Bernoulli machinery appears.
2. *The DH-specific half*: the closed-form block antiderivative
   `F(x) = Σ_j c_j (5x+j)^{1−s} / (5(1−s))`, which tends to `0` at `∞`
   precisely because the DH coefficients sum to zero (each summand alone
   diverges for `σ < 1`), so `∫_K^∞ B = −F(K)` is computable by the
   interval machinery already built; plus a third-difference bound on
   `∫_K^∞ ‖B''‖`, structurally identical to the block estimates already
   proved in `DHTailBound.lean`.
-/

open intervalIntegral MeasureTheory

namespace ZetaLean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Travel bound: a `C¹` function moves no further than the integral of its
derivative's norm.  Fundamental theorem of calculus plus the triangle
inequality for integrals. -/
theorem norm_sub_le_integral_norm_deriv {g g' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
    (hint : IntervalIntegrable g' volume a b)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ‖g x - g a‖ ≤ ∫ t in a..b, ‖g' t‖ := by
  have hax : Set.uIcc a x ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1]
    exact Set.Icc_subset_Icc le_rfl hx.2
  have heq : ∫ t in a..x, g' t = g x - g a :=
    integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hax ht)) (hint.mono_set hax)
  rw [← heq]
  refine (intervalIntegral.norm_integral_le_integral_norm hx.1).trans ?_
  have hsplit : (∫ t in a..x, ‖g' t‖) + ∫ t in x..b, ‖g' t‖ = ∫ t in a..b, ‖g' t‖ := by
    refine integral_add_adjacent_intervals ?_ ?_
    · exact (hint.norm).mono_set hax
    · refine (hint.norm).mono_set ?_
      rw [Set.uIcc_of_le hx.2, Set.uIcc_of_le hab]
      exact Set.Icc_subset_Icc hx.1 le_rfl
  have hnn : 0 ≤ ∫ t in x..b, ‖g' t‖ :=
    integral_nonneg hx.2 fun t _ => norm_nonneg _
  linarith

/-- **Rectangle rule with a derivative remainder.**  Replacing `∫_a^b g` by
the left-endpoint rectangle `(b − a) • g a` costs at most
`|b − a| · ∫_a^b ‖g'‖`.  Applied on unit steps and summed, this is the
trade that turns the DH tail's `K^{-σ}` into `K^{-(σ+1)}`. -/
theorem norm_sub_integral_le {g g' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
    (hint : IntervalIntegrable g' volume a b)
    (hg : IntervalIntegrable g volume a b) :
    ‖(b - a) • g a - ∫ t in a..b, g t‖ ≤ |b - a| * ∫ t in a..b, ‖g' t‖ := by
  have hsub : (b - a) • g a - ∫ t in a..b, g t = ∫ t in a..b, (g a - g t) := by
    rw [integral_sub intervalIntegrable_const hg, intervalIntegral.integral_const]
  rw [hsub, mul_comm]
  refine norm_integral_le_of_norm_le_const fun t ht => ?_
  rw [Set.uIoc_of_le hab] at ht
  rw [norm_sub_rev]
  exact norm_sub_le_integral_norm_deriv hab hderiv hint ⟨le_of_lt ht.1, ht.2⟩

end ZetaLean
