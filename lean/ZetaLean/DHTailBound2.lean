/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.DavenportHeilbronn
import ZetaLean.DHAnalytic
import ZetaLean.DHTailBound

/-!
# Sum versus integral: the steeper tail exponent

`ZetaLean/DHTailBound.lean` bounds the DH tail by summing per-block
estimates, which decays like `K^{-σ}` with `σ ≈ 0.81`, too slow to
instantiate rung 3 at the oracle point (`HANDOFF.md` prices that route at
~230 days of kernel compute).  Comparing the sum to an *integral* trades one
power of `K` for one derivative; the trapezoid refinement trades a second.
Validated numerically at the oracle point: 1e-3 accuracy needs `K ≈ 205000`
blocks through `DH_tail_bound`, `K ≈ 1800` through the order-1 bound here,
and `K ≈ 254` through the order-2 bound, the ~800× reduction that turns the
offline kernel run from months into hours.

No Bernoulli numbers and no general Euler–Maclaurin appear: Mathlib has
neither, and neither is needed: the first Euler–Maclaurin correction *is*
the trapezoid's endpoint average.

## The domain-independent half

* `norm_sub_le_integral_norm_deriv`, travel bound: a `C¹` function moves
  no further than the integral of its derivative's norm.
* `norm_sub_integral_le`, **rectangle rule with a derivative remainder**:
  `‖(b − a) • g a − ∫_a^b g‖ ≤ |b − a| · ∫_a^b ‖g'‖`.
* `norm_trapezoid_sub_integral_le`: **trapezoid rule with a
  second-derivative remainder**: replacing `∫_a^b g` by the endpoint
  average `((b−a)/2) • (g a + g b)` costs at most `((b−a)²/8)·∫_a^b ‖g''‖`,
  by integrating the weight `(t−a)(b−t)` by parts twice.
* `norm_tsum_sub_integral_le` / `norm_tsum_sub_integral_trapezoid_le`: the
  payoff, summed along unit steps of a half-line:
  `‖Σ_{n≥0} g(A+n) − ∫_A^∞ g‖ ≤ ∫_A^∞ ‖g'‖`, and with the trapezoid's
  endpoint correction `−½·g(A)` the remainder sharpens to
  `(1/8)·∫_A^∞ ‖g''‖`.

## The DH-specific half

The five-term block, read at a *continuous* argument and a *generic*
exponent, is one function:
`dhPair w x = (5x+1)^w − (5x+4)^w + κ((5x+2)^w − (5x+3)^w)`.
The block is `dhPair (−s)`, differentiation is `d/dx dhPair w = 5w·dhPair
(w−1)` (`hasDerivAt_dhPair`), the antiderivative is `dhAnti = dhPair (1−s) /
(5(1−s))`, closed-form precisely because the DH coefficients sum to zero:
each summand of `dhPair (1−s)` alone diverges for `σ < 1`, while the paired
combination tends to `0`, and one mean-value estimate (`norm_dhPair_le`)
bounds every level at once.

* `integral_Ioi_dhPair`: `∫_K^∞ B = −dhAnti K`, fundamental theorem of
  calculus on the half-line plus the vanishing limit.
* `DH_tail_bound_order1`, for `Re s > 0`, `s ≠ 1`, `K ≥ 1`:
  `‖DH s − (Σ_{n<5K} − dhAnti K)‖ ≤ (3+κ)·‖s‖·‖s+1‖·(5K+1)^{-σ-1}/(σ+1)`.
* `DH_tail_bound_order2`, with the endpoint correction `+ B(K)/2`:
  `‖DH s − (Σ_{n<5K} + B(K)/2 − dhAnti K)‖
     ≤ (5/8)·(3+κ)·‖s‖·‖s+1‖·‖s+2‖·(5K+1)^{-σ-2}/(σ+2)`.

The corrections cost the offline run five extra certified cpow evaluations
(`(5K+j)^{1−s} = (5K+j)·(5K+j)^{−s}` reuses the existing term boxes) and in
exchange divide the number of certified terms by ~800.  The assembly
theorems consuming these bounds live in `ZetaLean/DHAssembly.lean`.
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

/-- **Trapezoid rule with a second-derivative remainder.**  Replacing
`∫_a^b g` by the endpoint average `((b − a)/2) • (g a + g b)` costs at most
`((b − a)²/8) · ∫_a^b ‖g''‖`: integrate the weight `w t = (t−a)(b−t)` by
parts twice and bound `|w| ≤ (b−a)²/4`.  The first Euler–Maclaurin
correction with no Bernoulli machinery. -/
theorem norm_trapezoid_sub_integral_le {g g' g'' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
    (hderiv' : ∀ t ∈ Set.uIcc a b, HasDerivAt g' (g'' t) t)
    (hcont'' : ContinuousOn g'' (Set.uIcc a b)) :
    ‖((b - a) / 2) • (g a + g b) - ∫ t in a..b, g t‖
      ≤ (b - a) ^ 2 / 8 * ∫ t in a..b, ‖g'' t‖ := by
  -- continuity of `g` and `g'` follows from their differentiability
  have hcg : ContinuousOn g (Set.uIcc a b) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hcg' : ContinuousOn g' (Set.uIcc a b) := fun t ht =>
    ((hderiv' t ht).continuousAt).continuousWithinAt
  -- the weight `(t−a)(b−t)` and its derivatives
  have hwderiv : ∀ t : ℝ, HasDerivAt (fun t => (t - a) * (b - t)) (a + b - 2 * t) t := by
    intro t
    have he : a + b - 2 * t = 1 * (b - t) + (t - a) * (0 - 1) := by ring
    rw [he]
    exact ((hasDerivAt_id t).sub_const a).mul
      ((hasDerivAt_const t b).sub (hasDerivAt_id t))
  have hw'deriv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => a + b - 2 * t) (-2) t := by
    intro t
    have he : (-2 : ℝ) = 0 - 2 * 1 := by ring
    rw [he]
    exact (hasDerivAt_const t (a + b)).sub ((hasDerivAt_id t).const_mul (2 : ℝ))
  have hcw : Continuous fun t : ℝ => (t - a) * (b - t) := by fun_prop
  have hcw' : Continuous fun t : ℝ => a + b - 2 * t := by fun_prop
  -- integrability of every integrand in sight
  have hint_g : IntervalIntegrable g volume a b := hcg.intervalIntegrable
  have hint_wg' : IntervalIntegrable (fun t => (a + b - 2 * t) • g' t) volume a b :=
    ((hcw'.continuousOn).smul hcg').intervalIntegrable
  have hint_wg'' : IntervalIntegrable (fun t => ((t - a) * (b - t)) • g'' t) volume a b :=
    ((hcw.continuousOn).smul hcont'').intervalIntegrable
  have hint_2g : IntervalIntegrable (fun t => (-2 : ℝ) • g t) volume a b :=
    (continuous_const.continuousOn.smul hcg).intervalIntegrable
  -- first integration by parts: `∫ (w•g'' + w'•g') = [w•g']_a^b = 0`
  have hI1 := integral_eq_sub_of_hasDerivAt
    (f := fun t => ((t - a) * (b - t)) • g' t)
    (f' := fun t => ((t - a) * (b - t)) • g'' t + (a + b - 2 * t) • g' t)
    (fun t ht => (hwderiv t).smul (hderiv' t ht)) (hint_wg''.add hint_wg')
  have hIBP1 : ∫ t in a..b, ((t - a) * (b - t)) • g'' t
      = -∫ t in a..b, (a + b - 2 * t) • g' t := by
    rw [integral_add hint_wg'' hint_wg'] at hI1
    simp only [sub_self, mul_zero, zero_mul, zero_smul] at hI1
    exact eq_neg_of_add_eq_zero_left hI1
  -- second integration by parts: `∫ (w'•g' + (-2)•g) = [w'•g]_a^b`
  have hI2 := integral_eq_sub_of_hasDerivAt
    (f := fun t => (a + b - 2 * t) • g t)
    (f' := fun t => (a + b - 2 * t) • g' t + (-2 : ℝ) • g t)
    (fun t ht => (hw'deriv t).smul (hderiv t ht)) (hint_wg'.add hint_2g)
  have hIBP2 : ∫ t in a..b, (a + b - 2 * t) • g' t
      = ((a + b - 2 * b) • g b - (a + b - 2 * a) • g a)
        - (-2 : ℝ) • ∫ t in a..b, g t := by
    rw [integral_add hint_wg' hint_2g, intervalIntegral.integral_smul] at hI2
    exact eq_sub_of_add_eq hI2
  -- the exact identity, halved
  have hkey : ((b - a) / 2) • (g a + g b) - ∫ t in a..b, g t
      = (2⁻¹ : ℝ) • ∫ t in a..b, ((t - a) * (b - t)) • g'' t := by
    rw [hIBP1, hIBP2]
    module
  rw [hkey, norm_smul, Real.norm_eq_abs]
  -- bound `|∫ w•g''| ≤ ((b−a)²/4)·∫‖g''‖` and finish
  have h1 : ‖∫ t in a..b, ((t - a) * (b - t)) • g'' t‖
      ≤ ∫ t in a..b, ‖((t - a) * (b - t)) • g'' t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hab
  have h2 : ∫ t in a..b, ‖((t - a) * (b - t)) • g'' t‖
      ≤ ∫ t in a..b, (b - a) ^ 2 / 4 * ‖g'' t‖ := by
    refine intervalIntegral.integral_mono_on hab
      ((hcw.continuousOn.smul hcont'').norm.intervalIntegrable)
      ((continuous_const.continuousOn.mul hcont''.norm).intervalIntegrable)
      fun t ht => ?_
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [abs_le]
    constructor
    · nlinarith [ht.1, ht.2]
    · nlinarith [sq_nonneg (t - a - (b - t)), ht.1, ht.2]
  have h3 : ∫ t in a..b, (b - a) ^ 2 / 4 * ‖g'' t‖
      = (b - a) ^ 2 / 4 * ∫ t in a..b, ‖g'' t‖ :=
    intervalIntegral.integral_const_mul _ _
  calc |(2⁻¹ : ℝ)| * ‖∫ t in a..b, ((t - a) * (b - t)) • g'' t‖
      ≤ |(2⁻¹ : ℝ)| * ((b - a) ^ 2 / 4 * ∫ t in a..b, ‖g'' t‖) := by
        rw [← h3]
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg _)
    _ = (b - a) ^ 2 / 8 * ∫ t in a..b, ‖g'' t‖ := by
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)]
        ring

section HalfLine

variable {g g' g'' : ℝ → E} {A : ℝ}

private lemma step_le (A : ℝ) (n : ℕ) : (A + n : ℝ) ≤ A + (n + 1 : ℕ) := by
  push_cast
  linarith

private lemma step_subset (A : ℝ) (n : ℕ) :
    Set.uIcc (A + n : ℝ) (A + (n + 1 : ℕ)) ⊆ Set.Ici A := by
  intro t ht
  rw [Set.uIcc_of_le (step_le A n)] at ht
  have h0 : (A : ℝ) ≤ A + n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  exact le_trans h0 ht.1

/-- **Summed rectangle rule on a half-line.**  For `C¹` `g` with summable
unit-step samples and integrable `g`, `‖g'‖`,
`‖Σ_{n≥0} g(A+n) − ∫_A^∞ g‖ ≤ ∫_A^∞ ‖g'‖`. -/
theorem norm_tsum_sub_integral_le
    (hderiv : ∀ x ∈ Set.Ici A, HasDerivAt g (g' x) x)
    (hcont' : ContinuousOn g' (Set.Ici A))
    (hsum : Summable fun n : ℕ => g (A + n))
    (hint : IntegrableOn g (Set.Ioi A))
    (hint' : IntegrableOn (fun x => ‖g' x‖) (Set.Ioi A)) :
    ‖(∑' n : ℕ, g (A + n)) - ∫ x in Set.Ioi A, g x‖ ≤ ∫ x in Set.Ioi A, ‖g' x‖ := by
  have hcg : ContinuousOn g (Set.Ici A) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hint_g : ∀ n : ℕ, IntervalIntegrable g volume (A + n) (A + (n + 1 : ℕ)) :=
    fun n => (hcg.mono (step_subset A n)).intervalIntegrable
  have hint_g' : ∀ n : ℕ, IntervalIntegrable g' volume (A + n) (A + (n + 1 : ℕ)) :=
    fun n => (hcont'.mono (step_subset A n)).intervalIntegrable
  have hint_ng' : ∀ n : ℕ,
      IntervalIntegrable (fun x => ‖g' x‖) volume (A + n) (A + (n + 1 : ℕ)) :=
    fun n => ((hcont'.mono (step_subset A n)).norm).intervalIntegrable
  -- the per-step rectangle bound, at unit steps
  have hstep : ∀ n : ℕ, ‖g (A + n) - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t‖
      ≤ ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), ‖g' t‖ := by
    intro n
    have h := norm_sub_integral_le (step_le A n)
      (fun t ht => hderiv t (step_subset A n ht)) (hint_g' n) (hint_g n)
    have h1 : (A + ((n + 1 : ℕ) : ℝ)) - (A + n) = 1 := by push_cast; ring
    rw [h1, one_smul, abs_one, one_mul] at h
    exact h
  -- the finite-`N` inequality, uniform in `N`
  have hfin : ∀ N : ℕ, ‖(∑ n ∈ Finset.range N, g (A + n))
      - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t‖ ≤ ∫ x in Set.Ioi A, ‖g' x‖ := by
    intro N
    have hAN : (A : ℝ) ≤ A + (N : ℕ) := by
      have : (0 : ℝ) ≤ (N : ℕ) := Nat.cast_nonneg N
      linarith
    have hadj : ∑ n ∈ Finset.range N,
        ∫ t in ((fun k : ℕ => (A + k : ℝ)) n)..((fun k : ℕ => (A + k : ℝ)) (n + 1)), g t
        = ∫ t in ((fun k : ℕ => (A + k : ℝ)) 0)..((fun k : ℕ => (A + k : ℝ)) N), g t :=
      intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint_g k
    have hadj' : ∑ n ∈ Finset.range N,
        ∫ t in ((fun k : ℕ => (A + k : ℝ)) n)..((fun k : ℕ => (A + k : ℝ)) (n + 1)), ‖g' t‖
        = ∫ t in ((fun k : ℕ => (A + k : ℝ)) 0)..((fun k : ℕ => (A + k : ℝ)) N), ‖g' t‖ :=
      intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint_ng' k
    simp only [Nat.cast_zero, add_zero] at hadj hadj'
    have hdecomp : (∑ n ∈ Finset.range N, g (A + n))
        - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t
        = ∑ n ∈ Finset.range N,
            (g (A + n) - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t) := by
      rw [Finset.sum_sub_distrib, hadj]
    calc ‖(∑ n ∈ Finset.range N, g (A + n)) - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t‖
        = ‖∑ n ∈ Finset.range N,
            (g (A + n) - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t)‖ := by
          rw [hdecomp]
      _ ≤ ∑ n ∈ Finset.range N,
            ‖g (A + n) - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N, ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), ‖g' t‖ :=
          Finset.sum_le_sum fun n _ => hstep n
      _ = ∫ t in (A : ℝ)..(A + (N : ℕ)), ‖g' t‖ := hadj'
      _ ≤ ∫ x in Set.Ioi A, ‖g' x‖ := by
          rw [intervalIntegral.integral_of_le hAN]
          apply setIntegral_mono_set hint'
          · filter_upwards with x using norm_nonneg _
          · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  -- pass to the limit `N → ∞`
  have hlimS : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g (A + n))
      Filter.atTop (nhds (∑' n : ℕ, g (A + n))) := hsum.hasSum.tendsto_sum_nat
  have hlimI : Filter.Tendsto (fun N : ℕ => ∫ t in (A : ℝ)..(A + (N : ℕ)), g t)
      Filter.atTop (nhds (∫ x in Set.Ioi A, g x)) :=
    intervalIntegral_tendsto_integral_Ioi A hint
      (Filter.tendsto_atTop_add_const_left _ A tendsto_natCast_atTop_atTop)
  exact le_of_tendsto' ((hlimS.sub hlimI).norm) hfin

/-- **Summed trapezoid rule on a half-line.**  With the endpoint correction
`−½·g(A)`, the sum–integral comparison sharpens to a second-derivative
remainder: `‖Σ_{n≥0} g(A+n) − ½·g(A) − ∫_A^∞ g‖ ≤ (1/8)·∫_A^∞ ‖g''‖`.  This
is what turns the DH tail's `K^{-(σ+1)}` into `K^{-(σ+2)}`. -/
theorem norm_tsum_sub_integral_trapezoid_le
    (hderiv : ∀ x ∈ Set.Ici A, HasDerivAt g (g' x) x)
    (hderiv' : ∀ x ∈ Set.Ici A, HasDerivAt g' (g'' x) x)
    (hcont'' : ContinuousOn g'' (Set.Ici A))
    (hsum : Summable fun n : ℕ => g (A + n))
    (hint : IntegrableOn g (Set.Ioi A))
    (hint'' : IntegrableOn (fun x => ‖g'' x‖) (Set.Ioi A)) :
    ‖(∑' n : ℕ, g (A + n)) - (2⁻¹ : ℝ) • g A - ∫ x in Set.Ioi A, g x‖
      ≤ 8⁻¹ * ∫ x in Set.Ioi A, ‖g'' x‖ := by
  have hcg : ContinuousOn g (Set.Ici A) := fun t ht =>
    ((hderiv t ht).continuousAt).continuousWithinAt
  have hint_g : ∀ n : ℕ, IntervalIntegrable g volume (A + n) (A + (n + 1 : ℕ)) :=
    fun n => (hcg.mono (step_subset A n)).intervalIntegrable
  have hint_ng'' : ∀ n : ℕ,
      IntervalIntegrable (fun x => ‖g'' x‖) volume (A + n) (A + (n + 1 : ℕ)) :=
    fun n => ((hcont''.mono (step_subset A n)).norm).intervalIntegrable
  -- the per-step trapezoid bound, at unit steps
  have hstep : ∀ n : ℕ,
      ‖(2⁻¹ : ℝ) • (g (A + n) + g (A + (n + 1 : ℕ)))
          - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t‖
        ≤ 8⁻¹ * ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), ‖g'' t‖ := by
    intro n
    have h := norm_trapezoid_sub_integral_le (step_le A n)
      (fun t ht => hderiv t (step_subset A n ht))
      (fun t ht => hderiv' t (step_subset A n ht))
      (hcont''.mono (step_subset A n))
    have h1 : (A + ((n + 1 : ℕ) : ℝ)) - (A + n) = 1 := by push_cast; ring
    rw [h1, show (1 : ℝ) / 2 = 2⁻¹ by norm_num,
      show (1 : ℝ) ^ 2 / 8 = 8⁻¹ by norm_num] at h
    exact h
  -- the trapezoid sums telescope to the plain sums plus endpoint terms
  have htrap : ∀ N : ℕ, ∑ n ∈ Finset.range N,
        (2⁻¹ : ℝ) • (g (A + n) + g (A + (n + 1 : ℕ)))
      = (∑ n ∈ Finset.range N, g (A + n))
        + (2⁻¹ : ℝ) • g (A + (N : ℕ)) - (2⁻¹ : ℝ) • g (A + (0 : ℕ)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        module
  -- the finite-`N` inequality, uniform in `N`
  have hfin : ∀ N : ℕ, ‖(∑ n ∈ Finset.range N, g (A + n))
      + (2⁻¹ : ℝ) • g (A + (N : ℕ)) - (2⁻¹ : ℝ) • g A
      - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t‖
        ≤ 8⁻¹ * ∫ x in Set.Ioi A, ‖g'' x‖ := by
    intro N
    have hAN : (A : ℝ) ≤ A + (N : ℕ) := by
      have : (0 : ℝ) ≤ (N : ℕ) := Nat.cast_nonneg N
      linarith
    have hadj : ∑ n ∈ Finset.range N,
        ∫ t in ((fun k : ℕ => (A + k : ℝ)) n)..((fun k : ℕ => (A + k : ℝ)) (n + 1)), g t
        = ∫ t in ((fun k : ℕ => (A + k : ℝ)) 0)..((fun k : ℕ => (A + k : ℝ)) N), g t :=
      intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint_g k
    have hadj'' : ∑ n ∈ Finset.range N,
        ∫ t in ((fun k : ℕ => (A + k : ℝ)) n)..((fun k : ℕ => (A + k : ℝ)) (n + 1)), ‖g'' t‖
        = ∫ t in ((fun k : ℕ => (A + k : ℝ)) 0)..((fun k : ℕ => (A + k : ℝ)) N), ‖g'' t‖ :=
      intervalIntegral.sum_integral_adjacent_intervals fun k _ => hint_ng'' k
    simp only [Nat.cast_zero, add_zero] at hadj hadj''
    have hdecomp : (∑ n ∈ Finset.range N, g (A + n))
        + (2⁻¹ : ℝ) • g (A + (N : ℕ)) - (2⁻¹ : ℝ) • g A
        - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t
        = ∑ n ∈ Finset.range N,
            ((2⁻¹ : ℝ) • (g (A + n) + g (A + (n + 1 : ℕ)))
              - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t) := by
      rw [Finset.sum_sub_distrib, htrap N, hadj]
      simp only [Nat.cast_zero, add_zero]
    calc ‖(∑ n ∈ Finset.range N, g (A + n)) + (2⁻¹ : ℝ) • g (A + (N : ℕ))
          - (2⁻¹ : ℝ) • g A - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t‖
        = ‖∑ n ∈ Finset.range N,
            ((2⁻¹ : ℝ) • (g (A + n) + g (A + (n + 1 : ℕ)))
              - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t)‖ := by
          rw [hdecomp]
      _ ≤ ∑ n ∈ Finset.range N,
            ‖(2⁻¹ : ℝ) • (g (A + n) + g (A + (n + 1 : ℕ)))
              - ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), g t‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range N,
            8⁻¹ * ∫ t in (A + n : ℝ)..(A + (n + 1 : ℕ)), ‖g'' t‖ :=
          Finset.sum_le_sum fun n _ => hstep n
      _ = 8⁻¹ * ∫ t in (A : ℝ)..(A + (N : ℕ)), ‖g'' t‖ := by
          rw [← Finset.mul_sum, hadj'']
      _ ≤ 8⁻¹ * ∫ x in Set.Ioi A, ‖g'' x‖ := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          rw [intervalIntegral.integral_of_le hAN]
          apply setIntegral_mono_set hint''
          · filter_upwards with x using norm_nonneg _
          · exact Set.Ioc_subset_Ioi_self.eventuallyLE
  -- pass to the limit `N → ∞`
  have hlimS : Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, g (A + n))
      Filter.atTop (nhds (∑' n : ℕ, g (A + n))) := hsum.hasSum.tendsto_sum_nat
  have hlimE : Filter.Tendsto (fun N : ℕ => (2⁻¹ : ℝ) • g (A + (N : ℕ)))
      Filter.atTop (nhds ((2⁻¹ : ℝ) • (0 : E))) :=
    hsum.tendsto_atTop_zero.const_smul _
  have hlimI : Filter.Tendsto (fun N : ℕ => ∫ t in (A : ℝ)..(A + (N : ℕ)), g t)
      Filter.atTop (nhds (∫ x in Set.Ioi A, g x)) :=
    intervalIntegral_tendsto_integral_Ioi A hint
      (Filter.tendsto_atTop_add_const_left _ A tendsto_natCast_atTop_atTop)
  have hlim : Filter.Tendsto (fun N : ℕ =>
      ‖(∑ n ∈ Finset.range N, g (A + n)) + (2⁻¹ : ℝ) • g (A + (N : ℕ))
        - (2⁻¹ : ℝ) • g A - ∫ t in (A : ℝ)..(A + (N : ℕ)), g t‖)
      Filter.atTop
      (nhds ‖(∑' n : ℕ, g (A + n)) + (2⁻¹ : ℝ) • (0 : E)
        - (2⁻¹ : ℝ) • g A - ∫ x in Set.Ioi A, g x‖) :=
    (((hlimS.add hlimE).sub tendsto_const_nhds).sub hlimI).norm
  have h := le_of_tendsto' hlim hfin
  have he : (∑' n : ℕ, g (A + n)) + (2⁻¹ : ℝ) • (0 : E)
      - (2⁻¹ : ℝ) • g A - ∫ x in Set.Ioi A, g x
      = (∑' n : ℕ, g (A + n)) - (2⁻¹ : ℝ) • g A - ∫ x in Set.Ioi A, g x := by
    rw [smul_zero, add_zero]
  rwa [he] at h

end HalfLine

namespace DH

open Complex Finset

/-! ### The two-point mean-value bound at a generic exponent

`ZetaLean/DHTailBound.lean` proves this for exponents `−s` with `Re s > 0`;
the antiderivative needs exponent `1 − s` with `Re s < 1`, so the honest
hypothesis is `Re w ≤ 1`: the derivative norm `‖w‖·t^{Re w − 1}` is then
largest at the left endpoint. -/

/-- `‖b^w − a^w‖ ≤ ‖w‖·a^{Re w−1}·(b−a)` for `0 < a ≤ b` and `Re w ≤ 1`. -/
theorem norm_cpow_sub_cpow_le' {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {w : ℂ}
    (hw : w.re ≤ 1) :
    ‖(b : ℂ) ^ w - (a : ℂ) ^ w‖ ≤ ‖w‖ * a ^ (w.re - 1) * (b - a) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp [Complex.cpow_zero]
  · have hderiv : ∀ t ∈ Set.Icc a b,
        HasDerivWithinAt (fun y : ℝ => (y : ℂ) ^ w) (w * (t : ℂ) ^ (w - 1))
          (Set.Icc a b) t := fun t ht =>
      (hasDerivAt_ofReal_cpow_const (lt_of_lt_of_le ha ht.1).ne' hw0).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.Icc a b,
        ‖w * (t : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * a ^ (w.re - 1) := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        show (w - 1).re = w.re - 1 by simp]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)) (norm_nonneg w)
    have h := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv
      hbound (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ b - a)] at h

/-! ### The block as a function of a continuous variable

One definition serves every level: the block is `dhPair (−s)`, its
derivative is `5(−s)·dhPair (−s−1)`, its second derivative
`25s(s+1)·dhPair (−s−2)`, and its antiderivative `dhPair (1−s)/(5(1−s))`. -/

/-- The paired five-term block at exponent `w`:
`(5x+1)^w − (5x+4)^w + κ((5x+2)^w − (5x+3)^w)`.  The `j = 0` term is absent
because its DH coefficient is `0`. -/
noncomputable def dhPair (w : ℂ) (x : ℝ) : ℂ :=
  ((5 * x + 1 : ℝ) : ℂ) ^ w - ((5 * x + 4 : ℝ) : ℂ) ^ w
    + (dh_kappa : ℂ) * (((5 * x + 2 : ℝ) : ℂ) ^ w - ((5 * x + 3 : ℝ) : ℂ) ^ w)

/-- At natural arguments, `dhPair (−s)` *is* the DH block (the `j = 0` term
of `dhBlock` vanishes with its coefficient). -/
lemma dhPair_natCast (s : ℂ) (k : ℕ) : dhPair (-s) (k : ℝ) = dhBlock s k := by
  rw [dhBlock_eq_pair, dhPair]
  have h1 : ((5 * (k : ℝ) + 1 : ℝ) : ℂ) = ((k * 5 + 1 : ℕ) : ℂ) := by push_cast; ring
  have h2 : ((5 * (k : ℝ) + 2 : ℝ) : ℂ) = ((k * 5 + 2 : ℕ) : ℂ) := by push_cast; ring
  have h3 : ((5 * (k : ℝ) + 3 : ℝ) : ℂ) = ((k * 5 + 3 : ℕ) : ℂ) := by push_cast; ring
  have h4 : ((5 * (k : ℝ) + 4 : ℝ) : ℂ) = ((k * 5 + 4 : ℕ) : ℂ) := by push_cast; ring
  rw [h1, h2, h3, h4]

private lemma hasDerivAt_cpow5 {w : ℂ} (hw : w ≠ 0) {j : ℝ} {x : ℝ}
    (hx : 0 < 5 * x + j) :
    HasDerivAt (fun y : ℝ => ((5 * y + j : ℝ) : ℂ) ^ w)
      (5 * (w * ((5 * x + j : ℝ) : ℂ) ^ (w - 1))) x := by
  have houter : HasDerivAt (fun y : ℝ => (y : ℂ) ^ w)
      (w * ((5 * x + j : ℝ) : ℂ) ^ (w - 1)) (5 * x + j) :=
    hasDerivAt_ofReal_cpow_const hx.ne' hw
  have hinner : HasDerivAt (fun y : ℝ => 5 * y + j) 5 x := by
    simpa using ((hasDerivAt_id x).const_mul (5 : ℝ)).add_const j
  have h := HasDerivAt.scomp (𝕜 := ℝ) x houter hinner
  simpa [Function.comp_def, Complex.real_smul] using h

/-- Differentiation lowers the exponent: `d/dx dhPair w = 5w · dhPair (w−1)`.
One lemma serves the block, both its derivatives, and the antiderivative. -/
theorem hasDerivAt_dhPair (w : ℂ) (hw : w ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (dhPair w) (5 * w * dhPair (w - 1) x) x := by
  have h1 := hasDerivAt_cpow5 hw (j := 1) (x := x) (by linarith)
  have h2 := hasDerivAt_cpow5 hw (j := 2) (x := x) (by linarith)
  have h3 := hasDerivAt_cpow5 hw (j := 3) (x := x) (by linarith)
  have h4 := hasDerivAt_cpow5 hw (j := 4) (x := x) (by linarith)
  have h := (h1.sub h4).add ((h2.sub h3).const_mul (dh_kappa : ℂ))
  have he : 5 * (w * ((5 * x + 1 : ℝ) : ℂ) ^ (w - 1))
        - 5 * (w * ((5 * x + 4 : ℝ) : ℂ) ^ (w - 1))
      + (dh_kappa : ℂ) * (5 * (w * ((5 * x + 2 : ℝ) : ℂ) ^ (w - 1))
        - 5 * (w * ((5 * x + 3 : ℝ) : ℂ) ^ (w - 1)))
      = 5 * w * dhPair (w - 1) x := by
    rw [dhPair]
    ring
  rw [he] at h
  exact h

/-- The mean-value bound at every level at once:
`‖dhPair w x‖ ≤ (3+κ)·‖w‖·(5x+1)^{Re w − 1}` for `Re w ≤ 1`, `x ≥ 0`. -/
theorem norm_dhPair_le {w : ℂ} (hw : w.re ≤ 1) {x : ℝ} (hx : 0 ≤ x) :
    ‖dhPair w x‖ ≤ (3 + dh_kappa) * ‖w‖ * (5 * x + 1) ^ (w.re - 1) := by
  have hb1 : (0 : ℝ) < 5 * x + 1 := by linarith
  have hb2 : (0 : ℝ) < 5 * x + 2 := by linarith
  have hpair1 : ‖((5 * x + 1 : ℝ) : ℂ) ^ w - ((5 * x + 4 : ℝ) : ℂ) ^ w‖
      ≤ ‖w‖ * (5 * x + 1) ^ (w.re - 1) * 3 := by
    rw [norm_sub_rev]
    have h := norm_cpow_sub_cpow_le' hb1 (by linarith : 5 * x + 1 ≤ 5 * x + 4) hw
    refine h.trans (le_of_eq ?_)
    ring
  have hpair2 : ‖((5 * x + 2 : ℝ) : ℂ) ^ w - ((5 * x + 3 : ℝ) : ℂ) ^ w‖
      ≤ ‖w‖ * (5 * x + 1) ^ (w.re - 1) := by
    rw [norm_sub_rev]
    have h := norm_cpow_sub_cpow_le' hb2 (by linarith : 5 * x + 2 ≤ 5 * x + 3) hw
    have he : ‖w‖ * (5 * x + 2) ^ (w.re - 1) * (5 * x + 3 - (5 * x + 2))
        = ‖w‖ * (5 * x + 2) ^ (w.re - 1) := by ring
    rw [he] at h
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hb1 (by linarith) (by linarith)) (norm_nonneg w)
  calc ‖dhPair w x‖
      ≤ ‖((5 * x + 1 : ℝ) : ℂ) ^ w - ((5 * x + 4 : ℝ) : ℂ) ^ w‖
        + ‖(dh_kappa : ℂ) * (((5 * x + 2 : ℝ) : ℂ) ^ w - ((5 * x + 3 : ℝ) : ℂ) ^ w)‖ := by
        rw [dhPair]; exact norm_add_le _ _
    _ ≤ ‖w‖ * (5 * x + 1) ^ (w.re - 1) * 3
        + dh_kappa * (‖w‖ * (5 * x + 1) ^ (w.re - 1)) := by
        refine add_le_add hpair1 ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg dh_kappa_nonneg]
        exact mul_le_mul_of_nonneg_left hpair2 dh_kappa_nonneg
    _ = (3 + dh_kappa) * ‖w‖ * (5 * x + 1) ^ (w.re - 1) := by ring

private lemma continuousOn_dhPair (w : ℂ) (hw : w ≠ 0) :
    ContinuousOn (dhPair w) (Set.Ici (0 : ℝ)) := fun _x hx =>
  ((hasDerivAt_dhPair w hw hx).continuousAt).continuousWithinAt

/-- `dhPair w` vanishes at `+∞` whenever `Re w < 1`, even though for
`0 < Re w < 1` each of its four summands diverges: the paired differences
cancel the growth.  This is what makes the closed-form antiderivative
usable. -/
private lemma tendsto_dhPair_atTop {w : ℂ} (hw : w.re < 1) :
    Filter.Tendsto (dhPair w) Filter.atTop (nhds 0) := by
  have h5 : Filter.Tendsto (fun x : ℝ => 5 * x + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1
      (Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id)
  have hrpow : Filter.Tendsto (fun x : ℝ => (5 * x + 1) ^ (w.re - 1))
      Filter.atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < -(w.re - 1))).comp h5
    have he : ∀ x : ℝ, (5 * x + 1) ^ (-(-(w.re - 1))) = (5 * x + 1) ^ (w.re - 1) := by
      intro x; rw [neg_neg]
    simpa [Function.comp_def, he] using h
  have hb : Filter.Tendsto (fun x : ℝ => (3 + dh_kappa) * ‖w‖ * (5 * x + 1) ^ (w.re - 1))
      Filter.atTop (nhds 0) := by
    have h := hrpow.const_mul ((3 + dh_kappa) * ‖w‖)
    simpa using h
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  exact norm_dhPair_le hw.le hx

/-! ### Integrability and the closed-form half-line integrals -/

private lemma continuousOn_rpow_shift (c : ℝ) {A : ℝ} (hA : 0 < A) :
    ContinuousOn (fun x : ℝ => (5 * x + 1) ^ c) (Set.Ici A) := by
  intro x hx
  have hAx : A ≤ x := hx
  have h5 : (0 : ℝ) < 5 * x + 1 := by linarith
  have haff : ContinuousAt (fun x : ℝ => 5 * x + 1) x := by fun_prop
  exact (haff.rpow_const (Or.inl h5.ne')).continuousWithinAt

private lemma integrableOn_rpow_shift {c : ℝ} (hc : c < -1) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (fun x : ℝ => (5 * x + 1) ^ c) (Set.Ioi A) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => (5 * x + 1) ^ c)
      (volume.restrict (Set.Ioi A)) :=
    ((continuousOn_rpow_shift c hA).mono Set.Ioi_subset_Ici_self).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' (integrableOn_Ioi_rpow_of_lt hc hA) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
  intro x hx
  have hx0 : (0 : ℝ) < x := lt_trans hA hx
  have h5 : (0 : ℝ) < 5 * x + 1 := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h5.le c)]
  exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith)

/-- `∫_A^∞ (5x+1)^c dx = (5A+1)^{c+1}/(5(−c−1))` for `c < −1`, `A > 0`. -/
private lemma integral_Ioi_rpow_shift {c : ℝ} (hc : c < -1) {A : ℝ} (hA : 0 < A) :
    ∫ x in Set.Ioi A, (5 * x + 1) ^ c = (5 * A + 1) ^ (c + 1) / (5 * (-c - 1)) := by
  have hc1 : c + 1 ≠ 0 := by intro h; rw [show c = -1 by linarith] at hc; linarith
  have hderiv : ∀ x ∈ Set.Ici A,
      HasDerivAt (fun y : ℝ => (5 * y + 1) ^ (c + 1) / (5 * (c + 1)))
        ((5 * x + 1) ^ c) x := by
    intro x hx
    have hAx : A ≤ x := hx
    have h5 : (0 : ℝ) < 5 * x + 1 := by linarith
    have houter : HasDerivAt (fun y : ℝ => y ^ (c + 1))
        ((c + 1) * (5 * x + 1) ^ (c + 1 - 1)) (5 * x + 1) :=
      Real.hasDerivAt_rpow_const (Or.inl h5.ne')
    have hinner : HasDerivAt (fun y : ℝ => 5 * y + 1) 5 x := by
      simpa using ((hasDerivAt_id x).const_mul (5 : ℝ)).add_const (1 : ℝ)
    have h := (houter.comp x hinner).div_const (5 * (c + 1))
    have he : (c + 1) * (5 * x + 1) ^ (c + 1 - 1) * 5 / (5 * (c + 1))
        = (5 * x + 1) ^ c := by
      rw [show c + 1 - 1 = c by ring]
      field_simp
    rw [he] at h
    exact h
  have htend : Filter.Tendsto (fun y : ℝ => (5 * y + 1) ^ (c + 1) / (5 * (c + 1)))
      Filter.atTop (nhds 0) := by
    have h5 : Filter.Tendsto (fun x : ℝ => 5 * x + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1
        (Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id)
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < -(c + 1))).comp h5
    have he : ∀ x : ℝ, (5 * x + 1) ^ (-(-(c + 1))) = (5 * x + 1) ^ (c + 1) := by
      intro x; rw [neg_neg]
    have h2 : Filter.Tendsto (fun x : ℝ => (5 * x + 1) ^ (c + 1))
        Filter.atTop (nhds 0) := by
      simpa [Function.comp_def, he] using h
    simpa using h2.div_const (5 * (c + 1))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_rpow_shift hc hA) htend
  rw [h, zero_sub]
  have hc2 : -c - 1 ≠ 0 := by intro h'; rw [show c = -1 by linarith] at hc; linarith
  field_simp
  ring

private lemma integrableOn_dhPair {w : ℂ} (hw : w ≠ 0) (hwre : w.re < 0)
    {A : ℝ} (hA : 0 < A) : IntegrableOn (dhPair w) (Set.Ioi A) := by
  have hsub : Set.Ioi A ⊆ Set.Ici (0 : ℝ) := fun x hx => le_of_lt (lt_trans hA hx)
  have hmeas : AEStronglyMeasurable (dhPair w) (volume.restrict (Set.Ioi A)) :=
    ((continuousOn_dhPair w hw).mono hsub).aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono'
    (g := fun x : ℝ => ((3 + dh_kappa) * ‖w‖) * x ^ (w.re - 1)) ?_ hmeas ?_
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith) hA).const_mul _
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_trans hA hx
    refine (norm_dhPair_le (by linarith) hx0.le).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by linarith))
      (mul_nonneg (by linarith [dh_kappa_nonneg]) (norm_nonneg w))

/-- The closed-form antiderivative of the block:
`dhAnti s x = dhPair (1−s) x / (5(1−s))`, with `d/dx dhAnti = dhPair (−s)`
and `dhAnti → 0` at `+∞`.  The tail integral of the block is `−dhAnti K`,
computable by the interval machinery as four extra certified cpow values. -/
noncomputable def dhAnti (s : ℂ) (x : ℝ) : ℂ := dhPair (1 - s) x / (5 * (1 - s))

/-- `∫_A^∞ dhPair (−s) = −dhAnti A`: the fundamental theorem of calculus on
the half-line, valid for `0 < Re s`, `s ≠ 1`, `A > 0`. -/
theorem integral_Ioi_dhPair {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {A : ℝ}
    (hA : 0 < A) :
    ∫ x in Set.Ioi A, dhPair (-s) x = -dhAnti s A := by
  have h1s : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hsne : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr fun h => by simp [h] at hs
  have hsre : (-s : ℂ).re < 0 := by simpa using hs
  have hderiv : ∀ x ∈ Set.Ici A,
      HasDerivAt (fun y => dhPair (1 - s) y / (5 * (1 - s))) (dhPair (-s) x) x := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_trans hA.le hx
    have h := (hasDerivAt_dhPair (1 - s) h1s hx0).div_const (5 * (1 - s))
    have he : 5 * (1 - s) * dhPair (1 - s - 1) x / (5 * (1 - s)) = dhPair (-s) x := by
      rw [show (1 - s - 1 : ℂ) = -s by ring]
      field_simp
    rw [he] at h
    exact h
  have htend : Filter.Tendsto (fun y => dhPair (1 - s) y / (5 * (1 - s)))
      Filter.atTop (nhds 0) := by
    have h0 := tendsto_dhPair_atTop (w := 1 - s) (by simp; linarith)
    simpa using h0.div_const (5 * (1 - s))
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (integrableOn_dhPair hsne hsre hA) htend
  rw [h, dhAnti, zero_sub]

/-! ### The steeper tail bounds -/

private lemma norm_neg_sub_one (s : ℂ) : ‖(-s - 1 : ℂ)‖ = ‖s + 1‖ := by
  rw [show (-s - 1 : ℂ) = -(s + 1) by ring, norm_neg]

private lemma norm_neg_sub_two (s : ℂ) : ‖(-s - 2 : ℂ)‖ = ‖s + 2‖ := by
  rw [show (-s - 2 : ℂ) = -(s + 2) by ring, norm_neg]

private lemma re_neg_sub_one (s : ℂ) : (-s - 1 : ℂ).re = -s.re - 1 := by simp

private lemma re_neg_sub_two (s : ℂ) : (-s - 2 : ℂ).re = -s.re - 2 := by simp

/-- **The order-1 tail bound**, one power of `K` steeper than
`DH_tail_bound`.  Subtracting the closed-form integral `dhAnti K` from the
`5K`-term partial sum leaves an error controlled by `∫‖B'‖`:
for `Re s > 0`, `s ≠ 1`, `K ≥ 1`,
`‖DH s − (Σ_{n<5K} − dhAnti K)‖ ≤ (3+κ)‖s‖‖s+1‖(5K+1)^{-σ-1}/(σ+1)`. -/
theorem DH_tail_bound_order1 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {K : ℕ}
    (hK : 1 ≤ K) :
    ‖DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
        - dhAnti s (K : ℝ))‖
      ≤ (3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * (5 * (K : ℝ) + 1) ^ (-s.re - 1)
        / (s.re + 1) := by
  have hA : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hK
  have hsub0 : Set.Ici (K : ℝ) ⊆ Set.Ici (0 : ℝ) := Set.Ici_subset_Ici.mpr hA.le
  have hsne : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr fun h => by simp [h] at hs
  have h1ne : (-s - 1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h1re : (-s - 1 : ℂ).re < 0 := by simp; linarith
  have hkn : (0 : ℝ) ≤ 3 + dh_kappa := by linarith [dh_kappa_nonneg]
  -- hypotheses of the generic summed rectangle rule
  have hderiv : ∀ x ∈ Set.Ici (K : ℝ),
      HasDerivAt (dhPair (-s)) ((fun x => 5 * -s * dhPair (-s - 1) x) x) x :=
    fun x hx => hasDerivAt_dhPair (-s) hsne (le_trans hA.le hx)
  have hcont' : ContinuousOn (fun x => 5 * -s * dhPair (-s - 1) x)
      (Set.Ici (K : ℝ)) :=
    continuousOn_const.mul ((continuousOn_dhPair _ h1ne).mono hsub0)
  have hsum : Summable fun n : ℕ => dhPair (-s) ((K : ℝ) + n) := by
    refine ((summable_nat_add_iff K).mpr (summable_dhBlock hs)).congr fun n => ?_
    rw [show ((K : ℝ) + (n : ℝ)) = ((n + K : ℕ) : ℝ) by push_cast; ring, dhPair_natCast]
  have hint : IntegrableOn (dhPair (-s)) (Set.Ioi (K : ℝ)) :=
    integrableOn_dhPair hsne (by simpa using hs) hA
  have hnorm_c1 : ∀ x : ℝ, ‖5 * -s * dhPair (-s - 1) x‖
      = 5 * ‖s‖ * ‖dhPair (-s - 1) x‖ := by
    intro x
    rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_neg]
  have hint' : IntegrableOn (fun x => ‖5 * -s * dhPair (-s - 1) x‖)
      (Set.Ioi (K : ℝ)) := by
    have h := ((integrableOn_dhPair h1ne h1re hA).norm.const_mul (5 * ‖s‖))
    refine Integrable.congr h ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x _ => ?_))
    exact (hnorm_c1 x).symm
  have hmain := norm_tsum_sub_integral_le hderiv hcont' hsum hint hint'
  -- identify the left-hand side with the DH tail defect
  have htsum : (∑' n : ℕ, dhPair (-s) ((K : ℝ) + n)) = ∑' k, dhBlock s (k + K) :=
    tsum_congr fun n => by
      rw [show ((K : ℝ) + (n : ℝ)) = ((n + K : ℕ) : ℝ) by push_cast; ring,
        dhPair_natCast]
  have hLHS : DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
      - dhAnti s (K : ℝ))
      = (∑' n : ℕ, dhPair (-s) ((K : ℝ) + n))
        - ∫ x in Set.Ioi (K : ℝ), dhPair (-s) x := by
    rw [integral_Ioi_dhPair hs hs1 hA, sub_neg_eq_add, htsum,
      ← DH_sub_partial_eq_tsum hs K]
    ring
  -- bound the derivative integral in closed form
  have hIb : ∫ x in Set.Ioi (K : ℝ), ‖5 * -s * dhPair (-s - 1) x‖
      ≤ 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖)
        * ((5 * (K : ℝ) + 1) ^ (-s.re - 1) / (5 * (s.re + 1))) := by
    have hpt : ∀ x ∈ Set.Ioi (K : ℝ), ‖5 * -s * dhPair (-s - 1) x‖
        ≤ 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖) * (5 * x + 1) ^ (-s.re - 2) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans hA hx)
      have h := norm_dhPair_le (w := -s - 1) (by rw [re_neg_sub_one]; linarith) hx0
      rw [norm_neg_sub_one, re_neg_sub_one,
        show -s.re - 1 - 1 = -s.re - 2 by ring] at h
      calc ‖5 * -s * dhPair (-s - 1) x‖
          = 5 * ‖s‖ * ‖dhPair (-s - 1) x‖ := hnorm_c1 x
        _ ≤ 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖ * (5 * x + 1) ^ (-s.re - 2)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖) * (5 * x + 1) ^ (-s.re - 2) := by
            ring
    calc ∫ x in Set.Ioi (K : ℝ), ‖5 * -s * dhPair (-s - 1) x‖
        ≤ ∫ x in Set.Ioi (K : ℝ),
            5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖) * (5 * x + 1) ^ (-s.re - 2) := by
          refine setIntegral_mono_on hint'
            ((integrableOn_rpow_shift (by linarith) hA).const_mul _)
            measurableSet_Ioi hpt
      _ = 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖)
            * ∫ x in Set.Ioi (K : ℝ), (5 * x + 1) ^ (-s.re - 2) :=
          integral_const_mul _ _
      _ = 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖)
            * ((5 * (K : ℝ) + 1) ^ (-s.re - 1) / (5 * (s.re + 1))) := by
          rw [integral_Ioi_rpow_shift (by linarith) hA,
            show (-s.re - 2 + 1 : ℝ) = -s.re - 1 by ring,
            show (-(-s.re - 2) - 1 : ℝ) = s.re + 1 by ring]
  calc ‖DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
        - dhAnti s (K : ℝ))‖
      = ‖(∑' n : ℕ, dhPair (-s) ((K : ℝ) + n))
          - ∫ x in Set.Ioi (K : ℝ), dhPair (-s) x‖ := by rw [hLHS]
    _ ≤ ∫ x in Set.Ioi (K : ℝ), ‖5 * -s * dhPair (-s - 1) x‖ := hmain
    _ ≤ 5 * ‖s‖ * ((3 + dh_kappa) * ‖s + 1‖)
          * ((5 * (K : ℝ) + 1) ^ (-s.re - 1) / (5 * (s.re + 1))) := hIb
    _ = (3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * (5 * (K : ℝ) + 1) ^ (-s.re - 1)
          / (s.re + 1) := by
        have hp : s.re + 1 ≠ 0 := ne_of_gt (by linarith)
        field_simp

/-- **The order-2 tail bound**, two powers of `K` steeper than
`DH_tail_bound`.  The trapezoid's endpoint correction `+ dhBlock K / 2`
joins the integral correction `− dhAnti K`:
for `Re s > 0`, `s ≠ 1`, `K ≥ 1`,
`‖DH s − (Σ_{n<5K} + B(K)/2 − dhAnti K)‖
   ≤ (5/8)·(3+κ)‖s‖‖s+1‖‖s+2‖·(5K+1)^{-σ-2}/(σ+2)`.
At the oracle point this reaches 1e-3 with `K = 254` instead of the
`K ≈ 205000` that `DH_tail_bound` needs. -/
theorem DH_tail_bound_order2 {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {K : ℕ}
    (hK : 1 ≤ K) :
    ‖DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
        + dhBlock s K / 2 - dhAnti s (K : ℝ))‖
      ≤ 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
        * (5 * (K : ℝ) + 1) ^ (-s.re - 2) / (s.re + 2) := by
  have hA : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hK
  have hsub0 : Set.Ici (K : ℝ) ⊆ Set.Ici (0 : ℝ) := Set.Ici_subset_Ici.mpr hA.le
  have hsne : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr fun h => by simp [h] at hs
  have h1ne : (-s - 1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2ne : (-s - 2 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2re : (-s - 2 : ℂ).re < 0 := by simp; linarith
  -- hypotheses of the generic summed trapezoid rule
  have hderiv : ∀ x ∈ Set.Ici (K : ℝ),
      HasDerivAt (dhPair (-s)) ((fun x => 5 * -s * dhPair (-s - 1) x) x) x :=
    fun x hx => hasDerivAt_dhPair (-s) hsne (le_trans hA.le hx)
  have hderiv' : ∀ x ∈ Set.Ici (K : ℝ),
      HasDerivAt (fun x => 5 * -s * dhPair (-s - 1) x)
        ((fun x => 5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)) x) x := by
    intro x hx
    have h := (hasDerivAt_dhPair (-s - 1) h1ne (le_trans hA.le hx)).const_mul (5 * -s)
    rw [show (-s - 1 - 1 : ℂ) = -s - 2 by ring] at h
    exact h
  have hcont'' : ContinuousOn (fun x => 5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x))
      (Set.Ici (K : ℝ)) :=
    continuousOn_const.mul
      (continuousOn_const.mul ((continuousOn_dhPair _ h2ne).mono hsub0))
  have hsum : Summable fun n : ℕ => dhPair (-s) ((K : ℝ) + n) := by
    refine ((summable_nat_add_iff K).mpr (summable_dhBlock hs)).congr fun n => ?_
    rw [show ((K : ℝ) + (n : ℝ)) = ((n + K : ℕ) : ℝ) by push_cast; ring, dhPair_natCast]
  have hint : IntegrableOn (dhPair (-s)) (Set.Ioi (K : ℝ)) :=
    integrableOn_dhPair hsne (by simpa using hs) hA
  have hnorm_c : ∀ x : ℝ, ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖
      = 25 * ‖s‖ * ‖s + 1‖ * ‖dhPair (-s - 2) x‖ := by
    intro x
    simp only [norm_mul, Complex.norm_ofNat, norm_neg, norm_neg_sub_one]
    ring
  have hint'' : IntegrableOn (fun x => ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖)
      (Set.Ioi (K : ℝ)) := by
    have h := ((integrableOn_dhPair h2ne h2re hA).norm.const_mul (25 * ‖s‖ * ‖s + 1‖))
    refine Integrable.congr h ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Filter.Eventually.of_forall fun x _ => (hnorm_c x).symm))
  have hmain := norm_tsum_sub_integral_trapezoid_le hderiv hderiv' hcont''
    hsum hint hint''
  -- identify the left-hand side with the DH tail defect
  have htsum : (∑' n : ℕ, dhPair (-s) ((K : ℝ) + n)) = ∑' k, dhBlock s (k + K) :=
    tsum_congr fun n => by
      rw [show ((K : ℝ) + (n : ℝ)) = ((n + K : ℕ) : ℝ) by push_cast; ring,
        dhPair_natCast]
  have hhalf : (2⁻¹ : ℝ) • dhPair (-s) ((K : ℝ)) = dhBlock s K / 2 := by
    rw [dhPair_natCast, Complex.real_smul]
    push_cast
    ring
  have hLHS : DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
      + dhBlock s K / 2 - dhAnti s (K : ℝ))
      = (∑' n : ℕ, dhPair (-s) ((K : ℝ) + n)) - (2⁻¹ : ℝ) • dhPair (-s) ((K : ℝ))
        - ∫ x in Set.Ioi (K : ℝ), dhPair (-s) x := by
    rw [integral_Ioi_dhPair hs hs1 hA, sub_neg_eq_add, htsum, hhalf,
      ← DH_sub_partial_eq_tsum hs K]
    ring
  -- bound the second-derivative integral in closed form
  have hIb : ∫ x in Set.Ioi (K : ℝ), ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖
      ≤ 25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
        * ((5 * (K : ℝ) + 1) ^ (-s.re - 2) / (5 * (s.re + 2))) := by
    have hpt : ∀ x ∈ Set.Ioi (K : ℝ),
        ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖
        ≤ 25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
          * (5 * x + 1) ^ (-s.re - 3) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := le_of_lt (lt_trans hA hx)
      have h := norm_dhPair_le (w := -s - 2) (by rw [re_neg_sub_two]; linarith) hx0
      rw [norm_neg_sub_two, re_neg_sub_two,
        show -s.re - 2 - 1 = -s.re - 3 by ring] at h
      rw [hnorm_c x]
      calc 25 * ‖s‖ * ‖s + 1‖ * ‖dhPair (-s - 2) x‖
          ≤ 25 * ‖s‖ * ‖s + 1‖
            * ((3 + dh_kappa) * ‖s + 2‖ * (5 * x + 1) ^ (-s.re - 3)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
            * (5 * x + 1) ^ (-s.re - 3) := by ring
    calc ∫ x in Set.Ioi (K : ℝ), ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖
        ≤ ∫ x in Set.Ioi (K : ℝ),
            25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
              * (5 * x + 1) ^ (-s.re - 3) := by
          refine setIntegral_mono_on hint''
            ((integrableOn_rpow_shift (by linarith) hA).const_mul _)
            measurableSet_Ioi hpt
      _ = 25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
            * ∫ x in Set.Ioi (K : ℝ), (5 * x + 1) ^ (-s.re - 3) :=
          integral_const_mul _ _
      _ = 25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
            * ((5 * (K : ℝ) + 1) ^ (-s.re - 2) / (5 * (s.re + 2))) := by
          rw [integral_Ioi_rpow_shift (by linarith) hA,
            show (-s.re - 3 + 1 : ℝ) = -s.re - 2 by ring,
            show (-(-s.re - 3) - 1 : ℝ) = s.re + 2 by ring]
  calc ‖DH s - (∑ n ∈ range (K * 5), (dh_coeff n : ℂ) * (n : ℂ) ^ (-s)
        + dhBlock s K / 2 - dhAnti s (K : ℝ))‖
      = ‖(∑' n : ℕ, dhPair (-s) ((K : ℝ) + n))
          - (2⁻¹ : ℝ) • dhPair (-s) ((K : ℝ))
          - ∫ x in Set.Ioi (K : ℝ), dhPair (-s) x‖ := by rw [hLHS]
    _ ≤ 8⁻¹ * ∫ x in Set.Ioi (K : ℝ),
          ‖5 * -s * (5 * (-s - 1) * dhPair (-s - 2) x)‖ := hmain
    _ ≤ 8⁻¹ * (25 * ‖s‖ * ‖s + 1‖ * ((3 + dh_kappa) * ‖s + 2‖)
          * ((5 * (K : ℝ) + 1) ^ (-s.re - 2) / (5 * (s.re + 2)))) :=
        mul_le_mul_of_nonneg_left hIb (by norm_num)
    _ = 5 / 8 * ((3 + dh_kappa) * ‖s‖ * ‖s + 1‖ * ‖s + 2‖)
          * (5 * (K : ℝ) + 1) ^ (-s.re - 2) / (s.re + 2) := by
        have hp : s.re + 2 ≠ 0 := ne_of_gt (by linarith)
        field_simp
        ring

end DH

end ZetaLean
