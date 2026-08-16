/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import ZetaLean.Mertensstheorems

/-!
# Mertens's second theorem (hunt r_3c1cbb, Wikidata Q1196729)

Mertens's second theorem with an explicit constant, on top of the first
theorem proved in `ZetaLean.Mertensstheorems`:

* `mertens_second_theorem`: `|∑_{p ≤ N} 1/p − log log N| ≤ 16` for every
  natural `N` (the sum over primes `p ≤ N`; for `N ≤ 1` both sides are
  interpreted with Mathlib's `log 0 = 0` and the bound is trivial).

The proof is the classical partial summation against
`A(n) = ∑_{p ≤ n} log p / p = log n + O(1)`, where the `O(1)` band is
`mertens_first_theorem` (`|A(n) − log n| ≤ log 4 + 3`):

* `sum_inv_primes_eq` is the discrete Abel identity
  `∑_{p ≤ N} 1/p = A(N)/log N + ∑_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1))`,
  proved by induction from `N = 2`.
* The main-term sum `∑ log n (1/log n − 1/log(n+1))` is compared with
  `log log N` termwise through the bracket
  `(v−u)/v ≤ log v − log u ≤ (v−u)/u`, the gap being controlled by
  `∑ 1/n²` (Mathlib's `sum_Ioc_inv_sq_le_sub`).

The constant `16` is explicit and still not optimal (the classical bound
for the error is Mertens's own `≤ 4`): it inherits the `log 4 + 3` band
of the first theorem twice, through the factor `1/log 2 < 1.443`.  It
replaces the `76` this file first carried; that came from a `log 4 + 16`
band and from bounding `1/log 2` by `2`, and both of those were local
slack rather than anything the argument needed.  The residual `4`, from
`∑ 1/n²` against the quadratic gap in the logarithm bracket, is now the
largest single term that is not the Mertens band itself.
-/

namespace ZetaLean.Mertens

open Finset Real

/-! ## The elementary logarithm bracket -/

/-- Upper half of the bracket: `log v − log u ≤ (v − u)/u` for `0 < u ≤ v`. -/
theorem log_sub_log_le {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    log v - log u ≤ (v - u) / u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [← log_div hv.ne' hu.ne']
  calc log (v / u) ≤ v / u - 1 := log_le_sub_one_of_pos (by positivity)
    _ = (v - u) / u := by rw [sub_div, div_self hu.ne']

/-- Lower half of the bracket: `(v − u)/v ≤ log v − log u` for `0 < u ≤ v`. -/
theorem sub_div_le_log_sub_log {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (v - u) / v ≤ log v - log u := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [← log_div hv.ne' hu.ne']
  have h := one_sub_inv_le_log_of_pos (x := v / u) (by positivity)
  rw [show (v / u)⁻¹ = u / v by rw [inv_div]] at h
  calc (v - u) / v = 1 - u / v := by rw [sub_div, div_self hv.ne']
    _ ≤ log (v / u) := h

/-- The form the lower half takes after partial summation:
`x(x⁻¹ − y⁻¹) ≤ log y − log x` for `0 < x ≤ y`. -/
theorem mul_inv_sub_inv_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    x * (x⁻¹ - y⁻¹) ≤ log y - log x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hid : x * (x⁻¹ - y⁻¹) = (y - x) / y := by
    rw [mul_sub, mul_inv_cancel₀ hx.ne', sub_div, div_self hy.ne', div_eq_mul_inv]
  rw [hid]
  exact sub_div_le_log_sub_log hx hxy

/-- The form the upper half takes after partial summation, with the
quadratic gap made explicit: for `1/2 < x ≤ y` and `(y − x)² ≤ c`,
`log y − log x ≤ x(x⁻¹ − y⁻¹) + 4c`.  The factor `4` is `1/(xy) < 4`. -/
theorem log_sub_log_le_mul_add {x y c : ℝ} (hx : 1 / 2 < x) (hxy : x ≤ y)
    (hc : (y - x) ^ 2 ≤ c) :
    log y - log x ≤ x * (x⁻¹ - y⁻¹) + 4 * c := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hy2 : (1 : ℝ) / 2 < y := by linarith
  have hc0 : (0 : ℝ) ≤ c := le_trans (sq_nonneg _) hc
  have hxy0 : (0 : ℝ) < x * y := by positivity
  have hxy4 : (1 : ℝ) ≤ 4 * (x * y) := by nlinarith
  have hbr := log_sub_log_le hx0 hxy
  have hid : x * (x⁻¹ - y⁻¹) = 1 - x / y := by
    rw [mul_sub, mul_inv_cancel₀ hx0.ne', div_eq_mul_inv]
  have hid2 : (y - x) / y = 1 - x / y := by rw [sub_div, div_self hy0.ne']
  have hgap : (y - x) / x - (y - x) / y ≤ 4 * c := by
    have heq : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      rw [div_sub_div _ _ hx0.ne' hy0.ne',
        div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [heq, div_le_iff₀ hxy0]
    nlinarith [hc, hc0, hxy4]
  linarith [hbr, hgap, hid, hid2]

/-! ## Telescoping and the prime-filter split -/

/-- Telescoping over `Ico 2 N`. -/
theorem sum_Ico_telescope (g : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (g n - g (n + 1)) = g 2 - g N := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ M hM ih => rw [Finset.sum_Ico_succ_top hM, ih]; ring

/-- Splitting the top point off a prime-filtered sum. -/
theorem sum_filter_prime_succ (g : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ Ioc 0 (N + 1) with p.Prime, g p
      = (∑ p ∈ Ioc 0 N with p.Prime, g p)
        + if (N + 1).Prime then g (N + 1) else 0 := by
  rw [sum_filter, sum_filter, Finset.sum_Ioc_succ_top (Nat.zero_le N)]

/-! ## The Abel identity -/

/-- Discrete summation by parts specialised to the prime harmonic sum:
for `N ≥ 2`,
`∑_{p ≤ N} 1/p = A(N)/log N + ∑_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1))`
with `A(n) = ∑_{p ≤ n} log p / p`.  The proof is induction on `N`: the
increment of both sides at `N + 1` is `1/(N+1)` when `N + 1` is prime
(since `(log p / p) / log p = 1/p`) and `0` otherwise. -/
theorem sum_inv_primes_eq {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹
      = (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N
        + ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
            * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
  induction N, hN using Nat.le_induction with
  | base =>
    have h2 : (Ioc 0 2).filter Nat.Prime = {2} := by decide
    rw [h2]
    simp only [sum_singleton, Finset.Ico_self, sum_empty, add_zero]
    have hl2 : (0 : ℝ) < log ((2 : ℕ) : ℝ) := log_pos (by norm_num)
    rw [div_right_comm, div_self hl2.ne', one_div]
  | succ M hM ih =>
    have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hlogM : (0 : ℝ) < log (M : ℝ) := log_pos (by linarith)
    have hlogM1 : (0 : ℝ) < log ((M : ℝ) + 1) := log_pos (by linarith)
    have hM10 : ((M : ℝ) + 1) ≠ 0 := by positivity
    rw [sum_filter_prime_succ, sum_filter_prime_succ, Finset.sum_Ico_succ_top hM, ih]
    push_cast
    by_cases hp : (M + 1).Prime
    · simp only [hp, if_true]
      field_simp
      ring
    · simp only [hp, if_false]
      field_simp
      ring

/-! ## The `∑ 1/n²` control -/

/-- `∑_{n=2}^{N−1} 1/n² ≤ 1`, from Mathlib's partial-sum bound. -/
theorem sum_inv_sq_Ico_le_one {N : ℕ} (hN : 2 ≤ N) :
    ∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹ ≤ 1 := by
  have hsub : (Ico 2 N : Finset ℕ) ⊆ Ioc 1 N := fun x hx => by
    rw [mem_Ico] at hx
    rw [mem_Ioc]
    omega
  have h1 : ∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹ ≤ ∑ n ∈ Ioc 1 N, (((n : ℝ)) ^ 2)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity
  have h2 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 1) (n := N) one_ne_zero (by omega)
  have h3 : (0 : ℝ) ≤ ((N : ℝ))⁻¹ := by positivity
  push_cast at h2
  rw [inv_one] at h2
  linarith

/-! ## Mertens's second theorem -/

/-- Mertens's second theorem with the explicit constant `16`, for `N ≥ 2`:
`|∑_{p ≤ N} 1/p − log log N| ≤ 16`. -/
theorem mertens_second_theorem_of_two_le {N : ℕ} (hN : 2 ≤ N) :
    |(∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - log (log N)| ≤ 16 := by
  -- numeric groundwork
  have hlg : (0.6931471803 : ℝ) < log 2 := log_two_gt_d9
  have hll : log 2 < (0.6931471808 : ℝ) := log_two_lt_d9
  have hlog2 : (0 : ℝ) < log 2 := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : (0 : ℝ) < log (N : ℝ) := log_pos (by linarith)
  have hlog2N : log 2 ≤ log (N : ℝ) := log_le_log (by norm_num) hN2
  have hmul : log 2 * (log 2)⁻¹ = 1 := mul_inv_cancel₀ hlog2.ne'
  have hinvpos : (0 : ℝ) < (log 2)⁻¹ := by positivity
  have hinv2 : (log 2)⁻¹ < 1.443 := by nlinarith
  have hinvN0 : (0 : ℝ) ≤ (log (N : ℝ))⁻¹ := by positivity
  have hinvNle : (log (N : ℝ))⁻¹ ≤ (log 2)⁻¹ := inv_anti₀ hlog2 hlog2N
  have hinvN2 : (log (N : ℝ))⁻¹ < 1.443 := lt_of_le_of_lt hinvNle hinv2
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have h40 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
  have hc0 : (0 : ℝ) ≤ log 4 + 3 := by linarith
  have hc17 : log 4 + 3 ≤ (4.4 : ℝ) := by rw [hlog4]; linarith
  have hL2neg : log (log 2) < 0 := log_neg hlog2 (by linarith)
  have hL2gt : (-1 : ℝ) < log (log 2) := by
    have h := one_sub_inv_le_log_of_pos hlog2
    linarith
  -- the telescoped error band
  have hdN0 : (0 : ℝ) ≤ (log 2)⁻¹ - (log (N : ℝ))⁻¹ := by linarith
  have hdN2 : (log 2)⁻¹ - (log (N : ℝ))⁻¹ ≤ 1.443 := by linarith
  have hcd_ub : (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) ≤ 6.35 := by
    calc (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) ≤ 4.4 * 1.443 :=
          mul_le_mul hc17 hdN2 hdN0 (by norm_num)
      _ ≤ 6.35 := by norm_num
  have hcd_lb : (0 : ℝ) ≤ (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) :=
    mul_nonneg hc0 hdN0
  -- the boundary term `A(N)/log N ∈ 1 ± 6.35`
  have hAN := mertens_first_theorem (N := N) (by omega)
  obtain ⟨hANl, hANu⟩ := abs_le.mp hAN
  have hEq : (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1
      = ((∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N) * (log (N : ℝ))⁻¹ := by
    rw [sub_mul, mul_inv_cancel₀ hlogN.ne', div_eq_mul_inv]
  have hHead_ub : (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1 ≤ 6.35 := by
    rw [hEq]
    have h1 : ((∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N) * (log (N : ℝ))⁻¹
        ≤ (log 4 + 3) * (log (N : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right hANu hinvN0
    have h2 : (log 4 + 3) * (log (N : ℝ))⁻¹ ≤ 4.4 * 1.443 :=
      mul_le_mul hc17 hinvN2.le hinvN0 (by norm_num)
    linarith
  have hHead_lb : (-6.35 : ℝ) ≤ (∑ p ∈ Ioc 0 N with p.Prime, log p / p) / log N - 1 := by
    rw [hEq]
    have h1 : (-(log 4 + 3)) * (log (N : ℝ))⁻¹
        ≤ ((∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N) * (log (N : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right hANl hinvN0
    have h2 : (log 4 + 3) * (log (N : ℝ))⁻¹ ≤ 4.4 * 1.443 :=
      mul_le_mul hc17 hinvN2.le hinvN0 (by norm_num)
    linarith
  -- termwise upper bound on the Abel sum
  have hterm_ub : ∀ n ∈ Ico 2 N,
      (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ (log (log ((n : ℝ) + 1)) - log (log n))
          + (log 4 + 3) * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hx : (0 : ℝ) < log (n : ℝ) := log_pos (by linarith)
    have hxy : log (n : ℝ) ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
    have hd0 : (0 : ℝ) ≤ (log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹ := by
      have := inv_anti₀ hx hxy
      linarith
    have hup := mul_inv_sub_inv_le hx hxy
    have hA := mertens_first_theorem (N := n) (by omega)
    obtain ⟨-, hAu⟩ := abs_le.mp hA
    have h1 := mul_le_mul_of_nonneg_right hAu hd0
    linarith [h1, hup]
  -- termwise lower bound on the Abel sum
  have hterm_lb : ∀ n ∈ Ico 2 N,
      (log (log ((n : ℝ) + 1)) - log (log n)) - 4 * (((n : ℝ)) ^ 2)⁻¹
          - (log 4 + 3) * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
            * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    intro n hn
    rw [mem_Ico] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hninv0 : (0 : ℝ) ≤ ((n : ℝ))⁻¹ := by positivity
    have hx : (0 : ℝ) < log (n : ℝ) := log_pos (by linarith)
    have hxhalf : (1 : ℝ) / 2 < log (n : ℝ) := by
      have h := log_le_log (by norm_num : (0 : ℝ) < 2) hn2
      linarith [log_two_gt_d9]
    have hxy : log (n : ℝ) ≤ log ((n : ℝ) + 1) := log_le_log (by linarith) (by linarith)
    have hd0 : (0 : ℝ) ≤ (log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹ := by
      have := inv_anti₀ hx hxy
      linarith
    have hΔ : log ((n : ℝ) + 1) - log (n : ℝ) ≤ ((n : ℝ))⁻¹ := by
      have h := log_sub_log_le hn0 (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
      rw [add_sub_cancel_left, one_div] at h
      exact h
    have hΔ0 : (0 : ℝ) ≤ log ((n : ℝ) + 1) - log (n : ℝ) := by linarith
    have hsq : (log ((n : ℝ) + 1) - log (n : ℝ)) ^ 2 ≤ (((n : ℝ)) ^ 2)⁻¹ := by
      have h1 : (((n : ℝ))⁻¹) ^ 2 = (((n : ℝ)) ^ 2)⁻¹ := by rw [inv_pow]
      nlinarith [hΔ, hΔ0, hninv0, h1]
    have hlow := log_sub_log_le_mul_add hxhalf hxy hsq
    have hA := mertens_first_theorem (N := n) (by omega)
    obtain ⟨hAl, -⟩ := abs_le.mp hA
    have h1 := mul_le_mul_of_nonneg_right hAl hd0
    linarith [h1, hlow]
  -- the two telescoped sums
  have hLtel : ∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n))
      = log (log (N : ℝ)) - log (log 2) := by
    have h := sum_Ico_telescope (fun m => log (log (m : ℝ))) hN
    push_cast at h
    have h2 : ∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n))
        = -∑ n ∈ Ico 2 N, (log (log (n : ℝ)) - log (log ((n : ℝ) + 1))) := by
      rw [← Finset.sum_neg_distrib]
      exact sum_congr rfl fun n _ => by ring
    rw [h2, h]
    ring
  have hdtel : ∑ n ∈ Ico 2 N, ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹)
      = (log 2)⁻¹ - (log (N : ℝ))⁻¹ := by
    have h := sum_Ico_telescope (fun m => (log (m : ℝ))⁻¹) hN
    push_cast at h
    exact h
  -- assembled bounds on the Abel sum
  have hB_ub : ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
        * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
      ≤ (log (log (N : ℝ)) - log (log 2))
        + (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
    calc ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)
        ≤ ∑ n ∈ Ico 2 N, ((log (log ((n : ℝ) + 1)) - log (log n))
            + (log 4 + 3) * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹)) :=
          sum_le_sum hterm_ub
      _ = (∑ n ∈ Ico 2 N, (log (log ((n : ℝ) + 1)) - log (log n)))
          + (log 4 + 3)
            * ∑ n ∈ Ico 2 N, ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
          rw [sum_add_distrib, ← mul_sum]
      _ = (log (log (N : ℝ)) - log (log 2))
          + (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
          rw [hLtel, hdtel]
  have hsqsum := sum_inv_sq_Ico_le_one hN
  have hB_lb : (log (log (N : ℝ)) - log (log 2)) - 4
        - (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹)
      ≤ ∑ n ∈ Ico 2 N, (∑ p ∈ Ioc 0 n with p.Prime, log p / p)
          * ((log n)⁻¹ - (log ((n : ℝ) + 1))⁻¹) := by
    have hchain : ∑ n ∈ Ico 2 N, ((log (log ((n : ℝ) + 1)) - log (log n))
          - 4 * (((n : ℝ)) ^ 2)⁻¹
          - (log 4 + 3) * ((log (n : ℝ))⁻¹ - (log ((n : ℝ) + 1))⁻¹))
        = (log (log (N : ℝ)) - log (log 2))
          - 4 * (∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹)
          - (log 4 + 3) * ((log 2)⁻¹ - (log (N : ℝ))⁻¹) := by
      rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hLtel, hdtel]
    have hmono := sum_le_sum hterm_lb
    rw [hchain] at hmono
    have h4 : 4 * (∑ n ∈ Ico 2 N, (((n : ℝ)) ^ 2)⁻¹) ≤ 4 := by linarith
    linarith
  -- conclusion
  rw [sum_inv_primes_eq hN, abs_le]
  constructor
  · linarith [hHead_lb, hB_lb, hcd_ub, hL2neg]
  · linarith [hHead_ub, hB_ub, hcd_ub, hL2gt]

/-- **Mertens's second theorem**, prime-reciprocal form, with the explicit
constant `16`: for every natural `N`,
`|∑_{p ≤ N} 1/p − log log N| ≤ 16`.  The sum runs over primes `p ≤ N`.
For `N ≤ 1` the sum is empty and `log (log N) = 0` under Mathlib's
convention `log 0 = 0`, `log 1 = 0`, so the bound is trivial there. -/
theorem mertens_second_theorem (N : ℕ) :
    |(∑ p ∈ Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - log (log N)| ≤ 16 := by
  by_cases hN : 2 ≤ N
  · exact mertens_second_theorem_of_two_le hN
  · rw [not_le] at hN
    interval_cases N
    · norm_num
    · have hset : (Ioc 0 1 : Finset ℕ) = {1} := by
        ext x
        simp only [mem_Ioc, mem_singleton]
        omega
      rw [hset]
      simp [Finset.filter_singleton, Nat.not_prime_one]

end ZetaLean.Mertens
