/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib.NumberTheory.Chebyshev

/-!
# Mertens's theorems (hunt r_3c1cbb, Wikidata Q1196729)

Mertens's first theorem with explicit constants, in both the von Mangoldt
form and the prime form, against Mathlib v4.33.0-rc2, which carries no
Mertens statement of its own.

* `sum_log_eq_sum_vonMangoldt_mul_div`: the summatory identity
  `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`, from
  `ArithmeticFunction.vonMangoldt_sum` by counting multiples.
* `abs_sum_vonMangoldt_div_sub_log_le`: Mertens's first theorem, von
  Mangoldt form: `|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4` for `N ≥ 1`.
* `mertens_first_theorem`: Mertens's first theorem, prime form:
  `|∑_{p ≤ N} (log p)/p − log N| ≤ log 4 + 16` for `N ≥ 1`.

The constants are explicit and far from optimal (the true error in the
prime form is bounded by 2); they are what the elementary argument gives
without any numerical case analysis.

The upper Chebyshev input is Mathlib's `Chebyshev.psi_le_const_mul_self`
(`ψ x ≤ (log 4 + 4) x`).  The factorial bounds are replaced by an
induction using `log (1 + 1/M) ≤ 1/M`, so no integral comparison and no
Stirling estimate is needed anywhere in the file.  The prime-power
correction is controlled by `Chebyshev.sum_PrimePow_eq_sum_sum`, a
geometric tail in the exponent, and a telescoping bound for
`∑ n^(-3/2)`.
-/

namespace ZetaLean.Mertens

open Finset Real
open ArithmeticFunction hiding log id

/-! ## The summatory identity -/

/-- `∑_{n ≤ N} log n = ∑_{d ≤ N} Λ(d) ⌊N/d⌋`: sum `vonMangoldt_sum` over
`n ≤ N` and count multiples of each `d`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Ioc 0 N, log n = ∑ d ∈ Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h1 : ∀ n ∈ Ioc 0 N, log n = ∑ d ∈ Ioc 0 N with d ∣ n, Λ d := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [← vonMangoldt_sum]
    refine (sum_congr ?_ fun _ _ => rfl).symm
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hd0, _⟩, hd⟩
      exact ⟨hd, hn.1.ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn.1, (Nat.le_of_dvd hn.1 hd).trans hn.2⟩, hd⟩
  rw [sum_congr rfl h1]
  simp_rw [sum_filter]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun d hd => ?_
  rw [← sum_filter, sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

/-! ## Bounds on the log-factorial sum -/

/-- Upper bound `∑_{n ≤ N} log n ≤ N log N`, termwise. -/
theorem sum_log_le (N : ℕ) : ∑ n ∈ Ioc 0 N, log n ≤ (N : ℝ) * log N := by
  calc ∑ n ∈ Ioc 0 N, log n ≤ ∑ _n ∈ Ioc 0 N, log N := by
        refine sum_le_sum fun n hn => ?_
        rw [mem_Ioc] at hn
        exact log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    _ = (N : ℝ) * log N := by
        rw [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]

/-- Lower bound `N log N − N + 1 ≤ ∑_{n ≤ N} log n` for `N ≥ 1`, by
induction: the step needs only `M log(1 + 1/M) ≤ 1`, which is
`log x ≤ x − 1`.  This replaces the usual integral comparison. -/
theorem sum_log_ge (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * log N - N + 1 ≤ ∑ n ∈ Ioc 0 N, log n := by
  induction N with
  | zero => exact absurd hN (by norm_num)
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Nat.Ioc_succ_singleton, sum_singleton]
      norm_num
    · have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hMpos : (0 : ℝ) < (M : ℝ) := by linarith
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]
      have key : (M : ℝ) * (log (M + 1) - log M) ≤ 1 := by
        have hlog : log (((M : ℝ) + 1) / M) ≤ ((M : ℝ) + 1) / M - 1 :=
          log_le_sub_one_of_pos (by positivity)
        rw [log_div (by positivity) (by positivity)] at hlog
        have hfrac : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
        rw [hfrac] at hlog
        calc (M : ℝ) * (log (M + 1) - log M) ≤ (M : ℝ) * (1 / M) :=
              mul_le_mul_of_nonneg_left hlog (by linarith)
          _ = 1 := by field_simp
      have ihM := ih hM
      push_cast
      nlinarith [key, ihM]

/-! ## Mertens's first theorem, von Mangoldt form -/

/-- `Chebyshev.psi` at a natural argument is the plain finite sum. -/
theorem psi_natCast (N : ℕ) : Chebyshev.psi (N : ℝ) = ∑ n ∈ Ioc 0 N, Λ n := by
  rw [Chebyshev.psi, Nat.floor_natCast]

/-- Mertens's first theorem, von Mangoldt form, with the explicit
constant `log 4 + 4`: for `N ≥ 1`,
`|∑_{n ≤ N} Λ(n)/n − log N| ≤ log 4 + 4`. -/
theorem abs_sum_vonMangoldt_div_sub_log_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ d ∈ Ioc 0 N, Λ d / d) - log N| ≤ log 4 + 4 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- upper bound for T := ∑ log n in terms of S := ∑ Λ d / d
  have hTle : ∑ n ∈ Ioc 0 N, log n ≤ (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, mul_sum]
    refine sum_le_sum fun d hd => ?_
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    calc Λ d * ((N / d : ℕ) : ℝ) ≤ Λ d * ((N : ℝ) / d) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le vonMangoldt_nonneg
      _ = (N : ℝ) * (Λ d / d) := by ring
  -- lower bound: T ≥ N·S − ψ(N)
  have hTge : (N : ℝ) * (∑ d ∈ Ioc 0 N, Λ d / d) - Chebyshev.psi N
      ≤ ∑ n ∈ Ioc 0 N, log n := by
    rw [sum_log_eq_sum_vonMangoldt_mul_div, psi_natCast, mul_sum, ← sum_sub_distrib]
    refine sum_le_sum fun d hd => ?_
    rw [mem_Ioc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hfloor : (N : ℝ) / d - 1 < ((N / d : ℕ) : ℝ) := by
      have h := Nat.sub_one_lt_floor ((N : ℝ) / (d : ℝ))
      rwa [Nat.floor_div_natCast, Nat.floor_natCast] at h
    calc (N : ℝ) * (Λ d / d) - Λ d = Λ d * ((N : ℝ) / d - 1) := by ring
      _ ≤ Λ d * ((N / d : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hfloor.le vonMangoldt_nonneg
  have hpsi : Chebyshev.psi (N : ℝ) ≤ (log 4 + 4) * N :=
    Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hTub := sum_log_le N
  have hTlb := sum_log_ge N hN
  rw [abs_le]
  constructor
  · -- S ≥ log N − 1 ≥ log N − (log 4 + 4)
    have h1 : (N : ℝ) * (log N - 1) ≤ (N : ℝ) * ∑ d ∈ Ioc 0 N, Λ d / d := by
      nlinarith [hTle, hTlb]
    have h2 : log N - 1 ≤ ∑ d ∈ Ioc 0 N, Λ d / d :=
      le_of_mul_le_mul_left h1 hN0
    have h4 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
    linarith
  · -- S ≤ log N + (log 4 + 4)
    have h1 : (N : ℝ) * (∑ d ∈ Ioc 0 N, Λ d / d)
        ≤ (N : ℝ) * (log N + (log 4 + 4)) := by nlinarith [hTge, hTub, hpsi]
    have h2 := le_of_mul_le_mul_left h1 hN0
    linarith

/-! ## Elementary summation bounds for the prime-power correction -/

/-- Telescoping bound `∑_{n ≤ N} 1/(n √n) ≤ 3 − 2/√N` for `N ≥ 1`.  The
step is `1/((M+1)√(M+1)) ≤ 2/√M − 2/√(M+1)`. -/
theorem sum_inv_mul_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, ((n : ℝ) * √(n : ℝ))⁻¹ ≤ 3 - 2 / √(N : ℝ) := by
  induction N with
  | zero => exact absurd hN (by norm_num)
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      rw [Nat.Ioc_succ_singleton, sum_singleton]
      norm_num
    · have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have ihM := ih hM
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]
      have ha : (0 : ℝ) < √(M : ℝ) := sqrt_pos.mpr (by linarith)
      have hb : (0 : ℝ) < √((M : ℝ) + 1) := sqrt_pos.mpr (by linarith)
      have hab : √(M : ℝ) ≤ √((M : ℝ) + 1) := sqrt_le_sqrt (by linarith)
      have ha2 : √(M : ℝ) ^ 2 = (M : ℝ) := sq_sqrt (by linarith)
      have hb2 : √((M : ℝ) + 1) ^ 2 = (M : ℝ) + 1 := sq_sqrt (by linarith)
      have hdiff : (√((M : ℝ) + 1) - √(M : ℝ)) * (√((M : ℝ) + 1) + √(M : ℝ)) = 1 := by
        nlinarith [ha2, hb2]
      have hsum_pos : (0 : ℝ) < √((M : ℝ) + 1) + √(M : ℝ) := by positivity
      have hba_eq : √((M : ℝ) + 1) - √(M : ℝ)
          = 1 / (√((M : ℝ) + 1) + √(M : ℝ)) := by
        rw [eq_div_iff hsum_pos.ne']
        exact hdiff
      have key : (((M : ℕ) + 1 : ℝ) * √((M : ℝ) + 1))⁻¹
          ≤ 2 / √(M : ℝ) - 2 / √((M : ℝ) + 1) := by
        have h1 : 2 / √(M : ℝ) - 2 / √((M : ℝ) + 1)
            = 2 / ((√((M : ℝ) + 1) + √(M : ℝ)) * (√(M : ℝ) * √((M : ℝ) + 1))) := by
          rw [div_sub_div _ _ ha.ne' hb.ne',
            div_eq_div_iff (by positivity) (by positivity)]
          linear_combination (2 * (√(M : ℝ) * √((M : ℝ) + 1))) * hdiff
        rw [h1, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        -- (b+a)·a·b ≤ 2·(M+1)·b with b² = M+1, a ≤ b
        nlinarith [hb2, ha, hb,
          mul_nonneg (mul_nonneg hb.le hb.le) (sub_nonneg.mpr hab),
          mul_nonneg (mul_nonneg hb.le ha.le) (sub_nonneg.mpr hab),
          mul_nonneg (mul_nonneg hb.le hsum_pos.le) (sub_nonneg.mpr hab)]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      calc (∑ n ∈ Ioc 0 M, ((n : ℝ) * √(n : ℝ))⁻¹)
            + (((M + 1 : ℕ) : ℝ) * √((M + 1 : ℕ) : ℝ))⁻¹
          ≤ (3 - 2 / √(M : ℝ)) + (2 / √(M : ℝ) - 2 / √((M : ℝ) + 1)) := by
            rw [hcast]
            exact add_le_add ihM key
        _ = 3 - 2 / √(((M + 1 : ℕ) : ℝ)) := by rw [hcast]; ring

/-- `∑_{n ≤ N} (log n)/n² ≤ 6`, via `log n ≤ 2√n` and the telescoping
bound. -/
theorem sum_log_div_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 ≤ 6 := by
  have hstep : ∀ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 ≤ 2 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
    intro n hn
    rw [mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hs : (0 : ℝ) < √(n : ℝ) := sqrt_pos.mpr hn0
    have hss : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := mul_self_sqrt hn0.le
    have hlog : log n ≤ 2 * √(n : ℝ) := by
      have h1 : log ((n : ℝ)) = 2 * log (√(n : ℝ)) := by
        rw [log_sqrt hn0.le]; ring
      have h2 : log (√(n : ℝ)) ≤ √(n : ℝ) - 1 := log_le_sub_one_of_pos hs
      nlinarith [h1, h2]
    calc log n / (n : ℝ) ^ 2 ≤ 2 * √(n : ℝ) / (n : ℝ) ^ 2 := by
          gcongr
      _ = 2 * ((n : ℝ) * √(n : ℝ))⁻¹ := by
          rw [eq_comm, mul_comm 2 _, inv_mul_eq_div, div_eq_div_iff (by positivity) (by positivity)]
          nlinarith [hss]
  calc ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2
      ≤ ∑ n ∈ Ioc 0 N, 2 * ((n : ℝ) * √(n : ℝ))⁻¹ := sum_le_sum hstep
    _ = 2 * ∑ n ∈ Ioc 0 N, ((n : ℝ) * √(n : ℝ))⁻¹ := by rw [mul_sum]
    _ ≤ 2 * (3 - 2 / √(N : ℝ)) := by
        have := sum_inv_mul_sqrt_le N hN
        have hsN : (0 : ℝ) < √(N : ℝ) := sqrt_pos.mpr (by exact_mod_cast hN)
        nlinarith [this]
    _ ≤ 6 := by
        have hsN : (0 : ℝ) < √(N : ℝ) := sqrt_pos.mpr (by exact_mod_cast hN)
        have : 0 < 2 / √(N : ℝ) := by positivity
        linarith

/-- Geometric tail `∑_{k=2}^{K} 2⁻ᵏ ≤ 2⁻¹ − 2⁻ᴷ` for `K ≥ 1`. -/
theorem sum_geom_tail_le (K : ℕ) (hK : 1 ≤ K) :
    ∑ k ∈ Icc 2 K, ((2 : ℝ)⁻¹) ^ k ≤ 2⁻¹ - (2⁻¹ : ℝ) ^ K := by
  induction K, hK using Nat.le_induction with
  | base =>
    rw [show Icc 2 1 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by omega)]
    norm_num
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hpow : (0 : ℝ) < (2⁻¹ : ℝ) ^ M := by positivity
    have hstep : ((2 : ℝ)⁻¹) ^ (M + 1) = ((2 : ℝ)⁻¹) ^ M * 2⁻¹ := pow_succ _ _
    nlinarith [ih, hpow]

/-! ## Mertens's first theorem, prime form -/

/-- Mertens's first theorem with the explicit constant `log 4 + 16`:
for `N ≥ 1`, `|∑_{p ≤ N} (log p)/p − log N| ≤ log 4 + 16`.

The sum runs over primes `p ≤ N`.  The distance to the von Mangoldt form
is the prime-power correction `∑_{p^k ≤ N, k ≥ 2} (log p)/p^k`, which is
nonnegative and at most `12`. -/
theorem mertens_first_theorem {N : ℕ} (hN : 1 ≤ N) :
    |(∑ p ∈ Ioc 0 N with p.Prime, log p / p) - log N| ≤ log 4 + 16 := by
  have h4 : (0 : ℝ) ≤ log 4 := log_nonneg (by norm_num)
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · -- N = 1: both sums are empty or zero
    subst hN1
    have hset : (Ioc 0 1 : Finset ℕ) = {1} := by
      ext x
      simp only [mem_Ioc, mem_singleton]
      omega
    rw [hset]
    simp [Finset.filter_singleton, Nat.not_prime_one]
    linarith
  · have hN2 : 2 ≤ N := hN2
    have hN0 : (0 : ℝ) < N := by positivity
    have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    -- the von Mangoldt sum equals its restriction to prime powers
    have hfil : (∑ n ∈ Ioc 0 N with IsPrimePow n, Λ n / n) = ∑ d ∈ Ioc 0 N, Λ d / d := by
      refine sum_filter_of_ne fun n _ h => ?_
      have hΛ : Λ n ≠ 0 := by
        intro h0
        exact h (by rw [h0, zero_div])
      exact vonMangoldt_ne_zero_iff.mp hΛ
    -- decompose over exponents
    set K := ⌊log (N : ℝ) / log 2⌋₊ with hK
    have hK1 : 1 ≤ K := by
      rw [hK, Nat.one_le_floor_iff, le_div_iff₀ (log_pos (by norm_num)), one_mul]
      exact log_le_log (by norm_num) (by exact_mod_cast hN2)
    have hdec : (∑ n ∈ Ioc 0 N with IsPrimePow n, Λ n / n)
        = ∑ k ∈ Icc 1 K, ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
      have h := Chebyshev.sum_PrimePow_eq_sum_sum (R := ℝ)
        (fun n => Λ n / n) (Nat.cast_nonneg N)
      rw [Nat.floor_natCast] at h
      exact h
    -- the k = 1 layer is the prime sum
    have hone : (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (1 : ℕ))⌋₊ with p.Prime,
        Λ (p ^ 1) / ((p ^ 1 : ℕ) : ℝ))
        = ∑ p ∈ Ioc 0 N with p.Prime, log p / p := by
      rw [show ((1 : ℝ) / (1 : ℕ)) = 1 by norm_num, rpow_one, Nat.floor_natCast]
      refine sum_congr rfl fun p hp => ?_
      rw [mem_filter] at hp
      rw [pow_one, vonMangoldt_apply_prime hp.2]
    -- split off k = 1
    rw [← add_sum_Ioc_eq_sum_Icc hK1] at hdec
    rw [hone] at hdec
    -- the tail is nonnegative
    have htail_nonneg : (0 : ℝ) ≤ ∑ k ∈ Ioc 1 K,
        ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) := by
      refine sum_nonneg fun k _ => sum_nonneg fun p _ => ?_
      exact div_nonneg vonMangoldt_nonneg (by positivity)
    -- per-layer bound for k ≥ 2
    have hlayer : ∀ k ∈ Ioc 1 K,
        (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ))
        ≤ 4 * ((2 : ℝ)⁻¹) ^ k * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
      intro k hk
      rw [mem_Ioc] at hk
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 + j := ⟨k - 2, by omega⟩
      -- the inner index set sits inside Ioc 0 N
      have hsub : (Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊).filter Nat.Prime
          ⊆ Ioc 0 N := by
        refine (filter_subset _ _).trans (Finset.Ioc_subset_Ioc_right ?_)
        have hfle : (N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ)) ≤ (N : ℝ) :=
          rpow_le_self_of_one_le hN1R (by
            rw [div_le_one (by positivity)]
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega))
        calc ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ ≤ ⌊(N : ℝ)⌋₊ :=
              Nat.floor_le_floor hfle
          _ = N := Nat.floor_natCast N
      -- termwise: log p / p^(2+j) ≤ (log p / p²) (2⁻¹)^j
      have hterm : ∀ p ∈ (Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊).filter Nat.Prime,
          Λ (p ^ (2 + j)) / ((p ^ (2 + j) : ℕ) : ℝ)
          ≤ (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
        intro p hp
        rw [mem_filter] at hp
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
        have hΛ : Λ (p ^ (2 + j)) = log p := by
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp.2]
        have hcast : ((p ^ (2 + j) : ℕ) : ℝ) = (p : ℝ) ^ (2 + j) := by push_cast; rfl
        rw [hΛ, hcast]
        have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ j ≤ (p : ℝ) ^ (2 + j) := by
          rw [pow_add]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by norm_num) hp2 j) (by positivity)
        have hlogp : (0 : ℝ) ≤ log p := log_nonneg (by linarith)
        calc log p / (p : ℝ) ^ (2 + j) ≤ log p / ((p : ℝ) ^ 2 * (2 : ℝ) ^ j) := by
              gcongr
          _ = (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
              rw [inv_pow, ← div_div, div_eq_mul_inv]
      calc (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
            Λ (p ^ (2 + j)) / ((p ^ (2 + j) : ℕ) : ℝ))
          ≤ ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
              (log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := sum_le_sum hterm
        _ = (∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / (2 + j : ℕ))⌋₊ with p.Prime,
              log p / (p : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by rw [sum_mul]
        _ ≤ (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * ((2 : ℝ)⁻¹) ^ j := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            refine sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => ?_
            rw [mem_Ioc] at hn
            have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
            exact div_nonneg (log_nonneg this) (by positivity)
        _ = 4 * ((2 : ℝ)⁻¹) ^ (2 + j) * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
            rw [pow_add]
            ring_nf
    -- sum the layers: tail ≤ 2 B ≤ 12
    have hB := sum_log_div_sq_le N hN
    have hBnn : (0 : ℝ) ≤ ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 := by
      refine sum_nonneg fun n hn => ?_
      rw [mem_Ioc] at hn
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      exact div_nonneg (log_nonneg this) (by positivity)
    have htail_le : (∑ k ∈ Ioc 1 K,
        ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)) ≤ 12 := by
      have hIoc : (Ioc 1 K : Finset ℕ) = Icc 2 K := by
        ext x
        simp only [mem_Ioc, mem_Icc]
        omega
      calc (∑ k ∈ Ioc 1 K, ∑ p ∈ Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            Λ (p ^ k) / ((p ^ k : ℕ) : ℝ))
          ≤ ∑ k ∈ Ioc 1 K,
              4 * ((2 : ℝ)⁻¹) ^ k * ∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2 :=
            sum_le_sum hlayer
        _ = 4 * (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * ∑ k ∈ Ioc 1 K, ((2 : ℝ)⁻¹) ^ k := by
            rw [mul_sum]
            refine sum_congr rfl fun k _ => by ring
        _ ≤ 4 * (∑ n ∈ Ioc 0 N, log n / (n : ℝ) ^ 2) * (2 : ℝ)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [hIoc]
            have := sum_geom_tail_le K hK1
            have hpow : (0 : ℝ) < (2⁻¹ : ℝ) ^ K := by positivity
            linarith
        _ ≤ 4 * 6 * (2 : ℝ)⁻¹ := by
            have h6 : (0 : ℝ) < 6 := by norm_num
            nlinarith [hB, hBnn]
        _ = 12 := by norm_num
    -- assemble
    have hvM := abs_sum_vonMangoldt_div_sub_log_le hN
    rw [hfil] at hdec
    rw [abs_le] at hvM ⊢
    constructor
    · -- lower: prime sum ≥ Λ sum − 12 ≥ log N − (log 4 + 4) − 12
      nlinarith [hdec, htail_le, hvM.1]
    · -- upper: prime sum ≤ Λ sum ≤ log N + log 4 + 4
      nlinarith [hdec, htail_nonneg, hvM.2]

end ZetaLean.Mertens
