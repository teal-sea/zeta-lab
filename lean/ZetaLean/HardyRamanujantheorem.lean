/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib
import ZetaLean.MertensSecond

/-!
# The Hardy–Ramanujan theorem (hunt r_0339c1, Wikidata Q5656674)

The Hardy–Ramanujan theorem says that `ω n`, the number of distinct prime
factors of `n`, has normal order `log log n`: for every `ε > 0` the density of
the integers `n ≤ N` with `|ω n - loglog N| > ε * loglog N` tends to `0`.

This file proves it, by Turán's argument, with every constant explicit:

1. **First moment** (`sum_omega_eq_sum_div`, `first_moment_lower`,
   `first_moment_upper`): the double-counting identity
   `∑_{n ≤ N} ω n = ∑_{p ≤ N} ⌊N/p⌋` brackets the mean between
   `N·S(N) − N` and `N·S(N)`, where `S(N) = ∑_{p ≤ N} 1/p`.
2. **Second moment** (`card_dvd_pair`, `sum_omega_sq_eq`,
   `second_moment_upper`): expanding `ω(n)²` over ordered pairs of primes
   and counting multiples of `p*q` gives `∑_{n ≤ N} ω(n)² ≤ N·S(N)² + N·S(N)`.
3. **Mertens' second theorem** (`ZetaLean.Mertens.mertens_second_theorem`,
   proved in this repository on top of `mertens_first_theorem`):
   `|S(N) − loglog N| ≤ 16` for every `N`.
4. **Turán's variance bound** (`sum_sq_dev_le`, `turan_variance`): combining
   1–3, `∑_{n ≤ N} (ω n − loglog N)² ≤ 275 · N · loglog N` whenever
   `1 ≤ loglog N`, hence eventually; the constant `275` is `16² + 16 + 3`,
   where `16` is Mertens' band, and it moves quadratically with it.  It
   replaces the `5855 = 76² + 76 + 3` this file first carried: nothing in
   the variance argument changed, only the band it is fed.
5. **Chebyshev step** (`card_exceptional_mul_le`,
   `hardyRamanujan_of_turanVariance`): the variance bound forces the
   exceptional set below any positive density.

The final statement is `hardy_ramanujan : HardyRamanujanTheorem`.

The statement `HardyRamanujanTheorem`, the reduction
`hardyRamanujan_of_turanVariance`, and the identities
`primeFactors_eq_filter` and `sum_omega_eq_sum_div` are reused verbatim from
the first attempt on this hunt (run `16585a2a`, branch `hunt/r-0339c1`, same
author line), which proved the Chebyshev half and named Mertens' second
theorem as the missing input.  That input has since been built in
`ZetaLean.MertensSecond` (hunt r_3c1cbb); this file closes the remaining half.
-/

namespace ZetaLean.HardyRamanujan

open Finset Filter Topology

/-- `omega n` is the number of distinct prime factors of `n`, `ω` in the
literature.  It agrees with `ArithmeticFunction.cardDistinctFactors` by
definition; it is spelled out here so that no `ArithmeticFunction` coercion
sits between the combinatorics and the sums. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- The normalising function `log log N` of the theorem. -/
noncomputable def loglog (N : ℕ) : ℝ := Real.log (Real.log N)

/-- The integers `n ≤ N` whose prime-factor count deviates from `log log N` by
more than a fraction `ε` of it.  Hardy–Ramanujan says this set has density `0`. -/
noncomputable def exceptional (N : ℕ) (ε : ℝ) : Finset ℕ :=
  (Finset.Ioc 0 N).filter fun n => ε * loglog N < |(omega n : ℝ) - loglog N|

/-- **The Hardy–Ramanujan theorem**, as a proposition.  Proved below as
`hardy_ramanujan`. -/
def HardyRamanujanTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N : ℕ => ((exceptional N ε).card : ℝ) / (N : ℝ)) atTop (𝓝 0)

/-- **Turán's variance estimate**, as a proposition.  Proved below as
`turan_variance`, with the explicit constant `275`. -/
def TuranVariance : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Finset.Ioc 0 N, ((omega n : ℝ) - loglog N) ^ 2 ≤ C * (N : ℝ) * loglog N

/-! ### The unconditional double-counting identities -/

/-- For `0 < n ≤ N`, the prime factors of `n` are exactly the primes in `(0, N]`
that divide `n`. -/
theorem primeFactors_eq_filter {N n : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    n.primeFactors = (Finset.Ioc 0 N).filter fun p => p.Prime ∧ p ∣ n := by
  rw [Finset.mem_Ioc] at hn
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hp, hpd, -⟩
    exact ⟨⟨hp.pos, (Nat.le_of_dvd hn.1 hpd).trans hn.2⟩, hp, hpd⟩
  · rintro ⟨-, hp, hpd⟩
    exact ⟨hp, hpd, hn.1.ne'⟩

/-- For `0 < n ≤ N`, `ω n` counts the primes `p ≤ N` dividing `n`, as an
indicator sum over the primes in `(0, N]`. -/
theorem omega_eq_sum_ite {N n : ℕ} (hn : n ∈ Finset.Ioc 0 N) :
    omega n = ∑ p ∈ Finset.Ioc 0 N with p.Prime, if p ∣ n then 1 else 0 := by
  rw [omega, primeFactors_eq_filter hn, Finset.card_filter, Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ => by
    by_cases h1 : p.Prime <;> by_cases h2 : p ∣ n <;> simp [h1, h2]

/-- **Double counting**: `∑_{n ≤ N} ω n = ∑_{p ≤ N, p prime} ⌊N/p⌋`.

This is the first step of Turán's variance estimate, and it is unconditional.
The right-hand side is the point of contact with Mertens: `⌊N/p⌋ = N/p + O(1)`
turns it into `N ∑_{p ≤ N} 1/p + O(π N)`. -/
theorem sum_omega_eq_sum_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, omega n
      = ∑ p ∈ (Finset.Ioc 0 N).filter Nat.Prime, N / p := by
  have hL : ∑ n ∈ Finset.Ioc 0 N, omega n
      = ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ Finset.Ioc 0 N,
          if p.Prime ∧ p ∣ n then 1 else 0 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [omega, primeFactors_eq_filter hn, Finset.card_filter]
  rw [hL, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · rw [if_pos hp]
    simp only [hp, true_and]
    rw [← Finset.card_filter]
    exact Nat.Ioc_filter_dvd_card_eq_div N p
  · simp [hp]

/-- The pair count behind the second moment: for primes `p`, `q`, the number
of `n ∈ (0, N]` divisible by both is `⌊N/p⌋` on the diagonal and `⌊N/(pq)⌋`
off it (distinct primes are coprime, so joint divisibility is divisibility
by the product). -/
theorem card_dvd_pair {p q : ℕ} (N : ℕ) (hp : p.Prime) (hq : q.Prime) :
    ((Finset.Ioc 0 N).filter fun n => p ∣ n ∧ q ∣ n).card
      = if p = q then N / p else N / (p * q) := by
  rcases eq_or_ne p q with rfl | hpq
  · rw [if_pos rfl]
    simp only [and_self]
    exact Nat.Ioc_filter_dvd_card_eq_div N p
  · rw [if_neg hpq]
    have hco : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hiff : ∀ n ∈ Finset.Ioc 0 N, (p ∣ n ∧ q ∣ n) ↔ p * q ∣ n := by
      intro n _
      constructor
      · rintro ⟨h1, h2⟩
        exact hco.mul_dvd_of_dvd_of_dvd h1 h2
      · intro h
        exact ⟨(dvd_mul_right p q).trans h, (dvd_mul_left q p).trans h⟩
    rw [Finset.filter_congr hiff]
    exact Nat.Ioc_filter_dvd_card_eq_div N (p * q)

/-- **The second-moment expansion**: `∑_{n ≤ N} ω(n)²` is the number of triples
`(p, q, n)` with `p, q` prime and `p ∣ n`, `q ∣ n`, grouped by the pair. -/
theorem sum_omega_sq_eq (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, omega n ^ 2
      = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((Finset.Ioc 0 N).filter fun n => p ∣ n ∧ q ∣ n).card := by
  calc ∑ n ∈ Finset.Ioc 0 N, omega n ^ 2
      = ∑ n ∈ Finset.Ioc 0 N, ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((if p ∣ n then 1 else 0) * if q ∣ n then 1 else 0) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [sq, omega_eq_sum_ite hn, Finset.sum_mul_sum]
    _ = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ∑ n ∈ Finset.Ioc 0 N,
          ((if p ∣ n then 1 else 0) * if q ∣ n then 1 else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((Finset.Ioc 0 N).filter fun n => p ∣ n ∧ q ∣ n).card := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]

/-! ### Casting the floor divisions -/

/-- The lower half of the floor bracket, cast to `ℝ`: `N/p − 1 < ⌊N/p⌋`. -/
theorem sub_one_lt_cast_div {p : ℕ} (N : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 < ((N / p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h1 : N < p * (N / p) + p := by
    have hdm := Nat.div_add_mod N p
    have hm := Nat.mod_lt N hp
    omega
  have h2 : (N : ℝ) < (p : ℝ) * ((N / p : ℕ) : ℝ) + p := by exact_mod_cast h1
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hp0]
  nlinarith

/-- **First moment, upper**: `∑_{n ≤ N} ω n ≤ N · ∑_{p ≤ N} 1/p`. -/
theorem first_moment_upper (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, omega n : ℕ) : ℝ)
      ≤ (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
  rw [sum_omega_eq_sum_div, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
  rwa [div_eq_mul_inv] at h

/-- **First moment, lower**: `N · ∑_{p ≤ N} 1/p − N ≤ ∑_{n ≤ N} ω n`
(the loss is one unit per prime, and there are at most `N` primes in `(0, N]`). -/
theorem first_moment_lower (N : ℕ) :
    (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - N
      ≤ ((∑ n ∈ Finset.Ioc 0 N, omega n : ℕ) : ℝ) := by
  have hterm : ∀ p ∈ (Finset.Ioc 0 N).filter Nat.Prime,
      (N : ℝ) * (p : ℝ)⁻¹ - 1 ≤ ((N / p : ℕ) : ℝ) := by
    intro p hp
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have h := sub_one_lt_cast_div N hpp.pos
    rw [div_eq_mul_inv] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
    mul_one] at hsum
  have hcard : ((((Finset.Ioc 0 N).filter Nat.Prime).card : ℕ) : ℝ) ≤ N := by
    have h1 := Finset.card_filter_le (Finset.Ioc 0 N) Nat.Prime
    have h2 : (Finset.Ioc 0 N).card = N := by rw [Nat.card_Ioc, Nat.sub_zero]
    exact_mod_cast h1.trans_eq h2
  rw [sum_omega_eq_sum_div, Nat.cast_sum]
  linarith

/-- **Second moment, upper**: `∑_{n ≤ N} ω(n)² ≤ N·S² + N·S` with
`S = ∑_{p ≤ N} 1/p`.  The off-diagonal pairs are dominated by the full square
`N·S²`, the diagonal by `N·S`. -/
theorem second_moment_upper (N : ℕ) :
    ((∑ n ∈ Finset.Ioc 0 N, omega n ^ 2 : ℕ) : ℝ)
      ≤ (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2
        + (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
  have hpair : ∀ p ∈ (Finset.Ioc 0 N).filter Nat.Prime,
      ∀ q ∈ (Finset.Ioc 0 N).filter Nat.Prime,
      ((((Finset.Ioc 0 N).filter fun n => p ∣ n ∧ q ∣ n).card : ℕ) : ℝ)
        ≤ (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
          + if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0 := by
    intro p hp q hq
    have hpp : p.Prime := (Finset.mem_filter.mp hp).2
    have hqq : q.Prime := (Finset.mem_filter.mp hq).2
    rw [card_dvd_pair N hpp hqq]
    rcases eq_or_ne p q with rfl | hpq
    · rw [if_pos rfl, if_pos rfl]
      have h1 : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) * (p : ℝ)⁻¹ := by
        have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p)
        rwa [div_eq_mul_inv] at h
      have h2 : (0 : ℝ) ≤ (N : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by positivity
      linarith
    · rw [if_neg hpq, if_neg hpq, add_zero]
      have h1 : ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) * (q : ℝ)) := by
        have h := Nat.cast_div_le (α := ℝ) (m := N) (n := p * q)
        rwa [Nat.cast_mul] at h
      calc ((N / (p * q) : ℕ) : ℝ) ≤ (N : ℝ) / ((p : ℝ) * (q : ℝ)) := h1
        _ = (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
            rw [div_eq_mul_inv, mul_inv]; ring
  have hfirst : ∑ p ∈ Finset.Ioc 0 N with p.Prime,
      ∑ q ∈ Finset.Ioc 0 N with q.Prime, (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
      = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2 := by
    calc ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime, (N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
        = ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((N : ℝ) * (p : ℝ)⁻¹)
            * ∑ q ∈ Finset.Ioc 0 N with q.Prime, ((q : ℝ))⁻¹ :=
          Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
      _ = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, sq]
          ring
  have hdiag : ∑ p ∈ Finset.Ioc 0 N with p.Prime,
      ∑ q ∈ Finset.Ioc 0 N with q.Prime,
        (if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0)
      = (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
    have h1 : ∀ p ∈ (Finset.Ioc 0 N).filter Nat.Prime,
        ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          (if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0)
        = (N : ℝ) * (p : ℝ)⁻¹ := by
      intro p hp
      rw [Finset.sum_ite_eq _ p fun _ => (N : ℝ) * (p : ℝ)⁻¹, if_pos hp]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  calc ((∑ n ∈ Finset.Ioc 0 N, omega n ^ 2 : ℕ) : ℝ)
      = ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((((Finset.Ioc 0 N).filter fun n => p ∣ n ∧ q ∣ n).card : ℕ) : ℝ) := by
        rw [sum_omega_sq_eq]
        push_cast
        rfl
    _ ≤ ∑ p ∈ Finset.Ioc 0 N with p.Prime,
          ∑ q ∈ Finset.Ioc 0 N with q.Prime,
          ((N : ℝ) * (p : ℝ)⁻¹ * (q : ℝ)⁻¹
            + if p = q then (N : ℝ) * (p : ℝ)⁻¹ else 0) :=
        Finset.sum_le_sum fun p hp =>
          Finset.sum_le_sum fun q hq => hpair p hp q hq
    _ = (N : ℝ) * (∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) ^ 2
        + (N : ℝ) * ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ := by
        rw [← hfirst, ← hdiag, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib

/-! ### Turán's variance bound -/

/-- **Turán's variance bound, with the explicit constant `275`**: whenever
`1 ≤ loglog N`, `∑_{n ≤ N} (ω n − loglog N)² ≤ 275 · N · loglog N`.

The constant decomposes as `16² + 16 + 3 = 275`, where `16` is the Mertens
band of `ZetaLean.Mertens.mertens_second_theorem`.  The dependence on that
band is quadratic, which is why tightening Mertens is the whole lever
here: the `76` this file was first proved with gave `5855`. -/
theorem sum_sq_dev_le {N : ℕ} (hL : 1 ≤ loglog N) :
    ∑ n ∈ Finset.Ioc 0 N, ((omega n : ℝ) - loglog N) ^ 2
      ≤ 275 * (N : ℝ) * loglog N := by
  have hMert : |(∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹) - loglog N| ≤ 16 :=
    ZetaLean.Mertens.mertens_second_theorem N
  obtain ⟨hMl, hMu⟩ := abs_le.mp hMert
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hM1l := first_moment_lower N
  have hM2 := second_moment_upper N
  set S := ∑ p ∈ Finset.Ioc 0 N with p.Prime, ((p : ℝ))⁻¹ with hS
  set L := loglog N with hLdef
  -- expand the square around the mean
  have hexp : ∑ n ∈ Finset.Ioc 0 N, ((omega n : ℝ) - L) ^ 2
      = ((∑ n ∈ Finset.Ioc 0 N, omega n ^ 2 : ℕ) : ℝ)
        - 2 * L * ((∑ n ∈ Finset.Ioc 0 N, omega n : ℕ) : ℝ) + (N : ℝ) * L ^ 2 := by
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have hcardIoc : ((Finset.Ioc 0 N).card : ℝ) = (N : ℝ) := by
      rw [Nat.card_Ioc, Nat.sub_zero]
    rw [show (N : ℝ) * L ^ 2 = ∑ _n ∈ Finset.Ioc 0 N, L ^ 2 by
      rw [Finset.sum_const, nsmul_eq_mul, hcardIoc]]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  -- the moment bounds, in the shape the final estimate wants
  have key : 2 * L * ((N : ℝ) * S - N)
      ≤ 2 * L * ((∑ n ∈ Finset.Ioc 0 N, omega n : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hM1l (by linarith)
  have hsq : (S - L) ^ 2 ≤ 256 := by nlinarith
  have hD2 : (N : ℝ) * (S - L) ^ 2 ≤ (N : ℝ) * 256 :=
    mul_le_mul_of_nonneg_left hsq hN0
  have hSu : (N : ℝ) * S ≤ (N : ℝ) * (L + 16) :=
    mul_le_mul_of_nonneg_left (by linarith) hN0
  have hNL : (N : ℝ) * 1 ≤ (N : ℝ) * L := mul_le_mul_of_nonneg_left hL hN0
  nlinarith [hexp, hM2, key, hD2, hSu, hNL]

private theorem tendsto_loglog : Tendsto loglog atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Turán's variance estimate**, with the explicit constant `275`. -/
theorem turan_variance : TuranVariance := by
  refine ⟨275, ?_⟩
  filter_upwards [tendsto_loglog.eventually_ge_atTop 1] with N hL
  exact sum_sq_dev_le hL

/-! ### The Chebyshev step -/

/-- **Chebyshev's inequality, in the form Turán uses it.**  At any scale `N` where
the variance is at most `V` and `0 ≤ ε * loglog N`, the exceptional set is small. -/
theorem card_exceptional_mul_le {N : ℕ} {ε V : ℝ} (hε : 0 ≤ ε * loglog N)
    (hV : ∑ n ∈ Finset.Ioc 0 N, ((omega n : ℝ) - loglog N) ^ 2 ≤ V) :
    ((exceptional N ε).card : ℝ) * (ε * loglog N) ^ 2 ≤ V := by
  have hsub : exceptional N ε ⊆ Finset.Ioc 0 N := Finset.filter_subset _ _
  have hlow : ((exceptional N ε).card : ℝ) * (ε * loglog N) ^ 2
      ≤ ∑ n ∈ exceptional N ε, ((omega n : ℝ) - loglog N) ^ 2 := by
    rw [← nsmul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun n hn => ?_
    have h : ε * loglog N < |(omega n : ℝ) - loglog N| :=
      (Finset.mem_filter.mp hn).2
    have h1 : (ε * loglog N) ^ 2 ≤ |(omega n : ℝ) - loglog N| ^ 2 := by nlinarith
    rwa [sq_abs] at h1
  refine hlow.trans (le_trans ?_ hV)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => sq_nonneg _

/-- **The Chebyshev half of Turán's proof**: the variance estimate implies the
Hardy–Ramanujan theorem. -/
theorem hardyRamanujan_of_turanVariance : TuranVariance → HardyRamanujanTheorem := by
  rintro ⟨C, hC⟩ ε hε
  have hpos : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ loglog N :=
    tendsto_loglog.eventually_ge_atTop 1
  have hN : ∀ᶠ N : ℕ in atTop, (0 : ℝ) < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop 0
  have hg : Tendsto (fun N : ℕ => C / (ε ^ 2 * loglog N)) atTop (𝓝 0) :=
    (tendsto_loglog.const_mul_atTop (by positivity : (0:ℝ) < ε ^ 2)).const_div_atTop C
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hg
  filter_upwards [hC, hpos, hN] with N hvar hl hNpos
  have hl0 : (0 : ℝ) < loglog N := lt_of_lt_of_le zero_lt_one hl
  have hεl : 0 ≤ ε * loglog N := by positivity
  have key := card_exceptional_mul_le hεl hvar
  rw [div_le_div_iff₀ hNpos (by positivity : (0:ℝ) < ε ^ 2 * loglog N)]
  have hmul : (((exceptional N ε).card : ℝ) * (ε ^ 2 * loglog N)) * loglog N
      ≤ (C * (N : ℝ)) * loglog N := by nlinarith [key]
  exact le_of_mul_le_mul_right hmul hl0

/-- **The Hardy–Ramanujan theorem** (Wikidata Q5656674): `ω n` has normal
order `log log n`, in the density form.  Turán's proof, assembled from the
variance bound `turan_variance` and the Chebyshev step. -/
theorem hardy_ramanujan : HardyRamanujanTheorem :=
  hardyRamanujan_of_turanVariance turan_variance

end ZetaLean.HardyRamanujan
