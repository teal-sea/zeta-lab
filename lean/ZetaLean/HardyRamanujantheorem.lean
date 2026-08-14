/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib

/-!
# Hardy–Ramanujan: the statement, and the half of Turán's proof that is not the hard half

The Hardy–Ramanujan theorem says that `ω n`, the number of distinct prime factors
of `n`, has normal order `log log n`: for every `ε > 0` the density of the integers
`n ≤ N` with `|ω n - log log N| > ε * log log N` tends to `0`.

Turán's proof has two halves.

1. A **variance estimate**: `∑_{n ≤ N} (ω n - log log N)^2 = O(N log log N)`.
   This is the hard half.  It needs Mertens' second theorem,
   `∑_{p ≤ N} 1/p = log log N + M + O(1/log N)`, which this file does not have
   available and does not prove.
2. A **Chebyshev step**: the variance estimate implies the density statement.

This file contains, with no `sorry`:

* `ZetaLean.HardyRamanujan.HardyRamanujanTheorem`, the statement itself;
* `sum_omega_eq_sum_div`, the unconditional double-counting identity
  `∑_{n ≤ N} ω n = ∑_{p ≤ N} ⌊N/p⌋`, which is the first step of half 1;
* `hardyRamanujan_of_turanVariance`, the whole of half 2 as an implication.

It does **not** contain the Hardy–Ramanujan theorem.  `TuranVariance` is a
hypothesis here, not a theorem, so `hardyRamanujan_of_turanVariance` is a
reduction and nothing more.  See `hunts/r_0339c1/RESULTS.md` for what a next
attempt on the remaining half would need.
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

/-- **The Hardy–Ramanujan theorem**, as a proposition.  Not proved in this file. -/
def HardyRamanujanTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun N : ℕ => ((exceptional N ε).card : ℝ) / (N : ℝ)) atTop (𝓝 0)

/-- **Turán's variance estimate**, as a proposition.  Not proved in this file:
it is the half of the argument that needs Mertens' second theorem. -/
def TuranVariance : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ∑ n ∈ Finset.Ioc 0 N, ((omega n : ℝ) - loglog N) ^ 2 ≤ C * (N : ℝ) * loglog N

/-! ### The unconditional double-counting identity -/

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

/-! ### The Chebyshev step -/

private theorem tendsto_loglog : Tendsto loglog atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

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

/-- **The Chebyshev half of Turán's proof, in full.**  Turán's variance estimate
implies the Hardy–Ramanujan theorem.

This is an implication, not the theorem: `TuranVariance` is not proved here. -/
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

end ZetaLean.HardyRamanujan
