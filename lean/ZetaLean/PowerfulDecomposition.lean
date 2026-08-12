/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Squarefree
import ZetaLean.RepeatedPrimeDominated

/-!
# Powerful-squarefree arithmetic decomposition

This file defines a powerful natural directly through `Nat.factorization` and
constructs the canonical powerful and squarefree factors of every nonzero
natural. The construction splits prime exponents into those unequal to one
and those equal to one.

The factors multiply to the original natural, the first is powerful, the
second is squarefree, and they are coprime. The final section isolates the
exact local geometric tail for the weighted harmonic term. No coefficient
estimate, Cauchy bound, global Euler product, or asymptotic is asserted here.
-/

namespace ZetaLean.HigherXi

open Finsupp

/-- A nonzero natural is powerful when every nonzero prime exponent is at
least two. -/
def IsPowerfulNat (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p, n.factorization p = 0 ∨ 2 ≤ n.factorization p

/-- The exponent vector containing the exponents of `n` that are not one. -/
noncomputable def powerfulExponentPart (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter fun p ↦ n.factorization p ≠ 1

/-- The complementary exponent vector, containing exactly exponent one. -/
noncomputable def squarefreeExponentPart (n : ℕ) : ℕ →₀ ℕ :=
  n.factorization.filter fun p ↦ ¬n.factorization p ≠ 1

/-- The canonical powerful factor of `n`. -/
noncomputable def powerfulPart (n : ℕ) : ℕ :=
  (powerfulExponentPart n).prod (fun p e ↦ p ^ e)

/-- The canonical squarefree factor of `n`. -/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  (squarefreeExponentPart n).prod (fun p e ↦ p ^ e)

/-- The total number of prime factors of `n`, counted with multiplicity. -/
noncomputable def primeFactorMultiplicity (n : ℕ) : ℕ :=
  n.factorization.sum fun _ e ↦ e

/-- The arithmetic weight `(16/9)^Ω(n) / n`. -/
noncomputable def powerfulHarmonicWeight (n : ℕ) : ℝ :=
  (16 / 9 : ℝ) ^ primeFactorMultiplicity n / n

theorem powerfulExponentPart_add_squarefreeExponentPart (n : ℕ) :
    powerfulExponentPart n + squarefreeExponentPart n = n.factorization := by
  exact Finsupp.filter_add_filter_not n.factorization
    (fun p ↦ n.factorization p ≠ 1)

theorem powerfulExponentPart_le_factorization (n : ℕ) :
    powerfulExponentPart n ≤ n.factorization := by
  rw [Finsupp.le_def]
  intro p
  simp only [powerfulExponentPart, Finsupp.filter_apply]
  split <;> simp

theorem squarefreeExponentPart_le_factorization (n : ℕ) :
    squarefreeExponentPart n ≤ n.factorization := by
  rw [Finsupp.le_def]
  intro p
  simp only [squarefreeExponentPart, Finsupp.filter_apply]
  split <;> simp

theorem factorization_powerfulPart (n : ℕ) :
    (powerfulPart n).factorization = powerfulExponentPart n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (powerfulExponentPart_le_factorization n)

theorem factorization_squarefreePart (n : ℕ) :
    (squarefreePart n).factorization = squarefreeExponentPart n := by
  exact Nat.factorization_prod_pow_eq_self_of_le_factorization
    (squarefreeExponentPart_le_factorization n)

theorem powerfulPart_dvd (n : ℕ) : powerfulPart n ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (powerfulExponentPart_le_factorization n)

theorem squarefreePart_dvd (n : ℕ) : squarefreePart n ∣ n :=
  Nat.prod_pow_dvd_of_le_factorization (squarefreeExponentPart_le_factorization n)

theorem powerfulPart_ne_zero {n : ℕ} (hn : n ≠ 0) : powerfulPart n ≠ 0 :=
  ne_zero_of_dvd_ne_zero hn (powerfulPart_dvd n)

theorem squarefreePart_ne_zero {n : ℕ} (hn : n ≠ 0) : squarefreePart n ≠ 0 :=
  ne_zero_of_dvd_ne_zero hn (squarefreePart_dvd n)

/-- The canonical first factor is powerful. -/
theorem isPowerfulNat_powerfulPart {n : ℕ} (hn : n ≠ 0) :
    IsPowerfulNat (powerfulPart n) := by
  refine ⟨powerfulPart_ne_zero hn, fun p ↦ ?_⟩
  rw [factorization_powerfulPart, powerfulExponentPart,
    Finsupp.filter_apply]
  split_ifs with hp
  · rcases Nat.eq_zero_or_pos (n.factorization p) with hzero | hpos
    · exact Or.inl hzero
    · exact Or.inr (by omega)
  · exact Or.inl rfl

/-- The canonical second factor is squarefree. -/
theorem squarefree_squarefreePart {n : ℕ} (hn : n ≠ 0) :
    Squarefree (squarefreePart n) := by
  apply Nat.squarefree_of_factorization_le_one (squarefreePart_ne_zero hn)
  intro p
  rw [factorization_squarefreePart, squarefreeExponentPart,
    Finsupp.filter_apply]
  split_ifs with hp <;> omega

/-- The two exponent vectors have disjoint support. -/
theorem disjoint_powerful_squarefree_exponent_parts (n : ℕ) :
    Disjoint (powerfulExponentPart n).support
      (squarefreeExponentPart n).support := by
  rw [powerfulExponentPart, squarefreeExponentPart,
    Finsupp.support_filter, Finsupp.support_filter]
  rw [Finset.disjoint_left]
  intro p hpq hpm
  simp only [Finset.mem_filter] at hpq hpm
  exact hpm.2 hpq.2

/-- The canonical factors are coprime. -/
theorem coprime_powerfulPart_squarefreePart {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (powerfulPart n) (squarefreePart n) := by
  apply Nat.coprime_of_dvd
  intro p hp hpp hps
  have hq : 1 ≤ (powerfulPart n).factorization p :=
    (hp.dvd_iff_one_le_factorization (powerfulPart_ne_zero hn)).mp hpp
  have hm : 1 ≤ (squarefreePart n).factorization p :=
    (hp.dvd_iff_one_le_factorization (squarefreePart_ne_zero hn)).mp hps
  rw [factorization_powerfulPart, powerfulExponentPart,
    Finsupp.filter_apply] at hq
  rw [factorization_squarefreePart, squarefreeExponentPart,
    Finsupp.filter_apply] at hm
  split_ifs at hq hm
  all_goals omega

/-- The canonical powerful and squarefree factors multiply exactly to `n`. -/
theorem powerfulPart_mul_squarefreePart {n : ℕ} (hn : n ≠ 0) :
    powerfulPart n * squarefreePart n = n := by
  rw [powerfulPart, squarefreePart,
    ← Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _),
    powerfulExponentPart_add_squarefreeExponentPart,
    Nat.prod_factorization_pow_eq_self hn]

/-- Every nonzero natural has a powerful-squarefree decomposition with
coprime factors. -/
theorem exists_powerful_coprime_squarefree_decomposition {n : ℕ} (hn : n ≠ 0) :
    ∃ q m, IsPowerfulNat q ∧ Squarefree m ∧ Nat.Coprime q m ∧ q * m = n :=
  ⟨powerfulPart n, squarefreePart n, isPowerfulNat_powerfulPart hn,
    squarefree_squarefreePart hn, coprime_powerfulPart_squarefreePart hn,
    powerfulPart_mul_squarefreePart hn⟩

/-! ## The local weighted harmonic tail -/

theorem primeFactorMultiplicity_prime_pow {p e : ℕ} (hp : p.Prime) :
    primeFactorMultiplicity (p ^ e) = e := by
  simp [primeFactorMultiplicity, hp.factorization_pow]

/-- On a prime power, the arithmetic weight is exactly the expected local
Euler-factor term. -/
theorem powerfulHarmonicWeight_prime_pow {p e : ℕ} (hp : p.Prime) :
    powerfulHarmonicWeight (p ^ e) =
      (16 / 9 : ℝ) ^ e / (p : ℝ) ^ e := by
  simp [powerfulHarmonicWeight, primeFactorMultiplicity_prime_pow hp]

/-- For every possible prime, the powerful exponents `e ≥ 2` give a summable
local geometric tail. -/
theorem summable_powerful_prime_tail {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun j : ℕ ↦ ((16 / 9 : ℝ) / p) ^ (j + 2)) := by
  have hnonneg : 0 ≤ (16 / 9 : ℝ) / p := by positivity
  have hlt : (16 / 9 : ℝ) / p < 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    apply (div_lt_one (by positivity : (0 : ℝ) < p)).2
    norm_num
    linarith
  simpa [Nat.add_comm] using
    (summable_nat_add_iff 2).mpr
      (summable_geometric_of_lt_one hnonneg hlt)

/-- Exact value of the local powerful-prime tail. -/
theorem tsum_powerful_prime_tail {p : ℕ} (hp : 2 ≤ p) :
    ∑' j : ℕ, ((16 / 9 : ℝ) / p) ^ (j + 2) =
      ((16 / 9 : ℝ) / p) ^ 2 * (1 - (16 / 9 : ℝ) / p)⁻¹ := by
  have hnonneg : 0 ≤ (16 / 9 : ℝ) / p := by positivity
  have hlt : (16 / 9 : ℝ) / p < 1 := by
    have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
    apply (div_lt_one (by positivity : (0 : ℝ) < p)).2
    norm_num
    linarith
  rw [show (fun j : ℕ ↦ ((16 / 9 : ℝ) / p) ^ (j + 2)) =
      (fun j : ℕ ↦ ((16 / 9 : ℝ) / p) ^ 2 *
        ((16 / 9 : ℝ) / p) ^ j) by
      funext j
      rw [pow_add, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hnonneg hlt]

end ZetaLean.HigherXi
