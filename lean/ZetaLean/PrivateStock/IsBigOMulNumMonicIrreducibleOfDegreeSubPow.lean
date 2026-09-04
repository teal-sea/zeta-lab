import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.GeomSum
import ZetaLean.PrivateStock.SumDegreeMulNumMonicIrreducibleOfDegree

/-!
# The prime polynomial theorem for `F[X]`, with square-root error term

Let `F` be a finite field with `q = |F|` elements and let `N d` denote the number of monic
irreducible polynomials of degree `d` in `F[X]`. The mass formula
`∑ e ∈ d.divisors, e * N e = q ^ d` (proved in `Submission.SumDegreeMulNumMonicIrreducibleOfDegree`)
gives, for `d ≠ 0`,

`q ^ d - d * N d = ∑ e ∈ d.divisors.erase d, e * N e`.

Every proper divisor `e` of `d` satisfies `2 * e ≤ d`, and `e * N e ≤ q ^ e` by the same mass
formula applied to `e`. Hence the error is at most `∑ e ≤ d / 2, q ^ e < q ^ (d / 2 + 1)`, which
is `O(q ^ (d / 2))`.
-/

set_option autoImplicit false

open Finset

namespace Submission.Helpers

variable (F : Type*) [Field F] [Finite F]

/-- Each individual term of the mass formula is bounded by the total: for `e ≠ 0`, the number of
monic irreducible polynomials of degree `e` satisfies `e * N e ≤ |F| ^ e`. -/
theorem mul_numMonicIrreducibleOfDegree_le_pow {e : ℕ} (he : e ≠ 0) :
    e * Polynomial.numMonicIrreducibleOfDegree F e ≤ Nat.card F ^ e := by
  rw [← Polynomial.sum_degree_mul_numMonicIrreducibleOfDegree_eq_pow F he]
  exact Finset.single_le_sum (f := fun i ↦ i * Polynomial.numMonicIrreducibleOfDegree F i)
    (fun i _ ↦ Nat.zero_le _) (Nat.mem_divisors_self e he)

/-- The mass formula, split off the top term: the contribution of the proper divisors of `d` is
exactly the difference between `|F| ^ d` and `d * N d`. -/
theorem sum_erase_add_mul_numMonicIrreducibleOfDegree {d : ℕ} (hd : d ≠ 0) :
    (∑ e ∈ d.divisors.erase d, e * Polynomial.numMonicIrreducibleOfDegree F e) +
      d * Polynomial.numMonicIrreducibleOfDegree F d = Nat.card F ^ d := by
  rw [Finset.sum_erase_add _ _ (Nat.mem_divisors_self d hd)]
  exact Polynomial.sum_degree_mul_numMonicIrreducibleOfDegree_eq_pow F hd

/-- A proper divisor of `d` is at most `d / 2`. -/
theorem le_div_two_of_mem_divisors_erase {d e : ℕ} (he : e ∈ d.divisors.erase d) : e ≤ d / 2 := by
  obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp he
  obtain ⟨hdvd, hd⟩ := Nat.mem_divisors.mp hmem
  obtain ⟨c, rfl⟩ := hdvd
  have hc : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with hc | hc
    · interval_cases c
      · simp at hd
      · simp at hne
    · exact hc
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  exact Nat.mul_le_mul (le_refl e) hc

/-- The total contribution of the proper divisors of `d` is less than `|F| ^ (d / 2 + 1)`. -/
theorem sum_erase_lt_pow (d : ℕ) :
    (∑ e ∈ d.divisors.erase d, e * Polynomial.numMonicIrreducibleOfDegree F e) <
      Nat.card F ^ (d / 2 + 1) := by
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  calc (∑ e ∈ d.divisors.erase d, e * Polynomial.numMonicIrreducibleOfDegree F e)
      ≤ ∑ e ∈ d.divisors.erase d, Nat.card F ^ e :=
        Finset.sum_le_sum fun e he ↦ mul_numMonicIrreducibleOfDegree_le_pow F
          (Nat.pos_of_mem_divisors (Finset.mem_of_mem_erase he)).ne'
    _ < Nat.card F ^ (d / 2 + 1) :=
        Nat.geomSum_lt hq2 fun e he ↦ Nat.lt_succ_of_le (le_div_two_of_mem_divisors_erase he)

end Submission.Helpers

open Submission.Helpers in
/-- **The prime polynomial theorem for `F[X]`.** Over a finite field `F` with `q = |F|` elements,
the number `N d` of monic irreducible polynomials of degree `d` satisfies
`d * N d = q ^ d + O(q ^ (d / 2))` as `d → ∞`. -/
theorem Polynomial.isBigO_mul_numMonicIrreducibleOfDegree_sub_pow
    (F : Type*) [Field F] [Finite F] :
    (fun d : ℕ => (d : ℝ) * Polynomial.numMonicIrreducibleOfDegree F d - (Nat.card F : ℝ) ^ d)
      =O[Filter.atTop] (fun d : ℕ => (Nat.card F : ℝ) ^ ((d : ℝ) / 2)) := by
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hq1 : (1 : ℝ) ≤ (Nat.card F : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt hq2
  have hq0 : (0 : ℝ) ≤ (Nat.card F : ℝ) := by positivity
  rw [Asymptotics.isBigO_iff]
  refine ⟨(Nat.card F : ℝ), Filter.eventually_atTop.mpr ⟨1, fun d hd ↦ ?_⟩⟩
  have hd0 : d ≠ 0 := by omega
  set R : ℕ := ∑ e ∈ d.divisors.erase d, e * Polynomial.numMonicIrreducibleOfDegree F e with hR
  -- The difference is exactly `-R`.
  have hsplit : (R : ℝ) + (d : ℝ) * Polynomial.numMonicIrreducibleOfDegree F d
      = (Nat.card F : ℝ) ^ d := by
    have := sum_erase_add_mul_numMonicIrreducibleOfDegree F hd0
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) this
  have hdiff : (d : ℝ) * Polynomial.numMonicIrreducibleOfDegree F d - (Nat.card F : ℝ) ^ d
      = -(R : ℝ) := by linarith
  rw [hdiff, norm_neg, Real.norm_natCast]
  -- The right-hand norm is just the rpow itself.
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hq0 _)]
  -- `R < q ^ (d / 2 + 1)`.
  have hRlt : (R : ℝ) ≤ (Nat.card F : ℝ) ^ (d / 2 + 1) := by
    have : R ≤ Nat.card F ^ (d / 2 + 1) := (sum_erase_lt_pow F d).le
    exact_mod_cast this
  refine hRlt.trans ?_
  rw [pow_succ, mul_comm]
  gcongr
  rw [← Real.rpow_natCast (Nat.card F : ℝ) (d / 2)]
  refine Real.rpow_le_rpow_of_exponent_le hq1 ?_
  exact_mod_cast Nat.cast_div_le (α := ℝ)
