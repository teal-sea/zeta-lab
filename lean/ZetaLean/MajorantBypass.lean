/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ChebyshevBounds

/-!
# The majorant bypass: the display without the tight recurrence

`PrimeSimplex.distinctPrimeLogMass_le_factorial_majorant` reaches the
order-uniform display

`A_j(X) ≤ base · B^(j-1) / (j! (2j-1)!)`

from `hprime`, an insertion recurrence **on the true masses**.  Two
independent derivation attempts, plus an adversarial pass, established that
this route cannot be completed as stated, and why:

* the recurrence is **asymptotically tight**.  Measured over
  `X ∈ [10², 10⁷]`, the ratio `(j+1)(2j)(2j+1)A_{j+1}/A_j` is maximal at
  `j = 1` at every cutoff and equals `(1 - o(1))·(1 + log X)²`; the extremal
  family is pairs `{p, q}` with `pq` near `X` (the `Beta(2,2)` split profile
  of the weight).  So any `B(X) ≤ D(1 + log X)²` forces `D ≥ 1`;
* consequently `hprime` needs an order-uniform **lower** bound on `A_j` with
  a matching constant.  Chebyshev's estimate is an upper bound and supplies
  no such thing, and a route through separate upper and lower bounds
  inherits a `(C/c)^j` mismatch incompatible with an absolute `D`.

The bypass is that **nothing downstream consumes the recurrence**.  What the
mathematics uses is the endpoint display, and that survives domination: if a
majorant sequence `maj` dominates the true masses and satisfies the
recurrence itself, the display passes to the true masses.  This file supplies
the general fact and the concrete majorant, both unconditional.

`powerMajorant` is exactly the shape the display asserts, and
`powerMajorant_step` shows it satisfies the recurrence with **equality** at
`B · (1 + log X)²` — the factorial denominator is built so that
`(j+1)(2j)(2j+1)` is precisely the ratio `denominator(j+1)/denominator(j)`.

What remains open is therefore one hypothesis, `A_j(X) ≤ powerMajorant …`,
which is a plain domination and is what the prose in
`hunts/higher_xi/RAMS1-ATTACK.md` §4.2 actually argues (an integral
comparison in log coordinates).  That is a strictly weaker obligation than
`hprime`, and unlike `hprime` it is not tight.
-/

namespace ZetaLean.HigherXi

open Finset

/-- Domination transfers the order-uniform display.  A majorant that both
dominates a sequence and obeys the insertion recurrence hands the sequence
the display, with no recurrence assumed for the sequence itself. -/
theorem mass_le_of_dominated_majorant
    (mass maj : ℕ → ℝ) (base B : ℝ)
    (hdom : ∀ j, 1 ≤ j → mass j ≤ maj j)
    (hbase : maj 1 ≤ base) (hB : 0 ≤ B)
    (hstep : ∀ j, 1 ≤ j →
      ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ) * maj (j + 1) ≤
        B * maj j)
    {j : ℕ} (hj : 1 ≤ j) :
    mass j ≤ base * B ^ (j - 1) / simplexFactorialDenominator j :=
  le_trans (hdom j hj)
    (mass_le_base_mul_pow_div_simplexFactorialDenominator maj base B
      hbase hB hstep hj)

/-- The explicit majorant of the display's own shape:
`c · B^(j-1) · X · (1 + log X)^(2j+1) / (j! (2j-1)!)`. -/
noncomputable def powerMajorant (c B : ℝ) (X : ℕ) (j : ℕ) : ℝ :=
  c * B ^ (j - 1) * (X : ℝ) * (1 + Real.log X) ^ (2 * j + 1) /
    simplexFactorialDenominator j

/-- The majorant satisfies the insertion recurrence with **equality**, at
`B · (1 + log X)²`.  Nothing is lost here; the tightness that defeats
`hprime` on the true masses is exactly the equality the majorant enjoys. -/
theorem powerMajorant_step (c B : ℝ) (X : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    ((j + 1 : ℕ) : ℝ) * ((2 * j : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ) *
        powerMajorant c B X (j + 1) =
      (B * (1 + Real.log X) ^ 2) * powerMajorant c B X j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  unfold powerMajorant
  rw [simplexFactorialDenominator_succ hj]  -- factors appear on the right
  have hden : simplexFactorialDenominator (k + 1) ≠ 0 :=
    ne_of_gt (simplexFactorialDenominator_pos (k + 1))
  have hcoeff : ((k + 1 + 1 : ℕ) : ℝ) * ((2 * (k + 1) : ℕ) : ℝ) *
      ((2 * (k + 1) + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : (1 + Real.log X) ^ (2 * (k + 1 + 1) + 1) =
      (1 + Real.log X) ^ (2 * (k + 1) + 1) * (1 + Real.log X) ^ 2 := by
    rw [← pow_add, show 2 * (k + 1) + 1 + 2 = 2 * (k + 1 + 1) + 1 by omega]
  have hB : B ^ (k + 1 + 1 - 1) = B ^ (k + 1 - 1) * B := by
    rw [show k + 1 + 1 - 1 = (k + 1 - 1) + 1 by omega, pow_succ]
  rw [hpow, hB]
  field_simp

/-- **The bypass, concretely.**  Domination by `powerMajorant` delivers the
order-uniform display for the true distinct-prime masses, with no insertion
recurrence assumed for them.

The base bound `A_1(X) ≤ (log X)³ · X log 4` is already unconditional
(`distinctPrimeLogMass_one_le`); this theorem takes the domination and
returns the display, so the single remaining analytic obligation is the
hypothesis `hdom`. -/
theorem distinctPrimeLogMass_le_of_dominated
    (X : ℕ) (c B base : ℝ)
    (hdom : ∀ j, 1 ≤ j → distinctPrimeLogMass X j ≤ powerMajorant c B X j)
    (hbase : powerMajorant c B X 1 ≤ base)
    (hB : 0 ≤ B * (1 + Real.log X) ^ 2)
    {j : ℕ} (hj : 1 ≤ j) :
    distinctPrimeLogMass X j ≤
      base * (B * (1 + Real.log X) ^ 2) ^ (j - 1) /
        simplexFactorialDenominator j := by
  refine mass_le_of_dominated_majorant (distinctPrimeLogMass X)
    (powerMajorant c B X) base (B * (1 + Real.log X) ^ 2)
    hdom hbase hB ?_ hj
  intro i hi
  exact le_of_eq (powerMajorant_step c B X hi)

end ZetaLean.HigherXi
