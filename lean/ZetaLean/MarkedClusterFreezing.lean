/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterPrefix
import ZetaLean.RC2PrefixAssembly

/-!
# Marked-cluster summability and finite height freezing

This file isolates two abstract steps used by the marked-cluster argument in
`hunts/higher_xi/URMS2-051-AUDIT.md`.

First, a cluster series remains summable after multiplication by any fixed
polynomial mark when its terms admit a geometric envelope.  Second, a
coefficientwise Lipschitz bound transfers a marked square-mass estimate to the
square mass of the difference between moving and frozen coefficients.  The
latter statement is also connected to the existing conditional RC2 endpoint
energy theorem.

The analytic inputs remain explicit hypotheses.  In particular, this file does
not prove a geometric envelope for the connected clusters, a derivative
square-density estimate, the RAMS2 asymptotic, or a contour-transfer statement.
-/

namespace ZetaLean.HigherXi

open Finset

/-! ## Polynomial marks preserve geometric summability -/

/-- A fixed polynomial mark does not destroy summability under a geometric
envelope.  This is the abstract support-size step needed after a connected
cluster majorant has supplied the envelope; it does not construct that
majorant. -/
theorem summable_polynomiallyMarked_of_geometric_bound
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (degree : ℕ) {marked : ℕ → E} {C q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hmarked : ∀ r, ‖marked r‖ ≤ C * (r : ℝ) ^ degree * q ^ r) :
    Summable marked := by
  apply Summable.of_norm_bounded
    ((summable_pow_mul_geometric_of_norm_lt_one degree
      (show ‖q‖ < 1 by simpa [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1)).mul_left C)
  intro r
  simpa [mul_assoc] using hmarked r

/-! ## Exact finite freezing transfer -/

/-- A coefficientwise Lipschitz estimate transfers marked square mass to the
square mass of a moving-minus-frozen coefficient family.  This is an exact
finite inequality, with no asymptotic notation. -/
theorem prefixMass_frozenDifference_le
    {moving frozen : ℕ → ℂ} {mark : ℕ → ℝ} {Delta M : ℝ} {N : ℕ}
    (hDelta : 0 ≤ Delta) (hmark : ∀ n, 0 ≤ mark n)
    (hfreeze : ∀ n, ‖moving n - frozen n‖ ≤ Delta * mark n)
    (hmass : prefixMass (fun n ↦ mark n ^ 2) N ≤ M) :
    prefixMass (fun n ↦ ‖moving n - frozen n‖ ^ 2) N ≤ Delta ^ 2 * M := by
  calc
    prefixMass (fun n ↦ ‖moving n - frozen n‖ ^ 2) N ≤
        prefixMass (fun n ↦ Delta ^ 2 * mark n ^ 2) N := by
      unfold prefixMass
      apply Finset.sum_le_sum
      intro n hn
      have hnonneg : 0 ≤ Delta * mark n := mul_nonneg hDelta (hmark n)
      nlinarith [hfreeze n, norm_nonneg (moving n - frozen n)]
    _ = Delta ^ 2 * prefixMass (fun n ↦ mark n ^ 2) N := by
      simp only [prefixMass, Finset.mul_sum]
    _ ≤ Delta ^ 2 * M :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg Delta)

/-- A marked prefix square-density bound gives the corresponding bound for the
moving-minus-frozen coefficients, with the exact factor `Delta^2`.  The marked
prefix bound is still an analytic hypothesis. -/
theorem frozenDifference_prefixMass_le_of_markedPrefixMass_le
    {moving frozen : ℕ → ℂ} {mark : ℕ → ℝ} {Delta C : ℝ}
    (hDelta : 0 ≤ Delta) (hmark : ∀ n, 0 ≤ mark n)
    (hfreeze : ∀ n, ‖moving n - frozen n‖ ≤ Delta * mark n)
    (hpre : ∀ N, 1 ≤ N →
      prefixMass (fun n ↦ mark n ^ 2) N ≤
        C * N * (1 + Real.log N)) :
    ∀ N, 1 ≤ N →
      prefixMass (fun n ↦ ‖moving n - frozen n‖ ^ 2) N ≤
        (Delta ^ 2 * C) * N * (1 + Real.log N) := by
  intro N hN
  calc
    prefixMass (fun n ↦ ‖moving n - frozen n‖ ^ 2) N ≤
        Delta ^ 2 * (C * N * (1 + Real.log N)) :=
      prefixMass_frozenDifference_le hDelta hmark hfreeze (hpre N hN)
    _ = (Delta ^ 2 * C) * N * (1 + Real.log N) := by ring

/-- The exact two-range endpoint energy of the frozen difference is controlled
once the marked derivative family has the RAMS2-shaped prefix bound.  No such
bound is asserted here. -/
theorem twoRangeEndpointEnergy_frozenDifference_le
    {moving frozen : ℕ → ℂ} {mark : ℕ → ℝ} {Delta C : ℝ}
    {X W : ℕ}
    (hX : 1 ≤ X) (hXW : X ≤ W) (hDelta : 0 ≤ Delta) (hC : 0 ≤ C)
    (hmark : ∀ n, 0 ≤ mark n)
    (hfreeze : ∀ n, ‖moving n - frozen n‖ ≤ Delta * mark n)
    (hpre : ∀ N, 1 ≤ N →
      prefixMass (fun n ↦ mark n ^ 2) N ≤
        C * N * (1 + Real.log N)) :
    twoRangeEndpointEnergy (X : ℝ) W (fun n ↦ moving n - frozen n) ≤
      11 * (Delta ^ 2 * C) * X * (1 + Real.log X) := by
  apply twoRangeEndpointEnergy_le_of_prefixMass_le hX hXW
    (mul_nonneg (sq_nonneg Delta) hC)
  exact frozenDifference_prefixMass_le_of_markedPrefixMass_le
    hDelta hmark hfreeze hpre

/-- The exact finite RC2 mean-square remainder for the moving-minus-frozen
coefficient family.  The marked derivative prefix estimate and the
coefficientwise freezing estimate remain explicit hypotheses; this theorem
only performs their finite mean-square assembly. -/
theorem norm_twoRange_mean_square_sub_diagonal_frozenDifference_le
    (U : ℝ) {moving frozen : ℕ → ℂ} {mark : ℕ → ℝ}
    {Delta C : ℝ} {X W : ℕ}
    (hX : 1 ≤ X) (hXW : X ≤ W) (hDelta : 0 ≤ Delta) (hC : 0 ≤ C)
    (hmark : ∀ n, 0 ≤ mark n)
    (hfreeze : ∀ n, ‖moving n - frozen n‖ ≤ Delta * mark n)
    (hpre : ∀ N, 1 ≤ N →
      prefixMass (fun n ↦ mark n ^ 2) N ≤
        C * N * (1 + Real.log N)) :
    ‖(∫ t in U..2 * U,
        starRingEnd ℂ
            (logarithmicDirichletPolynomial W
              (twoRangeCoefficient X (fun n ↦ moving n - frozen n)) t) *
          logarithmicDirichletPolynomial W
            (twoRangeCoefficient X (fun n ↦ moving n - frozen n)) t) -
        (U : ℂ) * ∑ n ∈ Finset.Icc 1 W,
          starRingEnd ℂ
              (twoRangeCoefficient X (fun n ↦ moving n - frozen n) n) *
            twoRangeCoefficient X (fun n ↦ moving n - frozen n) n‖ ≤
      66 * realHarmonicMass W * (Delta ^ 2 * C) * X *
        (1 + Real.log X) := by
  apply norm_twoRange_mean_square_sub_diagonal_le_of_prefixMass_le U
    hX hXW (mul_nonneg (sq_nonneg Delta) hC)
  exact frozenDifference_prefixMass_le_of_markedPrefixMass_le
    hDelta hmark hfreeze hpre

end ZetaLean.HigherXi
