/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ComplexLogMeanValue
import ZetaLean.TwoRangeWeights
import ZetaLean.PowerMargin

/-!
# Assembly of the finite logarithmic mean square

This file closes the finite combinatorial seam between the exact double-sum
integral expansion and the paired off-diagonal norm estimate.  It then
specializes the result to the exact two-range RC2 coefficients.
-/

namespace ZetaLean.HigherXi

open Complex Finset

/-- A finite square over a linear order is its diagonal plus the two
orientations attached to each strict unordered pair. -/
theorem sum_square_eq_diagonal_add_pairs
    {R : Type*} [AddCommMonoid R] (S : Finset ℕ) (f : ℕ → ℕ → R) :
    (∑ m ∈ S, ∑ n ∈ S, f m n) =
      (∑ n ∈ S, f n n) +
        ∑ n ∈ S, ∑ m ∈ S.filter (fun m => m < n), (f m n + f n m) := by
  simp_rw [Finset.sum_filter]
  have hpairs :
      (∑ n ∈ S, ∑ m ∈ S, if m < n then f m n + f n m else 0) =
        (∑ n ∈ S, ∑ m ∈ S, if m < n then f m n else 0) +
          ∑ n ∈ S, ∑ m ∈ S, if m < n then f n m else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmn : m < n <;> simp [hmn]
  rw [hpairs]
  rw [show (∑ n ∈ S, ∑ m ∈ S, if m < n then f n m else 0) =
      ∑ m ∈ S, ∑ n ∈ S, if n < m then f m n else 0 by
        rw [Finset.sum_comm]]
  have hdiag :
      (∑ n ∈ S, f n n) =
        ∑ m ∈ S, ∑ n ∈ S, if m = n then f m n else 0 := by
    symm
    apply Finset.sum_congr rfl
    intro m hm
    simpa [eq_comm, hm] using Finset.sum_ite_eq' S m (fun n => f m n)
  rw [hdiag]
  rw [show (∑ x ∈ S, ∑ m ∈ S, if m < x then f m x else 0) =
      ∑ m ∈ S, ∑ n ∈ S, if m < n then f m n else 0 by
        rw [Finset.sum_comm]]
  rw [← add_assoc, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rcases lt_trichotomy m n with hlt | heq | hgt
  · simp [hlt, hlt.ne, hlt.not_gt]
  · subst n
    simp
  · simp [hgt, hgt.ne', hgt.not_gt]

/-- The exact logarithmic Dirichlet-polynomial integral is its explicit
diagonal plus the paired off-diagonal contribution. -/
theorem logarithmicDirichletPolynomial_integral_eq_diagonal_add_pairs
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    (∫ t in U..2 * U,
        starRingEnd ℂ (logarithmicDirichletPolynomial W c t) *
          logarithmicDirichletPolynomial W c t) =
      (U : ℂ) * ∑ n ∈ Finset.Icc 1 W, starRingEnd ℂ (c n) * c n +
        complexSharpPairSum U W c := by
  rw [logarithmicDirichletPolynomial_integral_expansion]
  rw [sum_square_eq_diagonal_add_pairs]
  rw [logarithmicSharpDiagonal_eq]
  rfl

/-- The exact remainder after subtracting the diagonal obeys the finite
six-harmonic endpoint-energy bound. -/
theorem norm_logarithmic_mean_square_sub_diagonal_le
    (U : ℝ) (W : ℕ) (c : ℕ → ℂ) :
    ‖(∫ t in U..2 * U,
        starRingEnd ℂ (logarithmicDirichletPolynomial W c t) *
          logarithmicDirichletPolynomial W c t) -
        (U : ℂ) * ∑ n ∈ Finset.Icc 1 W, starRingEnd ℂ (c n) * c n‖ ≤
      6 * realHarmonicMass W * complexWeightedCoefficientEnergy W c := by
  rw [logarithmicDirichletPolynomial_integral_eq_diagonal_add_pairs]
  simp only [add_sub_cancel_left]
  exact norm_complexSharpPairSum_le U W c

/-- RC2 finite mean-square specialization.  The remaining error is expressed
directly through the exact two-range endpoint energy. -/
theorem norm_twoRange_mean_square_sub_diagonal_le
    (U x : ℝ) (W : ℕ) (a : ℕ → ℂ) :
    ‖(∫ t in U..2 * U,
        starRingEnd ℂ
            (logarithmicDirichletPolynomial W (twoRangeCoefficient x a) t) *
          logarithmicDirichletPolynomial W (twoRangeCoefficient x a) t) -
        (U : ℂ) * ∑ n ∈ Finset.Icc 1 W,
          starRingEnd ℂ (twoRangeCoefficient x a n) *
            twoRangeCoefficient x a n‖ ≤
      6 * realHarmonicMass W * twoRangeEndpointEnergy x W a := by
  simpa [complexWeightedCoefficientEnergy, twoRangeEndpointEnergy] using
    norm_logarithmic_mean_square_sub_diagonal_le
      U W (twoRangeCoefficient x a)

end ZetaLean.HigherXi
