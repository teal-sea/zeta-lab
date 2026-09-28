import Mathlib

/-!
# Exact diagonal removal for the third cycle

For a symmetric kernel with unit diagonal, the pairwise-distinct-index triangle
is the all-index third cycle minus three second cycles plus twice the number
of indices. The two add-backs at a fully coincident triple are included.

The identity holds in any commutative ring, including the complex numbers.
Distinctness refers to index labels; different labels may represent equal
values of the underlying point multiset. This is an exact combinatorial
identity, not a new correlation estimate.
-/

open Finset
open scoped BigOperators

namespace CycleMoments

/-- Inclusion-exclusion for the three equality events of a triangle. -/
theorem distinct_triangle_indicator {R : Type*} [CommRing R] {n : Type*} [DecidableEq n]
    (K : n → n → R) (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1)
    (i j k : n) :
    (if i ≠ j ∧ j ≠ k ∧ k ≠ i then K i j * K j k * K k i else 0) =
      K i j * K j k * K k i
        - (if i = j then (K i k)^2 else 0)
        - (if j = k then (K i j)^2 else 0)
        - (if k = i then (K i j)^2 else 0)
        + (if i = j ∧ j = k then 2 else 0) := by
  by_cases hij : i = j <;> by_cases hjk : j = k <;> by_cases hki : k = i
  all_goals simp_all
  all_goals ring

/-- The all-index triangle with every repeated-index contribution removed exactly. -/
theorem distinct_triangle_identity {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (K : n → n → R) (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1) :
    (∑ i, ∑ j, ∑ k,
      if i ≠ j ∧ j ≠ k ∧ k ≠ i then K i j * K j k * K k i else 0) =
      (∑ i, ∑ j, ∑ k, K i j * K j k * K k i)
        - 3 * (∑ i, ∑ j, (K i j)^2) + 2 * (Fintype.card n : R) := by
  simp_rw [distinct_triangle_indicator K hsym hdiag]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_irrel, ite_and]
  ring


/-- The same identity with pairwise-distinct indices expressed by finite-set filters. -/
theorem distinct_triangle_filter_identity {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : n → n → R) (hsym : ∀ i j, K i j = K j i) (hdiag : ∀ i, K i i = 1) :
    (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i ≠ j),
      ∑ k ∈ Finset.univ.filter (fun k => j ≠ k ∧ k ≠ i), K i j * K j k * K k i) =
      (∑ i, ∑ j, ∑ k, K i j * K j k * K k i)
        - 3 * (∑ i, ∑ j, (K i j)^2) + 2 * (Fintype.card n : R) := by
  simpa [Finset.sum_filter, ite_and, Finset.sum_ite_irrel] using
    distinct_triangle_identity K hsym hdiag

/-- info: 'CycleMoments.distinct_triangle_indicator' depends on axioms: [propext] -/
#guard_msgs in #print axioms distinct_triangle_indicator
/-- info: 'CycleMoments.distinct_triangle_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms distinct_triangle_identity
/-- info: 'CycleMoments.distinct_triangle_filter_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms distinct_triangle_filter_identity

end CycleMoments
