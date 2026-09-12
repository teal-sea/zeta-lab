import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Roots

/-!
# Many roots of high multiplicity force a large degree

If a nonzero polynomial `P` over an integral domain vanishes to order at least `l` at every
point of a finite set `s`, then `#s * l ≤ deg P`.

The proof is the usual counting one: `P.roots` is a multiset whose multiplicity at `x` is
`rootMultiplicity x P`, and distinct points of `s` contribute disjointly to it, so
`#s * l ≤ ∑ x ∈ s, P.roots.count x ≤ card P.roots ≤ P.natDegree`.

This refines `Polynomial.card_le_degree_of_subset_roots`, which is the case `l = 1`.
-/

set_option autoImplicit false

open Finset

open scoped Polynomial

namespace Polynomial

/-- The sum of the multiplicities of `P.roots` over any finite set of points is at most the
total number of roots of `P` counted with multiplicity. -/
theorem sum_count_roots_le_card_roots {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (P : R[X]) (s : Finset R) :
    ∑ x ∈ s, P.roots.count x ≤ Multiset.card P.roots := by
  rw [← Multiset.toFinset_sum_count_eq P.roots,
    ← Finset.sum_subset (Finset.inter_subset_left (s₁ := s) (s₂ := P.roots.toFinset))
      (fun x hx hx' => Multiset.count_eq_zero.mpr fun hm =>
        hx' (Finset.mem_inter.2 ⟨hx, Multiset.mem_toFinset.2 hm⟩))]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

-- `hP` is part of the statement as required; the bound in fact also holds for `P = 0`.
set_option linter.unusedVariables false in
/-- A nonzero polynomial vanishing to order at least `l` at each of `#s` distinct points has
degree at least `#s * l`. -/
theorem card_mul_le_natDegree_of_le_rootMultiplicity {R : Type*} [CommRing R]
    [IsDomain R] {P : R[X]} (hP : P ≠ 0) (s : Finset R) (l : ℕ)
    (h : ∀ x ∈ s, l ≤ P.rootMultiplicity x) :
    s.card * l ≤ P.natDegree := by
  classical
  calc s.card * l = ∑ _x ∈ s, l := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ x ∈ s, P.roots.count x := Finset.sum_le_sum fun x hx => by
        rw [count_roots]; exact h x hx
    _ ≤ Multiset.card P.roots := sum_count_roots_le_card_roots P s
    _ ≤ P.natDegree := P.card_roots'

end Polynomial
