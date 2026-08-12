/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.ClusterPrefix

/-!
# Exact labelled matching counts

This file isolates the finite counting identity used by the squarefree RAMS2
cluster majorant.  A matching with `a` edges on `r` labelled vertices is
obtained by choosing its `2a` covered vertices and pairing them.  The pairing
count is defined recursively, so the construction is division-free in `ℕ`.

The resulting `matchingCount r a` is shown to satisfy both the factorial
formula

`r! / (2^a * a! * (r - 2a)!)`

on its natural range and the vertex-removal recurrence.  No analytic estimate,
connected-component classification, or RAMS2 asymptotic is asserted here.
-/

namespace ZetaLean.HigherXi

open Finset

/-- The number of pairings of `2a` labelled vertices. -/
def pairingCount : ℕ → ℕ
  | 0 => 1
  | a + 1 => (2 * a + 1) * pairingCount a

@[simp]
theorem pairingCount_zero : pairingCount 0 = 1 := rfl

@[simp]
theorem pairingCount_succ (a : ℕ) :
    pairingCount (a + 1) = (2 * a + 1) * pairingCount a := rfl

/-- The number of matchings with exactly `a` edges on `r` labelled vertices. -/
def matchingCount (r a : ℕ) : ℕ :=
  r.choose (2 * a) * pairingCount a

@[simp]
theorem matchingCount_zero_edges (r : ℕ) : matchingCount r 0 = 1 := by
  simp [matchingCount]

/-- There are no `a`-edge matchings when fewer than `2a` vertices are
available. -/
theorem matchingCount_eq_zero_of_lt {r a : ℕ} (h : r < 2 * a) :
    matchingCount r a = 0 := by
  simp [matchingCount, Nat.choose_eq_zero_of_lt h]

/-- The recursive pairing count clears the denominator in the standard
factorial expression `(2a)! / (2^a a!)`. -/
theorem pairingCount_mul_pow_two_mul_factorial (a : ℕ) :
    pairingCount a * (2 ^ a * a.factorial) = (2 * a).factorial := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [pairingCount_succ, pow_succ, Nat.factorial_succ]
      calc
        (2 * a + 1) * pairingCount a *
              (2 ^ a * 2 * ((a + 1) * a.factorial)) =
            (2 * a + 2) * (2 * a + 1) *
              (pairingCount a * (2 ^ a * a.factorial)) := by ring
        _ = (2 * a + 2) * (2 * a + 1) * (2 * a).factorial := by rw [ih]
        _ = (2 * (a + 1)).factorial := by
          rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
            Nat.factorial_succ,
            show 2 * a + 1 = 2 * a + 1 by rfl, Nat.factorial_succ]
          ring

/-- Denominator-cleared form of the exact labelled matching count. -/
theorem matchingCount_mul_denominator_eq_factorial {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a *
        (2 ^ a * a.factorial * (r - 2 * a).factorial) = r.factorial := by
  rw [matchingCount]
  calc
    (r.choose (2 * a) * pairingCount a) *
          (2 ^ a * a.factorial * (r - 2 * a).factorial) =
        r.choose (2 * a) *
          (pairingCount a * (2 ^ a * a.factorial)) *
            (r - 2 * a).factorial := by ring
    _ = r.choose (2 * a) * (2 * a).factorial *
          (r - 2 * a).factorial := by
      rw [pairingCount_mul_pow_two_mul_factorial]
    _ = r.factorial := Nat.choose_mul_factorial_mul_factorial h

/-- The factorial formula used as `N(r,a)` in the RAMS2 squarefree cluster
majorant. -/
theorem matchingCount_eq_factorial_div {r a : ℕ} (h : 2 * a ≤ r) :
    matchingCount r a =
      r.factorial /
        (2 ^ a * a.factorial * (r - 2 * a).factorial) := by
  apply Nat.eq_div_of_mul_eq_right
  · positivity
  · rw [mul_comm]
    exact matchingCount_mul_denominator_eq_factorial h

/-- Removing one distinguished vertex either leaves it unmatched or pairs it
with one of the other vertices.  This recurrence characterizes the same exact
labelled count without division. -/
theorem matchingCount_add_two_succ (r a : ℕ) :
    matchingCount (r + 2) (a + 1) =
      matchingCount (r + 1) (a + 1) +
        (r + 1) * matchingCount r a := by
  unfold matchingCount
  rw [show r + 2 = (r + 1) + 1 by omega,
    show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
    Nat.choose_succ_succ', pairingCount_succ]
  have hchoose :
      (r + 1) * r.choose (2 * a) =
        (r + 1).choose (2 * a + 1) * (2 * a + 1) :=
    Nat.add_one_mul_choose_eq r (2 * a)
  rw [show (r + 1) * (r.choose (2 * a) * pairingCount a) =
      ((r + 1) * r.choose (2 * a)) * pairingCount a by ring, hchoose]
  ring

section MatchingFamilyBridge

variable {α : Type*} [DecidableEq α]

/-- The `a`-edge slice of the concrete matching family from `ClusterPrefix`. -/
noncomputable def matchingSlice (S : Finset α) (a : ℕ) :
    Finset (Finset (Finset α)) := by
  classical
  exact (matchingFamily S).filter fun M ↦ M.card = a

omit [DecidableEq α] in
theorem mem_matchingSlice_iff {S : Finset α} {a : ℕ}
    {M : Finset (Finset α)} :
    M ∈ matchingSlice S a ↔ M ∈ matchingFamily S ∧ M.card = a := by
  classical
  simp [matchingSlice]

/-- Disjoint two-element edges cover exactly twice as many vertices as there
are edges.  This is the structural cardinality invariant behind the matching
count. -/
theorem card_coveredVertices_eq_two_mul_card
    {M : Finset (Finset α)}
    (hmatching : IsFiniteMatching M)
    (hedge : ∀ e ∈ M, e.card = 2) :
    (coveredVertices M).card = 2 * M.card := by
  have hpair : (M : Set (Finset α)).PairwiseDisjoint id := by
    intro e he f hf hef
    exact hmatching e he f hf hef
  rw [coveredVertices, Finset.card_biUnion hpair]
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact hedge e he
    _ = 2 * M.card := by simp [mul_comm]

/-- Every member of `matchingFamily S` satisfies the exact covered-vertex
cardinality invariant. -/
theorem card_coveredVertices_of_mem_matchingFamily
    {S : Finset α} {M : Finset (Finset α)}
    (hM : M ∈ matchingFamily S) :
    (coveredVertices M).card = 2 * M.card := by
  have hm := mem_matchingFamily_iff.mp hM
  apply card_coveredVertices_eq_two_mul_card hm.2
  intro e he
  exact (Finset.mem_powersetCard.mp (hm.1 he)).2

/-- A concrete matching covers only vertices of its ambient support. -/
theorem coveredVertices_subset_of_mem_matchingFamily
    {S : Finset α} {M : Finset (Finset α)}
    (hM : M ∈ matchingFamily S) :
    coveredVertices M ⊆ S := by
  intro p hp
  obtain ⟨e, heM, hpe⟩ := Finset.mem_biUnion.mp hp
  exact (Finset.mem_powersetCard.mp ((mem_matchingFamily_iff.mp hM).1 heM)).1 hpe

/-- Every member of the `a`-edge slice covers exactly `2a` support vertices. -/
theorem card_coveredVertices_of_mem_matchingSlice
    {S : Finset α} {a : ℕ} {M : Finset (Finset α)}
    (hM : M ∈ matchingSlice S a) :
    (coveredVertices M).card = 2 * a := by
  have hs := mem_matchingSlice_iff.mp hM
  rw [card_coveredVertices_of_mem_matchingFamily hs.1, hs.2]

omit [DecidableEq α] in
/-- A nonempty `a`-edge slice forces at least `2a` ambient vertices. -/
theorem two_mul_le_card_of_mem_matchingSlice
    {S : Finset α} {a : ℕ} {M : Finset (Finset α)}
    (hM : M ∈ matchingSlice S a) :
    2 * a ≤ S.card := by
  classical
  rw [← card_coveredVertices_of_mem_matchingSlice hM]
  exact Finset.card_le_card
    (coveredVertices_subset_of_mem_matchingFamily (mem_matchingSlice_iff.mp hM).1)

omit [DecidableEq α] in
/-- Above the natural range, the concrete matching slice is empty. -/
theorem matchingSlice_eq_empty_of_card_lt {S : Finset α} {a : ℕ}
    (h : S.card < 2 * a) :
    matchingSlice S a = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro M hM
  exact (Nat.not_le_of_lt h) (two_mul_le_card_of_mem_matchingSlice hM)

omit [DecidableEq α] in
/-- The concrete and arithmetic matching counts agree throughout the empty
range `S.card < 2a`. -/
theorem card_matchingSlice_eq_matchingCount_of_card_lt
    {S : Finset α} {a : ℕ} (h : S.card < 2 * a) :
    (matchingSlice S a).card = matchingCount S.card a := by
  classical
  rw [matchingSlice_eq_empty_of_card_lt h,
    matchingCount_eq_zero_of_lt h]
  simp

omit [DecidableEq α] in
/-- The zero-edge slice consists only of the empty matching. -/
theorem matchingSlice_zero (S : Finset α) :
    matchingSlice S 0 = {∅} := by
  classical
  ext M
  constructor
  · intro hM
    have hs := mem_matchingSlice_iff.mp hM
    have hzero : M = ∅ := Finset.card_eq_zero.mp hs.2
    simp [hzero]
  · intro hM
    have hzero : M = ∅ := by simpa using hM
    subst M
    apply mem_matchingSlice_iff.mpr
    exact ⟨mem_matchingFamily_iff.mpr ⟨by simp, by simp [IsFiniteMatching]⟩, by simp⟩

omit [DecidableEq α] in
/-- The concrete zero-edge matching slice has the exact cardinality predicted
by `matchingCount`. -/
theorem card_matchingSlice_zero (S : Finset α) :
    (matchingSlice S 0).card = matchingCount S.card 0 := by
  classical
  rw [matchingSlice_zero]
  simp

/-- The one-edge slice is exactly the singleton image of the two-element
subsets of the support. -/
theorem matchingSlice_one (S : Finset α) :
    matchingSlice S 1 = (S.powersetCard 2).image singleton := by
  classical
  ext M
  constructor
  · intro hM
    have hs := mem_matchingSlice_iff.mp hM
    obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp hs.2
    have he : e ∈ S.powersetCard 2 := hs.1 |> mem_matchingFamily_iff.mp |>.1 (by simp)
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · intro hM
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hM
    apply mem_matchingSlice_iff.mpr
    constructor
    · apply mem_matchingFamily_iff.mpr
      constructor
      · intro f hf
        have hfe : f = e := Finset.mem_singleton.mp hf
        simpa [hfe] using he
      · simp [IsFiniteMatching]
    · simp

omit [DecidableEq α] in
/-- The concrete one-edge matching slice has the exact cardinality predicted
by `matchingCount`. -/
theorem card_matchingSlice_one (S : Finset α) :
    (matchingSlice S 1).card = matchingCount S.card 1 := by
  classical
  rw [matchingSlice_one, Finset.card_image_of_injective _ Finset.singleton_injective,
    Finset.card_powersetCard]
  simp [matchingCount]

end MatchingFamilyBridge

end ZetaLean.HigherXi
