/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.MatchingCount

/-!
# Local structure of two-colour matching unions

This file records the graph-free structural consequences needed by the RAMS2
cluster expansion.  Each colour is a matching, so at most one edge of each
colour is incident to a vertex.  A connected pair on a support of size at
least two covers every support vertex.  Consequently every vertex has coloured
degree one or two; degree two means one incident edge of each colour.

The final theorem isolates the cycle-type parity constraint: if every support
vertex has coloured degree two, both colours are perfect matchings, their edge
counts agree, and the support has even cardinality.  No global path/cycle
classification or component enumeration is asserted here.
-/

namespace ZetaLean.HigherXi

open Finset

variable {α : Type*} [DecidableEq α]

/-- Edges of one colour incident to a vertex. -/
def incidentEdges (M : Finset (Finset α)) (p : α) : Finset (Finset α) :=
  M.filter fun e ↦ p ∈ e

/-- Degree in the coloured union.  An edge appearing in both matchings is
counted once in each colour. -/
def matchingPairColoredDegree
    (M₁ M₂ : Finset (Finset α)) (p : α) : ℕ :=
  (incidentEdges M₁ p).card + (incidentEdges M₂ p).card

/-- One matching contributes at most one incident edge at any vertex. -/
theorem card_incidentEdges_le_one
    {M : Finset (Finset α)} (hM : IsFiniteMatching M) (p : α) :
    (incidentEdges M p).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro e f he hf
  have he' := Finset.mem_filter.mp he
  have hf' := Finset.mem_filter.mp hf
  by_contra hef
  have hdisjoint := hM e he'.1 f hf'.1 hef
  exact (Finset.disjoint_left.mp hdisjoint) he'.2 hf'.2

/-- The coloured union of two matchings has degree at most two. -/
theorem matchingPairColoredDegree_le_two
    {M₁ M₂ : Finset (Finset α)}
    (hM₁ : IsFiniteMatching M₁) (hM₂ : IsFiniteMatching M₂) (p : α) :
    matchingPairColoredDegree M₁ M₂ p ≤ 2 := by
  unfold matchingPairColoredDegree
  have h₁ := card_incidentEdges_le_one hM₁ p
  have h₂ := card_incidentEdges_le_one hM₂ p
  omega

omit [DecidableEq α] in
/-- Two distinct incident edges in one matching cannot occur. -/
theorem eq_of_mem_matching_of_common_vertex
    {M : Finset (Finset α)} (hM : IsFiniteMatching M)
    {e f : Finset α} (he : e ∈ M) (hf : f ∈ M)
    {p : α} (hpe : p ∈ e) (hpf : p ∈ f) :
    e = f := by
  by_contra hef
  exact (Finset.disjoint_left.mp (hM e he f hf hef)) hpe hpf

/-- Distinct union edges meeting at a vertex have opposite available colours.
This is the local alternation constraint behind the path/even-cycle picture. -/
theorem distinct_incident_edges_have_opposite_colours
    {M₁ M₂ : Finset (Finset α)}
    (hM₁ : IsFiniteMatching M₁) (hM₂ : IsFiniteMatching M₂)
    {e f : Finset α} (he : e ∈ M₁ ∪ M₂) (hf : f ∈ M₁ ∪ M₂)
    {p : α} (hpe : p ∈ e) (hpf : p ∈ f) (hef : e ≠ f) :
    (e ∈ M₁ ∧ f ∈ M₂) ∨ (e ∈ M₂ ∧ f ∈ M₁) := by
  rcases Finset.mem_union.mp he with he₁ | he₂
  · rcases Finset.mem_union.mp hf with hf₁ | hf₂
    · exact False.elim (hef (eq_of_mem_matching_of_common_vertex
        hM₁ he₁ hf₁ hpe hpf))
    · exact Or.inl ⟨he₁, hf₂⟩
  · rcases Finset.mem_union.mp hf with hf₁ | hf₂
    · exact Or.inr ⟨he₂, hf₁⟩
    · exact False.elim (hef (eq_of_mem_matching_of_common_vertex
        hM₂ he₂ hf₂ hpe hpf))

/-- Edges in either concrete matching remain two-element subsets of the
ambient support. -/
theorem mem_union_matchingFamily_is_edge
    {S : Finset α} {M₁ M₂ : Finset (Finset α)}
    (hM₁ : M₁ ∈ matchingFamily S) (hM₂ : M₂ ∈ matchingFamily S)
    {e : Finset α} (he : e ∈ M₁ ∪ M₂) :
    e ∈ S.powersetCard 2 := by
  rcases Finset.mem_union.mp he with he₁ | he₂
  · exact (mem_matchingFamily_iff.mp hM₁).1 he₁
  · exact (mem_matchingFamily_iff.mp hM₂).1 he₂

/-- Cut connectivity on a support of size at least two forces every support
vertex to lie on an edge of the matching union. -/
theorem exists_incident_union_edge_of_connected
    {S : Finset α} {M₁ M₂ : Finset (Finset α)}
    (hcard : 2 ≤ S.card) (hconnected : MatchingPairConnected S M₁ M₂)
    {p : α} (hp : p ∈ S) :
    ∃ e ∈ M₁ ∪ M₂, p ∈ e := by
  unfold MatchingPairConnected at hconnected
  rcases hconnected with hsmall | hcuts
  · omega
  · have hsingleton : {p} ∈ S.powerset :=
      Finset.mem_powerset.mpr (by simpa using hp)
    have hnonempty : ({p} : Finset α).Nonempty := Finset.singleton_nonempty p
    have hne : ({p} : Finset α) ≠ S := by
      intro heq
      have : S.card = 1 := by rw [← heq]; simp
      omega
    obtain ⟨e, he, hcross⟩ := hcuts {p} hsingleton hnonempty hne
    refine ⟨e, he, ?_⟩
    simpa [Finset.disjoint_left] using hcross.1

/-- A connected concrete matching pair covers its whole support when the
support has at least two vertices. -/
theorem coveredVertices_union_eq_support_of_connected
    {S : Finset α} {M₁ M₂ : Finset (Finset α)}
    (hM₁ : M₁ ∈ matchingFamily S) (hM₂ : M₂ ∈ matchingFamily S)
    (hcard : 2 ≤ S.card) (hconnected : MatchingPairConnected S M₁ M₂) :
    coveredVertices (M₁ ∪ M₂) = S := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨e, he, hpe⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_powersetCard.mp
      (mem_union_matchingFamily_is_edge hM₁ hM₂ he)).1 hpe
  · intro p hp
    obtain ⟨e, he, hpe⟩ :=
      exists_incident_union_edge_of_connected hcard hconnected hp
    exact Finset.mem_biUnion.mpr ⟨e, he, hpe⟩

/-- Every vertex of a connected concrete pair has coloured degree one or two.
These are respectively the local endpoint and interior cases of the
path/even-cycle picture. -/
theorem connected_coloredDegree_between_one_and_two
    {S : Finset α} {M₁ M₂ : Finset (Finset α)}
    (hM₁ : M₁ ∈ matchingFamily S) (hM₂ : M₂ ∈ matchingFamily S)
    (hcard : 2 ≤ S.card) (hconnected : MatchingPairConnected S M₁ M₂)
    {p : α} (hp : p ∈ S) :
    1 ≤ matchingPairColoredDegree M₁ M₂ p ∧
      matchingPairColoredDegree M₁ M₂ p ≤ 2 := by
  have hm₁ := (mem_matchingFamily_iff.mp hM₁).2
  have hm₂ := (mem_matchingFamily_iff.mp hM₂).2
  constructor
  · obtain ⟨e, he, hpe⟩ :=
      exists_incident_union_edge_of_connected hcard hconnected hp
    rcases Finset.mem_union.mp he with he₁ | he₂
    · have hmem : e ∈ incidentEdges M₁ p := Finset.mem_filter.mpr ⟨he₁, hpe⟩
      have hpos : 0 < (incidentEdges M₁ p).card :=
        Finset.card_pos.mpr ⟨e, hmem⟩
      unfold matchingPairColoredDegree
      omega
    · have hmem : e ∈ incidentEdges M₂ p := Finset.mem_filter.mpr ⟨he₂, hpe⟩
      have hpos : 0 < (incidentEdges M₂ p).card :=
        Finset.card_pos.mpr ⟨e, hmem⟩
      unfold matchingPairColoredDegree
      omega
  · exact matchingPairColoredDegree_le_two hm₁ hm₂ p

/-- Coloured degree two means exactly one incident edge of each colour. -/
theorem coloredDegree_eq_two_iff
    {M₁ M₂ : Finset (Finset α)}
    (hM₁ : IsFiniteMatching M₁) (hM₂ : IsFiniteMatching M₂) (p : α) :
    matchingPairColoredDegree M₁ M₂ p = 2 ↔
      (incidentEdges M₁ p).card = 1 ∧ (incidentEdges M₂ p).card = 1 := by
  have h₁ := card_incidentEdges_le_one hM₁ p
  have h₂ := card_incidentEdges_le_one hM₂ p
  unfold matchingPairColoredDegree
  omega

/-- Coloured degree one means exactly one colour supplies the endpoint edge. -/
theorem coloredDegree_eq_one_iff
    {M₁ M₂ : Finset (Finset α)} (p : α) :
    matchingPairColoredDegree M₁ M₂ p = 1 ↔
      ((incidentEdges M₁ p).card = 1 ∧ (incidentEdges M₂ p).card = 0) ∨
      ((incidentEdges M₁ p).card = 0 ∧ (incidentEdges M₂ p).card = 1) := by
  unfold matchingPairColoredDegree
  omega

/-- Cycle-type parity constraint.  If every support vertex has coloured degree
two, each colour covers the support exactly once.  Hence both colours contain
the same number of edges and the support cardinality is even. -/
theorem full_coloredDegree_two_forces_even
    {S : Finset α} {M₁ M₂ : Finset (Finset α)}
    (hM₁ : M₁ ∈ matchingFamily S) (hM₂ : M₂ ∈ matchingFamily S)
    (hdegree : ∀ p ∈ S, matchingPairColoredDegree M₁ M₂ p = 2) :
    Even S.card ∧ M₁.card = M₂.card := by
  have hm₁ := (mem_matchingFamily_iff.mp hM₁).2
  have hm₂ := (mem_matchingFamily_iff.mp hM₂).2
  have hcover₁ : coveredVertices M₁ = S := by
    apply Finset.Subset.antisymm
    · exact coveredVertices_subset_of_mem_matchingFamily hM₁
    · intro p hp
      have hincident := (coloredDegree_eq_two_iff hm₁ hm₂ p).mp (hdegree p hp)
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (incidentEdges M₁ p).card)
      have he' := Finset.mem_filter.mp he
      exact Finset.mem_biUnion.mpr ⟨e, he'.1, he'.2⟩
  have hcover₂ : coveredVertices M₂ = S := by
    apply Finset.Subset.antisymm
    · exact coveredVertices_subset_of_mem_matchingFamily hM₂
    · intro p hp
      have hincident := (coloredDegree_eq_two_iff hm₁ hm₂ p).mp (hdegree p hp)
      obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (incidentEdges M₂ p).card)
      have he' := Finset.mem_filter.mp he
      exact Finset.mem_biUnion.mpr ⟨e, he'.1, he'.2⟩
  have hcard₁ := card_coveredVertices_of_mem_matchingFamily hM₁
  have hcard₂ := card_coveredVertices_of_mem_matchingFamily hM₂
  rw [hcover₁] at hcard₁
  rw [hcover₂] at hcard₂
  constructor
  · exact ⟨M₁.card, by omega⟩
  · omega

end ZetaLean.HigherXi
