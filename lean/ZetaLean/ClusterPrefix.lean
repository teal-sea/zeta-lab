/-
Copyright (c) 2026 Thomas Lince. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Thomas Lince
-/
import ZetaLean.AristotleRAMS2

/-!
# Finite monomer-dimer coefficients and square-mass clusters

This file gives the finite combinatorial interface needed before the analytic
RAMS2 prefix estimate.  A support `S` has a finite family of matchings.  Each
matching contributes the product of its dimer weights and the monomer weights
of its uncovered vertices.  Squaring the resulting coefficient is exactly a
sum over two coloured matchings.

The union of the two matchings is declared connected by the finite cut
criterion: every nonempty proper subset of the support is crossed by an edge.
The pair sum then splits exactly into connected and disconnected terms.  After
summing over integer supports through `N`, this becomes an identity for
`prefixMass`.  No growth estimate or asymptotic statement is assumed here.
-/

namespace ZetaLean.HigherXi

open Finset

section Matchings

variable {α R : Type*} [DecidableEq α] [CommRing R]

/-- A finite edge family is a matching when distinct edges are disjoint. -/
def IsFiniteMatching (M : Finset (Finset α)) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f

/-- All matchings on `S`.  Edges are two-element subsets of `S`. -/
noncomputable def matchingFamily (S : Finset α) : Finset (Finset (Finset α)) := by
  classical
  exact (S.powersetCard 2).powerset.filter IsFiniteMatching

omit [DecidableEq α] in
theorem mem_matchingFamily_iff {S : Finset α} {M : Finset (Finset α)} :
    M ∈ matchingFamily S ↔
      M ⊆ S.powersetCard 2 ∧ IsFiniteMatching M := by
  classical
  simp [matchingFamily]

/-- The vertices covered by a finite edge family. -/
def coveredVertices (M : Finset (Finset α)) : Finset α := M.biUnion id

/-- One monomer-dimer term.  Every selected edge contributes a dimer weight;
every uncovered support vertex contributes a monomer weight. -/
def matchingTerm (M : Finset (Finset α)) (vertexSupport : Finset α)
    (monomer : α → R) (dimer : Finset α → R) : R :=
  (∏ e ∈ M, dimer e) *
    ∏ p ∈ vertexSupport \ coveredVertices M, monomer p

/-- The finite monomer-dimer coefficient on `S`. -/
noncomputable def monomerDimerCoefficient (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) : R :=
  ∑ M ∈ matchingFamily S, matchingTerm M S monomer dimer

/-- The exact two-colour matching sum obtained after taking the square. -/
noncomputable def matchingPairMass (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) : R :=
  ∑ MN ∈ matchingFamily S ×ˢ matchingFamily S,
    matchingTerm MN.1 S monomer dimer * matchingTerm MN.2 S monomer dimer

/-- An edge crosses a cut when it meets both sides. -/
def EdgeCrosses (A e : Finset α) : Prop := ¬Disjoint A e ∧ ¬e ⊆ A

/-- Connectivity of the union of two matchings, expressed by the exact finite
cut criterion.  Empty and singleton supports are connected by convention. -/
def MatchingPairConnected (S : Finset α) (M₁ M₂ : Finset (Finset α)) : Prop :=
  S.card ≤ 1 ∨
    ∀ A ∈ S.powerset, A.Nonempty → A ≠ S →
      ∃ e ∈ M₁ ∪ M₂, EdgeCrosses A e

/-- Connected part of the two-colour matching mass. -/
noncomputable def connectedMatchingMass (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) : R := by
  classical
  exact ∑ MN ∈ (matchingFamily S ×ˢ matchingFamily S).filter
      (fun MN => MatchingPairConnected S MN.1 MN.2),
    matchingTerm MN.1 S monomer dimer * matchingTerm MN.2 S monomer dimer

/-- Disconnected part of the two-colour matching mass. -/
noncomputable def disconnectedMatchingMass (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) : R := by
  classical
  exact ∑ MN ∈ (matchingFamily S ×ˢ matchingFamily S).filter
      (fun MN => ¬MatchingPairConnected S MN.1 MN.2),
    matchingTerm MN.1 S monomer dimer * matchingTerm MN.2 S monomer dimer

/-- Squaring a monomer-dimer coefficient gives the exact two-colour matching
sum.  This is the finite Hadamard-square step, before any absolute values. -/
theorem monomerDimerCoefficient_sq_eq_matchingPairMass (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) :
    monomerDimerCoefficient S monomer dimer ^ 2 =
      matchingPairMass S monomer dimer := by
  classical
  simp only [monomerDimerCoefficient, matchingPairMass, pow_two,
    Finset.sum_product, Finset.mul_sum, mul_comm]

/-- The two-colour matching mass is exactly the sum of its connected and
disconnected pieces. -/
theorem matchingPairMass_eq_connected_add_disconnected (S : Finset α)
    (monomer : α → R) (dimer : Finset α → R) :
    matchingPairMass S monomer dimer =
      connectedMatchingMass S monomer dimer +
        disconnectedMatchingMass S monomer dimer := by
  classical
  unfold matchingPairMass connectedMatchingMass disconnectedMatchingMass
  exact (Finset.sum_filter_add_sum_filter_not
    (matchingFamily S ×ˢ matchingFamily S)
    (fun MN => MatchingPairConnected S MN.1 MN.2)
    (fun MN => matchingTerm MN.1 S monomer dimer *
      matchingTerm MN.2 S monomer dimer)).symm

end Matchings

section PrefixMass

variable {α : Type*} [DecidableEq α]

/-- The coefficient square mass through `N`, with the squarefree label support
of integer `n` supplied by `support n`. -/
noncomputable def monomerDimerPrefixMass (support : ℕ → Finset α)
    (monomer : ℕ → α → ℝ) (dimer : ℕ → Finset α → ℝ) (N : ℕ) : ℝ :=
  prefixMass (fun n =>
    monomerDimerCoefficient (support n) (monomer n) (dimer n) ^ 2) N

/-- Exact reduction of the coefficient prefix square mass to the sum of
connected and disconnected two-colour matching masses on every support. -/
theorem monomerDimerPrefixMass_eq_connected_add_disconnected
    (support : ℕ → Finset α) (monomer : ℕ → α → ℝ)
    (dimer : ℕ → Finset α → ℝ) (N : ℕ) :
    monomerDimerPrefixMass support monomer dimer N =
      (∑ n ∈ Finset.Icc 1 N,
        connectedMatchingMass (support n) (monomer n) (dimer n)) +
      ∑ n ∈ Finset.Icc 1 N,
        disconnectedMatchingMass (support n) (monomer n) (dimer n) := by
  classical
  simp only [monomerDimerPrefixMass, prefixMass,
    monomerDimerCoefficient_sq_eq_matchingPairMass,
    matchingPairMass_eq_connected_add_disconnected, Finset.sum_add_distrib]

end PrefixMass

end ZetaLean.HigherXi
