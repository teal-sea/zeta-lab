/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Erdős problem 359

The statement below is vendored **verbatim** from `formal-conjectures/359.lean`:
`IsGoodFor` and `erdos_359.parts.i`, copied exactly, with the literal `sorry`
kept. The `sorry` is the advertised open statement, not an uncertified step in
a proof: do not restate, generalise, weaken or specialise it, and do not
"fix" it in this file.

Only the surrounding scaffolding (the header, `import Mathlib`, and the
`open Filter` needed for `atTop`) is ours; every line of the two declarations
is upstream's.

Below the vendored block, and clearly separated from it, sits `IsGoodFor.exists_sum_Icc`:
the classical MacMahon completeness lemma that `IsGoodFor` encodes but never states.
That one is ours, and its `sorry` is an ordinary unproved step, not an advertised
open problem.
-/

open Filter

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)



theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

/- ---------------------------------------------------------------------------
End of the vendored block. Everything below is ours.
--------------------------------------------------------------------------- -/

/-- **MacMahon completeness.** The greedy condition in `IsGoodFor A n` never says outright
that `A` represents everything, but it forces exactly that above its first term: if
`IsGoodFor A n`, then every `N ≥ n` is a sum of a nonempty block of *consecutive* terms
of `A`.

The reason is the third clause of `IsGoodFor`, read in both directions. `A (j + 1)` is a
*least* element of the set of non-representable numbers above `A j`, so on the one hand
every `m` with `A j < m < A (j + 1)` fails membership, and since `A j < m` holds that
failure can only be representability, `m = ∑ i ∈ Finset.Icc a b, A i` for some block
inside `Finset.Iic j`; on the other hand each `A k` is its own one-term block
`Finset.Icc k k`, and `A 0 = n`. A strictly monotone `A : ℕ → ℕ` is unbounded, so every
`N ≥ n` is caught by one of those cases.

Stated with `a ≤ b` so that `Finset.Icc a b` is nonempty and the sum is a genuine
consecutive run rather than the empty sum. -/
theorem IsGoodFor.exists_sum_Icc {A : ℕ → ℕ} {n : ℕ} (hA : IsGoodFor A n) {N : ℕ}
    (hN : n ≤ N) : ∃ a b : ℕ, a ≤ b ∧ N = ∑ i ∈ Finset.Icc a b, A i := by
  sorry
