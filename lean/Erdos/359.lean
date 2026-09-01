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
That one is ours and it is proved, so the only `sorry` left in this file is the
vendored one on `erdos_359.parts.i`.
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
  obtain ⟨hA0, hmono, hleast⟩ := hA
  -- The induction is on the index `j`, not on `N`: what has to be climbed is the ladder
  -- `A 0 < A 1 < ⋯`, and every `N` below `A j` is settled in one step from the `j`-th rung.
  -- Unboundedness (`j ≤ A j`, from strict monotonicity on `ℕ`) then puts every `N` under
  -- some rung, namely the `N`-th.
  suffices H : ∀ j N, n ≤ N → N ≤ A j → ∃ a b : ℕ, a ≤ b ∧ N = ∑ i ∈ Finset.Icc a b, A i from
    H N N hN hmono.le_apply
  intro j
  induction j with
  | zero =>
    -- Nothing below the bottom rung: `n ≤ N ≤ A 0 = n`, so `N = A 0` is the one-term block.
    intro N hn hle
    rw [hA0] at hle
    refine ⟨0, 0, le_rfl, ?_⟩
    rw [Finset.Icc_self, Finset.sum_singleton, hA0]
    omega
  | succ j ih =>
    intro N hn hle
    rcases le_or_gt N (A j) with h | h
    · exact ih N hn h
    rcases eq_or_lt_of_le hle with rfl | hlt
    · -- `N = A (j + 1)`: its own one-term block `Finset.Icc (j + 1) (j + 1)`.
      exact ⟨j + 1, j + 1, le_rfl, by rw [Finset.Icc_self, Finset.sum_singleton]⟩
    -- `A j < N < A (j + 1)`. `A (j + 1)` is a *lower* bound on the non-representables above
    -- `A j`, so `N` is not one of them; as `A j < N` does hold, the failure is representability.
    have hNS : ¬(A j < N ∧ ∀ a b : ℕ, Finset.Icc a b ⊆ Finset.Iic j →
        N ≠ ∑ i ∈ Finset.Icc a b, A i) := fun hmem =>
      absurd ((hleast j).2 hmem) (not_le.mpr hlt)
    push Not at hNS
    obtain ⟨a, b, -, heq⟩ := hNS h
    refine ⟨a, b, ?_, heq⟩
    -- The block is nonempty: an empty `Finset.Icc a b` would force `N = 0`, yet `A j < N`.
    by_contra hab
    rw [Finset.Icc_eq_empty hab, Finset.sum_empty] at heq
    omega
