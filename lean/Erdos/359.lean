/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Erdős problem 359

The statements below are vendored **verbatim** from `formal-conjectures/359.lean`:
`IsGoodFor`, `erdos_359.parts.i` and `erdos_359.variants.isGoodFor_1_low_values`,
copied exactly, with the literal `sorry` kept. The `sorry` is the advertised
open statement, not an uncertified step in a proof: do not restate, generalise,
weaken or specialise it, and do not "fix" it in this file.

Only the surrounding scaffolding (the header, `import Mathlib`, and the
`open Filter` needed for `atTop`) is ours; every line of the declarations
is upstream's. Upstream's `@[category ..., AMS ...]` attributes are dropped,
because they come from `FormalConjecturesUtil`, which is not vendored here.

`isGoodFor_1_low_values` is upstream's finite partial result: it is
`@[category test]` there rather than `research open`, and pins the first eight
terms of the sequence, [OEIS A002048](https://oeis.org/A002048).
-/

open Filter

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)



theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry

/-- Suppose monotone sequence $A$ satisfies the following: `A 0 = 1` and for all `j`, `A (j + 1)` is the
smallest natural number that cannot be written as a sum of consecutive terms of `A 0, ..., A j`.
Then the first few terms of $A$ are $1,2,4,5,8,10,14,15,...$. -/
theorem erdos_359.variants.isGoodFor_1_low_values (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    A '' (Set.Iic 7) = {1, 2, 4, 5, 8, 10, 14, 15} := by
  sorry
