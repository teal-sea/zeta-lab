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
`open Filter Asymptotics` needed for `atTop` and `~[·]`) is ours; every line
of the two declarations is upstream's.

Below those, `erdos_359.parts.i_of_isGoodFor_1_asymptotic` is **ours**: a
reduction saying that Andrews' conjectured asymptotic implies part (i). Its
hypothesis is the conclusion of upstream's
`erdos_359.variants.isGoodFor_1_asymptotic`, copied verbatim, and its
conclusion is the conclusion of `erdos_359.parts.i`, copied verbatim. It also
carries a `sorry`: the reduction is stated here, not proved here.
-/

open Filter Asymptotics

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)



theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry



/-- **Andrews' conjecture implies part (i).** If `A` is good for `1` and
satisfies the conjectured asymptotic $a_k \sim \frac{k \log k}{\log\log k}$
-- i.e. the conclusion of `erdos_359.variants.isGoodFor_1_asymptotic`, stated
here verbatim as a hypothesis -- then $a_k / k \to \infty$, which is the
conclusion of `erdos_359.parts.i`.

This is a reduction, not a proof of either: it is what turns the open
asymptotic into the open part (i). The `sorry` is the reduction itself, which
is a genuine (if far easier) piece of work: from
`A k ~ k log k / log log k` and `log k / log log k → ∞` one gets
`A k / k → ∞`. -/
theorem erdos_359.parts.i_of_isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1)
    (hasymp : (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log)) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry
