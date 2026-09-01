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
of the vendored declarations is upstream's.

Below the vendored statements sits *our* material: the reduction of
`erdos_359.parts.ii` to Andrews' conjectured asymptotic
`A k ~ k * log k / log (log k)`. Those lemmas are ours to prove, and their
`sorry`s are real holes, unlike the advertised ones above.
-/

open Filter Asymptotics

def IsGoodFor (A : ℕ → ℕ) (n : ℕ) : Prop := A 0 = n ∧ StrictMono A ∧
  ∀ j, IsLeast
    {m : ℕ | A j < m ∧ ∀ a b, Finset.Icc a b ⊆ Finset.Iic j → m ≠ ∑ i ∈ Finset.Icc a b, A i}
    (A <| j + 1)



theorem erdos_359.parts.i (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    atTop.Tendsto (fun k ↦ (A k : ℝ) / k) atTop := by
  sorry



theorem erdos_359.parts.ii (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry



theorem erdos_359.variants.isGoodFor_1_asymptotic (A : ℕ → ℕ) (hA : IsGoodFor A 1) :
    (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log) := by
  sorry

/-!
## Reduction of `erdos_359.parts.ii` to Andrews' asymptotic

Everything from here down is ours, not upstream's.

`erdos_359.variants.isGoodFor_1_asymptotic` above is Andrews' conjecture, that
a good sequence satisfies `A k ~ k * log k / log (log k)`. It implies
`erdos_359.parts.ii` on the nose, because the comparison function itself
already tends to `0` after dividing by `k ^ (1 + c)`:

`(k * log k / log (log k)) / k ^ (1 + c) = log k / (log (log k) * k ^ c) → 0`

for every `c > 0`, the `k ^ c` beating `log k` and the `log (log k)` only
helping. So the reduction is two steps: the scalar limit
`tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero`, and then transporting it
along the `IsEquivalent` in `parts_ii_of_andrews_asymptotic`.

Note what `parts_ii_of_andrews_asymptotic` does *not* take: it has no
`IsGoodFor A 1` hypothesis. The asymptotic alone carries the whole statement,
so the lemma is stated for an arbitrary `A : ℕ → ℕ`; goodness enters only when
it is composed with Andrews' conjecture.
-/

/-- The scalar half of the reduction: for `c > 0`,
`log k / (log (log k) * k ^ c) → 0` along `atTop`.

This is `(k * log k / log (log k)) / k ^ (1 + c)` after cancelling one factor
of `k`, i.e. exactly the limit that Andrews' comparison function has. -/
theorem tendsto_log_div_loglog_mul_rpow_atTop_nhds_zero (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k : ℕ ↦ (k : ℝ).log / ((k : ℝ).log.log * (k : ℝ) ^ c)) (nhds 0) := by
  sorry

/-- **Andrews' conjectured asymptotic implies `erdos_359.parts.ii`.**

If `A k ~ k * log k / log (log k)` then `A k / k ^ (1 + c) → 0` for every
`c > 0`. The conclusion is `erdos_359.parts.ii`'s verbatim, so
`erdos_359.variants.isGoodFor_1_asymptotic` composed with this lemma closes
part (ii). -/
theorem parts_ii_of_andrews_asymptotic (A : ℕ → ℕ)
    (hAsymp : (fun k ↦ (A k : ℝ)) ~[atTop] (fun k ↦ k * (k : ℝ).log / (k : ℝ).log.log))
    (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) := by
  sorry

/-- The composite, for the record: goodness plus Andrews' conjecture gives
part (ii). This is `erdos_359.parts.ii` with its proof outsourced, and is the
only declaration here that is not open in its own right once the two inputs
are discharged. -/
theorem parts_ii_of_isGoodFor_of_andrews (A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c) :
    atTop.Tendsto (fun k ↦ A k / (k : ℝ) ^ (1 + c)) (nhds 0) :=
  parts_ii_of_andrews_asymptotic A (erdos_359.variants.isGoodFor_1_asymptotic A hA) c hc
