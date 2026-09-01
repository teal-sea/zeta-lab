/-
Copyright (c) 2026 Zeta Lab. All rights reserved.
Released under MIT license.
-/
import Mathlib

/-!
# Porubský's 1977 lemma (Erdős problem 359)

Erdős problem 359 concerns the greedy sequence `a₁ < a₂ < ⋯` with `a₁ = n` and
`a_{i+1}` the least integer that is *not* a sum of consecutive earlier terms.
For `n = 1` it begins `1, 2, 4, 5, 8, 10, 14, 15, …`, and Erdős asked whether
`a_k / k → ∞` while `a_k / k^{1+c} → 0` for every `c > 0`; the conjectured
truth is `a_k ∼ k log k / log log k`.

Such a greedy sequence has the property that **every** positive integer is a
sum of one or more *consecutive* terms of it: an integer that is not a sum of
consecutive earlier terms is itself enrolled as the next term, and a single
term is a sum of one consecutive term.  The discussion thread for problem 359
therefore quotes a general lemma about *any* sequence with that property,
attributed to Porubský (Nieuw Archief voor Wiskunde, 1977) and reached via
Guy, *Unsolved Problems in Number Theory* (1981):

> for every strictly increasing sequence `a_k` such that every positive
> integer can be written as a sum of one or more consecutive elements, and
> every `ε > 0`,
> `liminf_k (a_k · log log k) / (k · (log k)^{1+ε}) = 0`.

That lemma is the single statement this module carries.  It is one direction
of the expected `a_k ∼ k log k / log log k`: it says the ratio
`a_k log log k / (k log k)` cannot stay bounded away from `0` even after being
weakened by an arbitrarily small extra power of `log k`.

## Why this module is not in `ZetaLean`

`porubsky_liminf_eq_zero` below is a **statement only** and ends in `sorry`.
The lab's rule is that nothing in `ZetaLean/` counts until it compiles with
zero `sorry`s, and CI enforces that by grepping `ZetaLean/*.lean`.  This file
therefore sits outside the certified arm, alongside the other statement-only
surfaces (`Challenge.lean`, `DHChallenge.lean`), as its own `lean_lib`.  It is
in `defaultTargets`, so `lake build` still kernel-checks that the statement
elaborates; it just is not advertised as proved, because it is not.  Nothing
else in the repository imports it.

Only the surrounding prose is this repository's; the mathematical content is
Porubský's, restated.  No part of it is proved here, and no attempt at a proof
was made.

## Reading the statement

* `g : ℕ → ℕ` is the sequence, `StrictMono g` its strict increase.
* `IsConsecutiveSumComplete g` says every positive integer equals
  `g a + g (a+1) + ⋯ + g b` for some `a ≤ b`, which is what "a sum of one or
  more consecutive terms" means (`a = b` is the one-term case).
* The quotient is taken over `k : ℕ` along `Filter.atTop`, with `Real.log`
  and the real power `(log k) ^ (1 + ε)` (`Real.rpow`, since `1 + ε : ℝ`).
  The finitely many `k ≤ 2` where `log log k` and the denominator degenerate
  are irrelevant: `Filter.liminf _ atTop` depends only on eventual behaviour.
* The `liminf` is `Filter.liminf` into `ℝ`, which is a conditionally complete
  linear order; the sequence is bounded below by `0` from `k = 3` on, so the
  `liminf` is the honest one and not the junk value of an unbounded case.

## References

* erdosproblems.com, problem 359 and its discussion thread.
* Š. Porubský, *Nieuw Archief voor Wiskunde* (1977), as cited there.
* R. K. Guy, *Unsolved Problems in Number Theory* (1981).
-/

namespace ZetaLean.Erdos359

open Filter

/-- `IsConsecutiveSumComplete g` holds when every positive integer is a sum of
one or more consecutive terms of `g`: for every `n > 0` there are indices
`a ≤ b` with `n = g a + g (a + 1) + ⋯ + g b`. -/
def IsConsecutiveSumComplete (g : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ a b : ℕ, a ≤ b ∧ ∑ i ∈ Finset.Icc a b, g i = n

/-- The hypothesis class is not empty, so the lemma below is not vacuously
true: `g k = k + 1` is strictly increasing, and every positive `n` is the
one-term consecutive sum `g (n - 1)`.  This says nothing about Porubský's
lemma itself; it only checks that `StrictMono` together with
`IsConsecutiveSumComplete` is satisfiable. -/
theorem exists_strictMono_isConsecutiveSumComplete :
    ∃ g : ℕ → ℕ, StrictMono g ∧ IsConsecutiveSumComplete g := by
  refine ⟨fun k => k + 1, ?_, ?_⟩
  · intro a b hab
    change a + 1 < b + 1
    omega
  · intro n hn
    refine ⟨n - 1, n - 1, le_rfl, ?_⟩
    rw [Finset.Icc_self, Finset.sum_singleton]
    omega

/-- **Porubský (1977).**  For any strictly increasing `g : ℕ → ℕ` such that
every positive integer is a sum of one or more consecutive terms of `g`, and
every `ε > 0`,
`liminf_{k → ∞} (g k · log log k) / (k · (log k) ^ (1 + ε)) = 0`.

Stated as given in the erdosproblems.com discussion thread for problem 359
(sourced via Guy 1981).  Deliberately unproved: the `sorry` is the whole
content of the lemma, not a gap in some other argument. -/
theorem porubsky_liminf_eq_zero (g : ℕ → ℕ) (hmono : StrictMono g)
    (hcomplete : IsConsecutiveSumComplete g) (ε : ℝ) (hε : 0 < ε) :
    liminf (fun k : ℕ =>
        (g k : ℝ) * Real.log (Real.log (k : ℝ)) /
          ((k : ℝ) * Real.log (k : ℝ) ^ (1 + ε))) atTop = 0 := by
  sorry

end ZetaLean.Erdos359
