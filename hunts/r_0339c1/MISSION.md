# Hunt R-0339C1 — formalize the Hardy–Ramanujan theorem

**Run id**: `16585a2a-04a0-4eda-925f-1a79df23d758` · **Branch**: `hunt/r-0339c1`
· **Budget**: 60 minutes, no operator supervision.

## The statement targeted

The Hardy–Ramanujan theorem (Wikidata Q5656674; recorded by Mathlib as wanted
and unbuilt): the number of distinct prime factors `ω(n)` has **normal order**
`log log n`. In the density form Turán's proof establishes:

> for every `ε > 0`,
> `#{ n ≤ N : |ω(n) − log log N| > ε · log log N } / N → 0` as `N → ∞`.

Formalized in `lean/ZetaLean/HardyRamanujantheorem.lean` as
`ZetaLean.HardyRamanujan.HardyRamanujan`.

## What this hunt may write

`lean/ZetaLean/HardyRamanujantheorem.lean`, its import line in
`lean/ZetaLean.lean`, `hunts/r_0339c1/`, and one case-log entry in
`hunts/README.md` as **Hunt #12** (a number assigned by the brief, not chosen).
Nothing else. Existing proofs are not this hunt's to edit.

## The plan, and the split it rests on

Turán's proof factors into two halves, and the split is the whole planning
decision here:

1. **The variance estimate** `∑_{n ≤ N} (ω(n) − log log N)² = O(N log log N)`.
   This is the hard half. It runs through Mertens' second theorem,
   `∑_{p ≤ N} 1/p = log log N + M + O(1/log N)`.
2. **The Chebyshev step**: half 1 implies the density statement.

Half 2 is elementary and self-contained. Half 1 is not, and whether it is
reachable inside the budget is exactly what the run measures. The honest
outcome on a target of this size is a named wall, and the brief says so.

```huntspec
id: r_0339c1
question: Can the Hardy–Ramanujan theorem be formalized in Lean 4 + Mathlib inside a 60 minute budget, and if not, where precisely is the wall?
frontier: Mathlib v4.33.0-rc2 has omega as ArithmeticFunction.cardDistinctFactors and no normal-order statement about it; the wanted-and-unbuilt record is Q5656674
proposed_attack: split Turan's proof at the variance estimate, formalize the Chebyshev half unconditionally and the double-counting first step of the variance half, then measure how far Mathlib's prime-sum estimates carry the rest
dead_routes:
  - asserting the theorem with a sorry, which the Lean arm counts as nothing
  - restating the definitions in a compiling triviality and presenting it as the theorem
required_oracles:
  - the Lean 4 kernel via lake build, zero sorrys and standard axioms only
  - Mathlib declaration search over the pinned checkout, by name and by statement
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - the 60 minute budget is exhausted
  - progress requires editing an existing proof in lean/
  - the remaining gap is a named Mathlib absence rather than a provable lemma
agents_may:
  - search
  - derive
  - code
  - formalize
  - report a wall as the result
agents_may_not:
  - declare novelty
  - declare theorem status for anything carrying a sorry
  - claim the reserved word that zeta/rigor.py and the Lean arm own
  - promote their own claim
```
