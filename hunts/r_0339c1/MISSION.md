# Hunt R-0339C1: formalize the Hardy–Ramanujan theorem

Two runs. **Run 1** (`16585a2a-04a0-4eda-925f-1a79df23d758`, branch
`hunt/r-0339c1`, budget 60 minutes) proved the Chebyshev half and the
double-counting first step, and named the wall: Mathlib has no Mertens second
theorem. **Run 2** (`43d363c1-71f0-4ebf-9d9d-632819f96794`, branch
`hunt/r-0339c1-43d363c1`, budget 90 minutes, this document) is the retry with
the wall removed: `ZetaLean.Mertens.mertens_second_theorem` now exists on
main with the explicit band `76`, and the remaining half is priced as
bookkeeping. Run 2's case-log entry is **Hunt #36**; run 1's is **Hunt #12**.
Both numbers were assigned by their briefs, not chosen.

## The statement targeted

The Hardy–Ramanujan theorem (Wikidata Q5656674; recorded by Mathlib as wanted
and unbuilt): the number of distinct prime factors `ω(n)` has **normal order**
`log log n`. In the density form Turán's proof establishes:

> for every `ε > 0`,
> `#{ n ≤ N : |ω(n) − log log N| > ε · log log N } / N → 0` as `N → ∞`.

Formalized in `lean/ZetaLean/HardyRamanujantheorem.lean`; the theorem is
`ZetaLean.HardyRamanujan.hardy_ramanujan`.

## What this hunt may write

`lean/ZetaLean/HardyRamanujantheorem.lean`, its import line in
`lean/ZetaLean.lean`, `hunts/r_0339c1/`, and one case-log entry in
`hunts/README.md`. Nothing else. Existing proofs, including run 1's lemmas
and the Mertens files, are not this hunt's to edit; run 1's lemmas are reused
by copying into the new file with attribution, since its branch is unmerged.

## The plan of run 2, from run 1's recorded threads

Turán's proof factors into two halves. Run 1 finished half 2 (Chebyshev) and
the first step of half 1. What remained, and what run 2 adds:

1. **First moment.** `∑_{n ≤ N} ω(n) = ∑_{p ≤ N} ⌊N/p⌋` (run 1's
   `sum_omega_eq_sum_div`), bracketed by `N·S(N) − N ≤ ∑ ω ≤ N·S(N)` where
   `S(N) = ∑_{p ≤ N} 1/p`, then `|S(N) − log log N| ≤ 76` by Mertens II.
2. **Second moment.** Expand `ω(n)²` over ordered pairs of primes; the
   diagonal is the first step again, the off-diagonal counts multiples of
   `p·q` via `Nat.Ioc_filter_dvd_card_eq_div` at `p*q` (distinct primes are
   coprime). Bound: `∑ ω(n)² ≤ N·S(N)² + N·S(N)`.
3. **Variance.** `∑ (ω(n) − log log N)² ≤ 5855·N·log log N` whenever
   `log log N ≥ 1`; the constant is coarse by design, inheriting Mertens's
   deliberately slack band twice (`76² + 76 + 3 ≤ 5855`).
4. **Assembly.** Run 1's `hardyRamanujan_of_turanVariance` closes the theorem.

```huntspec
id: r_0339c1
question: Can the Hardy–Ramanujan theorem be formalized in Lean 4 + Mathlib inside the budget now that Mertens second theorem exists on main, and if not, where precisely is the remaining wall?
frontier: main carries ZetaLean.Mertens.mertens_second_theorem with band 76 and run 1's kernel-checked Chebyshev half; Mathlib v4.33.0-rc2 itself still has no Mertens rate and no normal-order statement; the wanted-and-unbuilt record is Q5656674
proposed_attack: reuse run 1's halves, expand the second moment over ordered prime pairs with Nat.Ioc_filter_dvd_card_eq_div at p*q, and close Turan's variance bound with explicit constants against the Mertens band
dead_routes:
  - asserting the theorem with a sorry, which the Lean arm counts as nothing
  - restating the definitions in a compiling triviality and presenting it as the theorem
  - rebuilding or editing the Mertens files or any other existing proof
required_oracles:
  - the Lean 4 kernel via lake build, zero sorrys and standard axioms only
  - Mathlib declaration search over the pinned checkout, by name and by statement
kill_conditions:
  - the toolchain will not install or Mathlib will not fetch
  - the 90 minute budget is exhausted
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

```runmanifest
id: r_0339c1-2026-08-16-run2
hunt: r_0339c1
started: 2026-08-16T15:42Z
finished: 2026-08-16T16:40Z
ran:
  - cd lean && lake exe cache get
  - cd lean && lake build ZetaLean.HardyRamanujantheorem
  - cd lean && lake build
  - lake env lean (print axioms for the seven public results)
outcome: the Hardy-Ramanujan theorem compiles kernel-checked with zero sorrys as ZetaLean.HardyRamanujan.hardy_ramanujan, via Turan's variance bound with explicit constant 5855
artifacts:
  - lean/ZetaLean/HardyRamanujantheorem.lean
  - hunts/r_0339c1/RESULTS.md
  - hunts/r_0339c1/results.json
  - hunts/r_0339c1/HANDBACK.json
```
