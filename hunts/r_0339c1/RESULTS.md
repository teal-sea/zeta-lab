# R-0339C1 results — Hardy–Ramanujan, formalized in half

**Outcome: not settled.** The Hardy–Ramanujan theorem is *not* proved. What is
proved, kernel-checked with zero `sorry`s, is the Chebyshev half of Turán's
argument as an implication, plus the unconditional first step of the other
half. The wall is named below, and it is a specific Mathlib absence, not a
tactic that failed.

## What compiles

`lean/ZetaLean/HardyRamanujantheorem.lean`, 146 lines, imported from
`lean/ZetaLean.lean`. `lake build ZetaLean.HardyRamanujantheorem` printed:

```
✔ [8697/8697] Built ZetaLean.HardyRamanujantheorem (10s)
Build completed successfully (8697 jobs).
```

Zero `sorry`s. The only occurrence of the string in the file is the word inside
the module docstring. All four results use standard axioms only:

```
'ZetaLean.HardyRamanujan.primeFactors_eq_filter' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.HardyRamanujan.sum_omega_eq_sum_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.HardyRamanujan.card_exceptional_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZetaLean.HardyRamanujan.hardyRamanujan_of_turanVariance' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### The statement

`HardyRamanujanTheorem` is the density form: for every `ε > 0`,

```
#{ n ∈ (0, N] : |ω n − log log N| > ε · log log N } / N → 0   as N → ∞.
```

It is a `def ... : Prop`. It is stated, not proved, and the file says so in its
docstring rather than leaving a reader to infer it.

### The two theorems

**1. `sum_omega_eq_sum_div` (unconditional).**

```
∑_{n ∈ (0,N]} ω n = ∑_{p ∈ (0,N], p prime} N / p        (Nat division, so ⌊N/p⌋)
```

This is genuinely the first step of Turán's variance estimate and it is
unconditional. Proof is double counting: rewrite `ω n` as the count of primes in
`(0, N]` dividing `n` (`primeFactors_eq_filter`, which needs `n ≤ N` to know no
prime factor escapes the window), expand both cards as indicator sums, swap with
`Finset.sum_comm`, and evaluate the inner sum with
`Nat.Ioc_filter_dvd_card_eq_div`.

**2. `hardyRamanujan_of_turanVariance` (an implication, not the theorem).**

```
TuranVariance → HardyRamanujanTheorem
```

where `TuranVariance` is `∃ C, ∀ᶠ N, ∑_{n ∈ (0,N]} (ω n − log log N)² ≤ C·N·log log N`.
This is the whole Chebyshev half, with the Chebyshev inequality itself isolated
as `card_exceptional_mul_le`: on the exceptional set each summand is at least
`(ε log log N)²`, so `#E · (ε log log N)² ≤ V`; divide by `N`, and the bound
`C / (ε² log log N)` goes to `0` because `log log N → ∞`.

**`TuranVariance` is a hypothesis in this file, not a theorem.** The implication
is therefore a reduction. It is not the Hardy–Ramanujan theorem and the file
must not be read as containing it.

## The obstruction, precisely

The remaining half is the variance estimate, and it stops at one missing input.

**Mertens' second theorem is not in Mathlib.** `grep -rln "Mertens\|mertens"`
over the pinned checkout (`v4.33.0-rc2`, `.lake/packages/mathlib/Mathlib/`)
returns exactly one file, `Mathlib/RingTheory/Polynomial/ContentIdeal.lean`, and
that hit is an unrelated identifier. There is no

```
∑_{p ≤ x} 1/p = log log x + M + O(1/log x)
```

nor its weaker cousin `∑_{p ≤ x} 1/p = log log x + O(1)`, under that name or any
other I could find.

What Mathlib does have, and why each one is not enough:

| Declaration | File | Why it does not close the gap |
| --- | --- | --- |
| `Nat.Ioc_filter_dvd_card_eq_div` | `Data/Nat/Factorization/Basic.lean` | Used, and it is what makes step 1 work. Counts multiples, says nothing about `∑ 1/p`. |
| `Nat.card_multiples`, `Nat.card_multiples'` | `Data/Nat/Factorization/Basic.lean` | Same content in `range` form. |
| `not_summable_one_div_on_primes`, `Nat.Primes.not_summable_one_div` | `NumberTheory/SumPrimeReciprocals.lean` | Divergence of `∑ 1/p` only. Qualitative; carries no rate, so it cannot produce `log log x`. |
| `Nat.Primes.summable_rpow` | `NumberTheory/SumPrimeReciprocals.lean` | Convergence iff exponent `< −1`. Again no asymptotic at the boundary. |
| `Nat.primeCounting`, `tendsto_primeCounting` | `NumberTheory/PrimeCounting.lean` | `π` diverges. No Chebyshev-type `π x ≍ x / log x` bound stated as an asymptotic here. |
| `Nat.ArithmeticFunction.cardDistinctFactors` (`ω`) | `NumberTheory/ArithmeticFunction.lean` | The definition of `ω` and its multiplicativity. Nothing about its distribution. |
| `Mathlib/NumberTheory/AbelSummation.lean` | | The summation-by-parts machinery Mertens is normally derived through. Present, but the derivation itself is not. |
| `Mathlib/NumberTheory/Chebyshev.lean` | | Chebyshev polynomials, not Chebyshev's prime bounds. A name collision worth flagging to the next attempt. |

Searched for and **not found**: `Mertens`, `sum_one_div_prime`, `primeCounting`
asymptotics, `sum_primesBelow_one_div`, any `IsBigO`/`IsEquivalent` statement
about a sum over primes, and any normal-order or `Filter`-density statement
about `ω` or `Ω`.

So the honest chain for the missing half is:

1. Chebyshev's bound `θ x = O(x)` or `π x = O(x / log x)`.
2. Abel summation (available) against that bound to get
   `∑_{p ≤ x} 1/p = log log x + O(1)`.
3. `∑_{n ≤ N} ω n = N log log N + O(N)` from step 1 of this file plus (2).
4. The second moment `∑_{n ≤ N} ω(n)² `, which needs the same estimate applied
   to pairs `p ≠ q` and the square of Mertens, and is where the `O(N log log N)`
   comes from.
5. `TuranVariance`, then this file's implication.

Steps 1 and 2 are each a substantial formalization on their own. Nothing about
them is deep; they are simply not in the library, and neither fits a 60 minute
budget alongside a cold Mathlib fetch.

## What the run actually cost, in shape

Roughly two thirds of the budget went to environment, not mathematics: `elan`
was not installed, `lean/.lake` did not exist, and `lake exe cache get` pulled
8,681 files (about 6.2 GB) before a single line could be checked. Three
compile-edit cycles were then enough, at about 10 s each once Mathlib's `.olean`
files were warm. The three fixes were: `div_le_div_iff` is now `div_le_div_iff₀`
in this Mathlib; a `sq_le_sq'` detour parse-errored and cascaded through the
rest of the file, masking otherwise-correct proofs; and `nsmul_eq_mul` wants
`↑n * a`, so the `mul_comm` before it was wrong.

## Scope

Nothing here is evidence for or against RH (`docs/08`). The reserved word that
`zeta/rigor.py` and the Lean arm own is not claimed anywhere in this hunt, and
the lexical ban on it under `hunts/` is respected to the byte. The two theorems
that exist are **kernel-checked**, which is the rung the certainty ladder gives
them; the target statement is not proved at all and carries no rung.

## Loose threads

- **Mertens' second theorem is the reusable object, not Hardy–Ramanujan.**
  `∑_{p ≤ x} 1/p = log log x + O(1)` is what is actually missing from Mathlib,
  and it is upstream of Hardy–Ramanujan, Erdős–Kac, and the normal order of
  `Ω(n)` alike. A hunt aimed at Mertens rather than at Hardy–Ramanujan would
  buy more per unit of formalization.
- **Chebyshev's `θ x = O(x)` may be closer than it looks.** `Mathlib/NumberTheory/Bertrand.lean`
  and `Primorial.lean` both carry central-binomial-coefficient bounds of the
  kind Chebyshev's proof uses. Whether either exposes a reusable `θ x ≤ c x` was
  not checked; that check is cheap and was outside this budget.
- **`Mathlib/NumberTheory/Chebyshev.lean` is about Chebyshev polynomials.** Any
  future search for prime-counting bounds that greps for "Chebyshev" will land
  there first and waste a cycle.
- **The second moment needs a pair version of step 1.** `∑_{n ≤ N} ω(n)² `
  expands into `∑_{p,q ≤ N} ⌊N/pq⌋` over ordered pairs of distinct primes plus
  the diagonal. The diagonal is step 1 again; the off-diagonal wants
  `Nat.Ioc_filter_dvd_card_eq_div` applied to `p*q`, which is available. So
  step 4 above is mostly bookkeeping once step 2 exists.
- **`SelbergSieve.lean` exists in this Mathlib.** Not examined. If it carries a
  usable prime-sum estimate as a byproduct, the chain above may be shorter than
  five steps.
