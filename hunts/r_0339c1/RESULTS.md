# R-0339C1 results: Hardy–Ramanujan, settled

**Outcome: settled.** The Hardy–Ramanujan theorem is proved, kernel-checked
with zero `sorry`s: `ZetaLean.HardyRamanujan.hardy_ramanujan` establishes the
density form of Turán's argument, with every constant explicit. This closes
the hunt that run 1 (`16585a2a`, 2026-08-14) left at a named wall; the wall
was Mertens' second theorem, and it was removed by hunt r_3c1cbb
(`ZetaLean.Mertens.mertens_second_theorem`, band `76`, on main).

## What compiles

`lean/ZetaLean/HardyRamanujantheorem.lean`, 380 lines, imported from
`lean/ZetaLean.lean`. `lake build ZetaLean.HardyRamanujantheorem` printed:

```
✔ [8699/8699] Built ZetaLean.HardyRamanujantheorem (22s)
Build completed successfully (8699 jobs).
```

The module compiled on the first attempt; a subsequent full `lake build` of
the package is recorded in `results.json`. Zero `sorry`s: the string does not
occur in the file at all. All results use standard axioms only; `#print
axioms` on the seven public theorems printed, for each of
`hardy_ramanujan`, `turan_variance`, `sum_sq_dev_le`, `second_moment_upper`,
`first_moment_lower`, `sum_omega_sq_eq`, `sum_omega_eq_sum_div`:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

### The statement proved

`HardyRamanujanTheorem` is the density form (unchanged from run 1): for every
`ε > 0`,

```
#{ n ∈ (0, N] : |ω n − log log N| > ε · log log N } / N → 0   as N → ∞,
```

with `ω n = n.primeFactors.card` and `loglog N = Real.log (Real.log N)`.
`hardy_ramanujan : HardyRamanujanTheorem` is a theorem, not a hypothesis or a
reduction. Which form was landed, plainly: this is the **normal-order density
form at scale `N`** (deviation measured from `log log N`, the form Turán's
proof directly gives), not the pointwise-normalised variant with
`log log n` inside the counter. The variance bound is landed separately as
`sum_sq_dev_le` with the explicit constant `5855`, so the quantitative core
is available to later work independently of the limit statement.

### The proof, piece by piece

New in run 2 (the second moment and the assembly):

1. `card_dvd_pair`: for primes `p, q`, the number of `n ∈ (0, N]` divisible
   by both is `⌊N/p⌋` if `p = q` and `⌊N/(pq)⌋` otherwise. Distinct primes
   are coprime (`Nat.coprime_primes`), joint divisibility is divisibility by
   the product (`Nat.Coprime.mul_dvd_of_dvd_of_dvd`), and the count is
   `Nat.Ioc_filter_dvd_card_eq_div` applied at `p * q`. Run 1 priced this
   step "mostly bookkeeping once Mertens exists" and that is what it was.
2. `sum_omega_sq_eq`: `∑_{n ≤ N} ω(n)²` expanded over ordered pairs of
   primes, by squaring the indicator sum and swapping summation twice.
3. `second_moment_upper`: `∑_{n ≤ N} ω(n)² ≤ N·S² + N·S` with
   `S = ∑_{p ≤ N} 1/p`. The off-diagonal is dominated by the full square
   `N·S²` (the discarded diagonal of the square is nonnegative), the
   diagonal by `N·S`.
4. `first_moment_upper` / `first_moment_lower`:
   `N·S − N ≤ ∑_{n ≤ N} ω(n) ≤ N·S`, from run 1's double-counting identity
   plus the floor bracket `N/p − 1 < ⌊N/p⌋ ≤ N/p` and `π(N) ≤ N`.
5. `sum_sq_dev_le`: for every `N` with `1 ≤ log log N`,
   `∑_{n ≤ N} (ω(n) − log log N)² ≤ 5855 · N · log log N`. Writing
   `D = S − log log N`, the expansion of the square gives
   `V = M₂ − 2·L·M₁ + N·L²` and the moment bounds give
   `V ≤ N·D² + N·S + 2·N·L`; Mertens II (`|D| ≤ 76`) and `L ≥ 1` give
   `5776 + 76 + 3 ≤ 5855` as the constant. Coarse on purpose: the brief's
   bar is explicit constants of any size, and every slack step is local.
6. `turan_variance : TuranVariance` (the `∀ᶠ` form, constant `5855`), then
   `hardy_ramanujan` by run 1's `hardyRamanujan_of_turanVariance`.

Reused verbatim from run 1's branch (`hunt/r-0339c1`, unmerged; copied with
attribution in the module docstring because existing proofs are not this
run's to edit and the branch is not on main): the definitions (`omega`,
`loglog`, `exceptional`, the two `Prop`s), `primeFactors_eq_filter`,
`sum_omega_eq_sum_div`, `card_exceptional_mul_le`,
`hardyRamanujan_of_turanVariance`, `tendsto_loglog`. One new helper
`omega_eq_sum_ite` restates run 1's indicator step in filtered form for the
squaring.

From this repository's Lean arm (used, not edited):
`ZetaLean.Mertens.mertens_second_theorem` (`|∑_{p ≤ N} 1/p − log log N| ≤ 76`
for every natural `N`), which imports `mertens_first_theorem`.

## Mathlib declarations relied on

The load-bearing ones, all present at the pin (`v4.33.0-rc2`):

| Declaration | Role |
| --- | --- |
| `Nat.Ioc_filter_dvd_card_eq_div` | multiples of `d` in `(0, N]` number `⌊N/d⌋`; used at `d = p` and `d = p*q` |
| `Nat.coprime_primes`, `Nat.Coprime.mul_dvd_of_dvd_of_dvd` | distinct primes are coprime; `p ∣ n ∧ q ∣ n → pq ∣ n` |
| `Nat.cast_div_le` | `⌊N/d⌋ ≤ N/d` after casting to `ℝ` |
| `Nat.div_add_mod`, `Nat.mod_lt` | the lower floor bracket `N/d − 1 < ⌊N/d⌋` |
| `Finset.sum_mul_sum` | expanding `ω(n)²` over ordered pairs |
| `Finset.sum_comm`, `Finset.card_filter`, `Finset.sum_filter`, `Finset.filter_congr` | the double counting |
| `Finset.sum_ite_eq` | collapsing the diagonal of the pair sum |
| `Finset.card_nsmul_le_sum`, `squeeze_zero'` | run 1's Chebyshev step |
| `Real.tendsto_log_atTop`, `tendsto_natCast_atTop_atTop` | `log log N → ∞` |

Searched for and still **not found** in Mathlib: any Mertens-rate statement,
any normal-order statement about `ω` or `Ω`, and any Turán-variance analogue.
Run 1's finding stands: the library absence was real, and this repository's
`MertensSecond.lean` is what closed it.

## What the run cost, in shape

The environment was cold again (no elan, no `.lake`): toolchain install plus
`lake exe cache get` (8681 files) took roughly 12 minutes before the first
compile. The mathematics itself compiled on the first attempt at 22 s for the
module. Reading run 1's file and threads before writing anything is what made
that possible: the route, the trap list (`Chebyshev.lean` is polynomials, not
prime bounds) and the pricing of the off-diagonal step were all already paid
for.

## Scope

Nothing here is evidence for or against RH (`docs/08`). The reserved word
that `zeta/rigor.py` and the Lean arm own is not claimed anywhere in this
hunt, and the lexical ban on it under `hunts/` is respected to the byte. On
the certainty ladder the result is **kernel-checked**: `hardy_ramanujan` and
the chain under it are theorems under `propext`, `Classical.choice`,
`Quot.sound`, and may be called theorems. External review remains pending, as
it does for every claim this laboratory publishes.

## Loose threads

- **The constant `5855` is soft.** It inherits Mertens's deliberately coarse
  band `76` quadratically. Tightening `mertens_first_theorem`'s `log 4 + 16`
  would propagate automatically; the classical band is `4`, which would put
  the variance constant near `4² + 4 + 3 = 23`. Local work, no new ideas.
- **The pointwise form is a short step away.** The statement here normalises
  by `log log N` at scale `N`; the textbook variant with `log log n` needs
  only the standard comparison `log log n ~ log log N` on `(N^δ, N]` plus a
  trivial count below `N^δ`. All ingredients are now in the file.
- **Erdős–Kac is the natural next target.** The first two moments of `ω` are
  now formal; the central limit theorem for `(ω(n) − log log n)/√(log log n)`
  is the canonical continuation, though it needs either moment control to all
  orders or a formalised Berry–Esseen route, each a real project.
- **Mathlib upstreaming.** Q5656674 is a wanted-and-unbuilt record; this
  file, `MertensSecond.lean` and `Mertensstheorems.lean` are within polishing
  distance of a Mathlib contribution, but the normalisations (`Ioc 0 N`
  rather than `range`, explicit constants rather than `IsBigO`) would need
  aligning with Mathlib house style. That is operator-priced work.
- **`omega` vs `ArithmeticFunction.cardDistinctFactors`.** The file keeps run
  1's spelled-out `omega n = n.primeFactors.card`. A bridging lemma to the
  `ArithmeticFunction` coercion would cost three lines and make the result
  easier to cite from other Mathlib-facing work.
