# Hunt R-3C1CBB results: Mertens's theorems in the Lean arm

## What compiles

One new file, `lean/ZetaLean/Mertensstheorems.lean` (409 lines), plus its
import line in `lean/ZetaLean.lean`. It builds against the pinned Mathlib
v4.33.0-rc2 with **zero sorrys** (`grep -c sorry` on the file: 0).

The full-package build after adding the file printed:

```
✔ [8743/8744] Built ZetaLean (5.2s)
Build completed successfully (8744 jobs).
```

The targeted build of the new module alone printed:

```
✔ [2758/2758] Built ZetaLean.Mertensstheorems (8.1s)
Build completed successfully (2758 jobs).
```

## The statements that landed

All in namespace `ZetaLean.Mertens`, all for natural `N` with the sums over
`Finset.Ioc 0 N`:

1. `sum_log_eq_sum_vonMangoldt_mul_div`:
   `Σ_{n≤N} log n = Σ_{d≤N} Λ(d) · ⌊N/d⌋`.
2. `sum_log_le`, `sum_log_ge`: `N log N − N + 1 ≤ Σ_{n≤N} log n ≤ N log N`
   for `N ≥ 1`, the lower bound by induction from `log(1+1/M) ≤ 1/M`
   rather than any integral comparison or Stirling input.
3. `abs_sum_vonMangoldt_div_sub_log_le` (Mertens's first theorem, von
   Mangoldt form): for `N ≥ 1`,
   `|Σ_{n≤N} Λ(n)/n − log N| ≤ log 4 + 4`.
4. `mertens_first_theorem` (prime form): for `N ≥ 1`,
   `|Σ_{p≤N, p prime} (log p)/p − log N| ≤ log 4 + 16`.

Supporting lemmas built on the way: `sum_inv_mul_sqrt_le`
(`Σ_{n≤N} 1/(n√n) ≤ 3 − 2/√N`, telescoping), `sum_log_div_sq_le`
(`Σ_{n≤N} (log n)/n² ≤ 6`), `sum_geom_tail_le`
(`Σ_{k=2}^{K} 2⁻ᵏ ≤ 2⁻¹ − 2⁻ᴷ`), `psi_natCast`.

The constants `log 4 + 4` and `log 4 + 16` are explicit and deliberately
slack (the classical error in the prime form is bounded by 2). They are
what the elementary argument yields with no numerical case analysis; every
slack step is local and could be tightened independently.

## Mathlib declarations relied on

- `ArithmeticFunction.vonMangoldt_sum` (`Σ_{d∣n} Λ(d) = log n`), plus
  `vonMangoldt_nonneg`, `vonMangoldt_apply_prime`, `vonMangoldt_apply_pow`,
  `vonMangoldt_ne_zero_iff`.
- `Nat.Ioc_filter_dvd_card_eq_div` (counting multiples: the divisor swap).
- `Chebyshev.psi_le_const_mul_self` (`ψ(x) ≤ (log 4 + 4)·x`) and
  `Chebyshev.sum_PrimePow_eq_sum_sum` (prime-power double-sum
  decomposition), both from `Mathlib.NumberTheory.Chebyshev`, which was
  upstreamed in part from the PrimeNumberTheoremAnd project.
- `Nat.cast_div_le`, `Nat.sub_one_lt_floor`, `Nat.floor_div_natCast`
  (floor-division bracketing).
- `Real.log_le_sub_one_of_pos`, `Real.log_sqrt`, `Real.sq_sqrt`,
  `Real.rpow_le_self_of_one_le`.

## What was looked for and the state of the field

- **No Mertens statement exists in this Mathlib.** `grep -ril mertens`
  over the pinned tree hits only `RingTheory/Polynomial/ContentIdeal.lean`
  (the Dedekind-Mertens content lemma, unrelated). The Q1196729 target was
  genuinely unbuilt at this pin.
- The operator addendum's worry that a Chebyshev upper bound would be the
  missing input is resolved: this Mathlib carries a full
  `Mathlib/NumberTheory/Chebyshev.lean` (ψ, θ, two-sided bounds,
  `theta_le_log4_mul_x`, `psi_le_const_mul_self`). The addendum's note
  that `Chebyshev.lean` is about polynomials is out of date at this pin.
- `Mathlib/NumberTheory/AbelSummation.lean` exists
  (`sum_mul_eq_sub_sub_integral_mul` and variants). It is integral-form
  Abel summation with `deriv f` and `MeasureTheory` integrability side
  conditions.
- `Mathlib/NumberTheory/SumPrimeReciprocals.lean` has divergence of
  `Σ 1/p` only, no rate.
- Looked for and not found: any `log log` asymptotic for prime sums; a
  partial-sum bound for `Σ n^(-3/2)` (built by hand as
  `sum_inv_mul_sqrt_le`; `Mathlib/Analysis/PSeries.lean` has the `1/n²`
  analogue `sum_Ioc_inv_sq_le_sub` but nothing at exponent 3/2); a
  discrete (Finset-indexed, derivative-free) Abel summation suited to
  weights `1/log n`.

## The obstruction for the second theorem

Mertens's second theorem in the in-budget form
`|Σ_{p≤N} 1/p − log log N| ≤ C` reduces, given `mertens_first_theorem`,
to one summation-by-parts argument: write `1/p = (log p/p)·(1/log p)`,
sum by parts against `A(n) = Σ_{p≤n} log p/p = log n + O(1)`, and compare
`Σ_{n} (log(n+1)−log n)/log(n+1)` with `log log N` termwise through
`log v − log u ∈ [(v−u)/v, (v−u)/u]`. Every ingredient is elementary and
the error terms close (`Σ 1/n²` via `sum_Ioc_inv_sq_le_sub`,
`1/log 2` factors from the `O(1)` band). What is missing is purely the
Lean labor of the discrete partial summation: Mathlib's
`Finset.sum_range_by_parts` is range-indexed and the reindex to
`Ioc`/`Icc` with the prime indicator weight, plus the termwise log-log
comparison, is an estimated 150 to 250 further lines. It was route-mapped
but not started, because the remaining budget could not absorb an
unfinished 200-line construction and a file with a sorry is worth less
than this report. A next attempt should budget 60 to 90 minutes for
exactly that block and nothing else; no new mathematics is needed.

The third theorem (`Π(1−1/p) ~ e^{−γ}/log x`) additionally needs the
Mertens constant and the Euler-Mascheroni comparison; it is not in reach
of this elementary toolkit and was not attempted.

## Loose threads

- The constants are slack by design. `log 4 + 4` in the von Mangoldt form
  loses about 4 against the classical bound; the prime form's `+16`
  carries a factor of roughly 6 of slack from three local coarse steps
  (`log n ≤ 2√n`, the `1/(n√n)` telescope entered at `n = 1`, and the
  geometric factor 4). Tightening any of them is independent local work.
- The second theorem is one 150-to-250-line discrete Abel block away, as
  mapped above. That block (Finset summation by parts against a bounded
  drift, with `1/log` weights) would also be reusable for other
  partial-summation arguments in the Lean arm.
- A `Σ n^(-s)` partial-sum bound for non-integer `s` (here hand-built at
  `s = 3/2`) looks like a small upstreamable gap in
  `Mathlib/Analysis/PSeries.lean`, which has the `s = 2` case.
- `Chebyshev.lean` at this pin also carries `primeCounting`-vs-θ integral
  identities that would shorten a future π(x)-form Mertens statement.
