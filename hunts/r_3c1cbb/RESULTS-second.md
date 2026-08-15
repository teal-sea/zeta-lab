# Hunt R-3C1CBB continuation results: Mertens's second theorem

Continuation run `05c755d3-1e75-4596-98b3-34ca2c084175`, building on run
`ed50af7f` (Hunt #30), which landed the first theorem and route-mapped the
second. This run built exactly the block that route map named, and nothing
else.

## What compiles

One new file, `lean/ZetaLean/MertensSecond.lean` (351 lines), importing
`ZetaLean.Mertensstheorems`, plus its import line in `lean/ZetaLean.lean`.
It builds against the pinned Mathlib v4.33.0-rc2 with **zero sorrys**
(`grep -c sorry` on the file: 0). No existing Lean file was edited.

The full-package build after adding the file printed:

```
✔ [8744/8745] Built ZetaLean (4.1s)
Build completed successfully (8745 jobs).
```

The targeted build of the new module alone printed:

```
✔ [2763/2763] Built ZetaLean.MertensSecond (19s)
Build completed successfully (2763 jobs).
```

## The statement that landed

In namespace `ZetaLean.Mertens`, sums over `Finset.Ioc 0 N` filtered on
`Nat.Prime`:

* `mertens_second_theorem`: for **every** natural `N`,
  `|Σ_{p ≤ N} 1/p − log log N| ≤ 76`.
  (For `N ≤ 1` the sum is empty and `log (log N) = 0` under Mathlib's
  `log 0 = 0` convention, so the bound is trivial there; the content is
  `N ≥ 2`, carried by `mertens_second_theorem_of_two_le`.)

This is the second theorem in the `log log x + O(1)` form that the mission
targeted, with an explicit constant. It is not the sharper
`log log x + M + o(1)` form: the Mertens constant `M` is untouched, exactly
as scoped. The constant `76` is explicit and far from optimal (Mertens's own
error bound is below 4 for the classical argument); it inherits the
deliberately slack `log 4 + 16` band from `mertens_first_theorem` twice,
each time through a factor `1/log 2 < 2`, plus `1 + |log log 2| + 4·Σ 1/n²`
for the termwise comparison. A numerical spot check (sieve to `10^6`):
the true deviation `|Σ 1/p − log log N|` decreases toward the Mertens
constant `≈ 0.2615` from `≈ 0.87` at `N = 2`, so the slack is a factor of
roughly 88 against the worst case, all of it inherited from named local
steps.

## How the block was closed

The predecessor's route was followed as written, with one deviation worth
recording:

1. `sum_inv_primes_eq`: the discrete Abel identity
   `Σ_{p ≤ N} 1/p = A(N)/log N + Σ_{n=2}^{N−1} A(n)(1/log n − 1/log(n+1))`
   with `A(n) = Σ_{p ≤ n} log p / p`. The deviation: rather than reindexing
   Mathlib's range-indexed `Finset.sum_range_by_parts` to `Ioc`/`Icc` (the
   predecessor's plan, estimated as the main labor), the identity is proved
   directly by induction from `N = 2` using `Finset.sum_Ioc_succ_top` /
   `Finset.sum_Ico_succ_top`: the increment of both sides at `N + 1` is
   `1/(N+1)` when `N + 1` is prime and `0` otherwise, one `field_simp; ring`
   per case. That killed the reindexing labor entirely.
2. The drift band `|A(n) − log n| ≤ log 4 + 16` is
   `mertens_first_theorem` from the predecessor's file, consumed as-is.
3. The termwise comparison runs through the elementary bracket
   `(v−u)/v ≤ log v − log u ≤ (v−u)/u` (`log_sub_log_le`,
   `sub_div_le_log_sub_log`, from `Real.log_le_sub_one_of_pos` and
   `Real.one_sub_inv_le_log_of_pos`), applied at `u = log n`,
   `v = log(n+1)`. The lower application telescopes to
   `log log N − log log 2` exactly; the upper application overshoots by
   `(log(n+1) − log n)²/(log n · log(n+1)) ≤ 4/n²`
   (`log_sub_log_le_mul_add`, using `log n ≥ log 2 > 1/2` via
   `Real.log_two_gt_d9`).
4. The error sums close by telescoping (`sum_Ico_telescope`) and Mathlib's
   `sum_Ioc_inv_sq_le_sub` at `k = 1` (`sum_inv_sq_Ico_le_one`,
   `Σ_{n=2}^{N−1} 1/n² ≤ 1`), exactly as the route predicted.
5. Final assembly is interval arithmetic in `linarith` with
   `Real.log_two_gt_d9` / `log_two_lt_d9` discharging the numerics:
   `|Σ 1/p − log log N| ≤ 1 + |log log 2| + 4 + 2(log 4 + 16)/log 2 < 76`.

The route map's estimate was 150 to 250 lines; the block came in at 351
lines including doc comments, or about 300 lines of proof text, at the top
of that band but inside one session as predicted. No new mathematics was
needed, as predicted.

## Mathlib declarations relied on

New to this file (the first theorem's inputs are listed in `RESULTS.md`):

- `Real.log_le_sub_one_of_pos`, `Real.one_sub_inv_le_log_of_pos` (both
  halves of the log bracket), `Real.log_div`, `Real.log_pow`,
  `Real.log_neg`, `Real.log_le_log`, `Real.log_pos`.
- `Real.log_two_gt_d9`, `Real.log_two_lt_d9`
  (`Mathlib.Analysis.Complex.ExponentialBounds`) for every numeric
  discharge.
- `sum_Ioc_inv_sq_le_sub` (`Mathlib.Analysis.PSeries`) for `Σ 1/n²`.
- `Finset.sum_Ioc_succ_top`, `Finset.sum_Ico_succ_top`, `Finset.sum_filter`
  for the induction steps; `Finset.sum_le_sum`,
  `Finset.sum_le_sum_of_subset_of_nonneg`, `Finset.sum_add_distrib`,
  `Finset.sum_sub_distrib`, `Finset.mul_sum`, `Finset.sum_neg_distrib` for
  the assembly.
- `inv_anti₀`, `div_le_iff₀`, `mul_inv_cancel₀`, `div_eq_div_iff`,
  `div_sub_div`, `div_right_comm` for the field manipulation.
- `Nat.le_induction` as the induction principle throughout.

Looked for and not needed after the route deviation:
`Finset.sum_range_by_parts` (the reindexing it would have required was the
predecessor's 150-to-250-line estimate; direct induction replaced it).

## What was checked

- `lake build` exit 0 on the module alone and on the full package, zero
  sorrys by grep, no warnings on the new file.
- The statement was numerically spot-checked against a sieve to `10^6`
  (deviation `0.87` at `N = 2` falling toward `0.2615`), confirming the
  formalized inequality is the classical second theorem and not a
  restatement or a vacuous form.

## Loose threads

- The constant `76` decomposes as
  `1 + |log log 2| + 4·(Σ 1/n²) + 2(log 4 + 16)/log 2` before rounding;
  nearly all of it is the inherited `log 4 + 16` band. Tightening the first
  theorem's band (already a recorded thread of Hunt #30) mechanically
  tightens this constant to about `4 + 4/log 2 ≈ 9.8` with no change to
  this file's structure.
- The direct-induction Abel pattern (`sum_inv_primes_eq` plus
  `sum_Ico_telescope`) is smaller and more reusable than the planned
  `sum_range_by_parts` reindex; the same shape would close other
  partial-summation arguments in the Lean arm (any weight `f(n)` with
  `f` monotone on `[2, ∞)`), and is a candidate for extraction if a second
  consumer appears.
- The third theorem (`Π_{p≤x}(1 − 1/p) ~ e^{−γ}/log x`) remains out of
  elementary reach, unchanged from `RESULTS.md`: it needs the Mertens
  constant and the Euler-Mascheroni comparison, neither of which this
  toolkit touches.
- The `log log x + M + o(1)` strengthening would need `M` defined in Lean
  (as `γ + Σ_p (log(1−1/p) + 1/p)` or via the limit), which is a genuinely
  new formalization target, not a tightening of this file.

Nothing here is evidence for or against RH.
