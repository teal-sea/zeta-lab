# Minimizing the factorial certificate B_N itself

Comparison, 2026-09-06, the third objective on the pilot's seed family. It is separate from
`../factorial_full_cost/`, whose record and conclusions (`COST_COMPARISON.md`) are left
unchanged, and from the preserved pilot in `../factorial_certificate_pilot/`. Script
`direct_bn.py`, record `direct_bn_results.json`, pinned by `tests/test_factorial_direct_bn.py`.

**Label.** A finite comparison of LP objectives on one seed family. Not an asymptotic
theorem, not an LP-optimality proof, not a prime-counting record, and nothing here bears
on RH (`docs/08`). Grade: *measured*, every accepted seed rechecked exactly.

## The question

The two earlier objectives were proxies for the certificate: the pilot minimized the
leading constant `C`, and `full_cost.py` minimized the proved bound `U_N`, which turned out
to move the certificate the wrong way. This comparison minimizes the certificate value
itself,

    B_N(a) = sum_{k=0}^K sum_{j|L} a_j log(floor(N/(j M^k))!),   K = floor(log_M N),

which for fixed `(L, M, N)` is linear in the seed: `B_N(a) = sum_j w_j a_j` with
`w_j = sum_k log(floor(N/(j M^k))!)`. Same constraints as the pilot, unchanged; same sizes
(`L in {30, 210, 2310}`, `M = 2..30`); same cutoffs `N in {10^4, 10^6, 10^8, 10^12}`; the
same 348 rows. Compared on `B_N` against BOTH the pilot's seed and the full-cost seed.

## Method

- The LP minimizes `sum_j (w_j/N) a_j` over the pilot's polytope (HiGHS, tolerances 1e-10);
  the `w_j` are computed at 50 digits and handed to the solver as floats. The LP only
  proposes: `Fraction(x).limit_denominator(10^6)` reconstructs, and every constraint is
  rechecked in integers by the same `exact_verify` that `full_cost.py` uses, imported
  from it so the constraint set is literally the same code.
- Fallback rule: the pilot's seed is the certificate of record. The direct proposal is
  adopted only if it re-verifies exactly AND its `B_N` is strictly below the pilot seed's.
  A worse or rejected proposal leaves the pilot seed in place and the row says so. Nothing
  worse was ever accepted, and no row needed the fallback for a worse or rejected proposal.
- All three seeds are evaluated on `B_N` at 50 digits from their exact rationals.
  Log-factorials only; no prime data used or produced.

## Results

**Counts.** 348 rows; 0 rejected reconstructions; 334 rows where the direct LP returns the
pilot's seed exactly; 14 rows where it strictly improves `B_N`; 0 rows worse than the
pilot's seed; 0 ties with a different seed. Against the full-cost seed the direct seed is
never worse and strictly better in 31 rows (the 30 rows where the full-cost seed differs
from the pilot's, by 15 to 312, plus one row where it does not). Runtime 13 s.

**Where and how much.** All 14 improvements are at `L = 2310`: 13 at `N = 10^4`
(`M = 2, 4, 5, 8, 13, 14, 16, 17, 18, 19, 20, 21, 22`) and one at `N = 10^6` (`M = 3`).
None at `10^8` or `10^12`. Absolute gains 0.09 to 2.76; relative 4.6e-7 to 2.5e-4. The
largest, `(2310, 17, 10^4)`: `B_N` 10871.5278 to 10868.7700, gain 2.758. The one at `10^6`:
`(2310, 3)`, 1148784.2045 to 1148783.6798, gain 0.525.

**The per-`(L, N)` winners do not move.** Under `B_N`, the best `M` for each `L` and `N` is
the same seed whether one takes the pilot's seeds or the direct ones:

| L | N | best M | B_N | full-cost winner's B_N (its M) |
|---|---|---|---|---|
| 30 | all four | 6 | Chebyshev, e.g. 11042.7472 at 10^4 | same |
| 210 | all four | 6 | e.g. 10727.2002 at 10^4 | same |
| 2310 | 10^4 | 10 | 10679.3997 | 10711.1476 (M = 15) |
| 2310 | 10^6 | 15 | 1069825.6923 | same |
| 2310 | 10^8 | 15 | 106985409.7569 | same |
| 2310 | 10^12 | 15 | 1069854452477.92 | same |

Two things in that table are worth a sentence. At `L = 2310`, `N = 10^4`, the pilot's own
seeds already put the smallest certificate at `M = 10`, not at the `M = 15` seed the pilot
selected by `C` (and which `full_cost.py` also selected by `U_N`); selecting by the
constant or by the proved bound picks a seed whose `B_N` is 31.7 higher at this `N`. And
the direct optimizer, given the freedom to exploit the actual fractional parts
`{N/(j M^k)}`, changes none of these winners: its 14 gains land on non-winning `M`.

**What the improved seeds look like.** Each is the pilot's seed with its small
denominators re-tuned (thirds to halves at `M = 2, 3, 4, 5`; new quarter-weights on
`21, 22, 33, 35, 55, ...` at `M = 13, 14`; a `2310` coefficient moved to `-3` at `M = 8`),
with the leading constant `C` equal or larger by at most 3e-5. The gain is entirely in
the lower-order terms, which is why it is a few units at `10^4` and nothing measurable
beyond. For scale, `REVIEW.md` records `psi(10^4) = 10013.397`, so the winning `L = 2310`
certificate at `10^4` sits 666.0 above `psi`; the best direct gain anywhere at `10^4` is
2.76, under half a percent of that gap. Within a fixed `(L, M)`, the certificate is
determined by the leading constant to within a few units, and the constant is what the
pilot already optimized.

**Does any pattern persist across `N`?** No. For every one of the 14 improving `(L, M)`
pairs the direct seed at the other three cutoffs is the pilot's seed, so each direct seed
is specific to its `N`. At `10^8` and `10^12` the direct LP returns the pilot's seed in
all 87 pairs. One caveat on those two cutoffs: differences between candidate seeds with
equal leading constant are of order `log^2 N`, which relative to `B_N ~ 10^12` is about
1e-9, close to the solver's 1e-10 tolerance; the exact evaluation is at 50 digits, but the
LP may not resolve a gain that small, so "no improvement at `10^12`" means none the float
LP could find, not a proof that none exists in the polytope.

## Answer

- **Does direct minimization improve `B_N`?** Marginally and only at small `N`: 14 of 348
  rows, all at `L = 2310`, 13 of them at `10^4` and one at `10^6`, by 0.09 to 2.76 (at most
  2.5e-4 relative). Never at `10^8` or `10^12`. It never changes the best seed for a given
  `(L, N)`. It beats the full-cost seed wherever that seed differs from the pilot's, by
  15 to 312, which restates `COST_COMPARISON.md`'s finding from the other side.
- **Does any pattern persist?** No. Every improvement is `N`-specific and disappears at the
  next cutoff; from `10^8` on, minimizing `B_N` directly returns the leading-constant seed
  in all 87 pairs. Of the three objectives, the pilot's is the one that agrees with the
  certificate at every large cutoff, and at `10^4` the best seed per `L` was already among
  the pilot's, at a different `M` than the constant selects.

## Checks run

`direct_bn.py` (348 rows, 0 rejections, fallback never needed); `tests/test_factorial_direct_bn.py`
(headline counts, every distinct direct seed rechecked exactly, every row's three `B_N`
values recomputed at 40 digits from the recorded rationals, the fallback rule re-derived
row by row, the headline row); `tests/test_factorial_full_cost.py`,
`tests/test_factorial_pilot_archive.py`, `tests/test_frontier_archive.py`,
`tests/test_hunt_probe_discipline.py`, `tests/test_docs_numbering.py`, `tests/test_doors.py`;
`scripts/make_context.py --check`. Not done: any LP-optimality proof, any search beyond the
pilot's sizes, any prime computation at these `N`, any edit to the earlier records.
