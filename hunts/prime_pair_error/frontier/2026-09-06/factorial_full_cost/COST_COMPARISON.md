# Full-cost versus leading-constant optimization of the factorial-certificate seed

Experiment, 2026-09-06, a follow-up to the preserved pilot in
`../factorial_certificate_pilot/` (read `PILOT.md`, `pilot.py` and `REVIEW.md` there first).
The pilot directory is untouched; everything here is new. Script `full_cost.py`, record
`full_cost_results.json`, pinned by `tests/test_factorial_full_cost.py`.

**Label.** A finite comparison of two LP objectives on one seed family. Not an asymptotic
theorem, not an LP-optimality proof, not a prime-counting record, and nothing here bears on
RH (`docs/08`). Grade: *measured*, with every accepted seed rechecked exactly.

## The question

The pilot chooses a seed `a = (a_j)_{j | L}` by minimizing the leading constant
`C = kappa/(1 - 1/M)`, `kappa = -sum_j a_j log(j)/j`, and then proves (PILOT.md section 3)

    psi(N) <= B_N <= U_N := kappa N (1 - M^{-K-1})/(1 - 1/M) + A [(K+1)(1 + log N) - log(M) K(K+1)/2],

with `A = sum_j |a_j|` and `K = floor(log_M N)`. Does minimizing all of `U_N` (constant and
error term together) give a better certificate than minimizing `C` alone, at the same
`L`, `M`, `N`?

## Method

- Same constraints as the pilot, unchanged: `j | L`; `sum_j a_j/j = 0`; `g(r) >= 0` for
  `0 <= r < L`; `g(r) >= 1` for `1 <= r < M`. Same sizes: `L in {30, 210, 2310}`, `M = 2..30`.
  Cutoffs `N in {10^4, 10^6, 10^8, 10^12}`. 87 x 4 = 348 rows.
- `U_N = c1 kappa + c2 A` with `c1 = N (1 - M^{-K-1})/(1 - 1/M)` and
  `c2 = (K+1)(1 + log N) - log(M) K(K+1)/2`, both positive. `A` enters the LP through
  auxiliaries `u_j >= |a_j|`; the objective handed to HiGHS is `kappa + (c2/c1) A`, tolerances
  1e-10. The LP only proposes: each proposal is reconstructed with
  `Fraction(x).limit_denominator(10^6)` (the pilot's rule) and every constraint is rechecked in
  integers. A failed recheck is a rejection, recorded, never rounded toward feasibility.
- Baseline: the pilot's recorded leading-constant seed for the same `(L, M)`, re-verified.
  The leading-constant LP was also re-solved here; it returned the recorded seed in all 87
  cases (`leading_constant_resolve_mismatches: 0`).
- Both seeds are evaluated on the same `U_N` at 50 digits from their exact rationals. The
  record also carries the certificate value itself, `B_N = sum_{k<=K} sum_j a_j log(floor(N/(j M^k))!)`,
  for every row where the two seeds differ. Log-factorials only. No prime data anywhere.

## Results

**Counts.** 348 rows; 348 accepted, 0 rejected; full cost strictly better than its own
baseline in 30 rows, tied in 318, worse in 0. Every one of the 318 ties is the identical
seed. Runtime 5.2 s.

**Where full cost wins.** 29 of the 30 wins are at `N = 10^4`: one at `(L, M) = (210, 7)` and
28 at `L = 2310` (every `M` except 6). The 30th is `(2310, 7)` at `N = 10^6`. At `N = 10^8`
and `N = 10^12` the full-cost LP returns the leading-constant seed in all 87 pairs.

**Size of the wins at `N = 10^4`.** Relative improvement of `U_N` from 0.07% (`(210, 7)`) to
5.4% (`(2310, 2)`); the `L = 2310` wins other than `M = 2, 3` are 0.8% to 2.9%. The one win
at `10^6` is 7.8e-6 relative.

**The mechanism is a trade of constant for coefficient mass.** In every winning row the
full-cost seed has a *larger* `C` and a *smaller* `A`. At `N = 10^4` and `M = 15` the LP
weighs one unit of `A` against `c2/c1 ~ 2.3e-3` units of `kappa`; at `10^6`, `10^8`, `10^12`
that price falls to about `4.5e-5`, `7.4e-7`, `1.5e-9`, below the cheapest available trade,
and the optimum reverts to the leading-constant seed.

**The headline row, and the per-`L` winners.** For `L = 30` and `L = 210` the two objectives
pick the same seed at every `N` (Chebyshev's `M = 6` seed with `A = 5`, and the pilot's
`M = 6` seed with `A = 10`). For `L = 2310` they differ only at `N = 10^4`:

| objective | M | A | C | U_{10^4} | B_{10^4} |
|---|---|---|---|---|---|
| leading constant (pilot) | 15 | 15 | 1.069854452573 | 11067.229100679 | 10681.264020 |
| full cost | 15 | 10 | 1.073022970930 | 10975.948357359 | 10711.147559 |

Full cost lowers the proved bound by 91.28 (0.82%). Winning seed:

    a_1 = 1; a_2 = a_3 = a_5 = -1; a_6 = 1; a_7 = -1; a_10 = 1; a_11 = -1;
    a_154 = 1/2; a_210 = -1/2; a_2310 = -1.

Baseline seed (the pilot's): `a_1 = 1; a_2 = a_3 = a_5 = -1; a_6 = 1; a_7 = -1; a_10 = 1;
a_11 = -1; a_30 = -1; a_33 = a_105 = 1; a_210 = a_330 = -1; a_385 = 1; a_1155 = -1`.
At `N >= 10^6` the `L = 2310` winner under both objectives is the baseline.

**But the certificate itself gets worse, in every winning row.** The last column above is
the point of this experiment. In all 30 rows where full cost lowers `U_N`, the actual
`B_N` of the full-cost seed is *higher* than the baseline's: by 29.88 in the headline row
(0.28% of `B_N`), and by 12.4 to 311.0 across the 30. Zero rows lower `B_N`. The reason is
in `REVIEW.md` section 3.6: the error term `A (K+1)(1 + log N)` is a valid bound on
`|B_N - main term|` but is loose by a factor of ten or more at these `N`, and the true
deviation is *negative* (the pilot seeds sit 10 to 40 below `C N`). So `U_N` charges `A`
at a rate the true `B_N` never pays, and an optimizer that believes the charge trades away
constant it did not need to. Full cost optimizes the proof, not the certificate.

**Does the coefficient pattern persist across cutoffs?** No. For each of the 29 `(L, M)` pairs
that differ at `10^4`, the full-cost seed at `10^6` is already the baseline, except
`(2310, 7)`, which passes through a third seed (`A = 22` against the baseline's `170/7`,
`C` larger by 6e-5) and rejoins the baseline at `10^8`. At `10^8` and `10^12` all 87 pairs
are the baseline. The small-`N` winners are lower-complexity seeds, and three are literally
sub-lattice seeds: at `(2310, 2)` the winner is the `L = 30` seed `a_1 = 1, a_2 = -2`; at
`(2310, 4)` and `(2310, 5)` it is the pilot's `L = 210, M = 6` seed. What persists as `N`
grows is the leading-constant seed, with the full-cost objective acting only as a tie-break
toward smaller `A` among leading-constant optima, and in this record that tie-break changes
nothing at `10^8` and beyond.

## Answer

- **Does full-cost optimization improve the bound?** At `N = 10^4`, yes, in 29 of 87 pairs,
  by up to 5.4% of `U_N` (0.82% at the `L = 2310` winner). At `10^6`, in 1 pair by 7.8e-6.
  At `10^8` and `10^12`, never: the two objectives return the same seed.
- **Does it improve the certificate?** No. In every row where the bound improves, `B_N` gets
  worse. The improvement is entirely in the slack of the error term.
- **Winning coefficients and both costs:** the table and seeds above; all 348 rows with
  both seeds, both `U_N`, and `B_N` where they differ, are in `full_cost_results.json`.
- **Pattern persistence:** none from `10^4` upward; the leading-constant seed is the
  full-cost optimum from `10^8` on in all 87 pairs, and from `10^6` on in 86.

## What this suggests testing mathematically next

1. **The stabilization is a parametric-LP fact and can be made exact.** `U_N/c1 = kappa + t A`
   with `t = c2/c1 -> 0` as `N -> inf`, over a fixed polytope. The optimal vertex is
   piecewise constant in `t` with finitely many breakpoints, so for each `(L, M)` there is a
   threshold `t*(L, M) > 0` below which the full-cost optimum is the minimum-`A` vertex among
   the leading-constant optima, and an `N_0(L, M)` beyond which nothing changes. The record
   shows `N_0 <= 10^8` for all 87 pairs and `<= 10^6` for 86. The concrete test: compute
   `t*(L, M)` exactly (rational LP, or minimum `A` subject to `kappa = kappa*` over the
   optimal face), derive `N_0`, and check that the pilot's recorded seeds are the
   minimum-`A` optima, which the `10^8` and `10^12` rows suggest but a float solver cannot
   establish.
2. **Replace the proxy before optimizing it.** The experiment shows that optimizing a valid
   but loose error term moves the seed in the wrong direction for `B_N`. The next lemma to
   try is a sharper per-term inequality: with Stirling's second-order term,
   `log(floor(y)!) - (y log y - y) = (1/2) log(2 pi y) - {y} log y + O(1/y)`, so the
   `a_j`-weighted sum has an explicit `(1/2)(log(2 pi N) sum_j a_j - sum_j a_j log j)` piece
   (note `sum_j a_j`, not `sum_j a_j/j`, so balance does not kill it) plus signed
   fractional-part terms `-sum_j a_j {N/j} log(N/j)`. Whether an error term of that shape,
   still a proved bound, makes the full-cost ordering agree with the `B_N` ordering on this
   record is a bounded question with the same 348 rows as its test.
3. **Consequence for the pilot's section 5.** Any varying-seed program that aims at
   `B_N - N = O(N^{1/2 + eps})` has to control the true deviation, not `A (K+1)(1 + log N)`;
   this record is a small, concrete instance of the proxy and the target pulling in
   opposite directions, at the one scale (`10^4`) where the proxy is not yet negligible.

## Checks run

`full_cost.py` (348 rows, 0 rejections, 0 re-solve mismatches); `tests/test_factorial_full_cost.py`
(headline counts, every distinct full-cost seed rechecked exactly, every row's `U_N`
recomputed at 40 digits from the recorded rationals, large-cutoff rows equal the baseline,
the headline row's numbers); `tests/test_factorial_pilot_archive.py`,
`tests/test_frontier_archive.py`, `tests/test_hunt_probe_discipline.py`,
`tests/test_docs_numbering.py`, `tests/test_doors.py`; `scripts/make_context.py --check`.
Not done: any exact LP-optimality proof, any search beyond the pilot's sizes, any prime
computation at these `N`.
