# RESULTS: Robin's inequality beyond the verified range (`robin_tfree/`)

**Status: candidate, ordinary derivation, unreviewed, pending external verification.**
The numerical step is enclosure-carrying (Arb balls, cross-checked by a second
quadrature route); the inputs are published theorems and tables, quoted in section 3
and not recomputed here. The steps that most need outside eyes are Lemma 3(b),(c) (the
reduction) and the use of Buthe's Table 1 and BKLNW's Tables 8 and 9 (section 9). No RH
claim. Against the literature found by the search of section 9, the t-free statement is
a delta of four (25 against the published 21); that is a recorded search, not a
novelty claim.

## Summary

Robin (1984): RH holds iff `sigma(n) < e^gamma n log log n` for every `n > 5040`.
Morrill and Platt verified the inequality for every `5040 < n <= x0#`,
`x0 = 29 996 208 012 611`. Every known t-free and valuation result above that range
reduces to one quantity at the primorials,

    E(x) = log( e^{-gamma} prod_{p <= x} p/(p-1) / log theta(x) ),   x = p_k >= x0.

**Claim 1 (candidate, ordinary derivation, unreviewed, pending external
verification).** For every `x >= x0`, `E(x) <= 2.4807 * 10^-8` (route A,
which uses only Buthe's `x - theta(x) <= 1.95 sqrt(x)`), and `E(x) <= 2.3414 * 10^-8`
(route B, Buthe's dyadic Table 1).

**Corollaries (candidate, same grade).**

1. Robin's inequality holds for every **25-free** `n > 5040`. Best published t-free
   result found (section 9): 21-free (Axler, Ramanujan J. 61 (2023) 909-919; reproved
   by Assani, Chester, Paschal, *Integers* 26 (2026) A86).
2. It holds for every `n > 5040` with `q^(nu_q(n)+1) < Q*` for some prime `q`, where
   `Q* >= 40 311 388` (route A; `42 709 615` route B). Spelled out: `nu_2(n) <= 24`, or
   `nu_3 <= 14`, `nu_5 <= 9`, `nu_7 <= 7` (8 by route B), `nu_11 <= 6`, `nu_q <= 5` for
   `q in {13, 17}`, `<= 4` for `19 <= q <= 31`, `<= 3` for `37 <= q <= 79`, `<= 2` for
   `83 <= q <= 337` (349 by route B), `<= 1` for primes `q < 6349`, or `q` does not
   divide `n` for some prime `q < 4.03 * 10^7`. Axler's Theorem 3 (Theorem 1.4 in
   arXiv:2110.13478v3) is the same shape; his list (`nu_2 <= 20`, `nu_5 <= 8`, ...,
   `nu_q = 1` up to 1777) corresponds to a threshold between `1777^2` and `1783^2`,
   about `3.17 * 10^6` (pinned).
3. `sigma(n) < (1 + 2.49 * 10^-8) e^gamma n log log n` for every `n > 5040`
   (Axler 2023, Corollary 2, which is Corollary 3.1 in arXiv v3: `1 + 3.15367 * 10^-7`;
   route B gives `2.35 * 10^-8`). Axler and Nicolas, *Acta Arith.* 209 (2023) 357-383, give
   further effective upper bounds for `n/phi(n)` and `sigma(n)/n` that this hunt has not
   read (paywalled), so this comparison is against Axler 2023 only.
4. Hence RH holds iff Robin's inequality holds for every `n > 5040` divisible by
   `M* = prod_{q < Q*} q^(e_q)`, `e_q` the least nonnegative integer `e` with
   `q^(e+1) >= Q*`. This does not reduce the remaining problem to 25-full integers:
   a multiple of `M*` may have prime factors with exponent less than 25.

**What makes the difference** is one exact identity (section 2): the boundary term of
Mertens' partial summation, `R(x)/(x log x)`, and the denominator correction
`log(log theta(x)/log x)` cancel to first order. Morrill-Platt (v4, Lemma 10) and Axler
(proof of Theorem 1) bound them separately. At `x0` that costs
`2 * 1.95/(sqrt(x0) log x0) = 2.29 * 10^-8`, and with that cost added route A gives 24,
not 25 (pinned by `test_separate_bounding_loses_what_the_cancellation_keeps`).

## 1. Setting

`theta(x) = sum_{p <= x} log p`, `psi` the Chebyshev function, `N_k = p_1 ... p_k`,
so `log N_k = theta(p_k)` and `N_k/phi(N_k) = prod_{p <= p_k} p/(p-1)`. Then

    N_k/phi(N_k) = e^gamma log log N_k exp(E(p_k)).                       (1.1)

Nicolas (1983) proved that RH holds iff `E(p_k) > 0` for every `k >= 2`.
The logarithm defining `E(2)` is not real, so `k = 1` is excluded. This hunt bounds
`E` from **above**, which is what Robin-type results for restricted families need.

## 2. The identity

Write `R(u) = theta(u) - u`, `w(u) = (1 + log u)/(u^2 log^2 u)`,
`h(p) = -log(1 - 1/p) - 1/p > 0`, `L = log x`, `d = R(x)/x`, and
`g(d) = d/L - log(1 + log(1 + d)/L)`.

**Lemma 1 (identity).** For real `x >= 3`,

    E(x) = - int_x^inf R(u) w(u) du  -  sum_{p > x} h(p)  +  g(d).          (2.1)

*Proof.* Stieltjes integration of `1/(u log u)` against `d theta` gives
`sum_{p <= x} 1/p = log log x + M + R(x)/(x log x) - int_x^inf R w`, with `M` the
Meissel-Mertens constant (the integral converges by the prime number theorem; this is
Rosser-Schoenfeld 1962 (4.20) with the remainder kept exact). Mertens' constant
relation `gamma = M + sum_p h(p)` gives
`sum_{p <= x} log(p/(p-1)) = gamma + log log x + R(x)/(x log x) - int_x^inf R w - sum_{p>x} h(p)`.
Finally `log log theta(x) = log log x + log(1 + log(1 + d)/L)`. Subtracting,
`R(x)/(x log x) = d/L` combines with the last term into `g(d)`. []

**Lemma 2 (second order).** If `|d| <= 10^-6` and `L >= 31`, then `|g(d)| <= d^2/L`.

*Proof.* `g(0) = g'(0) = 0` and
`g''(d) = (L + 1 + l)/((1 + d)^2 (L + l)^2)` with `l = log(1 + d)`, so
`0 < g'' <= (L + 1 + 1.1e-6)/((1 - 1e-6)^2 (L - 1.1e-6)^2) < 2/L` for `L >= 31`;
Taylor's theorem gives `|g(d)| <= (sup g''/2) d^2 <= d^2/L`. []

Both are checked on real primes in `test_bound.py`: the partial-summation identity
between `x < y` to `10^-25` at two ranges (and a flipped sign misses by more than
`10^-12`), the difference form `E(y) - E(x) = int_x^y R w + sum_{x<p<=y} h(p) + g(d_y) - g(d_x)`
to `10^-25`, and Lemma 2 at 400 random points.

## 3. Inputs (quoted, not recomputed)

| input | statement used | source |
|---|---|---|
| verified range | Robin holds for `5040 < n <= 10^(10^13.11485)` (Theorem 5) and for `13# <= n <= x0#`, `x0 = 29 996 208 012 611` (Corollary 2) | Morrill, Platt, *Integers* 21 (2021) A28, Theorem 5 and Corollary 2 (Theorem 13 and Corollary 14 in arXiv:1809.10813v4) |
| route A | `x - theta(x) <= 1.95 sqrt(x)` for `1423 <= x <= 10^19` | Buthe, *Math. Comp.* 87 (2018) 1991-2009, (1.6) |
| route B | `(t - psi(t))/sqrt(t) <= M+(x)` on `[x, 2x]`, dyadic rows `10^10 <= x <= 5.12 * 10^18`; `theta(y) < y` for `1 <= y <= 10^19` | same paper, Table 1 and (1.7) |
| past `10^19` | `|psi(x) - x| < eps(b, b') x` on `[e^b, e^b']`, `b'` the next printed row, rows `b = 40 ... 25000` | Broadbent, Kadiri, Lumley, Ng, Wilk, *Math. Comp.* 90 (2021) 2281-2315, Table 8 |
| past `e^26000` | `|theta(x) - x| < A_1(25000) x/log x`, `A_1(25000) = 7.5635 * 10^-45` | same paper, Table 9 |
| `psi - theta` | `psi(x) - theta(x) < 1.42620 sqrt(x)`, used as `1.5 sqrt(x)` | Rosser, Schoenfeld, *Illinois J. Math.* 6 (1962), Theorem 13 |

The printed exponent `13.11485` is rounded down: `10^(10^13.11485)` is below `x0#`, so
the top of the verified range is Corollary 2, not Theorem 5 (pinned by
`test_verified_range_top_is_the_corollary_not_the_rounded_theorem`).

Table 1 was transcribed from the published table and compared with a rendering of the
page; its maximum equals the `0.94` Buthe states as (1.5), which a test pins. Each
Table 1 entry gets `+0.005` (the table prints two decimals) and each Table 8/9 entry is
inflated by a relative `10^-5` (the paper notes printf rounding of the last digit).
Table 8 was computed by its authors assuming RH to height `2.446 * 10^12` (Wedeniwski's
`H0 = 2 445 999 556 030`, their B.1), inside Platt and Trudgian's verification to
`3 * 10^12` (*Bull. LMS* 53 (2021)). Its rows `b <= 2000` are computed by the method of
Buthe 2016, Theorem 1, which BKLNW restate as their Theorem 16 with a term their
footnote 4 says the original statement omitted. That the table values were computed with
the corrected term is the authors' statement; this hunt has not checked it, and rows
`b = 40, 45, 50`, all from that method, carry 99% of the tail (pinned).

**Transcription check, 2026-10-10.** The transcribed values were compared mechanically
with text extracted from the freely available arXiv versions: Buthe arXiv:1511.02032v2,
Table 1 (all 31 `M+` entries) and Theorem 2 (1.5)-(1.7); BKLNW arXiv:2002.11068v2,
Table 8 (all 50 rows with `b >= 40`, the rows used) and Table 9 (`A_1(25000)`). Every
value agrees. The published *Math. Comp.* tables were not re-read in this check; the
Morrill-Platt statements were checked against the *Integers* PDF and arXiv v4;
Rosser-Schoenfeld's Theorem 13 was not rechecked. A transcription that agrees with a
preprint is not a review of the tables: their computation, and BKLNW's partial-RH
input, await outside review like the rest of the derivation.

## 4. Reduction from Robin's inequality to `E`

**Lemma 3.** Let `n > x0#`, and let `k` satisfy `N_k <= n < N_(k+1)`. Then `p_k >= x0`,
`omega(n) <= k`, `log log n >= log theta(p_k)`, and:

(a) `sigma(n)/n = (n/phi(n)) prod_{p^a || n} (1 - p^-(a+1))`, and
`n/phi(n) <= N_k/phi(N_k)`, so for every prime `q | n`,
`sigma(n)/(n log log n) <= e^gamma (1 - q^-(nu_q(n)+1)) exp(E(p_k))`.

(b) If a prime `q < x0` does not divide `n`, the `omega(n) <= k` primes of `n` avoid
`q`, so `n/phi(n) <= (1 - 1/q) N_(k+1)/phi(N_(k+1))` and
`sigma(n)/(n log log n) < e^gamma (1 - 1/q) exp(E(p_(k+1)) + s)` with
`s = 4/(x0 - 1)`, since `log theta(p_(k+1))/log theta(p_k) <= 1 + 2/theta(p_k)` by
Bertrand and `theta(p_k) >= 0.99 p_k`.

(c) If `n` is t-free (Solé-Planat), `sigma(n) <= Psi_t(n)` and
`sigma(n)/(n log log n) <= e^gamma zeta(t)^-1 prod_{p > p_k}(1 - p^-t)^-1 exp(E(p_k))`,
and `log prod_{p > p_k}(1 - p^-t)^-1 <= 2/(x0 - 1) <= s`.

These are elementary; the `n/phi(n)` maximisation and `sigma(n)/n < n/phi(n)` are
checked exhaustively to `2 * 10^5`, and Robin's inequality directly on
`5041 <= n <= 30030`, in `test_bound.py`; `x0` is prime (pinned), so `p_k >= x0`.
Parts (b) and (c) carry the step from `E` to the integer statements and are the steps a
reviewer flagged as most needing outside eyes: ordinary arguments, unreviewed. The
checks to `2 * 10^5` exercise only their elementary inequalities at small `n`; nothing
here tests them at `n > x0#`.

## 5. The bound

**Claim 1 (candidate; restated).** For every `x >= x0`, `E(x) <= E*` with

| route | main, `[x0, 10^19]` | tail, `[10^19, inf)` | Lemma 2 term | `E*` |
|---|---|---|---|---|
| A (Buthe (1.6)) | `2.22602 * 10^-8` | `2.54657 * 10^-9` | `4.1 * 10^-15` | `2.48068 * 10^-8` |
| B (Buthe Table 1) | `2.08672 * 10^-8` | `2.54657 * 10^-9` | `4.1 * 10^-15` | `2.34138 * 10^-8` |

*Proof.* Drop `-sum_{p>x} h(p) <= 0` from (2.1). On `[x0, 10^19]`,
`0 < u - theta(u) <= B(u)` with `B(u) = 1.95 sqrt(u)` (A) or
`B(u) = (M+ + 0.005) sqrt(u) + sqrt(u) + u^(1/3) + u^(1/4) + 59 u^(1/5)` (B: write
`u - theta(u) = (u - psi(u)) + sum_{k >= 2} theta(u^(1/k))` and use `theta(y) < y`;
the terms vanish for `k > log_2 u <= 63`). Past `10^19`,
`|theta(u) - u| <= B(u) = eps(b, b') u + 1.5 sqrt(u)`, and past `e^26000` the Table 9
bound. So `-int_x^inf R w <= int_x^inf B w <= int_{x0}^inf B w`, the last step because
`B w >= 0`. For Lemma 2, `|d| <= 1.957/sqrt(x0) < 10^-6` on `[x0, 10^19]` (the
module's Table 1 envelope; Buthe (1.6) alone gives `1.95`) and
`|d| < 2 * 10^-8` beyond: the largest Table 8 envelope, including
`1.5/sqrt(10^19)`, is less than `1.982 * 10^-8`, and the Table 9 envelope is smaller.
The test `test_far_theta_deficit_envelopes_fit_second_order_domain` checks every
tail block and the infinite tail. []

Every piece `int u^alpha w(u) du` has the closed form
`F(y) = -e^(-beta y)/y - (1 - beta) E1(beta y)`, `beta = 1 - alpha`, `y = log u`
(`F = log y - 1/y` when `alpha = 1`), evaluated in Arb at 256 bits; the result's radius
is below `10^-27`. An independent `mpmath.quad` route over every Table 1 block agrees to
a relative `10^-12`.

## 6. Consequences

With `s = 4/(x0 - 1) = 1.3 * 10^-13`:

- **t-free.** `log(1/zeta(t)) + s + E* < 0` decides `t <= 25` for both routes (at
  `t = 25`: `-2.98035 * 10^-8 + 2.48068 * 10^-8 < 0`, margin `5.0 * 10^-9`) and fails at
  `t = 26` (`-1.49016 * 10^-8`). With Lemma 3(c) and Morrill-Platt below `x0#`:
  Corollary 1.
- **Valuations.** Lemma 3(a)-(b) give Robin whenever `q^(nu_q(n)+1) < Q*`,
  `Q* = 1/(1 - exp(-(E* + s)))`; each listed exponent is decided against the lower
  endpoint of the `Q*` ball. Corollary 2, which contains Corollary 1 via `q = 2`.
- **Unconditional constant.** `sigma(n)/n < n/phi(n) <= e^gamma log log n exp(E*)`:
  Corollary 3 with `epsilon = exp(E* + s) - 1`.

## 7. Against the prior method

| | Morrill-Platt 2021 | Axler 2023 | this hunt (A) |
|---|---|---|---|
| bound on `theta` near `x0` | Schoenfeld under partial RH, `sqrt(x) log^2 x/(8 pi)` | `0.024334 x/log^3 x` | Buthe `1.95 sqrt(x)` |
| boundary and denominator terms | bounded separately | bounded separately | cancel (Lemma 1) |
| margin used at `x0` | `~9 * 10^-7` | `~3.3 * 10^-7` | `2.48 * 10^-8` |
| t | 20 | 21 | 25 |

The first two margins are approximate, read from the papers' final inequalities and not
recomputed here; a test checks only that each lies between `log zeta(t+1)` and
`log zeta(t)` for that paper's `t`. The `theta` bounds in the first row are quoted.

Morrill-Platt's v1 (arXiv:1809.10813v1, 2018) claimed 25-free from one computed value
`R_25(N_177244758016) < 1 - 10^-16` and a monotonicity of `R_t(N_n)` it did not prove;
v4 withdrew to 20 and its section 5 says the monotonicity would have made the proof
easy. Corollary 1 recovers 25 by a different argument. Robustness: route B keeps
`t = 25` if every Table 1 entry is raised by `0.5`, and loses it at `+0.6`; route A loses
it if `1.95` is replaced by `2.6` (both pinned).

## 8. Checks (`test_bound.py`, 37 tests, ~45 s)

- Lemma 1 on real primes, two ranges, both the sum form and the `E` difference form;
  a flipped sign is caught. Lemma 2 at 400 random points.
- Closed-form integrals against `mpmath.quad`, 12 cases; the whole route-B main term
  against blockwise quadrature.
- The bound machinery, started at `x = 10^5, 10^6, 3 * 10^6` (global `0.94` below
  `10^10`), dominates the true `E(x)` computed from the primes; the same comparison with
  the integral scaled by `0.25` fails at some sampled `x` (the planted fault is caught).
- Inputs: Table 1 covers `[x0, 10^19]` with no gap and its maximum is Buthe's `0.94`;
  Table 8 ordering; Buthe's `0.05 sqrt(x) < x - theta(x) <= 1.95 sqrt(x)` at sampled
  `x <= 3 * 10^6`; every far-range deficit envelope is below `2 * 10^-8`.
- Lemma 3's elementary steps to `2 * 10^5`; Robin directly on `5041 <= n <= 30030`.
- Pins: `t = 25` passes and `26` fails on both routes; `E*`, `Q*`, the valuation list and
  `epsilon` for both routes; `results.json` on disk matches a fresh run.
- Every number this file derives is pinned at the precision it is printed (the
  `test_stated_*` tests, added 2026-10-10): the section 5 table, the radius, `s`, the
  `t = 25, 26, 27` values and margin, the separate-terms cost, every range of the
  valuation list, Axler's list against the threshold read off it, the deficit
  constants, and the numbers in "The doors" except the two marked there as unpinned
  estimates. Quoted inputs are constants of `bound.py`; section 7's prior margins are
  consistency-checked only.
  Planting `1.951` for `1.95`, one unit in the last digit of Table 8's first row, or
  `0.006` for the Table 1 margin turns these pins red. `x0` is prime, and
  `10^(10^13.11485) < x0#` (so the verified range ends at Corollary 2).

## 9. Grade, review, novelty

- Lemmas 1-3 and Claim 1's reduction: **ordinary derivation**, written and checked
  by one session; identities exact-checked on real primes. No independent review yet.
  A reviewer of PR #270 reports re-deriving Lemma 1 and recomputing the route-A main
  term (`2.22602 * 10^-8`) and the `t = 25, 26` decisions; that is a partial check, not
  a review.
- **Awaiting outside review, named:** Lemma 3(b) and (c) (the reduction from `E` to
  the t-free and valuation statements), and the tables: Buthe's Table 1 (route B only;
  route A uses his (1.6)) and BKLNW's Tables 8 and 9, the latter computed assuming RH to
  height `2.446 * 10^12` by a method whose original statement BKLNW correct (section
  3). The transcriptions agree with the arXiv versions (section 3); the tables
  themselves are taken on their authors' word.
- The evaluation of `E*`: **enclosure-carrying** (Arb), with an independent quadrature
  route agreeing.
- The inputs: published, quoted, not recomputed. Buthe's Table 1 and (1.6) rest on his
  analytic computation; Morrill-Platt's range on their interval-arithmetic run.
- Composite grade: candidate, ordinary derivation, unreviewed, pending external
  verification.

### Search (2026-10-10)

Searched on 2026-10-10, adding to the first session's three web searches (2026-10-03/04)
and its full texts of Axler 2023 and Morrill-Platt v1 and v4:

- **Web:** six queries: `Robin inequality t-free integers`, `Robin's inequality 21-free
  integers Axler`, `Morrill Platt Robin inequality 20-free`, `Robin inequality k-free
  integers 2025 2026 arXiv`, `"Robin's inequality" "25-free"`, `"Robin's inequality"
  free integers 2026`.
- **arXiv** (API, titles and abstracts containing Robin's inequality, Robin's criterion
  or colossally abundant, newest first, through arXiv:2609.33794 of 2026-09-27).
- **zbMATH Open** (API: title "Robin's inequality"; title Robin and inequality; abstract
  "Robin's inequality" and free; title "free integers" and Robin): every number-theory
  hit from 2022 on read at review or abstract level, earlier ones by title and the
  surveys in Axler 2023 and Assani, Chester, Paschal.
- **Citations:** Semantic Scholar's citing lists for Axler 2023 (arXiv:2110.13478, 7
  papers) and Morrill-Platt (arXiv:1809.10813, 5 papers).

Found, as they bear on this claim: 21-free remains the best published t-free result
(Axler, *Ramanujan J.* 61 (2023), zbMATH 1532.11010; reproved by Assani, Chester,
Paschal, *Integers* 26 (2026) A86, whose survey of June 2026 also ends at 21).
Morrill-Platt's v1 claim of 25-free (2018) is the only 25-free statement found, and its
own later versions and the journal version withdraw to 20. Valuation results:
`nu_2 <= 19` and others (Hertlein, *Integers* 18 (2018)), `nu_2 <= 20` and the list
above (Axler 2023), `nu_2 <= 16` (Wu, arXiv:1812.00987, unrefereed), Robin for `n` not
divisible by some prime `q <= 1 771 559` (Vega, *Ramanujan J.* 59 (2022)); a Zenodo
preprint (Cavalcante, 2026-07-31) bounds valuations only for a hypothetical least
counterexample, a different statement. Unconditional constants: `1 + 5.645 * 10^-7`
(Hertlein), `1 + 3.15367 * 10^-7` (Axler); Axler-Nicolas 2023 not read. Of the papers
read in full (Axler 2023, Morrill-Platt v1 and v4), none uses the first-order
cancellation of Lemma 1; the others were read at abstract or review level only. A
claimed proof of RH (arXiv:1605.08273, v15) was found and is not counted.

**Delta against the best source found:** Axler 2023 proves Robin's inequality for every
21-free `n > 5040`, for `nu_2(n) <= 20` and similar valuations, and with constant
`1 + 3.15367 * 10^-7`, using the same verified range (Morrill-Platt) and separate
bounds on the two first-order terms. This hunt claims, as a candidate pending external
verification: 25-free, `nu_2(n) <= 24` and the list of Corollary 2, and
`1 + 2.49 * 10^-8`, from the same verified range plus Buthe's `1.95 sqrt(x)` and the
cancellation. **Not searched:** MathSciNet, Google Scholar and non-English venues.
Original to this lab; novelty not established; no record is claimed beyond what this
search found.

## 10. Reproduction

    .venv/bin/python hunts/robin_tfree/bound.py                       # writes results.json, < 1 s
    .venv/bin/python -m pytest -n0 -q hunts/robin_tfree/test_bound.py  # 37 tests, ~45 s

Requires `python-flint` (Arb), `mpmath`, `numpy`. No network, no heavy compute.

## The doors

This hunt measured a ceiling: the largest `t` the Solé-Planat reduction reaches with
`E*` bounded as above. That is a candidate at `x0 = 29 996 208 012 611`, not a proved
ceiling of the problem.

**Active constraints at the optimum, ranked by shadow price.**

1. **The verified range `x0`.** The binding constraint. The main term is
   `~ 1.94 c/(sqrt(x0) log x0)`, so `E*` halves when `x0` grows about fourfold; each
   further unit of `t` costs roughly a factor 4 in `x0`. Raising `x0` means re-running
   Morrill-Platt's colossally-abundant verification (their v1 reports three weeks on one
   core for its run to `10^(10^13.099)`), linear in the prime range.
2. **The constant in `x - theta(x) <= c sqrt(x)` on `[x0, ~10^15]`.** Shadow price
   `dE*/dc = 1.14 * 10^-8` per unit of `c` (route A). `t = 26` needs `E* < 1.49 * 10^-8`,
   that is an effective `c` near `1.1`, while `u - theta(u)` itself averages about
   `1 * sqrt(u)` (the `psi(sqrt u)` term). So `t = 26` at this `x0` needs `theta`
   computed exactly on `[x0, ~10^15]` and is marginal even then; `t = 27`
   (`7.45 * 10^-9`) looks out of reach at this `x0` by any upper bound on `E(x0)`
   (heuristic scale `E(x0) ~ 2/(sqrt(x0) log x0) = 1.2 * 10^-8`: the arithmetic is
   pinned, the scale is neither measured at `x0` nor a theorem).
3. **The tail past `10^19`**, `2.55 * 10^-9`, 10% of `E*`, dominated by BKLNW rows
   `b = 40, 45, 50`. Buthe 2016's partial-RH Schoenfeld bound to `2.17 * 10^25` would
   cut it to about `1.8 * 10^-9` (an estimate, not computed by `bound.py` and not
   pinned); not used, so the tail rests on one input family, BKLNW's tables.

**Frozen-constant inventory.** `x0` (input; genuine trade shape: compute cost against
about half a bit of `t` per doubling). `1.95` / Table 1 values (input; tighter values
need new zero-based computation, genuine trade). `+0.005` table margin and `10^-5`
BKLNW inflation (safety; no trade, cost `5.7 * 10^-11` on route B, under `10^-13` for
the inflation). `1.5` for `psi - theta`
(safety over `1.4262`; cost below `10^-11`). Lemma 2's `10^-6` and `L >= 31` (sized to
`x0`; no trade). `s = 4/(x0 - 1)` (no trade). Choice of Table 8 over Buthe 2016 on
`[10^19, 2.17 * 10^25]` (genuine trade: about `7 * 10^-10` of margin, the same unpinned
estimate, against one more input).

**Information class of each door.** Door 1 (larger `x0`) and door 2 (exact `theta` past
`x0`) require reading more: new prime or colossally-abundant computation beyond what
any current table holds. Door 3 stays inside published data. The first-order
cancellation is spent; the remaining analytic slack inside this family is Lemma 2's
`4 * 10^-15`.

**What remains open.** These estimates leave Robin's inequality undecided on the
multiples of `M*`. Corollary 2 reduces RH to Robin's inequality on that remaining set;
the present bound does not establish it there. The scale for `E(x0)` discussed above
is a heuristic, and this derivation proves no necessary bound on `E(p_k)` for every
`k` and no impossibility theorem for further work on this route. Any stronger
conclusion needs a separate argument covering the remaining integers.
