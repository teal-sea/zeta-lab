# RESULTS: `skewes_enclosure` (hunt #152)

Status on 2026-10-27, three outcomes and one post-hoc finding:

- **Target A (Chao-Plymen, 2e6 zeros): gate passed.** pi(x) > li(x) for some x
  with log x in [727.9519119, 727.9521241] (section 1).
- **Target B at the printed omega = 727.95134: gate failed.** This is recorded
  permanently in section 6.
- **The pre-registered omega-grid rerun (B2): hypothesis H not supported by its
  rule.** At omega = 727.951335792, the sum misses Revers's S* by 3.37e-5,
  against a budget of 2.60e-5. The pre-declared localization at that omega
  holds anyway: pi(x) > li(x) for some x with log x in [727.951319892, 727.9513517]
  (section 7).
- **Post-hoc review finding (2026-10-27, measured, not pre-registered).** The
  3.37e-5 gap is twice the second-order sum S2: Revers's printed S* for the
  Saouter-Demichel region equals Saouter-Demichel's printed first-order sum
  minus S2, to 1.0e-9, where Theorem 3.1 adds S2. Our own first-order sum
  matches Saouter-Demichel's to 4.7e-8 (sections 3, 7 and 8). The
  pre-registered verdict stands.

**Correction (2026-10-27, review of PR #360).** The B interval was first quoted
with lower end 727.9513199. That rounds the exact lower end, 727.951335792 -
0.0000159 = 727.951319892, inward, so the quoted interval was not the one
proved. The quote above is exact at the lower end and rounded outward at the
upper end (exact: 727.951351692). `test_quoted_intervals_contain_the_exact_ones`
pins every quoted interval in this file and in the case log.

Nothing here is promoted: the grades below are this hunt's report, not a
reviewer's.

## 1. The bounded result (target A, Chao-Plymen region)

Parameters (Revers 2025, subsection 6.2): omega = 727.952018, alpha = 1.34e11,
A = 1.022e7, T = 1131944.4719, which Arb counts to exactly 2,000,000 zeros.

| quantity | value | how |
| --- | --- | --- |
| S = sum over the 2e6 zeros, Revers Theorem 3.1 | [-1.006553479 +/- 3.85e-10] (radius 1.34e-10) | 20 shards of Arb balls, summed in `acb` at 128 bits |
| Revers's printed S* | -1.006553478788955 | **inside the ball**; difference [+/- 1.74e-10] |
| lower bound on I(omega, eta), eta = 1.6e-4 | [0.000409637 +/- 1.67e-10] | -1 - S - R, R as a ball |
| eta = 1.061e-4 | **[0.000147477 +/- 2.21e-10] > 0** | |
| eta = 1.060e-4 | [-0.000124308 +/- 5.29e-10] < 0 | the floor, as in Revers |

**The claim, with its dependencies.** (Corrected 2026-10-27: this heading
first read "Measured claim", which contradicts the hardened grade given below.)
With every computed step carried by
Arb balls, I(727.952018, 1.061e-4) > 1.4747e-4 > 0. By the positivity argument
in Revers's "Runs of successive integers" subsection, pi(x) > li(x) for some x with log x in
[727.9519119, 727.9521241]. This rests on four inputs:

1. **Revers 2025 Theorem 3.1** (JNT 2025, peer reviewed). It is cited, and
   this hunt does not re-derive it. Its R1 to R6 are evaluated exactly as printed.
   They reproduce both of his resizing tables (13 rows, `test_skewes_terms.py`).
2. **RH to height A = 1.022e7.** Cited: Platt (2017, to 3.06e10) and
   Platt-Trudgian (2021, to 3e12).
3. **The zeros and their completeness: rigorous on route 1 only.** Arb's
   `acb_dirichlet_zeta_zeros` and Turing count. Every ball is disjoint from
   and below the next, both within and across shards. The last zero is below T,
   and N(T) = 2,000,000. (Corrected 2026-10-27: this item first said "route 1
   only". The count N(T) also has a float-grade second route: mpmath `nzeros`,
   which shares no code with Arb and is not rigorous, gives N(T) = 2,000,000 at
   T = 1131944.4719 and 22,000,000 at T = 10379600, and one less at each of
   Revers's printed T; `test_cutoffs_by_the_mpmath_route`. That route checks
   the count only, not that each ball holds a zero.)
4. **Route 2 is a sample.** 1150 of the 2e6 Arb brackets (200 in shard 1 and
   50 in each later shard, seeded) show a sign change of mpmath `siegelz`
   at +/- 1e-8. mpmath shares no code with Arb but is float grade, and it checks
   existence, not completeness.

**Grade.** The zero sum and the error terms are enclosure-carrying (the
`hardened` rung by its ball-arithmetic clause). The zero layer has one rigorous
route and a sampled, float-grade second route. The analytic inequality and RH to
A are cited, not checked here. The composite claim is therefore **a hardened
computation on a cited derivation**, with completeness resting on Arb alone.
That is weaker than a fully independent two-route result.

**What it is not.** It is not a new record. This interval is wider than and
sits above Saouter-Trudgian-Demichel 2015's [exp(727.951334747),
exp(727.951336105)]. It reproduces, at ball grade, the localization Revers
reported at float grade for the Chao-Plymen region. Our margin at eta =
1.061e-4 is his 1.28492e-4 plus his worst-case zero budget Delta S1 = 1.899e-5,
as expected once the zero error is enclosed rather than bounded.

**Novelty.** Platt-Trudgian 2015 already carried the analogous theta(x) - x
computation in MPFI interval arithmetic. The claim here is an
enclosure-carrying localization of a pi(x) - li(x) sign change. It is novel only
against the recorded search (MISSION.md section (a): three papers and one web
search), which is not a literature search. No priority is claimed.

## 2. Gates and planted faults

- **Gate**: S* inside the ball. Passed. It was also within Revers's own zero
  budget (1.899e-5) by a factor of about 1e5.
- **R4 dropped** at eta = 1.06e-4. The lower bound moves by R4 = 3.380e-3, from
  -1.24e-4 to +3.256e-3: the sign flips. The error term is load-bearing and the
  pipeline sees it.
- **gamma_1 shifted by 1e-6**. S moves by 7.729e-5, and the faulted ball no
  longer contains S*. A one-zero error of 1e-6 is visible, and the gate catches
  it.
- Small-scale versions of both faults, plus an mpmath float sum over 120 zeros,
  are pinned in `test_skewes_terms.py`.

## 3. Observations about the source

- In Revers's Saouter-Demichel table, the row printed as eta = 0.0000155 with
  R = 5.15554e1 is the value at eta = 0.0000156. At 0.0000155, Theorem 3.1 gives
  R = 5473.12. Both rows are negative, so the paper's conclusion is unaffected.
- **An observation about two printed values**, not about the paper's results.
  arXiv:2501.04488 v2, subsection 6.2 ("Reworked Bays-Hudson region by
  Chao-Plymen, 2010"), prints "T=\gamma_{2000000}<1131944.4718". Subsection 6.3
  ("The Saouter-Demichel region, 2010") prints "T=\gamma_{22000000}<10379599.7274".
  Both are quoted from the TeX source. Two routes place each zero just above
  its printed value:

  | | Arb (route 1, Turing count) | mpmath (route 2, `nzeros`/`zetazero`, not rigorous) |
  | --- | --- | --- |
  | N(1131944.4718) | 1999999 | 1999999 |
  | N(1131944.4719) | 2000000 | 2000000 |
  | gamma_2000000 | [1131944.471824862268 +/- 5.91e-13] | 1131944.471824862268492 |
  | N(10379599.7274) | 21999999 | 21999999 |
  | N(10379600) | 22000000 | 22000000 |
  | gamma_22000000 | [10379599.72743106016 +/- 1.23e-12] | 10379599.72743106015977 |

  (Updated 2026-10-27: the Arb cell for gamma_22000000 first read "not isolated
  yet". Production B isolated it; the value is `last` in
  `shards_b2/shard_220.json`, and it agrees with mpmath.)

  So each printed decimal is the zero truncated to four places, a lower bound,
  where the text has "<". The same sentences also print
  "\gamma<1131945" and "\gamma<10379600", which are correct upper bounds. If T
  were taken literally as the printed decimal, the sum would omit one zero, a
  term of at most about 1.5e-8, far below either margin. This hunt sums to
  T = 1131944.4719 and 10379600, which both routes count to exactly 2e6 and 2.2e7.
- **Added 2026-10-27 (post-hoc review, measured, not pre-registered): the
  subsection 6.3 S* subtracts the second-order sum.** Split Revers's sum as
  S = S1 + S2, with S1 the first-order (Lehman) part over 1/rho and S2 the
  second-order part over 1/(omega rho^2), both with the same Gaussian weight.
  Subsection 6.3 quotes "the Saouter-Demichel machine value with size
  -1.002906086981405" (first order, S1 only, at their omega = 727.951335792,
  alpha = 6e12, 2.2e7 zeros). With S2 at omega = 727.951335792 from the first
  2e4 zeros, 1.68592e-5 (section 7 has the tail estimate),

      Saouter-Demichel's S1 - S2 = -1.0029229462,  Revers's S* = -1.0029229472,

  which agree to 1.0e-9. Theorem 3.1 adds S2, and so do our sums. At the
  Chao-Plymen point Revers's S* agrees with ours, that is with +S2, to 1.7e-10
  (section 1), and his quoted Chao-Plymen value -1.006569 is our S1 to its six
  printed decimals. So the 6.3 value appears to subtract S2 where the theorem
  adds it. Driver and data: `s2_check.py`, `s2_first20000.json`,
  `s2_comparison.json`, pinned by `test_skewes_terms.py`.
- **Added 2026-10-27 (measured): an apparent digit slip in the 6.3 table.**
  Every other positive row of both resizing tables equals -1 - S* - Delta S1 -
  Delta S2 - R, recomputed from the printed S*, R and Delta S values, to within
  5e-9 (R is printed to six digits). The row eta = 0.0000159 prints 0.000015987,
  but the printed values give 6.5986e-5 there, 4.9999e-5 more. A "1" for a "6"
  in the leading digit fits. The row is positive either way, so the paper's
  conclusion is unaffected. Pinned by
  `test_revers_saouter_demichel_row_1_59e_5_is_a_digit_slip`.

## 4. Cost

Isolation of 2e6 zeros took 26,981 s, **7.5 core-hours**: 12.5 to 17.5 ms/zero,
4 nice'd processes, 1.9 h wall. The estimate was 10 to 20 core-hours. Route 2 and
the sums cost minutes. The shard JSONs total under 100 KB, and checksums are in
`shards/SHA256SUMS`. No zero list is kept: each shard records the SHA-256 of its
zeros as printed.

## 5. Reproduce

```bash
.venv/bin/python -m pytest -q -n0 hunts/skewes_enclosure/test_skewes_terms.py
hunts/skewes_enclosure/run_shards.sh <outdir> 1 2 ... 20      # ~7.5 core-hours
.venv/bin/python hunts/skewes_enclosure/combine.py --target chao_plymen --shards <outdir>
```

The committed `shards/` are this run's outputs. `combine.py` on them reproduces
`shards/combined_chao_plymen.json`. Shard 1 was run with `--sample 200 --seed 152`
and shards 2 to 20 with `--sample 50 --seed 152000+k`.

## 6. Production B, 2026-10-26: the gate failed (attempt unresolved)

All 220 shards (1 to 20 from target A, 216 on the box, 217 to 220 from the
pilot, and 21 to 215 from Actions run 40363428968) are sound. Indices are
contiguous, every ball is ordered and disjoint within and across shards, the last
zero is below T = 10379600, and Arb's Turing count gives N(T) = 22,000,000
exactly. All 5150 route-2 brackets show a sign change. Isolation took
349,099 core-seconds = 97 core-hours in total: 87.4 on runners for shards 21 to 215
(88.6 by job wall time x 4 vCPU), plus 1.5 for the pilot, 0.6 for shard 216 and 7.5
for target A on the box. (An earlier version of this line said "about 64 on
runners". That was an unchecked guess, corrected on 2026-10-26.)

| quantity | value |
| --- | --- |
| S at omega = 727.95134, alpha = 6e12 | [-0.99067672 +/- 1.89e-9] |
| Revers's printed S* | -1.002922947193156 |
| difference | 0.012246, about 470x his zero budget (2.6e-5) |
| lower bound on I at eta = 2.28e-5 | [-0.01211835 +/- 3.6e-9] (negative: no conclusion) |

By the kill condition, the gate failed, so this hunt stops target B and asks
which side is wrong. What is known:

- **The pipeline reproduces Revers at the Chao-Plymen parameters** (section 1),
  with the same code and zero layer, to 1.7e-10. The runner shards reproduce the
  box bit for bit (smoke check), and target A's shards 1 to 20 feed both sums.
- **Leading hypothesis: omega.** Subsection 6.3 prints "\omega=727.95134".
  Revers's own history table gives the Saouter-Demichel omega as 727.951335792,
  and 727.951335792 rounded to five decimals is 727.95134. At alpha = 6e12 the
  Gaussian kernel has width about alpha^{-1/2} = 4e-7 in omega, so the
  4.2e-6 difference is about 10 widths. Over the first 1e4 zeros (Arb, 128-bit
  sums) the two omegas give -0.977409433 and -0.977376629, which differ by only
  3.3e-5, because gamma * Delta omega < 0.04 there. The phase shift grows like
  gamma and reaches 4 to 40 rad for gamma between 1e6 and 1e7. That is where the
  remaining -0.013 (ours) versus -0.026 (Revers) of the sum lives. **This is
  consistent with the hypothesis but does not test it.**
- **Why it cannot be tested from the stored data.** Shards store the zeros'
  SHA-256 and partial sums at the two fixed omegas only, so a new omega needs the
  zeros recomputed. Storing sums on an omega grid at almost no cost would have
  avoided this. That design gap is ours.
- Disposition (ALIGNMENT section 5): **attempt unresolved** for target B. It is not
  a refutation of Revers. The ball sum at omega = 727.95134 is itself a valid
  enclosure-carrying measurement, and at that omega the lower bound gives no
  conclusion.

## 7. The pre-registered omega-grid rerun (B2), 2026-10-27

Pre-registration: `PREREG_B2.md` and `omega_grid.json`, committed alone as
e5b33dc90 before any rerun result existed. Shards 1 to 68 come from Actions run
40415010866, which the projection rule stopped (RUNS.md). Shards 69 to 220 come
from run 40426999125. The computing code is byte-identical across both runs
(SHA-256 table in RUNS.md). Evaluation: `evaluate_b2.py`, output
`shards_b2/evaluation.json`.

**Completeness**: 220/220 shards are sound, every ball is ordered and disjoint
within and across shards, N(T) = 22,000,000 by Arb's Turing count, all 4400
route-2 brackets show a sign change, and every shard carries all 83 omegas.

**Control** at 727.95134: [-0.99067672 +/- 1.89e-9], identical to the production
B ball. The rerun reproduces production B.

**The rule** (|S - S*| + rad(S) <= B = 2.60111e-5):

| omega (pre-declared) | S | distance to S* = -1.002922947193156 | rule |
| --- | --- | --- | --- |
| 727.951335792 (H) | [-1.00288927 +/- 5.39e-9] | 3.367e-5 | **not met** |
| 727.951335426 (STD15's omega_0) | [-1.00136447 +/- 3.90e-9] | 1.558e-3 | not met |

**H is not supported.** The rounded-omega hypothesis accounts for most of the
production-B gap (0.0122 at the printed omega, 3.4e-5 at 727.951335792), but
not all of it, and the rule was fixed in advance. The remaining 3.4e-5 exceeds
even Revers's worst-case zero budget, so it is not explained by zeros accurate to
1e-9. Candidate explanations, none tested here: further omega digits beyond
those printed; double-precision reduction of gamma*omega ~ 7.6e9 mod 2 pi in a
"machine computation" (Platt-Trudgian 2015 warn that this degrades relative
accuracy to about 2^-17 at gamma = 1e9); or a different zero list or cutoff.
Subsection 6.3 prints the sum as "S^*(\alpha,\omega,T)\geq-1.002922947193156"
with a "\geq", and our value at 727.951335792 does satisfy that inequality. The
inequality was not the pre-registered rule, so this is noted, not used.
**Disposition (ALIGNMENT section 5): attempt unresolved** for reproducing
Revers's S*. It is not a refutation of his result, whose positive conclusion
holds at our value too (below).

**Superseded in part, 2026-10-27 (post-hoc review of PR #360; measured; not
pre-registered).** The paragraph above is kept as recorded. Its three candidate
explanations are replaced by one that was measured afterwards, and none of the
three is it. Split S = S1 + S2 as in section 3 (S2 is the 1/(omega rho^2) part).

- **S2 at omega = 727.951335792** over the first 2e4 zeros (gamma_20000 =
  18046.46) is 1.685921553e-5, an Arb ball of radius 2e-18. The tail beyond
  gamma_20000 is not bounded rigorously. A main-term estimate,
  (2/omega)(log(Gamma/2 pi) + 1)/(2 pi Gamma) = 2.2e-7, bounds it if N(t)
  followed its main term. Going from 1e3 to 2e4 zeros moved S2 by 2.4e-8, about
  1% of the same estimate at 1e3 zeros (2.0e-6). So the tail is probably of
  order 1e-9.
- **The identity.** Saouter-Demichel's printed first-order sum minus S2,
  -1.002906086981405 - 1.68592e-5 = -1.0029229462, equals Revers's S* =
  -1.0029229472 to 1.0e-9. With +S2, as Theorem 3.1 has it, the miss is 3.37e-5.
- **The rule gap is 2 S2.** S - S* = 3.3673e-5, and 2 S2 = 3.3718e-5. The
  4.6e-8 difference is the next item.
- **An end-to-end check of the 2.2e7-zero list.** Our first-order sum,
  S - S2 = -1.0029061335, matches Saouter-Demichel's independently computed
  -1.0029060870 to 4.7e-8. That is about 1/1250 of the 5.8e-5 margin at
  eta = 1.59e-5. One zero at height gamma moves S by up to about
  2 e^{-gamma^2/2 alpha}/gamma, depending on its phase. Below height about 5e6
  that can exceed 4.7e-8, so a missing or spurious zero there could show at
  this level. Above 5e6 a single zero moves S by at most about 5e-8, and it
  would take over 1000 of them to erase the margin.
- **Target A is consistent with +S2.** There S2 = 1.595e-5. Revers's S* matches
  our S1 + S2 to 1.7e-10 (section 1) and misses S1 - S2 by 3.19e-5. Chao-Plymen's
  quoted -1.006569 is our S1 = -1.0065694 to its six printed decimals.
- **The alternative omega is far worse.** omega = 727.9513358 is 727.951335792
  to seven decimals. Interpolating the pre-registered grid (degree-7 polynomial
  through the 8 nearest points) gives S(727.9513358) - S* = -8.0e-7. That is
  about 800 times the 1.0e-9 residual of the identity, and it uses +S2.

The pre-registered verdict stands: **H is not supported by its rule.** In
substance, though, H's omega was right. The S* Revers printed is built from the
sum at 727.951335792, and the rule failed on the sign of S2, not on omega. The
grade is measured: it uses two printed decimals from the source and S2 truncated
at 2e4 zeros with an estimated tail. The disposition for reproducing Revers's
S* becomes **explained at measured grade, post hoc**. Driver: `s2_check.py`
(`compute` writes `s2_first20000.json` in about 5 core-minutes; `compare` writes
`s2_comparison.json` in seconds). Pinned in `test_skewes_terms.py`.

**Descriptive grid** (all 83 values are in `evaluation.json`, and no claim is made
from them): S ranges from -1.00664805 to -0.99067672. No grid point meets the
rule. The nearest, 727.951337542, is 2.88e-5 away.

**Pre-declared localization at omega = 727.951335792** (alpha = 6e12,
A = 6.85e7, T = 10379600):

| eta | lower bound on I(omega, eta) |
| --- | --- |
| 2.28e-5 | [9.420e-5 +/- 2.0e-9] |
| 2.0e-5 | [9.425e-5 +/- 5.7e-9] |
| 1.8e-5 | [9.428e-5 +/- 3.9e-9] |
| 1.6e-5 | [9.401e-5 +/- 2.7e-9] |
| **1.59e-5** | **[5.833e-5 +/- 5.9e-9] > 0** |
| 1.58e-5 | [-4.08588e-3 +/- 3.3e-9] < 0 |

So **pi(x) > li(x) for some x with log x in [727.951319892, 727.9513517]**
(exact: [727.951319892, 727.951351692]). (Corrected 2026-10-27: the lower end
was first quoted as 727.9513199, rounded inward; see the correction at the top.)
The grade matches target A: a hardened computation on a cited derivation (Revers
Theorem 3.1, RH to A = 6.85e7), with completeness on Arb alone and route 2
sampled. This is the Saouter-Demichel region at Revers's narrowest eta. It is
not a new record: Saouter-Trudgian-Demichel 2015's interval is narrower and lies
inside this one. (Corrected 2026-10-27: this sentence first said "narrower and
lower". STD15's [727.951334747, 727.951336105] lies inside this interval, so its
lower end is higher than ours, not lower. The localization here follows from
theirs, if theirs holds.) At omega_0 = 727.951335426 every bound is negative (about -1.43e-3), so
nothing is claimed there. That is expected, because STD15 used alpha = 1.61e15
and 5.25e8 zeros, not this family.

**Planted faults** at both decisive points: shifting gamma_1 by 1e-6 moves S by
7.79e-5 and out of its own ball, and dropping R4 moves the bound by 3.20e-5.
Pinned in `test_skewes_terms.py`.

**Cost**: 106.2 runner core-hours by job wall for the whole rerun, against
a final cap of 150 (RUNS.md has the cap history and watcher incidents). The
zeros of all 220 shards are uploaded as 90-day artifacts, and each one's
decompressed SHA-256 equals its shard's `zeros_sha256`. A new omega or alpha
therefore no longer needs a recompute until they expire.

## 8. Literature note (2026-10-27)

M. Revers, *New bounds in R.S. Lehman's estimates for the difference
pi(x) - li(x)*, arXiv:2501.04488 v2 (J. Number Theory 2025), subsection 6.3,
appears to subtract the second-order sum S2 where its Theorem 3.1 adds it. The
printed S* = -1.002922947193156 equals the Saouter-Demichel first-order value
it quotes, minus S2 at omega = 727.951335792, to 1.0e-9. With +S2, the miss is
3.37e-5. Subsection 6.2 uses +S2 and agrees with our ball sum to 1.7e-10. The
evidence is in section 7. The grade is measured: two printed decimals, plus S2
truncated at 2e4 zeros with an estimated tail. The same subsection's table also
has an apparent digit slip at eta = 0.0000159, and its eta = 0.0000155 row is
the value at 0.0000156 (section 3).

None of these changes the paper's conclusions. At omega = 727.951335792, Theorem
3.1 with the correct +S2 still gives a positive lower bound at eta = 1.59e-5:
5.83e-5 (section 7). The paper's printed S* and R give 9.20e-5 there before
its Delta S. This lab
does not contact authors. The note is recorded here only.

## The doors

**Active constraints at the optimum.** The binding quantity is the smallest
eta with a positive lower bound, 1.061e-4. The binding constraints, ranked by how
much of R they hold at eta = 1.061e-4 (R = 6.406e-3):

1. **R4, the truncation at T** (3.380e-3, 53%). It falls fast with T: 9.79e-4 at
   T = 1.25e6 and 5.3e-5 at T = 1.5e6.
2. **R1**, the prime-side floor 2/(omega - eta) + ... (2.763e-3, 43%).
   Theorem 3.1 fixes it, and it does not move with zeros or alpha.
3. **R6**, the RH-to-A and Gaussian-tail term (2.63e-4 at 1.061e-4, 5.35e-4 at
   1.060e-4). It is the term that sets the eta floor: it grows like
   e^{-alpha eta^2/4 + omega/2}. Zero error, which Revers bounded at 1.9e-5, is no
   longer a constraint (1.3e-10).

**The frozen-constant inventory.** These numbers were chosen, not optimized:

- omega = 727.952018, Revers's choice. Re-optimizing omega reads the same zeros,
  so the trade shape is genuine and cheap.
- alpha = 1.34e11. Raising it narrows the eta floor (it scales like
  sqrt(omega/alpha)), but it raises R4 unless T grows: a genuine trade against
  zero count.
- T = gamma_2000000. More zeros cut R4 sharply. Cost is linear at about
  13 ms/zero.
- A = 1.022e7, a cited input. RH is known to 3e12, so A could be raised for free
  inside R6. (Corrected 2026-10-27: false, see below.)
- The 64-bit isolation precision, and the route-2 sample of 1150. Neither binds.

**Correction (2026-10-27, review of PR #360): A is a binding constant with a
two-sided trade, not a free door.** R6 has two terms. The first,
(1 + 22/(A omega)) 8.283 log A e^{-alpha eta^2/4 + (omega+eta)/2}, grows like
log A. The second, 7.152 eta A log A e^{-A^2/2 alpha + (omega+eta)/2}, falls off
a cliff once A^2 is well above alpha omega, that is A above sqrt(alpha omega) =
9.9e6 here. So the best A sits just above the cliff, which is where Revers put
it, and raising A toward the verified RH height costs margin. R6 and the lower
bound at eta = 1.061e-4, with our S and every other parameter as in section 1
(all hypotheses of Theorem 3.1 hold at each A):

| A | R6 | lower bound on I |
| --- | --- | --- |
| 1.0e7 | 12.885 | -12.884 |
| **1.022e7 (Revers)** | **2.634e-4** | **+1.475e-4** |
| 6.85e7 | 2.935e-4 | +1.173e-4 |
| 3.06e10 | 3.928e-4 | +1.807e-5 |
| 3e12 | 4.674e-4 | -5.653e-5 |

At A = 3e12 the bound is negative, so "raise A for free" would have destroyed
the result. Raising alpha also forces A up like sqrt(alpha omega), so the alpha
door pays this log A cost too. Pinned by `test_doors_A_is_binding_not_free`.

**The information class of each door.** Re-choosing omega and A stays inside the
data the current run reads: the same 2e6 zeros and a cited RH height. Raising
alpha or T needs more zeros, which means reading more of the same kind of data
(target B is that door at 2.2e7 zeros). Lowering R1 needs new analysis on the
prime side, not more data: Saouter-Trudgian-Demichel's weighted kernel
(1 + 2u + 9.336u^2) is one such route, and it is not computed here. This is a
measured optimum at one parameter family, not a proved ceiling. (Corrected
2026-10-27: re-choosing A needs no new data, but it is not an open door. A is
already near its optimum, just above the R6 cliff, and moving it either way
costs margin, per the table above.)

**Doors at the Saouter-Demichel point (added 2026-10-27).** At omega =
727.951335792, alpha = 6e12, the floor is eta = 1.59e-5. R = 2.831e-3 there:
R1 = 2.763e-3 (98%), R6 = 3.6e-5 (which sets the eta floor, as before) and
R4 = 3.2e-5. The constraint that dominates R is R1, which is prime-side and
fixed by Theorem 3.1. More zeros could recover at most R4 = 3.2e-5, about half
the 5.8e-5 margin at the floor, but they cannot move R1. That is a different
balance from target A, where R4 was 53% of R. The frozen constants are the same, plus the
grid spacing of 5e-8, which is descriptive only. Information class: reaching
STD15's omega_0 needs alpha near 1.6e15 and about 5e8 zeros, which reads more of
the same data. Lowering R1 needs new prime-side analysis (STD15's weighted
kernel), not more data. The uploaded zero balls make any alpha <= 6e12 study on
these 2.2e7 zeros free of isolation cost until the artifacts expire.

(Corrected 2026-10-27: "the frozen constants are the same" carried over the false
"A for free" door. At B, A = 6.85e7 is again just above the R6 cliff,
sqrt(alpha omega) = 6.6e7. At eta = 1.59e-5 and omega = 727.951335792:

| A | R6 | lower bound on I |
| --- | --- | --- |
| 6.6e7 | 3.585e5 | -3.585e5 |
| 6.7e7 | 5.597 | -5.597 |
| **6.85e7 (Revers)** | **3.624e-5** | **+5.832e-5** |
| 1e8 | 3.674e-5 | +5.782e-5 |
| 3.06e10 | 4.816e-5 | +4.640e-5 |
| 3e12 | 5.730e-5 | +3.726e-5 |

Here the bound stays positive at A = 3e12, but the margin falls by 36%. A is
binding at both points.)

