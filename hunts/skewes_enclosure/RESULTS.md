# RESULTS: `skewes_enclosure` (hunt #152)

Status on 2026-10-26: **production A done, its gate passed. Production B ran
(2.2e7 zeros) and its gate FAILED** (section 6). That attempt is unresolved:
the leading hypothesis is a rounded omega in the source, and testing it needs a
recompute. Nothing here is promoted: the grades below
are this hunt's report, not a reviewer's.

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

**Measured claim, with its dependencies.** With every computed step carried by
Arb balls, I(727.952018, 1.061e-4) > 1.4747e-4 > 0. By the positivity argument
in Revers's "Runs of successive integers" subsection, pi(x) > li(x) for some x with log x in
[727.9519119, 727.9521241]. This rests on four inputs:

1. **Revers 2025 Theorem 3.1** (JNT 2025, peer reviewed). It is cited, and
   this hunt does not re-derive it. Its R1 to R6 are evaluated exactly as printed.
   They reproduce both of his resizing tables (13 rows, `test_skewes_terms.py`).
2. **RH to height A = 1.022e7.** Cited: Platt (2017, to 3.06e10) and
   Platt-Trudgian (2021, to 3e12).
3. **The zeros and their completeness: route 1 only.** Arb's
   `acb_dirichlet_zeta_zeros` and Turing count. Every ball is disjoint from
   and below the next, both within and across shards. The last zero is below T,
   and N(T) = 2,000,000.
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
  | gamma_22000000 | not isolated yet | 10379599.72743106015977 |

  So each printed decimal is the zero truncated to four places, a lower bound,
  where the text has "<". The same sentences also print
  "\gamma<1131945" and "\gamma<10379600", which are correct upper bounds. If T
  were taken literally as the printed decimal, the sum would omit one zero, a
  term of at most about 1.5e-8, far below either margin. This hunt sums to
  T = 1131944.4719 and 10379600, which both routes count to exactly 2e6 and 2.2e7.

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
349,099 core-seconds = 97 core-hours in total, about 64 of them on runners.

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
  inside R6.
- The 64-bit isolation precision, and the route-2 sample of 1150. Neither binds.

**The information class of each door.** Re-choosing omega and A stays inside the
data the current run reads: the same 2e6 zeros and a cited RH height. Raising
alpha or T needs more zeros, which means reading more of the same kind of data
(target B is that door at 2.2e7 zeros). Lowering R1 needs new analysis on the
prime side, not more data: Saouter-Trudgian-Demichel's weighted kernel
(1 + 2u + 9.336u^2) is one such route, and it is not computed here. This is a
measured optimum at one parameter family, not a proved ceiling.
