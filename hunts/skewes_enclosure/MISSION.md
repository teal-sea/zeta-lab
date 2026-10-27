# MISSION: `skewes_enclosure`, a ball-arithmetic Lehman localization of a sign change of pi(x) - li(x)

**Opened 2026-10-26. Hunt #152.** Part of the compute sweep the owner funded on
2026-10-26: walls the record calls cost walls rather than mathematical
ceilings, to be knocked down with hardened results. Nothing in this directory is a
result until the case log in `hunts/README.md` says how it ended.

Grades used here: *measured* (one route, float grade), *hardened* (independent
routes agree, or ball enclosures carry every step), *kernel-checked* (Lean). A
composite claim takes the grade of its weakest step. The reserved enclosure word
belongs to `zeta/rigor.py` and the Lean arm and appears nowhere in this directory.

## The question

> Can a sign change of pi(x) - li(x) be localized with every computed step
> carried by ball arithmetic: Lehman's integral with Revers's 2025 error terms,
> summed over the first ~2.2e7 zeta zeros, every zero an Arb enclosure with a
> second route?

## Why

`hunts/rogue_frontier/IDEA_PORTFOLIO.md` (lines 188-192) and
`hunts/rogue_frontier/FRONTIER_MAP.md` (lines 1284-1292) record that every
published crossover localization is float grade. That premise was unverified
when this hunt opened. The day-one read below checks it.

## Day-one read (2026-10-26, before any zero was computed)

Sources read, with what was read:

- **[STD15]** Y. Saouter, T. Trudgian, P. Demichel, *A still sharper region where
  pi(x) - li(x) is positive*, Math. Comp. 84 (2015) 2433-2446. Read: the
  submitted version (ANU Open Research, "Vers. 1 - Sub. to MCOM", 11 Jun 2013),
  sections 7 to 10. The published version was not read; its computational
  section may differ.
- **[PT15]** D. Platt, T. Trudgian, *On the first sign change of theta(x) - x*,
  arXiv:1407.1914 (Math. Comp. 2016). Read: the arXiv TeX source, all sections.
- **[Rev25]** M. Revers, *New bounds in R.S. Lehman's estimates for the difference
  pi(x) - li(x)*, arXiv:2501.04488 v2 (J. Number Theory 2025,
  doi S0022314X25002045). Read: the arXiv TeX source, Theorems 2.1 and 3.1 and
  section 6 (numerical applications, subsections 6.1 to 6.4).

### (a) Novelty: did any of them carry every step in interval arithmetic?

| paper | target | zeros used | zero accuracy | arithmetic of the zero sum |
| --- | --- | --- | --- | --- |
| [PT15] | theta(x) - x | ~2e10 (T = 6.97e9) | +/- 2^-102, from Platt's rigorous RH verification to 3.06e10 | **MPFI multiple-precision interval arithmetic for all floating-point work**; the sum is stated as the interval [-1.0013360278, -1.0013360277] |
| [STD15] | pi(x) - li(x) | 5.25e8 (T = 2e8) | "correct up to twenty decimal places", eps = 5e-21, source not stated in the read sections | not stated; the zero-error term is bounded by a mean-value argument (their (7.2)), and "the roundoff error was not added" to the final margin; J(omega_0) = 7.0294e-6 +/- 1e-10 is quoted without saying how the +/- was obtained |
| [Rev25] | pi(x) - li(x) | 2.2e7 (T = gamma_22000000 < 10379599.7274) | assumed abs. error <= 1e-9, source not stated | Mathematica 13.3/14.1 "machine computation"; zero error bounded by the mean-value argument (Delta S1 <= 2.6011e-5); no rounding-error bound for the sum itself |

Finding, as a bounded search of three papers and one web search (2026-10-26,
query on Lehman method plus interval arithmetic plus rigorous zeros, 2023 to 2026,
which returned nothing newer than [Rev25]):

1. The premise is **half right**. For pi(x) - li(x), neither paper read carries
   the zero sum in interval arithmetic, and neither cites a rigorous source for
   its zeros. Both are float grade with an analytic zero-error budget.
2. For theta(x) - x the same Lehman-type method **has already been carried in
   interval arithmetic** with rigorous zeros, by [PT15]. So the method is not
   new to interval arithmetic. The delta this hunt can offer is narrow:
   [PT15]'s arithmetic discipline applied to pi(x) - li(x) with [Rev25]'s error
   terms, with zeros taken from an Arb isolation and checked by a second route.
3. The kill condition "prior work already interval grade" **does not fire** for
   pi(x) - li(x). It would fire if the published [STD15] or an unread paper (for
   example Saouter-Demichel 2010, Chao-Plymen 2010, or Bays-Hudson 2000, none read
   today) turned out to use interval arithmetic. That check stays open, and no
   novelty is claimed.

### (b) Bits per zero needed

The sum's sensitivity to one zero is |d s / d gamma| <= 1508.2 / gamma at
omega ~ 727.95 ([Rev25] subsection 6.1, its bound labelled RieleS1 in the source). Summed over
zeros with sum 1/gamma ~ (1/4 pi) log^2(T/2 pi) = 16.31 at T = 1.038e7, a uniform
zero error eps moves the sum by at most about 2.46e4 eps. To keep that under
1e-7, a thousandth of the expected margin, needs eps <= 4e-12 ~ 2^-38 absolute.
At gamma < 2^23.4 that is about **62 significant bits per zero**. The term
e^{i gamma omega} needs gamma*omega ~ 7.6e9 ~ 2^33 reduced mod 2 pi, so the
working precision must be at least about 33 + 40 bits. Arb at 128 bits returns
radii near 1e-31 at gamma ~ 1e7 (measured below), about 2^-103, which leaves
roughly 65 bits of headroom. **The precision requirement is far inside what
isolation delivers**, so the second kill condition does not fire.

For [STD15]'s parameters (T = 2e8, sum 1/gamma ~ 23.75, margin 6.12e-6), the same
argument needs eps ~ 1e-12, again comfortable. That target needs 5.25e8 zeros,
about 24x this hunt's, and is out of scope here.

### (c) Expected positive margin

`skewes_terms.py` (this directory) re-evaluates [Rev25] Theorem 3.1's R1 to R6
at the Saouter-Demichel parameters omega = 727.95134, alpha = 6e12, A = 6.85e7,
T = 10379600 (see the T note in `skewes_terms.py`). It reproduces the R column of [Rev25]'s Saouter-Demichel resizing table to all six printed digits at
eta = 2.28e-5, 1.6e-5, 1.59e-5 and 1.58e-5 (2.79507e-3, 2.79527e-3, 2.83095e-3,
6.97516e-3). R is dominated by R1 = 2/(omega - eta) + ... = 2.763e-3 and
R4 = 3.2e-5. With [Rev25]'s float sum S* = -1.002922947193156:

    I(omega, eta) >= -1 - S* - R = 2.9229e-3 - 2.7951e-3 = 1.279e-4  (eta = 2.28e-5)

[Rev25] subtracts its worst-case Delta S1 = 2.6e-5 to get 1.0186e-4. With
ball-arithmetic zeros the zero term is negligible, so **the expected margin is
about 1.28e-4**, about 4.4% of the sum's excess over -1. That is about 1e3 times
any plausible rounding effect, and about 1.3e-4 / 2.46e4 ~ 5e-9 in uniform zero
error before the sign flips.

A cheaper first target is the Chao-Plymen region (omega = 727.952018,
alpha = 1.34e11, 2e6 zeros, eta down to 1.061e-4), where [Rev25]'s Chao-Plymen resizing table gives a
margin of about 3.9e-4 before its Delta S1. It uses a tenth of the zeros and is
the proposed first production unit.

### Go or no-go

**GO, with the novelty claim narrowed** as in (a). Neither kill condition
fires. What the hunt can deliver, if it succeeds: a hardened localization of a
point x in [exp(omega - eta), exp(omega + eta)] with pi(x) > li(x), at [Rev25]'s
parameters. It inherits the analytic inequality of [Rev25] Theorem 3.1 as a cited,
peer-reviewed derivation that this hunt does not re-derive. It also inherits the
hypothesis that RH holds to height A = 6.85e7 as a cited theorem (Platt 2017,
Platt-Trudgian 2021). The hardened grade covers the computation; the composite
claim is "hardened computation on top of a cited derivation". That is weaker
than an interval-grade result whose analytic step was also checked here.

## Coordinator decision (2026-10-26)

- **Production A approved**: the Chao-Plymen target, 2e6 zeros, on this box. The
  gate is that Revers's printed S* = -1.006553478788955 lies inside the ball
  sum, or within his stated zero-error budget. The result is recorded either way.
- **Production B approved in principle, conditional on A passing**: 2.2e7
  zeros through a GitHub Actions workflow on this branch, reviewed by the
  coordinator before its trigger file is committed.
- **Novelty, stated plainly.** Platt-Trudgian 2015 already carried theta(x) - x
  in MPFI interval arithmetic. The claim this hunt can make is an
  enclosure-carrying localization of a pi(x) - li(x) sign change. It is novel
  only against the recorded search in section (a): three papers and one web
  search. That is not a literature search, and no priority is claimed.
- **Recorded observation.** In [Rev25]'s Saouter-Demichel resizing table, the
  row printed as eta = 0.0000155 with R = 5.15554e1 is the value of Theorem 3.1's
  R at eta = 0.0000156. At 0.0000155 the formula gives R = 5473.12. Both rows are
  negative lower bounds, so the paper's conclusion is unaffected. This is pinned by
  `test_revers_row_labelled_1_55e_5_is_the_value_at_1_56e_5`.

## Inputs and their grades

| input | source | grade here |
| --- | --- | --- |
| Theorem 3.1 inequality and R1-R6 | [Rev25], peer reviewed (JNT 2025) | cited derivation, not re-derived |
| RH to height A = 6.85e7 | Platt (2017, to 3.06e10), Platt-Trudgian (2021, to 3e12) | cited theorem |
| zeros gamma_1 .. gamma_N, N = 2.2e7 | Arb `acb_dirichlet_zeta_zeros` via python-flint 0.9.0 | ball enclosures (route 1) |
| completeness N(T) | Arb `arb.zeta_nzeros` (Turing's method) | ball arithmetic (route 1) |
| zero cross-check | see "Rivals and the gate", route 2 | to be stated per zero |
| the sum S(alpha, omega, T) and R1-R6 | python-flint `arb`/`acb` at 128 bits | ball arithmetic |

## Rivals and the gate

- **Route 2 for the zeros.** Arb's zero routine implements Platt's algorithm
  (Platt and Johansson in Arb), so a second route that shares the least code is:
  (i) per-zero sign checks of Hardy's Z at the two ends of each Arb bracket
  (widened to 2^-60), evaluated in mpmath (mpmath `siegelz` at high dps, float
  route, or `mpmath.iv` where cost allows), which shares no code with Arb but
  only tests existence of a zero in the bracket; (ii) completeness is the shared
  layer: both routes rely on Arb's Turing count unless an independent count is
  found. A cited table (Platt's LMFDB zeros, +/- 2^-102, MPFI code) would share
  algorithm lineage but not code; its download location was not found on
  2026-10-26 and is an open item. Per-zero mpmath checks at height 1e7 may be too
  costly for all 2.2e7 zeros; if so, route 2 runs on a stated random sample, and
  the hardened grade then covers only the Arb route with a sampled cross-check.
  RESULTS.md must say which.
- **The gate for the sum.** Reproduce [Rev25]'s float values first: S* =
  -1.006553478788955 (Chao-Plymen parameters) and S* = -1.002922947193156
  (Saouter-Demichel parameters). Planted faults must widen or flip the result:
  drop one error term (R4) and see the margin change by the expected amount;
  perturb one zero by 1e-6 and see the ball move by about 1508/gamma * 1e-6.
- **Structure-matched rival.** Not applicable in the usual sense: this is a
  computation about the actual primes, not a structural explanation of RH. A
  Davenport-Heilbronn run would need a different explicit formula; none is
  planned.

## Kill conditions

- The published [STD15], or an earlier crossover paper, already carries the sum
  in interval arithmetic with rigorous zeros: the hunt shrinks to a reproduction
  of [Rev25]'s terms, recorded as such.
- The precision needed per zero exceeds what isolation delivers at the
  working precision the budget allows.
- The ball sum, at [Rev25]'s parameters, does not reproduce [Rev25]'s float S*
  to within its stated error budget: stop and find out which side is wrong.
- The planted faults do not move the result: the pipeline cannot fail, so it
  checks nothing.

## Write scope

- **May write:** `hunts/skewes_enclosure/` (this directory) and its case-log
  entry in `hunts/README.md`.
- **May not write:** `zeta/`, `ontology/`, `harness/`, `lean/`, `scripts/`, other
  hunts, `docs/`. Helper code lives here. Large outputs (zero tables) stay out of
  git, under 100 MB per file and 300 MB in total, recorded by SHA-256.

## Compute rules

The box is shared: at most 4 processes, `nice -n 10`, wait while the 1-minute
load exceeds 64 before any job longer than a minute, and stop the newest job if
MemAvailable falls below 20 GiB. Every estimate goes in `RUNS.md` before the
spend. Anything over one core-hour is asked of the coordinator first. Production
(2e6 or 2.2e7 zeros) is over that line and waits for an answer.

```huntspec
id: skewes_enclosure
question: Can a sign change of pi(x) - li(x) be localized with every computed step in ball arithmetic, using Lehman's integral with Revers's 2025 error terms over the first ~2.2e7 zeta zeros?
frontier: pi(x) > li(x) somewhere in [exp(727.951334747), exp(727.951336105)] (Saouter-Trudgian-Demichel 2015, float-grade zero sum); Revers 2025 resized eta to 1.59e-5 at the Saouter-Demichel region with 2.2e7 zeros, float grade; Platt-Trudgian 2015 carried the analogous theta(x) - x sum in MPFI interval arithmetic
proposed_attack: Arb zero isolation plus Turing count, Revers Theorem 3.1 error terms evaluated as arb balls, zero sum accumulated in acb at 128 bits
dead_routes:
  - none recorded for pi(x) - li(x) in this lab; the Saouter-Trudgian-Demichel 2015 secondary candidate omega = 727.951332982 was set aside by its authors as needing about 1e12 zeros, out of scope here
required_oracles:
  - Arb ball arithmetic (python-flint 0.9.0, acb_dirichlet zero isolation and Turing count)
  - Hardy Z sign checks in mpmath at Arb bracket endpoints, a code-disjoint second route
  - published float values in the two resizing tables of Revers 2025 subsections 6.2 and 6.3 as the reproduction target
kill_conditions:
  - a published crossover paper already carries the pi(x) - li(x) zero sum in interval arithmetic with rigorous zeros
  - the precision needed per zero exceeds what Arb isolation delivers at the affordable working precision
  - the ball sum fails to reproduce Revers's float S* within his stated zero-error budget
  - planted faults (one error term dropped, one zero perturbed by 1e-6) leave the result unmoved
agents_may:
  - search
  - derive
  - code
  - attack
  - compute within the compute gate in RUNS.md
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
  - start a job over one core-hour without the coordinator's answer
```
