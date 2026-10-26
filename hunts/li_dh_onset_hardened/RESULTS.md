# RESULTS: hunt #151

**Status, 2026-10-26: the pre-registered statement is established at the grade
*hardened*.** For the classical Davenport-Heilbronn function:

> **lambda_{328997}(DH) < 0, and lambda_n(DH) > 0 for every 1 <= n < 328997.**

The values: lambda_{328997} = [-2379.96470663976248370528984220 +/- 4.4e-27]
and lambda_{328996} = [+1385.31521851949223176484827912 +/- 2.9e-27]. Every one
of the 328,996 earlier balls lies entirely above 0, none undecided, and the
smallest is lambda_1 = 0.0976361468... Two production runs at different radii
(c = 5000 with 2^21 nodes, c = 2500 with 2^19) give the same n\*. Their balls
intersect at every n <= 500,000, and both runs passed the xi control and the
mpmath.iv node check inside the run. The index is exactly the n\* = 328997 that
hunt #128 extrapolated 66 times past its data, so the pre-registered prediction
is **confirmed** (section 4).

*Hardened* means two things here. Every step carries an Arb ball: the
admissibility certificate, M(rho), the node samples, the branch steps, the DFT
and the aliasing bound. And independent routes agree where they exist: two
radii, mpmath.iv at sampled nodes, and #128's float table. It is **not
kernel-checked**, and not reviewed outside this lab, so it is pending external
verification. One shared failure mode is named and not excluded: both radii use
the same Arb evaluator for f (four `acb.zeta` calls), and the independent
mpmath.iv route checks it at 20 nodes per run, not at all 1.3 million.

The repricing: hunt #128 priced this at about 20,000 core-hours. Both runs
together cost **0.46 core-hours** (1211 s and 447 s, single process). The wall
was a cost wall of the r <= 0.99 family, refuted at the stated parameters by
the run itself (category 1 below). Nothing here bears on the Riemann Hypothesis
(`docs/08`): every number is about the Davenport-Heilbronn function f, which
has no Euler product.

The first-wave record follows unchanged (its status line read "first wave done,
production not run"); section 4 and the dispositions are the production
addendum.

## 1. The admissibility certificate (`admissibility.py`)

Computed in Arb at 128 bits on the box B = [-3/4, 7/4] x (0, T):

| item | T = 160 | T = 133 (the brief's ceil(sqrt(3c)) + 10) |
|---|---|---|
| N_box (argument principle, Backlund fold) | **98**, ball [98 +/- 3e-32] | **78** |
| N_line (sign changes of F(1/2+it), grid 1/64) | **94** | **74** |
| located off-line zeros right of the line, count 1 each | pair1, pair2 (q = 2) | pair1, pair2 |
| N_box = N_line + 2q | **closes** | **closes** |
| drop one quadruple | breaks (98 != 96) | breaks |
| displace pair1's square by 1e-14 | count 0, breaks | count 0, breaks |
| wall time | 14 s | 12 s |

The pieces, each a ball statement:

- **Half-plane.** S(3/2) = sum_{n>=2} |a_n| n^{-3/2} = [0.737590649449... +/-
  1.5e-31] < 1, so f has no zero with Re s >= 3/2 and, by F(s) = F(1-s), none
  with Re s <= -1/2. S(7/4) = 0.4177..., so Re f > 0 on the right edge. The sum
  crosses 1 between 1.3950 and 1.3952, which pins #128's 1.3951 in balls.
- **Real axis.** f > 0 on [1/2, 7/4]: 82 real balls away from s = 1. Near s = 1,
  f(1) = 0.922801873802... comes from Arb's `dirichlet_l` and a Cauchy bound on f'
  (max |f| <= 1.3499 on |s - 1| = 1/4) gives a drift of at most 0.0900 on
  |s - 1| <= 1/64. G > 0 on the real axis, so F has no real zero in B.
- **Box count.** By F(s) = F(1-s) and F(conj s) = conj F(s), the boundary integral
  folds to N_box = (Im log G(1/2+iT) + arg f(1/2+iT))/pi. Here arg f is the
  principal value up the right edge, where Re f > 0, and is then continued
  along the top edge in 28 ball segments, each with its image in one open
  half-plane.
- **Located zeros.** Squares of half-width 1e-15 around hunt `flow_repair`'s
  40-digit values. Each square's argument-principle count is exactly 1
  (56 and 148 segment evaluations). Over the square, |1 - 1/s| is
  [0.999957995600177600 +/- 5.5e-19] for pair1 and [0.9999884276114027916 +/-
  9.4e-20] for pair2.

**What the equality buys.** The N_line sign changes are N_line distinct line
zeros. The squares hold q zeros right of the line and, mirrored by
s -> 1 - conj s, q zeros left of it. Equality leaves nothing over. So below
height T every zero with Re s > 1/2 is pair1 or pair2, and every line zero is
simple.

**Zeros with Re s > 1.** Davenport and Heilbronn (1936) proved that f has
infinitely many zeros with Re s > 1. The box covers them: no zero has
Re s >= 3/2 < 7/4, so any such zero below T lies inside B. It would raise
N_box without being a sign change or a located square, and the equality would
break. It does not break, so none exists below T = 160.

**Above T.** A zero with Re rho = sigma in (1/2, 3/2) and |Im rho| > T has
|1 - 1/rho|^2 = 1 - (2 sigma - 1)/|rho|^2 > 1 - 2/T^2. At T = 160 that floor is
0.99996094, which lies beyond pair1's 0.99995800. So

    R_a = min over zeros with Re > 1/2 of |1 - 1/rho| = |1 - 1/rho_1| = 0.9999579956001776 (+/- 6e-19),

with pair1 the binding zero (1 - R_a^2 = 8.4007e-5). At the brief's T = 133 the
above-T floor 0.99994347 binds instead, which is still admissible for c = 5000
but wastes a quarter of the gap. That is why T = 160: it is the first height at
which pair1 binds (T >= 154.3).

**c = 5000 is admissible:** r = sqrt(1 - 1/5000) = 0.99990000 < R_a, and
ln(R_a/r) = 5.80e-5. **The judge's c = 1e4 statement checks:**
r = 0.99995000, and the midpoint circle (1 + r)/2 = 0.99997500 lies beyond
R_a = 0.99995800. Any valid aliasing circle at c = 1e4 sits in a window of
width 8e-6. Step 3 prices that window at 9.2e6 nodes for n <= 4e5 and 9.9e6
for n <= 5e5 (2^24 after rounding), the same order as the judge's 1.3e7.

**Kill condition 1 does not fire.** The completeness equality closes in balls
at c = 5000, and with it at every c up to 1/(1 - R_a^2) = 11904.

## 2. The evaluator, the second route and the controls (`evaluator.py`, `iv_route.py`)

- **Timing**, on 1000 nodes spread over the upper half of the c = 5000 circle at
  N = 2^20, single process, contended box (load 27 to 36 on 32 vCPU): **1.03 ms per
  node at 200 bits, 1.83 ms at 250 bits** (log G + log|f|, four `acb.zeta` and one
  `acb.lgamma`). Hunt #128's mpmath evaluator measured 92 ms at 142 digits, so
  Arb is about 50 to 90 times faster per node.
- **mpmath.iv route** at 20 nodes chosen by height (Im s from 0.45 to 4958,
  including both off-line pairs, the box top and the large-|s| stretch). It
  uses its own Euler-Maclaurin Hurwitz sum, its own kappa solve and its own
  node built from c and k. Every Arb ball for f and for log G meets the iv box,
  and the iv boxes are 1e-44 to 7e-40 wide at 160 bits. **Planted:** an Arb leg
  with kappa moved by 2^-120 misses the iv box at 17 of 20 nodes.
- **xi positive control.** The same ball trapezoid pointed at xi
  (r = 1/2, aliasing circle 7/10, M <= 4.08, N = 260, 160 bits) contains all 48
  values of `data/li_lambda_dps30_methodcauchy_n48_radius0.5.json`, with ball
  radius 1.2e-28. **Planted:** Gamma(s/2) moved to Gamma(s/2 + 2^-60) leaves 0
  of 48 contained, and a 2 pi i branch slip in half the samples leaves 12 of 48.
- **Two radii for DH, n <= 200**: r = 0.9 (rho = 0.95, M <= 23.32, N = 1624) and
  r = 0.99 (rho = 0.995, M <= 454.9, N = 16178), 192 bits. The balls intersect at
  every n, with a largest difference of 2.0e-30. Each contains #128's float table
  at all 200 indices (to 1e-26), and all 200 coefficients are positive.
  lambda_1(DH) = [0.097636146809519671181548974393959334 +/- 3e-37],
  lambda_200(DH) = [467.68488655023814608084760783857 +/- 1.1e-30].
  **Kill condition 2 does not fire.** This moves "lambda_n(DH) > 0" from
  hardened-for-n <= 12 (#128's zero side) to **hardened for n <= 200**.

## 3. The trapezoid and branch bookkeeping (`trapezoid.py`, `sizing.py`)

**The aliasing bound.** For r < rho < R_a and N nodes,

    |lambda_n - n btilde_n| <= n M(rho) rho^{-n} x/(1 - x),   x = (r/rho)^N,      (A)

with M(rho) bounding max |g - C| on |z| = rho for any constant C. Only b_0 sees
the branch constant. `li_balls` adds (A) as a ball to every coefficient.
`test_the_aliasing_bound_holds_and_is_not_vacuous` pins two things. First, at
r = 0.9, N = 400, the true error lies below (A) at n = 1, 10, 20, 40. Second,
with rho = 0.999 the bound is within 1e4 of that error. At rho = 0.95 it is
valid but about 1e10 too large, because the true decay is set by R_a near 1.

**M(rho) in balls.** An adaptive arc cover of the upper half circle (conjugate
symmetry gives the rest) bounds M(rho). Each arc contributes |log G| from an Arb
ball. Where Re s > 3/2 it adds |Log f| <= -log(1 - S(3/2)) + arcsin S(3/2).
Elsewhere it adds |log|f|| plus the continued arg f, chained arc to arc. The
chain must return to arg f = 0 at s = 1/(1+rho), where f > 0, and it does at
every circle:

| rho | M(rho) <= | arcs | seconds |
|---|---|---|---|
| 1 - 5.0e-5 | 91,602 | 4906 | 41 |
| 1 - 4.6e-5 | 101,111 | 5129 | 45 |
| 1 - 4.4e-5 | 106,603 | 5273 | 44 |
| 1 - 4.3e-5 | 109,567 | 5346 | 46 |

The large-|s| end sets M: log Gamma near s = 1/(1 - rho), about 2e4.

**The branch on the sampling circle.** g = log G + log f. log G is Arb's
analytic log-gamma. log f is the principal Log on the contiguous stretch with
Re s > 3/2. Re s on the circle decreases monotonically in the angle, so that
stretch is the first block of nodes. Through the rest of the circle, arg f is
continued over blocks of up to 256 nodes. Each block is enclosed in one arc
ball whose f-image must lie in an open half-plane. If a single step between
neighbours is still undecided, the arc between them is bisected and f is
evaluated at the new points. A zero on the contour exhausts the depth and is
refused. `test_the_branch_step_refuses_a_zero_on_the_contour` plants one, and
`test_coarse_sampling_is_bridged_not_refused` checks that 32 nodes at
r = 0.99 still close. The chain must contain arg f = 0 at s = 1/(1+r).

**The production node count** (`artifacts/sizing.json`). Tolerance 1e-10 on
every lambda_n, n <= n_max. N is the aliasing requirement, rounded up to a power
of two for `acb.dft`. Only the upper half is sampled, N/2 + 1 evaluations,
priced at the contended 250-bit rate of 1.83 ms.

| c | n_max | N from (A) | N used | bits | sampling core-hours |
|---|---|---|---|---|---|
| 2000 | 500,000 | 334,456 (but N > n_max) | 2^19 | 270 | 0.13 |
| 2500 | 500,000 | 440,992 | 2^19 | 234 | 0.13 |
| 3000 | 400,000 | 523,308 | 2^19 | 186 | 0.13 |
| 4000 | 500,000 | 844,397 | 2^20 | 180 | 0.27 |
| **5000** | **500,000** | **1,214,771** | **2^21** | **162** | **0.53** |
| 10000 | 500,000 | 9,891,055 | 2^24 | 126 | 4.26 |

Add `acb.dft`: measured 2.9 s at 2^18 and 192 bits, so about 30 s at 2^21. Add
M(rho): 45 s. The branch cover and its overhead are measured by the rehearsal
below. **At c = 5000 the whole production is about 0.6 core-hours; at c = 2500
it is about 0.2.** Hunt #128 priced the r <= 0.99 plan at about 20,000. The
repricing holds, by a factor of roughly 3e4 to 1e5.

**The rehearsal on the production circle** (`rehearsal.py`,
`artifacts/rehearsal.json`) used c = 5000, rho = 1 - 4.6e-5, N = 2^17 (one
sixteenth of production), 192 bits and n <= 5000:

- **The branch closes.** Of 65,537 nodes, 209 are principal and 65,328 are
  tracked, using 2189 cover balls and 1720 arc bisections. The closure ball
  [+/- 2.5e-49] contains 0, and every lambda_n has an imaginary part
  containing 0.
- **Cost.** Sampling took 71 s (1.09 ms per node), tracking 18 s, the DFT 2 s;
  92 s in all.
- **What it does not decide.** At this N, bound (A) is about 5e5 wide at
  n = 5000, so the rehearsal decides nothing by design.
- **Plumbing check (measured only).** Its midpoints differ from #128's float
  table by at most 0.057 (at n = 5000, where lambda is about 2e4). That is the
  size the true aliasing at N = 2^17 should have.

A defect found by the first rehearsal attempt: the tracker asked Arb for f on
arc balls hundreds wide in s (256-node blocks where neighbouring nodes are
about 1 apart near |Im s| = 150). Those evaluations are slow, and their image
always meets 0. The attempt was stopped after 13 CPU-minutes. Balls wider than
1/2 in s are now split without being evaluated (`trapezoid.S_BALL_MAX`), and
tracking cost 18 s.

**Production, priced from the rehearsal:** at c = 5000, N = 2^21, n <= 500,000:
1,048,577 node evaluations at 1.1 to 1.8 ms (quiet to contended), so 0.32 to
0.53 core-hours; tracking under a minute (it is set by the near-line stretch,
not by N: 13 s at N = 2^14, 18 s at 2^17); the DFT about 30 s; M(rho) 45 s.
**About 0.4 to 0.6 core-hours, single process, under 2 GB of memory.** At
c = 2500 (N = 2^19, 234 bits), about 0.15 to 0.3.

## 4. The production runs, reported as pre-registered (`production.py`, `compare.py`)

Pre-registration: `MISSION.md`, "Pre-registration of the production runs",
commit 8964573b4. It was committed alone before run A started.

| | run A | run B |
|---|---|---|
| c, r | 5000, 0.99990000 | 2500, 0.99979998 |
| aliasing circle rho, M(rho) <= | 1 - 4.6e-5, 101,111 | same |
| N, precision | 2^21, 192 bits | 2^19, 256 bits |
| in-run controls | xi 48/48, both faults flip; iv 20/20 meet, kappa fault caught at 17 | same |
| principal / tracked nodes | 3,338 / 1,045,239 | 1,181 / 260,964 |
| branch closure at s = 1/(1+r) | [+/- 2.5e-49], contains 0 | [+/- 6.6e-69], contains 0 |
| imaginary parts of all lambda_n contain 0 | yes | yes |
| largest ball radius, n <= 500,000 | 4.6e-21 | 4.2e-15 |
| first ball-negative index | **328997** | **328997** |
| undecided indices before it | 0 | 0 |
| wall time (contended box, load 28 to 40 on 32 vCPU) | 1211 s (sampling 1098) | 447 s (sampling 367) |
| table, out of git | `artifacts/big/lambda_A.txt`, 26,953,876 bytes, sha256 5ebe8608...f87396b | `lambda_B.txt`, 25,007,262 bytes, sha256 b46903b3...590bbd2e4 |

**The two-radii rule held** (`artifacts/two_radii.json`): the A and B balls
intersect at all 500,000 indices, with a largest midpoint difference of
5.0e-15, set by B's wider balls. **No kill condition fired.**

Further checks on run A:
- **Against #128.** A's balls lie within 1e-20 of #128's 30-digit float table
  at every n <= 5000; the largest difference is 1.0e-25.
- **Against the prediction.** #128's background models predicted
  lambda_{n\*} between -2217 and -2317. The ball is -2379.96.

Around the onset (run A):

| n | lambda_n(DH) |
|---|---|
| 328992 | [19135.5323142982959541146984752 +/- 3.0e-26] |
| 328995 | [5420.11034980594646449706675502 +/- 5.1e-27] |
| 328996 | [1385.31521851949223176484827912 +/- 2.9e-27] |
| **328997** | **[-2379.96470663976248370528984220 +/- 4.4e-27]** |
| 328998 | [-5875.18237299302494479232020911 +/- 2.7e-27] |
| 329002 | [-17145.8812949163996232699459861 +/- 2.0e-26] |

**The outcome as pre-registered:**
- **The prediction is confirmed.** The first ball-decided negative index is
  328997, at distance 0 from #128's extrapolation and inside the window
  [328397, 329597].
- **The statement is established.** lambda_{328997}(DH) < 0 and
  lambda_n(DH) > 0 for every 1 <= n < 328997, hardened.
- **The stop rule was not triggered.**

Two notes on what the number means:
- **The extrapolation hit exactly, but within a known period.** #128 fitted a
  background a n log n + b n + c plus the explicit quadruple terms. The sign
  change sits on a dip of the dominant quadruple's oscillation, of period
  2 pi/psi, about 530. A background error would have moved n\* by whole
  periods, which is what #128's sensitivity table records. So landing on the
  right period is the background's accuracy, and landing on the exact index
  within that period is the quadruple term's.
- **Past the onset, the table is still enclosure-carrying.** To n = 500,000
  the off-line pair dominates: lambda_{500000} = 2.55e9, of the order of
  2 R^n with R - 1 = 4.2e-5. Positivity fails on whole half-periods after
  328997. The table records those signs but they are not analysed here.

**Cost.** 0.34 + 0.12 = 0.46 core-hours of wall time, against an estimate of
0.4 to 0.6 for A and 0.15 to 0.3 for B. #128's plan was priced at about 20,000
core-hours, so this is a factor of about 4e4.

## Dispositions (`ALIGNMENT.md` section 5)

- **n\*: established at the hardened grade.** The question is answered at the
  stated grade: n\* = 328997. It is pending external verification and is not
  kernel-checked.
- **#128's wall ("the direct route does not reach the onset"): candidate
  refuted (category 1), at its stated scope.** The identified invalid step is
  the treatment of r <= 0.99 as a limit. The production run at
  r = sqrt(1 - 1/c) reaches the onset in 0.46 core-hours. #128's own
  measurements stand: its tables, its extrapolation (now confirmed) and its
  cost model *for its family*.
- **First-wave status line** ("n\*: attempt unresolved"): superseded by
  section 4, and left in place as the record of what was known before the run.
- **No kill condition fired** in either wave.

## Prior work searched

The searches, run 2026-10-26 (web search plus the arXiv abstract pages and
PDFs; zbMATH and Google Scholar were not queried directly):

- **arXiv:1410.4384** (Ernvall-Hytönen, Odžak, Smajlović, Šušić, "On generalized
  Li criterion for a certain class of L-functions"). It has **no
  Davenport-Heilbronn numerics**, and "Heilbronn" does not occur in its text. Its
  example is a product of shifted Riemann zetas, with tau-Li coefficients from
  zero sums (2,001,052 Odlyzko zeros) in floating point with explicit error
  bounds, n up to 500. The brief's attribution is corrected here.
- **The paper that does compute DH-type Li coefficients:** Bucur,
  Ernvall-Hytönen, Odžak, Smajlović, "On a Li-type criterion for zero-free
  regions of certain Dirichlet series with real coefficients", LMS J. Comput.
  Math. 19(1) (2016) 259-280, doi:10.1112/S1461157016000115.
  - **Method and grade:** tau-Li coefficients lambda(n, tau) for tau in
    [1, 5], "conducted using the interval arithmetic package Arb", by a Taylor
    series at tau, not zero sums.
  - **Ranges:** n <= 500 in steps of 5 at 1e-35, and n <= 350 at 1e-110.
  - **Which function:** they "concentrated on the function L_DH(s, xi-)", the
    associated function. The classical Davenport-Heilbronn function is the xi+
    member. Our kappa = 0.284079... equals xi+ = -phi + sqrt(1 + phi^2), so the
    function here is the one they did not compute.
  - **First negative index:** shown only as dots in their Figure 4 for
    xi-, with no number stated in the text.
- **Johansson**, "Rigorous high-precision computation of the Hurwitz zeta
  function and its derivatives", Numer. Algorithms 69 (2015) 253,
  doi:10.1007/s11075-014-9893-1, arXiv:1309.2877. It computes **zeta's**
  Keiper-Li coefficients up to n = 100,000 in Arb, by power series rather than a
  contour. Its normalization, log xi(1/(1-x)) = -log 2 + sum lambda_n x^n,
  divides Li's lambda_n by n. Nothing on Davenport-Heilbronn.
- **arXiv:1602.06328** is Ferry, Ghisa, Muscutar, "On Davenport and
  Heilbronn-Type of Functions". It covers off-line zeros and has no Li
  coefficients, so it is not cited for this.
- Queries `"Davenport-Heilbronn" "Li coefficients"`,
  `"Li's criterion" "Davenport-Heilbronn" first negative`, and
  `"Li coefficients" Epstein zeta negative off-line zeros` found no stated
  first negative Li coefficient for the classical DH function, and no Li
  computation for any Epstein zeta.

**Deltas, as the coordinator asked, against the two named sources:**
- **arXiv:1410.4384** (Ernvall-Hytönen, Odžak, Smajlović, Šušić): it computes
  no Davenport-Heilbronn coefficient. Its numerics are tau-Li coefficients of a
  product of shifted zetas, in floating point from zero sums, for n up to 500.
  The delta is the whole result: the classical DH function, tau = 1, n to
  500,000, every step in balls, an explicit first negative index.
- **Johansson, Numer. Algorithms 69 (2015)**: rigorous Keiper-Li coefficients
  in Arb, for **zeta**, up to n = 100,000, by power series. The delta is a
  different function, one whose coefficients do turn negative, five times the
  range, and a contour route made admissible by a zero-location certificate
  instead of a power series.
- **Bucur, Ernvall-Hytönen, Odžak, Smajlović, LMS J. Comput. Math. 19 (2016),
  the closest source:** Arb tau-Li coefficients for the *associated* function
  L_DH(s, xi-), n <= 500, first negative indices only as a figure. The delta is
  the classical member xi+, ordinary Li coefficients, and n\* = 328997 stated
  and enclosed.

The result is **original** (this lab produced it). It is not claimed novel.
The search behind these deltas is recorded above. It is bounded (web search,
the arXiv pages and PDFs; zbMATH and Google Scholar were not queried directly)
and found no stated first negative Li coefficient for the classical
Davenport-Heilbronn function.

## The doors

The ceiling this wave measures is the cost of n_max on the ball trapezoid, as
a function of c. (The production runs since then confirm the model: about 0.34
core-hours for A against 0.4 to 0.6 estimated.)

### Active constraints at the optimum

1. **Node count from the aliasing gap ln(rho/r)**, which binds at c >= 3000.
   N grows like ln(n M rho^{-n}/tol)/ln(rho/r), and ln(rho/r) is at most
   ln(R_a/r) = 1/(2c) - 4.2e-5. The shadow price is steep near c = 1/(2(1-R_a)),
   about 11,900, where the gap closes: c = 5000 costs 2^21 nodes, while c = 1e4
   costs 2^24.
2. **N > n_max**, which binds at c <= 2500. There the aliasing need falls below
   n_max, and the DFT length is set by the largest index wanted.
3. **Precision**, which never binds here: n_max (1 - r) log2 e + about 90 bits.
   That is 162 bits at c = 5000 and 270 at c = 2000. It costs a factor of
   about 1.8 per node between 200 and 250 bits.
4. **R_a itself.** It is fixed by pair1 and is a property of f, not a constant
   anyone chose.

### The frozen-constant inventory

| constant | value | what relaxing it trades |
|---|---|---|
| c | 5000 (brief) | **genuine trade shape**: c = 2500 is about 3 times cheaper, at about 70 more bits |
| aliasing circle rho | 1 - 4.6e-5 | closer to R_a widens the gap but raises M only logarithmically; the four measured circles span M = 9.2e4 to 1.1e5 |
| tol | 1e-10 on lambda_n | each factor of 10 costs ln 10/ln(rho/r) nodes, about 4e4 at c = 5000; the sign decisions need far less unless some lambda_n sits within 1e-10 of 0 |
| n_max | 500,000 | about 1.5 times the extrapolated n\*; if no sign change appears below it, N and bits grow linearly |
| power-of-two N | 2^21 | Arb's DFT also takes smooth composite lengths: 5 x 2^18 = 1,310,720 would save 37 per cent at c = 5000 |
| box height T | 160 | 154.3 is the minimum that makes pair1 bind; 133 also certifies c = 5000 |
| square half-width | 1e-15 | sets the R_a ball width (6e-19); far below every other uncertainty |
| block of 256 nodes | branch cover | cost only; bisection repairs any block that fails |

### The information class

**Inside the family** (the same contour integral, computed more cheaply): c, rho,
tol, the power of two and the block size. **Requires reading more**: none of
the production numbers. The admissibility certificate already reads the zeros
up to T = 160, and nothing above T enters except through the closed-form floor
1 - 2/T^2. The one door that would change the *answer* rather than the cost
belongs to #128's census: a zero above T with a larger (2 beta - 1)/|rho|^2 than
pair1 would move n\*. It cannot change R_a, because the floor 1 - 2/T^2 already
excludes such a zero from the disc.

A measured optimum is not a proved ceiling. These costs are estimates fitted
to timed units on a contended box, at the stated tol and n_max, and nothing in
them is proved.

## Addendum, 2026-10-26 (evening): the named shared failure mode, tested

**Pre-registration.** `MISSION.md`, "Pre-registration of the
independent-evaluator rerun of run B", commit 485359c38. It was committed
before the run, and it fixes the seed (1512026), the sample rule and three
rules.

**What was done.** Run B (c = 2500, N = 2^19, 256 bits, rho = 1 - 4.6e-5,
n <= 500,000) was repeated with a second evaluator (`iv_fast.py`, `ivpipe.py`).
It shares no evaluation code with the Arb one:
- f by Euler-Maclaurin in mpmath.iv, with its own kappa solve and its own
  rigorous remainder;
- log Gamma by `mpmath.iv.loggamma`;
- S(3/2) in iv.

Every use of f went through it: the 262,145 node samples, the 40,199
branch-cover arc boxes, and the 15,313-arc M(rho) cover, which gave
M(rho) <= 99,865 against Arb's 101,111. Shared with run B on purpose: the node
geometry, the tracking logic, `acb.dft` and the aliasing arithmetic. Arb only
holds and transforms numbers there. Before the run, the iv evaluator was
checked against Arb and against the slower `iv_route` at nodes including an
exactly real s.

**Outcome, as pre-registered:**

| rule | result |
|---|---|
| 1. first ball-negative index 328997, none undecided before it | **holds**: 328997, 0 undecided |
| 2. signs agree wherever both decide, n <= 500,000 | **holds**: both decide all 500,000, 0 disagreements |
| 3. balls intersect at 328996, 328997 and the 1000 sampled n | **holds**: all intersect; in fact the balls intersect at every n <= 500,000 |

At the onset, iv gives lambda_{328996} = [1385.31521851949223176 +/- 5.9e-18]
and lambda_{328997} = [-2379.96470663976248371 +/- 5.8e-18]. Arb run B gives
the same digits with radius 5.9e-18 and 5.8e-18. The largest midpoint difference
over the sample is 4.9e-15, below either run's ball radius there. The iv table
is `<cache>/li_dh_onset_hardened/lambda_B_iv.txt`, sha256
901380462bf4f7435bddcd510e6787e231ca09b54cfb5651d68aeadc54924aa2. Cost:
6.45 core-hours (RUNS.md).

**What this excludes, and at which grade.** The failure mode RESULTS.md named,
"both radii use the same Arb evaluator for f", is **excluded for run B's
table**. An mpmath.iv evaluation of every value f and log Gamma contribute
reproduces the same n\* and the same sign at every n <= 500,000, at interval
grade (every evaluation enclosed). Run A at c = 5000 was not repeated in iv. It
is tied to the iv route through the A/B intersection at every n.

**What it does not exclude:**
- a fault in the shared machinery: `acb.dft`, the aliasing bound (A) as
  derived here, the tracking logic, or the node geometry;
- a fault in the mathematics both routes encode identically: the
  Euler-Maclaurin remainder bound, and the admissibility argument.

The admissibility certificate itself is Arb-only. An iv replay of the box count
was not done.

**The grade is unchanged:** *hardened*, pending external verification. It is not
kernel-checked and has had no outside review. This addendum narrows which
failure modes remain open; it does not change the rung.

**Novelty, as a delta against the recorded search.** Searches were run on
2026-10-26 by web search plus the arXiv abstract pages and full PDFs. zbMATH
and Google Scholar were not queried directly. Queries:
`"Davenport-Heilbronn" "Li coefficients"`,
`"Li's criterion" "Davenport-Heilbronn" first negative Li coefficient`,
`"Li coefficients" Epstein zeta function negative off-line zeros computation`,
`arXiv "Li-type criterion for zero-free regions"`, a DOI lookup through OpenAlex,
and author and journal lookups for the items below.
- **arXiv:1410.4384** (Ernvall-Hytönen, Odžak, Smajlović, Šušić): no
  Davenport-Heilbronn numerics at all. The word does not occur in its text.
  Its examples are a product of shifted zetas, n <= 500, in floating point.
- **Bucur, Ernvall-Hytönen, Odžak, Smajlović, LMS J. Comput. Math. 19 (2016)
  259-280:** Arb tau-Li coefficients for the *associated* function
  L_DH(s, xi-) only, n <= 500, with first negative indices only as a figure.
  The classical function (xi+, our kappa = 0.284079...) is not computed.
- **Johansson, Numer. Algorithms 69 (2015), arXiv:1309.2877:** rigorous
  Keiper-Li coefficients for **zeta** up to n = 100,000, in Arb.

**The delta:**
- the classical Davenport-Heilbronn function;
- ordinary Li coefficients;
- every lambda_n for n <= 500,000 enclosed by two radii and two evaluators;
- the explicit first negative index n\* = 328997.

The result is original to this lab. It is not claimed novel beyond the stated
search.
