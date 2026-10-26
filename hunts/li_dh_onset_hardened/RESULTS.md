# RESULTS: the first wave of hunt #151

**Status, 2026-10-26: first wave done, production not run.** No n\* has been
found yet. The wave settles whether the 20,000 core-hour wall that hunt #128
(`li_dh_onset`) priced is mathematical or a cost wall: it is a cost wall of
the r <= 0.99 family. Moving the radius to r = sqrt(1 - 1/c) is licensed by an
admissibility certificate that closes exactly in balls, and the ball trapezoid
on that circle prices at **under one core-hour** for every n <= 500,000.
Nothing here bears on the Riemann Hypothesis (`docs/08`): every number is about
the Davenport-Heilbronn function f, which has no Euler product.

Grades, weakest step first. Steps 1 and 3 are *hardened*: every step carries
an Arb ball, and a second route agrees where one exists. The production
estimate in step 3 is *measured*: a float model fitted to timed units. Step 2's
timings are *measured*; its cross-checks are hardened comparisons.

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

## Dispositions (`ALIGNMENT.md` section 5)

- **n\*: attempt unresolved (category 3).** Production has not run, so no
  negative coefficient has been computed and nothing here locates n\*.
- **#128's wall ("the direct route does not reach the onset"):** it was a cost
  wall of its own family. The binding constant, r <= 0.99, was the top of a
  scan, not a limit. This is not yet a refutation of the wall, because the
  refutation is the production run. It is a repricing from timed units, graded
  measured.
- **No kill condition fired.**

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

**Delta against the closest source (Bucur et al. 2016):** a different member of
the family (xi+, the classical function), ordinary Li coefficients (tau = 1),
and a contour route whose cost at n ~ 3e5 is priced here. The hardened
lambda_n(DH) > 0 for n <= 200 above is **original** (this lab produced it). It is
not claimed novel: the search is recorded above, and Bucur et al. compute the
neighbouring function at comparable n in balls.

## The doors

The ceiling this wave measures is the cost of n_max on the ball trapezoid, as
a function of c.

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
