# EVALUATOR: Polymath 15's effective approximation in Arb

**Status: built and checked against two independent routes to H_t, at
small x and (Milestone 1b) at large x where the correction term is tested
sharply; the printed Table 1 row 2 bound is reproduced, together with a
reading of what it bounds; one barrier rectangle wound at two times, and the
barrier decision audited from outside. A hunt instrument, not a result.** Nothing here is a statement about the de Bruijn-Newman constant, and
no sweep was launched. The evaluator lane of hunt `dbn_pt_height` (see
`../MISSION.md`); every number below is asserted by `test_effective.py`, either
recomputed or read from the data files the scripts here wrote.

## What it is

`effective.py` evaluates, in python-flint ball arithmetic, the quantities of
D.H.J. Polymath, arXiv:1904.12438v2 (source tarball sha256
`1be3bc38d203ad0142f1c97c267c7deaa06b84c97716c9a1ec1f56456d826863`, read as data,
line numbers refer to its `debruijn.tex`):

- `point(x, y, t)`: f_t, the correction C_t/B_t and the error quantities
  e_A, e_B, e_C, e_{C,0} exactly as defined in (ea-def)-(ec-def), lines 969-974,
  by direct summation, with the Riemann-Siegel factor C_0(p) of (C0-def)
  evaluated through its removable singularities at p = 1/2 and p = -1/2.
  `Point.Ht_ABC()` is the ball A + B - C plus a disk of radius
  E_A + E_B + E_C, which by Corollary 6.4 (lines 926-948) contains H_t(x + iy).
- `theorem_bounds`: the closed forms (gamma-bound)-(ec-bound) of Theorem 1.3
  and Proposition 6.6(vi).
- `trib2_bounds`, `euler2_lower_bound`: Lemma 10.1 (trib2, lines 1975-1992) and
  the Euler 2 bound of Section 10.
- `euler_mollified_F`: F_{N-,N+} of Section 8.5 for any set of primes (2, 3, 5
  is the paper's Euler 5), with the coefficient truncation n/d <= N handled
  for every N in the interval at once (`truncation="worst"`).
- `unmollified_triangle_bound`: the claim (c) triangle bound of Section 8.3,
  with an erfi majorant for the tail.
- `derivative_bounds`: the |df/dz| and |df/dt| bounds of the lemma at lines
  1442-1453, as suprema over a rectangle (the majorant is convex in y, so
  strip suprema are endpoint maxima).
- `FixedTimeMultiEval`: Taylor multi-evaluation (Section 7) with blocks of
  log-width 1/2, K = 16 terms and the truncation tail charged into every ball.
- `barrier_rectangle`: the Rouche and winding check of Section 8.4 on one
  rectangle at one time, with an adaptive dyadic mesh and per-strip
  derivative bounds.

**Grade.** Every returned ball contains the exact value of the formula it
implements (enclosure-carrying, the ladder's second rung). The analytic steps,
Theorem 1.3, Corollary 6.4, Lemma 10.1 and the derivative lemma, are the
paper's, used as published and not reviewed here; a conclusion that leans on
them takes their status, and the lab has no kernel-checked or outside-reviewed
version of any of them. The paper states Theorem 1.3 and Corollaries 6.4 and
6.5 for t > 0; `effective.py` also admits t = 0, by letting t -> 0+ (the lab's
derivation, unreviewed, in `_check_region`). The results that rest on it are
the t = 0 rows: the second row-2 rectangle, the barrier audit at x = 1e8 + 0.7,
the zero-refusal control and the t = 0 points of Milestones 1 and 1b.

`oracles.py` holds the two independent routes: `zeta.heatflow.H_t` (Phi
quadrature) and an mpmath quadrature of the paper's heat-kernel
representation (htz) with mpmath's zeta and gamma. Neither shares code with
the evaluator; both are floating point, so agreement with them is measured,
not enclosed.

## Milestone 1: agreement with H_t for x <= 400, and beyond with mpmath

`agreement.py` wrote 60 values per route on x in {200, 250, 300, 350, 400},
y in {0, 0.5, 1}, t in {0, 0.05, 0.2, 0.5}, and four more heat-kernel values
at x = 1000 and 2000 (`agreement_phi.jsonl`, `agreement_hk.jsonl`).

- All 124 values lie inside the evaluator's A + B - C ball, and inside the
  cruder A + B ball of radius e_A + e_B + e_{C,0}.
- The measured error |H_t - (A + B - C)| is at most 0.031 of the radius at
  every point: the error terms are conservative, e_C most of all.
- The two routes agree with each other to a relative 1e-8 or better at all 60
  shared points (they share no code; the heat-kernel route is the less
  accurate of the two at x >= 250).
- **Lesion.** Dropping e_C from the radius breaks containment at 7 of the 60
  grid points, under both routes at each, among them (x, y, t) = (200, 1, 0),
  which the test also recomputes live. So e_C is load-bearing, not
  decorative.

## Milestone 1b: containment at large x, and the checks that came with it

On the Milestone 1 grid (x <= 2000) the correction C_t/B_t is about as large
as its own error term e_C, so containment there cannot tell a right C_t from
several wrong ones. `large_x_oracles.py` wrote 12 values of H_t where it can
(`large_x_oracles.jsonl`):

- 8 at t = 0, x from 1e5 + 0.3 to 1e8 + 0.73, as (1/8) xi((1 - y + ix)/2) by
  mpmath and by PARI/GP (through cypari2), two routes sharing no code; they
  agree to a relative 8.7e-27 to 2.5e-23.
- 4 at t in {0.05, 0.2, 0.4, 0.5}, x from 1e5 to 1e6 + 0.5, by Gauss-Hermite
  quadrature of the heat-kernel representation at 80 and at 120 nodes; the two
  node counts agree to a relative 2.9e-22 to 4.5e-21.

What the tests show (`test_effective.py`; measured, since the oracles are
floating point):

- **Containment.** All 12 values lie inside the A + B - C ball. The worst
  measured error uses 25 to 30 per cent of the radius (0.031 on the small-x
  grid), and |C_t/B_t| is at least 17.6 times e_C at every point, so the test
  is sharp for C_t. One t = 0 value (x = 1e6 + 0.37, y = 1) is recomputed live.
- **C_t lesions.** Four planted faults in C_t (the y-phase conjugated,
  e^{i pi/8} dropped, exp(t pi^2/64) dropped, the sign of C flipped) each put
  some large-x value outside its ball. The first three pass the whole x <= 2000
  grid unnoticed, which is why this milestone exists.
- **A re-derivation from the TeX.** `oracles.formula_mpmath` re-evaluates f_t,
  C_t/B_t and the four error quantities in mpmath, written from the paper in a
  different algebraic form (the second sum of (ft-def) with conj(s_*) + kappa,
  and E_A, E_B of Corollary 6.4). It agrees with `point` to a relative 1e-26 at
  five points from x = 211.7 to 1e8 + 0.73, and it sees two slips (C_0
  conjugated, kappa dropped) that are too small for any containment test.
- **Proposition 6.6(vi), a source erratum, measured.** Just above a jump x_N
  with small N, the exact e_C of (ecc-def) exceeds the printed bound (vi) by a
  factor between 1.02 and 1.15 (N = 4, 5, 6, 10); at N = 20 and 50 the bound
  holds again. Theorem 1.3's (ec-bound) for e_{C,0} still held at those points.
  `effective.py` no longer uses (vi) anywhere: the rectangle error bound takes
  the exact (ec-def) over a mesh of sub-boxes (`_eC0_upper_on_box`), and stays
  above the exact e_A + e_B + e_{C,0} just above x_4, where (vi) would not.
- **The step at line 1107.** Replacing 0.397 9^sigma e^{3.49/(T-4)}/(a - 0.865)
  by 1.24 3^{+-y}/(a - 0.125), with the paper's factor e^{3.49/(T-4)} <= 1.037,
  holds only for a >= 187 (the two sides cross at a = 186.14; a = sqrt(T'/2 pi),
  so x of about 4.4e5), while the paper's region starts at a = 4. Only
  `theorem_bounds`, the closed forms, uses that step; nothing that feeds an
  enclosure does.
- **The Taylor tail is charged, and sharply.** For one exponential the charged
  tail lies between the exact omitted part and that part divided by
  1 - rho/(K + 1) (K = 2 to 16, rho = 0.05 to 2). In a two-term configuration
  built so the tail is nearly attained, the actual truncation error uses 85 to
  100 per cent of it; halving the tail, or dividing the B-sum tail by 1000,
  leaves the direct value outside the ball.
- **The derivative majorants, part by part.** Each of the four parts of the
  Lemma's majorant dominates the exact termwise derivative sums of the Lemma's
  proof (lines 1464-1505) in the windows n in [1, 25], [N - 24, N] and [1, N],
  at x = 1e6 (t = 0 and 0.4) and 1e8 (t = 0.1). The first-sum z-part is
  attained exactly at t = 0 and is within 1.0001 of exact at 1e8; no part is
  looser than a factor 3. Five planted slips are caught (either z-weight
  halved, the first-sum t-weight slip, the gamma t-term divided by 10, tau
  taken from the upper end). Halving the gamma t-term is not caught: that part
  has slack 1.56 to 1.60 over the exact sums in every window, so a halving
  stays above them. The lesion was therefore strengthened, not dropped.
- **The barrier decision, audited from outside.** `_audit_barrier` re-derives a
  `barrier_rectangle` decision from its returned segments alone. It checks the
  tiling of every edge, the rule |f| > E + D h/2 with f by direct summation and
  h recomputed, E against the exact e_A + e_B + e_{C,0} at every mesh point, D
  against the strip majorants and the exact termwise sums, the
  multi-evaluator's values against direct ones, and the winding number from
  direct values. Two rectangles pass: [1e6, 1e6 + 1] x [0.2, 1] at t = 0.1,
  starting from 4 points per edge and refining to 40, and
  [1e8 + 0.7, 1e8 + 1.2] x [0.2, 0.7] at t = 0. E is within 5 per cent of the
  largest exact value. Four planted faults each fail the audit: the margin
  h/4, no derivative margin, D divided by 10, e_{C,0} dropped from E. The first
  two could not show from 16 starting points per edge, where the rule never
  has to refine; that is why the first case starts from 4.
- **A zero on the boundary is refused.** A rectangle whose bottom edge y = 0
  passes through the zero x = 2 t_z of H_0 (t_z = 50000000.48372..., a sign
  change of mpmath's `siegelz`, located in the test) reports no winding number.
  The same x-range moved up to y in [0.2, 0.7] passes, so the refusal is caused
  by the zero.

Grade: the containment, re-derivation and lesion results are measured
(floating-point oracles against enclosures of the formulas). The majorant and
audit checks are enclosure-carrying comparisons of the module against exact
termwise values at finitely many points, not proofs that the majorants hold
everywhere.

## Milestone 2: Table 1, row 2

Row 2 prints X = 5e12 + 194858, t0 = 0.186, y0 = 0.16733, Lambda = 0.20,
winding number 0, N0 = 630783 and "|f_t(x+iy)| lower bound" 0.0376
(line 1950). `row2_check.py` wrote `row2_check.json`.

**N0.** floor(sqrt(X/(4 pi) + t0/16)) = 630783, and N is constant on
[X, X + 1] at t = t0 and at t = 0.

**The printed 0.0376 is reproduced, as a bound on the Euler 2 mollified f.**
Lemma 10.1 bounds |1 - lambda| |sum a_n| with lambda = b_2 2^{-s_*}; applied
to both sums of f_t with the same lambda, it gives the numerator
LB_beta - |gamma| UB_alpha, a lower bound for |E_2 f_t| with
E_2 = 1 - b_2 2^{-s_*}. At x = X:

| y0 | numerator (bounds \|E_2 f\|) | numerator / (1 + \|lambda\|) (bounds \|f\|) |
|---|---|---|
| 0.16733 | 0.037617 | 0.029195 |
| sqrt(0.028) | 0.037627 | 0.029202 |

The printed value is the numerator. The same reading reproduces the printed
column in rows 1, 3, 4 and 5 (numerators 0.034132, 0.034941, 0.037704,
0.036946 against printed 0.0341, 0.0349, 0.0377, 0.0369), while the version
divided by 1 + |lambda| matches none of the five rows. The project's PARI
function `abbeff_moll2_analytic_bound` (file `dbn_upper_bound/pari/abbeff_largex_bounds.txt`
of github.com/km-git-acc/dbn_upper_bound, lines 138-145, read as data from the
chain lane's download) has exactly this undivided form, and re-implemented
here it gives 0.037603. Grade: the column value is a measured three-digit
match of a recomputed formula in five rows plus the source code's form; the
lab did not see the script that printed the table.

So the bound the row supplies for |f_t| itself at N = N0 is 0.0292 (with |gamma|
exact at X), or 0.0284 uniformly over every x with N(x) = N0 (sigma as a ball
over [x_N0, x_N0+1), |gamma| replaced by its (gamma-bound) majorant). Either is
far above the error terms there: at x = X the direct evaluation gives
|f| = 1.684, |E_2 f| = 1.206, e_A = 1.06e-13, e_B = 7.48e-13 and
e_{C,0} = 1.03e-7. The paper's selection target of 0.03 (line 1965) is not met
by the |f| bound, only by the |E_2 f| bound; nothing in the row's logic used
0.03 as a threshold.

**One rectangle, two times.** R = [X, X + 1] x [y0, 1]:

| t | winding | evaluations | min \|f\| on mesh (lower) | D_z, bottom edge | E = e_A + e_B + e_{C,0} on R |
|---|---|---|---|---|---|
| 0.186 | 0 | 68 | 1.4458 | 8.4893 | 1.067e-7 |
| 0 | 0 | 580 | 4.68315 | 10085.47 | 4.264e-4 |

The E column is from the record regenerated on 2026-10-26 (`RUNS.md`, E4). The
2026-10-21 record had 1.031e-7 and 4.119e-4, from the earlier rectangle error
bound that used Proposition 6.6(vi), which Milestone 1b found to fail just
above small jumps. Every other entry of the table is unchanged. The new E
stays above the exact e_A + e_B + e_{C,0} at the worst corner, within 4 per
cent of it (a slow test, one O(N) evaluation per time).

The project's own log of this barrier (`output/windingnumbers/windnum_nolemma_x5000000194858_y_0.16733_1_t_0_0.186.txt`,
sha256 `3406175695291ea000e37c9e6466c4d34975a58a76472ba6bde204ddb34022c7`,
read as data) lists 435 rectangles from t = 0 to t = 0.17557 with 7,368,456 mesh
points in all, every winding number 0. Its t = 0 line gives ceiling(ddt bound)
54747, ceiling(ddz bound) 10087 and a mesh minimum of |f| of 4.6831460650 on
40344 points; this evaluator, written independently, gives D_t <= 54745.85,
D_z <= 10085.47 and a mesh minimum of 4.68315 on 580 adaptive points. That
agreement is a cross-check between two implementations, not a verification of
the barrier: the t-direction is not covered here, and one rectangle is not a
barrier.

**Euler 5.** The paper prints F_{69098, 8x10^4} = 0.0263... at t = y = 0.2
(line 1738). Recomputing the printed formula with the paper's constants
(1.03, sigma = 0.599 + 0.1 log N-) gives 0.0178 when every truncation in the
interval is covered, 0.0202 truncated at N+, 0.0576 at N-, and -2.776 with no
truncation, as the printed definition of beta_n (line 1654) reads; Euler 7
gives 0.0639 and 0.1018. With the constants derived in `effective.py` the
covering value is 0.0308. None prints as 0.0263, so the printed digits are not
explained; every truncated variant clears the paper's threshold 2.15e-3, so
the conclusion for that interval is not in question. At row 2's parameters
the first unit of the sweep, F_{630783, 640783}, is 0.4686 (covering
truncation, derived constants).

## Milestone 3: cost

Timings, unit costs and the projections for the full row-2 asymptotic sweep
and for a (t0, y0) re-optimisation at X <= 6.0e12 are in `../RUNS.md`
(entries E2 and E3). The per-rectangle cost at N = 630783 is dominated by the
two O(N) passes (derivative bounds and the multi-evaluation set-up), not by
the mesh.

## Defects found while building, and how each is now caught

- **A silent series cap.** The first multi-evaluator built its Taylor
  coefficients with `arb_series(...).exp()`, which python-flint truncates at
  `ctx.cap = 10` terms without warning, while the tail bound assumed K = 16.
  The balls were then too small (during development, differences near 1e-20
  against radii near 1e-28 at x = 1e10; not pinned). The off-centre overlap
  test against direct summation caught it; coefficients are now built explicitly
  with a length assertion, and `test_lesion_multieval_without_tail_is_caught`
  shows the overlap test fails when the tail is removed.
- **`arb ** int` returns NaN** when the base ball touches 0, which happens at
  the expansion centre; powers are now repeated multiplication.
- **Inputs built at 53 bits.** A ball constructed outside the working
  precision carries a 53-bit radius into every phase (during development, ball
  radii near 1e-7 in f at x = 1e8; not pinned). The result is still a valid
  enclosure, only a wide one; drivers and tests pass strings, parsed inside the
  context.

## Observations about the source, for the chain lane

- The printed definition of beta_n (line 1654) omits the condition n/d <= N
  that its identity needs; the project code has it (`combdelta`).
- Theorem 1.3's (res-bound) carries 4y(1+y)/x^2 where Proposition 6.6(ii) and
  its proof carry 8y(1-y)/x^2 (lines 239, 984, 1038); for y < 1/3 the printed
  theorem is the stronger and less supported one, by O(t/x^4).
- Line 1147 writes (b + (t/2) log n0)^i / i! where the expansion two lines
  earlier has the j index; line 1639 ends with (n/N-)^{-0.2} where the next
  display uses (n/N-)^{0.2}.
- The project repository holds a second Euler 5 run at this same X with
  t = 0.17, y = 0.2 (`output/eulerbounds/lemmasawtooth_bounds_t_0.17_y_0.2_N_630783_15mil_moll_2,3,5.txt`
  and a matching winding summary). It is not row 2, and this lane did not
  analyse it.

## Open

- The full barrier, the asymptotic sweep and any Lambda statement are out of
  this lane's scope. They are gated on the pipeline refusing the
  Davenport-Heilbronn rival where its heat flow still has non-real zeros.
  0.2304 is not Lambda_DH. It is the floor of hunt #61's bracket
  0.2304 < Lambda_DH <= 0.7697 (wide frame; `docs/29`,
  `hunts/lambda_dh_bounds/SEPARATION.md`), from a winding count of 1 at narrow
  t = 36/625 that the hunt grades decided, with the frame factor 4 derived in
  its `FRAME.md`. The control has since been built, preregistered
  (`DH_GATE_PREREG.md`) and run (`../RUNS.md`, E7). The barrier rule passes it
  on six boxes; a one-corner check and a main-terms-only evaluation fail it.
  It exercises the barrier rule only. Theorem 1.3's error terms and the
  Euler-mollified sweep are not tested by it (`DH.md`).
- The methods index `docs/37-methods.md` has no entry for this instrument;
  adding one is outside this lane's write scope.
