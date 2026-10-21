# EVALUATOR: Polymath 15's effective approximation in Arb

**Status: built and checked against two independent routes to H_t; the
printed Table 1 row 2 bound is reproduced, together with a reading of what
it bounds; one barrier rectangle wound at two times. A hunt instrument, not a
result.** Nothing here is a statement about the de Bruijn-Newman constant, and
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
version of any of them.

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
| 0.186 | 0 | 68 | 1.4458 | 8.4893 | 1.031e-7 |
| 0 | 0 | 580 | 4.68315 | 10085.47 | 4.119e-4 |

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
  this lane's scope and gated on the pipeline refusing the Davenport-Heilbronn
  rival below Lambda_DH = 0.2304 (wide frame; the value is the campaign's gate,
  quoted from the task and not recomputed here); that control has not been run
  and needs a DH analogue of the effective approximation, which this module
  does not provide.
- The methods index `docs/37-methods.md` has no entry for this instrument;
  adding one is outside this lane's write scope.
