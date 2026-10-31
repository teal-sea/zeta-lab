# DH_GATE_PREREG: the Davenport-Heilbronn refusal gate, preregistered

**Written and committed 2026-10-26, before the gate was run.** The commit that
adds this file precedes every gate run. `dh_gate.main` writes
`dh_gate_results.json`, and the result is recorded in `RUNS.md` (E7) as this
file defines it, whichever way it comes out. If anything below is changed after
the run, it is a new preregistration with a new run, and the first result stays
on record.

## What the gate asks

Would the barrier decision this evaluator makes for zeta call a rectangle
zero-free that holds a zero of the Davenport-Heilbronn heat flow? The decision
is the rule of `effective.barrier_rectangle` (Polymath 15, Section 8.4):

- dyadic mesh on each edge; a segment of length h is accepted when
  |f| > E + D h/2 at both of its endpoints, else bisected;
- once every segment is accepted, the winding number is the integer in
  (1/2pi) sum Arg(f_{j+1}/f_j).

It runs on DH through `dh_gate.dh_barrier`:

- f = H_t^DH, enclosed by hunt #61's `instrument.H_ball`, so E = 0 and the
  enclosure radius is carried in the balls;
- D = max |H'| at the two segment ends (`instrument.Hprime_ball`) + M2 h/2,
  where M2 is #61's decided bound on |H''| (`winding.second_derivative_bound`);
- everything in the wide frame of Polymath 15 (H_wide(z, t) = H_61(z/2, t/4);
  M2 divided by 4).

Parameters, fixed here:

- 8 initial points per edge;
- max_depth 6;
- at most 600 evaluations per box run (a box that runs out is undecided);
- working precision 160 + ceil(pi x_hi/(8 log 2)) bits (`dh.split_prec`).

**The ground truth** for each box is hunt #61's own decided count,
`winding.winding_rectangle` at 420 bits on the narrow-frame image of the box.
It uses a different rule (chord clearance against M2 h^2/2, then
Re(H_b/H_a) > 0), so the gate does not grade itself.

## The boxes (wide frame, exact rationals)

| name | t | x | y | expected | why |
|---|---|---|---|---|---|
| Z1 | 144/625 | [245909/512, 123159/256] | [3/512, 35/512] | one zero | 2 x hunt #61's decided box at t = 36/625 (its `winding_results.json`, `t2_stretch_run`) |
| Z2 | 0 | [171.2, 171.6] | [0.5, 0.7] | one zero | the pinned zero 0.80852 + 85.69935i of `zeta.epstein`, z = 171.3987 + 0.6170i |
| Z3 | 0 | [228.1, 228.5] | [0.2, 0.4] | one zero | Spira's 0.650830 + 114.163343i, z = 228.3267 + 0.3017i |
| Z4 | 0 | [353.2, 353.6] | [0.35, 0.55] | one zero | Spira's 0.724258 + 176.702461i, z = 353.4049 + 0.4485i |
| C1 | 144/625 | as Z1 | [1/5, 3/5] | none | control above Z1 |
| C2 | 0 | as Z2 | [0.8, 1] | none | control above Z2 |

"Expected" is a prior. The truth step decides each box.

## The decision table

For each box, with the truth's decided count N (or none) and the pipeline's
winding w (or undecided):

| box kind | truth | pipeline | class |
|---|---|---|---|
| zero | N >= 1 | w = N | REFUSE |
| zero | N >= 1 | undecided | REFUSE_WEAK |
| zero | N >= 1 | w = 0 | **ACCEPT** (the pipeline called a box with a zero zero-free) |
| zero | N >= 1 | w >= 1, w != N | **INCONSISTENT** |
| zero | N = 0 | any | TRUTH_EMPTY (excluded, reported) |
| control | N = 0 | w = 0 | DISCRIMINATES |
| control | N = 0 | undecided | NON_DISCRIMINATING |
| control | N = 0 | w != 0 | **INCONSISTENT** |
| control | N >= 1 | any | CONTROL_NOT_EMPTY (excluded, reported) |
| any | undecided | any | TRUTH_UNAVAILABLE (excluded, reported) |

**Verdict** (`dh_gate.verdict`):

- **FAIL** if any box is ACCEPT or INCONSISTENT.
- **PASS** if every remaining zero box is REFUSE or REFUSE_WEAK, at least one
  is REFUSE, and every remaining control DISCRIMINATES.
- **INCONCLUSIVE** otherwise.

A failed DH computation excludes nothing (`CLAUDE.md`), so an INCONCLUSIVE gate
says nothing about zeta.

## The planted faults

Each fault runs on all six boxes with the same truth.

**Caught** means its verdict is FAIL. A fault that only makes the pipeline
stricter cannot be caught by a refusal gate, and that is recorded, not hidden.

| fault | what it does | must be caught? | expectation, from the development box D0 |
|---|---|---|---|
| one_corner | calls the box zero-free when |H| > 0 at its lower-left corner. This is the row-2 pattern of CHAIN.md: one check at (N0, y0), the rest argued. | **yes** | caught (D0: winding 0 on a box with a zero) |
| main_terms_only | f = A + B, the sharp main terms with no correction, E = 0 | **yes** | caught (D0: winding 0) |
| no_margin | accepts a segment when its endpoint balls exclude 0, with no D h/2 term and no refinement from 4 points per edge | no | possibly not caught (D0: still winding 1) |
| no_M2 | D without the M2 h/2 term | no | possibly not caught (D0: still winding 1) |
| narrow_frame | wide coordinates and time handed to the narrow-frame instrument unconverted | no | stricter, not caught (D0: every segment fails, undecided) |

**The gate is accepted as a control** if the clean pipeline's verdict is PASS,
and both must-catch faults give FAIL. Anything else is reported as it is.

## What was computed on gate points before this file was committed

All of these were point evaluations, never a box decision:

- The four t = 0 zeros were located with mpmath's findroot on F (each moved at
  most 6e-7 from Spira's digits).
- The correction C = A + B - H was evaluated at the zeros of Z1 and Z2
  (`test_dh.py`).
- H at #61's located Z1 zero was checked against the Gauss-Hermite oracle.

The boxes were drawn from the literature coordinates and #61's recorded box,
with no box decision run on them.

## Cost estimate (before the run)

Development boxes, one process, load average about 21 to 35:

- one H_ball plus Hprime_ball pair costs 0.15 to 0.25 s;
- a clean box run takes 7 to 11 s; a truth run 2 to 3 s;
- the fault runs take 0.3 to 8 s each, except narrow_frame, which spends its
  whole budget: at most 600 evaluations, about 150 s.

Six boxes times (truth + clean + five faults) comes to under 20 core-minutes,
well below the one core-hour that needs the coordinator. One process, nice 10,
started only once the load average is under 64.

## Grades

- The truth and the pipeline's decisions are enclosure-carrying, given hunt
  #61's analytic steps: the shifted-contour M2 derivation, its Phi_DH
  representation, and kappa's functional equation. #61 grades those decided
  and they are not re-reviewed here. A t = 0 count also uses the identity
  H_0 = F, checked against F_split.
- Spira's coordinates were recalled from memory. They are not needed for rigor,
  because the truth step decides each box.
- The gate's verdict is a statement about these six boxes and this rule. It is
  not a statement about any de Bruijn-Newman constant, and the zeta pipeline's
  Theorem 1.3 error terms are not exercised: on DH, f is H itself and E = 0.
