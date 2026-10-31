# DH_GATE_PREREG_2: a second stage for the Davenport-Heilbronn gate, preregistered

**Written and committed 2026-10-31, at landing, before any stage-2 box was
decided.** Stage 1 (`DH_GATE_PREREG.md`, commit 2ba8cbba3) is not changed by
this file: its six boxes, its parameters, its decision table, its verdict rule,
its list of faults that must be caught and its recorded run
(`dh_gate_results.json`, `../RUNS.md` E7) all stand as they are. That file says
that a change after the run is a new preregistration with a new run; this is
that, and it adds boxes rather than changing any.

## Why a second stage

Stage 1 recorded `no_margin` and `no_M2` as not caught: both give PASS. The
cause, read from `dh_gate_results.json` and the stage-1 boxes:

1. **A principal argument fails only when the zeros on one side of a segment
   subtend more than a half turn in total.** H_t is even and entire of order 1,
   so by its Hadamard product its argument change along a segment is the sum,
   over its zeros, of the angle the segment subtends at each, signed by the
   side the zero is on (the lab's reading, unreviewed). A single zero
   subtends less than a half turn at any distance, and zeros on opposite sides
   partly cancel. So a margin-free count can only go wrong where two or more
   zeros lie close to the same side of one segment.
2. **No stage-1 segment met that condition.** Z2, Z3 and Z4 each hold one zero
   at least 0.083 from every edge, with its conjugate more than half a unit
   below the box. Z1 is the one box beside a close pair (its zero and the
   conjugate, 0.041 apart), and both lie below its top edge. But Z1 is centred
   on the zero, whose abscissa is 0.0001 from a vertex of the four-point mesh,
   so the pair's angle is split over two top-edge segments, about 142.5 degrees
   each, and the count stays right. Had the pair sat mid-segment, that segment
   would have subtended about 225 degrees. The fault removes a guarantee; on
   the stage-1 boxes nothing needed it.
3. **`no_M2` drops a second-order term.** Where H is close to linear or
   quadratic along a segment (an isolated zero, or a close pair), |H'| along
   the segment is the distance to a point on a line times a constant, which is
   largest at an endpoint, so the endpoint maximum already bounds |H'| on the
   segment and the dropped M2 h/2 cannot change a decision. It can only matter
   where |H'| peaks strictly inside a segment, which needs a third zero (a
   second zero of H') close to the segment. This file knows no such
   configuration at heights where hunt #61's truth step decides a box: that
   step uses one M2, a supremum over Re z >= x_lo, and |H| falls like
   e^{-pi x/8}, so its boxes are a few units wide at most, while the real zeros
   near x = 480 are about 2.4 apart on average (an estimate from the mean
   spacing 2 pi / log(5 gamma / 2 pi) at gamma = 240, doubled for the wide
   frame; not computed here).

## The configuration stage 2 uses

Hunt #61 located a zero of the narrow-frame flow at t = 36/625 near
z_n = 240.3451714460939 + 0.01018313776460141 i (`winding_results.json`,
`zstar_re`, `zstar_im`; a measured locating pass inside a decided box). In this
evaluator's wide frame it is z = 480.6903 + 0.0204 i at t = 144/625, and its
conjugate 480.6903 - 0.0204 i is also a zero (real coefficients). The pair is
0.041 apart: two zeros close to one side of any segment that passes just above
the upper one.

The stage-2 boxes share the x-range [480.39, 481.19], so that the four-point
mesh of `no_margin` (vertices 480.39, 480.59, 480.79, 480.99, 481.19) has one
segment centred over the pair, and the clean mesh (eight points) has a vertex
directly above it. A segment of half-length 0.1 at height 0.0096 above the upper
zero and 0.0504 above the lower one subtends about 2 arctan(0.1/0.0096) +
2 arctan(0.1/0.0504), about 169 + 127 = 296 degrees.

## The boxes (wide frame, exact rationals)

| name | t | x | y | expected | why |
|---|---|---|---|---|---|
| Z5 | 144/625 | [48039/100, 48119/100] | [1/100, 3/100] | one zero | the upper zero of the pair; the top edge passes 0.0096 above it, so both zeros lie below that edge |
| C3 | 144/625 | [48039/100, 48119/100] | [3/100, 1/5] | none | above Z5; its bottom edge is Z5's top edge, with both zeros below it |

"Expected" is a prior: the truth step (hunt #61's decided count, as in stage 1)
decides each box.

## What is unchanged

- The pipeline: `dh_gate.dh_barrier` exactly as at 2ba8cbba3, with stage 1's
  parameters (8 initial points per edge, max_depth 6, at most 600 evaluations
  per box run, precision `dh.split_prec(x_hi)`).
- The truth step: `dh_gate.truth` at 420 bits.
- The faults: the five of stage 1, unchanged.
- The decision table and the verdict rule: `dh_gate.classify` and
  `dh_gate.verdict`, unchanged. Caught still means a FAIL verdict.

The stage-2 code (`GATE_BOXES_2`, `run_stage2_boxes`, `assemble_stage2`,
`combined_verdicts`, `main_stage2`) only names the new boxes, runs them and
applies the stage-1 rules to their rows.

## Verdicts reported

1. The stage-2 verdict of each run (clean and each fault): the stage-1 rule on
   the stage-2 rows alone.
2. The combined verdict of each run: the stage-1 rule on the union of the
   stage-1 rows (read from `dh_gate_results.json`, not rerun) and the stage-2
   rows.

## Predictions, fixed here

| run | stage-2 prediction | reason |
|---|---|---|
| clean | no ACCEPT and no INCONSISTENT; Z5 REFUSE (winding 1) and C3 DISCRIMINATES, or a box left undecided | the clean rule is sound given the enclosures; next to the pair the margin needs five bisections on y = 0.03 and six, the cap, on y = 0.01 (estimate below), so an undecided Z5 is possible |
| no_margin | **caught (FAIL)**: Z5 ACCEPT, C3 INCONSISTENT | Z5's top edge, traversed from right to left, wraps about +296 degrees on the segment [480.59, 480.79], whose principal value is about -64 degrees, so the count drops by one to 0; C3's bottom edge wraps about -296 degrees there and the count rises by one to 1 |
| no_M2 | **not caught** | reason 3 above: near the pair H is close to quadratic, so the endpoint maximum of |H'| bounds it on every short segment |
| one_corner | caught (Z5 ACCEPT) | as in stage 1 |
| main_terms_only | no prediction | stage 1 caught it on every zero box; its value at this pair was not computed |
| narrow_frame | no prediction | stage 1's expectation for it was wrong |

**Stage 2 is read as showing that the gate can see a margin-free count** if
`no_margin` gives FAIL on the stage-2 boxes and the clean run has no ACCEPT and
no INCONSISTENT row there. Any other outcome is recorded as it comes out. A
stage-2 result does not change the stage-1 verdicts, which stay on record.

## What was computed on stage-2 points before this file was committed

Point evaluations only, never a box decision and never a run of `dh_barrier`
or `truth` on a stage-2 box (`dh.H_ball`, `dh.Hprime_ball` at 433 bits, and
`dh_gate.M2_wide`):

| point (x, y) | abs H | abs H' | arg H |
|---|---|---|---|
| (480.69, 0.03) | 1.103e-84 | 1.364e-82 | -3.107 |
| (480.69, 0.01) | 7.157e-85 | 4.548e-83 | -0.0245 |
| (480.79, 0.03) | 2.469e-83 | 4.525e-82 | 0.555 |
| (480.59, 0.03) | 2.638e-83 | 4.942e-82 | -0.568 |
| (480.39, 0.01) | 2.199e-82 | 1.492e-81 | -0.068 |
| (481.19, 0.01) | 4.755e-82 | 1.689e-81 | 0.036 |
| (480.39, 0.2) | 3.184e-82 | 1.819e-81 | -1.204 |
| (481.19, 0.2) | 5.549e-82 | 1.850e-81 | 0.672 |
| the located zero | 1.811e-96 | 9.255e-83 | |

M2 (wide frame) is 2.729e-79 for Z5 and 2.795e-79 for C3, about 60 times the
local |H''| of about 4.5e-81 implied by the pair. The arguments along y = 0.03 at
480.59, 480.69 and 480.79 fall through -0.568, -3.107 and (one turn down) 0.555,
a change of about -5.16 radians, -296 degrees, as the geometry predicts. With
that M2, the clean rule accepts a segment ending at (480.69, 0.03) only once
h is about 0.0031 (five bisections of the initial 0.1), and one ending at
(480.69, 0.01) only at about 0.0016 (six, the depth cap). These are estimates
from the endpoint values above, not runs of the rule.

## Cost estimate (before the run)

From stage 1's Z1 and C1, at the same t and height: truth 5 to 10 s, clean 15
to 40 s, `narrow_frame` up to its 600-evaluation budget (about 170 s), the
other faults under 20 s each. About four to five minutes per box; the two boxes
run as two processes at nice 10, under ten minutes of wall time.

## Grades

As stage 1: the truth and the pipeline's decisions are enclosure-carrying,
given hunt #61's analytic steps (the shifted-contour M2 derivation, its Phi_DH
representation and kappa's functional equation), which are not re-reviewed
here. The location of the pair is hunt #61's measured locating pass; the truth
step, not that location, decides each box. The stage-2 verdicts are statements
about these two boxes and this rule, not about any de Bruijn-Newman constant,
and Theorem 1.3's error terms are still not exercised (on DH, E = 0).
