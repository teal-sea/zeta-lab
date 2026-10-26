# RUNS: hunt #119, `lambda_dh_exact`

Every run this hunt ever performed, including the ones that produced nothing.
Reconstructed 2026-09-12 from the committed artifacts and the session record,
because the runs that would normally have written this file died before
writing anything.

The hunt ran a theory phase, opened an evaluation phase, and stopped there.
The evaluation agents and the adjudicator all terminated on API 529 errors on
2026-08-18. Three consequences, stated once and true of everything below:
**no verdict was written, no adversary attacked any number, and the nine
predictions registered in `MISSION.md` were never scored.**

## Run 1: the theory phase

```runmanifest
id: R1-theory
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: completed; derivations and their probes ran, nothing was adjudicated
ran:
  - theory.py
artifacts:
  - theory_results.json
  - MISSION.md sections 1 to 5 and the nine registered predictions
```

What it produced, each a float-grade measurement on synthetic or already-published
configurations and none of them on a new Davenport-Heilbronn zero:

- `isolated_pair`: the isolated-pair landing law t* = y0^2/2 reproduced to 3e-13
  at y0 = 0.2 and to machine precision at y0 = 0.5, under exact polynomial flow.
- `quartic_control`: the closed-form quartic landing time agreed with the
  measured one to 4e-13 at two parameter settings, with the real-root count
  after landing equal to 4 as required.
- `no_creation`: 400 sampled configurations, 400 admitted at t = 0, and **0**
  in which forward flow drove two real zeros off the axis. This supports the
  no-creation step. It does not prove it, and `MISSION.md` says the proof is
  meant to come from the time-reversed Sturm zero-number theorem.
- `crowding`: the one-parameter shave model against exact polynomial flow.
- `calibration`: nine `d/h` ratios from hunts/flow_repair's landings, mean
  1.4284417709796269.
- `density`: the local zero-density formula against measured strip counts, best
  row 1.4 percent relative.
- `criterion`: the model's ceiling on sup t* at 0.14709208930872253, which is
  0.764413309320685 of the hunt #61 upper bound, with the crossover heights at
  which each candidate floor would have to be attained.
- `delay`: of 300 sampled two-pair configurations, 6 land later than the
  isolated-pair value, which is why only Delta^2/2 and not y0^2/2 is read as a
  ceiling.
- `lesion_degree52`: a deliberately planted fault, recorded so the detector's
  blind spot is visible rather than inferred.

## Run 2: the low and middle screens

```runmanifest
id: R2-screen
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: partial; the low screen completed, the middle screen was cut off mid-sweep and no zero was ever located from either
ran:
  - deep_zeros.py validate
  - deep_zeros.py screen 8 10000
  - deep_zeros.py screen 10000 100000
artifacts:
  - deep_zeros.json
```

- `validation`: the float64 Euler-Maclaurin route against mpmath at dps 25,
  worst absolute error 1.09e-12 over the sampled points, 9.3e-15 at the best.
- `screen` over t in [8, 10000] at Re s in [0.85, 2.05]: `complete: true`,
  65 refinements, 13.6 s, **21 flagged windows**, each of winding count 1.
- `screen_hi` over t in [10000, 100000]: `complete: false`. It stopped after
  349 refinements and 1143 s with 88 windows flagged, and the remainder of the
  range was never swept.
- **`stage_locate` never ran on either screen.** Neither has a `zeros` key, so
  no zero was pinned down and no window was ruled out. A flagged window is a
  place the argument principle says to look, not a zero.

## Run 3: the screen's own controls

```runmanifest
id: R3-control
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: completed; the screen nests correctly in its inner abscissa
ran:
  - deep_zeros.py screen 8 600 --sigma-c 0.55
  - deep_zeros.py screen 8 600 --sigma-c 0.75
artifacts:
  - deep_zeros_control.json
```

Both completed. Over t in [8, 600] the flagged-window sets are strictly nested
as the inner abscissa drops, which is what the argument principle requires of a
contour that is being widened:

| inner abscissa Re s | flagged windows in [8, 600] | total winding |
|---|---|---|
| 0.85 | 1 | 1 |
| 0.75 | 7 | 7 |
| 0.55 | 13 | 14 |

and set-wise 0.85's window is contained in 0.75's, which is contained in
0.55's. The single window the deepest screen flags below height 600 is
[228, 248], which is the window holding the pair at gamma = 240.4046 that
hunts/flow_repair had already measured. That agreement was not arranged.

## Run 4: the height-10^6 screen, the only evaluation datum

```runmanifest
id: R4-deep
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: completed for its window; one zero located, float grade, never enclosure-decided and never adjudicated
ran:
  - deep_zeros.py screen 1000000 1001200
  - deep_zeros.py locate
artifacts:
  - deep_zeros_1e6.json
```

`complete: true` over t in [1000000, 1001200], 7 refinements, 762.8 s, exactly
one flagged window [1000440, 1000460], and `stage_locate` did run here. The
zero:

| quantity | value |
|---|---|
| gamma | 1000459.7433532759 |
| beta | 0.8583118590734415 |
| depth y0 = beta - 1/2 | 0.35831185907344154 |
| winding count | 1 |
| winding defect | 2.220446049250313e-16 |
| abs f at the root | 4.3516753449553316e-11 |
| route | float64 Euler-Maclaurin + Newton |

Read it as one float-grade location with a unit winding count whose defect is
at machine precision. It is not an enclosure and the sweep covered 1200 units
of height, not a decade.

## Run 5: the landing census

```runmanifest
id: R5-landing
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: completed; nine landings with their neighbour distances, used as the model's training and holdout data
ran:
  - landing.py
artifacts:
  - landing.json
```

The nine hunts/flow_repair pairs with measured nearest and second-nearest
neighbour distances, local strip-zero counts and measured densities: the data
`theory.py`'s calibration consumes.

## Runs that were started and produced nothing

```runmanifest
id: R6-dead
hunt: lambda_dh_exact
started: 2026-08-18
finished: 2026-08-18
outcome: null; all four agents terminated on API 529 before writing an artifact
ran:
  - evaluation agent 1, the depth-versus-height law above height 10^4
  - evaluation agent 2, the shave model against new landings
  - evaluation agent 3, the no-creation step as a proof rather than a sample
  - the adjudicator, which would have scored the nine predictions
artifacts:
```

Recorded because a null run that is not written down looks like a run that was
never planned. The five kill conditions in `MISSION.md` are therefore all
unfired rather than survived, and the pre-registered verdict (that the bracket
does not collapse) is unevaluated.

## Resumption, 2026-10-26: estimates before spending

Measured unit costs on the shared box (load about 10 of 32), python-flint
backend confirmed (`rigor.BACKEND == "python-flint"`):

- Arb: one evaluation of f(s) = 5^{-s} sum_a c_a zeta(s, a/5) at
  s = 0.858 + 1000459.74 i, 128 bits: 1.7 s (2.3 s at 192 bits).
- mpmath.iv: one term n^{-s} at that height, 96 bits: 134 microseconds.

**Step 1 (decide the deep zero).** Arb leg: a rectangle boundary of about 32
segments needs about 32 point plus 32 segment evaluations, about 64 x 1.7 s,
call it 2 to 4 minutes with subdivision. iv leg: Euler-Maclaurin with
N = ceil(1.25 |s| / 2pi), about 2.0e5, so a head of about 8.0e5 nonzero terms,
each one complex exponential plus a degree-6 Taylor update, about
8e5 x 200 us = 160 s once for the Taylor coefficients; each later evaluation
is a polynomial plus a 4 x 165-term tail, under 1 s. Total step 1: about
10 core-minutes, under the one core-hour gate, so no ask.

## Run 7: the height-10^6 zero, decided on both backends (2026-10-26)

```runmanifest
id: R7-decide-deep
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: decided; exactly one zero of f in an exact rectangle of half-width 2^-27 lying wholly in Re s > 1/2, same integer on Arb and on mpmath.iv, planted faults flip it to 0
ran:
  - decide_deep_zero.py --quick (Arb leg alone, first)
  - decide_deep_zero.py (both legs, faults, cross-check)
artifacts:
  - decide_deep_zero.json
```

Backends: python-flint (Arb, 128 bits, Arb's Hurwitz zeta) and mpmath.iv
(128 bits, hand-rolled Euler-Maclaurin, N = 199153, p = 293, Taylor model of
degree K = 14 about the rectangle centre, head built once in 383 s). Total
wall time 525 s on one core, against the 10 core-minute estimate above.
Rectangle: sigma in [943723861105, 943723877489] / 2^40, t in
[537117734833355, 537117734833363] / 2^29. Both legs: 16 segments, winding
enclosure [0.9999999999999991, 1.0000000000000009], count 1. Worst
clearance-over-tube margin 1420 (Arb) and 174151 (iv). Planted faults: kappa
+ 1e-3 (Arb) and the rectangle shifted right by four half-widths (both legs)
each decide count 0. Cross-check: Arb and iv enclosures of f intersect at two
corners and the centre, radii 7e-33 and 5e-31.

Two instrument bugs met and fixed on the way, both before any count was read:
the segment-ball test was replaced by the chord tube after Arb's ball over a
segment measured about 120 |f'| times the segment radius (it would have
needed about 1400 segments), and mpmath 1.3's interval `conjugate()` raises,
so the conjugate is built from parts. A third was met in Run 8.

## Run 8: the 21 low-screen zeros, located and decided (2026-10-26)

```runmanifest
id: R8-locate-low
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; stage_locate found 21 zeros, one per flagged window, and all 21 are decided count 1 on both backends
ran:
  - deep_zeros.py locate --out deep_zeros_locate_20261026.json
  - decide_low_zeros.py
artifacts:
  - deep_zeros_locate_20261026.json
  - decide_low_zeros.json
```

`stage_locate` wrote into a copy of the low screen (`deep_zeros.json` is
unchanged), 10.5 s. `decide_low_zeros.py` then ran the Run 7 instrument
around each zero, 270 s for all 21 on both backends. The iv leg first came
back "undecided" at gamma = 240: it chose the Euler-Maclaurin order p from
|s| alone, and below height about 600, 2p > |s| makes the Pochhammer factor
grow factorially (the point enclosure was 1e85 wide). Fixed by fixing p first
and taking N from |s| + 2p; the deep run was rerun after the fix and is the
one recorded.

## Run 9: screen_hi finished (2026-10-26)

```runmanifest
id: R9-screen-hi
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; the sweep stopped on 2026-08-18 at t = 82480 was resumed from its own checkpoint and finished at t = 100000
ran:
  - deep_zeros.py screen --t0 10000 --t1 100000 --out deep_zeros_hi_20261026.json --key screen_hi
artifacts:
  - deep_zeros_hi_20261026.json
```

Resumed on a copy, so the recorded `deep_zeros.json["screen_hi"]` still reads
`complete: false` and is now superseded by the copy, which reads
`complete: true`, 536 s for the last 17520 units, 111 flagged windows, each
of winding 1, worst defect 4.4e-12.

## Estimate before spending: the landing census to 10^4 and 10^5 (step 3, not run)

Asked of the coordinator before any of it runs (over the one core-hour gate).

**Route.** The Xi-plane contour-moment landing measurement is out of reach at
these heights: `hunts/lambda_dh_bounds/census_results.json` records 1126 s
for one pair at gamma = 412 (dps 165) and projects 35 to 60 min at gamma =
531 (dps about 206, about 27000 nodes). dps and node count both grow linearly
in gamma, so cost goes roughly as gamma^2.6, about 1e3 core-hours per pair at
10^4. The census therefore uses the N-body ODE landing that
`lambda_dh_bounds` validated against the Xi-plane measurement to 0.04 percent
on flow_repair pairs 1 to 5: 77.7 s for one pair at gamma = 531 with 69 line
zeros in a 40-unit window, 800 steps. Its grade is *measured*.

**Who needs a landing.** A pair can beat the measured landing 0.0576518 only
if y0^2/2 exceeds it (up to the delay mechanism, 6 of 300), so y0 > 0.3395;
screen at Re s = 0.82 (y0 > 0.32) for margin.

| piece | unit cost (measured) | units | core-hours |
|---|---|---|---|
| screen [8, 1e4] at 0.82 | 13.6 s at 0.85 | x2 for the deeper edge | 0.01 |
| screen [1e4, 1e5] at 0.82 | 1143 s + 536 s at 0.85 | x1.3 | 0.6 |
| locate | 0.5 s (low), about 5 s (1e5) | about 40 + 200 | 0.3 |
| line-zero scan per pair | float evaluator, seconds | 240 | 0.1 |
| ODE landing, gamma < 1e4 | about 100 s | about 40 pairs | 1.1 |
| ODE landing, 1e4 to 1e5 | about 240 s (window holds 1.75x the line zeros, O(n^2)) | about 200 pairs | 13 |

Pair counts extrapolate the 0.85 counts measured here (21 below 1e4, 111 in
[1e4, 1e5]) by about 1.8 for the deeper edge, from the nesting control's
slope. **Total: about 1.5 core-hours to 10^4, about 15 core-hours more to
10^5**, each uncertain by a factor 2 either way, so 0.7 to 3 and 7 to 30.
That sits inside the recon's 10 to 50. Wall time on this box at 4 processes:
about 25 min to 10^4 and 4 h to 10^5. Sharded by height on GitHub Actions
(4 vCPU jobs, 10 shards), the 10^5 leg is about 1 h of wall time.

**Also priced: a decided zero-free statement for kill condition 2.** Count
the zeros of f with beta >= 0.90 in t in [8, 10^4] by the Run 7 instrument
along the edge Re s = 0.90 (the right edge at Re s = 2.05 is free, where
sum_{n>=2} |a_n| n^{-2.05} < 1). Arb costs 1 to 30 ms per evaluation below
10^4; about 2e5 boundary points plus one second-derivative ball per block
comes to about 1 core-hour, 15 min of wall time at 4 processes.

### Revised estimate for the decided KC2 count, timed before the run

Coordinator's reply to the ask (2026-10-26): run the decided KC2 count first,
then the census to 10^4; defer 10^5. `decide_kc2.py time` on 5-unit pieces of
the left edge Re s = 0.90 (blocks of 1/8, chord-tube margins 1.003 to 1.19):
0.08 s per unit of height at t = 500, 0.64 at 5000, 1.56 at 9900. Integrated
over [8, 10^4] that is about 7500 s, **about 2.1 core-hours**, twice the
1 core-hour priced in the ask (the price assumed about 2e5 points; the edge
needs about 60 per unit near 10^4). Within the factor-2 band stated there, so
it runs as 8 height shards, 4 at a time, about 35 min of wall time.

### Deferred: the 10^5 leg, and the workflow proposed for it (not added)

Deferred by the coordinator until the 10^4 results are in. The estimate
stands as above: about 15 core-hours (7 to 30). What it would answer: P4 and
P5 past 10^4 (does the measured sup of landings peak and fall, kill
condition 4), and the landing of the deepest pair seen in that decade,
y0 = 0.437058 at gamma = 49688.34 (`deep_zeros_hi_20261026.json`, float),
whose y0^2/2 = 0.0955 is the largest naive landing this hunt has located.
`screen_hi` is already complete at Re s = 0.85, so the leg needs only the
deeper re-screen at 0.82 for the band y0 in (0.32, 0.35), the window census,
and the ODE landings.

Proposed GitHub Actions workflow, written here rather than added under
`.github/` (the brief forbids adding one unasked; nothing in this PR touches
`.github/`):

```yaml
# .github/workflows/hunt119-census-1e5.yml  (PROPOSAL, not committed)
name: hunt119-census-1e5
on: workflow_dispatch
jobs:
  shard:
    runs-on: ubuntu-latest           # 4 vCPU / 16 GB / 6 h
    timeout-minutes: 300
    strategy:
      fail-fast: false
      max-parallel: 10
      matrix:
        lo: [10000, 19000, 28000, 37000, 46000, 55000, 64000, 73000, 82000, 91000]
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: {python-version: "3.12"}
      - run: pip install -r requirements.txt && pip install -e .
      - run: python -c "from zeta import rigor; assert rigor.BACKEND == 'python-flint'"
      - name: re-screen, locate, window census, ODE landings for [lo, lo + 9000]
        run: |
          python hunts/lambda_dh_exact/deep_zeros.py screen --t0 ${{ matrix.lo }} \
            --t1 $(( ${{ matrix.lo }} + 9000 )) --sigma-c 0.82 \
            --out shard.json --key screen_c82
          python hunts/lambda_dh_exact/deep_zeros.py locate --out shard.json --key screen_c82
          python hunts/lambda_dh_exact/census_1e4.py --source shard.json --out census_${{ matrix.lo }}.json
      - uses: actions/upload-artifact@v4
        with: {name: "census-${{ matrix.lo }}", path: "census_*.json shard.json"}
```

It needs one change to `census_1e4.py` before it can run: a `--source`
option reading float locations from a screen artifact instead of
`decide_low_zeros.json`. Ten shards of about 1.5 core-hours each fit one
runner's 6 h with a factor of 4 to spare; outcomes would be recorded here by
artifact SHA-256.

### Census to 10^4, timed before the run

Control on the floor pair (gamma = 240.4047): window accounting closes
(strip 67 = 65 line + 2 x 1), ODE t* = 0.0576657 against the recorded
Xi-plane 0.05765184 (+0.024 percent, inside the 0.04 percent band), 16.2 s.
The 21 candidates at heights up to 10^4 should cost 16 to about 120 s each
(line zeros in the window grow from 65 to about 113, ODE cost as n^2), so
**about 0.3 core-hours**, under the 1.1 priced. One process, sequential.

## Run 10: kill condition 2 by a decided zero-free count (2026-10-26)

```runmanifest
id: R10-kc2-decided
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: decided on Arb; zero zeros of f in [0.90, 2.05] x [8, 10^4]; planted faults give 1 and 0 as required
ran:
  - decide_kc2.py shard --i 0..7 --n 8 (4 at a time, nice 10)
  - decide_kc2.py short
  - decide_kc2.py fault
  - decide_kc2.py combine --n 8
artifacts:
  - kc2/left_0_of_8.json ... kc2/left_7_of_8.json
  - kc2/short_edges.json
  - kc2/faults.json
  - decide_kc2.json
```

Arb (python-flint) only, 96 bits. Left edge Re s = 0.90: 79936 blocks of 1/8,
448092 point evaluations, 6579 core-seconds (1.83 core-hours, inside the
revised 2.1), no block needed splitting, worst clearance-over-tube 1.0000007
(every accepted segment has clearance strictly above its tube; segments that
did not were halved). Short edges: right edge by the decided bound
S = sum_{n>=2} |a_n| n^{-2.05} in 0.24597836634965556 +- 5e-28 < 1; bottom
and top by the chord tube. Total winding ball [-5.4e-12, 8.0e-12], count 0.
Faults: [0.89, 2.05] x [2400, 2500] gives 1 (the zero at gamma = 2442.53,
beta = 0.89775), [0.90, 2.05] x [2400, 2500] gives 0.

Why one backend: the mpmath.iv route costs about 1 s per point evaluation at
these heights against Arb's 1 to 30 ms, so the 448092 points would be about
120 core-hours. The second backend was not run, and the count is graded
decided on Arb alone.

## Run 11: the landing census to height 10^4 (2026-10-26)

```runmanifest
id: R11-census-1e4
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; 21 of 21 windows accounted and landed by the ODE; control within band; no landing beats 0.0576518
ran:
  - census_1e4.py --index 4 (control, the floor pair, scratch output)
  - census_1e4.py --only 21
  - kc2/below8.py (the strip |t| <= 8 for kill condition 2, decided count 0)
artifacts:
  - census_1e4.json
  - kc2/below8.json
```

21 candidates, 32.7 to 65.6 s each, about 0.3 core-hours, as timed. Window
accounting N_strip = N_line + 2 N_right closed at the first line-zero grid in
all 21. One instrument bug met before the run: Newton on the fast evaluator
diverged to NaN from a poor grid seed; `census_1e4.py` carries its own
box-guarded Newton (`deep_zeros.py` is unchanged). `kc2/below8.py` first
failed on the real axis at s near 1, where the four Hurwitz poles cancel and
a ball evaluation is useless; the rectangle was made symmetric about the real
axis so s = 1 is interior.

**Total resumption spend**: about 2.6 core-hours (step 1 0.15, step 2 0.25,
KC2 1.85, census 0.3, controls and timing 0.05), against 2.5 approved for the
KC2 count and the census plus the earlier sub-hour steps.

### Targeted check above 10^4, estimate before spending

Coordinator-approved 2026-10-26: land the four pairs with y0 > 0.40 in
[10^4, 10^5] (float locations from `deep_zeros_hi_20261026.json`), chosen with
the registered model, as a targeted check and not a census. At gamma about
2e4 to 5e4 a +-40 window holds about 120 to 135 line zeros, so about 2 to 4
min each with the window counts: about 0.2 core-hours, sequential.

Correction to the ask, recorded when it was noticed: the decade holds
**nine** zeros with y0 > 0.40, not four (0.43706, 0.41860, 0.41833, 0.41614,
0.41031, 0.40897, 0.40718, 0.40569, 0.40022). The four named in the ask were
those whose model landing exceeds 0.85 x 0.0576518, and a first correction
written here said seven because only the top of a sorted list had been
printed; both slips were in the writer's reading, not in the artifact. The run
lands all nine, which is the approved selection rule (y0 > 0.40), at about
0.8 core-hours (about 5 to 7.5 min each at these heights) rather than 0.2.

## Run 12: the targeted check above 10^4 (2026-10-26)

```runmanifest
id: R12-deep-above-1e4
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; nine pairs with y0 > 0.40 in [10^4, 10^5] attempted, eight landed (none near the floor), one left unlanded because its window accounting stayed open
ran:
  - census_1e4.py --source deep_zeros_hi_20261026.json --min-y0 0.40 --out census_deep4_1e5.json
artifacts:
  - census_deep4_1e5.json
```

3137 core-seconds (0.87 core-hours), 279 to 455 s per pair. The window at
gamma = 88167.40 kept N_strip = 142 against 128 line zeros + 2 x 6 off-line
after the line grid was refined to 1/240 of a gap, so that pair was not
landed. **Total resumption spend: about 3.5 core-hours.**

## Run 13: the test module and its planted faults (follow-up, 2026-10-26)

```runmanifest
id: R13-pins
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; both tiers pass, and the planted-fault run turns exactly the recomputation tests red
ran:
  - pytest -q -n0 -m "not slow" hunts/lambda_dh_exact
  - pytest -q -n0 hunts/lambda_dh_exact
  - LDH_PLANT_FAULT=1 pytest -q -n0 hunts/lambda_dh_exact
artifacts:
  - test_lambda_dh_exact.py
```

Estimate before spending: the recomputations were timed first (Arb leg of
one low zero 0.03 s, iv leg 10.4 s, falling to 2.8 s once `IvRoute` cached
its Euler-Maclaurin coefficients; the |t| <= 8 rectangle 0.5 s; the 2442
window 6 s; the lowest KC2 shard about 125 s, so that one is `slow`). The
cache multiplies the same intervals in the same order as before, so no
recorded enclosure depends on it. Outcomes are recorded below, under
"Run 13 outcomes".

## Run 14: the slip effect and the per-pair d/h refit (follow-up, 2026-10-26)

```runmanifest
id: R14-slips-refit
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; four inherited y0 slips corrected in this hunt (flow_repair untouched), their effect measured below every reported digit; the one-sided d/h plug-in is worse than the frozen DBAR, the inverse tracks measured d/h at r = 0.967
ran:
  - slip_effect.py (stage 5 and stage 6 with recorded and corrected y0; 9 s)
  - refit_dh.py (29 landings, plug-in and inverse; 2 s)
artifacts:
  - slip_effect.json
  - refit_dh.json
```

Both under a core-minute. See `RESULTS.md` section 8.9.

### Run 13 outcomes

- `pytest -q -n0 -m "not slow" hunts/lambda_dh_exact`: **31 passed, 1
  deselected, 12.9 s.**
- `pytest -q -n0 hunts/lambda_dh_exact`: **32 passed, 131 s** (the slow
  shard recompute about 112 s of it).
- `LDH_PLANT_FAULT=1 pytest -q -n0 hunts/lambda_dh_exact`: **4 failed, 28
  passed, 126 s**. The four red tests are exactly the recomputations:
  `test_recompute_one_low_zero_on_both_backends` (zero pushed four
  half-widths past its interval), `test_recompute_kc2_below8_slice` and
  `test_recompute_kc2_edge_sensitivity_at_2442` (count off by one), and
  `test_recompute_kc2_lowest_shard_matches_record` (one extra winding on the
  slice). The pins and the four always-on fault tests stay green, as they
  should, because they do not read the switch.
- Gates `tests/test_hunt_probe_discipline.py`, `test_hunt_numbering.py`,
  `test_docs_numbering.py`, `test_doors.py`, `test_hunt_doors.py`,
  `test_huntspec.py`: 86 passed, 3 xfailed. `scripts/make_context.py --check`:
  up to date.

## Estimate before spending: the two-sided gap (unit 3, step 1)

Line scan of [gamma - 4h, gamma + 4h] per window, about 480 grid points plus
about 8 x 30 bisections. The fast evaluator costs about 1 ms per point at
gamma = 5e4 (about 1.2e5 head terms) and much less below 1e4, so it should
take under 5 s per window. For 29 windows that is **under 0.05 core-hours**,
then 29 one-dimensional integrals, about a second in total. Cap from the
coordinator: 0.5 core-hours, one process, nice -n 10, wait while loadavg
exceeds 64.

## Run 15: the two-sided local gap (unit 3, step 1, 2026-10-26)

```runmanifest
id: R15-twosided
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; gate clean (max defect 1.3e-11); pre-registered verdict IMPROVES (rms 0.112, 26 of 29 in band), not PASS
ran:
  - twosided.py (one process, nice 10, loadavg 18.6 at start)
artifacts:
  - twosided.json
```

12.8 s of compute (0.004 core-hours), against the estimate of under 0.05
and the cap of 0.5. The PREREG (RESULTS.md section 8.10) was committed and
pushed as a31d30911 before the run. Pinned in `test_lambda_dh_exact.py`
section 6. The planted fault (under `LDH_PLANT_FAULT=1`, the lower neighbour
of the control window moved by 5 percent of a gap) turns
`test_recompute_twosided_control_window` red, and only that test among the
twosided ones.

## The 1e5 census on Actions: prepared, not triggered (unit 3, step 2)

**Workflow**: `.github/workflows/lambda-dh-census.yml`. It runs only on a push
to `hunt/lambda-dh-exact-resume` that touches
`hunts/lambda_dh_exact/RUN_REQUEST.json`, which is *not* in the tree.
Limits: `permissions: contents: read`, concurrency group `lambda-dh-census`,
`timeout-minutes` 350 per shard job (each process self-stops at 335), matrix
`max-parallel: 4`. Artifacts are named
`lambda-dh-census-r<request attempt>-job<j>-attempt<run_attempt>`. A re-run
attempt downloads its job's earlier attempts into separate directories, and
`census_shard.py gather` keeps the most advanced copy of each shard, so a
stale copy cannot win by download order. The shard run itself resumes: the
screen from its checkpoint, the census by skipping landed rows.

**Shard plan**: `census_plan_1e5.json`, sha256
`461079f90cf78f9c635b44ab365d9cf956cbe8bce23532fc55c6d4eef226eaa9`. 36 shards
of 2500 units tile [10^4, 10^5]: 9 jobs x 4 processes, so 16 shards at a
time. Per shard: screen at Re s = 0.82, locate, land every zero with
y0 > 0.3396.

**Preflight, fail closed** (`census_shard.py preflight`, every job):
- the exact versions in `census_constraints.txt` (python-flint 0.9.0,
  mpmath 1.3.0, numpy 2.5.4, scipy 1.18.1: those that made `census_1e4.json`);
- `rigor.BACKEND == "python-flint"`;
- `RUN_REQUEST.json`'s `plan_sha256` equal to the committed plan's, and the
  committed plan equal to the one the code generates;
- the smoke row: `census_1e4.json`'s γ = 240.4047 window recomputed, with
  integer counts equal and the landing within 1e-6 relative. Locally it
  reproduces 0.057665659795901776 exactly, in 16 s.

A wrong hash exits non-zero before any computation (pinned by a test).

**Calibration mode** (`{"mode": "calibrate"}`): one job runs one shard,
`calibrate_shard` (default 18 = [55000, 57500], mid-decade height, 3 zeros at
0.85 against a decade mean of 3.1), in one process. `census_shard.py calib`
then reports CPU seconds (user + sys of the stage subprocesses) per screened
20-unit window and per census window. It projects core-hours two ways: x36,
and scaled from the decade's 111 zeros at 0.85 by the shard's ratio.

**Local dry run** (mini-plan [24400, 24440], one candidate): screen 7.0 s,
locate 6.6 s, census 130.9 s CPU. The landing of γ = 24415.48 reproduces
`census_deep4_1e5.json` to 6e-14 relative. The second run resumed (census
6.3 s), and gather and merge worked. One defect was found and fixed: a
resumed run overwrote the CPU record instead of adding to it.

**Projected cost, before calibration**: screen at 0.82, 4500 windows at about
0.5 s (the 0.85 screen measured 0.37 s per window over the decade), about
0.6 core-hours. Candidates: about 111 at y0 > 0.35, times about 1.6 for the
band (0.3396, 0.35] (half of the low screen's 21 lie in [0.35, 0.36)),
about 180. Census about 150 to 350 s each (131 s measured unloaded at
γ = 24415, 279 to 455 s under load at 2e4 to 9e4). **About 13 core-hours
(8 to 20)**, inside K-e's 30. Wall about 2 h at 16 concurrent shards. The
calibration replaces all of this with runner numbers.

### Unit 3 test outcomes (2026-10-26)

- `pytest -q -n0 -m "not slow" hunts/lambda_dh_exact`: 41 passed, 1
  deselected, 15 s.
- `pytest -q -n0 hunts/lambda_dh_exact`: **42 passed, 129 s.**
- `LDH_PLANT_FAULT=1`: **6 failed, 36 passed**. The four recomputations of
  Run 13, plus `test_recompute_twosided_control_window` (a neighbour moved
  5 percent of a gap) and
  `test_census_pins_match_the_versions_that_made_the_artifacts` (a drifted
  pin).
- Gates (`tests/test_doors.py` excluded per the brief; CI runs it):
  81 passed, 3 xfailed. `make_context.py --check`: up to date.

### Coordinator's go, and the memory record (2026-10-26)

Reply to the ask: go for `{"mode": "calibrate", "attempt": 1, "plan_sha256":
"461079f9..."}` after one change, recording memory. `census_shard.py run`
now writes `peak_rss` into each shard JSON: `RUSAGE_SELF` as asked, and
`RUSAGE_CHILDREN`, because the screen, locate and census stages run as child
processes. The driver alone measured 0.017 GiB against 0.22 GiB for its
children on the local mini-plan, so `RUSAGE_SELF` alone would have
understated memory 13-fold. `calib` reports `peak_rss_gb`,
`four_x_peak_rss_gb` and the 13 GB check in `calibration.json` and in the
step summary. Pinned by `test_census_records_peak_rss_and_calib_reports_it`;
a planted 3.5 GiB peak turns it red.

Measured before pushing: the whole window machinery (both counts, line
zeros, location) at the top of the decade, γ = 99500, peaks at **0.23 GiB**
(`/usr/bin/time -v`: 239836 kB), so 4 x peak is about 0.9 GB. It took
**6.6 min** without the ODE. Per-candidate cost grows with height (131 s
in total at 2.4e4), so the projection is revised: about 320 s per candidate
averaged over the decade, x about 180, plus the screen, **about 17
core-hours (10 to 25)**. That is still under the coordinator's 20-hour bar
for the full run, but nearer it. The mid-decade calibration shard measures
the average, and its number decides.

Pre-approved conditions for `full` (coordinator): the smoke row passes;
projected core-hours <= 20; 4 x peak RSS <= 13 GB. Otherwise, report the
numbers instead. Never push a second request while a run is running or
pending.

### Workflow fix after the calibrate push (2026-10-26)

The coordinator's fix (add `shell: bash` so `calib | tee` runs under
`-o pipefail`) reached this session after the calibrate request had already
been pushed (964847327, run 40357487645 in progress). It went in as a
workflow-level `defaults: run: shell: bash` in the next commit, pinned by
the guard-rail test. The in-flight calibrate run uses the file as it was at
964847327, so its calibration record step could go green on a failing
`calib`. Its numbers are therefore re-derived from the uploaded `shard_18.json`
with `census_shard.py calib` before anything is read from the step summary.

## Run 16: census calibration on Actions (run 40357487645, 2026-10-26)

```runmanifest
id: R16-census-calibrate
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; preflight ok on the runner (smoke landing exact); all three pre-approved conditions for the full run met
ran:
  - lambda-dh-census.yml, mode calibrate, request attempt 1, run_attempt 1, shard 18 = [55000, 57500], one process
artifacts:
  - census_runs/calibrate_r1/shard_18.json (sha256 795a3fbd9c288ffe56164fd26d2513e2a81186d175c334e282d2040d1d84bdbc)
  - census_runs/calibrate_r1/calibration.json (sha256 fb8fc6ec3daadc0ef7a029ed7984de32fa366acd8cf9dce9269ec85800711e9d)
  - census_runs/calibrate_r1/census_18.json (sha256 b7ec99cba72e769f75a024f04785fb27d64474c5b055b2ea563f153c377dbd89)
  - not committed: screen_18.json (7259dc7c...42bd), log_18.txt (c512c1f7...59b0), in artifact lambda-dh-census-r1-job0-attempt1
```

Shard job 17 min 23 s of wall time. Preflight on the runner: pins equal, Arb
backend, plan hash equal, smoke landing 0.057665659795901776 (identical to
`census_1e4.json`), 13.7 s. Shard 18: 125 screen windows, 9 zeros located
at Re s > 0.82, 6 candidates with y0 > 0.3396, 6 landed, 0 unaccounted.
CPU: screen 22.95 s, locate 16.15 s, census 930.46 s. **0.313 CPU-s per
screened window, 155.1 CPU-s per census window.** Projected core-hours:
**9.70** (x36) and **9.95** (scaled from the 111 zeros at 0.85). Peak RSS
0.238 GiB (children; driver 0.018), **4 x peak 0.95 GB**.
`calibration.json` was re-derived locally from `shard_18.json` with
`census_shard.py calib` and agrees in every field. This run used the
workflow before the pipefail fix, so the step summary was not trusted on
its own.

Pre-approved conditions (coordinator, 2026-10-26): smoke passes (yes),
projected <= 20 core-hours (9.95), 4 x peak RSS <= 13 GB (0.95). **All met,
so the full request is pushed next.** No other census run was running or
pending (checked with `gh run list` just before).

The six calibration landings (measured, recorded here, not read against the
pre-registration until the merged census exists) are 0.0287 to 0.0394,
none later than y0^2/2.

## Run 17: the full census (run 40360558359, 2026-10-26): K-d fires, census void

```runmanifest
id: R17-census-full
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed on Actions (36 of 36 shards, merge success); evaluated against RESULTS.md 8.12: K-d fires, so the census is void as registered
ran:
  - lambda-dh-census.yml, mode full, request attempt 1, run_attempt 1 (9 jobs x 4 processes, max-parallel 4)
  - evaluate_census.py (locally, 3.6 min)
artifacts:
  - census_runs/full_r1/census_1e5.json (sha256 84e8ec88a7dcc75d33318edba9a8fa9b99fbc106efaa61df6238f6135331af72; equals the merge job's printed sha256; artifact zip lambda-dh-census-r1-merged-attempt1 digest sha256:85790e6fc92fdaeade731a3de0539d93c65c775ddb6e6e817b01191e6d803b0b, equal to the downloaded zip)
  - census_runs/full_r1/evaluation.json
```

Wall 16:35 to 17:39 (64 min). **11.05 core-hours** of CPU summed over the
36 shard records (projected 9.95; K-e's stop is 30). Peak RSS 0.258 GiB
(max over shards). 162 rows, 161 landed, 1 unaccounted (γ = 88167.40
again). **K-d fails:** seven of the eight targeted pairs re-land to
3e-12 relative or better, but γ = 20011.16 (y0 0.4002) is absent from the
census. Cause: `deep_zeros.stage_locate` accepted a root at γ = 20017.93,
β = 0.727, for the flagged window [20000, 20020]. That root lies outside the
counted box β > 0.82, so the window's true zero was never located. The
check in `stage_locate` is on height only (`pa - 0.5 <= Im <= pb + 0.5`),
not on β > sigma_c. **16 of the 282 located census zeros are mislocated
this way** (β <= 0.82, listed in `evaluation.json`'s companion,
`census_runs/full_r1/mislocated.json`). The completed 0.85 `screen_hi`
of Run 9 has one too (β = 0.7132).

### Estimate before spending: relocating the missed zeros (diagnostic)

17 windows (16 census, 1 screen_hi), each a constrained search on its own
20-unit window: grid minima of |f| over Re s in [sigma_c + 0.005, 1.15]
(24 rows x 400 points), Newton kept inside the box, then a float count on
the box to confirm exactly one. At heights to 9e4 that is about 20 to 40 s
per window, **about 0.2 core-hours**, one process, nice 10. Measured grade
(float, diagnostic only). It does not repair the census: the census stays
void as registered.

## Run 18: relocating the mislocated windows (diagnostic, 2026-10-26)

```runmanifest
id: R18-relocate
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; all 17 windows count 1 in their box and hold exactly one root found by the constrained search; 8 census candidates with y0 > 0.3396 were missed (deepest 0.4002 at γ = 20011.16); the screen_hi window's true zero has y0 0.3742
ran:
  - relocate_missed.py (one process, nice 10)
artifacts:
  - census_runs/full_r1/mislocated.json
  - census_runs/full_r1/relocated.json
```

360.7 s (0.10 core-hours), against an estimate of 0.2. Measured grade,
diagnostic. It does not repair the census (RESULTS.md section 8.13).

### Unit 3 final test outcomes (2026-10-26)

- Fast tier: 47 passed, 1 deselected, 15 s. Both tiers: **48 passed, 127 s.**
- `LDH_PLANT_FAULT=1`: **12 failed, 36 passed**. Exactly the planted tests
  go red: the 4 recomputations of Run 13, the two-sided control window, the
  pin drift, the RSS record, and the 5 census tests of `RESULTS.md` 8.13
  (merged-hash byte, K-d with the missing pair restored, an evaluation
  that let K-d pass, a kept wrong root, the screen_hi true zero made
  deeper).
- Gates (without `tests/test_doors.py`): 81 passed, 3 xfailed.
  `make_context.py --check`: up to date.

## Unit 4 (2026-10-26): estimate before spending, the audit under the guard

Coordinator's decision: re-run the whole census on guarded code (request
attempt 2), with no splicing onto the void attempt 1. The guard is commit
"stage_locate box guard". Audit of every result that consumed
`stage_locate` output, re-located from scratch copies of the recorded screens
with the located roots stripped. Nothing recorded is overwritten.

| screen | flagged windows | estimate |
|---|---|---|
| low, [8, 1e4] at 0.85 (`deep_zeros_locate_20261026.json`) | 21 | about 15 s |
| screen_hi, [1e4, 1e5] at 0.85 (`deep_zeros_hi_20261026.json`) | 111 | about 6 min (Run 9's locate took 323 s) |
| 1e6, [1000000, 1001200] at 0.85 (`deep_zeros_1e6.json`) | 1 | about 5 min (head about 2.4e6 terms) |

Total about 0.2 core-hours, three processes, nice 10. The two control screens
(`deep_zeros_control.json`) and `deep_zeros.json` hold no located roots and
are not affected.

### Estimate before spending: re-landing the window at γ = 88167.40 with the fallback

One census window at 8.8e4 under the new accounting fallback: about 8 min
(Run 12 measured 455 s for this window), 0.13 core-hours. The diagnosis so
far is about 3 min. Bounded total for step 3: under 0.25 of the 1 core-hour cap.

## Run 19: the audit under the guard (2026-10-26)

```runmanifest
id: R19-audit-guard
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: completed; low 21 identical, 1e6 identical to 1.3e-13, screen_hi 110 identical and one root replaced (the known one)
ran:
  - deep_zeros.py locate on scratch copies of the low, screen_hi and 1e6 screens (three processes, nice 10)
artifacts:
  - census_runs/audit_u4/guarded_locate.json
```

Low 15 s, screen_hi about 7 min, 1e6 about 5 min: about 0.2 core-hours, as
estimated.

## Run 20: the window at γ = 88167.40 (2026-10-26)

```runmanifest
id: R20-w88167
hunt: lambda_dh_exact
started: 2026-10-26
finished: 2026-10-26
outcome: resolved; a near-line pair at γ 88132.180, β 0.50479 was the 2 unaccounted zeros; with the 0.5005 accounting fallback the window closes and lands at 0.04012
ran:
  - float counts at β > 0.5005, 0.501, 0.502 (65 s)
  - bisection on the 0.502 versus 0.505 counts and a box search (83 s)
  - census_one under the fallback (1060 s)
artifacts:
  - census_runs/audit_u4/w88167_relanded.json
```

About 0.34 core-hours, against the 1 core-hour cap.

## Estimate before spending: the full census, attempt 2 (guarded)

Basis: attempt 1 *measured* 11.05 runner core-hours on the same plan and
code, apart from the guard and the fallback. Additions:
- 8 previously missed candidates at about 250 s each: 0.56;
- guard box searches on about 17 refused roots at about 30 s each: 0.14;
- accounting-fallback windows (one known, 1060 s locally): 0.3.

**About 12.0 core-hours**, under the pre-approved 15, and K-e stops at 30.
Peak RSS: the guard's search grid has the same shape as the census's
off-line search; attempt 1 measured 0.258 GiB, so 4 x peak is about
1.0 GB against 13. Guard tests pass (section 9; all 17 windows in the slow
tier). The smoke row passes locally under the guarded code, landing
0.057665659795901776 exactly as before. All four pre-approved conditions are
met, so no calibrate run is needed: the projection rests on attempt 1's
measured runner cost.
