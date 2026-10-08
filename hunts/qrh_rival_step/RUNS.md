# Runs

Every run, including the ones that produced nothing.  Wall times are from a
four-core cloud container, one process per core; nothing ran on the operator's
machines.  Estimates were written before each production run from the
exploration timings below, as `CLAUDE.md` asks.

## 2026-10-08, exploration: deriving the routes and timing them

**Estimate.** None written; these were the unit timings everything else was
priced from.

Scratch scripts (not committed): the Fourier-Bessel expansion was written down,
then checked against `zeta.epstein.epstein_zeta` at twelve points over four
forms and against the direct Dirichlet series at s = 3 (agreement 1e-22 at
twenty digits; the direct sum to |m|, |k| <= 400 agrees to 1.4e-11, its tail).
The genus-character factorization for discriminant -15 was checked against
both at the same points.  Unit costs at fifteen digits: route A 1.6 s per point
at height 12 and 4.4 s at height 30 (forty digits); route B 0.04 s per point;
route C 0.05 s at height 50, 0.13 s at 200, 0.22 s at 400; the Davenport-
Heilbronn function 0.02 to 0.06 s.  Route B on mpmath at fifteen digits drifts
from route C by 0.04 at t = 100 and 0.73 at t = 200, and at thirty digits by
1.6 at t = 200: the cancellation between 1 / Gamma(s) and the K-Bessel factors
costs about 0.7 digits per unit height, the same rate as route A, and mpmath
does not warn.  Route B on python-flint balls with a ball-valued argument of
radius 1e-4 returns a radius of 1e67 at height 15 (the Bessel order is then
inexact), so segment enclosures use route C on balls instead, where a segment
of length 0.006 inflates the radius about 25-fold, like Arb's zeta.
python-flint's `bessel_k` takes the argument as `self` and the order as the
parameter, the reverse of its docstring; the probe calibrates this at first
use against mpmath.  The exact Dirichlet inverse of the representation numbers
costs 0.75 s to 10^6 by sieve.

A sixty-unit scan of three functions in ten-unit windows took 6 m 49 s on one
core and found: discriminant -15, one zero beyond 7/8 in each of [10.5, 20.5]
and [40.5, 50.5], none beyond 1; discriminant -23, one beyond 7/8 in
[10.5, 20.5], none beyond 1; Davenport-Heilbronn, none beyond 7/8 below 60.

```runmanifest
id: qrh_rival_step-2026-10-08-exploration
hunt: qrh_rival_step
started: 2026-10-08T00:30Z
finished: 2026-10-08T01:40Z
ran:
  - scratch scripts deriving and timing routes A, B, C and the ball routes (not committed; every check they made is repeated in probe.py and test_rival_step.py)
outcome: the Fourier-Bessel constants match the lattice route to 1e-22; route B on mpmath loses accuracy above height 100 and route B on ball-valued arguments is unusable; route C is cheap at every height tried; three rival zeros beyond 7/8 and none beyond 1 were seen below height 60
artifacts:
```

## 2026-10-08, smoke tests of each probe subcommand

**Estimate.** From the unit costs: one census window about 10 s plus 10 s to
locate, controls about 20 s, the Davenport-Heilbronn census 3 s per window,
the inverse 2 s.  Measured: 16 s, 19 s, 6 s (two windows), 1.5 s.

```runmanifest
id: qrh_rival_step-2026-10-08-smoke
hunt: qrh_rival_step
started: 2026-10-08T01:45Z
finished: 2026-10-08T02:10Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route c15 --t0 10.5 --t1 20.5 --locate --out <scratch>
  - .venv/bin/python hunts/qrh_rival_step/probe.py controls --h1-t-max 10.5 --out <scratch>
  - .venv/bin/python hunts/qrh_rival_step/probe.py dh --t-max 20 --out <scratch>
  - .venv/bin/python hunts/qrh_rival_step/probe.py inverse --form d15 --nmax 100000 --zeros <scratch census> --out <scratch>
outcome: the first zero beyond 7/8 of the discriminant -15 rival was located at 0.92746088 + 15.49663407i with mpmath winding 1; the zeta control recovered gamma_1 to 2e-16; the h = 1 control saw nothing; the inverse coefficients were non-multiplicative with maximum 5136 below 10^5
artifacts:
```

## 2026-10-08, two null runs: the segment-ball winding as first written

**What happened.** The first ball winding summed the arguments of the segment
balls themselves.  Those radii do not shrink in aggregate under subdivision
(the sum of per-segment uncertainties scales with perimeter times inflation
over |f|, not with the segment count), so the winding ball at 1024 segments
was [-89, 91] on the zeta control, and on the rival the route B segment balls
never excluded zero at all.  Two `confirm` runs cycled through every
subdivision and precision level without deciding anything and were stopped by
hand after about eleven and ten minutes.  The repair, in the committed probe:
segment balls are used only to exclude zero along each segment (which bounds
the increment below pi), the increments come from tight point balls at the
segment endpoints, and the segment enclosures use route C on balls.  After the
repair the zeta control decides winding 1 with a ball of width 1e-73 at 256
segments, and the displaced square decides 0.

```runmanifest
id: qrh_rival_step-2026-10-08-null-segment-balls
hunt: qrh_rival_step
started: 2026-10-08T02:10Z
finished: 2026-10-08T02:45Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py confirm --census <scratch census> --form d15 --out <scratch>  (first winding scheme, stopped after about 11 minutes)
  - .venv/bin/python hunts/qrh_rival_step/probe.py confirm --census <scratch census> --form d15 --out <scratch>  (same scheme with more subdivision, stopped after about 10 minutes)
outcome: nothing was decided; the scheme summed segment-ball arguments, whose aggregate width does not shrink under subdivision, and was replaced
artifacts:
```

## 2026-10-08, a null run: the strip census crashed on a clustered window

The window [10.5, 20.5] of the strip [0.55, 1.6] holds three zeros; the first
grid seed did not converge under the secant solver and the run died.  The
locator now tries up to eight seeds in order of residual with secant then
Muller, verifies the residual, and a window whose zeros it cannot locate is
recorded as such rather than killing the census.

```runmanifest
id: qrh_rival_step-2026-10-08-null-strip-crash
hunt: qrh_rival_step
started: 2026-10-08T02:50Z
finished: 2026-10-08T02:51Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route c15 --re-lo 0.55 --re-hi 1.6 --t0 0.5 --t1 60.5 --locate --out hunts/qrh_rival_step/results_census_d15_strip.json
outcome: ValueError from findroot in the window [10.5, 20.5]; no file written; locator made robust and the run repeated below
artifacts:
```

## 2026-10-08, production: four censuses, two confirmations, the controls, the inverse

**Estimates written before launch**, from the exploration unit costs.  Route C
window counts at 8 s (height 15) growing to about 60 s (height 300): the
D = -15 census to 300.5 priced at 25 to 35 minutes plus about 30 s per
located zero; the Re s > 1 count the same without locating; the strip census
to 60.5 at 2 minutes plus locating; the D = -23 census on route B at 2
minutes; the Davenport-Heilbronn census at 3 to 6 minutes; the controls at 3
minutes; the inverse at a few seconds.  One process per core, four cores.
Nothing checkpoints: no unit exceeds twenty minutes, and every window's
count is printed as it lands, so a killed run keeps its log.

**Measured.**  D = -15 census to 300.5: 1622 s, windows from 7.7 s at height
15 to 66 s at height 300, twelve zeros counted and twelve located, one
relocated (next entry).  Re s > 1 count: 1279 s, two zeros.  Strip census
[0.55, 1.6] to 60.5: 115 s, six zeros located.  D = -23 census to 60.5 on
route B: 103 s, one zero; its confirmation 12 s (route A at 36 digits took
7 s).  Davenport-Heilbronn census to 300: 367 s, thirty empty windows.
Controls: 122 s.  Inverse to 10^6: 5.6 s (run twice, the second time with the
relocated zero in the explicit-formula sum).  Half-step recount of the top
window: 433 s for the four counts.  Total production compute about 68 CPU
minutes, over the brief's budget by the two D = -15 censuses, which the
coordinator capped at twenty more minutes while they were in their last
windows; both exited inside the cap.

```runmanifest
id: qrh_rival_step-2026-10-08-census-d15
hunt: qrh_rival_step
started: 2026-10-08T03:40Z
finished: 2026-10-08T04:07Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route c15 --re-lo 0.8751 --re-hi 1.6 --t0 0.5 --t1 300.5 --win 10 --dps 15 --locate --locate-dps 20 --out hunts/qrh_rival_step/results_census_d15.json
outcome: twelve zeros of the discriminant -15 Epstein zeta function in [0.8751, 1.6] x [0.5, 300.5], all located with mpmath winding 1, two with Re s > 1 (1.02597 at height 61.42 and 1.02677 at height 246.99), largest real part 1.026775
artifacts:
  - hunts/qrh_rival_step/results_census_d15.json
```

```runmanifest
id: qrh_rival_step-2026-10-08-census-d15-re1
hunt: qrh_rival_step
started: 2026-10-08T03:40Z
finished: 2026-10-08T04:01Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route c15 --re-lo 1.0003 --re-hi 1.6 --t0 0.5 --t1 300.5 --win 10 --dps 15 --out hunts/qrh_rival_step/results_census_d15_re1.json
outcome: two zeros with Re s > 1.0003 below height 300.5, in the windows [60.5, 70.5] and [240.5, 250.5], the same windows as the located zeros past 1
artifacts:
  - hunts/qrh_rival_step/results_census_d15_re1.json
```

```runmanifest
id: qrh_rival_step-2026-10-08-census-d15-strip-and-d23
hunt: qrh_rival_step
started: 2026-10-08T03:42Z
finished: 2026-10-08T03:46Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route c15 --re-lo 0.55 --re-hi 1.6 --t0 0.5 --t1 60.5 --win 10 --dps 15 --locate --locate-dps 20 --out hunts/qrh_rival_step/results_census_d15_strip.json
  - .venv/bin/python hunts/qrh_rival_step/probe.py census --route b:d23 --re-lo 0.8751 --re-hi 1.5 --t0 0.5 --t1 60.5 --win 10 --dps 15 --locate --locate-dps 20 --out hunts/qrh_rival_step/results_census_d23.json
  - .venv/bin/python hunts/qrh_rival_step/probe.py confirm --census hunts/qrh_rival_step/results_census_d23.json --form d23 --dps 30 --out hunts/qrh_rival_step/results_confirm_d23.json
outcome: six off-line zeros of the discriminant -15 function in the strip [0.55, 1.6] below height 60.5, two of them beyond 7/8; one zero of the discriminant -23 function beyond 7/8 below 60.5, at 0.95326047 + 16.29021572i, with routes A and B both at 3.6e-41 and a point winding of 1 on route B balls
artifacts:
  - hunts/qrh_rival_step/results_census_d15_strip.json
  - hunts/qrh_rival_step/results_census_d23.json
  - hunts/qrh_rival_step/results_confirm_d23.json
```

```runmanifest
id: qrh_rival_step-2026-10-08-dh-and-controls
hunt: qrh_rival_step
started: 2026-10-08T03:42Z
finished: 2026-10-08T03:51Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py dh --t-max 300 --out hunts/qrh_rival_step/results_dh.json
  - .venv/bin/python hunts/qrh_rival_step/probe.py controls --h1-t-max 60.5 --out hunts/qrh_rival_step/results_controls.json
outcome: no Davenport-Heilbronn zero with Re s > 7/8 below height 300, the pinned zero at 0.80852 and the deepest census pair at 0.86953 both below 7/8; the zeta control recovers gamma_1 to 2e-16 with ball winding 1 and 0 on the displaced square; the class-number-one form shows no zero in the same box below 60.5 and its inverse is multiplicative and bounded by the divisor function; planted faults are detected
artifacts:
  - hunts/qrh_rival_step/results_dh.json
  - hunts/qrh_rival_step/results_controls.json
```

```runmanifest
id: qrh_rival_step-2026-10-08-halfstep
hunt: qrh_rival_step
started: 2026-10-08T03:47Z
finished: 2026-10-08T03:55Z
ran:
  - scratch script calling zeta.epstein.count_zeros_box on [0.8751, 1.6] x [290.5, 300.5] and [1.0003, 1.6] x [290.5, 300.5] with the default forced step and with half of it, route C at fifteen digits
outcome: the counts agree at both step sizes, 2 and 2 beyond 7/8, 0 and 0 beyond 1, so the forced subdivision is not aliasing a turn at height 300
artifacts:
  - hunts/qrh_rival_step/results_halfstep.json
```

## 2026-10-08, one relocation: the window [200.5, 210.5]

The locator's first version accepted any converged root; in this window the
best grid seed converged to a zero at 0.78259 + 201.056i, which is a zero of
the function but outside the box (Re s < 0.8751), so the box's own zero was
unlocated and the census file said so (`inside_window: false`).  The locator
now rejects roots outside its box and keeps trying seeds.  The window was
re-located with the repaired locator (40 s), landing at
0.90705464 + 205.69694327i inside the box with |f| = 3.2e-24 and mpmath
winding 1, and the census file was patched in place with the old root
recorded in the entry's `relocated` field.  The inverse analysis was re-run
afterwards so its explicit-formula sum used the in-box zero.

```runmanifest
id: qrh_rival_step-2026-10-08-relocate-205
hunt: qrh_rival_step
started: 2026-10-08T04:09Z
finished: 2026-10-08T04:10Z
ran:
  - scratch script calling probe.locate_zeros on [0.8751, 1.6] x [200.5, 210.5] with the in-box filter and patching results_census_d15.json
  - .venv/bin/python hunts/qrh_rival_step/probe.py inverse --form d15 --nmax 1000000 --zeros hunts/qrh_rival_step/results_census_d15_strip.json hunts/qrh_rival_step/results_census_d15.json --out hunts/qrh_rival_step/results_inverse_d15.json
outcome: the box's zero in [200.5, 210.5] is 0.90705464 + 205.69694327i; the inverse coefficients to 10^6 have maximum 39504, 460 multiplicativity failures in 3406 coprime pairs, envelope exponent 0.886, and the sixteen located zeros explain half the rms of the partial sums over the top decade
artifacts:
  - hunts/qrh_rival_step/results_census_d15.json
  - hunts/qrh_rival_step/results_inverse_d15.json
```

## 2026-10-08, hardening the twelve D = -15 zeros

**Estimate.**  Route B on mpmath needs about 0.8 digits per unit height and
the route B ball point winding costs 256 points times about 190 Bessel terms
at 2600 bits near height 300, about forty minutes a zero, so both were
restricted to zeros below height 100 before the run; the route C polish,
the route C ball winding and one route B ball evaluation at the root were
priced at under a minute per zero.  A first launch on the pre-relocation
census file was stopped after two minutes and relaunched on the patched one.

**Measured.**  170 s for all twelve zeros on one core.

```runmanifest
id: qrh_rival_step-2026-10-08-confirm-d15
hunt: qrh_rival_step
started: 2026-10-08T04:10Z
finished: 2026-10-08T04:13Z
ran:
  - .venv/bin/python hunts/qrh_rival_step/probe.py confirm --census hunts/qrh_rival_step/results_census_d15.json --form d15 --dps 30 --route-a-max-t 100 --out hunts/qrh_rival_step/results_confirm_d15.json
  - .venv/bin/python hunts/qrh_rival_step/probe.py assemble --inputs <the ten results_*.json files> --out hunts/qrh_rival_step/results.json
outcome: every one of the twelve zeros has a segment-enclosed ball winding of 1 on route C (0 on the displaced square) and overlapping ball values on routes B and C at the root; the three zeros below height 100 agree between routes B and C to 3e-40 with route A vanishing to 3e-41 and point windings of 1 on route B balls; the twelve-digit roots give ball values at most 1.2e-9
artifacts:
  - hunts/qrh_rival_step/results_confirm_d15.json
  - hunts/qrh_rival_step/results.json
```
