# RUNS

Every run of this hunt, including the ones whose output was not kept. All runs so far
were local and single-core: phase 0 is light by the MISSION's own estimate, and the
timing below confirmed it before the sweep.

## Unit timing, taken before the sweep (2026-10-18, worktree `.venv`, Python 3.14.0, mpmath 1.3.0)

| unit | time |
| --- | --- |
| route A, one block of 64 moments by the shared-grid trapezoid, dps 60, k = 49..112 / 800..863 / 3142..3205 | 0.04 / 0.03 / 0.03 s |
| check route, one moment by tanh-sinh over `zeta.core.omega`, dps 80, k = 49 / 3205 | 0.67 / 1.64 s |
| route B, saddle expansion to order 9 with M = 6 corrections, n = 3200, dps 60 | 0.93 s |

Estimate written before the sweep: route A over k = 49..3205 is 50 blocks, about 2 s; the
check route over the 147 indices of the 21 subgrid windows, about 3 to 4 min at the unit
times (the trial had measured 488 s for the same indices, the mid-range k being slower
than either end); route B at 21 points with its ladder, about 1 min; the dense model fits
at 3151 n, under 1 min; the large-n table, about 1 min. Total about 10 min. Measured:
521 s, 442 s and 516 s for the three recorded runs, of which about 404 s each time was
the check route.

`results.json` records `git_head` as the base commit `7c97b34`: the recorded run used the
working tree that the phase 0 commit lands, which differs from it only in the probe's
module docstring, edited after the run to describe the final error rule.

An earlier per-index tanh-sinh version of route A timed at 2.36 s per moment at k = 3205
(about 2 h for the dense range) and was replaced by the shared-grid trapezoid before any
sweep ran; the tanh-sinh code survives as the check route.

```runmanifest
id: jensen_wedge-2026-10-18-trial
hunt: jensen_wedge
started: 2026-10-18T21:46-05:00
finished: 2026-10-18T21:56-05:00
ran:
  - /Users/thomas/Zeta/.venv/bin/python hunts/jensen_wedge/probe.py --out <session scratchpad>/trial.json
outcome: both sign facts held at every n from 50 to 3200 and route B agreed in sign at all 21 subgrid points, but the preset route-B error rule (M = 4, Laplace part |M4 - M3|) missed at n = 150 and every theta = 1 finite-free solve failed, so the probe was revised before the recorded run; this run used the main checkout's interpreter (same Python 3.14.0 and mpmath 1.3.0) while the worktree venv was still installing, and its JSON was not kept
artifacts:
```

```runmanifest
id: jensen_wedge-2026-10-18-phase0-a
hunt: jensen_wedge
started: 2026-10-18T21:59-05:00
finished: 2026-10-18T22:08-05:00
ran:
  - .venv/bin/python hunts/jensen_wedge/probe.py --time-unit
  - .venv/bin/python hunts/jensen_wedge/probe.py
outcome: every verdict flag passed with route B at M = 6 and the preset M = 4 rule's miss at n = 150 recorded; the theta grid bracketed the R_5 sign crossing at n = 100, 1600 and 3200 but not at n = 400, where the walk failed at theta = 0.9 before the crossing, so the grid was refined and the probe re-run; this JSON was superseded by the next run and not kept
artifacts:
```

```runmanifest
id: jensen_wedge-2026-10-18-phase0-b
hunt: jensen_wedge
started: 2026-10-18T22:08-05:00
finished: 2026-10-18T22:16-05:00
ran:
  - .venv/bin/python hunts/jensen_wedge/probe.py
outcome: with the refined theta grid the walk found the crossings at n = 100, 400 and 3200 but now stalled at theta = 0.86 for n = 1600, where the coarser grid had passed 0.9, which showed the stalls were partly the fixed-step Newton solver's; the solver was moved to log variables with adaptive steps and the probe re-run; this JSON was superseded and not kept
artifacts:
```

```runmanifest
id: jensen_wedge-2026-10-18-phase0-c
hunt: jensen_wedge
started: 2026-10-18T22:17-05:00
finished: 2026-10-18T22:26-05:00
ran:
  - .venv/bin/python hunts/jensen_wedge/probe.py
outcome: the recorded run, 516 s; Laguerre defect at R_3 positive and Jacobi defect at R_4 negative at all 3151 n in 50..3200 on route A with no sign change, route B in sign agreement and within its stated error at all 21 subgrid points, the preset M = 4 rule's miss at n = 150 kept, Holland's constants approached to n = 1e20, and the R_5 defect negative at D = B_J/2 everywhere measured with a sign crossing in theta found at all four theta rows
artifacts:
  - hunts/jensen_wedge/results.json
  - hunts/jensen_wedge/RESULTS.md
```
