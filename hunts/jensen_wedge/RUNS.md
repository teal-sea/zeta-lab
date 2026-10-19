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
  - <main checkout>/.venv/bin/python hunts/jensen_wedge/probe.py --out <session scratchpad>/trial.json
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

## Phase 1: unit timing, taken before the sweep (2026-10-18, worktree `.venv`, Python 3.14.0, mpmath 1.3.0, numpy 2.x)

| unit (`probe_phase1.py --time-unit`) | time |
| --- | --- |
| route A, one block of 64 moments, dps 60, k = 3233..3296 | 0.07 s |
| the four-parameter Pade solve (A, B, C, D) at n = 3200, dps 75 | 0.02 s |
| one theta walk of the D-fixed family, 0.5 to 0.85, n = 3200 | 0.04 s |
| route B by direct saddle evaluation, log R_0..R_6, n = 1e4 / 1e20 | 0.05 / 0.08 s |
| the leading-order three-factor scan on a 150 + 40 grid, eps = 0.01 | 0.79 s |

Estimate written before the trial: route A over k = 49..3296 is 51 blocks, about 4 s; the
check route at 26 indices, about 1 to 1.5 min at phase 0's per-moment times; the theta map
at 21 values of n, a few seconds each; the dense Pade solve at 3151 values of n, about
1 min; route B at 6 subgrid points and 8 large n, a few minutes; the three-factor scans on
the full 500 + 120 grid, (620/190)^2 x 0.8 s, about 9 s per eps and 1 min for six; root
geometry at n = 3200 for d up to 96, not timed in advance (the degree-96 evaluations were
the unknown). Total about 8 to 12 min.

```runmanifest
id: jensen_wedge-2026-10-18-phase1-trial
hunt: jensen_wedge
started: 2026-10-18T23:10-05:00
finished: 2026-10-18T23:24-05:00
ran:
  - .venv/bin/python hunts/jensen_wedge/probe_phase1.py --out <session scratchpad>/trial1.json
outcome: run after the unit timing above; stopped by hand in the large-n stage after 14 min, so no JSON was written; its log showed route A and its check route agreeing to 5.2e-75, theta_star equal to phase 0's crossings to 12 digits, E_S6 negative at all 3151 n, and route B agreeing with route A on E_S6 to relative 2e-18..2e-22, and it exposed three defects that were fixed before the recorded run: the theta grid (0.85, 0.9, 0.95) stepped over theta_inf into the B = infinity wall at n = 50..70 and n >= 500, and the fixed large-n grid did the same from n = 1e8, so the grids were refined (0.01 steps above 0.8, and a grid in units of 1/L at large n); in a side check of the root-geometry code the scale S was built at 15 digits, which polluted c_j at 1e-14; and the Jensen polynomial at d = 48 showed 6 complex pairs that a precision sweep traced to cancellation (about 77 digits lost in the monomial basis, against about 70 carried), so the root-geometry part got its own dps-260 route A block and dps 60 + 2d evaluation
artifacts:
```

Measured: 400 s for the recorded run (check route 85 s, theta map 48 s, route B 45 s,
leading-order model 48 s, root geometry 116 s, the rest the dense Pade solve and the
validations). `results_phase1.json` records `git_head` as the base commit `5d34ddb`: the
run used the working tree that the phase 1 commit lands, before it was committed.

```runmanifest
id: jensen_wedge-2026-10-18-phase1-a
hunt: jensen_wedge
started: 2026-10-18T23:24-05:00
finished: 2026-10-18T23:32-05:00
ran:
  - .venv/bin/python hunts/jensen_wedge/probe_phase1.py --time-unit
  - .venv/bin/python hunts/jensen_wedge/probe_phase1.py
outcome: the recorded run, 400 s; route A to k = 3296 agrees with its check route to 5.2e-75 and with zeta/li.py's tables; theta_star and theta_inf found at all 21 subgrid n and all 8 large n with no failed walk, theta_star equal to phase 0's crossings to 12 digits; the Pade model solved at every n = 50..3200 with all parameters positive and its R_6 defect negative at all 3151 n and at every large n, n^5 L E_S(6) = -1.872 at 1e20; route B agrees with route A on E_S(6) to relative 1.8e-22 at n = 3200; the three-factor scan found admissible configurations at all six eps; every model and Jensen polynomial at n = 3200, d <= 96 has all roots real
artifacts:
  - hunts/jensen_wedge/results_phase1.json
  - hunts/jensen_wedge/RESULTS.md
