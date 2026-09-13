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
