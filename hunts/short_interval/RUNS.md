# Runs

Estimates before launch, outcomes after, including runs that produced
nothing. Per `CLAUDE.md`: nothing heavy on the operator's machines, GitHub
Actions is the default compute, and anything over about twenty minutes
checkpoints per unit.

## Compute spent so far

**None worth an estimate.** Everything in `RESULTS.md` is closed-form
evaluation and one 250-node linear solve, all of it sub-second on one core.
No Actions job has been launched for this hunt and no paid compute has been
touched.

The first thing here that will need an estimate is the configuration-ceiling
LP as a function of bandwidth (`MISSION.md` §7). Write the estimate below
before launching it, taken from one rung measured and multiplied, not from a
guess.

```runmanifest
id: short_interval-2026-09-12-open
hunt: short_interval
started: 2026-09-12
finished: 2026-09-12
ran:
  - python3 hunts/short_interval/verify.py
outcome: no mathematics attempted; the run reproduced every constant printed in both source papers and established that this tree's existing bandwidth landscape is Wang's curve to 1e-16, which reframed the hunt's question before any compute was spent
artifacts:
  - hunts/short_interval/MISSION.md
  - hunts/short_interval/RESULTS.md
  - hunts/short_interval/verify.py
```

Exact clock times for that run were not recorded, only the date. Later
manifests should carry them.

## A note on the two withdrawn readings

Two earlier readings were written into this hunt's brief and withdrawn the
same day, both before any compute. They are named in `RESULTS.md` §3 rather
than deleted, because a brief that quietly loses its wrong turns teaches the
next session nothing. Neither cost anything but tokens.

## 2026-09-12, ceiling_theta.py: the estimate, written before any launch

The instrument is `ceiling_theta.py`, the `frontier_math/configuration_lp.py`
LP with the band `[-1, 1]` replaced by `[-theta, theta]` (`MISSION.md` §7).
One unit is one LP solve at one `(X, J)` rung; the ladder per theta is the
six rungs `outband_intake` recorded for the in-band control,
`X = 40, 80, 120, 160, 240, 320` with `J = 200, 320, 480, 640, 960, 1280`
and `eps = 0.4/X`.

**Measured, this container (4 cores, `.venv` numpy 2.4.6, scipy 1.17.1),
2026-09-12T23:04Z to 23:09Z:**

| rung `X` | 40 | 80 | 120 | 160 | 240 | 320 | ladder total |
|---|---|---|---|---|---|---|---|
| `theta = 1.00`, seconds | 0.2 | 1.1 | 4.4 | 10.1 | 44.1 | 194.9 | 255 |
| `theta = 0.55`, seconds | 0.1 | 0.4 | 1.4 | 3.2 | 10.3 | 19.7 | 35 |

The same rungs at `theta = 1` took `0.2, 0.7, 2.8, 6.6, 37.9, 95.1 s` on the
operator's laptop (`hunts/outband_intake/artifacts/lane-a-control-inband.json`
and `lane-a-control-inband-long.json`), so this container is about two times
slower on the largest rung; a GitHub-hosted runner is assumed no slower than
this container, and the cap below carries a further factor of two.

**The estimate.** The row count scales with `theta`, so `theta = 1` is the
worst cell at 255 s and the ten-theta default grid costs at most
`10 x 255 s = 43 CPU-minutes` in total, about 25 minutes if the rows scale
linearly. One theta per job, so the longest job is about 4.5 minutes here and
under 10 minutes with the factor of two, against the 20-minute cap. The
`X = 480` rung is **not** in the default ladder: the last two rungs at
`theta = 1` scale as `X^5.2` (`44.1 -> 194.9 s` for `240 -> 320`), which prices
`X = 480, J = 1920` at about `1590 s`, 26 minutes, over the cap. It can be
passed through the workflow's `rungs` input by whoever wants it and accepts
the job cap. Peak memory at `X = 320, J = 1280` is a `2562 x 5127` dense
constraint matrix, about 105 MB, well inside a runner.

Every rung checkpoints to `artifacts/ceiling-theta-<theta>.json` as it
completes, so a killed job keeps what it paid for.

```runmanifest
id: short_interval-2026-09-12-ceiling-theta-control
hunt: short_interval
started: 2026-09-12T23:04Z
finished: 2026-09-12T23:09Z
ran:
  - .venv/bin/python hunts/short_interval/ceiling_theta.py --control
  - .venv/bin/python hunts/short_interval/ceiling_theta.py --theta 0.55
outcome: the theta-parameterized LP reduces to configuration_lp.solve at theta 1 exactly and reproduces all six recorded in-band rungs to 1e-12, but its extrapolated bandwidth-one value 0.6740762 lands on the Montgomery-Taylor record within the method error (+0.0016) and 0.0078 below the configuration ceiling 0.6818286874638, so this LP is the measure-level dual at every band and cannot measure the configuration ceiling, whose headroom is configuration realizability; at theta 0.55 it descends to 0.0104 at X 320 and extrapolates to 0.0007 against c(0.55) of -0.0006, consistent with zero headroom
artifacts:
  - hunts/short_interval/ceiling_theta.py
  - hunts/short_interval/artifacts/ceiling-theta-1.00.json
  - hunts/short_interval/artifacts/ceiling-theta-0.55.json
  - .github/workflows/hunt-short-interval-ceiling.yml
```

The workflow was written and **not dispatched**. Nothing ran on GitHub Actions
for this hunt, and nothing ran on the operator's machines.
