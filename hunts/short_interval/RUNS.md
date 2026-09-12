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
LP as a function of bandwidth (`MISSION.md` §6.2). Write the estimate below
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
