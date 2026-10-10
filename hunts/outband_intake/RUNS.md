# Runs

## 2026-08-31, price_the_band.py, lanes A and B

**Estimate written before launching.** Two solves were timed first, on this
machine: `X=40, J=200` took 5.7 s and `X=80, J=320` took 40.1 s. That is an
exponent of 2.81 in X, so the remaining rungs price at roughly 123 s
(`X=120`), 276 s (`X=160`) and 866 s (`X=240`).

- Lane A, one pass over five rungs: about 22 minutes. Two passes, out-of-band
  on and the in-band control, about 44 minutes.
- Lane B, seven solves at the fixed `X=80, J=320` grid: about 5 minutes.
- **Total estimate: about 49 minutes**, on the operator's laptop. Peak memory
  at the largest rung is a constraint matrix near 200 MB, which is why the
  ladder stops at `X=240`; anything larger goes to GitHub Actions.

Every solve checkpoints to `artifacts/` as it completes, so an interruption
keeps what it has already paid for.

An earlier claim in conversation that this sweep would take two days was
wrong, and was made before anything was timed. Recorded because the repo's
compute rule exists to stop exactly that.

outcome: lane B measured separately after the first sweep was killed (91% of the gain sits inside alpha in (1, 1.5]); the out-of-band information is worth about +0.0068 at the measure level (class value 0.6793, method error 2.2e-3), and no autocorrelation-kernel certificate can reach it; lane A stopped at X=160 when the X=240 rung exceeded an hour and the sweep was killed there, which is why lane B was run on its own afterwards

## 2026-08-31, the X=240 out-of-band rung, re-run to completion

No new estimate was written; the rung was restarted and left alone, which is
the thing the rule above exists to stop. It finished at **10598 s**, twelve
times the 866 s estimate. The wall times `5.8, 40.4, 428.4, 2069.1, 10597.9 s`
at `X = 40, 80, 120, 160, 240` scale as `X^2.8` only across the first pair; the
later steps run at `X^4` to `X^5.5`, so the first-pair estimate was the wrong
instrument for the rungs that mattered. Value `0.6828907`, checkpointed into
`artifacts/lane-a-convergence.json`. Anything past this goes to CI.

## 2026-09-01, refit.py

Seconds of compute. Re-extrapolates both ladders three ways from the
checkpointed artifacts.

outcome: the earlier class value 0.6793 was one fit among several; the difference route gives 0.6790, the direct out-of-band fit 0.6815, and pinning the exponent moves the difference limit across 0.0027 to 0.0071. RESULTS.md §1 now states the range [0.679, 0.682] and withdraws the coincidence with CGdL's 0.6792

## 2026-10-10, replay of the cheap rows (issue #240)

The three runs above predate this hunt's manifests. They were not re-run in full here,
and no manifest is back-filled for them from their prose: a block written from prose would
look pinned and would not be. The block below records only what was re-run on 2026-10-10,
on a shared four-core Linux container (scipy 1.18.1, numpy 2.5.3), not the operator's
laptop.

- **Re-solved** by `replay.py`, which writes nothing: lane A out-of-band at X = 40 and 80,
  the in-band control at X = 40 to 160, and every recorded lane B reach at X = 80. Eleven
  rows.
- **Exact** (within 1e-9, in fact 2e-13) for the seven rows with reach none, 1.25 or 1.5.
- **Within solver tolerance only** for the four rows with reach 2.0 or 3.0: off by 6.7e-8
  to 2.0e-7. HiGHS stops at 1e-7 feasibility tolerances, and on this host its own three
  methods disagree among themselves by up to 7e-8 on two of those rows, so the gap is the
  solver's, not the model's. It still moves the seventh printed decimal by one unit:
  re-solved 0.6918386, 0.6862543 and 0.6858060 against the recorded 0.6918387, 0.6862544
  and 0.6858061 (RESULTS.md sections 1 and 1b; `docs/35` prints the last two). No gain,
  share or limit moves at the precision RESULTS.md states its conclusions to. The first
  replay ran at the 1e-9 tolerance alone and reported these four rows as mismatches; the
  two-tolerance rule in `replay.py` was written after measuring the method spread.
- **Reproduced from the artifacts, not from re-solves**: `refit.py` prints the 0.6790
  difference limit, the 0.6815 direct fit and the 0.0027 to 0.0071 pinned-exponent range
  stated in the 2026-09-01 entry.
- **Not re-solved, so still unpinned**: the out-of-band rungs at X = 120, 160 and 240
  (recorded at 428 s, 2069 s and 10598 s) and the in-band control at X = 240 and 320
  (`lane-a-control-inband-long.json`). Every extrapolated limit leans on those rungs, so
  the limits rest on the original artifacts alone.

```runmanifest
id: outband_intake-2026-10-10-replay
hunt: outband_intake
started: 2026-10-10T01:27Z
finished: 2026-10-10T01:37Z
ran:
  - .venv/bin/python hunts/outband_intake/replay.py, first at a single 1e-9 tolerance (4 of 11 rows over it), then with the EXACT 1e-9 and SOLVER 1e-6 pair it now carries
  - the X = 40 reach 3.0 and X = 80 reach 2.0 solves under each of scipy's highs, highs-ds and highs-ipm, by a scratch patch of configuration_lp's linprog method that was not kept, to size the solver's own spread
  - .venv/bin/python hunts/outband_intake/refit.py
outcome: 11 cheap rows re-solved, 7 to within 2e-13 and the 4 with reach 2.0 or 3.0 to within 2.0e-7, which moves the seventh printed decimal of three recorded values by one unit and no stated conclusion; refit.py reproduces the 0.6790, 0.6815 and 0.0027 to 0.0071 figures from the artifacts; the out-of-band rungs at X = 120, 160 and 240 and the control at X = 240 and 320 were not re-solved and stay unpinned
artifacts:
  - hunts/outband_intake/replay.py
```
