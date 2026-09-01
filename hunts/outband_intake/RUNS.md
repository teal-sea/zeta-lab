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
