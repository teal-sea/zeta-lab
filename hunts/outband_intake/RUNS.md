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

outcome: lane B measured on the second attempt (91% of the gain sits inside alpha in (1, 1.5]); the out-of-band information is worth about +0.0068 at the measure level (class value 0.6793, method error 2.2e-3), and no autocorrelation-kernel certificate can reach it; lane A stopped at X=160 when the X=240 rung exceeded an hour, lane B never ran
