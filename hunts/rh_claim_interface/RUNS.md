# Run record (hunt #161)

## Baseline

Checkout `/home/user/zeta-lab` at `c6fbf9fb`, nothing committed by this hunt.
`zeta.rigor.BACKEND` is `python-flint` (backends `['mpmath.iv', 'python-flint']`),
python-flint 0.9.0. Four cores and 15 GB, three cores held by another job for
the hour: every run below is one process. Peak memory, measured by `ru_maxrss`
on repeat runs: 1.88 GB for the float scan (blocks of `2^24` integers) and
1.53 GB for the rival stage at `n <= 10^7`, both under the 3 GB limit. The
repeat of the rival stage reproduced `rivals.json` exactly apart from the
elapsed time.

`SCRATCH` below is this session's scratch directory for the hunt. It holds the
zero table, the scan checkpoints and the logs, and is not committed. The zero
table is identified by its sha256 in `zeros.json`.

All times are UTC on 2026-11-20. Total heavy computation: about 13 CPU-minutes
of the 45 allowed in the first round, and under 3 more in the review round.

## Unit timings and estimates of the first round

A correction from the review round. This heading used to read "Unit timings
and estimates, written before the scaled runs". That is not evidenced. Only
the scan units have a manifest and a log line. The other units below were
timed by hand between the chained runs and left no log, the chains ran back to
back (`SCRATCH/log_chain1.txt`: explicit, enclose, three character stages,
lesion and decoy from 17:01:30 to 17:07:18 with no gap), and this file was
written at 17:26, after every run of the first round. Read the estimates below
as recollection, not as a record made in advance. Three stages had no unit at
all: `lseries` (no estimate; measured 46.4 s), `decoy` (no estimate; measured
1.3 s) and `lesion` (estimated from its parts, as stated below). None of this
put the budget at risk: the longest run was 147.9 s. The review-round runs
further down were estimated in a time-stamped log line before they started.

**Float scan.** Units: `2 <= n <= 10^7` in 1.4 s, `10^8` in 13.1 s (the second
is the timed unit). The cost per integer rises slowly with the sieve. Estimate
for `10^9`: 140 to 170 s, well under the 20 CPU-minute limit set for going to
`10^9`, so it was run. Measured: 130.1 s. The scan checkpoints after every
block of `2^24` integers (about 2 s) and resumes from the checkpoint file.

**Zero table.** Units: 5000 zeros from index 1 in 16.6 s; 2000 zeros from index
50001 in 14.9 s; 1000 from index 100001 in 6.5 s (64 bits). A table of 10^5
would cost about 10 minutes, too much of the budget. Estimate for 20000: about
100 s. Measured: 147.9 s. The estimate was low: the cost per zero grows with
the index and the machine was loaded. Checkpointed per 2000 zeros.

**Arb prefix sums.** Unit: 2 * 10^5 iterations of log, divide and two
additions at 128 bits in 0.115 s, so 0.57 microseconds per prime. There are
5.08 * 10^7 primes below 10^9. Estimate for one pass: 30 to 60 s. Measured:
41.7 s for two passes (128 and 192 bits) with all the per-decade evaluations.

**Level scan.** Unit: conductor at most 8, `n <= 10^5`, 21 combinations, 0.1 s.
Scaling by 100 in `n` and by 114/21 in combinations: estimate 55 to 60 s for
conductor at most 20 at `10^7`. Measured: 93.1 s (the extended-precision
running sums dominate at this size). The extension to conductor 30 was run at
`10^6` (11.0 s) and not at `10^7` (estimated 4 minutes).

**Character zeros.** Unit: five characters to height 60 on a 0.05 grid in
5.8 s. Estimate for 26 characters to height 80 on a 0.04 grid: about 70 s.
Measured: 89.2 s.

**Rivals.** Unit at `n <= 10^5`: 6.7 s, mostly the fixed cost of the constants.
The recursion is `n log n`. Estimate at `10^7`: under two minutes. Measured:
30.7 s.

**Lesion.** No separate unit: the prime-side part is a scan to `10^7` with 16
lesions (estimated 20 s), the model part 3.3 * 10^5 grid points against 2000
zeros (estimated 10 s). Measured: 37.3 s, then 24.0 s on one thread.

## A deviation, recorded

The first lesion run (17:06:40) used numpy's matrix product for the zero sums
and the BLAS library took more than one core for about half a minute (117
percent in `ps`). Every run from 17:08:46 on had `OMP_NUM_THREADS=1`,
`OPENBLAS_NUM_THREADS=1` and `MKL_NUM_THREADS=1` set. The first explicit-formula
run (17:01:30) used the same product and may have done the same.

Two stages were run twice. The lesion stage was rerun after the envelope
detector on the prime side was changed to read from `n >= 10`, to match the
model grid; the first run had read it from `n = 2`, which made the two columns
incomparable for `gamma0 = 10`. The rival stage was rerun after the
demodulation window was changed from a rectangle to a Hann window in `log n`:
with the rectangle, frequencies 0.75 away gave nearly the same amplitude, so
the first version of the control could not fail. The committed JSON is from
the second runs.

## Run manifests

```runmanifest
id: rh_claim_interface-2026-11-20-scan-units
hunt: rh_claim_interface
started: 2026-11-20T16:54:43+00:00
finished: 2026-11-20T16:55:01+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan scan SCRATCH 1e7
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan scan SCRATCH 1e8
outcome: unit timings 1.4 s and 13.1 s; F stays between -0.0227 and 0.0247 on the integers from 2 to 10^8; the two unit files were superseded by the 10^9 run and are not kept
artifacts:
```

```runmanifest
id: rh_claim_interface-2026-11-20-scan-1e9
hunt: rh_claim_interface
started: 2026-11-20T16:55:08+00:00
finished: 2026-11-20T16:57:19+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan scan SCRATCH 1e9
outcome: every integer from 2 to 10^9 scanned in 130.1 s on one core; maximum of F 0.024694 near 34186454, minimum -0.022681 at 319439, both inside plus or minus c0 = 0.046191
artifacts:
  - hunts/rh_claim_interface/scan_1e9.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-zeros
hunt: rh_claim_interface
started: 2026-11-20T16:57:19+00:00
finished: 2026-11-20T16:59:47+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan zeros SCRATCH 20000
outcome: 20000 zeros to height 18046.46 in 147.9 s; c0 minus the partial sum is 1.580858e-04 against 1.580895e-04 from the zero density
artifacts:
  - hunts/rh_claim_interface/zeros.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-explicit-and-enclosures
hunt: rh_claim_interface
started: 2026-11-20T17:01:30+00:00
finished: 2026-11-20T17:02:48+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan explicit SCRATCH
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan enclose SCRATCH 1e9
outcome: the explicit formula holds within 0.082 of the exact tail budget at 255 points with y > 1 (the 256th, y = 1, cannot fail); Arb values at the 18 decade extremes agree with the float scan to 4.0e-12; in this run only the 9 minima were repeated at 192 bits, and the first version of this line said all 18 were, which the review-round rerun below makes true
artifacts:
  - hunts/rh_claim_interface/explicit_zeta.json
  - hunts/rh_claim_interface/scan_1e9_enclosed.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-characters
hunt: rh_claim_interface
started: 2026-11-20T17:02:48+00:00
finished: 2026-11-20T17:06:40+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_characters lseries 20
  - .venv/bin/python -m hunts.rh_claim_interface.run_characters explicit 12 80
  - .venv/bin/python -m hunts.rh_claim_interface.run_characters levels 20 1e7
outcome: three routes for L'/L(1,chi) agree for 79 characters; the character formula holds within 0.132 of its budget for 26 characters; 35 levels stay within 0.7180 of the GRH envelope and one character reaches 0.9463 because of a zero at height -0.019
artifacts:
  - hunts/rh_claim_interface/lseries.json
  - hunts/rh_claim_interface/explicit_chi.json
  - hunts/rh_claim_interface/levels_q20_y7.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-lesion-decoy-first
hunt: rh_claim_interface
started: 2026-11-20T17:06:40+00:00
finished: 2026-11-20T17:07:18+00:00
ran:
  - .venv/bin/python -m hunts.rh_claim_interface.run_lesion lesion SCRATCH
  - .venv/bin/python -m hunts.rh_claim_interface.run_lesion decoy
outcome: lesion run superseded (envelope detector read from n = 2 on one side and from y = 10 on the other, and BLAS used more than one core); the decoy file is from this run and shows the Cramer set at 40.8 or more against c0 = 0.0462
artifacts:
  - hunts/rh_claim_interface/decoy.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-rivals-first-and-reruns
hunt: rh_claim_interface
started: 2026-11-20T17:08:46+00:00
finished: 2026-11-20T17:10:20+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_rivals 1e7
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_lesion lesion SCRATCH
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_scan explicit SCRATCH
outcome: rival run superseded (rectangular demodulation window, control could not fail); lesion rerun gives 25 of 48 cases with onset below 10^30, all with a violation in every window from onset to the power two thirds; explicit rerun identical apart from one added field
artifacts:
  - hunts/rh_claim_interface/lesion.json
  - hunts/rh_claim_interface/explicit_zeta.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-rivals-and-wide-levels
hunt: rh_claim_interface
started: 2026-11-20T17:10:52+00:00
finished: 2026-11-20T17:11:37+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_rivals 1e7
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_characters levels 30 1e6
outcome: demodulated exponents 0.806 to 0.808 for Davenport-Heilbronn and 0.943 to 0.955 for Epstein (1,1,6) against recorded zeros at 0.80852 and 0.95326; 56 levels of conductor at most 30 stay within 0.6983 of the envelope up to 10^6
artifacts:
  - hunts/rh_claim_interface/rivals.json
  - hunts/rh_claim_interface/levels_q30_y6.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-repeats-and-tests
hunt: rh_claim_interface
started: 2026-11-20T17:20:18+00:00
finished: 2026-11-20T17:25:14+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_rivals 1e7 (repeat, for ru_maxrss)
  - .venv/bin/python -m hunts.rh_claim_interface.run_scan scan SCRATCH 1e8 (repeat, for ru_maxrss; its output file was removed)
  - .venv/bin/python -m hunts.rh_claim_interface.run_characters lseries 20 (repeat after a scoped mpmath precision replaced a global one)
  - .venv/bin/python -m pytest -q -n0 hunts/rh_claim_interface
  - .venv/bin/python -m pytest -q -n0 tests/test_hunt_probe_discipline.py tests/test_huntspec.py
outcome: both repeats reproduced their JSON exactly apart from the elapsed time; the hunt's 25 tests pass in 8 s; of the 23 repository tests named, 22 pass and the case-log coverage test fails because hunts/README.md has no entry yet for this directory or for three other directories opened in the same session
artifacts:
  - hunts/rh_claim_interface/rivals.json
  - hunts/rh_claim_interface/lseries.json
```

## Review round (after two independent reviews)

Estimates, written to `SCRATCH/log_review_round.txt` at 18:07:06, before any
run of this round:

- **Enclosure rerun** (maxima at the second precision too). Unit: the first
  enclosure run, 41.7 s for two passes. The change adds 27 evaluations and no
  pass. Estimate: 40 to 60 s. Measured: 43.0 s.
- **Rival rerun** at `10^7` with the onset attribution and the battery record.
  Unit: the three earlier runs, 30.4 to 38.1 s; the additions timed in scratch
  at 0.7 s and 0.2 s. Estimate: 35 to 50 s. Measured: 46.5 s, then 54.1 s for
  the second run. The second is above the estimate; the machine load was near
  3 throughout.
- **Frontier stage.** Reads the cached zero table. Estimate: under 2 s.
  Measured: under 0.1 s.
- **Lesion reach check** (three plants on the prime side to `10^7`). Timed in
  scratch: 2.6 s for all three. It now runs inside the test suite.

Two faults of this round, recorded. The first rival rerun (18:09:49) had a
wrong bound in the new battery claim: it compared `|Lambda_f(p^k)|` with `p`
instead of `log p`, so the shifted product came out as passing while its
recorded `Lambda_f(2)/log 2` was 2.03. The bound was fixed and the stage rerun
(18:10:53); the committed `rivals.json` is from the second run, and the first
output is kept in `SCRATCH/rivals_review_first_buggy_type_claim.json`. The
frontier stage was run twice (18:09:17 and 18:16:23); the second run added the
block of sources and changed no number.

Both reruns reproduced every field of the first round exactly, apart from the
elapsed time and the new fields (compared key by key against copies taken
before the round, `SCRATCH/scan_1e9_enclosed_before_review.json` and
`SCRATCH/rivals_before_review.json`).

```runmanifest
id: rh_claim_interface-2026-11-20-review-enclosures
hunt: rh_claim_interface
started: 2026-11-20T18:07:33+00:00
finished: 2026-11-20T18:08:16+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_scan enclose SCRATCH 1e9
outcome: all 36 per-decade values (minimum, integer maximum, interior maximum, maximum of G over sqrt n) enclosed at 128 and at 192 bits in 43.0 s; the two enclosures overlap everywhere and Arb decides that F is inside plus or minus c0 at all 27 values of F at both precisions; every field of the first run reproduced
artifacts:
  - hunts/rh_claim_interface/scan_1e9_enclosed.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-review-rivals
hunt: rh_claim_interface
started: 2026-11-20T18:09:49+00:00
finished: 2026-11-20T18:11:48+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_rivals 1e7 (superseded, wrong bound in the battery claim)
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_rivals 1e7
outcome: the standing battery on the type claim gives zeta true, Davenport-Heilbronn, Epstein (1,1,6) and the shifted product false, Epstein (2,1,3) undefined; with the recorded quadruple subtracted the Epstein function still breaks the bound at theta 0.5 (first at 89) and no longer breaks it at 0.55 or 0.6; every field of the first round reproduced
artifacts:
  - hunts/rh_claim_interface/rivals.json
```

```runmanifest
id: rh_claim_interface-2026-11-20-review-frontier
hunt: rh_claim_interface
started: 2026-11-20T18:09:17+00:00
finished: 2026-11-20T18:16:23+00:00
ran:
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_scan frontier SCRATCH
  - OMP_NUM_THREADS=1 .venv/bin/python -m hunts.rh_claim_interface.run_scan frontier SCRATCH (again, with the sources block)
outcome: without RH the weight above height 3e12 is 1.48e-12 by the zero density and G(y) <= sqrt(y) is guaranteed to about 4.2e23 (8.2e22 from the published theorem); the printed Lemma 4.2 of the 2013 paper is exceeded at T = 1000 by the listed zeros alone, 8.866e-04 against 8.140e-04
artifacts:
  - hunts/rh_claim_interface/frontier.json
```

REVIEW_TESTS_MANIFEST

## What was not run

- The level scan for conductor at most 20 beyond `10^7`: about 15 minutes per
  further decade.
- A zero table beyond 20000: about 10 minutes for 10^5.
- The smoothed sum of the shifted-product rival. Its log-derivative
  coefficients went through the battery in the review round; the rest is
  derivation only, see RESULTS.md section 7.
- The Arb spot checks of the explicit formula with all 20000 zeros (about
  80 s per point at 128 bits by the 2000-zero unit of 8.6 s): the coarse
  resolution of the 2000-zero check is stated instead.
- Any Lean or Lake command, on the archive or otherwise.
