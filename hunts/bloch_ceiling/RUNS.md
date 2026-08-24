# Runs

Environment for the local runs: macOS (Darwin 25.5.0, Apple Silicon), CPython 3.12.12 in
a fresh venv from the archive's `requirements.txt` (`python-flint` 0.9.0, `numpy` 2.5.1,
`scipy` 1.18.0), on the archive `bloch-computations-1.0.0.zip` (sha256
`bdaa1ff3…408e7`, verified; all 28 entries of `CHECKSUMS.sha256` verified). Modal runs use
the same pinned packages on `debian_slim` / CPython 3.12, one physical core per container
(`cpu=1.0`), with the archive's `src/` copied in unchanged. The archive lives in a
gitignored directory outside `hunts/` (`.upstream/bloch/`, fetched by
`fetch_upstream.sh`); nothing from it is vendored here.

Modal runs this code about 2.3x slower per core than the local machine (fixed-radius
ceiling witness 8.9 s vs 3.5 s; `verify --mesh 20` 112 s vs 52 s).

**The section 5 runs are on GitHub Actions, not Modal**, on `ubuntu-latest` standard
runners (4 vCPU, 4 worker processes per job) with the archive's own
`requirements.txt` installed unchanged: `python-flint` 0.9.0, `numpy` 2.5.1,
`scipy` 1.18.0 on CPython 3.12. The archive is fetched by `fetch_upstream.sh` in
every job, sha256 and all 28 internal checksums verified there as well, and cached
between jobs under a key that *is* the archive's sha256. A standard runner is 2.9x
slower per core than the author's own machine and about 3.4x slower than the local
one. Runner speed is not uniform: across the shards it ranged from 0.053 to 0.105
seconds per terminal box.

The **local** calibration in this section ran on CPython 3.14.0 with `numpy` 2.5.2,
which is this repository's own environment and not the archive's pin. That is
recorded rather than hidden: it is why the calibration is used only for ratios and
rates, while every number that carries a result comes from CI, where the pin is
installed. The two agree where they overlap, exactly (section 5).

```runmanifest
id: bloch_ceiling-2026-08-23-fetch-and-fixed-radius
hunt: bloch_ceiling
started: 2026-08-23T08:04-05:00
finished: 2026-08-23T08:09-05:00
ran:
  - hunts/bloch_ceiling/fetch_upstream.sh (download, sha256, unzip, CHECKSUMS.sha256)
  - .venv/bin/python src/verify_all.py (archive root, pinned venv)
outcome: the zip's sha256 and all 28 internal checksums match; both fixed-radius certificates verify in under a second and every printed enclosure matches expected-output/verification.md to the last printed digit
artifacts:
  - hunts/bloch_ceiling/fetch_upstream.sh
  - hunts/bloch_ceiling/artifacts/local/bloch-verify-fixed.txt
```

```runmanifest
id: bloch_ceiling-2026-08-23-near-branch-and-mesh
hunt: bloch_ceiling
started: 2026-08-23T08:09-05:00
finished: 2026-08-23T08:11-05:00
ran:
  - .venv/bin/python src/variable_radius_certificate.py verify --mesh 20 (52 s)
  - .venv/bin/python src/certify_fixed_radius_ceiling.py (3.5 s)
outcome: uniform positivity margin +0.000936855231, near moment slope margin 0.0331790701855, near centre 0.136904745959 < 0.436558987993, near moment gain 0.0153040536989472, 20x20 mesh away minimum 0.015866072532 in sectors 6 and 18, MESH RESULT PASS > 0.0153; fixed-radius ceiling witness 0.01519720970909415 < 0.0152 with 53302 annulus boxes (33051 terminal); all match the archive's expected output and VARIABLE_RADIUS_FINDINGS.md
artifacts:
  - hunts/bloch_ceiling/artifacts/local/bloch-verify-mesh20.txt
  - hunts/bloch_ceiling/artifacts/local/bloch-ceiling-witness.txt
```

## The estimate for the section 5 run, published before it was launched

The first attempt at section 5 had no cost estimate, and that is how it burned
six hours. This is the estimate, written here before any of the run was
launched, in the four numbers CLAUDE.md's compute discipline asks for: cells per
sector, sectors, seconds per cell, therefore job count and wall time.

**What one unit costs.** The unit is one of the 1600 initial cells of one away
sector, run through the author's `branch_verify` with `domain` set to that cell.
Measured locally (`calibrate_cell.py`, and note the environment is CPython
3.14.0 with `numpy` 2.5.2, *not* the archive's pinned 3.12/2.5.1, which is what
CI installs):

| sector | what | at target 0.0153 | at target 0.0153040536 | at target 0.015316 |
|---|---|---|---|---|
| 1 | three lowest-bound cells | 2777 boxes, 80.5 s | 2783 boxes (x1.0022), 82.5 s | |
| 17 | lowest-bound cell (1599) | 6820 boxes, 190.5 s | 6888 boxes (x1.0100), 216.5 s | 7106 boxes (x1.0419), 228.3 s |

Two things fall out. The **cost of raising the target is small**: +4.05e-6 of
target costs 1.0% more boxes in the worst place measured, and even +1.6e-5 costs
4.2%. And **the per-shard fixed cost is negligible**: 0.9 to 1.0 s to build the
1057 halfspaces and the sector row, against hundreds of seconds of subdivision.

**What the whole run costs.** The archive's own reference logs give the exact
box count at the published target, so the projection multiplies a measured rate
by a known quantity rather than extrapolating a guess:

| quantity | value | source |
|---|---|---|
| cells per sector | 1600 | the author's 40x40 initial grid |
| sectors | 24 | `variable_radius_certificate.py:354` |
| terminal boxes at target 0.0153 | 11,443,518 | sum of `reference-run/logs/*.log` |
| the author's own cost | 380,294 s over the 23 sectors with a fresh log, 105.6 core-hours, 0.0340 s/box | the same logs |
| box growth at target 0.0153040536 | x1.010, worst case measured | the table above |
| projected boxes | 11.56e6 | |
| seconds per box on a standard runner | **0.10008** | the calibration job below: 40 cells, 14,182 boxes, 1419.3 core-seconds |
| projected core-hours | **321** | 11.56e6 x 0.10008 |
| jobs | 314, at 38,000 reference boxes each | `ci_plan.py plan` |
| processes per job | 4 | standard runners are 4 vCPU |
| wall budget per process | 1020 s, inside a 25-minute job timeout | `ci_run.json` |
| per-job capacity | 4 x 1020 / 0.10008 = 40,767 boxes, so 38,000 leaves 7% of headroom | |
| concurrency | 20 | GitHub's limit for this account |
| projected wall clock | ~4.8 hours | 314 jobs / 20 concurrent, ~18.5 min per wave |

A 40x40 matrix of 314 jobs does not fit GitHub's 256-job limit, so the run is
**two workflow runs**: sectors 0-11 (140 jobs) and sectors 12-23 (174 jobs).
They serialise on the workflow's concurrency group, which is what the wall-clock
figure above already assumes, since 20 concurrent jobs is the account limit
either way.

The instrument is `ci_away_shard.py`: each process appends a cell's verdict to
its own JSON-lines file the moment that cell finishes, and stops on its own wall
budget rather than being killed by the job timeout. A shard that was
underestimated therefore ends cleanly with partial results, and `mode: sweep`
re-runs only the cells still missing.

```runmanifest
id: bloch_ceiling-2026-08-24-calibrate-one-cell
hunt: bloch_ceiling
started: 2026-08-24T08:50-05:00
finished: 2026-08-24T09:35-05:00
ran:
  - hunts/bloch_ceiling/calibrate_cell.py --sector 1 --ncells 3 --targets 0.0153,0.0153040536 (local)
  - hunts/bloch_ceiling/calibrate_cell.py --sector 17 --ncells 3 --targets 0.0153,0.0153040536,0.015316 (local, stopped after the first cell had all three targets)
  - hunts/bloch_ceiling/ci_away_shard.py on one GitHub Actions runner, sector 17, shard 0 of 41 (the diagonal of the 40x40 grid), target 0.0153040536
outcome: a standard runner does 0.10008 s per terminal box with 4 worker processes (40 cells, 14,182 boxes, 1419.3 core-seconds, 718 s wall), which is 2.9x slower than the author's own machine and puts the whole 24-sector away branch at 321 core-hours; raising the target from 0.0153 to 0.0153040536 costs 1.0% more boxes at the worst cell measured and 4.2% at 0.015316; and cell 1599 of sector 17 returns exactly 6888 terminal boxes on the runner and on the local machine, which is the machine-independence the per-cell sharding relies on
artifacts:
  - hunts/bloch_ceiling/calibrate_cell.py
  - hunts/bloch_ceiling/artifacts/calibration-2026-08-24.json
```

```runmanifest
id: bloch_ceiling-2026-08-23-modal-quick
hunt: bloch_ceiling
started: 2026-08-23T08:14-05:00
finished: 2026-08-23T08:18-05:00
ran:
  - .venv/bin/modal run hunts/bloch_ceiling/modal_reproduce.py::quick
  - .venv/bin/modal run hunts/bloch_ceiling/modal_reproduce.py::collect
  - python hunts/bloch_ceiling/compare_expected.py
outcome: the four sub-minute programs rerun in a Modal container give the same 22 statistics as the local run and as expected-output/verification.md (compare_expected.py, 22 of 22 match); the only textual difference is the twelfth decimal of the mesh minimum, which the findings file quotes rounded
artifacts:
  - hunts/bloch_ceiling/modal_reproduce.py
  - hunts/bloch_ceiling/compare_expected.py
  - hunts/bloch_ceiling/artifacts/modal-reproduce.json
```

```runmanifest
id: bloch_ceiling-2026-08-24-away-branch-at-a-raised-target
hunt: bloch_ceiling
started: 2026-08-24T09:42-05:00
finished: 2026-08-24T18:33-05:00
ran:
  - .github/workflows/bloch-higher.yml on GitHub Actions, four runs: sectors 0-11 (32740352675, 140 shards), sectors 12-23 (32743533542, 174 shards), a sweep of the cells those two left plus the exact-count oracle (32774563515, 121 shards), and a final sweep of three cells and the oracle's cheap tail (32789363183, 30 shards)
  - each shard is hunts/bloch_ceiling/ci_away_shard.py, the author's branch_verify on one stride-slice of a sector's 1600 initial cells, 4 worker processes, one JSON-lines record written and fsynced per cell as it finishes
  - hunts/bloch_ceiling/ci_plan.py collect over all 489 shard artifacts, at each target separately
outcome: the author's own verifier ACCEPTS target 0.0153040536, above the published 0.0153, in all 24 away sectors and all 38,400 initial cells, with zero cells refused anywhere; 11,543,180 terminal boxes, 0.87% above the archive's 11,443,518 at its own weaker target, every sector between +0.58% and +1.25%; the near branch clears the same target on the unmodified shipped npz at the head of every shard (positivity margin +0.000936855231, near gain 0.0153040536989472), and that gain is the rigorous cap, so nothing above it is reachable without regenerating the certificate data; the exact-count oracle matches to the integer, sectors 0 and 1 rerun at the published 0.0153 giving 270,744 and 292,931 against reference-run/logs
artifacts:
  - hunts/bloch_ceiling/ci_away_shard.py
  - hunts/bloch_ceiling/ci_plan.py
  - hunts/bloch_ceiling/ci_run.json
  - .github/workflows/bloch-higher.yml
  - hunts/bloch_ceiling/artifacts/higher-target-rollup.json
  - hunts/bloch_ceiling/artifacts/oracle-0.0153-rollup.json
  - hunts/bloch_ceiling/artifacts/higher-target-cells.tar.gz
```

## What the run actually cost, against the estimate

The estimate above said 321 core-hours and 314 jobs. The run spent **307.4
core-hours** at the raised target plus 16.7 for the oracle, over **476 jobs** in
five workflow runs, **114.8 runner-hours** of GitHub-hosted machine time, billed
zero, in **9.1 hours** of wall clock at 20 concurrent jobs. The projection was
4.2% high on compute, at a realised 0.0959 seconds per terminal box against the
0.10008 measured in calibration. The extra jobs are the two sweeps, whose size
the estimate did not try to predict because it is not knowable before the first
pass.

Nine jobs were cancelled by their own `timeout-minutes`, all in the first away
run and all before that timeout was raised from 25 to 35 minutes. Every one of
them still uploaded the cells it had reached. That is the per-unit checkpointing
doing the job it exists for: the nine cost nine *partial* shards rather than nine
shards, and a sweep did the remainder. The attempt this replaces lost a whole
shard every time it was preempted, which is why six hours of it bought nothing.
