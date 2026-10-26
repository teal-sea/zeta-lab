# RUNS: `skewes_enclosure` (hunt #152)

Every estimate is written here before the spend. Box: shared 32 vCPU Linux VM,
python-flint 0.9.0 (Arb), `nice -n 10`, with a co-tenant holding the 1-minute load
near 30 to 65 during these runs, so wall times are pessimistic for a free core
(the processes showed 72 to 80% CPU).

## 2026-10-26: unit timings (tiny, under a minute each, no estimate needed)

| what | index range | prec (bits) | batch | ms/zero | max Arb radius on gamma |
| --- | --- | --- | --- | --- | --- |
| `acb.zeta_zeros` | 1 .. 200 | 128 | 200 | 4.5 | 4.7e-38 |
| `acb.zeta_zeros` | 1 .. 2000 | 128 | 1000 | 8.5 | 1.2e-35 |
| `acb.zeta_zeros` | 1000001 .. +200 | 128 | 200 | 51.1 | 3.1e-33 |
| `acb.zeta_zeros` | 21000001 .. +200 | 128 | 200 | 43.5 | 4.9e-32 |
| `acb.zeta_zeros` | 21000001 .. +1000 | 64 | 1000 | 27.1 | 9.1e-13 |
| `acb.zeta_zeros` | 21000001 .. +5000 | 64 | 5000 | 35.8 | 9.1e-13 |
| `acb.zeta_zeros` | 21000001 .. +1000 | 128 | 1000 | 50.7 | 4.9e-32 |
| `acb.zeta_zeros` | 21000001 .. +5000 | 128 | 5000 | 48.9 | 4.9e-32 |
| `lehman_sum` (acb, 128 bits) | 1 .. 2000 | 128 | | 0.020 | |

Reading: isolation dominates and the zero sum costs nothing by comparison. Larger
batches do not amortize at height 1e7 in this build. At 64 bits the radius at
height 1e7 is 9.1e-13, below the 4e-12 that MISSION.md (b) requires (it moves
the sum by at most about 2.2e-8 against a margin of about 1.28e-4). So production
isolates at 64 bits and sums at 128.

## 2026-10-26: estimate for one 1e5-zero shard (written before running it)

Shard: indices 1 .. 100000 (heights up to ~7.5e4), 64-bit isolation, batch 5000,
route-2 sample of 200 mpmath brackets. Interpolating the table above, between
8.5 ms/zero (height 2.5e3) and ~30 to 50 ms/zero (height 6e5 and above), gives an
estimate of **15 to 35 ms/zero, so 1500 to 3500 s, about 0.4 to 1.0 core-hour**,
single process. That is at most the one-core-hour line, so it runs without an ask.

## 2026-10-26: the 1e5-zero shard (ran; inside the estimate)

13:07:07 to 13:38:20 UTC, one process, `nice -n 10`, load 29 to 40, process at
84 to 89% CPU. Isolation of gamma_1 .. gamma_100000 (last = 74920.8274989941868)
took **1749.9 s = 17.5 ms/zero = 0.49 core-hour**, inside the 1500 to 3500 s
estimate. Per 5000-zero batch the cost ran 9.0, 16.5, 20.5, 22.9, 25.2, then
settled at 15 to 20 ms/zero. Every ball is disjoint from and below the next, and
the max radius is 7.3e-15. Partial sums over these zeros:
Chao-Plymen [-0.9941173437 +/- 5.43e-11], Saouter-Demichel
[-0.9835492370 +/- 5.20e-11]. The radius is the 64-bit zero radii propagated
through the sum, as MISSION.md (b) predicts. Summing took 1.3 s.
**Route 2**: 200 random brackets (seed 152), widened to +/- 1e-8, all show a
sign change of mpmath `siegelz`, with no failures. They took **121 s, 0.6 s per
zero** at heights up to 7.5e4, which is 35 times the cost of isolation. Route 2
therefore cannot cover every zero at this cost and stays a sample.
Output JSON sha256 924aedc4c16d4ca720e57729d11c8292375b0fcd4f78e673f6e93b968e01ec4e,
zeros digest 9af0e310bf275fdcca609e15d49c734c730f46870c327f26b37fda1730443a3e
(scratch only, not committed).

```runmanifest
id: skewes_enclosure-2026-10-26-shard1
hunt: skewes_enclosure
started: 2026-10-26T13:07:07+00:00
finished: 2026-10-26T13:38:20+00:00
ran:
  - nice -n 10 .venv/bin/python -u hunts/skewes_enclosure/zero_layer.py --n0 1 --num 100000 --batch 5000 --prec 64 --sample 200 --out shard_000001_100000.json
outcome: 1e5 zeros isolated at 17.5 ms per zero, all balls ordered and disjoint, 200 of 200 sampled brackets show a sign change in mpmath, partial sums recorded
artifacts:
  - scratch shard_000001_100000.json, sha256 924aedc4c16d4ca720e57729d11c8292375b0fcd4f78e673f6e93b968e01ec4e, not committed
```

## 2026-10-26: production estimate (not run; asked of the coordinator)

Measured cost per zero at 64 bits: 17.5 ms (heights up to 7.5e4), 27 to 36 ms
(height 1e7). The figure at height 6e5 is 51 ms, but it came from a 200-zero
batch at 128 bits, so it overstates the cost. Taking 17.5 to 36 ms/zero as the
range:

| target | zeros | core-hours | wall on this box, 4 processes |
| --- | --- | --- | --- |
| Chao-Plymen (alpha = 1.34e11, T = 1131944.47) | 2.0e6 | 2e6 x 0.0175 to 0.036 s = **10 to 20** | 2.5 to 5 h |
| Saouter-Demichel (alpha = 6e12, T = 10379599.73) | 2.2e7 | 2.2e7 x 0.0175 to 0.036 s = **107 to 220** | 27 to 55 h |

Route 2 at 0.6 s/zero or more stays a sample: 2000 zeros per target costs about
0.3 to 1 core-hour, more at height 1e7 if `siegelz` cost grows with sqrt(t).
Disk: one JSON of about 2 KB per 1e5-zero shard. Zeros are not stored, only
digested, so the disk budget is untouched. Both targets are over the
one-core-hour line, so production waits for the coordinator.

## 2026-10-26: production A, Chao-Plymen, 2e6 zeros (ran; coordinator approved)

Estimate (above): 10 to 20 core-hours. The coordinator answered "A now" on
2026-10-26. Shards 2 to 20 ran as 4 workers of `run_shards.sh` from 13:41:32 to
15:34:04 UTC (wall 1.9 h). Every shard checkpoints to its own JSON. Load
stayed between 22 and 45, and MemAvailable above 60 GiB. **Total isolation
26,981 s = 7.5 core-hours**, under the estimate: per-shard cost was 12.5 to
17.5 ms/zero, falling with height in this range. No shard failed. `combine.py`
then joined the shards in seconds. Outcome in RESULTS.md section 1: the gate
passed and the lower bound is positive down to eta = 1.061e-4.

```runmanifest
id: skewes_enclosure-2026-10-26-productionA
hunt: skewes_enclosure
started: 2026-10-26T13:41:32+00:00
finished: 2026-10-26T15:34:04+00:00
ran:
  - hunts/skewes_enclosure/run_shards.sh shards 2 6 10 14 18
  - hunts/skewes_enclosure/run_shards.sh shards 3 7 11 15 19
  - hunts/skewes_enclosure/run_shards.sh shards 4 8 12 16 20
  - hunts/skewes_enclosure/run_shards.sh shards 5 9 13 17
  - .venv/bin/python hunts/skewes_enclosure/combine.py --target chao_plymen --out shards/combined_chao_plymen.json
outcome: 2e6 zeros in 7.5 core-hours, N(T) = 2000000, Revers S* inside the ball sum, lower bound on I positive down to eta = 1.061e-4, both planted faults detected
artifacts:
  - hunts/skewes_enclosure/shards/shard_001.json .. shard_020.json
  - hunts/skewes_enclosure/shards/combined_chao_plymen.json
  - hunts/skewes_enclosure/shards/SHA256SUMS
```

## 2026-10-26: production B estimate (workflow pushed for review; not triggered)

Target: shards 1..220 (zero indices 1..2.2e7, T = 10379600, which Arb counts to
exactly 22,000,000). On this box, cost ran 12.5 to 17.5 ms/zero below height
1.13e6 and 27 to 36 ms/zero near 1e7. Taking about 25 ms/zero as the mean over
the range gives **2.2e7 x 0.025 s = 153 core-hours**, with a range of 107 to 220.
Shards 1 to 20 are already done (target A's zeros; their Saouter-Demichel partial
sums are in the same JSONs), so 200 shards remain: about 140 to 200 core-hours.
On GitHub Actions (`.github/workflows/skewes-enclosure.yml`), 16 shards per
4-vCPU job means 13 jobs; at max-parallel 6 that is 3 waves of at most about
4.5 h, roughly 13 h wall. Runner speed is unmeasured, so the first request is a
4-shard pilot at the top of the range (shards 217 to 220). It measures ms/zero
on a runner before the remaining shards are requested. The workflow triggers only
on a push touching `hunts/skewes_enclosure/RUN_REQUEST.json`, which is not
committed until the coordinator replies "go".

## 2026-10-26: peak-RSS shard on the box (estimate before running)

Shard 216 (zero indices 21500001 .. 21600000, height ~1.02e7), 64-bit, sample 20,
under `/usr/bin/time -v`, as the coordinator asked for the workflow's memory rule.
Estimate: 27 to 36 ms/zero, so 2700 to 3600 s, **0.75 to 1.0 core-hour**,
single process. Its JSON is a production-B shard and is kept.

Ran 15:50:30 to 16:27:28 UTC (load 9 to 37): **22.1 ms/zero, 2214 s = 0.62 core-hour**,
under the estimate. **Peak RSS 44,976 kB** (`/usr/bin/time -v` and the shard's own
`max_rss_kb` agree). A 1e4-zero probe at index 21900001 peaked at 38,144 kB
(23.9 ms/zero). The workflow's `SHARD_RSS_KB = 120000` is therefore a 2.7x margin.
All balls are ordered and disjoint, and 20/20 route-2 brackets show a sign change.
`shards_b/shard_216.json` is kept as a production-B shard. On this box a top-of-range
shard costs 0.62 core-hour, which is the reference for the pilot's
<= 1.1 core-hour/shard condition.

```runmanifest
id: skewes_enclosure-2026-10-26-shard216
hunt: skewes_enclosure
started: 2026-10-26T15:50:30+00:00
finished: 2026-10-26T16:27:28+00:00
ran:
  - /usr/bin/time -v nice -n 10 python -u hunts/skewes_enclosure/zero_layer.py --n0 21500001 --num 100000 --batch 5000 --prec 64 --sample 20 --seed 152216 --out shards_b/shard_216.json
outcome: shard 216 at 22.1 ms per zero, peak RSS 44976 kB, balls ordered and disjoint, 20 of 20 sampled brackets show a sign change
artifacts:
  - hunts/skewes_enclosure/shards_b/shard_216.json
```

## 2026-10-26: pilot request for production B (GitHub Actions)

Coordinator-approved pilot: shards 217 to 220, one 4-shard job. Estimate from
shard 216 on the box: 0.62 core-hour per shard, so **about 2.5 core-hours and
40 to 60 min wall** if the runner matches the box. Pass conditions, set by the
coordinator: 4/4 shards complete with no timeouts, the smoke check passes, and
the measured cost is at most 1.1 core-hours per shard.

Pilot outcome (run 40359429542, commit a29106dc6, 22 min 46 s job): **passed all
three conditions**. 4/4 shards completed with no timeouts, and the smoke check
reproduced the box's digest, both partial sums and run A's gamma_2000000
exactly. Cost was 13.3 to 13.5 ms/zero, **0.369 to 0.375 core-hour per shard**,
against a limit of 1.1. Peak RSS was 47.5 to 48.3 MB. Every ball is ordered and
disjoint, and 20/20 route-2 brackets per shard show a sign change. The runner was an
AMD EPYC 9V45 with 4 vCPU and 16 GB, running python-flint 0.9.0 and mpmath 1.3.0.
Its manifest and the four shard JSONs are in `shards_b/`.

## 2026-10-26: main run for production B (pre-approved on the pilot's numbers)

Remaining shards: 21 to 215. That is 195 shards, not the 196 the plan
assumed, because shard 216 already ran on the box. Sizing from the pilot: at
most 0.375 core-hour, so about 23 min per shard at the top of the range and
less below. 16 shards per job give 13 jobs, each running 4 rounds of 4.
Rounds x per-shard timeout = 4 x 80 min = 320 min <= 330, so even a block whose
every shard hit the timeout fits the job cap. Expected cost is **195 x 0.30 to
0.375 = 59 to 73 runner core-hours**. Expected wall is 4 waves (max-parallel 4)
x about 1.6 h, roughly **6.5 h**. The 80-minute per-shard timeout is kept.

## 2026-10-26: main run outcome (Actions run 40363428968)

13/13 jobs succeeded between 16:53 and 22:33 UTC. 195 shards ran, all sound;
per-block speed was 8.2 to 16 ms/zero, varying by runner. **Total isolation over
all 220 shards was 97 core-hours**. **Correction (2026-10-26):** an earlier
version said "about 64 of them on runners, within the estimate". In fact shards
21 to 215 cost **87.4 runner core-hours** (88.6 by job wall time x 4), **over** the
59 to 73 estimate. The cause is the per-CPU spread. Runner speed was 8.2 to 16 ms/zero
depending on the CPU model a job landed on, against the pilot's 13.4. The estimate
extrapolated from one CPU, and the upper blocks drew slower ones. `combine.py --target saouter_demichel`: completeness holds, but **the gate failed**
(RESULTS.md section 6). The combined JSON is `shards_b/combined_saouter_demichel.json`,
and checksums are in `shards_b/SHA256SUMS`.

```runmanifest
id: skewes_enclosure-2026-10-26-productionB
hunt: skewes_enclosure
started: 2026-10-26T16:53:28+00:00
finished: 2026-10-26T22:33:12+00:00
ran:
  - GitHub Actions skewes-enclosure run 40363428968 (RUN_REQUEST shards 21-215, 16 per job)
  - .venv/bin/python hunts/skewes_enclosure/combine.py --target saouter_demichel --shards <all 220 shards> --out shards_b/combined_saouter_demichel.json
outcome: 2.2e7 zeros complete by Turing count, but the ball sum at omega 727.95134 misses Revers's printed S* by 0.0122, so the gate failed and target B is unresolved
artifacts:
  - hunts/skewes_enclosure/shards_b/shard_021.json .. shard_220.json
  - hunts/skewes_enclosure/shards_b/combined_saouter_demichel.json
  - hunts/skewes_enclosure/shards_b/SHA256SUMS
```

## 2026-10-26: rerun of target B on the pre-registered omega grid (estimate)

Pre-registration: `PREREG_B2.md` and `omega_grid.json`, commit e5b33dc90. The
coordinator directed all 220 shards on runners, with a cap of 100 runner core-hours.
Sized from the measured spread, not the mean: 8 to 16 ms/zero by CPU model, so 0.23
to 0.45 core-hour per shard. The grid adds 0.23 ms/zero (under 2%), and gzipping the
zeros costs seconds. **220 shards x 0.23 to 0.45 = 51 to 99 core-hours; the
central estimate, from the last run's actual 89.2 core-hours for shards 21 to 220
plus about 5 for shards 1 to 20 at runner speed and 2% for the grid, is about
96 core-hours.** That is close to the cap. A watcher projects the run's total
from finished shards and stops the run if the projection passes 100. Plan: 14
jobs of 16 shards (the last has 12), max-parallel 4, per-shard timeout 80 min. At
16 ms/zero a shard is about 27 min, so a job is about 110 min.
