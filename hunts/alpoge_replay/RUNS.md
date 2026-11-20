# alpoge_replay: allocations, estimates, outcomes

All compute is GitHub-hosted `ubuntu-24.04` runners (four cores, 16 GB) under
`.github/workflows/replay-alpoge-rh.yml` on branch
`claude/bold-ramanujan-x7z42m`. The repository is public, so these bill zero.
Nothing is built on a laboratory machine or in an assistant container. Times
are UTC.

## Estimate before spending, 2026-11-20

Nothing of this archive had been timed when this was written. Two things were
available.

**The nearest measured unit is this laboratory's October replay**
(`docs/38` section 7): 2,925 modules and 25 MB of source, with their patched
dependencies, built on one four-core runner in 2 h 15 min; three leaf modules
elaborated in 1.9 s to 5.2 s each. This archive is 175,187 modules and
1,030 MB. By source bytes that is 41 times the October closure, by module
count 60 times. Scaling the October wall time gives 90 to 135 runner-hours.
That is an extrapolation across two different code bases, not a measurement,
and the archive sets `maxHeartbeats = 4000000` package-wide, twenty times
Lean's default, so its heaviest declarations may cost far more per byte.

**The round structure was simulated on the real import graph**
(`replay_plan.py simulate`, sixteen shards) under two cost models:

| cost model | CPU-hours | 4 h rounds | 2 h rounds | 1 h rounds |
| --- | --- | --- | --- | --- |
| 4 s + 0.5 s per KB | 338 | 7 rounds | 10 rounds | 14 rounds |
| 6 s + 1.5 s per KB | 721 | 10 rounds | 14 rounds | 17 rounds |

Progress per round is limited by the graph, not by runner count: a module
whose unbuilt imports sit in two shards waits a round. So short rounds finish
sooner. With one hour of building and about twenty minutes of setup, restore
and packing per round, both models land between 20 and 24 hours of wall time.
If the real cost per module is three times the heavier model, that is about
three days. The planner refits its rate from each round's timings, and every
shard runs under a deadline, so a wrong estimate costs rounds, not
correctness.

**Disk is the open risk.** The last shard and the verdict job need every
output on one runner. October's 25 MB closure left 1.01 GB of saved outputs.
If this archive keeps that ratio the full set is tens of gigabytes compressed
and may pass 100 GB unpacked, against about 95 GB free on a cleaned runner.
The workflow carries an optional zstd-compressed btrfs loop volume
(`compress_fs`) for that case. The pilot measures the ratio before any long
round is dispatched.

**Runner budget.** Fourteen shards plus the plan and merge jobs, under the
account's twenty concurrent jobs, leaving room for the laboratory's own
checks and for the session building on the result in parallel.

## Runs

Appended as they land. A run that failed is recorded with what it showed.

### Pilot round 0, 2026-11-20, run 44775351495

Epoch `p1`, four shards, six build minutes each, no chaining. Started
16:38:12Z by the push that registered the workflow; merged 16:53Z.

| | |
| --- | --- |
| plan job | 2 min 50 s, of which 2 min 9 s saving the archive to the branch cache; the archive came from its author's site in 5 s and matched the pinned sha256 |
| shard setup | about 3 min 40 s per runner: disk cleanup 96 to 135 s, archive from cache and extraction 10 s, toolchain 11 to 18 s, dependencies and the Mathlib olean cache 64 to 81 s |
| planned / built | 747 / 491 modules; three of four shards were stopped by the deadline, as intended |
| failures | 0 modules failed to elaborate, 0 crashed, 0 `declaration uses 'sorry'` lines, 0 modules rebuilt outside their shard |
| timings | 291 of the 491 have a recorded time (the parser missed modules Lake marked with a warning sign, fixed in `3cf772a8`): 2,897 s in all, mean 9.96 s, median 6.80 s, 90th percentile 14.0 s, slowest 159 s |
| fit | seconds = 5.47 + 0.583 per KB of source, least squares over those 291 |
| outputs | 3,258 MB for 4.67 MB of source. 375 MB is `.olean` (80 times the source); the rest is almost all `<module>.setup.json`, about 6 MB each |
| bundle | 237 MB, artifact 14650860108; state artifact 14648714591 |

**What it changes in the estimate.** By the fit, the whole archive is about
433 CPU-hours; by throughput (491 modules in 96 CPU-minutes, with three shards
cut mid-module) about 570. Both sit between the two cost models of the
simulation above, so the round count stands: 14 to 17 one-hour rounds, about a
day. These are leaf modules only. Nothing deeper in the graph has been timed.

**Disk is now a measured problem, not a guess.** At 80 times the source, the
`.olean` files of the whole archive come to about 83 GB, by the per-module
average about 134 GB, against about 88 GB free on a cleaned runner that
already holds Mathlib. So the late rounds and the verdict job run with
`compress_fs` on, and round 1 of the pilot exercises it. The setup files are
not carried at all from `3cf772a8` on; at 6 MB each they alone would have been
a terabyte.

### Pilot round 1, 2026-11-20, run 44778953944

Epoch `p1`, four shards, six build minutes, `compress_fs` on, chained with
`max_round=2`. Dispatched 17:00:10Z from state artifact 14648714591, merged
17:13Z. This round exists to test three things, and all three held.

| | |
| --- | --- |
| restore across runners | shard 1 needed 75 modules built in round 0 on other runners, found all 75 on disk, and Lake rebuilt none of them: 0 modules rebuilt outside their shard in the whole round |
| the compressed volume | btrfs with zstd on a loop file mounted over `.lake/build` on every runner; the runner's root disk is 145 GB with 88 GB free before cleanup and 101 GB after |
| the chain | the merge job dispatched round 2 by itself (run 44781165276, started by `github-actions[bot]` at 17:13:16Z) |
| planned / built | 618 / 532 modules; 1,023 of 175,187 in all (0.58%) |
| failures | 0 failed, 0 crashed, 0 `declaration uses 'sorry'` lines |
| timings | all 532 timed: 5,160 s, mean 9.70 s per module; 9.79 s over the 823 timed so far |
| outputs per module | `.olean` 611 KB, `.ilean` 32 KB, `.c` 6 KB, `.trace` 4.6 KB; 87 times the source in all, with the setup files no longer carried |
| bundle | 103.5 MB for 532 modules, artifact 14651982496; state artifact 14652177405 |

**Estimate, refit.** At 87 times the source the carried outputs of the whole
archive are 90 to 115 GB unpacked and, at the 3.3 to 1 the chunks compress,
about 34 GB as bundles. On the compressed volume that fits one runner.
Re-simulated with the measured cost (5.47 s + 0.583 s per KB, 433 CPU-hours):
14 rounds at twelve shards and sixty build minutes, the same at sixteen
shards, so the chain runs at twelve. With about fifteen minutes of setup,
restore and merge per round that is about 17.5 hours, if modules higher in
the graph cost what leaves cost. That last condition is not measured.

### Pilot round 2, 2026-11-20, run 44781165276

Dispatched by round 1's merge job at 17:13:16Z, same settings, merged 17:25Z,
stopped at `max_round=2` as set.

| | |
| --- | --- |
| planned / built | 621 / 539 modules; 1,562 of 175,187 in all (0.89%) |
| failures | 0 failed, 0 crashed, 0 `declaration uses 'sorry'` lines, 0 modules rebuilt outside their shard |
| timings | all 539 timed, mean 9.00 s, slowest 141 s |
| cost against depth | mean seconds per module over the 1,362 timed so far, by level in the import graph: 10.8, 9.8, 7.6, 8.8, 8.4 at levels 1 to 5 and 10.0 at level 6 and above. Flat so far, on a sample that reaches only the bottom of a graph 203 levels deep |
| bundle | 119.2 MB, artifact 14652084151; state artifact 14652239123 |

### The full chain, launched 2026-11-20 17:29Z

Epoch `p1`, from round 3 and state artifact 14652239123: twelve shards, sixty
build minutes, `compress_fs` on, `chain` on, `max_round=60`. Each round's
merge job dispatches the next; the round that builds `Main` dispatches the
verdict job instead. Rounds are appended below as they merge.

| round | run | merged (UTC) | built | total | % | failed | crashed | rebuilt outside shard | mean s per module | note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 44775351495 | 16:53 | 491 | 491 | 0.28 | 0 | 0 | 0 | 9.96 | pilot, 4 shards x 6 min |
| 1 | 44778953944 | 17:13 | 532 | 1,023 | 0.58 | 0 | 0 | 0 | 9.70 | pilot |
| 2 | 44781165276 | 17:25 | 539 | 1,562 | 0.89 | 0 | 0 | 0 | 9.00 | pilot |
| 3 | 44783691856 | 18:38 | 21,121 | 22,683 | 12.95 | 0 | 0 | 0 | 7.68 | first full round, 12 shards x 60 min, 22,522 planned |
| 4 | 44794657912 | 19:48 | 16,552 | 39,235 | 22.40 | 0 | 0 | 0 | 8.39 | 17,263 planned; state artifact 14662502720 |

**After round 4 (read 2026-11-20 20:05Z).** 39,235 modules, 243 MB of the
1,030 MB of source, have elaborated with no failure, no crash, no
`declaration uses 'sorry'` line, and no module rebuilt outside its shard. A
round takes about 70 minutes end to end and dispatches the next by itself.

The condition the estimate hung on is now partly measured. Mean seconds per
module over 39,035 timed modules, by level in the import graph: 6.9 at levels
1 to 2, 7.4 at 3 to 5, 8.2 at 6 to 10, 9.3 at 11 to 20, 9.3 at 21 to 40, and
8.7 at level 41 and above (1,144 modules). Cost does not grow with depth over
the bottom fifth of the graph. Median 6.4 s, 99th percentile 31 s, slowest
509 s (`BCrisGalois`, 5.5 KB of source).

Re-simulated from this state with the refit rate (0.656 s per KB plus 4 s):
295 CPU-hours left, 13 more rounds at twelve shards, so `Main` builds at
about 11:30Z on 2026-11-21 if nothing above costs more than what is below.
Sixteen or eighteen shards would save one round, so the chain stays at twelve.
