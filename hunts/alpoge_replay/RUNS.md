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
| 5 | 44805594376 | 20:56 | 12,292 | 51,527 | 29.41 | 0 | 0 | 0 | 8.58 | 12,692 planned (the simulation from round 4 said 11,147); state artifact 14667569877 |
| 6 | 44815849893 | 22:13 | 13,236 | 64,763 | 36.97 | 0 | 0 | 0 | 8.57 | 14,921 planned; state artifact 14674737119 |
| 7 | 44827219416 | 23:30 | 15,906 | 80,669 | 46.05 | 0 | 0 | 0 | 8.99 | 17,808 planned; state artifact 14678652610 |
| 8 | 44837378674 | 00:49 (11-21) | 15,904 | 96,573 | 55.13 | 0 | 0 | 0 | 9.91 | 19,412 planned, seven shards stopped by the deadline; state artifact 14683342288 |
| 9 | 44846358339, remerged by 44856817210 | 02:36 | 13,890 | 110,463 | 63.05 | 0 | 0 | 0 | 11.02 | eleven of twelve shards; see the incident below; state artifact 14687303640 |
| 10 | 44856849272 | 04:09 | 6,971 | 117,434 | 67.03 | 0 | 0 | 0 | 15.82 | 11,909 planned; only eight of twelve shards reported, see the second incident; state artifact 14691128227 |
| 11 | 44864672470 | 05:44 | 9,886 | 127,320 | 72.68 | 0 | 0 | 0 | 14.80 | 16,828 planned; eleven of twelve shards reported, shard 10's runner was lost mid-build; the last round on four compiles and swap; state artifact 14694700878 |
| 12 | 44872248926 | 07:21 | 10,926 | 138,246 | 78.91 | 0 | 0 | 0 | 7.71 | 17,472 planned at the old sizing; all twelve shards reported; the first round at two compiles and the first with a watchdog, which killed nothing; state artifact 14697715651 |
| 13 | 44879877336 | 08:54 | 5,170 | 143,416 | 81.86 | 0 | 0 | 0 | 22.30 | three compiles at once: half of round 12's output, see the judgement below; all twelve shards reported, the watchdog suspended and killed nothing; 2 modules built twice, same bytes; state artifact 14699969555 |
| 14 | 44887113440 | 10:08 | 7,071 | 150,487 | 85.90 | 0 | 0 | 0 | 8.12 | two compiles, outputs in a plain directory; eleven of twelve shards reported, shard 2 was lost to a race in the new restore; 7,239 planned and 7,071 built, see the note below; state artifact 14702344189 |

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

### Incident, round 9, 2026-11-21 02:11Z: the chain stopped for 25 minutes

Two unrelated things went wrong in run 44846358339. Neither was a module
failing.

- **One runner died.** Shard 10 was shut down 52 minutes into its build
  ("The runner has received a shutdown signal"), with no done record and no
  evidence artifact, so the cause is not recorded. Running out of memory is
  the likeliest: the mean cost per module has climbed from 7.7 s in round 3
  to 11.0 s in round 9 as modules import more, and four elaborate side by
  side. Its modules were never counted as built and are planned again.
- **The merge job lost a race.** It asked the run's artifact listing for the
  bundle it had just uploaded, the listing did not show it yet, and the job
  exited before writing the state. The eleven finished shards were already
  bundled (artifact 14686328694), so nothing was lost but the record.

Repair, commit `bb294271`: the merge job takes the bundle id from the action
that made it and polls the listing if that is empty; build and replay runners
add 16 GB of swap, best effort; and a new mode `remerge` folds a finished
round from its run id without rebuilding anything. Run 44856817210 did that
for round 9 in 24 seconds and dispatched round 10 at 02:36:46Z. Whether swap
is the right remedy is not known until a round that deep completes on all
twelve runners.

### Second incident, round 10, 2026-11-21 04:09Z: four runners lost, and what it means

Round 10 ran with the extra swap. Four of its twelve shards never reported;
one job is recorded as failed with no log, the others ended without a done
record. The eight that reported built 6,971 modules at 15.8 s each, against
11.0 s in round 9 and 7.7 s in round 3. No lean process was recorded as
crashed in any round. Read together: memory, not chance. Four deep modules
elaborating side by side fill a 15 GB runner, the runner stops answering
before the kernel kills anything, and with swap the survivors thrash.

Changed in `0a93a8b5`, taking effect from round 12 (round 11 was already
running): two compiles at once by default; the swap removed;
`mem_watchdog.py` in the build and replay steps, which kills the largest lean
process when available memory stays under 700 MB, so that a full runner
costs one module and not the shard, and which logs memory every thirty
seconds; and the chain now lowers the thread count when a round loses shards,
not only when a compile is killed.

**The estimate above is withdrawn.** It assumed four compiles per runner to
the top of the graph. At two, and with rounds now about ninety minutes, the
57,753 modules left are eight or more rounds: `Main` no earlier than about
18:00Z on 2026-11-21. That in turn assumes one deep module fits a runner by
itself. Whether it does is not measured; the memory log of round 12 is the
first measurement, and if the top of the graph needs more than a hosted
runner has, this route ends there and that will be said.

### What round 12 measured, 2026-11-21 07:00Z: memory was never the limit at two compiles

Round 12 was the first with a memory log. Read from its first four shards
while the others were still building (two compiles at once, watchdog version
one, no kill):

| | |
| --- | --- |
| peak memory in use | 3.3 to 4.5 GB of 15.6 GB |
| largest anonymous memory of one lean process | 0.7, 0.8, 0.9 and 2.5 GB |
| file-backed memory of one lean process | 8 to 10.6 GB: mapped `.olean` files, shared between processes and reclaimable |
| runner swap | three of the four runners came with about 3 GB and used 0.3 to 1.9 GB of it while 12 GB counted as available; the fourth had none |
| throughput | 467 to 514 modules per shard-hour, 14 to 15 thread-seconds each, in the three shards whose modules together import 33,000 to 40,000 built modules; 1,672 in 59 minutes, 4.2 thread-seconds each, in the shard that imports 9,760 |
| restore before the build | 6.3 to 7.0 minutes on these four shards, 22 to 31 minutes on the other eight, for about the same number of chunks (84 to 114) |

So the second incident's reading was wrong: it was not the heap. At this
depth a module fits a runner with room to spare, two at once leave two
thirds of the memory unused, and the ten seconds a module costs here over a
shallow one is most likely its import. The few modules at the very top
import four times more and are not measured yet. What lost runners at four
compiles in rounds 9 to 11 is not identified. The mapped files are the
suspect: four processes each touching 8 to 10 GB of them on a 15.6 GB
machine that is already swapping.

**The import closures, exactly** (bit sets over the DAG, state after round
11). The 127,320 modules built have small closures: median 318 archive
modules, 99th percentile 9,401, largest 21,129. The 47,867 left: median
5,199, 90th percentile 21,575, 99th 30,586. Only 91 import more than 40,000
and nine more than 150,000, ending in `Main` with all 175,187. Median build
time against closure, over 127,120 timed modules: 6.3 s under 100 modules,
7.4 s at 1,000 to 3,000, 9.7 s at 8,000 to 10,000, 13 s at 10,000 to 15,000.
Eleven modules between 15,000 and 22,000 took a median of 500 s and one took
2,307 s (`...AutomorphicMembership.ParMem`, 10 KB of source), all in rounds
10 and 11 at four compiles with swap, so that figure mixes cost with
thrashing and is not a rate.

**What limits the campaign now is the shape of a round, not the runners.**
By the cost model the unbuilt part is 202 thread-hours with a critical path
of 0.55 hours (105 modules): 4.2 hours on twelve runners at four compiles.
The planner needs far more, because a shard must hold every unbuilt import
of what it builds, so a module that joins several unbuilt clusters waits a
round. Simulated from the state after round 11, 35 minutes of overhead per
round:

| compiles x minutes | rounds | hours | lower bound on rounds for any downward-closed plan |
| --- | --- | --- | --- |
| 2 x 60 | 9 | 14.2 | |
| 3 x 60 | 8 | 12.0 | 6 |
| 4 x 60 | 7 | 10.2 | 5 |
| 4 x 90 | 6 | 12.2 | 4 |
| 4 x 120 | 5 | 12.9 | 3 |
| 4 x 150 | 5 | 15.4 | |

Longer rounds do not help: the last rounds hold a few thousand modules and
still run one shard to its deadline. The lower bound counts a module as
buildable in a round when its whole unbuilt closure fits one shard, with
twelve shards' capacity and shared prerequisites built for free; it is what a
planner that built shared prerequisites twice could approach.

**Correction, 07:25Z, with all twelve shards of round 12 in.** The table
above takes a runner's capacity as proportional to the compiles it runs at
once. Round 12 says it is not. Every shard spent 96 to 99 percent of its two
workers' time inside lean, so nothing waits on Lake; a module took 7.7 s on
average, against 14.8 s in round 11 and 15.8 s in round 10 at four at once;
and a shard-hour built 910 modules at two compiles against 899 (round 11)
and 871 (round 10) at four. Four at once made every module take twice as
long and built no more. That is what four hardware threads on two cores
would do; the core count has not been read from the machine yet, the next
round's logs record it. Four at once was all cost: the same throughput, and
one to four runners lost per round.

Re-simulated from the state after round 12 (36,941 modules left, 82
worker-hours at round 12's rate of 0.71 s per KB plus 4 s, a runner counted
as two workers, 25 minutes of overhead per round): six rounds and 7.9 hours
at twelve shards of 60 minutes; six rounds and 7.5 hours with the filling
pass, the last of them five modules; five rounds and 6.1 hours if a third
compile adds a quarter. The last three rounds hold under 4,000 modules
between them: the tail is the shape of the graph, not capacity.

**Changed for round 13**, in order of commit:

- `2fea1e67` watchdog version two: under 2.5 GB available it suspends every
  lean process but the largest and resumes them when memory is back; under
  700 MB it kills a suspended one first ("crowded", counted but no strike),
  and only a process that is alone and still fills the runner is killed as a
  crash. It writes each module's peak memory. The chain lowers the thread
  count only when a runner is lost.
- `126dd0fe` the plan is sized for the compiles a shard will run, at the rate
  of the last two rounds (2.0 s per KB after round 11, where the all-time
  rate said 1.0).
- `b92dab76` the memory log counts major page faults and swap traffic, which
  is what will say whether three or four compiles thrash.
- `e8582bc4`, `1a6142dd`, `956d215a` the restore unpacks three chunks at a
  time and, of each chunk, only the modules the shard imports; the verdict
  job restores through the same script.
- `585591e0` the filling pass (`fill_idle`, input `fill`): an idle shard
  also builds a module whose unbuilt imports another shard owns, building
  those imports a second time; the merge compares the `.olean` bytes of
  everything built twice.
- `19c443f1` each round's state carries the watchdog's summary: least
  available memory, major faults, suspensions, kills, and the modules that
  held the most.

Round 13 was dispatched by the chain at 07:21:06Z with the old settings (run
44879843072), cancelled by hand thirty seconds later, and dispatched again
as run 44879877336: three compiles at once, the filling pass on. Three is
an experiment with a bounded cost, one round: if a third compile adds
nothing, or a runner is lost, the chain goes back to two.

### Round 13, 2026-11-21 08:54Z: three compiles at once halve the output

The experiment recorded above had a bounded cost, and it cost it. Twelve
shards at three compiles built 5,170 modules in the hour where round 12
built 10,926 at two.

| | round 12, two at once | round 13, three at once |
| --- | --- | --- |
| modules built | 10,926 | 5,170 |
| per shard | 452 to 1,672 | 24 to 1,083 |
| lean seconds per module, mean | 7.7 | 22.3 |
| per shard, mean | 4.1 to 15.8 | 4.9 to 296 |
| runners lost | 0 | 0 |
| major page faults, all runners | not logged | 132.5 million |
| pages written to swap, all runners | not logged | 84.6 million, about 340 GB |
| least memory counted as available | 11.2 GB (four shards read) | 7.3 GB |

The memory that runs out is the page cache. A lean process at this depth
holds a few hundred megabytes of its own and maps 8 to 10 GB of `.olean`
files; three such processes do not fit beside each other in 15.6 GB, the
kernel evicts mapped pages and writes heaps to swap, and every import reads
its files again. "Available" memory counts cache as free and stayed at 7 GB
and more throughout, so the watchdog, which watches that number, saw
nothing: no suspension, no kill. One module held 6.2 GB of its own
(`...DivisorProofs.ZetaSuccPow`), the first of that size seen; five passed
2 GB.

This also answers what lost runners at four compiles in rounds 9 to 11.

Changed for round 14:

- Two compiles at once again. The chain dispatched round 14 at 08:54:03Z
  with three (run 44887021838); it was cancelled by hand and dispatched
  again.
- `94dd6602` outputs go in a plain directory on the runner's disk when the
  shard's imports fit (up to 90,000 modules, about 47 GB), and on the
  compressed btrfs volume only above that. The volume dates from when a
  shard unpacked every chunk whole. Read through it, a mapped file costs a
  decompression on every fault and sits in the cache twice. What a shard
  imports now, about 31 GB for 42,000 modules, fits the disk as it is.
- `79818e7c` three bundles are downloaded at a time. Round 13's restores,
  with the bundles one after another, took 5.7 to 27 minutes for the same
  thirteen bundles; the two slowest shards started their hour 20 minutes
  after the fastest and the round waited for them.

The filling pass placed its first two extras in this round: two modules
were built by two shards each, and both came out with the same `.olean`
bytes.

**Forecast after round 13 (09:00Z).** 31,771 modules left, 71 worker-hours
at round 12's rate. Simulated with twelve shards of two compiles, the
filling pass on and 28 minutes of overhead a round: five rounds, 6.3 hours
if modules cost what they did in round 12 and 7.3 hours if those higher in
the graph cost 1.3 times as much. `Main` built between about 15:10Z and
16:20Z, the verdict job an hour to an hour and a half after that. The
window given at 07:35Z (13:30Z to 15:10Z) counted on a third compile adding
a quarter; it took away half a round instead. Round 14 is run 44887113440,
started 08:57Z; its restore took 4.5 minutes on the shard read.

### Round 14, 2026-11-21 10:08Z: the plain directory, a shard lost to my own script, and a 13.7 GB module

Two compiles at once, outputs in a plain directory, three bundles in
flight. The round took 71 minutes from dispatch to merge.

| | round 12 | round 13 | round 14 |
| --- | --- | --- | --- |
| compiles at once, volume | 2, compressed | 3, compressed | 2, plain |
| modules built | 10,926 | 5,170 | 7,071 of 7,239 planned |
| lean seconds per module, mean | 7.7 | 22.3 | 8.1 |
| major page faults, all runners | not logged | 132.5 million | 36.6 million |
| pages written to swap | not logged | 84.6 million | 38.8 million |

Three things to read from it.

**The round was planned too small.** The eleven shards that ran built 97.7
percent of what they were given and spent 51 to 98 percent of their two
workers' time inside lean; several finished a quarter of an hour early. The
planner sized the round from the timings of rounds 12 and 13, and round 13's
were thrashing, not cost. From round 16 a round is planned forty percent
over its budget (`ae768d0a`): too much is cut by the deadline and planned
again, too little is an idle runner.

**Shard 2 was lost to a race in the new restore**, seven minutes in. Several
extractors run side by side into one tree, and Python 3.12's tarfile, which
the runners have, makes a missing parent directory with a check and then a
plain mkdir. Two processes both passed the check; the second died with
`FileExistsError` and the restore, correctly, stopped the shard. Its 600 or
so modules were planned again. Fixed in `ae768d0a`: the extractor makes the
parent itself, tolerantly, before it asks tarfile. The test that came with
`1a6142dd` could not have caught it here: this tree's Python is 3.13, which
tolerates the race. The new test pins the remedy and fails without it.

**One module needed nearly the whole runner.**
`Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication`
held 13.7 GB of anonymous memory, on a machine with 15.6 GB and 3 GB of
swap, and finished. The watchdog did what version two was written for: it
suspended the other compile twice, killed one suspended compile at the hard
floor (counted as crowded, no strike, planned again), and left the large
one alone. Available memory touched 694 MB. Under version one the large
module would have been the one killed. Nothing in the graph says how many
more like it lie above; one that needs a gigabyte or two more will not fit,
and that will show as a module killed alone.

### Rehearsal of the verdict job, 2026-11-21 07:27Z to 08:04Z, run 44880300164

Estimated before: nothing was known, which is why it was run. One runner
beside round 13's twelve and the replay's four, seventeen jobs for 37
minutes. Mode `rehearse` on state 14697715651: the verdict job's own restore
of everything built in rounds 0 to 12, then a `lake build` whose targets are
the built modules that nothing built imports.

| | |
| --- | --- |
| runner | Intel Xeon 6975P-C, 4 logical CPUs on 2 cores, 15 GB |
| restore | 13 bundles, 126 chunks in 1,828 s, three chunks at a time and the bundles one after another; the disk went from 32 to 72 GB used of 145 |
| on disk afterwards | 138,246 `.olean` files, one per module in the state |
| the build | 11,020 targets in 8 invocations, exit code 0, 161 s |
| modules Lake elaborated | 0 |
| modules Lake replayed from their stored logs | 203,186 lines (a module with output is listed once per invocation that reaches it) |
| `declaration uses 'sorry'` in any replayed log | 0 |
| Lake's own memory | 1.0 GB anonymous at the peak, 2.3 GB in use on the machine |

What it establishes, and only for these 138,246 modules: the outputs of 126
chunks, each built on a different runner job, agree on one machine with what
Lake computes there from the sources. Nothing was out of date. It is the
"outputs travel between runners" limit of `MISSION.md` measured at 79
percent, by Lake's hashes, not by a kernel.

It is also the first reading of the hardware, on this one runner: two cores
with two threads each, which is what the correction above inferred from
throughput.

What it found wrong in the job, fixed before the real one: the count of
modules elaborated matched only lines marked with a tick, and Lake marks a
module that printed a warning with a warning sign, so a rebuilt module with
a warning would have been counted as none. The count was right here because
no line of the log says "Built" at all. And the log was 365 MB, because Lake
repeats every stored warning; it is compressed now.

Read forward to the verdict: the restore of all 175,187 modules is about 39
minutes at this rate and less with three bundles in flight, the check about
four minutes, and the disk has room (about 83 GB of 145). The two steps that
cannot be rehearsed are the ones that import `Main`.

**Second rehearsal, dispatched 2026-11-21 10:38Z** on state 14702344189
(150,487 modules, rounds 0 to 14), commit `4c74ca7b`. Estimate from the
first: under 35 minutes on one runner. Reason: three things the verdict job
depends on changed after the first rehearsal and have not run in it, the
volume script (now asking the loop device for direct I/O, with a fallback),
the restore with three bundles in flight, and the corrected count of
elaborated modules. Outcome: not read yet. Its evidence artifact is
`alpoge-p1-rehearse-<run id>`; `run.txt` must again say exit code 0 and
"modules elaborated in this job: 0", and its "volume:" line says whether
direct I/O was granted.

## Second pass: kernel replay

What it is and why it exists: `MISSION.md`, "The second pass". Compute is the
same hosted runners, under `.github/workflows/replay-alpoge-check.yml`.

### Estimate before spending, 2026-11-20

Nothing was known about the cost of a replay on this archive. The unit was
timed first, on one runner, before any chain was dispatched.

### Replay pilot, 2026-11-20, run 44810043854

Started 20:17:45Z by the push that registered the workflow, merged 20:31Z.
One shard, eight minutes allowed, four driver processes side by side, build
state 14662502720 (39,235 modules built).

| | |
| --- | --- |
| planned / replayed | 288 / 288, the lowest modules of the import graph; all four driver processes exited 0 |
| kernel rejections | 0 |
| processes that died | 0 |
| cost | 1,324 s of process time, 4.6 s per module: median 3.35 s, 90th percentile 4.24 s, slowest 86.7 s |
| against the build | the same modules took 10.67 s each to elaborate, so the replay costs 0.43 of the build on this sample |
| restore | 258 s for five bundles, `.olean` files only |
| check state | artifact 14667945776 |

**Estimate from the unit.** At 4.6 s per module the whole archive is about
224 process-hours, 56 runner-hours at four processes per runner: fourteen
hours on four runners, under five on twelve. The sample is the bottom of the
graph, where a module imports little beyond Mathlib; a module near the top
imports tens of thousands of archive modules before its replay starts, and
that cost is not measured.

### The replay chain, launched 2026-11-20 20:36Z

From check round 1 and check state 14667945776: four shards, one hundred
minutes each, four processes per runner, chained, always against the newest
build state. Four runners beside the build's twelve keeps the account at
sixteen of twenty. When a round finds nothing unreplayed it stops and waits
for the build; it is raised to twelve shards once the build has finished.

| check round | run | merged (UTC) | replayed | total | % of archive | kernel rejections | struck | mean s per module | note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 44810043854 | 20:31 | 288 | 288 | 0.16 | 0 | 0 | 4.60 | pilot, 1 shard x 8 min |
| 1 | 44812857514 | 22:19 | 18,800 | 19,088 | 10.90 | 0 | 0 | 4.12 | 4 shards x 100 min against build state 14662502720; every planned module replayed; dispatched check round 2 by itself; check state 14674692886 |
| 2 | 44828069566 | 00:15 (11-21) | 19,539 | 38,627 | 22.05 | 0 | 0 | 4.52 | against build state 14674737119; 20,956 planned, one shard stopped by its deadline; check state 14680894266 |
| 3 | 44842635028 | 02:10 | 14,133 | 52,760 | 30.12 | 0 | 0 | 6.77 | against build state 14678652610; 19,976 planned, all four shards stopped by the deadline; check state 14687215680 |
| 4 | 44854433459 | 03:50 | 17,352 | 70,112 | 40.02 | 0 | 0 | 3.89 | against build state 14683342288; every planned module replayed; check state 14690269141 |
| 5 | 44863171205 | 06:40 | 7,886 | 77,998 | 44.52 | 0 | 0 | 5.50 | against build state 14687303640; two of four shards reported, see the third incident; check state 14696455861 |
| 6 | 44876650580 | 08:38 | 16,601 | 94,599 | 54.00 | 0 | 0 | 4.80 | against build state 14694700878; 18,040 planned, one shard stopped by its deadline; all four shards reported and the watchdog (version one) killed nothing; check state 14700320734 |

### Third incident, check round 5, 2026-11-21: one stalled download held the replay chain for an hour

Two of the four shards of run 44863171205 never reported. Neither was a
kernel rejection.

- **Shard 0's runner was lost** 83 minutes into its replay, leaving no log
  and no done record. Four replay processes side by side on a 15 GB runner is
  the likeliest cause, the wall the build met in round 10; this run started
  before the watchdog existed.
- **Shard 1 never began replaying.** Its restore step started at 03:53:42Z
  and was still downloading a bundle at 06:39Z. `gh api` has no time limit,
  the job's own limit is 350 minutes, and the merge job waits for every
  shard, so the chain would have stood still until 09:41Z. Shards 2 and 3 had
  finished by 05:42Z.

Repair, commit `b4a2d279`: `fetch_artifact.sh` gives each download 900
seconds and four attempts, and counts a zip that does not list as a failure;
every artifact download in both workflows goes through it, and
`test_fetch_artifact.py` plants the hang, a truncated zip and a refusal. The
run was cancelled by hand at 06:39Z. Its merge job then folded the two shards
that had reported and dispatched check round 6 at 06:40:23Z on the repaired
code, which also carries the watchdog. Cost: about an hour of chain time and
the work of two shards, whose modules are planned again.

### The driver's memory, 2026-11-21 09:05Z: a leak inherited from upstream, fixed

Check round 6 was the first with a memory log. On shard 0, four driver
processes side by side held 0.7 GB of anonymous memory each at the start and
2 to 5.6 GB each later; the runner used all its swap and 12.7 of its 15.6 GB.
That is the likely cause of the runner lost in check round 5.

Cause: `replayFromImports`, as copied from Lean's `LeanChecker.lean`, never
unmaps the module's own `.olean`. In a process that replays one module that
costs nothing. In one that replays thousands in import order, a later module
that imports an earlier one cannot map that file at its address again, and
Lean then reads the whole file into the heap. The process ends up holding a
heap copy of most of what it has replayed.

Fix: the driver unmaps the module's own files when the module is done. One
function call added to the upstream function, marked in `ReplayDriver.lean`.
Measured in this lab's container, on Mathlib's own build outputs with the
pinned toolchain, 210 modules in one process (207 from four low
directories, then three that import them):

| | driver as it was | driver now |
| --- | --- | --- |
| modules replayed, failed, exit code | 210, 0, 0 | 210, 0, 0 |
| peak anonymous memory | 2,052 MB | 678 MB |
| anonymous memory after a module | not printed | 527 to 649 MB, flat |

The three high modules took 35.0, 51.5 and 2.8 s before and 1.5, 1.6 and
1.6 s after, but the first run also had a cold disk, so only the memory
figures are a comparison. About 0.5 GB of what remains is the Lean library
loaded twice, once by the interpreter that runs the driver and once by the
import; a compiled driver would not pay that and has not been built.

The driver now prints the anonymous memory it holds after each module, and
each round's check state keeps the twenty largest. That is the number that
will say whether the modules at the top of the graph can be replayed on a
hosted runner at all.

Check round 7 (run 44885838195) had started at 08:38Z with the old driver.
It was cancelled by hand and dispatched again with the new one, outputs in a
plain directory.
