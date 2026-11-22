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
| 15 | 44892897103 | 11:16 | 3,435 | 153,922 | 87.86 | 0 | 0 | 0 | 7.78 | one compile per runner, by a rule since removed, see below; all twelve shards reported; 3,463 planned; no suspension, no kill, largest module 5.1 GB; state artifact 14704557927 |
| 16 | 44899651298 | 12:52 | 6,300 | 160,222 | 91.46 | 0 | 0 | 0 | 9.80 | two compiles; 12,746 planned and every shard stopped by its deadline; 1,281 modules built by two shards, every pair identical; 255 of the built modules stand on 72 that no chunk holds, see below, so 159,967 are usable (91.31 percent); state artifact 14707902742 |
| 17 | 44906573935 | 14:18 | 6,229 | 166,451 | 95.01 | 0 | 0 | 0 | 11.55 | two compiles; 8,702 planned and ten of twelve shards stopped by their deadline; 857 modules built by two shards, every pair identical; 1,418 extras built and all kept; 166,449 usable (two modules of round 16 still stand on one unbuilt); no suspension, no kill, largest module 3.0 GB; a compile is now mostly its imports, see below; state artifact 14710597929 |
| 18 | 44913274901 | 15:40 | 3,280 | 169,731 | 96.89 | 0 | 0 | 0 | 21.71 | two compiles, the last round planned by source size and the last under the runner's own page-fault windows; 7,044 planned and all twelve shards stopped by their deadline; 562 modules built twice, every pair identical; nothing stranded any more; 260 million major page faults over the twelve runners, three suspensions, no kill, largest module 7.4 GB; state artifact 14713104221 |
| 19 | 44920413546 | 16:58 | 4,611 | 174,342 | 99.52 | 0 | 0 | 0 | 11.24 | the first round with the planner pricing by imports, small page-fault windows on every shard and a plan of three times capacity; 5,150 planned, four of twelve shards stopped by their deadline; 2,327 extras built, 1,603 modules built twice, every pair identical; no suspension, no kill, largest module 4.0 GB; 24 million major page faults where round 18 had 260 million; state artifact 14715757843 |
| 20 | 44927890126 | 17:49 | 823 | 175,165 | 99.99 | 0 | 0 | 0 | 15.77 | dispatched by hand and planned to 3,024 s a shard; twelve shards, every one of the 823 planned modules built, none stopped by its deadline, 44 minutes from plan to merge; 288 extras, 185 modules built twice, every pair identical (4,490 of 4,490 over the campaign); no suspension, no kill, largest module 4.4 GB; state artifact 14718047776 |
| 21 | 44932152644 | 19:27 | 22 | 175,187 | 100.00 | 0 | 0 | 0 | 311.05 | one shard, one runner, the 22 modules at the top, on a plain directory holding the outputs of all 175,165 others (101 GB, restored in 693 s); read-ahead 0 and a 4 KB fault-around window; 4,773 s of build, never suspended, largest module 2.0 GB; `Main` in 640 s; **every module of the archive is built**; state artifact 14720649806 |

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

### Round 15, 2026-11-21 11:16Z: one compile per runner, by a rule that should not have fired

Round 15 built 3,435 modules. Nothing was wrong with it except that every
runner compiled one module at a time. The hand-on step of the merge job
lowered `LEAN_NUM_THREADS` whenever a shard failed to report, on the reading
that a silent shard is a runner out of memory. Round 14's silent shard was
the restore race, seven minutes in and before any compile. The rule took 2
down to 1 and nothing ever raises it. Round 15's shards were 43 to 98
percent busy on their one worker, and round 16 was dispatched the same way
at 11:16:36Z (run 44898323934).

Removed in `29cf5de1`: the thread count is what the dispatch says, and the
watchdog deals with memory inside a round. Round 16 was cancelled by hand 16
minutes in and dispatched again at two compiles. Its plan is the first where
the filling pass does real work: about 12,700 modules planned, some 2,000 of
them built a second time on another shard, so the next state will carry the
first real count of whether a module elaborated twice comes out the same.

Cost of the two mistakes of the last three rounds, the restore race and this
rule: about one round. **Forecast after round 15:** 21,265 modules left, 49
worker-hours at round 14's rate; four rounds by simulation, `Main` built
around 16:15Z to 16:35Z.

### Round 16, 2026-11-21 12:52Z: elaboration is reproducible across runners; and the filling pass broke the state

**The measurement.** Round 16 was the first in which the filling pass did
real work. 1,281 modules were elaborated twice, on two different runners,
from the same sources against separately restored imports. The merge
compared the two `.olean` files of each: all 1,281 pairs are identical byte
for byte (sha256), none differ. With round 13's two, 1,283 of 1,283. This
is a measurement of reproducibility for those modules on this toolchain and
these runners; it is not a second kernel and says nothing of the other
173,904.

**The fault.** Round 17's plan then refused to run ("plan is not closed"),
and the chain stood still from 12:53Z to 12:59Z. A shard that took a module
through the filling pass built that module's unbuilt prerequisites too, as
extras, but packed only the modules it owned. Where the owner of an extra
ran out of its hour before reaching it, the extra was kept by nobody, and
whatever the other shard had built on top of it was recorded as built with
nothing under it: 255 modules standing on 72. The check that caught it is
the one planted for exactly this (`built_closure`); it did its job one
round late, because the planner trusted the state's list of built modules
without asking whether each could be loaded.

Fixed in `9afac704`. A shard now keeps everything it builds. Both planners
count a module as built only if everything under it is built
(`replay_plan.usable`): the 255 are planned again with what they stand on,
and a state that is not closed can no longer stop a plan. Round 17 was
dispatched by hand at 12:59Z from the same state.

**The cost.** The filling pass was meant for idle shards. Round 16 was
planned forty percent over, so by the planner's arithmetic every shard was
idle, and the pass gave them extras: 2,068 of the round's 8,368 compiles
built something a second time, while every shard ran out of its hour. The
pass now fills a shard only up to what it can really do. Round 16 built
6,300 new modules where a round without the pass would have built about
8,000.

**Forecast after round 16:** 15,220 modules left, 35 worker-hours at round
14's rate. Four rounds by simulation, 4.2 to 4.5 hours: `Main` built around
17:10Z to 17:30Z. The window given at 09:07Z ended at 16:20Z; the hour was
lost to the three faults of rounds 14 to 16, all in code written today.

### Round 17, 2026-11-21 14:18Z: a compile is now mostly its imports, and every forecast so far ignored that

Round 17 built 6,229 new modules with no failure, and the three changes of
`9afac704` held: the plan ran, every shard kept its extras, and the merge
left 2 stranded modules where round 16 left 255 (both from round 16, both
on one module that no shard reached this round either). The filling pass
built 857 modules twice, all pairs identical; with rounds 13 and 16 that is
2,140 of 2,140.

It built fewer than planned again, and this time the reason is not in the
workflow. Seconds per compile, by how many of the archive's modules the
module imports all the way down (exact counts, `replay_plan.closure_sizes`;
modules in brackets):

| imports | round 14 | round 16 | round 17 | still to build |
| --- | --- | --- | --- | --- |
| under 5,000 | 7 (2,859) | 7 (3,129) | 6 (3,233) | 2,488 |
| 5,000 to 10,000 | 7 (2,654) | 9 (1,359) | 10 (1,106) | 1,374 |
| 10,000 to 15,000 | 9 (704) | 9 (847) | 11 (615) | 1,094 |
| 15,000 to 20,000 | 14 (68) | 15 (492) | 16 (487) | 571 |
| 20,000 to 25,000 | 13 (786) | 23 (453) | 20 (707) | 1,934 |
| 25,000 to 30,000 | | 64 (12) | 36 (69) | 675 |
| 30,000 to 35,000 | | 153 (6) | 130 (9) | 440 |
| 35,000 to 40,000 | | | 190 (1) | 75 |
| 40,000 to 50,000 | | 215 (2) | 197 (2) | 60 |
| 50,000 to 60,000 | | | | 10 |
| over 60,000 | | | | 17 |

Before it elaborates a line, `lean` maps the `.olean` of every module under
the one it compiles. Two shards' memory logs give the resident file-backed
memory of a compile as 4.9 to 6.1 GB (Mathlib) plus 0.29 to 0.31 GB per
thousand archive modules imported. A runner keeps about 11 GB of file pages.
A module on 20,000 others just fits; past that every start reads from disk
what the last one pushed out, two compiles push each other's out, and the
runners' disks are the limit: shard 9 took 11.7 million major page faults
in its hour. Nothing was suspended or killed, and `MemAvailable` never fell
under 10.8 GB, because it counts those pages as free. The machine was one
of the cheaper cases: shard 7 ran on an AMD EPYC 7763 instead of the Xeon
6975P-C of the other shards seen so far and compiled 333 modules in the hour
where shard 9, on similar work, compiled 537.

What is left is the top of the archive. 602 of the 8,738 modules import
30,000 or more. The 585 of them under 60,000 are 24 of the 55 worker-hours
that everything under 60,000 costs at round 17's prices. The other 17
import more than 60,000, the last five 175,174 or more, and they form one
chain up to `Main`. Nothing built so far imports more than 48,140, so what
those 17 cost has not been measured.

**Correction to every forecast above.** They priced a module by the length
of its source, 4 s plus about 1 s per KB, fitted on the rounds before. That
model puts the 8,738 modules left at 24 worker-hours; by import count they
are 55, before the 17. The window given at 13:02Z (`Main` at 17:10Z to
17:30Z) is wrong by hours, and so is the planner that used the same model:
it gave a shard of such modules about twenty times what it could do, the
deadline cut it off, and what stood above waited a round. By simulation on
the state after round 17 (the planner's own functions, shards paying the
prices in the table, 60 minutes a round) that planner needs 16 more rounds
if the cost above 50,000 imports grows in proportion to the count and 21 if
with its square.

Changed in `f918390d`: the planner prices a module by what it imports
(`replay_plan.import_cost`: seconds = a value per 5,000 imports, fitted on
the last two rounds and never falling, plus a rate per KB). The same
simulation gives 7 rounds in the first case and 12 or 13 in the second.
Round 18 was planned before the change; round 19 is the first with it.

**Two measurements running**, each on one more runner (17, then 18 in all
for about an hour):

- Run 44914862924, dispatched 14:37Z (`39652852`): the verdict job's
  restore of all 166,449 loadable modules on the compressed volume, then
  `lean` on files that hold nothing but imports, over 45,128, 80,111 and all
  166,449 modules: cold, warm, and with the volume's read-ahead at 128 KB
  instead of its own 4 MB. This is what one of the last modules pays, and
  what the verdict's axiom printout pays to load `Main`.
- A probe job, dispatched 14:48Z (`ffbb14e5`): the same two smaller imports
  on a plain directory, as a build shard has it, under the runner's own
  settings and under small page-fault windows (read-ahead 16 KB instead of
  128, fault-around one page instead of 64 KB). On a fault in a mapped file
  the kernel reads a window around the page and maps what is in memory
  around it, so an imported `.olean` costs memory for far more than `lean`
  looked at. If small windows let 45,000 modules stay in memory, the 602
  cost a fraction of the table. `d4aba210` adds the same setting to the
  build shards behind a switch (`IO_TUNE`), off until this is measured.

**Forecast, with what was known at 14:50Z:** three more rounds for the wide
part once the new planner is in (to about 19:30Z), then the chain of 17 on
one runner, 3 to 7 hours by the two extrapolations. `Main` not before about
22:30Z, more likely after 00:00Z on the 22nd, unless a probe finds the
imports can be made cheap. The next section is what the probe found.

### The import probe, 2026-11-21 15:32Z: small page-fault windows make a 45,000-module import fit in memory

Run 44916286894 (the 14:48Z run was cancelled and dispatched again at
14:54Z so that the first comparison is uploaded by itself). One runner, AMD
EPYC 9V74, 15 GB, an NVMe disk with ext4; the `.olean` files of 80,111
modules restored into a plain directory (43 GB, 542 s). `lean` on a file
that holds nothing but imports, 45,128 modules in all, six times:

| read-ahead | fault-around | cache | wall s | user s | system s | peak resident MB | major faults | disk reads | MB read |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 128 KB | 64 KB | cold | 415.5 | 10.6 | 40.6 | 11,520 | 874,288 | 1,480,945 | 71,669 |
| 128 KB | 64 KB | warm | 298.3 | 10.7 | 38.5 | 12,159 | 782,175 | 1,472,449 | 59,028 |
| 128 KB | 64 KB | warm | 308.1 | 10.7 | 36.6 | 12,609 | 678,182 | 1,424,967 | 51,557 |
| 16 KB | 4 KB | cold | 350.0 | 10.1 | 20.6 | 8,504 | 679,418 | 1,180,665 | 13,830 |
| 16 KB | 4 KB | warm | 28.6 | 8.4 | 9.8 | 8,510 | 2,250 | 14,862 | 190 |
| 16 KB | 4 KB | warm | 19.4 | 8.4 | 10.3 | 8,510 | 207 | 1,116 | 14 |

The first three rows are the runner as it comes, and they are what the build
shards have been paying. The import needs about 20 s of processor. The rest
of five minutes is the disk: 52 to 72 GB read for an import whose archive
files are about 24 GB in all (0.54 MB a module here), the same pages read
again and again, because what the kernel maps around each fault does not
fit in memory and is pushed out before `lean` returns to it. A warm cache
does not help; there is no warm state to reach.

With the windows small the same import keeps 8.5 GB resident, the first run
reads 14 GB (one read per fault, about 3,400 a second for the whole run,
which looks like this disk's limit, so the cold run is no faster than
before), and every run after it finds everything in memory: 29 s, then 19
s. Fifteen times faster on this runner, for a setting that changes nothing
`lean` computes.

**What I did with it, including the wrong turn.** `d4aba210` had put the
setting behind a switch in the build job (`IO_TUNE`, `io_tune.sh`). At
15:01Z I set it for the odd shards of round 19 as a comparison. At 15:28Z
and 15:32Z, with the probe's six runs past twenty minutes and no result
readable, I took the slow runs to be the small windows, narrowed the
comparison to three shards and then turned it off. The slow runs were the
runner's own settings. The result arrived at 15:36Z and the switch went to
every shard at 15:37Z (`IO_TUNE: "all"`), before round 19 was dispatched.
With it, two more changes for that round:

- The plan goes further over a shard's capacity (`PLAN_OVER` 3.0,
  `FILL_OVER` 2.5, where 1.4 and 1.0 stood). The planner's prices are the
  last two rounds', which paid the old price; a shard planned to 1.4 times
  its capacity at those prices would be done in half its hour.
- A shard keeps a plain directory up to 115,000 imported modules, where the
  limit was 90,000. The small windows only work there: on the compressed
  volume a fault reads a whole 128 KB extent whatever window is asked for.

Not measured yet: two compiles at once under the setting, runners with a
slower disk (the cold run is bound by operations per second), the 80,111
import (second part of the same run), and anything on the compressed
volume, where the last modules must be built because 175,187 modules do not
fit a runner's disk uncompressed. Round 19's own timings will show the
first two.

### Round 18 and the dispatch of round 19, 2026-11-21 15:40Z

Round 18 was planned before `f918390d` and ran before the switch: 3,280
modules for twelve runner-hours, 21.7 s per compile where round 17 paid
11.6, and 260 million major page faults. It is the round the table in the
section on round 17 predicts. It leaves 5,456 modules: 1,094 import 25,000
or more, 17 more than 60,000.

Round 19 (run 44920413546, dispatched 15:40Z on `d24ef946`) is the first
with all of: the planner pricing by imports (fitted on rounds 17 and 18: 4,
7, 11, 16, 19, 59, 116 s for 0 to 35,000 imports, 0.52 s per KB), the plan
taken to three times a shard's capacity at those prices, small page-fault
windows on every shard, and a plain directory up to 115,000 imported
modules. Its plan, reproduced here from the state: 5,150 modules owned and
2,436 extras on twelve shards, 2,015 of them planned for two shards, 306
left waiting; the largest shard imports 105,534 modules, the highest
planned module 100,723. What waits is the top: 13 modules importing 79,669
to 175,187, and what stands between.

A third probe, run 44920814617 dispatched 15:44Z (epoch `p1x` so that it
runs beside the second), restores the `.olean` files of all 169,731 built
modules into a plain directory, after removing the parts of the runner
image the job does not use, and imports all of them under small windows and
under no read-ahead. That is the case of the last nine modules and of the
verdict's axiom printout.

### What the two older probe runs had when they were stopped, 2026-11-21 15:54Z

Both were cancelled at 15:54Z: the account was at its limit of twenty jobs
(twelve build shards, four replay shards, three probes, and the
repository's own nightly suite), a job that reports the runners' disks had
been waiting six minutes, and what these two still had to run was known in
kind. A cancelled job still uploads its evidence.

**The 80,111-module import on a plain directory, small windows** (run
44916286894, second part, same runner as the table above):

| cache | wall s | user s | system s | peak resident MB | major faults | disk reads | MB read |
| --- | --- | --- | --- | --- | --- | --- | --- |
| cold | 569.0 | 16.3 | 37.1 | 9,450 | 1,399,604 | 2,092,247 | 24,549 |
| warm | 82.3 | 14.4 | 19.5 | 10,087 | 121,070 | 191,059 | 1,935 |
| warm | 35.8 | 13.6 | 17.5 | 10,193 | 438 | 14,941 | 188 |

From 45,128 to 80,111 modules the resident set grows by 1.7 GB: 48 KB a
module, on about 6.3 GB for Mathlib and `lean` itself. By that line the
import of all 175,187 would hold about 14.7 GB, against the 13 GB or so a
runner keeps for file pages: close, and not measured. The runs it had not
reached (the same import as the runner comes, each setting by itself, no
read-ahead) are not needed for the decision made at 15:37Z.

**The 166,449-module import on the compressed volume, as the verdict job
would run it** (run 44914862924; the restore took 575 s and the build over
3,355 built sinks found 155,508 modules up to date and elaborated none, in
137 s, for the third time). `lean` on the file importing everything, btrfs
with zstd through a loop device with direct I/O, the volume's own
read-ahead of 4 MB: stopped by the probe's limit after 2,400 s, not done,
with 457 GB read from the disk. The second run was eighteen minutes in when
the job was cancelled.

That is a finding about the verdict job, not about the archive: as
written, its axiom printout would import `Main` three times on that volume
and might not finish. The same holds for the last nine modules, which
import 146,663 and more and cannot be given a plain directory by the rule
of 115,000. The compressed volume was the answer to a disk too small for
the archive; it is the wrong answer to a memory too small for an import.
What replaces it for the top is being measured: run 44920814617 (everything
on a plain directory after a further cleanup, small windows), and a job on
three runners that reports their disks and whether f2fs or zfs can be
mounted (run 44921139865).

### What the runners have, and what follows for the top, 2026-11-21 16:00Z

Run 44921139865 asked three runners. Two answered before a mistake of mine
in the job's second step ended it (a `du` over paths that do not all exist,
under `pipefail`); the third step, which would have tried f2fs and zfs, did
not run and is not needed now.

| runner | disk | free as it comes | after the usual cleanup | after the further cleanup |
| --- | --- | --- | --- | --- |
| Xeon Platinum 8573C, kernel 7.0.0-1017-azure | sda, 150 GB, ext4 | 86 GB | 111 GB (84 s) | 130 GB (67 s more) |
| kernel 7.0.0-1014-aws, `/dev/mapper/cow-root` | 145 GB, ext4 | | 114 GB (93 s) | 133 GB (69 s more) |

The further cleanup removes parts of the runner image no step of these
workflows uses (`/opt/hostedtoolcache`, Swift, Julia, the JVMs, PowerShell,
browsers, cloud command lines and the like). Both kernels can load btrfs,
f2fs, zfs and erofs.

The outputs of all 169,731 modules built so far are 102.7 GB, 0.61 MB a
module; all 175,187 will be about 107 GB. So after the further cleanup a
runner holds the whole archive uncompressed, with Mathlib and the toolchain
beside it and 8 to 15 GB to spare. Changed accordingly:

- Build shards (`4cf89301`): the further cleanup, and a plain directory
  whenever the free space holds what the shard imports
  (`build_volume.sh ... disk`); one bundle in flight above 115,000 modules.
- The verdict (`e7648bae`): three jobs. One restores everything and runs
  `lake build`, which must find nothing to do. One runner per question
  prints the axioms of one theorem of `Main.lean` (or the four interior
  statements, or measures the cone) from a plain directory with small
  windows. A last job puts the five answers side by side and applies the
  guard; it was tried here on stand-in answers with a missing answer, an
  error in place of an answer, `sorryAx`, a foreign axiom, another
  theorem's line and a failed build job planted, and refused each.
- A shard may build ninety minutes past the hour its plan is sized by
  (`DEADLINE_EXTRA_MIN`), so that the deadline does not cut the last
  modules off mid-import round after round.

Run 44922636081 (dispatched 16:05Z) rehearses the three verdict jobs on
what is built: the build job on all 169,731 modules, the axioms jobs on
`SelfIntersectionVolumeEstimates.topCovolSlim2_use`, the theorem of the
built module that imports most (48,140).

### Fourth rehearsal, 2026-11-21 16:05Z to 16:23Z: the verdict's jobs on plain directories

Run 44922636081, on two runners of the kind with kernel 7.0.0-1014-aws
(Xeon 6975P-C, 132 GB free after the cleanup).

**The build job.** 122,533 MB were free once the toolchain and Mathlib were
in place, room for 184,730 modules by `build_volume.sh`'s arithmetic, so a
plain directory. All 169,731 modules restored from 19 bundles in 607 s,
two bundles in flight; the disk then stood at 122 GB used and 24 GB free,
which makes the outputs 97 GB, 0.57 MB a module. `lake build` over the
2,212 built modules that nothing built imports: exit code 0 in 102 s, no
module elaborated, 137,939 found up to date. The whole archive, 5,456
modules more, will leave about 20 GB.

**The axioms job.** 48,140 `.olean` files restored in 261 s, the small
windows set, then one `lean` on

    import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.HilbertSamuelApplications.TopCovolSlim2Use
    set_option maxHeartbeats 0
    #print axioms SelfIntersectionVolumeEstimates.topCovolSlim2_use

which printed, in 110 s including the import, holding 853 MB at most:

    'SelfIntersectionVolumeEstimates.topCovolSlim2_use' depends on axioms: [propext, Classical.choice, Quot.sound]

This is the first axiom printout from the archive in this campaign. It is
about one theorem a quarter of the way up, chosen because its module is the
built one that imports most, and it says what it says: that theorem rests
on no axiom beyond the three standard ones and on no `sorry`, by Lean's own
walk over everything it uses, in the modules as these runners elaborated
them. It is not the verdict and says nothing about `Main`.

**The cone job and the summary.** On a third runner (kernel
7.0.0-1017-azure, NVMe): the same 48,140 files restored in 253 s, then
`Cone.lean` compiled and run on that module and theorem, exit code 0 in
571 s. Of the 48,140 archive modules the theorem's module imports, 28,389
hold a constant the theorem rests on (59 percent); of their 772,401
declarations, 226,315 (29 percent); of their 597,004 theorems, 187,643 (31
percent). 404,665 constants in the cone with Mathlib's. The summary job
found both answers and listed them; the run ended green at 16:38Z.

So every job of the verdict has now run once on real outputs, on plain
directories, on both kinds of runner. What has not run is the summary's
guard on real answers for the five theorems; it was tried on stand-ins.

### The import of everything built, on a plain directory, 2026-11-21 16:33Z

Run 44920814617, first part. One runner (AMD EPYC 9V45, NVMe, ext4), 129 GB
free after the further cleanup; the `.olean` files of all 169,731 built
modules restored in 607 s (86 GB), 32 GB left. `lean` on a file that
imports all of them through the 2,212 built modules nothing built imports,
read-ahead 16 KB, fault-around 4 KB:

| cache | wall s | user s | system s | peak resident MB | major faults | disk reads | MB read |
| --- | --- | --- | --- | --- | --- | --- | --- |
| cold | 737.4 | 25.9 | 76.4 | 8,547 | 3,792,591 | 4,983,932 | 59,744 |
| warm | 583.7 | 26.3 | 70.3 | 8,862 | 3,122,896 | 4,062,165 | 47,362 |
| warm | 570.3 | 26.1 | 67.6 | 8,837 | 3,020,269 | 3,922,466 | 45,894 |

Three things. The import works: `lean` loads 169,731 modules of the archive
together with Mathlib, exit code 0, holding 1.4 GB of its own at most. So
nothing in the archive so far clashes with anything else in it when all of
it is in one environment, which is what `Main` will ask for.

It does not fit in memory at this setting. By the line through the 45,128
and 80,111 imports it would want about 14.5 GB resident and the runner
keeps 12; each run reads 46 to 60 GB for it, each page about four times
over, and the warm runs are no better than the cold one. Ten minutes an
import on this runner, whose disk gave 6,800 reads a second; on a runner
giving 3,400, twenty.

And it is still the difference between a result and none: on the
compressed volume the same import was stopped after forty minutes.

The last nine modules import 146,663 and more, one after the other, so at
this setting they are an hour and a half to three hours of imports.

**The same import with no read-ahead** (one 4 KB page per fault; second
part of the run, 16:51Z):

| cache | wall s | user s | system s | peak resident MB | major faults | disk reads | MB read |
| --- | --- | --- | --- | --- | --- | --- | --- |
| cold | 661.0 | 26.1 | 57.0 | 13,193 | 4,234,004 | 4,546,960 | 17,925 |
| warm | 207.9 | 24.8 | 38.3 | 13,257 | 1,049,577 | 1,154,806 | 4,810 |
| warm | 232.4 | 24.7 | 40.3 | 13,284 | 1,290,574 | 1,363,673 | 5,365 |

My guess that it would fit was wrong: the cold run faults 4.2 million
single pages, 17 GB that `lean` really reads, about 100 KB a module at this
height and not the 48 KB of the two smaller imports. But a warm import is
now three and a half to four minutes and reads 5 GB, where at 16 KB it was
ten and read 46. `IO_TUNE_RA_BIG_KB` is set to 0: a build shard that
imports more than 110,000 modules, and each of the verdict's axioms jobs,
runs with no read-ahead. For the last nine modules that is about eleven
minutes for the first import and four for each after it on a disk like
this one, and about twice that on the slower kind.

### Round 19, 2026-11-21 16:58Z: what the small windows do on twelve runners

4,611 modules, 99.52 percent in all, no failure, 845 left. Seconds per
compile by how many modules the module imports (modules in brackets):

| imports | round 17 | round 18 | round 19 |
| --- | --- | --- | --- |
| under 5,000 | 6 (3,233) | 9 (1,310) | 7 (930) |
| 5,000 to 10,000 | 10 (1,106) | 11 (413) | 7 (898) |
| 10,000 to 15,000 | 11 (615) | 19 (298) | 8 (710) |
| 15,000 to 20,000 | 16 (487) | 35 (89) | 11 (439) |
| 20,000 to 25,000 | 20 (707) | 25 (986) | 14 (896) |
| 25,000 to 30,000 | 36 (69) | 75 (124) | 13 (386) |
| 30,000 to 35,000 | 130 (9) | 117 (59) | 19 (280) |
| 35,000 to 40,000 | 190 (1) | | 14 (50) |
| 40,000 to 50,000 | 197 (2) | | 19 (18) |
| 50,000 to 60,000 | | | 18 (2) |
| over 60,000 | | | 148 (2) |

Round 19 is the first under read-ahead 16 KB and fault-around 4 KB, on
every shard, with two compiles at once, on whatever runners the fleet
handed out. A module on 30,000 to 50,000 others costs what one on 20,000
did, where it had cost seven to ten times that. The probe's single-runner
result holds in production. 1,603 more modules were built on two runners
and all pairs agree: 4,305 of 4,305 over the campaign.

**Round 20, dispatched twice.** The chain dispatched it at 16:58Z (run
44927486409) with the plan at three times capacity, and with only 845
modules left, priced at 17,443 s, that plan was a single cluster: one
runner for everything up to `Main`, eleven idle, two to three hours. I
cancelled it at 17:03Z and dispatched round 20 again (run 44927890126) on
`80e4db83`, planned to 3,024 s a shard: 823 modules over twelve shards, 22
waiting, by the plan reproduced here from the state. The 22 are the top:
they go to one shard in round 21, which runs with no read-ahead and may
build for 150 minutes.

### Round 20 and the last round, 2026-11-21 17:49Z

Round 20 built what it was given: 823 modules, 99.99 percent in all, no
failure. 22 modules are left, a tangle at the top that ends in `Main`: nine
that import 41,841 to 55,728 modules, then 61,081, 66,168, 79,669, 112,385,
151,286, 157,603, 157,604, 170,702, and the last five at 175,174 to
175,187.

Round 21 (run 44932152644, dispatched by the chain at 17:49Z on
`0fcfa13d`) is one shard with all 22. Its job restored the outputs of all
175,165 built modules in twelve minutes, one bundle at a time, and
`lake build` started at 18:05:55Z. By the probe of 16:33Z the modules at
the very top are an import of eleven minutes or more for the first and
about four for each after it on a fast disk, twice that on a slow one, so
`Main` is expected between 19:00Z and 19:40Z; the shard may build until
20:35Z. When `Main` is built the merge dispatches the verdict.

### Round 21, 2026-11-21 19:27Z: `Main` is built and the build is complete

All 175,187 modules of the archive have elaborated on GitHub-hosted
runners, with the archive's own toolchain (`leanprover/lean4:v4.33.1`) and
its pinned Mathlib (`0df444a360eaa60ab8c11dca51a86af692955474`). Over the
22 rounds: 0 modules failed, 0 crashed, 0 `declaration uses 'sorry'`
warning lines, 0 modules rebuilt outside their shard. 4,490 modules were
elaborated on two different runners and every pair of `.olean` files is
byte-identical. 174,986 modules carry a recorded compile time (201 do
not: 200 of the 491 of pilot round 0 and one from round 18);
the recorded times sum to 1,783,871 s, 495.5 hours. The final state is
artifact 14720649806.

This says that Lean's elaborator and kernel accepted every module once, in
shards, with outputs carried between runners as artifacts. It says nothing
about the mathematics, and nothing about whether the statements in
`Main.lean` are the ones their names suggest. The axioms those statements
rest on are the verdict's question, below; a second kernel pass over the
stored outputs is the replay chain's.

Round 21 itself was one job on one runner (4 cores, 15 GB, Xeon 6975P-C,
kernel 7.0.0-1014-aws). After the further cleanup the runner had 122,382 MB
free, room for 184,487 modules by the 620 KB rule, so the outputs went to a
plain directory: 21 bundles and 221 chunks in 693 s, one bundle at a time,
101 GB on disk and 20 GB left. `io_tune.sh` set the read-ahead from 128 KB
to 0 (the rule for more than 110,000 imported modules) and the fault-around
window from 65,536 to 4,096 bytes. `lake build` ran 4,773 s and exited 0,
well inside its deadline. The watchdog never stopped or killed a process:
at most 9,707 MB in use on the machine, 2,049 MB in the largest `lean`.
62.3 million major page faults, 6.3 million pages written to swap.

| imports (itself included) | compile s | largest resident anonymous MB | module (last component) |
| --- | --- | --- | --- |
| 41,841 | 111 | 900 | `AllStagesAtMemberOfSpecializations` |
| 43,137 | 112 | 922 | `PointwiseGaloisPropertiesOfLocalInputs` |
| 43,212 | 15 | 924 | `PreAtMem` |
| 45,505 | 260 | 958 | `GeometricRealizationOfWeightOne` |
| 45,860 | 42 | 947 | `WeightOneGeometricRealization` |
| 47,538 | 25 | 934 | `ThetaLiftHypothesesOfNonvanishing` |
| 48,123 | 19 | 999 | `CFinal` |
| 51,387 | 26 | 984 | `ExistsBaseLatticeOfPrime` |
| 55,728 | 23 | 1,041 | `MemberBundlesLargeUnramifiedExponents` |
| 61,081 | 43 | 1,092 | `GaloisRepresentationsOfThetaLift` |
| 66,168 | 21 | 1,105 | `RowSrc` |
| 79,669 | 253 | 1,213 | `HypothesesNonemptyOfUnramifiedExponents` |
| 112,385 | 395 | 1,545 | `SiegelEisensteinSecondTermHypotheses` |
| 151,286 | 560 | 1,852 | `EveryCharacterOfLiteratureOfVWin` |
| 157,603 | 646 | 1,548 | `TopMainZj` |
| 157,604 | 761 | 1,930 | `VwinOfRow` |
| 170,702 | 619 | 2,049 | `CorGKOf` |
| 175,174 | 619 | 1,962 | `CharacterBoxes.MainConclusion` |
| 175,179 | 682 | 1,815 | `Supplements.Kernels.MainTheorems` |
| 175,183 | 528 | 1,888 | `Supplements.Kernels.MainTheoremsCritical` |
| 175,185 | 443 | 2,039 | `Supplements.Kernels.MainTheoremsAll` |
| 175,187 | 640 | 2,036 | `Main` |

Against the forecast. The probe of 16:33Z measured an import of everything
built at 661 s from a cold cache and 208 to 232 s after that, with a
read-ahead of 0. In the real build every module above 150,000 imports took
443 to 761 s, near the cold price each time and not the warm one. Two
compiles ran at once for about half of the round (73 of 159 half-minute
samples), the runner's 3 GB of swap was full from the seventh minute on,
and each real module also elaborates and writes its outputs, which an
import-only file does not; how those seconds divide between the import and
the rest was not measured.
`Main` was forecast for 19:00Z to 19:40Z and the build ended at 19:25Z.

The merge found `Main` built and dispatched the verdict: run 44941044062
at 19:27:37Z on `af44b45e`, from state 14720649806. One job restores every
output and `lake build` must find nothing left to do; seven more each
import `Main` on a runner of their own, one per theorem of `Main.lean`, one
for the four interior statements and one for the dependency cone.

### The verdict, 2026-11-21 20:07Z, run 44941044062

On `af44b45e`, from state 14720649806. Every job ran on a hosted runner of
its own: 4 cores, 15 GB.

**The build job.** 122,529 MB free after the cleanup, so a plain directory.
22 bundles and 222 chunks restored in 631 s, two bundles at a time: 175,187
`.olean` files on disk. `lake build` of every default target then exited 0
in 198 s with `Build completed successfully (183903 jobs).` and elaborated
no module. Its log is what Lake replays from the stored logs of the 104,066
modules whose compile printed anything: 2,330,552 lines, none an error and
none containing `sorry` in any letter case. Artifact 14722476517.

**The five theorems of `Main.lean`, and four interior statements.** Each
job restored the `.olean` files of the 175,187 modules `Main` imports,
itself included, set the read-ahead to 16 KB and the fault-around window to
4 KB, and ran `lake env lean --tstack=400000` on a file of `import Main`,
`set_option maxHeartbeats 0` and one `#print axioms` per name. The file for
`riemannHypothesis` also asks `#check (riemannHypothesis :
RiemannHypothesis)` and `#print RiemannHypothesis`.

| question | restore s | `lean` s | largest `lean`, MB | artifact |
| --- | --- | --- | --- | --- |
| `riemannHypothesis` | 1,165 | 482 | 1,365 | 14723105904 |
| `riemannZeta_eq_zero_re` | 559 | 469 | 1,363 | 14722197330 |
| `LFunction_ne_zero_of_half_lt_re` | 1,040 | 468 | 1,367 | 14722518197 |
| `LFunction_eq_zero_re` | 1,524 | 482 | 2,043 | 14722648794 |
| `LFunction_eq_zero_re_of_isPrimitive` | 555 | 461 | 1,367 | 14722521880 |
| `interior` | 1,095 | 480 | 1,364 | 14722971548 |

The restores differ by runner, 555 s to 1,524 s for the same files; the
import and the walk took 461 s to 482 s on every one. All six exited 0.
What Lean printed, whole and unedited, the five theorems in the order of
`Main.lean`:

```
riemannHypothesis : RiemannHypothesis
def RiemannHypothesis : Prop :=
∀ (s : ℂ), riemannZeta s = 0 → (¬∃ n, s = -2 * (↑n + 1)) → s ≠ 1 → s.re = 1 / 2
'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
'riemannZeta_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_ne_zero_of_half_lt_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'LFunction_eq_zero_re_of_isPrimitive' depends on axioms: [propext, Classical.choice, Quot.sound]
```

and for the interior statements:

```
'Deduction.zeroFree_of_rpow_window' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpperTheory.Comparison₂.formB' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpperTheory.FinalTheorems.everyCharacter' depends on axioms: [propext, Classical.choice, Quot.sound]
'UpperTheory.V.SmallClassNumbers.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**What this is.** Lean 4.33.1 elaborated all 175,187 modules, each once,
and its kernel accepted every declaration it was given; with every module
loaded, the axiom walk from each of the five theorems reaches `propext`,
`Classical.choice` and `Quot.sound` and no other axiom. No `sorryAx`, no
`Lean.ofReduceBool`, no axiom of the archive's own. The statement of the
first theorem is the constant `RiemannHypothesis`, and Lean prints that
constant's definition as above. Whether this is the repository's third
rung, kernel-checked, for these five statements waits on limits 2 and 3
below: a composite claim takes the grade of its weakest step.

**What it rests on, checked the same hour.**

- *Mathlib.* The pinned commit `0df444a360eaa60ab8c11dca51a86af692955474`
  is the tag `v4.33.1` of `leanprover-community/mathlib4`. It is not on
  `master`: it is one commit, "chore: bump toolchain to v4.33.1" of
  2026-08-21, on top of `db584cd6`, "chore: bump toolchain to v4.33.0
  (#42604)", which is on `master`, and the two differ in `lean-toolchain`
  alone (a treeless clone of the official repository at 20:06Z, `master` at
  `a495318f`). The definition printed above is the one at lines 185 and
  186 of `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` at that tag, whose
  docstring calls it "A formal statement of the **Riemann hypothesis**". The other
  eight packages of the manifest are under `leanprover-community` and
  `leanprover`.
- *The package file.* `lakefile.toml` passes `--tstack=400000` to `lean`
  and sets `autoImplicit`, `relaxedAutoImplicit`, `maxSynthPendingDepth`,
  `pp.unicode.fun`, `maxHeartbeats` and, for one library,
  `synthInstance.maxHeartbeats`. Nothing in it concerns the kernel.
- *The statements.* `Statements.lean` is 783 bytes, imports `Mathlib` and
  nothing else, and defines the other four statements with no notation of
  its own; `Main.lean` is 433 bytes and opens no namespace.

**The text of the archive, 175,187 files.** Text is not the check (the
second pass and the cone are); it is what a reader would look for first.

| files | containing |
| --- | --- |
| 0 | `sorry`; a declared `axiom`; `native_decide`; `ofReduceBool`, `trustCompiler`; `skipKernelTC` or any `debug` option, as text or as a name; `unsafe`; `implemented_by`; `extern`; `initialize`; `#eval`; `command_elab`, `elab_rules`, `macro_rules`, `syntax`; `withOptions`, `setOption`; `addDeclCore`, `WithoutChecking` |
| 1 | `addDecl`: `CutCptCopy.lean` defines a command `cpt_copy_thms` that copies definitions and theorems under new names, through `addDecl`, which is the kernel |
| 5 | `run_cmd`, all in `BuildAid/`: each adds one name to the deny list of Lean's library suggestions |
| 3 | an `elab`, four in all: two tactics, `kcopy` and `kexactB`, and two commands, `#kcopy_probe` and `cpt_copy_thms` |
| 55 | a `macro`; all tactics but five local term macros |
| 952 | a notation, most of them `local`; none names `RiemannHypothesis`, `riemannZeta`, `LFunction`, `DirichletCharacter` or `IsPrimitive` |

`set_option` appears in 75,197 files, with 33 distinct options: heartbeat
and instance-search limits, linters, `autoImplicit`,
`backward.isDefEq.respectTransparency`, `allowUnsafeReducibility` (37
files, which permits changing a reducibility attribute and nothing in the
kernel) and the like. None is a `debug` option.

**The limits.**

1. One kernel. Nothing here is a second implementation of the type
   checker, and a soundness bug in Lean 4.33.1's kernel would pass every
   job above and the second pass too. What is known about that kernel is
   set out under "Limit 1 in detail" below.
2. The build was cut into shards and its outputs carried between runners
   as artifacts. 4,490 modules were built twice, on different runners, and
   every pair of outputs is identical. The second pass, which sends every
   stored declaration through the kernel again, stood at 145,947 modules,
   83.31 percent, with no rejection when these lines were printed.
   *Closed 2026-11-22 03:37Z.* The second pass finished: 175,187 of
   175,187 modules, no rejection, each replayed from the artifact these
   jobs restored it from ("The second pass is complete" under "Second
   pass: kernel replay").
3. `#print axioms` and `#check` run inside the environment they describe.
   A module of that environment can replace a command or a notation, and
   `test_replay_check.py` builds one that does. The text above shows no
   such thing, and text is not the check: run 44943756336 asked the same
   questions of the stored terms with a program that runs none of the
   archive's commands, and got the same answers ("The walk of the stored
   terms" below). This limit is closed.
4. Mathlib's own `.olean` files come from Mathlib's cache and are replayed
   by neither pass.
5. Nothing here is a statement about the mathematics, or about whether a
   person can follow the argument. `Mathlib`'s `RiemannHypothesis` is the
   statement its authors and reviewers take to be the Riemann hypothesis;
   that it is, is their claim and is not checked here.

Still running when this was written: the cone job of this run, started
19:52:59Z, and after it the summary job with its guard.

**The grade, 2026-11-22 04:45Z.** Limits 2 and 3 are closed, so the
sentence left open under "What this is" can be finished. On this
repository's ladder the five statements of `Main.lean` stand at the third
rung, kernel-checked: they are theorems of Lean 4.33.1 over Mathlib at its
tag `v4.33.1`, from `propext`, `Classical.choice` and `Quot.sound`.
*Pending external verification.* The steps, and the grade of each:

- Lean 4.33.1 elaborated every one of the archive's 175,187 modules with no
  error and no `sorry`, its kernel accepting each declaration as it was
  made (the build, rounds 0 to 21).
- Every stored declaration of every module went through that kernel a
  second time, read from the `.olean` files by a program that runs none of
  the archive's code, with no rejection (the second pass, rounds 0 to 17).
- Read from the stored terms by a program that runs none of the archive's
  commands, the five theorems rest on the three standard axioms and no
  other, and the first is a proof of the constant `RiemannHypothesis` that
  Mathlib defines (run 44943756336).

Each is the third rung by this repository's definition of it, whose own
Lean arm is checked by one kernel and takes Mathlib's `.olean` files from
Mathlib's cache. So the rung says no more than that: one kernel, twice.
What it does not include, and what the footnote stands for:

- No second kernel has finished and no external checker or `comparator`
  has been run (limit 1). The lean4lean pass stood at 59,426 of 175,187
  modules with no rejection when this was written ("Third pass" below);
  it is a second route, not an independent one.
- Mathlib's own `.olean` files were replayed by neither pass (limit 4).
- Limit 5 as written: this grades five Lean statements. That the first
  says what mathematicians mean by the Riemann hypothesis is Mathlib's
  reading, and whether the argument can be followed, shortened or
  explained is not touched by any of it.

**The cone and the summary, 20:35Z.** The cone job exited 0 after 2,495 s
(artifact 14724395088), and the summary job found all seven answers, the
build job green and five axiom lines, each its own theorem's and each the
three standard axioms: the guard passed and the run ended green (artifact
14723384776). What the theorems rest on, counted by `Cone.lean` as it was
at `af44b45e`:

| roots | constants in the cone | archive modules (percent) | archive declarations (percent) | archive theorems (percent) |
| --- | --- | --- | --- | --- |
| `riemannHypothesis` | 1,478,219 | 146,437 of 175,187 (83.6) | 1,265,256 of 1,905,921 (66.4) | 1,075,015 of 1,548,655 (69.4) |
| all five | 1,478,243 | 146,440 of 175,187 (83.6) | 1,265,279 of 1,905,921 (66.4) | 1,075,031 of 1,548,655 (69.4) |

By library, for `riemannHypothesis`: Development 842,309, Formalism 278,273, Mathlib 203,035, GroundTheory 76,752, ReciprocityTheory 47,612, CompanionTheory 15,717, Init 9,662, PositivityTheory 4,276, Lemmata 314, Batteries 253, Std 9, Aesop 3, Supplements 2, Main 1, Lean 1. No name was missing from the
environment.

So the proof of the first theorem mentions, directly or through what it
uses, 84 of every 100 modules of the archive and two of every three of its
declarations; 28,750 modules hold nothing it rests on. The four
statements about Dirichlet L-functions add 3 modules and 23 declarations
to that: the five theorems are one proof. The note that came with the
archive expects the argument to be "massively simplified". This count says
that it will not be by deleting what is unused: most of what is there is
used. It says nothing about how much of it a shorter argument would need.

**The walk of the stored terms, 21:04Z, run 44943756336.** Mode `rehearse`
on `Main`, on `b5d8c520`, the first commit with the extended `Cone.lean`. It
ended green: its build job restored all 175,187 outputs again and found
nothing to build, its axioms job printed the five lines again from one
import (artifact 14723701380), all five reading `[propext,
Classical.choice, Quot.sound]`, and its cone job exited 0 after 2,552 s
(artifact 14724543673). The cone job loads the `.olean` files and reads
terms; it elaborates nothing and runs no command, notation or macro of the
archive.

- Axioms in the cone of `riemannHypothesis`, and in the cone of all five:
  `Classical.choice`, `Quot.sound`, `propext`. No other, and no name the
  environment lacks.
- The statements as stored:

  | root | kind and module | its statement is the constant | which is defined in |
  | --- | --- | --- | --- |
  | `riemannHypothesis` | theorem, in `Main` | `RiemannHypothesis` | `Mathlib.NumberTheory.LSeries.RiemannZeta` |
  | `riemannZeta_eq_zero_re` | theorem, in `Main` | `RiemannZetaZerosOnLine` | `Statements` |
  | `LFunction_ne_zero_of_half_lt_re` | theorem, in `Main` | `DirichletLNonvanishingRightOfHalf` | `Statements` |
  | `LFunction_eq_zero_re` | theorem, in `Main` | `DirichletLZerosOnLine` | `Statements` |
  | `LFunction_eq_zero_re_of_isPrimitive` | theorem, in `Main` | `PrimitiveDirichletLZerosOnLine` | `Statements` |

- What `RiemannHypothesis` unfolds to, as the environment stores it:

  ```
  forall (s : Complex), (Eq.{1} Complex (riemannZeta s) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZero))) -> (Not (Exists.{1} Nat (fun (n : Nat) => Eq.{1} Complex s (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMul) (Neg.neg.{0} Complex Complex.instNeg (OfNat.ofNat.{0} Complex 2 (instOfNatAtLeastTwo.{0} Complex 2 Complex.instNatCast RiemannHypothesis._proof_1))) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAdd) (Nat.cast.{0} Complex Complex.instNatCast n) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOne))))))) -> (Ne.{1} Complex s (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOne))) -> (Eq.{1} Real (Complex.re s) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOne)) (OfNat.ofNat.{0} Real 2 (instOfNatAtLeastTwo.{0} Real 2 Real.instNatCast RiemannHypothesis._proof_1))))
  ```

  That is the definition at lines 185 and 186 of Mathlib's file, and
  `RiemannZetaZerosOnLine` of `Statements.lean` unfolds to the same term but
  for the name of one auxiliary proof.
- The counts are those of the verdict run's cone to the last digit, by
  library as well, from a second runner.

So the printout of `#print axioms` and the reading of `Main.lean` were not
artefacts of the environment they were made in.

**Limit 1 in detail: the kernel of 4.33.1 (read 20:10Z to 20:16Z).** The
sources are Lean's release notes for 4.33.0, 4.33.1, 4.34.0, 4.34.1, 4.35.0
and 4.36.0 on lean-lang.org, Leonardo de Moura's "Postmortem for the Kernel
Soundness Bug Hunt" of 2026-08-24, and the pages of lean4 pull requests
14806, 14807 and 14843. They were read through a fetching agent, which
returned the kernel sections verbatim and the rest as summaries; nothing
below was checked against Lean's source.

- In July and August 2026 a series of soundness bugs was found in Lean's
  kernel and runtime, several of them by an AI model set to hunt for them.
  The postmortem: "The OpenAI internal model managed to exploit all of them
  to get the official kernel to accept a proof of `False`." So an
  AI-written development that passes one kernel is not a hypothetical
  risk. It is the case this limit is about.
- 4.33.1, of 2026-08-21, is the release that closed that hunt. The
  postmortem: "On August 21, we released Lean v4.33.1 with bug fixes for
  all issues found during the kernel bug hunt." Its notes list pull
  requests 14582, 14806, 14807, 14808, 14833, 14838, 14843, 14847 and
  14849, and the fixes of 4.33.0 (14498, 14577, 14607, 14609, 14613, 14616
  and the hardening after them) are below it. The archive's pin is this
  release, and Mathlib's tag `v4.33.1` was cut for it the same day.
- Every kernel item in the notes of 4.34.0 is already in 4.33.1. After
  4.33.1 the notes list three more fixes that bear on proof checking, all
  in the runtime and all in 4.34.1 of 2026-09-24: 15241, 15288 and 15289.
  By those notes 15241 needs a machine "with at least 18GB free RAM",
  15289 concerns "inputs north of 100GB", and 15288 concerns objects
  shared between threads, which the kernel does not do in its default
  configuration. The runners of the build and of the verdict have 15 GB of
  memory and about 3 GB of swap, and the largest `lean` process the
  watchdog saw in the rounds of the build it watched held 13.7 GB. A
  process on such a machine cannot have met the first two. (The replay's
  runners are given up to 24 GB more swap. The largest driver seen there
  is the one on `SesquilinearFractions.ExistsFactorThroughMultiplication`,
  130 lines of algebraic geometry: 12.7 GB when the watchdog ended it in
  round 10, and in round 11 a resident peak of 10.0 GB with about 13 GB of
  the runner's swap in use.)
  4.35.0 and 4.36.0 list no further soundness fix for the official kernel.
- The same sources say what the standard second opinion is. The
  postmortem: "The gold standard is `comparator` and external checkers
  when you want to protect against a seriously malicious proof", and "`lake
  build` does not protect users from adversarial proofs that try, for
  example, to corrupt memory using Lean extensions." From 4.35.0 Lean
  ships `lake check --paranoid`, which exports a project and replays the
  export through Lean's kernel and four external checkers (lean4lean,
  nanoda, con-leche, con-ron). None of that exists for 4.33.1 as a
  command, and none of it has been run on this archive here. An export of
  the cone of five theorems over 175,187 modules, held in the memory of one
  checker, is not a job for a 15 GB runner; its size is not measured yet.
- What a 15 GB runner can carry is the per-module form of the same idea:
  the replay of the second pass with lean4lean's type checker in place of
  the C++ kernel. lean4lean is a second implementation of the checking
  logic, written in Lean. Its own README says it "is derived directly from
  the C++ kernel implementation, and as such likely shares some
  implementation bugs with it", and it runs on the same runtime, so it is
  a second route and not an independent one. The notes of 4.34.0 say it
  did not have the bug of pull request 14807, which nanoda had. Its
  `master` (`67f63b0c`, 2026-10-10) is on toolchain 4.33.0-rc2; whether it
  builds on 4.33.1 is untried. It could not be tried in this container,
  which may not build downloaded code, so the first step is a pilot on a
  runner with the planted fault of `test_replay_check.py`.

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
elaborated modules. Outcome, run 44895281825, 17 minutes end to end: the
loop device granted direct I/O (flag 1); the restore of 15 bundles and 149
chunks took 633 s, against 1,828 s for 126 chunks the first time; 150,487
`.olean` files on disk; the build over 8,528 targets ended with exit code 0
in 132 s with 0 modules elaborated and 217,216 lines replayed from stored
logs; Lake held 1.2 GB. The disk stood at 74 GB of 145.

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
| 7 | 44887964847 | 10:53 | 16,577 | 111,176 | 63.46 | 0 | 0 | 4.59 | against build state 14699969555; the fixed driver, outputs in a plain directory; 18,032 planned, one shard stopped by its deadline; all four shards reported, nothing killed; check state 14704356588 |
| 8 | 44896453130 | 12:43 | 9,472 | 120,648 | 68.87 | 0 | 0 | 7.59 | against build state 14702344189; three of four shards reported, shard 0's runner was lost and left no log; 13,611 planned on the three, all stopped by the deadline; the chain lowered itself to two processes per runner for round 9; check state 14707134382 |
| 9 | 44905297777 | 14:31 | 6,449 | 127,097 | 72.55 | 0 | 0 | 3.78 | against build state 14704557927; two processes per runner; three of four shards reported, shard 1's runner was lost and left no log, as shard 0's was in round 8 at four; 6,504 planned on the three, one stopped by its deadline; the chain lowered itself to one process per runner for round 10; check state 14710478596 |
| 10 | 44914347569 | 15:46 | 4,107 | 131,204 | 74.89 | 0 | 0 | 3.08 | against build state 14710597929; one process per runner; all four shards reported; 4,392 planned; one strike, see below: the watchdog ended the replay of `SesquilinearFractions.ExistsFactorThroughMultiplication` at 12.7 GB, alone on its runner, and the 285 modules after it in that list were not reached; check state 14713298174 |
| 11 | 44924547755 | 18:16 | 8,137 | 139,341 | 79.54 | 0 | 0 | 5.58 | against build state 14713104221; dispatched by hand at 16:26Z after the cancelled run; two processes per runner, small page-fault windows, extra swap, plain directories; all four shards reported; 8,884 planned, three shards stopped by their deadline; no process killed, no new strike; the module struck in round 10, `SesquilinearFractions.ExistsFactorThroughMultiplication`, went through the kernel on shard 0 in 2,076 s with the swap in place; check state 14718594608 |
| 12 | 44934638612 | 19:52 | 6,606 | 145,947 | 83.31 | 0 | 0 | 4.07 | against build state 14718047776; two processes per runner; three of four shards reported, each with all 2,202 of its modules and none stopped by its deadline; shard 2's runner was lost 49 minutes into its replay and left no log, and the two surviving runners looked at never had less than 11 GB available, so memory in general was not short; check state 14722696394. Round 13 started with four shards (run 44943257562), was cancelled after twelve minutes and dispatched again with twelve (run 44944303371) |
| 13 | 44944303371 | 22:00 | 15,578 | 161,525 | 92.20 | 0 | 0 | 6.79 | against build state 14720649806, the complete one; twelve shards, two processes per runner; nine of twelve shards reported, eight of them stopped by their deadline, 19,971 planned on the nine; shards 5, 6 and 11 lost their runners 91, 65 and 89 minutes into the replay and left no log, see "The lost runners are not a module" below; check state 14727455301. Round 14 is run 44954431174, twelve shards, the first round with the self-test |
| 14 | 44954431174 | 00:39 | 6,521 | 168,046 | 95.92 | 0 | 0 | 7.12 | seven shards for the 13,662 modules left, the self-test passed on all seven; four reported, three of them stopped by their deadline, 7,248 planned on the four; shards 1 and 2 lost their runners (marked failed 106 and 78 minutes into the replay), and shard 5 was still "in progress" 138 minutes into a replay of 100 with the round waiting on it, so the run was cancelled at 00:33Z: the merge then ran on the four records and handed on; check state 14732520405. Round 15 started as run 44967645994 on the old commit, was cancelled after four minutes and dispatched again as run 44967950293 on `f225a431`: forty-minute shards and the memory group |
| 15 | 44967950293 | 01:40 | 6,352 | 174,398 | 99.55 | 0 | 0 | 6.32 | forty-minute shards inside the memory group; nine shards for the 7,141 modules left and all nine reported, four of them stopped by their deadline; check state 14734760370. Round 16 is run 44972556875: the plan put the 789 modules left on one runner |
| 16 | 44972556875 | 02:37 | 670 | 175,068 | 99.93 | 0 | 0 | 7.14 | one shard of forty minutes inside the memory group, 789 planned, stopped by its deadline with 119 left: the modules at the top. Check state 14735552970. Round 17 started as run 44976967434 with one shard again, was cancelled and dispatched as run 44977095184 on `c3621689`: planned for half a minute a shard (`plan_minutes`), so that the 119 spread over twelve runners, with a deadline of sixty minutes |
| 17 | 44977095184 | 03:37 | 119 | 175,187 | 100.00 | 0 | 0 | 66.03 | eleven shards inside the memory group, eleven modules each and nine on the last; all eleven reported, the self-test passed on each, none stopped by its deadline; `Main` itself replayed on shard 10 in 852 s, and the slowest of the round was `SmallClassNumbers.CorGKOf` in 879 s; the merge found nothing left to plan and the chain ended itself; check state 14737209276 |

### The second pass is complete, 2026-11-22 03:37Z

Eighteen rounds, 20:17Z on 2026-11-20 to 03:37Z on 2026-11-22. Read from
check state 14737209276 at 04:36Z (the zip's sha256 is the digest GitHub
reports for the artifact, `befcd447...8458`), against build state
14720649806:

| | |
| --- | --- |
| modules replayed | 175,187, and as a set of names they are the 175,187 of the build state: nothing missing, nothing extra |
| kernel rejections | 0 |
| modules left out | 0 |
| strikes | 1: `SesquilinearFractions.ExistsFactorThroughMultiplication`, ended by the watchdog for memory in round 10 and replayed in round 11 in 2,076 s |
| cost | 254.3 process-hours: mean 5.23 s a module, median 4.37 s, 90th percentile 7.2 s, 99th 15.6 s; the slowest after the struck one took 879 s |
| lost shards | one in round 5 and 9 of the 39 of rounds 8 to 14; none of the 21 of rounds 15 to 17, which ran inside the memory group. A lost shard cost its round's work and no module |

**What a replay of a module is.** `ReplayDriver.lean` reads the module's
`.olean`, loads its imports from their `.olean` files without checking
them, and sends the module's constants through the kernel in that
environment (`Lean.Environment.replay`). It runs no command, tactic or
macro of the archive. With every module replayed, every import a replay
relied on was itself replayed, so the whole is checked from Mathlib up.
Three things that sentence leans on, each looked at:

- *The files replayed are the files the verdict read.* Rounds 0 to 12 ran
  while the build was still going, against twelve earlier build states. A
  build state names, for each module, the chunk that holds its outputs,
  and for each build round the artifact that holds that round's chunks.
  In all twelve (39,235 to 175,165 modules) every module is recorded in the
  chunk the final state names for it, and every bundle carries the
  artifact id the final state gives it: no difference in any of them. Every
  module was in the build state of the round that replayed it. So each
  `.olean` was replayed from the artifact the verdict's jobs restored it
  from (for the 4,490 modules built twice, from one of two identical
  copies), and artifacts are not rewritten.
- *An `.olean` of the archive holds whole proofs.* No file of the archive
  is a `module` in Lean's sense (0 of 175,187 has a line starting with
  `module`, `public import`, `import all`, `public section` or
  `@[expose]`), so there is one `.olean` per file and it stores every
  theorem with its proof term. (Mathlib at the pinned tag does use the
  module system, as the first lines of its `RiemannZeta.lean` show; its
  files are limit 4, not this.)
- *What the replay leaves out.* `Lean.Environment.replay` skips constants
  marked unsafe or partial. The archive's text has no `unsafe` and two
  `partial def`, both helpers of its own tactics (`copyAt` in
  `OwnStruct.lean`, `go` in `CutCptCopy.lean`). The kernel does not let a
  theorem mention such a constant; that is from memory of Lean's source
  (`type_checker::infer_constant`) and was not read again here.

The grade this gives the verdict is written there, under "The grade".

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

### Check round 10, 2026-11-21 15:46Z: the module that the replay cannot hold

Round 10 ran one process per runner, after rounds 8 and 9 each lost a
runner without a log. All four shards reported and the kernel rejected
nothing. On shard 3 the watchdog ended the replay of
`Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication`
when it held 12,750 MB with nothing else running: one strike. That is the
module that held 13.7 GB when it was compiled (build round 14). Rounds 8
and 9 replayed against build states that contain it, with four and two
processes side by side, so it is the likely cause of the two lost runners;
their logs are gone and that stays an inference.

A strike is not a rejection: the kernel never finished with the module.
Changed for rounds 11 and 12 on (`310093ae`, `a832489a`): a replay
shard adds swap on what its disk has left, the watchdog ends a replay only
when the swap is nearly used up too, a module gets four strikes before it
is left out, and the chain never runs fewer than two processes per runner.
Round 11 was dispatched at 15:46Z, before the swap, with the small
page-fault windows and two processes; if it strikes the module again, the
later rounds still try it twice with swap.

*Added 18:33Z.* That round 11 was cancelled and dispatched again at 16:26Z
with the swap (see the next section), and in it the module was replayed:
2,076 s in the kernel on shard 0, accepted. The row I first wrote for round
11 said it had not been reached; the check state says otherwise.

### Check round 11 cancelled, 2026-11-21 16:18Z: the replay waits for the rehearsal of the verdict

Round 11 (run 44920988121, dispatched 15:46Z) was cancelled half an hour
in, with nothing merged. The account was at its limit of twenty jobs, the
rehearsal of the new verdict jobs (run 44922636081) had been queued for
thirteen minutes, and the four replay runners were the ones to give up: the
verdict path has to work the first time, and the replay can catch up. The
chain does not restart by itself after a cancelled round. It is to be
dispatched again by hand from check state 14713298174, with the swap, the
small windows, the further cleanup and a plain directory for any shard.

### The lost runners are not a module, 2026-11-21 22:38Z

Since check round 8 a replay shard has ended six times with its runner gone
and no log: one of four in rounds 8, 9 and 12, three of twelve in round 13,
none in rounds 10 and 11. Six of 32. The build lost no runner that way in
rounds 12 to 21, about 120 shards. What can be said:

- *It was not a module in round 12.* The 2,202 modules of round 12's lost
  shard 2 were planned again as the first 2,202 of round 13's shard 0, in
  the same order and with the same split between two processes. Round 12's
  runner was lost 2,927 s into its replay; at the times round 13 measured
  for those modules, its two processes were then on about the 421st and
  426th module of their lists. Round 13 replayed 865 and 867 from each list
  without incident. Whatever ended that runner, the modules it was on
  replay.
- *It was not memory on the runners that survived beside them.* Round 13's
  shards 4, 7 and 10, the neighbours of the lost 5, 6 and 11, never had
  less than 7.0, 10.1 and 11.4 GB available, left their 27 GB of swap
  untouched (25.9 GB free at the least), and the watchdog stopped and
  killed nothing. What the lost runners saw is not known: they uploaded
  nothing, GitHub returns no log for them (HTTP 404) and their check runs
  carry no text.
- *Both kinds of runner are lost.* By their restore times, round 13's
  shards 5 and 6 were on the faster disks and shard 11 on the slower.
- *When.* 49, 65, 89 and 91 minutes into a replay of 100 in the four cases
  timed.

So the cause is not found. What follows from what is known: a lost shard
costs its round's work and nothing else, its modules replay when planned
again, and there is no module to isolate or to strike. The chain carries
on; a round that loses shards leaves their modules to the next. If the
rate holds, about a fifth of each round's runner time is lost. Uploading a
shard's record in parts would cap that, and has not been built.

**Round 14, 2026-11-22 00:40Z: the rate rises with the height of the
modules, and a lost runner is one that has stopped answering.** Three of
seven shards in round 14, after three of twelve in round 13 and one of four
in round 12, as the modules left climb the import graph (a shard of round
13 needed 72,000 to 129,000 files restored). One of the three, shard 5, was
not marked failed at all: its replay step still read "in progress" 38
minutes after the deadline `replay_check.py` enforces, and it did not react
to the run's cancellation at 00:33:37Z: the run ended, and the merge ran,
five minutes later, which is GitHub ending a job by force. So these runners
do not crash. They stop answering, and GitHub fails them when it notices.

A mechanism that fits, not shown: a replay process this high maps a
hundred thousand files and reads more than the runner's memory holds, so
the page cache turns over for the whole replay; every idle process on the
machine loses its pages to that, the runner's own agent among them, and
has to read them back through a disk that is busy. `MemAvailable` counts
page cache as available, which is why the shards that survived looked
comfortable. The build's shards at the top did the same reading and lost
no runner, which this does not explain; the replay sets `vm.swappiness` to
10 where the build left it at 60, and that is one difference.

The test of it is `cgroup_cap.sh`: from the next round each shard's replay
processes run in a memory group of their own, 4 GB under the runner's
memory, with the cache dropped first so that what they read is charged to
the group. The turnover then happens inside the group and the rest of the
machine keeps 4 GB. If shards stop being lost, that was it; if they are
still lost at the same rate, it was not, and the cap has cost a few
minutes of cold cache per shard.

**Round 15, 2026-11-22 01:40Z: nine of nine.** The first round inside the
group, and the first with forty-minute shards, lost no runner, on modules
higher than those of rounds 13 and 14, which lost three of twelve and three
of seven. Shard 0's record shows the group in force (`cgroup_cap: pid 4610
is in alpoge-replay, memory.high 12168724480 bytes`): page cache never over
9.3 GB where the earlier survivors showed 10 to 11, and all 842 of its
modules replayed in 2,202 s. Two things changed at once, so this does not
say which of them did it: the earlier losses came 49 to 106 minutes into a
replay, and no shard of round 15 ran that long. It is one round. What it
does say is that the combination runs clean where its absence did not.

**Rounds 16 and 17, and the test that separates the two, 2026-11-22
04:45Z.** The kernel's last two rounds lost none either: one shard of
forty minutes and eleven of sixty, the longest replaying for 43 minutes.
So 21 shards inside the group, none lost, and none of them long enough to
say whether the group or the shorter shard did it. The second checker's
pass says more: its rounds 4 and 5 ran eight shards of one hundred minutes
inside the group and lost none, lower in the graph than where the kernel's
shards were lost, and from round 6 it runs sixteen such shards through the
heights at which rounds 13 and 14 lost six of nineteen. If those report,
it was the group.

**Round 6 of the second checker, 2026-11-22 07:07Z: sixteen of sixteen,
and a correction.** All sixteen hundred-minute shards inside the group
reported. They were not yet at the heights the paragraph above names: round
6 planned positions 59,000 to 129,000 of the graph's order, which is where
the kernel's rounds 4 to 10 ran, and those lost three of 28 shards (one
each in rounds 5, 8 and 9). The heights of rounds 13 and 14 are reached in
round 7.

**Round 7 of the second checker, 2026-11-22 08:56Z: sixteen of sixteen at
those heights.** Round 7 planned everything that was left, the heights of
the kernel's rounds 13 and 14 among it, on sixteen shards of one hundred
minutes inside the group, and all sixteen reported. With the group no shard
has been lost at all: 21 of the kernel's, of forty and sixty minutes, and 40
of lean4lean's, of one hundred. Without it the kernel's shards of one
hundred minutes were lost ten times in 67 (rounds 1 to 14), six of nineteen
at these heights. So the long shard is cleared: a hundred minutes inside the group
is safe. What is not separated is the group from the checker. The sixteen
differ from the nineteen in both, and lean4lean's processes are replaced
every four modules where the kernel's driver lived for its whole shard and
kept mapping files. One of the two did it; the kernel's pass is over and
will not say which.

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

**What check round 7 measured (10:53Z).** The fix changed the memory and not
the speed: 16,577 modules replayed against 16,601 in round 6, 4.59 s a
module against 4.80. So what a module costs to replay is its import and its
kernel work, not the leak. The driver's memory after a module, which it now
prints, peaked between 2,537 and 2,658 MB: the twenty largest readings sit
within 121 MB of each other, in six directories, after modules whose import
closures are small (36 to 2,012 archive modules). A reading that flat, after
modules that shallow, is where a process's heap stood at its high-water
mark, kept by the allocator; it does not say those twenty modules need it,
and it does not yet say what the deepest modules will need. It is half of
what round 6 saw at its worst (5.6 GB). Nothing was suspended or killed, and
all four shards reported.

## Third pass: the same replay with a second checker

Why: limit 1 of the verdict, set out under "Limit 1 in detail" there. What:
`L4LDriver.lean` puts lean4lean's type checker behind the front end of
`ReplayDriver.lean`, and `replay-alpoge-check.yml` takes `checker=lean4lean`
and an epoch of its own, `l4l`. lean4lean is derived from the C++ kernel and
runs on the same runtime: a second route, not an independent one. Nothing
of it is built in the session's container, which may not build downloaded
code; it is fetched and compiled on the runner, where the archive is.

### Estimate before spending, 2026-11-21 20:20Z

Nothing was known: whether lean4lean at its `master` (`67f63b0c`,
toolchain 4.33.0-rc2) builds with Lean 4.33.1 at all, whether it reads this
archive, what a module costs. Its paper says 20 to 50 percent slower than
the kernel; the kernel's replay stands at 197 process-hours for 145,947
modules. So the unit was timed first, on one runner.

### The self-test every shard now runs, 2026-11-21 20:23Z, run 44946013320

Before it replays anything a shard builds the three-module toy of
`test_replay_check.py` and requires its driver to answer OK, FAIL, OK
(`replay_check.py selftest`). Tried first on the kernel's driver, epoch
`t1`, one shard, five minutes, on `83a9fc6f`: the self-test passed in five
seconds with

```
"Lib.Cheat": "while replaying declaration 'bad': | (kernel) declaration type mismatch, 'bad' has type |   True | but it is expected to have type |   Eq 1 2"
```

and the shard replayed the 90 modules of its plan, 2.66 s each, none
rejected. The kernel's chain picks the step up with round 14.

### Pilot of the second checker, 2026-11-21 20:23Z to 20:38Z, run 44946010580

Epoch `l4l`, round 0, one shard, eight minutes, two processes, on
`83a9fc6f`, build state 14720649806.

| | |
| --- | --- |
| build | lean4lean at `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` and batteries at `76e1c118b0700b4ceafe99532e887d6431625e1a`, with the archive's toolchain: 33 s, no error |
| self-test | passed: `Lib.Honest` OK, `Lib.Cheat` FAIL ("at bad: (kernel) declaration type mismatch, 'bad' has type ... True but it is expected to have type ... Eq.{1} Nat ..."), `Lib.UsesCheat` OK |
| planned / replayed | 144 / 86 when the eight minutes ended; 3,226 declarations |
| rejections | 0 |
| cost | 828 s for the 86; the kernel's replay took 371 s for the same 86 (check state 14722696394), a ratio of 2.23 on a runner that was swapping from its second minute |
| memory | each process grew by about 480 MB with every module that imports Mathlib (389, 871, 1,355, 1,817, 2,321 MB after the fourth to the eighth), to 6.3 GB resident; the two together used up all 27 GB of swap in five minutes, and the watchdog suspended one of them once |
| check state | artifact 14723794021 |

So it builds, it reads the archive's `.olean` files, it rejects the planted
fault, and it agrees with the kernel on 86 modules. It also keeps about
half a gigabyte for every module it has replayed, which the kernel's driver
does not (527 to 649 MB flat, above). Where that memory is held was not
found by reading lean4lean's source and could not be probed here. The
remedy does not depend on knowing: `replay_check.py run --batch 4` gives a
process four modules and then replaces it. The second pilot (round 1, ten
minutes, dispatched 20:42Z on `06a8e36d`) measures what a module costs
without the swapping.

### Second pilot, 2026-11-21 20:42Z to 20:55Z, run 44947689609

Epoch `l4l`, round 1, one shard, ten minutes, two processes of four modules
each at a time, on `06a8e36d`.

| | |
| --- | --- |
| self-test | passed on this runner as well |
| planned / replayed | 180 / 180 in 271 s, before the deadline; 8,752 declarations |
| rejections | 0 |
| memory | 114, 599, 1,574 and 2,089 MB after the four modules of the first process, 114, 599, 1,082 and 1,567 MB in the ones after it, each then replaced: 2.1 GB at most by the driver's own reading; the runner never had less than 10.9 GB available and no swap was used |
| cost | 484 s, 2.69 s a module. The kernel's replay of the same 180 modules is on record at 1001 s (5.56 s a module), but that was on shards of two thousand modules with four times the files restored; the like-for-like figure is the kernel's 2.66 s a module in the five-minute test above |
| check state | artifact 14724676759 |

lean4lean prints a line of its own for a declaration that takes it more
than a second ("lean4lean took 16671" for one theorem here); those lines are
not verdicts and the reader of the driver's output skips them.

With the import dominating both, a module costs lean4lean about what it
costs the kernel at the bottom of the graph. What it costs higher up, where
its own table of every imported constant grows with the import, is not
measured.

### The chain, launched 2026-11-21 21:04Z

Run 44949631188: epoch `l4l`, round 2, from check state 14724676759, four
shards, one hundred minutes, three processes per runner (the pilots ran
two; three is a guess the chain corrects, since it halves the count after a
kill or a lost runner), chained. Four shards while the kernel's replay
holds twelve runners; more when it is done. Rounds are appended below as
they merge.

| round | run | merged (UTC) | replayed | total | % of archive | rejections | struck | mean s per module | note |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 44946010580 | 20:38 | 86 | 86 | 0.05 | 0 | 0 | 9.63 | first pilot, swapping |
| 1 | 44947689609 | 20:54 | 180 | 266 | 0.15 | 0 | 0 | 2.69 | second pilot, four modules per process |
| 2 | 44949631188 | 22:52 | 12,175 | 12,441 | 7.10 | 0 | 0 | 4.19 | four shards, three processes, four modules per process; all four reported, two stopped by their deadline, 13,140 planned; three modules ended in lean4lean's `deterministic timeout`, see below; on the 12,441 modules both checkers have timed, lean4lean 14.5 process-hours and the kernel 13.9; the largest driver held 7.0 GB after a module; check state 14728422994. Round 3 is run 44958976482 |
| 3 | 44958976482 | 00:47 | 14,509 | 26,950 | 15.38 | 0 | 0 | 3.21 | all four shards reported, one stopped by its deadline, 15,408 planned; two more `deterministic timeout` stops of the same kind (`DyadicPrimeIntervals.Run2` and `Run4`), five in all; on the 26,950 modules both checkers have timed, lean4lean 27.5 process-hours and the kernel 31.7; check state 14732841469. Round 4 is run 44968369103, the first with the fuel scale in the driver (built against lean4lean in 27 to 33 s, self-test passed) and with the memory group |
| 4 | 44968369103 | 02:38 | 16,352 | 43,302 | 24.72 | 0 | 0 | 3.56 | the first round inside the memory group and with the fuel scale in the driver; all four shards reported, two stopped by their deadline, 17,668 planned; no new stop, five in all; on the 43,302 modules both checkers have timed, lean4lean 43.6 process-hours and the kernel 56.4; the largest driver held 5.4 GB after a module; check state 14735144301. Round 5 is run 44977057501 |
| 5 | 44977057501 | 04:28 | 16,124 | 59,426 | 33.92 | 0 | 0 | 3.93 | all four shards reported, three stopped by their deadline, 17,864 planned; no new stop, five in all; on the 59,426 modules both checkers have timed, lean4lean 61.2 process-hours and the kernel 78.7; the largest driver held 4.6 GB after a module; check state 14739785115. Round 6 started by itself as run 44985248355 with four shards at 04:29Z, was cancelled at 04:41Z with nothing replayed, and was dispatched again as run 44986236486 with sixteen, see below |
| 6 | 44986236486 | 06:39 | 58,272 | 117,698 | 67.18 | 0 | 0 | 4.08 | sixteen shards, three processes; all sixteen reported, nine stopped by their deadline, 69,888 planned; no new stop, five in all; no process killed and no strike; on the 117,698 modules both checkers have timed, lean4lean 127.3 process-hours and the kernel 155.7; the largest driver held 5.1 GB after a module, and one held 10.3 GB on a module it did not finish, see "A module lean4lean does not finish" below; check state 14743497145. Round 7 is run 44994721820, dispatched by the chain at 06:39Z on `56e684b3`, sixteen shards |
| 7 | 44994721820 | 08:37 | 35,830 | 153,528 | 87.64 | 0 | 0 | 6.68 | sixteen shards, three processes; all sixteen reported, fourteen stopped by their deadline; the plan took everything left, 57,484; no new stop, five in all; no process killed and no strike; on the 153,528 modules both checkers have timed, lean4lean 193.8 process-hours and the kernel 213.7, and in this round lean4lean 66.5 against the kernel's 58.0: this high it is the slower of the two (1.2, 1.7 and 2.3 times the kernel on the modules of the kernel's rounds 13, 14 and 15); the largest driver held 4.7 GB after a module; two shards were held up by one module each, see "A module lean4lean does not finish"; check state 14747021470. Round 8 is run 45003686475 on `fe199842`: the 21,654 modules left cut evenly over sixteen shards, 1,353 or 1,354 each, and the first round with the limit per module |
| 8 | 45003686475 | 10:30 | 21,404 | 174,932 | 99.85 | 0 | 0 | 7.33 | sixteen shards, the 21,654 left cut evenly; all sixteen reported, two stopped by their deadline; the first round with the limit per module: six modules given up after 1,800 s, see "Round 8" below; no rejection and no new fuel stop, so eleven listed as failed, five fuel stops and six without an answer; no process killed and no strike; on the 174,932 modules both checkers have timed, lean4lean 237.3 process-hours and the kernel 251.8, in this round 43.6 against 38.1; the largest driver held 4.5 GB after a module; check state 14750736222. Round 9 is run 45012762475 on `33dbea80`: the 244 modules left, fifteen or sixteen a shard |

**Sixteen shards from round 6, 2026-11-22 04:42Z.** The kernel's replay
ended at 03:37Z and its runners are free; sixteen is what the build and the
replay held between them. The estimate, before spending: the 115,756
modules left took the kernel 175.6 process-hours; lean4lean has run at 0.78
of the kernel's time on the 59,426 both have timed (0.65 to 1.04 by round);
and a shard of one hundred minutes at three processes delivered 4.4
process-hours in round 5. Sixteen shards are then about 70 process-hours a
round and the rest is two to three rounds of two hours each, done between
09:00Z and 11:00Z, if the ratio holds higher up. That is not measured: the
kernel's last round, the 119 modules at the top, cost it 66 s a module,
nearly all of it import, and lean4lean keeps a table of its own of what it
imports. The five fuel stops are retried in one round after that.

**The plan no longer leaves runners idle at the end, 04:48Z.** The kernel's
pass needed four rounds for its last 13,662 modules, with 7,141, 789 and
119 left after each: a shard is filled to its budget at the mean time of a
replay so far, the modules at the top cost several times the mean, and so
each plan put what was left on a runner or two and found half of it still
there two hours later. `plan_minutes` was the repair by hand. From the
round after 6, `replay_check.py plan` cuts everything left evenly over all
the shards it is given whenever it would otherwise use fewer
(`test_a_tail_that_fits_fewer_shards_is_cut_evenly_over_all_of_them`, which
fails on the planner as it was).

### A module lean4lean does not finish, 2026-11-22 07:07Z: no answer is not a rejection

Fifteen of round 6's sixteen shards delivered 3.5 to 4.7 process-hours of
replay. Shard 6 delivered 2.2 and replayed 1,319 of its 4,368 modules. From
its evidence (artifact 14743362390) and the round's plan (artifact
14739727611):

- About 1,400 s into the replay one of the three driver processes began to
  grow: 9.3 GB of anonymous memory at 1,622 s, 10.3 GB at its peak. The
  runner swapped from then on. At 3,604 s the watchdog suspended the other
  two processes, as it is built to (it suspends all but the largest), and
  they were suspended for most of the last forty minutes. The large process
  was still running at the deadline, 6,003 s, 4,644 s after it had started.
- It was on the third module of its batch, the two before it done in 2.6 s
  and 3.3 s:
  `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions`,
  51 lines, one theorem about points of schemes, its last steps a `change`,
  a `rw` and a `rfl`. So lean4lean had been on this module for about 77
  minutes.
  The kernel replayed it in 4.07 s (its round 6).
- lean4lean printed nothing for it: no rejection, and none of its fuel
  counters stopped it.

So this is neither a verdict nor a fuel stop: lean4lean was still working
and the shard's time ran out. Slow modules are not new to it. It took
4,961 s over `HidaCompleteRings.OrdBasic` in round 3, which the kernel
replays in 52 s, and 1,690 s and 1,535 s over two modules of round 6 that
take the kernel 18 s and 13 s; all three finished and were accepted. In
total it is the faster of the two on what both have timed, and on a few
modules it is a hundred times the slower.

Left alone this would have cost a shard a round, every round: the module
is neither failed nor struck, so each plan takes it up again, and the chain
would have ended only on a round that replayed nothing.

**The repair.** `batch_runner.py` (the runner that gives a driver a few
modules at a time, until now a string inside `replay_check.py`) takes a
limit per module, `replay_check.py run --module-seconds`. A module the
driver has been on for longer is given up: the driver is ended, the module
is recorded as `FAIL` with the message `no answer after 1800 s: this run
stopped waiting, the checker gave no verdict`, and the modules after it go
to a fresh process. Time a driver spends suspended by the watchdog does not
count. The limit is 1,800 s in ordinary lean4lean rounds
(`L4L_MODULE_SECONDS`) and none in the kernel's. A module given up is not
lost: `retry_failed=fuel` now plans the `no answer after` modules with the
fuel stops, and a retry round has no limit but its deadline. Of the 117,698
modules lean4lean has finished, the limit would have put one into that
retry, the 4,961 s one. Three tests in `test_replay_check.py`: a module
that never answers is given up and the rest of its batch and the later
batches are replayed; the deadline still ends a driver that now runs in a
process group of its own (it fails when the runner is made to forget the
driver); a stopped driver's time is not held against its module.

Round 7 was dispatched before this and has no limit. The module is in its
plan again and will cost one of its sixteen shards most of its round. It
was not restarted for that: its runners had restored their files and were
replaying, and a restart costs more than the shard. The limit applies from
round 8.

*Pilot of the new runner, 07:09Z to 07:16Z, run 44996902719.* Epoch `t2`,
one shard, four minutes, on `810cf308`: the runner drove the real driver
through `lake env` with the limit set (`"module_seconds": 1800.0`, four
modules a process): 108 planned, 108 replayed in 152 s, none rejected,
every process ended 0, and the watchdog still saw each driver under its
list's name. What it does not show is a module given up on a runner: none
of the 108 is slow. That path has run on the stub of the tests only, and
round 8 is its first real use.

**Where the pass stands after round 6.** 57,484 modules left, 98.6
process-hours by the kernel's clock; round 6 delivered 66.1 process-hours
of lean4lean's time, 0.86 of the kernel's on the same modules. Round 7
should leave a tail that the next plan cuts over sixteen shards, then the
retry of the five fuel stops and of whatever was given up.

**Round 7, 08:56Z: the same module again, and a second.** Shard 1 had
`EncardComplexPointFibreEqEncardRingHomExtensions` in its plan and replayed
818 of 3,593 modules: the process that reached it was on it for 5,102 s, to
the deadline, at up to 10.7 GB (artifact 14746539240). Shard 2 replayed
2,308 of 3,593: from its evidence
(artifact 14745779076) one process was on a module for the last 3,022 s of
the replay, at up to 10.5 GB, and the watchdog suspended the other two at
4,028 s. That module is
`Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication`,
the heaviest of the archive for the kernel as well: 2,076 s there, and the
one strike of the second pass. Fifty minutes without an answer is nearly
one and a half times the kernel, which is where lean4lean stands on other
modules this high. So this one is slow, as far as fifty minutes can tell,
and the first one is something else: 77 minutes in round 6 and 85 in round
7 without an answer, on a module the kernel does in four seconds. Round 8
gives both up after 1,800 s and the retry takes each alone on a runner.

**Where the pass stands after round 7.** 21,654 modules left, 40.6
process-hours by the kernel's clock. Fifteen of round 8's shards hold 1.4
to 2.8 of those hours each. The sixteenth holds the top of the graph, 6.6,
more than a shard delivers at lean4lean's rate up there, so a round 9 is
expected for what is left of it, cut over sixteen runners. Estimate: round
8 merges about 10:40Z and round 9 about 11:45Z to 12:00Z; then the retry
round, whose deadline is the time the modules without an answer are given.
The retry's path has not run on a runner, so it is rehearsed in an epoch of
its own, `t3`, run 45004870709: the five fuel stops, from check state
14747021470, with a hundred times the fuel, on three shards. Its check
state is thrown away; the retry that counts starts from the chain's last
state.

**The rehearsal, 08:53Z to 08:59Z: with a hundred times the fuel lean4lean
accepts all five.** Run 45004870709 took six minutes. The plan found the
five modules and nothing else and cut them over the three shards; the
driver reported `l4ldriver: fuel times 100` and ran with no limit per
module; all five were replayed and accepted; and the merge moved them from
`failed` to `checked`, their first messages kept under `retried`
(`n_retried_ok` 5, nothing failed, nothing struck).

| module | lean4lean, fuel times 100 | kernel |
| --- | --- | --- |
| `ChebyshevPrimeBounds.SmallLoop` | 90.3 s | 95.6 s |
| `DyadicPrimeIntervals.Run1` | 55.2 s | 22.8 s |
| `DyadicPrimeIntervals.Run2` | 54.9 s | 22.5 s |
| `DyadicPrimeIntervals.Run3` | 39.8 s | 28.6 s |
| `DyadicPrimeIntervals.Run4` | 40.0 s | 25.2 s |

So the five stops were lean4lean's counters and nothing else, as their
message said. This is the rehearsal's state (artifact 14747621968), a fork
of the chain's that is not carried on: the chain's own state lists the five
as failed until the retry that counts has run.

### Round 8, 2026-11-22 10:30Z: six modules without an answer, and the limit at work

Round 8 gave up six modules after 1,800 s each. None was rejected, none
ran out of fuel: lean4lean was still on each when the run stopped waiting.

| module | the kernel's time | round 8's shard |
| --- | --- | --- |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.EncardComplexPointFibreEqEncardRingHomExtensions` | 4.1 s | 0 |
| `Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSymmetricFunctionValuesInGroundField` | 11.8 s | 9 |
| `Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ValTransOfEq` | 22.7 s | 2 |
| `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwist` | 33.0 s | 7 |
| `Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisations` | 34.2 s | 7 |
| `Development.WeilBound.CoreStatements.SesquilinearFractions.ExistsFactorThroughMultiplication` | 2,076.1 s | 2 |

The first and the last are the two of rounds 6 and 7. `ValTransOfEq` is the
module the third process of round 7's shard 2 was on when its deadline
came, so that shard had two of them. Five of the six are quick in the
kernel.

The limit did on runners what it did on the stub. Shard 0 replayed every
module of its plan but the one given up, 1,352 of 1,353, where the shards
that met that module in rounds 6 and 7 replayed 1,319 of 4,368 and 818 of
3,593. Shard 2, with two, replayed 1,352 of 1,354, and shard 9, with one,
1,352 of 1,353: what came after a module given up in its batch went to a
fresh process and was replayed. Shard 7, with two, was stopped by its
deadline at 1,119 of 1,354. This is read from the check state and the
plan; no shard's own memory log was opened for it, so that the driver given
up was gone from memory at once is inferred from the shards finishing, not
seen.

*Added 10:52Z: seen.* Shard 0's evidence (artifact 14748842102). The
driver's output has the line `FAIL ... EncardComplexPointFibreEqEncardRingHomExtensions
1804152 no answer after 1800 s: this run stopped waiting, the checker gave
no verdict`. The watchdog's table has one driver process that peaked at
10.7 GB and ended after 1,798 s. The memory log has the runner at 12.5 GB
used with swap in use at 1,501 s and at 4.8 GB with the swap free again at
1,862 s. The shard was done 3,222 s after it began, 1,352 of 1,353
replayed.

**The retry, dispatched 10:34Z, run 45013099986.** Epoch `l4r`, round 9,
from check state 14750736222: the eleven modules listed as failed, one to
a shard, two hundred minutes, a hundred times the fuel and no limit per
module. It was not held back for the chain to end. Round 9's sixteenth
shard holds the sixteen modules at the top and runs to about 11:50Z, the
retry is the long part, and nothing in it depends on those 244 modules. The
price is two states at the end, the chain's and the retry's, which the
close-out names side by side.

### Three modules lean4lean gave up on, 2026-11-21 22:52Z: its fuel, not a rejection

Round 2 recorded three failures, all with the same message:

```
Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChebyshevPrimeBounds.SmallLoop    at PI.PC.loop_run._proof_1_1: (kernel) deterministic timeout
Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run1         at PI.PrimesDyadicRS.K.run1._proof_1_1: (kernel) deterministic timeout
Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.Run3         at PI.PrimesDyadicRS.K.run3._proof_1_1: (kernel) deterministic timeout
```

`Run1.lean` is eight lines: `theorem run1 : run 32768 1612 32766 2 1 =
true := by decide +kernel`. These are computations the kernel carries out
by reduction (a count of primes in dyadic intervals); the C++ kernel takes
23, 29 and 96 s to replay the three modules. lean4lean bounds its
reduction loops with counters "set so mathlib passes"
(`Lean4Lean/FuelConfig.lean`: 100,000 unfolding steps, among others) and
ends in `deterministic timeout` when one runs out. That is lean4lean
stopping, not lean4lean finding an error, and the check state's word
"failed" for these three is wrong in the second sense until they are tried
with more fuel.

So that they can be: `L4LDriver.lean` reads `L4L_FUEL_SCALE` and multiplies
lean4lean's counters by it (the recursion depth by at most ten, since that
one costs stack); `replay_check.py plan --retry-failed TEXT...` plans only
the failed modules whose message contains one of the texts; and the merge
moves a module that passes its second attempt from `failed` to `checked`,
keeping the first message under `retried`. The workflow's inputs are
`retry_failed=fuel` and `fuel_scale`. A retry is one round, dispatched by
hand once the ordinary rounds are done, so that the chain's check states do
not fork. The front end was compiled here against a stand-in with
lean4lean's two signatures and run with a scale of 100; against lean4lean
itself it is compiled first on a runner.
