# rung3_ball_production: estimates and run manifests

The swarm box `<box>`: 32 vCPU reported as "Intel Core Processor (Haswell, no
TSX)", one thread per core, 115 GiB, no swap, shared with other workflows. Times are UTC.
Lean is `v4.35.0-rc2` (`lean/lean-toolchain`) against Mathlib `065356127b1d`
(`lean/lake-manifest.json`). Every Lake command ran in this worktree's own `lean/.lake`,
fetched fresh; no `.lake` was copied. No production shard was launched by this lane.

## Estimate before spending, 2026-10-21

Written before any compile, from the figures `main` records; every number in this section
is a prior estimate, not a measurement.

| unit | basis | estimate |
|---|---|---|
| fresh Lake fetch (`lake exe cache get`) | network-bound clone of nine packages and the Mathlib cache | about 10 min wall |
| `ZetaLean` closure of the certificate (15 modules, `lake build ZetaLean.BallCertSupport ZetaLean.BallTerm`) | hunt #132 built four `ZetaLean` modules in about 4 min | 20 to 40 min wall, under 2 core-hours |
| one staged prime tower (`scripts/68`, prime 2), 3 runs plus 3 import baselines | `scripts/67` records about 30 s wall and 42 CPU-s per run under `v4.33.0-rc2` | about 3 min |
| ten composite atoms (`scripts/66`), 3 runs | `scripts/66` records about 8 s wall per run | about 1 min |
| pilot site `B_right_06` (K = 17: 23 prime towers, 48 composites, 36 kappa products, 774 atoms by `scripts/67`'s count) | 909 CPU-s atom-only at the `v4.33.0-rc2` rates; the unsharded K = 17 file recorded USER 1369 s | 1400 to 2000 CPU-s; 5 to 35 min wall at one process, depending on Lean's in-process threads |
| planted faults: one prime-tower radius, the tail radius, `M`, and the centre's `eps'` | one shard or the root module each, recompiled against the clean pilot's oleans | under 30 min in all |

Total well under 3 hours of compute at one process at a time. The site compile is the only
unit that may exceed 20 minutes; `scripts/72` checkpoints it per module, so a restart resumes
at the first unfinished module. Stop rule: stop the newest job if `MemAvailable` falls below
20 GiB, and wait while the 1-minute load average is above 64 before starting a heavy unit.

## First attempt, 17:41 to 18:08 UTC: interrupted, kept, not used for the cost table

Work directory `<cache>/rung3-ball-production-pilot`, left as it was.
The 1-minute load average was 50 to 76 on the 32 vCPU throughout. Recorded there: two
`scripts/68` tower runs at p = 2 with their import baselines, the generation of
`B_right_06` and of the centre's sources (Python only), and the first four modules of the
`B_right_06` compile (`Base`, `Primes00`, `Primes01`, `Primes02`, all exit 0, checkpointed by
`scripts/72`). The session ended while `Primes03` was compiling; no Lean process from it
survives. Those records are a load-sensitivity cross-check only.

```runmanifest
id: rung3_ball_production-2026-10-21-attempt1
hunt: rung3_ball_production
started: 2026-10-21T16:41Z
finished: 2026-10-21T18:08Z
ran:
  - lake exe cache get into a fresh lean/.lake (inferred from the clone times of the nine packages, 16:41 to 16:45, and of Mathlib.olean, 16:44)
  - a lake build of the certificate's ZetaLean imports (inferred from the 15 ZetaLean oleans dated 17:39 to 17:41)
  - hunts/rung3_ball_production/pilot.py tower --prime 2 --repeat 3, stopped after two repeats
  - hunts/rung3_ball_production/pilot.py site --site B_right_06, stopped during Primes03
  - hunts/rung3_ball_production/pilot.py centre-eps --generate-only
outcome: Lean and the ZetaLean closure were set up and four of the ten pilot-site modules compiled with exit 0 before the session ended; nothing from this attempt enters the cost table
artifacts:
  - <cache>/rung3-ball-production-pilot/runs.jsonl
  - <cache>/rung3-ball-production-pilot/site/B_right_06/out/checkpoints/CB_right_06
```

## Second attempt, from 21:29 UTC: estimate before spending

Fresh work directory `<cache>/rung3-ball-production-pilot-2`, so every
number in `pilot.json` comes from one session. `scripts/72` is `main`'s version (merge commit
`e08e801da`), byte-identical to `origin/main` `5da48eed7`. The `ZetaLean` closure built at
17:38 to 17:41 is reused: no file under `lean/` differs between `fb647bfc7` and `5da48eed7`.

| unit | basis (first attempt, at load 50 to 76) | estimate |
|---|---|---|
| tower p = 2, 3 runs plus 3 baselines | 108 to 125 s wall per tower run, 13 to 73 s per baseline | 7 to 9 min |
| tower p = 1801, 2 runs plus 2 baselines | text about 3 times the p = 2 tower | 8 to 15 min |
| ten composite atoms (`scripts/66`), 3 runs plus 3 baselines | not run yet | 2 to 4 min |
| `B_right_06`, 10 modules, one process | `Base` 19 s, `Primes00` 166 s, `Primes01` 135 s, `Primes02` 117 s wall | 15 to 30 min; checkpointed per module |
| import-only probes, 10 modules, 2 runs each | 13 s for the warm `BallTerm` baseline | 5 to 12 min |
| axioms print, three faults, centre eps' probes, mirror | one shard or the root module per fault | 15 to 30 min |

In all, about 1 to 2 hours of wall time at one Lean process at a time, every unit gated on
a 1-minute load average of at most 64 and `MemAvailable` of at least 30 GiB. Added after
this estimate, each under ten minutes: the `-j1` tower and the `-j1` shard, a 100-atom
composite file, and the tower with Lean's linters off.

### Decision recorded at 22:07 UTC, before the p = 1801 tower ran

The first four prime shards of `B_right_06` in this attempt cost, net of an import of
about 11 CPU-s, between 61 and 85 CPU-s per tower, while their CPU per source byte fell as
the primes grew (from about 2.8e-4 in `Primes00`, p = 2 to 17, to about 1.8e-4 in
`Primes03`, p = 67 to 83). So "CPU follows the text" is not supported by the shards, and
"CPU per tower is flat in p" is not tested above p = 89. The projection therefore prices
the towers both ways, and the request uses the larger total. The `scripts/68` towers at
p = 2 and p = 1801 are reported beside the shards as the only evidence on the dependence
on p; they do not choose the model.

Correction at 22:25 UTC, after the site finished: the per-tower figures above miscounted
the towers in `Primes00` (seven, not six) and `Primes01` (five, not six). With the right
counts the five shards cost 69 to 75 CPU-s per tower net of import, flat in p up to 89,
while the per-byte trend stands. The decision is kept as recorded: both models are
priced, and the request uses the larger, which is the per-byte one.

## Second attempt: what ran (UTC)

- 21:29 to 21:37: `pilot.py tower --prime 2 --repeat 3`, gated only before its first run
  (load 57 there); its third tower run started at a load of 68 and ran through a burst to
  about 160 from other workflows, which is why its wall time is long and its CPU is not.
- 21:37 to 21:46: the ten-atom composite unit waited at the gate (load 100 to 160), and the
  driver was stopped while waiting, with no Lean process running.
- From 21:46, a second driver with two gates: at most 64 before the heavy units (the site
  compile and the fault recompiles), at most 96 before single small files (under two
  minutes, one process each), `MemAvailable` at least 30 GiB throughout. From that
  restart on, every Lean run waited at the gate, not only a batch's first. A logger
  appended the 1-minute load every 10 s to `loadlog.tsv` from 21:50.
- 21:46 to 21:48: ten composite atoms, 3 runs plus 3 baselines.
- 21:48 to 22:11: `pilot.py site --site B_right_06`: generation (2 s) and the ten-module
  compile at one process, started at a load of 63; the 1-minute load sampled during it
  ran from 62 to 121, mean 90.
- 22:11 to 22:17: `pilot.py axioms`, then `pilot.py imports --repeat 2` (20 probes).
- 22:16 to 22:19: the three faults, `pilot.py fault --kind tower-rad`, `tail-rad`, `M`, each
  a recompile of one module against a copy of the clean output root; each refused.
- 22:19 to 22:20: `pilot.py centre-eps`: the centre's sources generated again (Python
  only, 27 s; the centre was not compiled) and four probes of its last step.
- 22:20: `pilot.py mirror` (Python only).
- 22:20 to 22:26: `pilot.py tower --prime 2 --repeat 3 --lean-threads 1`.
- 22:26 to 22:34: `pilot.py shard --module CB_right_06/Primes02.lean --lean-threads 1`,
  one recompile of that shard at one thread into a scratch olean.
- 22:34 to 22:37: `pilot.py tower --prime 1801 --repeat 2`.
- 22:36 to 22:45: a third driver, queued behind the second: `pilot.py composite --atoms 100
  --repeat 3` (22:36 to 22:40), then `pilot.py tower --prime 2 --repeat 3 --lean-opt
  linter.all=false` (22:40 to 22:45). No Lean process of this lane ran after it.
- After 22:45: `report.py` wrote `pilot.json` from `runs.jsonl`, the checkpoints and the
  load log; `render_docs.py` wrote its tables into `PILOT.md` and `OWNER_MEMO.md`.

```runmanifest
id: rung3_ball_production-2026-10-21-attempt2
hunt: rung3_ball_production
started: 2026-10-21T21:29Z
finished: 2026-10-21T22:45Z
ran:
  - hunts/rung3_ball_production/pilot.py tower --prime 2 --repeat 3
  - hunts/rung3_ball_production/pilot.py composite --atoms 10 --repeat 3
  - hunts/rung3_ball_production/pilot.py site --site B_right_06
  - hunts/rung3_ball_production/pilot.py axioms --site B_right_06
  - hunts/rung3_ball_production/pilot.py imports --site B_right_06 --repeat 2
  - hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind tower-rad
  - hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind tail-rad
  - hunts/rung3_ball_production/pilot.py fault --site B_right_06 --kind M
  - hunts/rung3_ball_production/pilot.py centre-eps
  - hunts/rung3_ball_production/pilot.py mirror --site B_right_06
  - hunts/rung3_ball_production/pilot.py tower --prime 2 --repeat 3 --lean-threads 1
  - hunts/rung3_ball_production/pilot.py shard --site B_right_06 --module CB_right_06/Primes02.lean --lean-threads 1
  - hunts/rung3_ball_production/pilot.py tower --prime 1801 --repeat 2
  - hunts/rung3_ball_production/pilot.py composite --atoms 100 --repeat 3
  - hunts/rung3_ball_production/pilot.py tower --prime 2 --repeat 3 --lean-opt linter.all=false
  - hunts/rung3_ball_production/report.py
outcome: the pilot site compiled with every module exit 0 and only the three standard axioms, all three planted site faults and both eps' perturbations below the bound were refused, and the costs and projection in pilot.json were measured; no production shard was launched
artifacts:
  - hunts/rung3_ball_production/pilot.json
  - <cache>/rung3-ball-production-pilot-2/runs.jsonl
  - <cache>/rung3-ball-production-pilot-2/loadlog.tsv
  - <cache>/rung3-ball-production-pilot-2/site/B_right_06/out/results/CB_right_06.json
```

## Resumed 2026-10-26: `decide +kernel` re-pricing pilot, estimate before spending

Owner decision of 2026-10-26 (`MISSION.md`): this box takes pilots under one core-hour
only; this unit was pre-approved by the coordinator under that cap. One Lean process at a
time, `nice -n 10`, gated on a 1-minute load of at most 64 and `MemAvailable` of at least
30 GiB before each run. Instrument: `decide_pilot.py`, work directory
`<cache>/rung3-ball-production-decide`. Every figure in this table is a prior estimate.

| unit | basis | estimate |
|---|---|---|
| import-only baseline, 2 runs | about 10 CPU-s each on 2026-10-21 | under 1 min |
| `scripts/68` tower p = 2, staged equalities by `norm_num`, equalities only, 1 run | 2.09 CPU-s per atom, 30 atoms, plus import | about 75 CPU-s |
| the same tower with every staged equality by `decide +kernel`, equalities only and full file, 2 runs each | unknown; bounded above by the `norm_num` run if the kernel is no slower | under 6 min |
| planted fault: one staged literal one unit of 2^-64 off, 1 run | as one decide run | under 2 min |
| one composite product and one kappa product, `decide +kernel` (2 runs) and `norm_num` (1 run) each | about 0.67 CPU-s per composite atom plus import | under 3 min |
| whole-tower `dirichletTermBallB ... = lit := by decide +kernel`, 1 run | unknown; `Nat.sqrt` and the recursive tower in the kernel | capped at 10 min wall by a timeout |

Total under 30 core-minutes, well inside the one core-hour cap. Threshold recorded before
any run: a full tower (the `decide +kernel` file with its containment theorem, net of the
import baseline) at **at most 10 CPU-s** confirms the repricing of production to roughly
20 to 90 core-hours; above that, the `norm_num` price in `OWNER_MEMO.md` (416 core-hours)
stands.

## Resumed 2026-10-26: what ran (UTC)

- Before 12:56: `decide_pilot.py emit`, then a one-off smoke compile of
  `Composite_decide.lean` and `WholeEval.lean` outside the log, to check the syntax before
  the logged run.
- 12:56 to 13:01: `decide_pilot.py run`, 16 Lean runs, one at a time.
- 13:03 to 13:05: `decide_pilot.py run --only` the full `norm_num` tower control and
  the three whole-route files (6 runs), added after the first run showed that the whole
  decision finished in seconds. They are inside the same pre-approved one core-hour unit.
- Then `decide_pilot.py summarize` wrote `pilot.json`'s `decide_kernel` section.

In all, 22 logged Lean runs and 7.4 core-minutes of CPU, against the estimate of under
30.

```runmanifest
id: rung3_ball_production-2026-10-26-decide
hunt: rung3_ball_production
started: 2026-10-26T12:50Z
finished: 2026-10-26T13:05Z
ran:
  - hunts/rung3_ball_production/decide_pilot.py emit
  - hunts/rung3_ball_production/decide_pilot.py run
  - hunts/rung3_ball_production/decide_pilot.py run --only TowerNormNum.lean TowerWhole_p2.lean TowerWhole_p1801_box.lean TowerWholeFault_p2.lean
  - hunts/rung3_ball_production/decide_pilot.py summarize
outcome: every decide +kernel file with correct literals was accepted with only the three standard axioms, both planted one-unit faults were refused at the named declaration, the staged variant missed the 10 CPU-s threshold (43.4 net) and the whole-decision tower met it (3.4 and 5.3 net), repricing production to 50 to 58 core-hours by extrapolation, conditional on a generator change; no production shard was launched
artifacts:
  - hunts/rung3_ball_production/pilot.json (decide_kernel)
  - <cache>/rung3-ball-production-decide/runs.jsonl
  - <cache>/rung3-ball-production-decide/src
```

## Resumed 2026-10-26: the assembly harness

Estimate before spending: `Support.lean` about 15 CPU-s (one module, against the built
`ZetaLean`); the stub module about 20 CPU-s; the harness about 1,100 small `norm_num`
calls, guessed at 2 to 10 CPU-min. Under 15 core-minutes in all, one process, gated as
above. Measured: 12.7, 17.8 and 124.2 CPU-s.

```runmanifest
id: rung3_ball_production-2026-10-26-assembly
hunt: rung3_ball_production
started: 2026-10-26T13:09Z
finished: 2026-10-26T13:14Z
ran:
  - hunts/rung3_ball_production/assembly.py --stubs <cache>/rung3-ball-production-assembly --real B_right_06
  - lake env lean --root=hunts/rung3_ball_production/lean -o <cache>/rung3-ball-production-assembly/Rung3Assembly/Support.olean hunts/rung3_ball_production/lean/Rung3Assembly/Support.lean
  - lake env lean --root=<cache>/rung3-ball-production-assembly -o <cache>/rung3-ball-production-assembly/StubSites.olean StubSites.lean (LEAN_PATH adds the work directory and the pilot site's gen directory)
  - lake env lean <cache>/rung3-ball-production-assembly/Harness.lean (same LEAN_PATH)
  - hunts/rung3_ball_production/assembly.py --check --real B_right_06 --record <cache>/rung3-ball-production-assembly/harness.record.log
outcome: Support.lean and the emitted assembly body elaborated with exit 0 and no errors against 214 stub site interfaces and the real B_right_06 oleans; the three theorems rest on the three standard axioms and the 214 stubs only; no production shard was launched and davenport_heilbronn is not proved
artifacts:
  - hunts/rung3_ball_production/lean/Rung3Assembly/Assembly.lean
  - hunts/rung3_ball_production/lean/Rung3Assembly/Separation.lean
  - hunts/rung3_ball_production/pilot.json (assembly_harness)
  - <cache>/rung3-ball-production-assembly/harness.log
```

The harness log's exit status (0) was recorded by the shell at the time and prepended as
`rc=0` to `harness.record.log`, which `--record` parses.
