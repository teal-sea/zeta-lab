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
above. Measured: 12.7, 17.8 and 124.2 CPU-s. CI then refused the committed emitted files,
which are not `module` files and cannot be (`PILOT.md` section 8). So `Support.lean` became
a `module`, the emitted files moved out of the tree with a SHA-256 pin, and the three
compiles ran again from 13:16 (10.6, 17.1 and 124.1 CPU-s, exit 0, no errors). The record
in `pilot.json` is the second run.

```runmanifest
id: rung3_ball_production-2026-10-26-assembly
hunt: rung3_ball_production
started: 2026-10-26T13:09Z
finished: 2026-10-26T13:21Z
ran:
  - hunts/rung3_ball_production/assembly.py --stubs <cache>/rung3-ball-production-assembly --real B_right_06
  - (from 13:16, after the module change) hunts/rung3_ball_production/assembly.py --out <cache>/rung3-ball-production-assembly --stubs <cache>/rung3-ball-production-assembly --real B_right_06 --pin, then the three compiles below again
  - lake env lean --root=hunts/rung3_ball_production/lean -o <cache>/rung3-ball-production-assembly/Rung3Assembly/Support.olean hunts/rung3_ball_production/lean/Rung3Assembly/Support.lean
  - lake env lean --root=<cache>/rung3-ball-production-assembly -o <cache>/rung3-ball-production-assembly/StubSites.olean StubSites.lean (LEAN_PATH adds the work directory and the pilot site's gen directory)
  - lake env lean <cache>/rung3-ball-production-assembly/Harness.lean (same LEAN_PATH)
  - hunts/rung3_ball_production/assembly.py --real B_right_06 --record <cache>/rung3-ball-production-assembly/harness.record.log --check
outcome: Support.lean and the emitted assembly body elaborated with exit 0 and no errors against 214 stub site interfaces and the real B_right_06 oleans; the three theorems rest on the three standard axioms and the 214 stubs only; no production shard was launched and davenport_heilbronn is not proved
artifacts:
  - hunts/rung3_ball_production/lean/Rung3Assembly/Support.lean
  - <cache>/rung3-ball-production-assembly/Rung3Assembly/Assembly.lean and Separation.lean (pinned in pilot.json, assembly_emitted)
  - hunts/rung3_ball_production/pilot.json (assembly_harness)
  - <cache>/rung3-ball-production-assembly/harness.log
```

The second run's shell wrote the harness's exit status into `harness.record.log` as
`rc=<status>`, which `--record` parses.

## Follow-up 2026-10-26: the opt-in whole-tower generator mode

**The change.** The coordinator extended this lane's scope under the owner's production
grant. `scripts/69_rung3_ball_generate.py` gained `tower_mode="whole"` and
`scripts/60_rung3_generate.py` a `--tower {staged,whole}` flag, `staged` by default. In
whole mode each prime tower is one `private lemma ev_whole : dirichletTermBallB ... = Sq_10
:= by decide +kernel` plus `theorem pilot_contains_cpow` through
`contains_dirichletTermBallB`, in the same `Prime_<p>` namespace with the same exported
names, so nothing downstream changes. The literal is the mirror's `dirichletTermBox2`. The
generator raises if it differs from the staged chain's last ball in any field. **Why:**
section 7 of `PILOT.md` measured 3.4 to 5.3 CPU-s per tower this way against about 66
staged, which reprices production by a factor of about 7.

**Byte identity of the default.** Before the change (at `304dee102`) and after it,
`scripts/60 ... --arith ball --shard --only <id>` wrote 94 files for `B_right_06` and the
centre. Their SHA-256 lists compare equal (`cmp` of the two sorted `sha256sum` lists).
`tests/test_rung3_ball_whole_tower.py` pins that an explicit `staged` equals the default,
and the hunt test pins the default `B_right_06` sources against the SHA-256 recorded on
2026-10-21.

**Estimate before spending** (prior figures): generation a few seconds. The site in whole
mode is 5 modules: towers at about 4 CPU-s each (23 of them), the composites, terms and
root at their 2026-10-21 cost of about 150 to 200 CPU-s, so 250 to 400 CPU-s. Two fault
recompiles of `Primes.lean`, about 110 CPU-s each. Four import probes, about 12 CPU-s
each. Under 15 core-minutes, one process, `nice -n 10`, gated as before; outputs under
`<cache>/rung3-ball-production-whole`, expected well under 300 MB.

### What ran (UTC)

- 13:40 to 13:42: `whole_pilot.py site`, which generated the site (3 s) and compiled 5
  modules at one process (111.5 s wall); the load was 24 at the gate.
- 13:43 to 13:45: `whole_pilot.py imports` (4 probes), then `whole_pilot.py faults`
  (2 recompiles). That first fault run's records are kept in `runs.first-faults.jsonl`.
  They were re-run at 13:45 to 13:46 after a fix to how the instrument names the enclosing
  namespace of an error; the outcomes did not change.
- 13:46 to 14:05: `whole_pilot.py census`, added after the estimate above. It is Python
  only: every site emitted in whole mode in memory, nothing written but one JSON line per
  site. Timed on its first four sites at 20 to 69 s each and estimated at about 50
  core-minutes, it was split across 3 processes (`--part`). It used 50.7 CPU-minutes.
- Then `whole_pilot.py summarize` wrote `whole_site` and `whole_projection` into
  `pilot.json`.

In all, about 6 core-minutes of Lean and 51 of Python. The whole follow-up was just under
the one core-hour cap for this box. The census was not in the estimate, which is a miss
recorded here. Disk: 17 MB under `<cache>/rung3-ball-production-whole`.

```runmanifest
id: rung3_ball_production-2026-10-26-whole
hunt: rung3_ball_production
started: 2026-10-26T13:40Z
finished: 2026-10-26T14:05Z
ran:
  - hunts/rung3_ball_production/whole_pilot.py site
  - hunts/rung3_ball_production/whole_pilot.py imports
  - hunts/rung3_ball_production/whole_pilot.py faults
  - hunts/rung3_ball_production/whole_pilot.py census --part {0,1,2} --parts 3
  - hunts/rung3_ball_production/whole_pilot.py summarize
outcome: B_right_06 compiled in whole mode with every module exit 0 (163.6 CPU-s, 16.8 MB of oleans, against 1861 CPU-s and 180 MB staged); both one-unit tower faults refused at ev_whole; the import ratio re-measured at 0.70; the census emitted all 215 sites with every whole-tower literal equal to the staged chain's, and production re-projects to 29.8 core-hours and 14.8 to 16.0 GB of oleans; no production shard was launched
artifacts:
  - hunts/rung3_ball_production/pilot.json (whole_site, whole_projection)
  - <cache>/rung3-ball-production-whole/runs.jsonl
  - <cache>/rung3-ball-production-whole/site/out/results/CB_right_06.json
  - <cache>/rung3-ball-production-whole/census.jsonl and census.{0,1,2}.jsonl
```

## Follow-up 2026-10-26: the production workflow (not yet run)

`.github/workflows/rung3-production.yml` and `production.py` were added; `PRODUCTION.md`
section 2 describes them. They were pushed **without** `RUN_REQUEST.json`, so nothing
runs until the coordinator's 'go' and the request commit.

Smoke on this box before pushing, all Python except two small Lean runs under the usual
gate:
- `production.py plan` on the calibrate and full requests;
- `assign(20)`: 215 sites in 20 jobs of 1.45 to 1.51 projected core-hours each;
- `preflight` and `toplevels` against this checkout;
- `axioms` and `record` on the whole-mode pilot site, where `upper_B_right_06` printed
  the three standard axioms and the record gave 16,758,440 olean bytes;
- `fault`, then `scripts/72`, then `refused` in `<cache>/rung3-ball-production-wfsmoke`.
  The first try was refused by `scripts/72`'s manifest byte check, not by the kernel: the
  fault step now records the planted file's size, as `pilot.py fault` does. The second
  try was refused by the kernel at `Prime_2.ev_whole`, after 44.8 CPU-s.

**Estimate for the calibration run**, before spending (at this box's rates; a runner's
speed is unmeasured): the centre at 2,173 CPU-s and `B_right_06` at 162. That is about 40
minutes at one process, plus about 15 to 25 minutes of setup (cache get and the
`ZetaLean` closure), so about 1 hour of one job. It runs on free GitHub Actions minutes.

## 2026-10-26: the calibration run on GitHub Actions

After the coordinator's 'go', `RUN_REQUEST.json` (calibrate: the centre and
`B_right_06`) was committed at `c697df4f0` and pushed; that push started run
40340279740. The estimate above was about 1 hour of one job; it took 15.5 minutes. The
figures are in `PILOT.md` section 10.

```runmanifest
id: rung3_ball_production-2026-10-26-calibrate-runner
hunt: rung3_ball_production
started: 2026-10-26T14:30Z
finished: 2026-10-26T14:47Z
ran:
  - .github/workflows/rung3-production.yml, mode calibrate, run 40340279740 (https://github.com/teal-sea/zeta-lab/actions/runs/40340279740), commit c697df4f0
  - gh run download 40340279740 -n rung3-production-record-job0-attempt1 (the record, into <cache>/rung3-ball-production-calib)
outcome: plan, sites 0 and verdict succeeded; the centre (1348.1 CPU-s, 556.6 s wall, 11.32 GB peak RSS, 343.5 MB of oleans) and B_right_06 (65.9 CPU-s, 7.20 GB, 16.8 MB) compiled under --tower whole with exactly the three standard axioms; setup 295 s; the full plan is re-sized to 20 jobs at one Lean process each, every job bounded at 1.43 to 1.49 h
artifacts:
  - hunts/rung3_ball_production/pilot.json (calibration_runner)
  - GitHub artifacts rung3-production-job0-attempt1 (oleans of both sites) and rung3-production-record-job0-attempt1, 30-day retention
```

## 2026-10-26: the full run cancelled, the cross-site name collision fixed

- 14:50: full run 40343451044 started from `RUN_REQUEST.json` at `0f42610de`.
- Minutes later, the two-root import probe (`PILOT.md` section 11) showed that site roots
  collide on `ZetaLean.DH.Cert.Prime_<p>.*`. The coordinator cancelled the run at once.
  Its final state: `cancelled`, ended 14:55:15. Jobs 0 to 5 ran about 4 minutes each,
  through setup only (about 24 runner-minutes); no site compiled, and their artifacts hold
  only records of about 250 bytes. The other 15 jobs and the fault job were cancelled while
  queued. The verdict job failed, as it must for an incomplete run.
- The fix, in whole mode only, is `Prime_<sid>_<p>`. The staged default was re-checked
  byte-identical.
- On this box, one Lean process at a time beside 3 Python processes for the census:
  - `B_right_06` re-run through `whole_pilot.py site`, `faults` and `imports`, in
    `<cache>/rung3-ball-production-whole2`;
  - `B_bottom_23` generated and compiled there (`site2`, 159.2 CPU-s);
  - the two-root probe (9.8 CPU-s);
  - the assembly harness with both real sites (126.8 CPU-s);
  - `production.py fault` and `refused` again (refused at `Prime_B_right_06_2.ev_whole`);
  - the centre import probe on the runner oleans (2 x 3 runs, under 20 CPU-s each).
- `whole_pilot.py names` (Python, 3 processes) emitted all 215 sites in whole mode and
  recorded their public names (`namespace_census`).

About 12 core-minutes of Lean and the census's Python, about 50 core-minutes, together
under the one core-hour cap. Next: the calibration re-run with the new names (`"attempt":
2` in the request), then a new full request for the coordinator's 'go'.

```runmanifest
id: rung3_ball_production-2026-10-26-calibrate-runner-attempt2
hunt: rung3_ball_production
started: 2026-10-26T15:32Z
finished: 2026-10-26T15:48Z
ran:
  - .github/workflows/rung3-production.yml, mode calibrate, "attempt": 2, run 40350287309 (https://github.com/teal-sea/zeta-lab/actions/runs/40350287309), commit 4bac8d79d
  - gh run download 40350287309 -n rung3-production-record-job0-attempt1 (into <cache>/rung3-ball-production-calib/40350287309)
outcome: success; with site-qualified tower namespaces the centre (1229.1 CPU-s, 533.8 s wall, 11.31 GB, 343.5 MB of oleans) and B_right_06 (58.1 CPU-s, 7.19 GB) compiled with exactly the three standard axioms; setup 308 s; the full plan is bounded at 1.32 to 1.37 h per job
artifacts:
  - hunts/rung3_ball_production/pilot.json (calibration_runner; the first run is calibration_runner_v1)
  - GitHub artifacts of run 40350287309, 30-day retention
```

## 2026-10-26: the full run, and the assembly on this box (estimate before spending)

Full run 40353536947 started at 15:52Z from `RUN_REQUEST.json` at `85cabd55b`. Its
watcher, a detached process on this box (`<cache>/rung3-ball-production-full/watcher.log`),
waits for the run's terminal state and writes it to `terminal.json`; its outcome is
recorded below when it ends. No second request will be pushed while the run is live.

The coordinator placed the assembly on this box, with the oleans on `/dev/shm`, on these
conditions:

- start only while `MemAvailable` is above 45 GiB and the load is below 64, and abort
  below 20 GiB;
- one Lean process under `nice -n 10`, with `lean` and `LEAN_PATH` only, against this
  checkout's own `lean/.lake`;
- downloads straight to `/dev/shm`, each zip checked against GitHub's digest;
- everything in `/dev/shm` deleted at the end, keeping receipts, hashes and logs.

Prepared before the verdict (measured):

- **The combined `LEAN_PATH` for the separation.** Hunt #137's oleans
  (`<cache>/rh100-out`) carry their own `ZetaLean.Rigor`, `IntervalExp` and
  `IntervalCExp`. Their bytes differ from this checkout's, but `lean/CompareOleans.lean`
  (in this hunt) reads all three parts of each and finds every constant's name, kind, type
  and value identical (264, 155 and 262 constants); a control pair of different modules
  is reported as different. So one overlay directory, holding this checkout's `ZetaLean`
  oleans plus hunt #137's `HardyZ`, serves both. A probe importing `RHHeight100.Main100`
  with `Rung3Assembly.Support` through that overlay elaborated with no error (12.3 CPU-s,
  6.7 GB), and checked `RHHeight100.rh_height_hundred : RHHeight.RHHeight100`.
- `tests/test_epstein.py::test_no_offline_zero_below_the_pinned_one` runs now, as one
  process.

**Estimate**, from this hunt's measurements:

| unit | basis | estimate |
|---|---|---|
| collect: 20 zips (about 5 GB compressed, about 16 GB unzipped) into `/dev/shm`, SHA-256 each | the calibration artifact (113 MB) took seconds | 5 to 10 min wall, under 5 CPU-min |
| `Support.olean` | 10.6 CPU-s measured | under 1 min |
| `Assembly.lean`, 215 roots | the two-site harness 127 CPU-s, plus imports | 5 to 15 CPU-min, 17 to 18 GB RSS |
| `Separation.lean` and `#print axioms` on every final declaration | the probe above, plus the 215-root import again | 5 to 10 CPU-min |
| four planted faults on the production output (tower radius, tail radius, M, centre eps') | 35 to 110 CPU-s each on 2026-10-21 and today | under 8 CPU-min |

That totals 20 to 40 core-minutes, under the one core-hour cap. Anything beyond goes back
to the coordinator first.

### The full run's terminal state, the fault re-run, and the assembly (measured)

- **Run 40353536947** (watcher's `terminal.json`): conclusion `failure`, ended
  17:44:11Z. Plan and all 20 site jobs succeeded. `sites fault (full)` failed because
  `bash -e` ended its step before the exit code was captured, so its evidence is void
  (`PILOT.md` section 13). The verdict job failed because no `fault.json` existed, as it
  had to. The records give 215/215 sites `ok`, every site theorem on exactly `propext`,
  `Classical.choice` and `Quot.sound`, 16.1 runner core-hours, and 15,123,966,128 bytes
  of oleans.
- **Run 40372531479** at `78e91a542` (`"mode": "fault"`, `"completes_run": 40353536947`):
  success. The fault was refused at `Prime_B_right_06_2.ev_whole`, and its logs are kept
  as `rung3-production-fault-logs-attempt1` (90 days). `production.py verdict --runs
  40353536947 40372531479` counts the pair.
- **On this box**, one Lean process at a time under `nice -n 10`, gated:
  - `collect`: 20 zips, 4,744,646,464 bytes, straight to `/dev/shm`, every SHA-256 equal
    to GitHub's digest, 106 CPU-s and 179 s of wall;
  - the four planted faults against the downloaded `B_right_06` oleans, each refused
    where planted, with only the touched module recompiled (`pilot.json`
    `production.box_faults`);
  - `assemble`: Support 9.1 CPU-s; Assembly 85.3 CPU-s at 17.87 GB peak RSS; Separation
    11.8 CPU-s; the axioms print 11.6 CPU-s. `MemAvailable` started at 50.1 to 50.4 GiB
    and its low was 48.9 GiB.

  Then `/dev/shm` was deleted, and the receipts (site-root and assembly olean SHA-256,
  logs, `collected.json`, `assemble.json`) were kept in
  `<cache>/rung3-ball-production-full/receipts`. On-box total: about 10 core-minutes,
  inside the estimate of 20 to 40.

```runmanifest
id: rung3_ball_production-2026-10-26-production
hunt: rung3_ball_production
started: 2026-10-26T15:52Z
finished: 2026-10-26T18:00Z
ran:
  - .github/workflows/rung3-production.yml mode full, run 40353536947 (https://github.com/teal-sea/zeta-lab/actions/runs/40353536947), commit 85cabd55b
  - .github/workflows/rung3-production.yml mode fault, run 40372531479 (https://github.com/teal-sea/zeta-lab/actions/runs/40372531479), commit 78e91a542
  - hunts/rung3_ball_production/production.py verdict --runs 40353536947 40372531479
  - hunts/rung3_ball_production/production.py collect --run 40353536947 --dest /dev/shm/rung3-assembly
  - hunts/rung3_ball_production/pilot.py fault --kind tail-rad and --kind M, production.py fault + scripts/72 + refused, pilot.py centre-eps (work directory <cache>/rung3-ball-production-faults4)
  - hunts/rung3_ball_production/production.py assemble --dest /dev/shm/rung3-assembly --overlay <cache>/rung3-ball-production-assembly/overlay --rh100 <cache>/rh100-out
outcome: theorem davenport_heilbronn, dh_zero_located, dh_zero_located' and dh_separation_hundred compiled with zero sorry, and all 17 final declarations print exactly propext, Classical.choice and Quot.sound; 215/215 sites ok; every planted fault refused at its declaration; /dev/shm cleared
artifacts:
  - hunts/rung3_ball_production/RESULTS.md
  - hunts/rung3_ball_production/pilot.json (production)
  - <cache>/rung3-ball-production-full/receipts
```

## 2026-10-26: the strip re-assembly on this box (estimate before spending)

Door 2 of `RESULTS.md`: one theorem, `davenport_heilbronn_strip`, in a new emitted module
`Strip.lean` that imports `Rung3Assembly.Assembly` alone (`assembly.py`). `Assembly.lean`
and `Separation.lean` are emitted byte for byte as before (`cmp` against the copies in the
first receipts). The site oleans are gone from this box, so `collect` downloads run
40353536947's 20 artifacts again.

Conditions set by the coordinator for this run:

- **No Lake build.** No `lake build`, `lake update` or `lake exe cache` in this worktree;
  the `ZetaLean` oleans are this checkout's of 2026-10-21 under `lean/.lake`, used as last
  time through the overlay, and only `lake env lean` runs. Their SHA-256 list is taken
  before and after.
- **On disk, not `/dev/shm`.** A guarded `leanchecker` job of about 7 GB holds RAM, so
  `--dest` is `<cache>/rung3-ball-production-strip-20261026`, on `/` (47 GB free).
  `production.py` does not hard-code `/dev/shm`: `collect` and `assemble` already take
  `--dest`, so nothing was patched.
- **Memory.** `MemAvailable` above 20 GiB throughout: `run_guarded` refuses to start a
  Lean process below 45 GiB and kills it below 20 GiB; `ulimit -s unlimited` before every
  Lean process; one Lean process at a time under `nice -n 10`.
- **Integrity.** `collect` checks each zip's SHA-256 against GitHub's digest and each
  site's root olean and root checkpoint; the 215 root oleans are also compared with the
  SHA-256 list in the first receipts.

A syntax smoke ran first, outside the log: the emitted `Strip.lean` body after a scratch
file that states `dh_zero_located` as a stub (`lake env lean`, importing
`ZetaLean.DHAnalytic` only). Exit 0, 8.8 CPU-s, 6.7 GB; it printed the three standard
axioms and the stub, as a stub harness must.

**Estimate**, from the first assembly's measurements (`production.assembly_box`):

| unit | basis | estimate |
|---|---|---|
| `collect`: 20 zips, 4,744,646,464 bytes, to disk; about 15.1 GB unzipped | 106 CPU-s and 179 s of wall into `/dev/shm` | 100 to 150 CPU-s; 3 to 10 min wall, since the unzip writes to disk |
| `Support.olean` | 9.1 CPU-s, 3.8 GB | about 10 CPU-s |
| `Assembly.lean`, 215 roots | 85.3 CPU-s, 17.87 GB | 85 to 120 CPU-s, 17.5 to 18.5 GB peak RSS |
| `Separation.lean` | 11.8 CPU-s, 17.57 GB | about 12 CPU-s, the same RSS |
| `Strip.lean`, which imports `Assembly` | the same import as `Separation` | 10 to 20 CPU-s, the same RSS |
| `#print axioms`, 18 declarations | 11.6 CPU-s | about 12 CPU-s |
| `strip-faults`: the control and two planted faults | three imports as above | 30 to 60 CPU-s, one process at a time |

In all, 250 to 400 CPU-s (4 to 7 core-minutes) and 17.5 to 18.5 GB peak RSS per Lean
process. With the oleans in the page cache instead of a tmpfs, `MemAvailable` is expected
to start near 65 GiB and stay above 40 GiB. Disk: about 15.1 GB of oleans plus one zip.

### What ran (UTC, measured)

- Before 23:36: the syntax smoke above (8.8 CPU-s).
- 23:36:19 to 23:39:31: `production.py collect --request <receipts>/RUN_REQUEST.full.json
  --run 40353536947 --dest <cache>/rung3-ball-production-strip-20261026`. The request is
  the full-mode one of `85cabd55b`, copied into the receipts, because the committed
  `RUN_REQUEST.json` is the later fault request, which names one job. 20 zips,
  4,744,646,464 bytes, every SHA-256 equal to GitHub's digest and to the first collect's
  `collected.json`. 116.8 CPU-s, 192 s of wall, 71 MB peak RSS. Then, by hand: the 215
  root oleans' SHA-256 equal the first receipts' list, all 215 root checkpoints are
  present, and the output directory holds 15,125,743,627 bytes, as the first time.
- 23:40:20 to 23:42:11: `production.py assemble` (`ulimit -s unlimited`, `nice -n 10`):
  Support 8.2 CPU-s at 3.90 GB; Assembly 73.8 CPU-s at 18.03 GB; Separation 10.9 at
  17.71 GB; Strip 10.7 at 17.62 GB; the axioms print 10.8 at 17.72 GB. All exit 0, none
  stopped by the guard; `MemAvailable` started at 65.0 to 66.1 GiB and its low was
  63.7 GiB. All 18 declarations print exactly `propext`, `Classical.choice` and
  `Quot.sound`. The Support, Assembly and Separation oleans hash exactly as in the first
  receipts.
- 23:42 to 23:43: `production.py strip-faults`: the control 11.3 CPU-s, exit 0; `s.re <
  19/25` 11.1 CPU-s and `s.re ≠ 4/5` 10.3 CPU-s, each exit 1 and refused at
  `davenport_heilbronn_strip`; each at about 17.6 GB, `MemAvailable` low 64.9 GiB.
- After: the `ZetaLean` build's 195 files hash as before the run, and no file under
  `lean/.lake/build` is newer than the run's start. The record went into `pilot.json`
  `production.strip_assembly`, the receipts into
  `<cache>/rung3-ball-production-full/receipts-strip-20261026`.

Against the estimate: about 280 CPU-s in all (collect 116.8; assemble 121.5 for the
driver, 114.4 of it Lean; the faults 32.7; the smoke 8.8), inside 250 to 400; peak RSS
18.03 GB, inside 17.5 to 18.5; `MemAvailable` low 63.7 GiB, above the 40 expected.
Assembly took less CPU than the first time (73.8 against 85.3) with the oleans in the
page cache straight after the unzip; that comparison is one run each.

Then the unpacked oleans (`<cache>/rung3-ball-production-strip-20261026`, about 15 GB)
were deleted, keeping the receipts, with the zips' digests in `collected.json`.

```runmanifest
id: rung3_ball_production-2026-10-26-strip
hunt: rung3_ball_production
started: 2026-10-26T23:36Z
finished: 2026-10-26T23:43Z
ran:
  - hunts/rung3_ball_production/production.py collect --request <receipts>/RUN_REQUEST.full.json --run 40353536947 --dest <cache>/rung3-ball-production-strip-20261026
  - hunts/rung3_ball_production/production.py assemble --dest <cache>/rung3-ball-production-strip-20261026 --overlay <cache>/rung3-ball-production-assembly/overlay --rh100 <cache>/rh100-out
  - hunts/rung3_ball_production/production.py strip-faults --dest <cache>/rung3-ball-production-strip-20261026 --overlay <cache>/rung3-ball-production-assembly/overlay
outcome: theorem davenport_heilbronn_strip compiled with zero sorry and prints exactly propext, Classical.choice and Quot.sound, as do the 17 earlier final declarations; the 20 artifacts, the 215 root oleans and the Support, Assembly and Separation oleans are byte-identical to the first assembly's; both planted strip faults refused at davenport_heilbronn_strip and the control accepted; no Lake build, the ZetaLean oleans unchanged; the unpacked oleans deleted afterwards
artifacts:
  - hunts/rung3_ball_production/RESULTS.md
  - hunts/rung3_ball_production/pilot.json (production.strip_assembly)
  - <cache>/rung3-ball-production-full/receipts-strip-20261026
```

## 2026-10-27: door 1, the replay (estimate before spending, part 1: the sampling windows)

The coordinator's brief of 2026-10-27: Stage A, `leanchecker --fresh` over the closure of
all 18 final declarations, Lean's own kernel; Stage B, if it fits, an export by
`leanexport` checked by `con-ron --verified`. Same constraints as the strip re-assembly: no
Lake build, oleans on disk, `MemAvailable` above 20 GiB, `ulimit -s unlimited`, kills by
recorded PID only. The height-100 `leanchecker` job has finished.

No emitted module imports all 18 declarations (`Separation` lacks the strip theorem and
`Strip` lacks `dh_separation_hundred`), so `assembly.py` now also emits `Final.lean`, which
imports both and declares nothing. `Assembly`, `Separation` and `Strip` are emitted byte for
byte as before. `assemble` compiles `Final` after `Strip`.

`leanchecker --fresh` replays every constant the module imports, and `ZetaLean` imports
all of `Mathlib`, so Stage A replays the whole of Mathlib as well as the sites; the export
of Stage B holds only the constants the 18 declarations use. Neither tool reports
progress, so the estimate is built from samples, each one Lean process, before the run:

| unit | estimate |
|---|---|
| `collect` and `assemble` again, as on 2026-10-26, with `Final` | about 250 CPU-s, 18 GB peak RSS, 15.1 GB of disk |
| a census of the closure's constants by origin (one import of `Final`) | about 15 CPU-s, 18 GB |
| `leanchecker` on a module that does not exist (must exit 1) | seconds |
| `leanchecker` without `--fresh` on the site `CB_right_06` (its own constants, replayed into its imports): a timing sample and the control for the olean fault | 1 to 3 min, about 10 GB |
| a planted kernel-level fault: one byte of a big literal changed in a scratch copy of `CB_right_06/Primes.olean`, then `leanchecker` on that module | 1 to 3 min, about 10 GB |
| a progress replay for a short window: a script that replays the closure module by module in import order through the same `Kernel.Environment.replay`, logging each module's time, stopped after 10 minutes | 10 min of one core, about 20 GB |
| Stage B sample: `leanexport` of the closure of `upper_B_right_06` alone, then `con-ron --verified --jobs=8` on it | a few minutes, under 10 GB |

In all, under 40 core-minutes. The full estimate follows from these samples, before the
replay starts.

### The sampling windows (measured, 2026-10-27, 00:05 to 00:33 UTC)

- `collect` (same 20 digests, the 215 root oleans identical to the first receipts, every
  root checkpoint present, 15,125,743,627 bytes) and `assemble` with `Final` (Support 9.5,
  Assembly 73.3, Separation 11.1, Strip 12.2, Final 10.8 CPU-s; the 18 declarations print
  the three standard axioms; Support, Assembly, Separation and Strip hash exactly as in the
  strip receipts).
- `leanchecker --fresh Rung3Assembly.NoSuchModule`: exit 1, "Could not find any oleans", in
  8.8 s, which is the checker's walk of every olean on the search path.
- **Census** (`ReplayProgress.lean`, first version): `Final`'s closure has 11,955 modules and
  1,569,505 constants: the 215 sites 761,387 (1,075 modules), Mathlib 580,690, Lean's core
  182,964, its dependencies 19,389, hunt #137 24,311, `ZetaLean` 733, the assembly 31.
  That version then replayed module by module in import order to log progress, and the
  kernel stopped it at `List.drop.eq_def`, which uses a private splitter that the
  constant-to-module map files under a later module. Constants realized on demand are
  filed out of dependency order, so that order is not a valid replay order; the instrument
  was wrong, not the environment. It was rewritten to sample instead.
- **Replay sample** (`ReplayProgress.lean sample`, seed 20261027, four streams under the
  guard, all exit 0): each module's own constants replayed into the environment of its
  imports, as `leanchecker` does without `--fresh`, timed apart from the import. 175
  modules: 9 whole sites (the centre, `B_right_06` and 3 big boxes and 4 grid points at
  random), 60 Mathlib, 30 core, 10 dependency and 10 hunt #137 modules at random, every
  `ZetaLean` and assembly module. Every one was accepted. The centre's five modules took
  490 s, `B_right_06`'s 24 s, a grid site about 105 s; across the 9 sites the replay is
  0.325 of the site's runner compile CPU.
- `leanchecker CB_right_06` without `--fresh` (the whole site, its 5 modules in parallel):
  exit 0, 45.7 s wall, 145 CPU-s; an import-only baseline (`Rung3Assembly.Support`) costs
  about 16 CPU-s.

**Estimate for Stage A**, `leanchecker --fresh Rung3Assembly.Final`, one thread (sample
totals scaled by constants, by olean bytes and by module count, or for sites by runner
compile CPU and by olean bytes; the range is the spread of those estimators):

| part | estimate |
|---|---|
| the 215 sites | 18,400 to 20,200 s |
| Mathlib | 2,300 to 2,700 s |
| hunt #137's modules | 1,700 to 2,200 s |
| Lean's core and dependencies | about 200 s |
| `ZetaLean` and the assembly | about 5 s |
| import and the search-path walk | about 25 s |

That is 6.3 to 7.0 hours from the sample. The same method would put height 100's closure
under about 4,700 s, against its measured 6,000 s, so the estimate written down is **6 to
10 hours** of one core. Peak RSS: the import of the closure alone is 17.9 GB (the census
run); the kernel environment then grows by the 1.57 million replayed constants, so **18 to
26 GB**, with `MemAvailable` expected to stay above 35 GiB. The guard is
`guard.py` of hunt #137, copied unchanged (SHA-256 `cbdcd817bea525f0...`): no wall limit,
SIGTERM to the checker's process group below 20 GiB, a status file every minute, a receipt
at the end.

### Stage A, launched (00:35:12 UTC)

`guard.py leanchecker-fresh <receipts> -- <toolchain>/bin/leanchecker --fresh
Rung3Assembly.Final`, with the toolchain's `bin` first on `PATH` (the checker runs `lean
--print-prefix`) and the `LEAN_PATH` of `lean-path.txt` in the receipts: the overlay, the
assembly, the 215 site outputs and hunt #137's oleans ahead of the paths `lake env`
reports (read with `lake env printenv`, which builds nothing). Guard PID 308349, checker
PID 308357, recorded in the receipts. Its outcome is below when it ends.

### Planted kernel-level fault in a scratch olean (measured, 00:36 to 00:40 UTC)

In a scratch copy of `CB_right_06/Primes.olean`, the radius of `Prime_B_right_06_2.Sq_10`,
36391283805789411/2^63, was lowered by one unit. The literal is below 2^63, so the olean
stores it as the tagged word 2n + 1; the word occurs once in the file, at byte 62304, and
the copy differs from the original in that one byte. The scratch directory went first on
`LEAN_PATH`, beside links to the site's other oleans. (A first try without those links
stopped before any replay, at "object file ... CB_right_06/Base.olean does not exist",
because Lean resolves `CB_right_06.*` in the first directory holding `CB_right_06/`; that
was a setup miss, not a verdict.)

| run | outcome |
|---|---|
| `leanchecker CB_right_06.Primes`, the unchanged olean | exit 0, 31.1 s wall |
| the same, the planted copy | exit 1: "(kernel) application type mismatch" while replaying `Prime_B_right_06_2.ev_whole._proof_1_1`; the decision no longer evaluates to `true` |
| `con-ron --verified` on the export of `Prime_B_right_06_2.pilot_contains_cpow` from the unchanged olean (26,561 declarations) | exit 0, accepted, 41 s |
| the same from the planted copy (the two exports differ in one record, `natVal` 36391283805789411 against 36391283805789410) | exit 1, rejected: "application type mismatch" at the same `ev_whole._proof_1_1` |

### Stage B: estimate, and the decision to stop there

Measured samples, each under the guard:

- `leanexport CB_right_06 -- ZetaLean.DH.Cert.upper_B_right_06`: 486,513,215 bytes,
  61,786 declarations, 50.6 s, 7.0 GB peak RSS. Charging each record to the declaration it
  is first written for: the site's own 687 declarations are 14.8 MB (0.88 bytes per byte of
  the site's 16.8 MB of oleans), the shared base 471.7 MB.
- `con-ron --verified --jobs=8 --progress=1` on it: **accepted 61,782 declarations**, exit
  0, 690 s wall, 2.2 GB peak. The base checked in about 80 s; the rest was the site's 23
  whole-tower decisions, each 16 s (p = 2) to about 265 s (p = 89), about 3,940 CPU-s in
  all. Lean's kernel replays the same module in 16.3 s.
- The towers p = 2, 401 and 1801 of the centre (export 150 MB, 26,575 declarations):
  accepted, exit 0, 0.76 GB peak; the towers took about 16, 400 and 648 s.

Projection for the export of the 18 declarations' closure: about 13.3 GB for the sites (by
olean bytes) plus a base under 1.5 GB, so **14 to 15 GB**, against 0.53 GB at height 100.
The export itself, by a line through the two `leanexport` samples (50.6 s for 486.5 MB,
18.3 s for 150.3 MB), takes **20 to 30 minutes** at **30 to 40 GB** of RSS (the 17.9 GB
import of `Final` plus about 0.9 bytes per export byte) and 14 to 15 GB of disk. `con-ron`
used 4.0 to 5.2 bytes of RSS per export byte on the three samples and 6.8 at height 100, so
**56 to 102 GB** of peak RSS. The 15,608 towers (each site uses the first T primes other than 5, T from the
generator census), priced by interpolating the measured tower times in log p, come to
**about 1,300 core-hours**: 81 hours of wall at `con-ron`'s default cap of 16 workers and 43
at 30. Both the time (over 24 hours) and the memory (this box had 72 GiB available after
Stage A, so about 52 GiB above the 20 GiB floor) exceed the brief's bounds, so Stage B
stops at this estimate, and neither the full export nor its check was launched. It needs a
larger machine: about 128 GB of RAM, and 1,300 core-hours, which is about 20 hours on 64
cores if `con-ron` scales there (`--jobs` above its default cap of 16 must be set by hand). Per-site exports (about 0.5 to 0.9 GB
each, about 3 GB of `con-ron` RSS) would remove the memory bound but not the CPU, and would
leave the assembly's own closure to check separately. NanoDa was not run.

### Stage A: the outcome (measured)

The parent session was restarted at about 02:59Z and this lane's copy stopped at about
03:35Z; the detached guard and checker were not touched and ran on. The guard's receipt
(`<receipts>/leanchecker-fresh.receipt.json`):

| | estimate | measured |
|---|---|---|
| exit | | **0**, stdout and stderr empty, `stop_reason` null |
| wall, one core | 6 to 10 h | **7 h 17 min 46 s** (00:35:12 to 07:52:58 UTC, 26,266 s) |
| peak RSS | 18 to 26 GB | **22.76 GB** (22,759,764 KiB, sampled every 5 s) |
| lowest `MemAvailable` | above 35 GiB | **49.3 GiB** (51,670,496 KiB) |

The checker binary hashes the same before and after (SHA-256 `9e36e955a251b131...`). The
sample's projection, 22,605 to 25,325 s, fell 4 to 14 % short of the measured time; the
widened estimate written down, 6 to 10 hours, held. `Final` imports `Separation`,
which imports `RHHeight100.Main100`, so this replay also re-checked hunt #137's closure.

Then the unpacked oleans and the sample exports
(`<cache>/rung3-ball-production-replay-20261027`, about 16 GB) were deleted, keeping the
receipts, the zips' digests (`collected.json`) and the exports' SHA-256.

```runmanifest
id: rung3_ball_production-2026-10-27-door1
hunt: rung3_ball_production
started: 2026-10-27T00:05Z
finished: 2026-10-27T07:53Z
ran:
  - hunts/rung3_ball_production/production.py collect --request <receipts>/RUN_REQUEST.full.json --run 40353536947 --dest <cache>/rung3-ball-production-replay-20261027
  - hunts/rung3_ball_production/production.py assemble --dest <cache>/rung3-ball-production-replay-20261027 --overlay <cache>/rung3-ball-production-assembly/overlay --rh100 <cache>/rh100-out
  - <toolchain>/bin/leanchecker --fresh Rung3Assembly.NoSuchModule
  - <toolchain>/bin/leanchecker -v CB_right_06, and leanchecker Rung3Assembly.Support twice (import baseline)
  - lean --run hunts/rung3_ball_production/lean/ReplayProgress.lean (first version: census, then a stopped progress replay), and its sample mode in 4 guarded streams over 175 modules
  - <toolchain>/bin/leanchecker CB_right_06.Primes on the unchanged olean and on a scratch copy with one radius literal one unit low
  - <toolchain>/bin/leanexport CB_right_06 -- ZetaLean.DH.Cert.upper_B_right_06; leanexport Ccentre.Primes (towers 2, 401, 1801); leanexport CB_right_06.Primes (tower 2, clean and planted)
  - <toolchain>/bin/con-ron --verified --jobs=8 --progress=1 on each of those four exports, under guard.py
  - guard.py leanchecker-fresh <receipts> -- <toolchain>/bin/leanchecker --fresh Rung3Assembly.Final
outcome: Stage A accepted, a same-kernel fresh replay of the closure of all 18 final declarations (1,569,505 constants, Mathlib and hunt 137 included), exit 0 in 7 h 17 min at 22.8 GB; a missing module exits 1 and a one-unit radius fault in a scratch olean is refused by the kernel at Prime_B_right_06_2.ev_whole; Stage B ran on samples only (con-ron accepted the closure of upper_B_right_06 and three centre towers, and rejected the planted fault at the same declaration) and stopped at its estimate, about 1,300 core-hours and 56 to 102 GB for the full closure
artifacts:
  - hunts/rung3_ball_production/pilot.json (production.replay)
  - hunts/rung3_ball_production/lean/ReplayProgress.lean
  - <cache>/rung3-ball-production-full/receipts-replay-20261027
```
