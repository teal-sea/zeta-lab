# RUNS: hunt `weil_dh_line` (#146)

Box: the swarm box (32 vCPU, 115 GiB, no swap), shared with other workflows.
Python is the repository `.venv` (python-flint 0.9.0 with the Arb backend, numpy,
scipy with HiGHS). Estimates are written before the runs they price; every run
below is owned by this session and was watched to a terminal state. Wall times
are contended: the one-minute load average stood between about 35 and 255 during
the hunt, so a process typically received 45 to 95 percent of a core.
`MemAvailable` stayed above 78 GiB throughout.

## Two sessions

The hunt was opened by an earlier session of this lane (15:47 to about 18:07
UTC). It wrote `MISSION.md`, the case-log entry, `price.py` with the floor,
per-prime and price machinery, `price_table.json`, `partition_lower.json`,
`overlap_L_DH.json`, `k2_dh.json`, `k2_epstein.json`, a first `joint.py` and
`scout.py`, and timed one scout unit. Its joint-envelope runs all failed or
were cut off: the L = 7/5 cluster `{3,7,13}` exhausted a 4 million box budget,
`{2,5,11}` stopped on a HiGHS status 15, the DH-line `{3,13,23}`/`{5,11,19}`
part exhausted its box budget, and the `{2,17,29}`/`{7}` part was still in its
exchange LP when its own `timeout 14400` ended it at about 21:23 UTC, with no
output. Nothing from those runs is used. This session (from 21:23 UTC) replaced
the exchange LP by a smoothed minimax with an exchange step, added a sharper
rigorous box bound, overlapping-cluster weights, the odd sector and a faster
measured Bessel column to the scout, and ran everything below.

## Envelope builds (one process each, under 2 GB)

The ledger below gives every build that produced an artifact. Each line of a
`price.py --joint-spec` log is one cluster; `price.py --merge` re-runs every
check on the saved coefficients (see `price.merge_parts`).

| run | started (UTC) | outcome | compute |
|---|---|---|---|
| `--joint-spec specs/dh_1.4.json` | 22:02 | success | 413 s for `{2,3,7}`, under 20 s per one-prime cluster |
| `--joint-spec specs/ep_L_DH.json`, `specs/ep_1.6615.json` | 22:02 | success | about 3 min each |
| `--joint-spec specs/zeta_1.4_a.json` (`{3,7,13}`) | 22:08 | success | 456 s, 2 216 872 boxes |
| `--joint-spec specs/zeta_1.4_b.json` (`{2,5,11}`) | 22:08 | success | 1104 s, 4 455 782 boxes |
| `--merge` of the three K2 envelopes | 22:12 | success | under 1 min each |

## The scout at L = 7/5 (estimate written before launch)

Plan: envelope `joint_1.4.json` (two clusters, 1190 cosine terms, `S = 4.117980...`,
so `β* > 0` from `T# = 2π e^S ≈ 386`); even Legendre modes `N = 560` (orders 0 to
1118, `2N/x = 1.25` at `T# = 640`); Gauss-Legendre `q = 64` per panel of width
`1/2`; 640 bits (the bits rule of `price.py`); `T#` up to 640; units of 40 panels,
so 32 units, checkpoints every 20 in `T#`; the fast (midpoint recurrence) Bessel
column, which agrees with the re-seeded Arb column to `1e-185` relative at
`K = 1039` to `4159` (`bessel_scaling.json`) and is 21 to 59 times cheaper there.

**Unit timing.** Unit 31 (panels 1240 to 1280, the largest arguments) ran alone,
22:27 to 22:34 UTC, under a load average of 36 to 48: **396 s**, about 155 ms per
node, dominated by the 1190-term H in Arb at 640 bits (the Bessel column is about
20 ms of it).

**Estimate.** The node cost is nearly uniform across units, so 32 units cost
about `32 x 400 s = 12 800` contended core-seconds, about **3.6 core-hours**, and
35 to 45 minutes of wall time on 6 processes. The reducer (13 checkpoints, each a
midpoint LDL of a 560 x 560 block at 640 bits in Python plus inverse iteration,
and two response checkpoints with two more LDLs each) adds 20 to 40 minutes on
one core. Under 1 GB per process; 32 checkpoint files of about 30 MB in
`<cache>/weil_dh_line/scout_L140`. Every unit writes its file
on completion (checkpoint per unit); a restarted run skips finished units.

## Ledger

| run | started (UTC) | outcome | compute |
|---|---|---|---|
| scout unit 31, timing (`scout.py --time-unit 31`) | 22:27 | success, file written | 396 s |

## Resumed 2026-10-26 (owner's decision to resume the lane in place)

Box rules for this session are stricter than the MISSION's: at most 4 processes,
wait while the one-minute load exceeds 64, `nice -n 10`, no file over 100 MB, at
most 200 MB added to disk. The heavy artifacts stay in `<cache>/weil_dh_line/`
(about 1.3 GB, out of git). Load during the session: 9 to 60.

**Provenance of the scout units.** All 32 files in `<cache>/weil_dh_line/scout_L140/`
record `env = <cache>/weil_dh_line/parts/provisional_1.4.json`, `N = 560`,
`prec = 640`, `q = 64`, even parity, fast Bessel column. `provisional_1.4.json`
(SHA-256 `bf81f528...20c0bc`) carries the same two clusters, with identical
`omega`, dyadic `h` and `U`, as the part files `zeta_1.4_a.json` (`{3,7,13}`,
`d57d58c5...fa626`) and `zeta_1.4_b.json` (`{2,5,11}`, `6096db02...abfb2`); its
`S` is the sum of the two `U`, `4.117980522896958`. The 2026-10-21 merge log
(`merge_zeta_1.4.log`) ends after `{3,7,13}`; `{2,5,11}` was never re-checked.
So `joint_1.4.json` is built by `price.py --merge` of the two part files, and the
scout's `C` and `G` (which depend on `H`, not on `S`) are valid for it.

**Thread note.** The first merge launch (12:54:45 UTC) let numpy's BLAS start
about 12 threads (1966 CPU seconds in 163 s of wall time). It was stopped and
relaunched at 12:57:43 UTC with `OMP_NUM_THREADS=OPENBLAS_NUM_THREADS=MKL_NUM_THREADS=1`;
every later run here sets the same caps.

### Estimates (written before any run they price)

- **Merge of zeta at `L_DH`** (four parts, item 3). A merge re-runs the
  whole-torus box bound, and its cost tracks the build's `sup_bound` seconds
  (`{3,7,13}` at 7/5: 135 s at build, 153 s and 162 s at merge). The four parts
  record 678 s (`{2,17,29}`), 3819 s (`{3,13,23}`), 3687 s (`{5,11,19}`) and
  0.5 s (`{7}`, the LP version), so about **8200 core-seconds, 2.3 core-hours**
  (wall about 65 min on three processes). Over one core-hour: asked first.
- **K2, DH at `L_DH`** (item 6). The DH merge (`dh_L_DH_v2.json`) records
  201 + 83 + 3241 + 21 s of box bound, about **1.0 core-hour**. The parts give
  `S >= 6.039784733` before the dropped `l1` tail is added, so `beta* > 0` needs
  `T# > 2 pi e^S / 5`, about 528. A stage-A run comparable to the zeta scout
  (`beta*` about 0.4 at the top) needs `T#` to 800, `N = 856` even modes
  (`2N/x = 1.25`), 1280 bits (the bits rule at `L_DH`), 40 units of 40 panels.
  **Timed slice**: panels 1596 to 1600 (the largest arguments), in memory, no file
  written, 12:56 to 12:59 UTC under load about 50: **174 s**. A unit is then
  about 1740 s and the units about **19 core-hours**; the reducer (17 midpoint
  LDLs of an 856 x 856 block at 1280 bits in Python) adds, scaling the 7/5
  estimate by `(856/560)^3 x 2`, about **3 to 6 core-hours**. Each unit file
  would be about 140 MB (5.6 GB in all), which breaks the box's 100 MB per-file
  and 200 MB per-session limits. Asked first; see the ledger for the answer.

### Decision on the two runs over one core-hour (coordinator, 2026-10-26)

Asked through the coordinator with the estimates above. Answer: **run A** (the
four-cluster zeta merge at `L_DH`, at most 3 processes) and **defer B** (K2 on DH
at `L_DH`). B is recorded as **estimated, not run**: about 1 core-hour of merge,
about 19 core-hours of units, 3 to 6 core-hours of reducer, 40 units of about
140 MB each. It goes to funded cloud compute when the owner tops that up (cloud
compute was unfunded on 2026-10-26); it was not shrunk to fit.

**Could the reducer consume units as a stream?** Yes, and that would make B fit
an ordinary disk. The reducer reads each unit exactly once, in panel order, and
needs only the prefix sums `C(T#)` and `G(T#)` at unit boundaries (`scout.reduce`).
A streaming driver would run the units in ascending order on a pool with ordered
results (`imap`, not `imap_unordered`), hand each unit's `C` and `G` to the
parent through the pipe instead of a file, add them to the running sums, run
the checkpoint LDL and inverse iteration at once, write that row (a few hundred
bytes) and keep only the running sums on disk as the restart checkpoint. Disk at
peak is then one copy of the running sums, about the size of one unit file
(about 140 MB at `N = 856`, 1280 bits; split into row blocks to stay under a
100 MB per-file limit), instead of 5.6 GB. Costs: a checkpoint row waits for
every lower unit, which is harmless because unit cost is nearly uniform; the
parent holds two full `856 x 856` Arb matrices at 1280 bits (a few hundred MB of
RAM); and a crash loses only the units in flight. Not implemented here: nothing
in this session would consume it.

### Decision changed: run B here, streamed (coordinator, 2026-10-26, evening)

Cloud compute stayed unfunded, and the owner's compute rules let a session
already on this box use it for work that fits. With the streaming reducer B
fits, so B now runs here. **Estimate, written before launch**:

- the DH merge at `L_DH` (`price.py --merge parts/dh_L_DH_v2.json`, four
  clusters, 3 processes): about **1.0 core-hour**, about 55 min wall (bounded by
  `{11,19,29}`, 3241 s at build);
- the units: 40 units of 40 panels (`T#` to 800, `N = 856` even, 1280 bits,
  `q = 64`, `h = 1/2`), about 1740 s each from the timed slice, **about 19
  core-hours**, about 6.5 h wall on 3 worker processes;
- the reduction, in the parent process as each checkpoint completes: 14
  checkpoints with `beta* > 0` (`T#` = 540 to 800), plus the `N` and precision
  responses at 540 and 800, **3 to 6 core-hours**.

**Total 23 to 26 core-hours, hard cap 30.** The projection is recomputed from
measured unit times as units finish, and the run stops if it passes 30. At most
4 processes (3 workers and the parent), `nice -n 10`, BLAS threads capped at 1,
no launch while the one-minute load exceeds 64, and the newest job stops if
`MemAvailable` falls below 20 GiB. Disk: no unit file is written, and the
restart checkpoint is the running `C` and `G` in files under 100 MB, two
generations at most, about 300 MB at peak (cap 1 GB). Watched by recorded PID.

### Ledger (2026-10-26)

```runmanifest
id: weil_dh_line-2026-10-26-merge-1.4
hunt: weil_dh_line
started: 2026-10-26T12:57Z
finished: 2026-10-26T13:08Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/price.py --merge <cache>/weil_dh_line/parts/zeta_1.4_a.json <cache>/weil_dh_line/parts/zeta_1.4_b.json --out joint_1.4.json
outcome: success, 10 min 35 s wall, 425 s user, 0.42 GB peak; both clusters re-bounded to the build value ({3,7,13} U 1.8622602217962332, 2 216 872 boxes; {2,5,11} U 2.2557203011007245, 4 455 782 boxes), frequency audit, Arb spot check and Arb box check all ok, weights cover the comb; S_exact 18545735548437699/4503599627370496 = 4.117980522896958, identical to provisional_1.4.json, so the scout units built on that file stand
artifacts:
  - hunts/weil_dh_line/joint_1.4.json (SHA-256 598ef7d2bec612db9b0deffe6487142370d64e9a3457a074b4e4079a0f1b5aad)
  - <cache>/weil_dh_line/parts/merge_zeta_1.4_v2.log
```

```runmanifest
id: weil_dh_line-2026-10-26-scout-reduce-1.4
hunt: weil_dh_line
started: 2026-10-26T13:08Z
finished: 2026-10-26T13:33Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/scout.py --reduce --env joint_1.4.json --N 560 --Tmax 640 --prec 640 --q 64 --h 1/2 --unit-panels 40 --responses 400 640 --out scout_L140.json
outcome: success, 24 min 31 s wall (inside the 20 to 40 min estimate), 1307 s user, 0.66 GB peak; 32 checkpoints, 13 with beta* > 0 (T# = 400 to 640); n_neg = 2 at 400, 1 at 420 and 440, 0 from 460 to 640; the N = 517 and 512-bit responses at 400 and 640 keep n_neg (2 and 0) and lambda_min; units recorded 9159 core-seconds on 2026-10-21
artifacts:
  - hunts/weil_dh_line/scout_L140.json (SHA-256 98a2b49d82733fbaa1bc2d6e359f0028c8f33608b8e5a8bd6f352494f14652de)
  - <cache>/weil_dh_line/scout_L140_reduce.log
  - <cache>/weil_dh_line/scout_L140/ (32 unit files, 945 MB, not committed; SHA-256 below)
```

```runmanifest
id: weil_dh_line-2026-10-26-k2-scouts
hunt: weil_dh_line
started: 2026-10-26T12:58Z
finished: 2026-10-26T12:58Z
ran:
  - .venv/bin/python hunts/weil_dh_line/price.py --k2-scouts <cache>/weil_dh_line/k2
outcome: success; assembled from the four K2 stage-A runs of 2026-10-21 (dh_140_even, ep_LDH_even, ep_16615_odd, ep_16615_even); dh_LDH_even was never run and is absent (deferred, see the decision above)
artifacts:
  - hunts/weil_dh_line/k2_scouts.json
  - inputs <cache>/weil_dh_line/k2/dh_140_even.json e9cffd1a2cee33c5170113edaaa73e3f6b6eb0a014c6a86ff3734ccf2096a875, ep_16615_even.json 76089cdd1e76a12bdf5c89e48f22dccbb2fbd3cc596440c043d530048493f06a, ep_16615_odd.json 8f3a386aefddd16eee7f23028f0e70de3c48f2bb00b19e37b424d75540f2275e, ep_LDH_even.json e00d8b04e53534d9c3b5ce50e2389ab1cda87d852f56095c05f3f0c8882e938e
```

```runmanifest
id: weil_dh_line-2026-10-26-time-dh-L_DH
hunt: weil_dh_line
started: 2026-10-26T12:56Z
finished: 2026-10-26T12:59Z
ran:
  - nice -n 10 .venv/bin/python <scratch>/time_dh_ldh.py hunts/weil_dh_line <cache>/weil_dh_line/parts/dh_L_DH_v2.json <scratch>/env_dh_ldh.json 856 1280 1600  (scout.unit on panels 1596 to 1600, kind dh, even, in memory)
outcome: success, 174 s for 4 panels at N = 856, 1280 bits; the S used to load the envelope (6.039784733, sum of the part U values without the dropped l1 tail) does not enter C or G
artifacts:
  - none (timing only; the estimate above uses it)
```

```runmanifest
id: weil_dh_line-2026-10-26-merge-L_DH
hunt: weil_dh_line
started: 2026-10-26T13:00Z
finished: 2026-10-26T14:10Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/price.py --merge <cache>/weil_dh_line/parts/zeta_L_DH_a.json <cache>/weil_dh_line/parts/zeta_L_DH_b.json <cache>/weil_dh_line/parts/zeta_L_DH_c_no7.json <cache>/weil_dh_line/parts/zeta_L_DH_d.json --merge-procs 3 --out joint_L_DH.json
outcome: success (run A of the decision above), 1 h 9 min 51 s wall, 6236 s user and 1813 s system (about 2.2 core-hours against the 2.3 estimated), 0.76 GB peak; every cluster re-bounded to its build value ({2,17,29} U 1.9060110552607548, 5 787 856 boxes; {3,13,23} U 1.9396377024317553, 16 467 956 boxes; {5,11,19} U 1.8364049896574703, 15 942 328 boxes; {7} U 0.7360570900158183, 15 162 boxes), frequency audit, Arb spot check (60 points) and Arb box check (12 boxes) ok in each cluster, weights cover the comb; S_exact 28904601575583153/4503599627370496 = 6.4181108373657985
artifacts:
  - hunts/weil_dh_line/joint_L_DH.json (SHA-256 702c118e3eaa325b2a22928b0641a8a5ffd43021b734b548c256858d7b443ee3)
  - <cache>/weil_dh_line/parts/merge_zeta_L_DH.log (SHA-256 5b1625d6d134e421ee3d2600ea01483c1b78e941a3d7caa380855ae34163aa00)
  - inputs zeta_L_DH_a.json 6f274baf020c26bc3f0cc455f390f13f1b3ac24259442f107d8f832940be9051, zeta_L_DH_b.json ff74f3436a3d383bbffe51924358ebf8eee875b9dc0da01679df5026d4bee9ff, zeta_L_DH_c_no7.json 4592eedf056f4387a9bd7bc15a7fbbf2459cf8da49f6150ab707d2ab8420831f (zeta_L_DH_c.json 5387fdee18308d468322f45fd3ba6f21b2b8fa3ce006d5f22680a146f3abc250 with its superseded {7} cluster removed), zeta_L_DH_d.json 6aa6b41aa7baba0f920b17d4759b480c10641950a68e6682fac642205f7496ea
```

```runmanifest
id: weil_dh_line-2026-10-26-merge-dh-L_DH
hunt: weil_dh_line
started: 2026-10-26T16:45Z
finished: 2026-10-26T17:23Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/price.py --merge <cache>/weil_dh_line/parts/dh_L_DH_v2.json --merge-procs 3 --out k2env_dh_L_DH.json
outcome: success (first step of run B), 37 min 50 s wall, 2012 s user and 247 s system (about 0.63 core-hours against the 1.0 estimated), 0.68 GB peak; every cluster re-bounded to its build value ({2,3,7} U 3.4565192383627505, 485 100 boxes; {2,13} U 0.7662182682168919, 219 816 boxes; {11,19,29} U 1.5014327584236216, 15 974 930 boxes; {17,23} U 0.31561446800606674, 132 332 boxes), frequency audit, Arb spot check and Arb box check ok in each cluster, weights cover the DH comb; dropped l1 tail at most 1.6e-76; S = 6.039784733009331 (S_exact in the file), so beta* > 0 needs T# above about 527.5
artifacts:
  - hunts/weil_dh_line/k2env_dh_L_DH.json (SHA-256 a4426e2179497454688488cbe4d3c1ab0527e3d0ef7e1846eec9b16f46f398ba)
  - <cache>/weil_dh_line/parts/merge_dh_L_DH.log (SHA-256 57d063ad778c54f5cdde92823e108c255bb2691f860b494fb6b0371b96bc90d7)
  - input <cache>/weil_dh_line/parts/dh_L_DH_v2.json (SHA-256 13ada3f5da5ec89ddfd3ea87f1f1fa6952c4e54b03e1e74a57128b1265dcc149)
```

```runmanifest
id: weil_dh_line-2026-10-26-k2-dh-L_DH-stream
hunt: weil_dh_line
started: 2026-10-26T17:23Z
finished: 2026-10-26T22:57Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMBA_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/scout.py --stream --L 171079/100000 --env k2env_dh_L_DH.json --N 856 --q 64 --h 1/2 --prec 1280 --Tmax 800 --unit-panels 40 --parity even --bessel fast --procs 3 --responses 540 800 --dir <cache>/weil_dh_line/k2/dh_LDH_even --out <cache>/weil_dh_line/k2/dh_LDH_even.json --cap-core-hours 29.3 --min-mem-gib 20
  - .venv/bin/python hunts/weil_dh_line/price.py --k2-scouts <cache>/weil_dh_line/k2   (adds dh_LDH_even to k2_scouts.json; the four earlier cases unchanged)
outcome: success (run B), status done, 5 h 33 min wall, 58 228 s user and 237 s system, about 16.2 core-hours (units 51 150 s, 1258 to 1356 s each against the 1740 s estimated; reduction 8267 s, 443 to 531 s per checkpoint), so 16.9 core-hours with the merge against 23 to 26 estimated and the 30 cap (the driver's last projection 59 417 s); 3 workers and the parent, 2.66 GB peak resident in one process, MemAvailable at least 28.5 GiB, restart state 125 MB per generation, 188 MB at the sampled peak; no unit file written; max entry radius 1.8e-75. Result: beta* > 0 from T# = 540; at all 14 checkpoints from 540 to 800 one negative pivot and no undecided one, lambda_min from -6.68685229203e-30 (540) to -4.15160674834e-30 (800), shrinking in magnitude as T# grows, residuals 4e-84 to 3e-86; at 540 and 800 the N = 791 block and the 1152-bit reduction keep n_neg = 1 and the same lambda_min to 12 digits
artifacts:
  - hunts/weil_dh_line/k2_scouts.json (entry dh_LDH_even)
  - <cache>/weil_dh_line/k2/dh_LDH_even.json (SHA-256 a41f8792804d3240ee1bde295373571a3ecba1bc629da3ee82e84141c2fd8451)
  - <cache>/weil_dh_line/k2/dh_LDH_even.log (SHA-256 abdc54896597464850b9b74deb3d15202765f1fcd71a7282088f1f0e1917167f)
  - <cache>/weil_dh_line/k2/dh_LDH_even/rows.jsonl 53139308b9a898b430d0ac1b3e4a0a8f00bc51c4cebd2ee568e8903368e5d54d, state.json e0e99762edc260ad608a1d3790bcb01971237a780feb40793b410f2705809329
  - final restart state, the sums C and G at T# = 800 (8 files of 12 to 18 MB, not committed): state_01600_C_000.pkl 5d62bc91ce5d463c8dcfb98693526c1eb87145ce8b728242a44ab61fd5bf2bb1, C_001 f84a6bf9d3114ee44005388ab8d92ebb161723f86b44e44d265994d0d34584ea, C_002 4c0da7737983a8819d8805266f28a2524c975c27d99e84df51c218b6256da7c0, C_003 8a09941a673a6e157b4cf24b1d00910a2cc00aaabca8109abfeb259e4c5daafb, G_000 2db89a3b5b4404b4a53b29ce59374f54d0f568a9620761867def4c47a714caf6, G_001 86faa4e75bfccdecb308f1a6ec2f62c2ba2476532f39e4254f2c49c71249f116, G_002 bb3e64ba537af9bac4cfe2bd6fd30b55d8b2207443224ab27cc80d4859f0139b, G_003 8189516cebb36601d0355109819d7d7fc069709cd1ace483f6d90e16443c2bea
```

Unit files of the scout at `L = 7/5` (`<cache>/weil_dh_line/scout_L140/`, about 30 MB each, kept out of git):

```
583ab7cb3d4f45b6ac16ecc52e4de30cf60cdb1d02b30380f2d4463bc2c2a2e0 scout_panels_00000_00040.pkl
cee420ad9e56662b31598ba83b060c9536bb24050dddee14ff98c72e290c7b5e scout_panels_00040_00080.pkl
6e8c597d4bc636af291e2f8eb0dae0271dd04b4da764e8abbb1aacdd9f2161d6 scout_panels_00080_00120.pkl
646baa3b42b945a353e55670b1cc9fa6ee22ecc328c1e569c1f3234bfa316401 scout_panels_00120_00160.pkl
d821149e54bf375ccf8e49f47fa1873cb857ff7fe6d98a37308c93e739ea3f36 scout_panels_00160_00200.pkl
effe85282c7051a1ea6d51936564e27e6f50550d7a346ab169576730436fb9bc scout_panels_00200_00240.pkl
e92a095232cce11979685eeb3a68924ebc83814f7fa1ec2143467a62d3bfa874 scout_panels_00240_00280.pkl
af6e85fbf156b40141ca1951f45875c40416dfe55fbca6b941628a26845c5df2 scout_panels_00280_00320.pkl
e0b5998ae8b7adac72b6028450152f81ec885d76295d59a5602083341291d3ef scout_panels_00320_00360.pkl
31907bd09c1788a4576c001a454dc6c249e1238cb003825bfc21b903fdc4844e scout_panels_00360_00400.pkl
7ac4c6961057050cd5fe85bec9163558dfe7c25c7967cf2516739d55481902f4 scout_panels_00400_00440.pkl
1e28e455f60dd5424c2f85c79dc50f2a596cf3a381d362b3484a2c4b5df1ea1b scout_panels_00440_00480.pkl
81c450a0856ddb2903fec892c79b1d5515d720b3d3e1d46438d1a28feb78de16 scout_panels_00480_00520.pkl
2fc81511dc2aa3c6d5ff2edf96a307322d0c07285ad539182bd36cd484063929 scout_panels_00520_00560.pkl
2ac5610a29ff59483c99faf3795a2163c4549d83f5ef70ff46b5c42e0cabd9c1 scout_panels_00560_00600.pkl
6bc7de7feccf04951a361377eff1908b1cce49ac87a2bdd5e2f353b0e1fe9e27 scout_panels_00600_00640.pkl
015cb2538fc1031369d05b1f6a92390aa64a0fa2ff38e70ffc3ecfd9c3f7b22a scout_panels_00640_00680.pkl
2133f2d13c91d87f7a3e599dd55d5ac274673d1ba7f2dd4f726e5340a0a442ae scout_panels_00680_00720.pkl
c98df750bfea953661de2fa61021b9226882e7220e858cd53c4b3e512d85b408 scout_panels_00720_00760.pkl
cc7b07410a18dc8db247ff2d91c9a92e162d6545f87997f87eb081c3730e66f7 scout_panels_00760_00800.pkl
deb6b968801d84454a07895a53660532430a75b6f672f2c09a68449692e8f1c4 scout_panels_00800_00840.pkl
0fde951c7ba1eca20514f425ea47f684dff1f7afe124da7c11c53e8d56ef3bfe scout_panels_00840_00880.pkl
94a03c1c851b95be1f564a0d56fe0e728ce1494de7b0d37676ececb52d9de361 scout_panels_00880_00920.pkl
63035abb54ffed418872ccef85feeccb8ecfe757b9f9b9d2d8fada154f700f80 scout_panels_00920_00960.pkl
5fe03b44305011c303d153a1807b5d5cbefb366c058dc3c14055720a5bf162e6 scout_panels_00960_01000.pkl
fa59933272226283b14b1a8d1d9641fb54bed3310e9f3b3e80525c5b36f225d8 scout_panels_01000_01040.pkl
1ef3587f7b1ecee35817a14708cc92ab28b249b60f2cea5dfe6112ddc9dcee59 scout_panels_01040_01080.pkl
582ccbdf28ffb0ed24c220f2096df53c778d259dad5e3ad13bbca835cf171c2f scout_panels_01080_01120.pkl
3a0e79c74b052102deaa3aa050d01de078570e84a1641d3e2fac062ea0f82b01 scout_panels_01120_01160.pkl
396a9e27a688b7e9971bd5ae52d74837409d6ef183850e4c4920532ae6562f5a scout_panels_01160_01200.pkl
1064dd74e0c7b3ba22f1913eb74b1b8eaba033d6da573ad0e330c8881e4e3548 scout_panels_01200_01240.pkl
f621655399a312e2b4835ebf0de154697dd20e319b2ddc3c75bca00d20362a16 scout_panels_01240_01280.pkl
```

## Raised 2026-10-27: the full form Q_856 in position space (estimate before launch)

Task from the owner after the adversarial review of PR #356: replace the measured
refusal at `T# <= 800` by a decisive statement about every `T#`. `R(T#)` increases
to the 856-mode DH form `Q_856` in the Loewner order, so the pipeline refuses at
every `T#` exactly when `lambda_min(Q_856) < 0`. `witness.py` assembles `Q_856`
with no `T#` split, through the explicit formula in position space, in Arb.

**Timed unit** (2026-10-27 01:44 UTC, load average 4 to 9): one node (a Gram
matrix of the 856 Chebyshev modes on the `M = 1711` mirrored Gauss nodes) takes
**10.5 s** and peaks at about 1.1 GB. The assembly needs 1830 nodes (`G(0)`, 1801
Gauss nodes in `x` on `[0, 2L]`, 28 comb points), so about **19 200 core-seconds,
5.4 core-hours**, about 45 min wall on 8 processes at `nice -n 10`, plus about
2 min for `K Q K^T` and the error bounds. Units of 24 nodes (about 4.3 min each,
77 units); the running sums are saved after every unit (one file of about 40 MB
in `<cache>/raise_2026-10-27/q856/`, a new directory; nothing of run B's state is
touched), so a restart loses only the units in flight. Calibration before launch
(`N = 20` and `40`, seconds): agreement with the stored `C(800)` block on smooth
vectors to `1e-39` and with the CCM closed-form assembly to `1e-61` (see below).

The other runs of the raise were each estimated below 20 minutes of one or two
processes, and run at most 8 numeric processes at a time at `nice -n 10`
with BLAS threads capped at 1, watched by recorded PID to a terminal state
(`MemAvailable` at least 49 GiB throughout; one-minute load 13 to 22, mostly
other jobs). One estimate missed: the single-vector stage-A runs were estimated
at about 8 min from the cost of `Psi + H` (10.3 ms a node at 256 bits) and took
about 45 min, because every job rebuilt the Chebyshev change of basis `K` from
exact binomials (135 s a call); `K_matrix` now uses the recurrence for
`a_j` (0.44 s), which changes no value (the test checks the enclosures
overlap).

### Ledger (2026-10-27)

```runmanifest
id: weil_dh_line-2026-10-27-q856
hunt: weil_dh_line
started: 2026-10-27T01:47Z
finished: 2026-10-27T02:35Z
ran:
  - OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/witness.py --N 856 --procs 8 --unit-points 24 --dir <cache>/raise_2026-10-27/q856 --out <cache>/raise_2026-10-27/q856.pkl
outcome: success, 48 min 11 s wall, 20 297 core-seconds of units (5.6 core-hours against 5.4 estimated; 250 to 274 s a unit of 24 nodes), 8 workers of about 0.7 GB and the parent; 1824 nodes (G(0), 1801 Gauss nodes in x, 22 comb points); E_psi 3.52e-70, eps 5.98e-64, quadrature bound 6.22e-92, dropped comb mass 1.58e-76, |K G(0) K^T - I| <= 5.8e-74
artifacts:
  - <cache>/raise_2026-10-27/q856.pkl (Q_856 lower triangle at 256 bits, 18.5 MB, not committed; SHA-256 04d022fba445f5094aaad8e9cedce3935902b8591ce66923a0af874a1b6c9430)
  - <cache>/raise_2026-10-27/q856/state.pkl (final running sums, 55 MB; 9a599a8350e27898853d1f1e6a17d2aa1cc3599df06b3dae931040ad7d323ce7)
```

```runmanifest
id: weil_dh_line-2026-10-27-analysis
hunt: weil_dh_line
started: 2026-10-27T02:36Z
finished: 2026-10-27T02:58Z
ran:
  - nice -n 10 .venv/bin/python hunts/weil_dh_line/witness.py --analyze <cache>/raise_2026-10-27/q856.pkl --out <cache>/raise_2026-10-27/witness_q856.json --vec-out <cache>/raise_2026-10-27/witness_v856.json --v800 hunts/weil_dh_line/v800_T800.json --state <cache>/k2/dh_LDH_even --blocks 400 500 550 600 650 700 750 800
  - leading blocks 50 to 350 and 100 to 145, the 101-mode witness vector, the re-assembly of Q_101 by the same code (witness.unit at N = 101, Nx = 291, 320 bits, 32 s) and the Sylvester counts of (Q_856 - R(800)) + sigma I, sigma = 1e-66 to 1e-50 (R(800) from the run-B restart state, read only): first run by scratch drivers over the functions of witness.py; corrected 2026-10-27: now the committed subcommands `witness.py blocks`, `block-witness`, `reassemble` and `shifted-counts`, and the merge `witness.py record`, which reproduced every piece (reproduction manifest below)
outcome: success, one process at a time (about 3 GB with the stored state loaded). Midpoint LDL of Q_856: 1 negative pivot, 855 positive; lambda_min -1.94308362498385e-30 (residual 3e-78); the stored 40-digit eigenvector has an enclosed Rayleigh quotient [-1.94308362498385e-30 +/- 3.5e-70], below 0 with 2 eps added. Leading blocks: none negative at 50 and 100 modes, one negative eigenvalue at every tested size from 101 (-4.49000370077e-32) to 800 (-1.93813662196e-30). The re-assembly of Q_101 by the same code at its own nodes and precision reproduces the 101-mode quotient to 15 digits (corrected 2026-10-27: first called independent; it is not a separate implementation). Q_856 at the T# = 800 eigenvector +6.36613886240e-30 (enclosed, positive); R(800) there -4.15160674834e-30, the stored row. (Q_856 - R(800)) + 1e-66 I has no negative pivot.
artifacts:
  - hunts/weil_dh_line/witness_q856.json (the merged record as committed, SHA-256 788a5974f1a362afe6ff5dd594661c14341b321643a072d78817bdc9cc5095fb; it also carries the responses at T# = 800 and the timed slices; corrected 2026-10-27 from 39bf78cf..., the hash of an earlier merge without those two keys)
  - hunts/weil_dh_line/witness_v856.json (779d9d5456994275c8d282b8f4e9f120de51a7cb202506a52e2df4513b7c5395), hunts/weil_dh_line/witness_v101.json (85c9a0aee3d1c6e53c8b3bb54a78f4d6e2d3200a710b7a20499ca18b2cdf3402)
  - <cache>/raise_2026-10-27/analyze.log (29a594522090c78618f78903a1ff840cf73b0a195aa76c465555c05135b88750), d_check.json (b877822bf15795a0b033bedb8074f1a999ca1def5fd6bf93be4c68fb0f2d7274), blocks_small.json, blocks_onset.json, blocks_onset2.json, witness_v101_reassembled.json
  - input hunts/weil_dh_line/v800_T800.json (the T# = 800 eigenvector, 40 digits, from the adversarial review's inverse iteration on the restart state; its R(800) quotient reproduces the stored row)
```

```runmanifest
id: weil_dh_line-2026-10-27-lesion-S
hunt: weil_dh_line
started: 2026-10-27T02:32Z
finished: 2026-10-27T03:07Z
ran:
  - nice -n 10 .venv/bin/python hunts/weil_dh_line/scout.py --L 171079/100000 --env hunts/weil_dh_line/k2env_dh_L_DH.json --N 856 --prec 1280 --h 1/2 --dir <cache>/k2/dh_LDH_even --lesion DS [--lesion-nearest] --out <cache>/raise_2026-10-27/lesion/...  (one process per dS; full rows at 0, 1417/200, 5917/200, 43, 44, 12477/100; eigenvalue nearest 0 only at 40, 43, 44, 45, 50)
  - .venv/bin/python hunts/weil_dh_line/price.py --k2-scouts <cache>/k2 --k2-lesion dh_LDH_even <the full rows and the nearest-only rows at 40, 45, 50>  (the five existing entries of k2_scouts.json regenerate unchanged)
outcome: success; full rows 441 to 449 s, nearest-only 289 to 317 s, about 1.15 core-hours in all. dS = 0 reproduces the recorded row (one negative pivot, -4.15160674834e-30); one negative pivot at 7.085 (-1.89171050630e-30), 29.585 (-4.48677787439e-31), 43 (-2.00511481317e-32); none at 44 (+7.00109338881e-33) and 124.77 (+1.31838669984e-30); nearest 0: -1.046e-31 at 40, +3.352e-32 at 45, +1.589e-31 at 50. Flip between 43 and 44.
artifacts:
  - hunts/weil_dh_line/k2_scouts.json (entry dh_LDH_even, key lesion_S)
  - <cache>/raise_2026-10-27/lesion/ full_0.json c011d6872f2a7a8483b05e5e9c3a4a2d7643ef2201c8ba36d7ce9641a160fdac, full_7085_1000.json (dS = 1417/200) 1d7fcffbc7bd8d670761beebba7f212e62e46185b175b5854062b43d077f1f4f, full_29585_1000.json (dS = 5917/200) ebb42a6e698b67996ce2774c34b1ea4e0c08ea925e85a346533d199bcc16d4ff, full_43 525d8d60c309e85450ee2f0e5b828cce5095ab8bfc466e47bb92ad27526a8edc, full_44 e9751c6a2805e47eb0a6c32ef63638d876a08f6b72dc3993898362fb2d1a7c35, full_12477_100 5f7defbdb829e89216e12b2fe753071a878dd48df6e5cf37c9af798a5a2c9db3, nearest_40 f6c6884dee8ba01d7ef660df57c5a4eea4b013944c300bb353a8d75de6890be5, nearest_45 1af338d524875b95a65dd64fe057b7b76387a8686a4e42d442905720d634d28e, nearest_50 d9ce5321361ebe0085066aceee20dff61655e4b2e137b2ce9fd0a87bd469cfed
```

```runmanifest
id: weil_dh_line-2026-10-27-timed-slices
hunt: weil_dh_line
started: 2026-10-27T02:32Z
finished: 2026-10-27T02:39Z
ran:
  - nice -n 10 .venv/bin/python <scratch>/time_slice.py L N 1280 k0 k1  (scout.unit in memory, envelope k2env_dh_L_DH.json, even, q = 64, h = 1/2, fast Bessel; no file written): (171079/100000, 856, panels 2396 to 2400), (8503/5000, 856, panels 1596 to 1600), (171079/100000, 1711, panel 3199)
outcome: success; 31.76 s a panel at T# = 1198 to 1200 and N = 856 (0.75 GB), 32.04 s a panel below the line (c = 30.0006, the same 22 comb terms) and N = 856, 123.47 s a panel at T# = 1600 and N = 1711 (2.2 GB). These price the two runs not launched ("The doors" item 5 of PRICE.md).
artifacts:
  - <cache>/raise_2026-10-27/time_slices.log (cce7d13eb6a2e0c6559f93d99ef83b18f21810f9cb7808e1efc518ecd55cdf0c)
```

```runmanifest
id: weil_dh_line-2026-10-27-stage-a-v800
hunt: weil_dh_line
started: 2026-10-27T02:36Z
finished: 2026-10-27T03:20Z
ran:
  - OMP_NUM_THREADS=1 nohup nice -n 10 .venv/bin/python hunts/weil_dh_line/witness.py stage-a hunts/weil_dh_line/v800_T800.json x 800 <cache>/raise_2026-10-27/stage_a_v800.json 64 2   (PID 856926, two pool workers; exit 0)
outcome: success, 43 min 53 s wall on 2 workers (about 1.5 core-hours, of which about 1.2 the per-job rebuild of K noted above); v^T R(800) v / v^T v = [-4.15160674833728e-30 +/- 1.0e-72] for the scout's discrete rule, the stored row to its 12 digits; exact integrals within 8.0e-89; tail mass above 800 1.4883465e-30. The F_v balls of this run were not widened for the scout's node snapping (shift below 2^-1268); the change of F_v under it is below 2 L sqrt(L/2) |v| 2^-1268 < 1e-370, far inside the recorded radius, and witness.py now widens them.
artifacts:
  - hunts/weil_dh_line/stage_a_v800.json (the raw output, SHA-256 f9a4db31a3787f0d8e048877039cc2a3c2be21c1edac89766d0116a241ba6acd; the snapping note is in this manifest, not in the file; corrected 2026-10-27 from 918680eb..., a version with the note that was not committed. This manifest was written twice on 2026-10-27, the second copy is removed)
  - <cache>/raise_2026-10-27/stage_a_v800.json f9a4db31a3787f0d8e048877039cc2a3c2be21c1edac89766d0116a241ba6acd, stage_a_v800.log 58b1935b4be3b5d36d5da444ee94d0161d7b6e550b7ebe7fe8defc925ca02fb8
```

```runmanifest
id: weil_dh_line-2026-10-27-responses-T800
hunt: weil_dh_line
started: 2026-10-27T02:59Z
finished: 2026-10-27T03:13Z
ran:
  - OMP_NUM_THREADS=1 nice -n 10 .venv/bin/python hunts/weil_dh_line/scout.py --L 171079/100000 --env hunts/weil_dh_line/k2env_dh_L_DH.json --N 856 --prec 1280 --h 1/2 --dir <cache>/k2/dh_LDH_even --responses-at-state --out <cache>/raise_2026-10-27/responses_T800.json
outcome: success, 822 s; the responses of scout.responses_of at T# = 800 from the stored state: leading_N_791 one negative pivot, lambda_min -4.15160674834e-30; rounded_1152 (the data rounded to 1152 bits, then reduced) one negative pivot, lambda_min -4.15160674834e-30
artifacts:
  - <cache>/raise_2026-10-27/responses_T800.json 2843a364501c14f2090fd248867e700febd8b733ca6200d8f9987289a6d2f10b, responses_T800.log 4016972b6020ae364202cf648ed8a9e3a0dfc7431cb24b5ddde879e57da15608
```

### Two runs priced, not launched (owner's instruction, 2026-10-27)

- **The stream past `T# = 800`** at run B's settings (restart from the stored
  state; the driver would need its unit plan extended, a small change). A unit of
  40 panels (20 in `T#`) is about `40 x 31.8 = 1270` s and a checkpoint about
  500 s (run B: 443 to 531). To `T# = 880`, past the `beta = 1/2` operating point
  `870.8`: 4 units and 4 checkpoints, about **2.0 core-hours**, about 1 h wall.
  To `T# = 1600`: 40 units, about 50 900 s, and 8 checkpoints (one every 100),
  about 4 000 s: **about 15 core-hours, about 2 h wall on 8 workers**; with a
  checkpoint every 20, about 20 core-hours and about 6 h wall (the serial
  reduction binds). Disk: the restart state, 125 MB a generation. With the mode
  rule `2N/x = 1.25` instead (`N = 1711` at `T# = 1600`, a new assembly from
  `T# = 0`): `3200 x 123.5 s`, about **110 core-hours** of units plus about 9 of
  reduction, about 15 h wall on 8 workers, 2.2 GB a worker.
- **The below-the-line discrimination control**: DH at `L' = 8503/5000`
  (`c = 30.0006`), `N = 856`, 1280 bits, `T#` to 800, with `k2env_dh_L_DH.json`
  (valid at `L'`: the same comb, and every frequency at least `2 L_DH > 2L'`).
  40 units of `40 x 32.0 s` and 14 checkpoints: **about 16.2 core-hours**, about
  5.5 h wall on 3 workers (run B's configuration) or about 2.5 h on 7. Its
  decisive companion, `Q_856` at `L'` by `witness.py --L 8503/5000`: **5.6
  core-hours, 48 min wall on 8 processes**, as measured at `L_DH`.

Recorded in flight before waiting on it, then completed:

```runmanifest
id: weil_dh_line-2026-10-27-stage-a-witness
hunt: weil_dh_line
started: 2026-10-27T02:51Z
finished: 2026-10-27T03:36Z
ran:
  - nohup nice -n 10 .venv/bin/python hunts/weil_dh_line/witness.py stage-a <cache>/raise_2026-10-27/witness_v856.json v 800 <cache>/raise_2026-10-27/stage_a_witness.json 64 2   (PID 917918, pool workers 917927 and 917928; log stage_a_witness.log)
outcome: success, exit 0, 44 min 33 s wall on 2 workers (about 1.5 core-hours). v^T R(800) v / v^T v at the 856-mode witness = [-2.83155721280920e-30 +/- 1.03e-72] (the stored-state value of the analysis, -2.83155721281e-30, by a route independent of it), exact integrals within 8.03e-89; tail mass above 800 m_800 = 1.4220221e-31 (upper 1.42202215e-31), so the refusal at every T# >= 800 survives an envelope bound low by any delta < 1.9430836e-30 / 1.4220222e-31 = 13.66 (for N >= 856). This run, like the v800 run, started before witness.py widened F_v for the node snapping; the same note applies (a change below 1e-370, far inside the radius)
artifacts:
  - hunts/weil_dh_line/stage_a_witness.json (SHA-256 fec84f2311bf4528de456c8d920ad330e8ee26d6b94e0092a3be7d01d427cef8)
```

## Corrections and reproduction (2026-10-27, after the review of ee06df8af)

Recorded in flight before waiting (the derived pieces of `witness_q856.json`
re-run from committed code, `witness.py` subcommands, into
`<cache>/raise_2026-10-27/repro/`; launched 04:08Z with `setsid nohup nice -n 10`,
BLAS threads 1):

- `witness.py blocks <cache>/raise_2026-10-27/q856.pkl repro/blocks.json 50 100 101 ... 350` (PID 1242189, log repro/blocks.log)
- `witness.py shifted-counts <cache>/raise_2026-10-27/q856.pkl <cache>/k2/dh_LDH_even repro/counts.json` (PID 1242191, log repro/counts.log)
- `witness.py reassemble hunts/weil_dh_line/witness_v101.json 320 repro/reassembled_101.json` (PID 1242192, log repro/reas.log)
- `witness.py block-witness <cache>/raise_2026-10-27/q856.pkl 101 repro/witness_v101.json` (finished in seconds)

Outcome (04:15Z, all exit 0; about 0.15 core-hours): every piece reproduced.
`blocks` gave the 23 leading-block rows of `blocks_small`, `blocks_onset` and
`blocks_onset2` identically; `block-witness 101` gave `witness_v101.json`
byte for byte; `reassemble` gave the same quotient `-4.49000370077141e-32`
(32.8 s); `shifted-counts` gave the same six counts. `witness.py record` merges
them with the analysis record, the stored responses and the timed slices into a
file identical to the committed `witness_q856.json` except one wall-clock
field (the re-assembly's `seconds`, 32.78 against 32.20), so the committed file
stands. Outputs: repro/blocks.json 34acfbb36e85c69c8dab124ff2e44a45d0af3bedfccd7b9c8cd8b459b37440d4,
repro/counts.json 16fae8c143f2800cd99a0abcce934892b0059a76d7f18a2829ccc76d077213b4,
repro/reassembled_101.json 4ab73dcdaff052ecea06492d88766bf48a4261a8dc91445283ae1bb3afe73182,
repro/witness_q856.json 80948a9e9ee5bdcca6480fcaa3ecf7aa24d62c20468d4808707007b2402f9e28.

Other corrections from the review: the "independent assembly" of `Q_101` is
the same code at other nodes and precision (the independent check is the
reviewer's separate implementation, `PRICE.md` item 7); every SHA-256 named
here for a committed artifact now matches its bytes, and
`test_witness.py::test_runs_md_hashes_match_the_committed_artifacts` keeps it so.

Provenance: part of ee06df8af was written in this checkout by a second, resumed
copy of the session after a restart around 03:00Z (the widening of `F_v` for
the node snapping in `witness.py`, the stage-A v800 and responses manifests, and
the keys `responses_T800` and `timed_slices` of `witness_q856.json`). It was
committed unreviewed; this correction reviewed it: the widening is right
(`|F_v'| <= 2 L sqrt(L/2) |v|`), the two keys copy their sources faithfully, and
the manifests are corrected above.
