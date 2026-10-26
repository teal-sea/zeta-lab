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
