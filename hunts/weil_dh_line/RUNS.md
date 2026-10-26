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
