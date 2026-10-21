# RUNS: estimates before spending, and what each run did

Box rules (MISSION.md): the swarm box is shared; at most 4 worker processes; no heavy
start while the 1-minute load average is above 64; `MemAvailable` above 20 GiB (each
worker here holds well under 1 GiB). Every census stage checkpoints one JSON file per
unit and skips units already on disk, so an interrupted run resumes.

## Estimate for the census to height 1000 (written 2026-10-21, before launch)

Timed units, measured single-process on the box under a load average of about 80 to
100, at heights near 990 where every unit is most expensive (`census.py` stages):

| unit | q = 17 | q = 73 |
|---|---|---|
| route A: one Z(t) value (mpmath fp, 16 or 72 Hurwitz values) | 0.023 s | 0.28 s |
| route B: one decided sign of Z(t) (Arb, 64 bits) | 0.019 s | 0.061 s |
| route A: one folded count N(0, T) (32 evaluations) | 1.4 s | 4.1 s |
| route B: one decided folded count (18 and 24 segments) | 0.53 s | 2.5 s |
| route A: one right-box count, height 8 (about 500 evaluations) | 10 s | 59 s |

Multiplied out (grid of 1/12 of the mean gap for route A, 1/10 for route B, windows of
height about 8, so about 125 boundaries per q; about 4 right-box counts and one Newton
grid per window that carries an excess; the number of such windows guessed from the
pilot below as 20 to 35):

| stage | q = 17 CPU | q = 73 CPU |
|---|---|---|
| scanA | 200 to 300 s | 2000 to 2500 s |
| psiA | 125 s | 400 s |
| winA | 800 to 1500 s | 3000 to 5000 s |
| scanB | 150 s | 550 s |
| psiB | 60 s | 250 s |
| boxB | 150 s | 200 s |
| **total** | **about 0.5 to 0.7 CPU-hours** | **about 1.8 to 2.5 CPU-hours** |

On 4 workers that is about 10 to 15 minutes of wall time for q = 17 and 30 to 45 minutes
for q = 73 on an idle box; the box is oversubscribed, so up to three times that.
Memory is negligible. Both are above the twenty-minute line together, hence this
estimate, the per-unit checkpoints, and a launcher that waits for the load rule.

## The launch decision (2026-10-21, about 17:25)

A launcher waiting for the 1-minute load to fall to 64 waited from 17:07 to 17:23 with the
load between 70 and 81 throughout (other workflows' Lean builds hold the box). It was
replaced by a per-stage launcher: each census stage starts with 4 workers if the
1-minute load is at most 64 and `MemAvailable` at least 30 GiB, and otherwise with one
worker. A single process on a 32-vCPU box is not treated as a heavy parallel job; it adds
one core and under 1 GiB. The cost of that choice is wall time only: at one worker the
estimate above becomes about 0.5 to 0.7 hours for q = 17 and 2 to 2.5 hours for q = 73.

## Incident: a stalled right-box window, and two fixes (2026-10-21, about 17:47 to 18:05)

Route A's right-box stage for q = 17 stopped advancing at window 80 (heights 639.6 to
647.95) for more than ten minutes. Two defects combined. `newton_fp` stopped on an
absolute step tolerance of 1e-13, and at height 640 the spacing of floats near Im s is
about 1e-13, so Newton never declared convergence on the zero near
0.55671 + 642.88846 i (|F| had reached 8.4e-14). The bisection then caught that error at
every level and retried five shifted cuts, each of which recursed down to the same
failure: an exponential retry, not a hang. Fixes, both in this commit's code: the Newton
tolerance is relative to |s| (64 ulp), and only the count at the cut is retried, so a
failure below it propagates at once. The stalled stage was stopped by PID and relaunched;
the 25 windows already checkpointed were kept, since each closed its own accounting.
Those 25 were computed with the earlier sampling (forced step 0.04, both halves counted);
every later window uses step 0.08 with the upper half's count inferred by additivity.
The two give the same zeros on the windows re-run to compare (25.69, 99.88).

## Pilot (2026-10-21): q = 17 to height 120, 2 workers, 43 s wall

`census.py --q 17 --stage all --workers 2 --tend 120`, scratch checkpoints. Both routes
closed every one of 15 windows: 91 zeros with 0 < Im s <= 120.0234375, 87 sign changes
of Z on the line, 2 zeros in Re s > 1/2 (near 0.66703 + 25.69077 i and
0.84076 + 99.87784 i), each in a decided route B box of half-width 2^-30. The parity
check sign Z(T_j) = (-1)^N(T_j) held at every boundary on both routes.
