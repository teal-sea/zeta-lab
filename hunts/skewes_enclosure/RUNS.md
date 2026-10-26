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

## 2026-10-26: production estimate (not run; asked of the coordinator)

Pending the shard result below. Bracket from the unit timings: the top of the
range costs 27 to 36 ms/zero at 64 bits on this loaded box. If the cost were
flat at that level, 2.2e7 zeros would take **2.2e7 x 0.027 to 0.036 s =
165 to 220 core-hours**, and 2e6 zeros (Chao-Plymen, T = 1131944.47) would take
**2e6 x 0.02 to 0.05 s = 11 to 28 core-hours**. Both are far over the one-core-hour
line and wait for the coordinator's answer.
