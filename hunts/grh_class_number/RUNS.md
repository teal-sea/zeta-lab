# Run record

## Baseline

Checkout `/home/user/zeta-lab`, branch `claude/sweet-planck-pf4oco` at
`a401821c`. `zeta.rigor.BACKEND` is `python-flint` (backends
`['mpmath.iv', 'python-flint']`). cypari2 is importable. gcc 13.3 compiles
`cnx.c` (`-O3 -march=native`, AVX-512BW present). Four cores and 15 GB, shared
with other sessions that are reading an archive; at most three search
processes at a time, each under 3 GB. `SCRATCH` below is
`/tmp/claude-0/-home-user-zeta-lab/0611ad8c-0964-51e2-b6c9-1e1cf6364191/scratchpad/grh_class_number`:
the full lists live there and are not committed; each is identified by its
sha256.

## Unit timings and estimates, written before the scaled run (2026-11-20T16:53Z)

**Bound side** (Arb, 128 bits, sigma0 = 1/2). The fine cover of
`[10^2, 10^11]` at ratio 1.01 (2041 cells) took 79.7 s, the log-scale bridge
`[10^11, 10^50]` (77 cells) and the tail constant 4.2 s. It gives
`D_GRH(5000) = 16 396 235 837`, which fixes the search range.

**Search side, the sibling's `cn.c` unchanged, H = 5000** (one core, seconds):

| unit | seconds | per 10^6 of range | note |
| --- | --- | --- | --- |
| `[3, 2*10^6]` | 6.5 | 3.2 | every discriminant is listed |
| `[10^7, 1.2*10^7]` | 22.3 | 11.2 | 601 782 of 607 925 listed |
| `[10^8, 1.02*10^8]` | 42.9 | 21.4 | 404 056 listed |
| `[5*10^8, 5.2*10^8]` | 471.1 | 23.6 | 4 339 260 exact counts, 1 263 806 listed |
| `[2*10^9, 2.02*10^9]` | over 300 | over 15 | did not finish in the 600 s window with the others |
| `[10^10, 1.002*10^10]` | (not timed alone) | | 31 filter survivors |
| `[1.6*10^10, 1.602*10^10]` | 17.6 | 0.88 | 0 survivors |

Estimate for `cn.c` at H = 5000 over `[3, 16 396 235 837]`: the list has about
4.1 H^2 = 10^8 fields and each costs an exact count of 40 to 110 microseconds
(over 2 CPU-hours for the listed fields alone), and between 10^8 and 4*10^9
almost every discriminant survives the streamed filter (composite cap 4000,
tuned for H <= 1500) and pays the same exact count: more than 20 s per 10^6 of
range over more than 3*10^9, so **more than 20 CPU-hours**. That is five times
the budget of about 4 CPU-hours. With `cn.c` alone the budget allows about
H = 3000.

**Decision, before the scaled run.** Keep H = 5000 and replace the driver, not
the arithmetic: `cnx.c` includes `cn.c` unchanged and adds cache-sized blocks,
saturating counters and, below 3*10^9, a direct enumeration of the reduced
forms with large first coefficient, so that no per-discriminant exact stage is
needed there (RESULTS.md section 5). Unit timings of `cnx.c`, H = 5000, one
core, on ranges of 10^7 or 2*10^7 (seconds per 10^6 of range):

| at | mode | per 10^6 | compared with |
| --- | --- | --- | --- |
| 3 | full | 0.06 | `cn.c` output, byte-identical |
| 10^7 | full | 0.08 | `cn.c` output, byte-identical |
| 10^8 | full | 0.28 | `cn.c` output, byte-identical |
| 5*10^8 | full | 0.35 | `cn.c` output, byte-identical (1 263 806 fields) |
| 10^9 | full | 0.50 | |
| 2*10^9 | full | 0.78 | |
| 3*10^9 | full | 0.79 | filter mode, byte-identical |
| 3*10^9 | filter, all a | 0.87 | 8 188 survivors per 10^7 |
| 4*10^9 | full / filter all a / filter A0 = 28000 | 1.15 / 0.65 / 0.64 | |
| 5*10^9 | filter A0 = 26000 / 20000 | 0.53 / 0.56 | |
| 6.5*10^9 | filter A0 = 20000 / 16000 | 0.45 / 0.44 | |
| 8*10^9 | filter A0 = 16000 / 12000 | 0.46 / 0.31 | |
| 10^10 | filter A0 = 10000 / 7000 | 0.29 / 0.25 | |
| 1.2*10^10 | filter A0 = 8000 / 5000 | 0.41 / 0.22 | |
| 1.4*10^10 | filter A0 = 4000 / 2000 / 1 | 0.24 / 0.21 / 0.19 | |
| 1.6*10^10 | filter A0 = 1 (primes only) | 0.19 | 0 survivors |

Mode "full" costs about 0.52 sqrt(n / 10^9) s per 10^6 of range, so it is used
up to 3*10^9, where the filter becomes cheaper. **Estimate for the scaled
run** (`search.py plan 5000 16396235837`): 194 chunks, 60 in full mode (1802
CPU-s) and 134 in filter mode (4703 CPU-s), **6505 CPU-seconds = 1.8
CPU-hours**, about 2170 s on each of three workers, so 40 to 60 minutes of
wall clock on shared cores, plus about 25 s per worker to build the pattern
cache (about 1.3 GB per worker, under the 3 GB limit). Every chunk is a
checkpoint (at most about 80 s each): a chunk whose `.stats` file exists is
skipped on restart. CPU already spent before the scaled run: about 20 minutes
(the `cn.c` units above, the `cnx.c` units and checks, the bound tables).
