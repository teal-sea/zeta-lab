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

## Unit timings and estimates, written before the scaled run (2026-11-20T16:52Z)

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
| `[2*10^9, 2.02*10^9]` | 350.2 | 17.5 | 3 271 455 exact counts, 68 820 listed |
| `[10^10, 1.002*10^10]` | 12.7 | 0.63 | 31 filter survivors |
| `[1.6*10^10, 1.602*10^10]` | 17.6 | 0.88 | 0 survivors |

Estimate for `cn.c` at H = 5000 over `[3, 16 396 235 837]`: the list has about
4.1 H^2 = 10^8 fields and each costs an exact count of 10 to 110 microseconds
(over 2 CPU-hours for the listed fields alone), and between 10^8 and 4*10^9
more than half of the discriminants survive the streamed filter (composite
cap 4000, tuned for H <= 1500) and pay the same exact count: 17 to 24 s per
10^6 of range over more than 3*10^9, so **more than 20 CPU-hours**. That is
five times the budget of about 4 CPU-hours. With `cn.c` alone the budget
allows about H = 3000 (an estimate, not run).

(Honest edit note: the timing batch finished at 16:39Z, before the scaled
run, but its rows for 2*10^9 and 10^10 were read into this table only after
the run, and the paragraph above was reworded then from "almost every
discriminant survives ... more than 20 s per 10^6". The conclusion, the
decision below and the estimate of 6505 CPU-seconds are as first written.)

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
| 2*10^9 | full | 0.78 | `cn.c` output, byte-identical (68 820 fields) |
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

## The scaled run, measured

Launched 2026-11-20T16:52:53Z, finished 17:35:28Z: 2555 s of wall clock with
three workers, all 194 chunks, no restart needed. CPU time of the three
workers, read from `ps` ten seconds before the last one exited: 33:43, 33:44
and 33:50, so **6077 CPU-seconds = 1.69 CPU-hours** against the estimate of
6505. The cores were shared (load average 3.5 to 5.8 throughout), so the
per-chunk times the workers recorded are wall clock and add up to more:

| zone | chunks | estimated CPU-s | recorded chunk seconds (wall, shared cores) |
| --- | --- | --- | --- |
| mode 1, `[3, 3*10^9]` | 60 | 1802 | 2071 |
| filter, all a, to 3.6*10^9 | 6 | 480 | 618 |
| filter A0 = 28000, to 5*10^9 | 14 | 868 | 1065 |
| filter A0 = 24000, to 6*10^9 | 10 | 500 | 503 |
| filter A0 = 18000, to 8*10^9 | 20 | 860 | 1049 |
| filter A0 = 12000, to 10^10 | 20 | 620 | 899 |
| filter A0 = 7000, to 1.2*10^10 | 20 | 500 | 499 |
| filter A0 = 4000, to 1.4*10^10 | 20 | 420 | 481 |
| filter A0 = 1, to 16 396 235 837 | 24 | 456 | 470 |

Resident memory per worker was 1.20 to 1.23 GB when last sampled, ten
minutes before the end, and the pattern cache ended at 1.24 to 1.27 GB, so
each worker stayed near 1.5 GB, under the 3 GB limit. The list files take 1.5 GB in `SCRATCH`.

Whole hunt, all CPU: about 2.2 CPU-hours of the 4 allowed (16 minutes for the
`cn.c` units, which is what showed that `cn.c` could not do it; 1.69 hours
for the run; the rest for the `cnx.c` units and checks, the bound tables,
the controls and the tests).

## Run manifests

```runmanifest
id: grh_class_number-2026-11-20-cn-units
hunt: grh_class_number
started: 2026-11-20T16:22:10Z
finished: 2026-11-20T16:39:50Z
ran:
  - hunts/grh_class_number/build/cn (the sibling's cn.c, compiled here) at H 5000 on seven ranges of 2*10^6 or 2*10^7
outcome: cn.c costs 21 to 24 s per 10^6 of range between 10^8 and 5*10^8 at H 5000, which extrapolates to more than 20 CPU-hours for the whole range, five times the budget
artifacts:
```

```runmanifest
id: grh_class_number-2026-11-20-dtable
hunt: grh_class_number
started: 2026-11-20T16:41:48Z
finished: 2026-11-20T16:43:12Z
ran:
  - .venv/bin/python -m hunts.grh_class_number.bounds dtable
outcome: 2041 adjacent cells cover 10^2 to 10^11 at abscissa 1/2, 77 bridge cells and the tail constant 0.3857 close the range beyond, and D_GRH(h) follows for every h up to 10000, with D_GRH(100) = 5554909 and D_GRH(5000) = 16396235837, in 84 s
artifacts:
  - hunts/grh_class_number/dtable_grh.json
```

```runmanifest
id: grh_class_number-2026-11-20-cnx-units
hunt: grh_class_number
started: 2026-11-20T16:43:30Z
finished: 2026-11-20T16:51:20Z
ran:
  - hunts/grh_class_number/build/cnx 5000 PLAN on 33 unit ranges in both modes, compared with cn.c output on four of them
  - CNX_CHECK_STREAM=40 hunts/grh_class_number/build/cnx 5000 PLAN on four filter windows
  - CNX_CHECK_FULL=1 hunts/grh_class_number/build/cnx 5000 PLAN on four mode 1 windows
outcome: mode 1 output is byte-identical to cn.c on five ranges (2946395 fields) and to mode 0 at 3*10^9, 28496 sampled streamed counts and 212769 enumerated class numbers recompute equal, and the unit timings give an estimate of 6505 CPU-seconds for H 5000
artifacts:
```

```runmanifest
id: grh_class_number-2026-11-20-search-h5000
hunt: grh_class_number
started: 2026-11-20T16:52:53Z
finished: 2026-11-20T17:36:28Z
ran:
  - .venv/bin/python -m hunts.grh_class_number.search run 5000 16396235837 SCRATCH/search5000 3
  - .venv/bin/python -m hunts.grh_class_number.search summarise 5000 16396235837 SCRATCH/search5000
outcome: 4983858175 fundamental discriminants below D_GRH(5000) in 6077 CPU-seconds on three workers; 102746940 fields have h at most 5000, largest 6912348787 with h 4967, every h occurs, and the bound sits at least 1.449 times below the exact L(1, chi_D) of every listed field
artifacts:
  - hunts/grh_class_number/search_H5000.json
  - hunts/grh_class_number/controls_exact_l.json
```

```runmanifest
id: grh_class_number-2026-11-20-bound-controls
hunt: grh_class_number
started: 2026-11-20T16:53:04Z
finished: 2026-11-20T17:08:40Z
ran:
  - .venv/bin/python -m hunts.grh_class_number.bounds theorem_a
  - .venv/bin/python -m hunts.grh_class_number.bounds ladder
  - .venv/bin/python -m hunts.grh_class_number.bounds door
  - .venv/bin/python -m hunts.grh_class_number.controls lls
  - .venv/bin/python -m hunts.grh_class_number.controls zero_term
  - .venv/bin/python -m hunts.grh_class_number.controls independent
outcome: the cover keeps L log log q at least 1/3 from 22786 to 10^50; the bound at 1/2 is 2.52 to 2.92 times the bound at 7/8 on all 2041 cells and 1.06 to 2.35 times the published GRH bound on all 2118 cells; at seven characters the explicit-formula identity holds to 7e-6 with PARI zeros and the true zero sum is 0.40 to 0.80 of its bound; a second evaluation route agrees to 0.09 percent in R
artifacts:
  - hunts/grh_class_number/theorem_a_grh.json
  - hunts/grh_class_number/controls_ladder.json
  - hunts/grh_class_number/door_2_40.json
  - hunts/grh_class_number/controls_lls.json
  - hunts/grh_class_number/controls_zero_term.json
  - hunts/grh_class_number/controls_independent.json
```

```runmanifest
id: grh_class_number-2026-11-20-list-controls
hunt: grh_class_number
started: 2026-11-20T17:36:40Z
finished: 2026-11-20T17:39:56Z
ran:
  - .venv/bin/python -m hunts.grh_class_number.controls make_hk SCRATCH/hk_class_group_orders.txt
  - .venv/bin/python -m hunts.grh_class_number.controls crosschecks
  - .venv/bin/python -m hunts.grh_class_number.controls fault
  - .venv/bin/python -m hunts.grh_class_number.controls small_range SCRATCH/search5000
  - .venv/bin/python -m hunts.grh_class_number.controls pari SCRATCH/search5000
outcome: the lists equal the sibling's for h at most 1500 (same sha256), Watkins for h at most 100, Holmin-Kurlberg for all 2500 odd h below 5000 and the 20 rows of the Garcia-Grenie-Lee-Molteni table; PARI agrees on the largest discriminant of every h, 577 random entries and 11856 discriminants in 13 windows; the planted sign fault produces 2724 violations and the true bound none
artifacts:
  - hunts/grh_class_number/holmin_kurlberg_odd_5000.json
  - hunts/grh_class_number/crosschecks.json
  - hunts/grh_class_number/controls_fault.json
  - hunts/grh_class_number/theorem_a_small.json
  - hunts/grh_class_number/controls_pari.json
```
