# Run record

## Baseline

Checkout `/home/user/zeta-lab-qrh-class-number`, branch `hunt/qrh-class-number`
from `origin/main` at `ef4e0564`. `zeta.rigor.BACKEND` is `python-flint`
(backends `['mpmath.iv', 'python-flint']`). cypari2 is importable; no `gp`
binary is used. gcc 13.3 compiles `cn.c` (`-O3 -march=native`). Four cores and
15 GB shared with three other agents: every heavy run below was a single
process.

## Unit timings and estimates, before the scaled runs

Bound side (Arb, 128 bits). One verified interval of Theorem B (float
optimisation plus Arb evaluation) takes 0.08 to 0.13 s. The D(h) cover of
`[10^2, 10^11]` at ratio 1.01 has about 2080 intervals: estimate 4.5 min,
measured 2 min 51 s. The Theorem A cover (163 log-scale intervals to 10^50)
and the tail: measured 19 s. The abscissa ladder (24 points): 8 s.

Search side (`cn.c`, H = 1000), measured on 2*10^6-wide or 2*10^7-wide units:

| unit | seconds | seconds per 10^6 of range |
| --- | --- | --- |
| `[3, 2*10^6]` | 7.6 | 3.8 |
| `[10^7, 1.2*10^7]` | 9.2 | 4.6 |
| `[5*10^7, 5.2*10^7]` | 2.6 | 1.3 |
| `[2*10^8, 2.02*10^8]` | 0.54 | 0.27 |
| `[4.5*10^8, 4.52*10^8]` | 0.69 | 0.35 |
| `[10^9, 1.02*10^9]` | 1.5 | 0.075 |
| `[5*10^9, 5.02*10^9]` | 1.6 | 0.078 |

Integrating piecewise over `[3, D(1000)] = [3, 5433399820]`: about 42 + 112 +
105 + 90 + 380 s, so about 12 minutes of one core. Chunks are at most
5*10^6 wide below 10^8 and 2*10^8 wide above (each under 25 s), and every
chunk is a checkpoint (`run_search.py` skips completed chunk files). The H = 100
run to `D(100) = 48611613` is estimated at under 10 s.

An H = 2000 run to `D(2000) = 22320645193` extrapolates to more than an hour
(the prime-only stage alone is about 3300 s with K = 2640 primes), outside the
budget; see RESULTS.md, The doors.

## H = 1500, estimate before launch

After the H = 1000 run (600 s, of which 316 s in the prime stage above
5 * 10^8): the prime stage scales with K = 1990 / 1340 and with the range
`[1.2 * 10^9, D(1500) = 12409254457]`, about 56 chunks of 19 s, so 18 min;
below that the survivor stage grows with the list. Estimate 30 to 35 min of
one core, within the remaining budget; checkpointed per chunk. The run was
launched at 12:12 UTC with the H = 1000 results already recorded, so that a
stop at any chunk loses nothing already claimed.

`SCRATCH` below is this session's scratchpad directory: the full lists live
there and are not committed; each is identified by its sha256.

## Run manifests

```runmanifest
id: qrh_class_number-2026-10-08-dtable
hunt: qrh_class_number
started: 2026-10-08T11:55:35+00:00
finished: 2026-10-08T11:58:26+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.run_bounds dtable
outcome: 2041 verified intervals cover 10^2 to 10^11 and give D(h) for every h up to 2000, with D(100) = 48611613 and D(1000) = 5433399820, in 171 s
artifacts:
  - hunts/qrh_class_number/dtable.json
```

```runmanifest
id: qrh_class_number-2026-10-08-theorem-a
hunt: qrh_class_number
started: 2026-10-08T11:58:59+00:00
finished: 2026-10-08T11:59:27+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.run_bounds theorem_a
  - .venv/bin/python -m hunts.qrh_class_number.run_bounds abscissae
outcome: the tail constant at 10^50 is 0.10341 and the 163-interval cover from 121 to 10^50 keeps L log log q at least 0.10030; the abscissa ladder 1/2, 7/8, 11/12, 15/16 is strictly ordered at all six q
artifacts:
  - hunts/qrh_class_number/theorem_a.json
  - hunts/qrh_class_number/abscissae.json
```

```runmanifest
id: qrh_class_number-2026-10-08-search-h100
hunt: qrh_class_number
started: 2026-10-08T11:59:51+00:00
finished: 2026-10-08T11:59:53+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.run_search 100 48611613 SCRATCH/search100
  - .venv/bin/python -m hunts.qrh_class_number.controls watkins 100
outcome: 42272 fields with h at most 100 below D(100), largest 2383747, all 100 counts and largest discriminants equal to Watkins' table, in 1.8 s
artifacts:
  - hunts/qrh_class_number/search_H100.json
```

```runmanifest
id: qrh_class_number-2026-10-08-search-h1000
hunt: qrh_class_number
started: 2026-10-08T12:00:05+00:00
finished: 2026-10-08T12:10:04+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.run_search 1000 5433399820 SCRATCH/search1000
  - .venv/bin/python -m hunts.qrh_class_number.controls watkins 1000
outcome: 1651555483 fundamental discriminants below D(1000) sieved in 599 s on one core; 4115897 fields have h at most 1000, largest 227932027, Watkins reproduced for h at most 100 and Holmin-Kurlberg reproduced for every odd h at most 1000
artifacts:
  - hunts/qrh_class_number/search_H1000.json
  - hunts/qrh_class_number/holmin_kurlberg_odd.json
  - hunts/qrh_class_number/watkins.json
```

```runmanifest
id: qrh_class_number-2026-10-08-exact-l
hunt: qrh_class_number
started: 2026-10-08T12:11:20+00:00
finished: 2026-10-08T12:11:38+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.controls exact_l SCRATCH/exactl
outcome: every one of 911847 fundamental discriminants with 100 to 3*10^6 has exact L(1, chi_D) at least 3.888 times the verified bound, PARI lfun agrees to 2.2e-16, and L log log |D| is at least 0.1 from |D| = 4
artifacts:
  - hunts/qrh_class_number/controls_exact_l.json
```

```runmanifest
id: qrh_class_number-2026-10-08-search-h1500
hunt: qrh_class_number
started: 2026-10-08T12:12:19+00:00
finished: 2026-10-08T12:51:39+00:00
ran:
  - .venv/bin/python -m hunts.qrh_class_number.run_search 1500 12409254457 SCRATCH/search1500
  - .venv/bin/python -m hunts.qrh_class_number.run_search 1500 12409254457 SCRATCH/search1500
  - .venv/bin/python -m hunts.qrh_class_number.controls watkins 1500
outcome: the first session was stopped by the 30-minute background limit after 56 of 82 chunks and the second resumed from the chunk checkpoints; 3771960997 fundamental discriminants below D(1500) in 2327 s of chunk time, 9245562 fields with h at most 1500, largest 562394347, Watkins and Holmin-Kurlberg (odd h at most 1500) reproduced
artifacts:
  - hunts/qrh_class_number/search_H1500.json
  - hunts/qrh_class_number/holmin_kurlberg_odd.json
```

The estimate (30 to 35 min) was close to the measured 39 min; the survivor
stage between 10^8 and 5 * 10^8 cost 465 s against about 150 s expected,
because the list with h <= 1500 is dense there (one chunk alone took 360 s).

```runmanifest
id: qrh_class_number-2026-10-08-checks
hunt: qrh_class_number
started: 2026-10-08T12:51:50+00:00
finished: 2026-10-08T12:57:30+00:00
ran:
  - CN_CHECK_STREAM=1 hunts/qrh_class_number/build/cn on four windows (10^5 to 3*10^5 at H 100; 3*10^8, 10^9, 2*10^9 at H 1000 or 1500)
  - hunts/qrh_class_number/build/cn on two H 1000 chunks, compared byte for byte with the run files
  - .venv/bin/python -m hunts.qrh_class_number.run_bounds eleven
  - .venv/bin/python -m hunts.qrh_class_number.controls pari 1500 SCRATCH/search1500
outcome: every streamed count recomputed equal, both chunks byte-identical, 11/12 gives c = 1/16 and D(1000) = 10592194843, PARI agrees on 1900 discriminants, and the h at most 1000 and h at most 100 sub-lists of the H 1500 run hash equal to the H 1000 and H 100 runs
artifacts:
  - hunts/qrh_class_number/eleven_twelfths.json
  - hunts/qrh_class_number/controls_pari_H1500.json
```
