# RUNS: li_arithmetic (hunt #150, mechanism 3)

Single-process Python on the campaign box (`<box>`), commands run from the repository root
with `.venv/bin/python`. The 2026-10-21 runs were written up on 2026-10-26: their times
come from each artifact's own `generated` stamp (the box clock is UTC) and its file
modification time, and their durations from the `seconds_*` fields the artifacts record.
The 2026-10-26 run was timed by the session at `nice 10`, with the 1-minute load average
about 48 from other sessions' work.

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-21-split
hunt: rh_moonshot
started: 2026-10-21T22:22Z
finished: 2026-10-21T22:28Z
ran:
  - .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_split.py
outcome: zeta 179 s (A 156 s, T 10 s, lambda 13 s) and DH 150 s (A 52 s, T 98 s) for n <= 5000 at r = 0.95, 162 work digits, 16384 nodes; identity defects 8.1e-28 and 3.1e-27, and abs T(n) at most 13.5 for zeta and 19.1 for DH
artifacts:
  - hunts/rh_moonshot/li_arithmetic/artifacts/split_zeta.json
  - hunts/rh_moonshot/li_arithmetic/artifacts/split_dh.json
```

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-21-wa
hunt: rh_moonshot
started: 2026-10-21T22:33Z
finished: 2026-10-21T22:39Z
ran:
  - .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_wa.py
outcome: 334 s (Cauchy at r = 0.95 120 s, control at r = 0.93 191 s, zero side 23 s) for n <= 9000 with 32768 nodes; the two radii agree to 2.6e-48 and the first negative index is 8260, where the zero-side route agrees to 2.5e-3
artifacts:
  - hunts/rh_moonshot/li_arithmetic/artifacts/wa_quarter.json
```

Estimate written before the prime-side run: one unit, x0 = 10^6 and n <= 500, took 9 s
wall (5 s CPU, 52 MB peak), 7.2 s of it the kernel bounds on 135925 grid points. The kernel
cost scales with grid points times n, so the full run (222035 points, n <= 5000) was
estimated at 7.2 x 16.3, about 2 minutes, plus the 10^8 sieve: well under one core-hour,
so it ran without asking.

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-26-prime-timing
hunt: rh_moonshot
started: 2026-10-26T12:56Z
finished: 2026-10-26T12:56Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_prime.py --x0 1000000 --n-max 500 --out-dir <scratch>/prime_t1
outcome: 9 s wall; the timing unit, output kept in the session scratch directory only
artifacts:
```

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-26-prime
hunt: rh_moonshot
started: 2026-10-26T12:56Z
finished: 2026-10-26T12:57Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/li_arithmetic/run_li_arith_prime.py
outcome: 76 s wall, 56 s CPU, 486 MB peak (sieve 3 s, 5762859 prime powers below 10^8, kernel 65 s); the pointwise bound exceeds the margin at every n <= 5000 where the margin is positive, the mean-square bound is below it only for n in [32, 1258], and the regularized prime sum is within 8.1e-4 of T(n) for n <= 6
artifacts:
  - hunts/rh_moonshot/li_arithmetic/artifacts/prime_side.json
```

```runmanifest
id: rh_moonshot-li_arithmetic-2026-10-26-tests
hunt: rh_moonshot
started: 2026-10-26T13:07Z
finished: 2026-10-26T13:08Z
ran:
  - nice -n 10 .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/li_arithmetic/test_li_arithmetic.py
outcome: 15 passed in 27 s, the tree unchanged
artifacts:
  - hunts/rh_moonshot/li_arithmetic/test_li_arithmetic.py
```
