# RUNS: estimates, launches and manifests for hunt #148

All runs are single-process Python on the swarm box (32 vCPU, 115 GiB, shared), started at
`nice 10`, with the 1-minute load average between 56 and 100 during the session (other
workflows' Lean builds and numerics). Times below are wall-clock under that load, so they
are upper estimates for an idle box.

## Estimate written before the full run (2026-10-21, 17:40 box time)

Unit timings, from the exploratory runs of this session (same code paths, single process):

| unit | size | measured time |
|---|---|---|
| Davenport-Hasse by brute force, q = 7, n = 3, deg c <= 3 | 34,202 Gauss sums | 23 s |
| the same, q = 7, n = 6 | 85,505 | 73 s |
| the same, q = 13, n = 4, deg c <= 2 | 85,683 | 81 s |
| structural against brute-force Gauss sums, q = 7, n = 3 | 319,200 | 164 s |
| three routes to F(s, A, H) | 30,576 | 138 s |
| K against the product of local summands | 12,642 tuples | 48 s (3.8 ms per tuple) |
| probe triples of total degree at most 5, three representations | 13 triples | 300 s, slowest 210 s |
| n = 4 relations at q = 13 (C sums up to degree 5) | about 40 coefficients | over 40 minutes, not finished when stopped |

Estimate for the full run, by part (each part writes `results_<part>.json` when it ends,
and steps 2 and 3 checkpoint every unit to `results_<part>.partial.json`, so a restart
resumes after the last finished unit):

| part | estimate |
|---|---|
| step1 (sources formulas, q = 7, n = 3 brute force to degree 3) | 10 minutes |
| step2 (the probe and Lemma 7.1; K on about 130,000 tuples; three large triples) | 90 to 150 minutes |
| step3 (biquadratic theta at q = 13, degree-4 samples) | 60 to 120 minutes |
| ledger (prime classes to degree 6; two balanced probes) | 15 minutes |
| rival (210 characters; principal row to degree 3 in X and 1 in W) | 5 minutes |

The parts run as four concurrent single-process jobs, inside the cap of 8 processes, with
`MemAvailable` above 90 GiB throughout (each job stays under 2 GiB).

## Estimate written before the second session's runs (2026-10-21, 22:40 box time)

A second session resumed this hunt after the first stopped (nothing ran in the worktree for
three hours). It added `step2b` (the remaining probe triples of total degree at most 6, through
vectorized D_s = 0 routes) and `crosscheck.py` (the second implementation reproducing every
exact number). Unit timings, from validation runs of this session under a load average of 50
to 110:

| unit | measured time |
|---|---|
| a D_s = 0 triple with D_A = 3, all five routes (direct, Poisson, Euler, and the two vectorized ones) | 1 s to 370 s (the slow routes dominate) |
| one PARI symbol table entry (resultant in GP) | about 10 microseconds |
| one PARI local coefficient by definition, small t | about 10 ms |
| one PARI F(s, A, H) by enumeration, deg T A = 3 | about 3 ms |

Estimates: `step2b` 30 to 60 minutes (the frequency sum of (0,0,5) dominates: about 13,000
indices A against 14,406 frequencies, one symbol table per A); `crosscheck.py` 60 to 120
minutes, dominated by the K check (164,591 tuples, 3 to 4 ms each on each side), the
structural check (319,200 Gauss sums by enumeration) and the n = 4 coefficients of degree 4
(C sums over 371,293 moduli). Both checkpoint per unit (per triple, per item) and run as
single processes at `nice 10`.

## Manifests

Run manifests are appended below as each part ends.

```runmanifest
id: ff_probe-2026-10-21-rival
hunt: ff_probe
started: 2026-10-21T17:40Z
finished: 2026-10-21T17:41Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part rival
outcome: 210 characters modulo T^3 scanned in 16 s; 66 rivals with zeros off the circle; the principal-row local identity fails for the rival first at X^2 and holds for chi to X^3 W
artifacts:
  - hunts/ff_probe/results_rival.json
```

The next four manifests were written by the second session from the results files and their
modification times (box clock); the first session ended before writing them.

```runmanifest
id: ff_probe-2026-10-21-ledger
hunt: ff_probe
started: 2026-10-21T17:40Z
finished: 2026-10-21T17:55Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part ledger
outcome: 890 s; abs(F)^2 = 7 q_A in all 417 generic cases; the largest ratio to the template's bound is 7^(-1/2) over 63,870 nonzero cases; the principal correction stays within 0.199 of 1 on Re x = 7/8; the two balanced probe values agree in their direct and Euler representations
artifacts:
  - hunts/ff_probe/results_ledger.json
```

```runmanifest
id: ff_probe-2026-10-21-step3
hunt: ff_probe
started: 2026-10-21T17:40Z
finished: 2026-10-21T18:01Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part step3
outcome: the n = 4 coefficients over F_13[T]; the final invocation resumed from a complete checkpoint, so the recorded 0.3 s is that invocation only; the census of the 2,028 squarefree cubics and the forced zeros of every component family are in S4.md
artifacts:
  - hunts/ff_probe/results_step3.json
```

```runmanifest
id: ff_probe-2026-10-21-step1
hunt: ff_probe
started: 2026-10-21T17:59Z
finished: 2026-10-21T18:09Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part step1
outcome: 611 s; the cited formulas checked by brute force at q = 7, n = 3 (and n = 6, and q = 13, n = 4 where stated), with the corrections listed in SOURCES.md
artifacts:
  - hunts/ff_probe/results_step1.json
```

```runmanifest
id: ff_probe-2026-10-21-step2
hunt: ff_probe
started: 2026-10-21T17:43Z
finished: 2026-10-21T18:26Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part step2
outcome: 2,582 s; the phase identities, F in three routes, C_p, the separation of K, Lemma 7.1 at 72 (prime, row) cases and the probe at 16 triples, all equal; the five triples on the selection-rule class are nonzero
artifacts:
  - hunts/ff_probe/results_step2.json
```

The next manifest was written on 2026-10-26 by the resuming session, from `results_step2b.json`
and its modification time (box clock); the second session of 2026-10-21 ended before writing it.

```runmanifest
id: ff_probe-2026-10-21-step2b
hunt: ff_probe
started: 2026-10-21T22:24Z
finished: 2026-10-21T22:50Z
ran:
  - .venv/bin/python hunts/ff_probe/ffprobe.py --part step2b
outcome: 1,612.5 s; the remaining probe triples of total degree at most 6 on the selection-rule class; nine have an empty frequency box and a zero direct sum; at the four D_s = 0 triples (0,0,5), (1,0,5), (3,0,5), (4,0,5) the direct, Poisson and Euler representations agree exactly, zero at the first two and nonzero at the last two
artifacts:
  - hunts/ff_probe/results_step2b.json
```

## The crosscheck run (2026-10-26, opened before launch)

Resumed by the owner's decision of 2026-10-26 and pre-approved by the coordinator as one
single-process run. `results_second.partial.json` held 4 of 15 items (symbols, C_routes,
F_routes, C_p) from 2026-10-21; `crosscheck.py` resumes after them. The estimate is the one
above, 60 to 120 minutes on one process, which is under the coordinator's one-core-hour
approval gate at its low end and was approved as written. At launch the 1-minute load
average was 51 and `MemAvailable` 68 GiB.

```runmanifest
id: ff_probe-2026-10-26-crosscheck
hunt: ff_probe
started: 2026-10-26T12:52Z
finished: pending
ran:
  - nice -n 10 .venv/bin/python hunts/ff_probe/crosscheck.py
outcome: pending
artifacts:
  - hunts/ff_probe/results_second.json
```
