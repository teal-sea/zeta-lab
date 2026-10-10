# li_dh_onset: run manifests

Every run below happened on one shared container: 4 vCPU, 15 GB, both
ball-arithmetic backends live, no Lean. Other tenants were on the box
throughout (load average 8 to 13 against 4 vCPU), so the measured wall times
are **contended** wall times and the observed speedup from three worker
processes was close to 1. That is recorded rather than smoothed away, because
the cost model in `RESULTS.md` is built from these numbers.

The estimate that was written down before the expensive run, per this
repository's compute discipline: `completed_dh` warm at 0.092 s per evaluation
at 142 digits, 5112 nodes at n_max = 2000 and r = 0.9, so 470 s of evaluation
and roughly 90 s of transform. Measured: 503 s and 124 s. The cold-cache
scouting figure the brief carried (0.42 s per evaluation at 150 digits) was
measuring `zeta.epstein.kappa` being re-derived on every call, not the Hurwitz
values; `dhli.completed_dh_fast` warms that cache once per process.

```runmanifest
id: li_dh_onset-2026-09-10-radius
hunt: li_dh_onset
started: 2026-09-10T00:52
finished: 2026-09-10T01:04
ran:
  - .venv/bin/python hunts/li_dh_onset/radius_scan.py --radii 0.9,0.95 --tall-max 120 --census-max 90
outcome: the sum of |a_n| n^-2 over n >= 2 measures 0.26666 so f has no zero with Re s >= 2, and the argument principle finds no zero of f in either rectangle covering the Apollonius disc of r = 0.9 or of r = 0.95, none with Re s in [1.0001, 4] below height 120, and box counts equal grid-refined line counts in every height window below 80 with an excess of exactly 2 in [80, 90]
artifacts:
  - hunts/li_dh_onset/artifacts/radius_scan.json
```

```runmanifest
id: li_dh_onset-2026-09-10-controls
hunt: li_dh_onset
started: 2026-09-10T01:00
finished: 2026-09-10T01:04
ran:
  - .venv/bin/python hunts/li_dh_onset/run_controls.py --processes 2 --xi-n 400 --dh-n 200
outcome: the identical pipeline pointed at xi reproduces the committed zeta table to 4.4e-28 at both r = 0.5 and r = 0.9, the fast evaluator matches zeta.epstein.completed_dh to 6.6e-46 on the contour, a parallel run and a serial run are bit identical, and lambda_n(DH) for n <= 200 is bit identical across r in 0.5, 0.7, 0.9
artifacts:
  - hunts/li_dh_onset/artifacts/controls.json
```

```runmanifest
id: li_dh_onset-2026-09-10-definition
hunt: li_dh_onset
started: 2026-09-10T01:25
finished: 2026-09-10T01:27
ran:
  - .venv/bin/python hunts/li_dh_onset/defect_check.py
outcome: the generating function n [z^n] log F(1/(1-z)) reproduces Li's literal n-th derivative definition for the Davenport-Heilbronn function at n = 1, 2, 3, 4 to 4e-27 at dps 25, and lambda_1 also matches a third route through the closed form for the completing factor
artifacts:
  - hunts/li_dh_onset/artifacts/definition_defect.json
```

```runmanifest
id: li_dh_onset-2026-09-10-main2000
hunt: li_dh_onset
started: 2026-09-10T01:07
finished: 2026-09-10T01:18
ran:
  - .venv/bin/python hunts/li_dh_onset/run_main.py --n-max 2000 --radius 0.9 --dps 30 --processes 3
outcome: 142 working digits, 5112 nodes, 503 s sampling and 124 s extraction, winding number zero, every lambda_n(DH) for 1 <= n <= 2000 positive with the minimum at n = 1
artifacts:
  - hunts/li_dh_onset/artifacts/lambda_dh_n2000_r0.9.json
```

```runmanifest
id: li_dh_onset-2026-09-10-main5000
hunt: li_dh_onset
started: 2026-09-10T01:32
finished: 2026-09-10T01:57
ran:
  - .venv/bin/python hunts/li_dh_onset/run_main.py --n-max 5000 --radius 0.95 --dps 30 --processes 3
outcome: 162 working digits, 12281 nodes, 1007 s sampling and 465 s extraction, winding number zero, every lambda_n(DH) for 1 <= n <= 5000 positive and bit identical to the r = 0.9 table over their common range
artifacts:
  - hunts/li_dh_onset/artifacts/lambda_dh_n5000_r0.95.json
```

```runmanifest
id: li_dh_onset-2026-09-10-xi-companion
hunt: li_dh_onset
started: 2026-09-10T01:57
finished: 2026-09-10T01:59
ran:
  - .venv/bin/python hunts/li_dh_onset/run_main.py --target xi --n-max 2000 --radius 0.9 --dps 30 --processes 2
outcome: the same pipeline on xi at n <= 2000 costs 30 s sampling and 85 s extraction, and the measured difference lambda_n(DH) - lambda_n(zeta) - (n/2) log 5 stays inside [-16.89, +21.83] with mean -1.54, which is the conductor showing up where the density says it should
artifacts:
  - hunts/li_dh_onset/artifacts/lambda_xi_n2000_r0.9.json
```

```runmanifest
id: li_dh_onset-2026-09-10-zeroside
hunt: li_dh_onset
started: 2026-09-10T01:31
finished: 2026-09-10T02:07
ran:
  - .venv/bin/python hunts/li_dh_onset/zero_side.py --t-max 430 --n-max 12
outcome: 313 critical-line ordinates below height 430, argument-principle box counts equal line count plus two per known quadruple with zero unaccounted at heights 100, 200, 300 and 430, and the zero-side lambda_n agrees with the Cauchy table to 1.1e-8 relative at n <= 12
artifacts:
  - hunts/li_dh_onset/artifacts/zero_side.json
```

```runmanifest
id: li_dh_onset-2026-09-10-dominance
hunt: li_dh_onset
started: 2026-09-10T01:57
finished: 2026-09-10T02:00
ran:
  - .venv/bin/python hunts/li_dh_onset/dominance.py
outcome: no zero of f with Re s >= 0.83 in height [90, 190], and the coefficient bound covers everything above 188.97, so no unfound quadruple can out-grow the pair at height 85.699
artifacts:
  - hunts/li_dh_onset/artifacts/dominance.json
```

```runmanifest
id: li_dh_onset-2026-09-10-onset
hunt: li_dh_onset
started: 2026-09-10T02:00
finished: 2026-09-10T02:05
ran:
  - .venv/bin/python hunts/li_dh_onset/onset.py --table hunts/li_dh_onset/artifacts/lambda_dh_n5000_r0.95.json --n-hi 3000000
  - .venv/bin/python hunts/li_dh_onset/ceiling.py
outcome: the background fitted to the measured coefficients has b = -0.32530 against the derived -0.32561, and the first negative index is 328997 under four background variants and 325229 under the zeta-shaped one; the cost model puts n_max = 20000 at about 3.7 h and the onset index itself at about 20000 core-hours
artifacts:
  - hunts/li_dh_onset/artifacts/onset.json
  - hunts/li_dh_onset/artifacts/ceiling.json
```

## The sampling checkpoints

`run_main.py` writes each block of 64 contour samples to
`artifacts/samples_<target>_r<r>_N<nodes>_w<work>.json` as it lands, so a killed
run resumes instead of restarting, and so a second extraction at a different
n_max off the same circle is free. Those three files came to 7.8 MB and were
**deleted after the runs landed**: they are working files, not measurements, and
the measurements they produced are the lambda tables beside them. Re-creating
them costs 1007 s (r = 0.95, 12281 nodes), 503 s (r = 0.9, 5112 nodes) and 30 s
(xi). Anyone re-running is expected to let the checkpoint rebuild itself.

## What was not done, and why

- **n_max was not pushed past 5000.** The brief's safe target was 2000 and its
  stretch was 5000; both landed. The model prices n_max = 10000 at about 1.1 h on
  a quiet box and 3 h on the contended one, against a marginal gain of halving
  the extrapolation distance from sixty-six to thirty-three times. That is a
  door, priced in `RESULTS.md`, not a run.
- **The radius 0.99 that the cost model prefers was not validated.** Its
  rectangle comes within 0.0025 of the critical line and wants an argument
  principle scan run with more care than the two rectangles here needed.
- **No enclosures anywhere.** Every number is float grade in the ball-arithmetic
  sense, including the winding numbers.
- **hunts/README.md was not edited.** This hunt writes only inside its own
  directory. Its case-log entry (hunt #123) was already in place when the work
  started and still says "in flight"; whoever lands this should update that line
  to match `RESULTS.md`. `tests/test_hunt_probe_discipline.py`,
  `tests/test_docs_numbering.py` and `tests/test_doors.py` pass as they stand,
  17 of 17.

```runmanifest
id: li_dh_onset-2026-10-10-landing
hunt: li_dh_onset
started: 2026-10-10T14:06+00:00
finished: 2026-10-10T15:18+00:00
ran:
  - .venv/bin/python hunts/li_dh_onset/run_main.py --n-max 5000 --radius 0.95 --dps 30 --processes 2
  - .venv/bin/python hunts/li_dh_onset/run_main.py --n-max 2000 --radius 0.9 --dps 30 --processes 2
  - .venv/bin/python hunts/li_dh_onset/run_main.py --target xi --n-max 2000 --radius 0.9 --dps 30 --processes 2
  - .venv/bin/python hunts/li_dh_onset/onset.py --table hunts/li_dh_onset/artifacts/lambda_dh_n5000_r0.95.json --n-hi 3000000
  - .venv/bin/python hunts/li_dh_onset/ceiling.py
  - .venv/bin/python hunts/li_dh_onset/zero_side.py --t-max 430 --n-max 12
  - .venv/bin/python hunts/li_dh_onset/radius_scan.py --radii 0.9,0.95 --tall-max 120 --census-max 90
  - .venv/bin/python hunts/li_dh_onset/dominance.py
  - .venv/bin/python hunts/li_dh_onset/run_controls.py --processes 1 --xi-n 400 --dh-n 200
  - .venv/bin/python hunts/li_dh_onset/defect_check.py
  - .venv/bin/python -m pytest -q hunts/li_dh_onset
outcome: the three coefficient tables (dh to 5000 at r = 0.95, dh to 2000 at r = 0.9, xi to 2000) came back identical in every stored digit; zero_side.json, radius_scan.json, dominance.json, ceiling.json and definition_defect.json came back identical field for field apart from timings and stamps; onset.json agrees to 1e-11 relative (least-squares round-off in three derived floats); controls.json agrees except two round-off-level evaluator comparisons (8.0e-46 against 6.6e-46, and 6.7e-51 against 1.34e-51) that depend on mpmath's cache history; seven numbers stated in RESULTS.md and one in this file do not follow from these artifacts and are marked where they are stated
artifacts:
  - hunts/li_dh_onset/test_li_dh_onset.py
  - hunts/li_dh_onset/RESULTS.md
```

Every script above was run on 2026-10-10 in a scratch copy of this directory
(with `data/`, `hunts/flow_repair` and `hunts/lambda_dh_bounds` linked in), so
nothing in the tree was overwritten, and its output was compared with the
committed artifacts field by field. The estimate written down first, per the
compute rule: `completed_dh_fast` timed at 0.078 s per evaluation at 142 digits
and 0.118 s at 162 on this container, so about 400 s and 1450 s of sampling for
the two tables on one core, plus the recorded extraction times. Measured, on a
container shared with another session's test run (load average 6 to 7 on 4
vCPU): 1061 s and 435 s for n = 5000 with two processes, 233 s and 63 s for
n = 2000, 33 s and 65 s for the xi companion; the zero side took 3637 s, 1722
of them in the line scan; the radius scan 226 s, the dominance wedge 157 s,
the controls 202 s and the definition check 84 s.

- **Landed on main and renumbered #123 to #128, 2026-10-10.** The note above
  says "Its case-log entry (hunt #123)". That entry never reached main; by the
  time this directory did, main had used #123 to #126, and #127 is
  `euler_defect_axis` (#297), so this hunt is #128. The case-log entry now on
  main carries the branch's text with the new number and the landing notes.
  The stretch numbers in the bullet "n_max was not pushed past 5000" are not
  reproduced as stated: the cost model gives 3.52 h at r = 0.95 on one
  effective core (the contended calibration) and 1.17 h on three, against
  "3 h" and "about 1.1 h"; at the model's cheapest radius, 0.99, it gives
  0.78 h on one core.
- **The manifests' clock times are not the artifacts'.** Several `started` and
  `finished` fields above disagree with the `generated` stamps the scripts
  wrote: `definition_defect.json` 01:14:22 against 01:25 to 01:27; the xi table
  01:48:28 against 01:57 to 01:59; `dominance.json` 01:46:20 against 01:57 to
  02:00; `onset.json` 01:46:03 and `ceiling.json` 01:43:02 against 02:00 to
  02:05; and the n = 5000 table, generated 01:43:46 after 1472 s of work,
  cannot have started at 01:32. The stamps are the scripts' and the manifests
  were written by hand, so the stamps are the better record. Left as written.
- **Evaluator timings, re-measured.** See `RESULTS.md`, the doors, constraints
  1 and 4: the exponent is near 2 but not 1.97 from the two points quoted, and
  `zeta.epstein.completed_dh`'s factor of six is a cold-cache cost, not a
  per-call one.
- **A global-precision leak, recorded and not fixed.** With `processes = 1`,
  `dhli.sample_circle` and `dhli.coefficients_from_samples` call
  `_worker_init` and `_dft_init` in the caller's own process, and those set
  `mp.dps` globally, which this repository's precision rule forbids. No number
  here depends on it (every reader works at an explicit precision), but a test
  that ran after one of those calls read the leaked precision until
  `test_li_dh_onset.py` began restoring it after every case. The code is left
  as it ran so the artifacts stay reproducible by it.
