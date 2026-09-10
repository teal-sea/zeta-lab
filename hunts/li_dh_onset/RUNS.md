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
  - hunts/li_dh_onset/artifacts/samples_dh_r0.9_N5112_w142.json
```
