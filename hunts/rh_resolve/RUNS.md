# RUNS: rh_resolve

```runmanifest
id: rh_resolve-2026-10-03-phase1
hunt: rh_resolve
started: 2026-10-03T00:00-05:00
finished: 2026-10-03T01:00-05:00
ran:
  - .venv/bin/python hunts/rh_resolve/probe_phase1.py
  - .venv/bin/python -c "zeta.epstein.battery constant-True check"
  - .venv/bin/python -c "zeta.li.hyperbolicity_scan(4, 2, dps=20)"
outcome: three lanes measured healthy with no violation and no support, Li Cauchy chosen for phase 2 enclosures
artifacts:
  - hunts/rh_resolve/probe_phase1.py
  - hunts/rh_resolve/results_phase1.json
  - hunts/rh_resolve/RESULTS.md
  - hunts/rh_resolve/MISSION.md
```

```runmanifest
id: rh_resolve-2026-10-03-phase2
hunt: rh_resolve
started: 2026-10-03T01:00-05:00
finished: 2026-10-03T03:00-05:00
ran:
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmax 1 --K 4096 --prec 128
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmax 1 --K 32768 --prec 128
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmax 3 --K 32768 --prec 128
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmax 2 --K 32768 --prec 192
  - branch soundness panel check (min Re(xi) lower 0.4951, max arg upper 0.0329)
  - closed-form cross-check for lambda_1 via arb constants
outcome: lambda_1 to lambda_3 positivity decided by enclosure, branch proved, precisions overlap
artifacts:
  - hunts/rh_resolve/enclose_li.py
  - hunts/rh_resolve/enclosure_li_K4096_p128.json
  - hunts/rh_resolve/enclosure_li_K32768_p128.json
  - hunts/rh_resolve/enclosure_li_K32768_p192.json
```
