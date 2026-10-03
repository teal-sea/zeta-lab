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
