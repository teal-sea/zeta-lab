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

```runmanifest
id: rh_resolve-2026-10-03-phase3
hunt: rh_resolve
started: 2026-10-03T03:00-05:00
finished: 2026-10-03T05:00-05:00
ran:
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmax 5 --K 131072 --prec 128
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmin 6 --nmax 10 --K 131072 --prec 128 --R 0.3
  - .venv/bin/python hunts/rh_resolve/enclose_li.py --nmin 6 --nmax 10 --K 131072 --prec 128 --R 0.7
  - branch soundness panel check at R 0.7 (min Re lower 0.4869, max arg upper 0.1192)
  - Li positivity scan to n 100 and Jensen scan d 16 n 25 (disproof search, both empty)
outcome: positivity enclosed for n 1 to 10, disproof search to n 100 and 416 Jensen rows found no violation
artifacts:
  - hunts/rh_resolve/enclosure_li_K131072_p128.json
  - hunts/rh_resolve/enclosure_li_R0.3_K131072_p128.json
  - hunts/rh_resolve/enclosure_li_R0.7_K131072_p128.json
  - hunts/rh_resolve/disproof_li100.json
  - hunts/rh_resolve/disproof_jensen16x25.json
```
