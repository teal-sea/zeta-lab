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

```runmanifest
id: rh_resolve-2026-10-03-phase4
hunt: rh_resolve
started: 2026-10-03T05:00-05:00
finished: 2026-10-03T08:00-05:00
ran:
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 1 --nmax 32 --K 16384 --R 0.7 --rho 0.85
  - M-bound probes at rho 0.9, 0.88, 0.85 selecting rho 0.88 with K0 16384
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 33 --nmax 48 --K 65536 --R 0.8 --rho 0.88
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 49 --nmax 64 --K 65536 --R 0.8 --rho 0.88
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 65 --nmax 72 --K 65536 --R 0.8 --rho 0.88
  - re-ran 33-48 under range-stamped filename after overwrite, mechanical 1-71 coverage check
outcome: positivity enclosed for every n 1 to 71, n 72 mapped as the boundary at this K
artifacts:
  - hunts/rh_resolve/enclose_li_mid.py
  - hunts/rh_resolve/enclosure_mid_R0.7_K16384_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n33-48_K65536_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n49-64_K65536_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n65-68_K65536_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n69-70_K65536_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n71-72_K65536_p128.json
```

```runmanifest
id: rh_resolve-2026-10-03-correction
hunt: rh_resolve
started: 2026-10-03T09:00-05:00
finished: 2026-10-03T12:00-05:00
ran:
  - re-derivation of midpoint remainder found missing oscillation terms
  - fixed G2 in enclose_li_mid.py, moved six invalid files to superseded/ unmodified
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 1 --nmax 16 --K 16384 --R 0.7
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 17 --nmax 40 --K 65536 --R 0.8
  - .venv/bin/python hunts/rh_resolve/enclose_li_mid.py --nmin 41 --nmax 60 --K 65536 --R 0.8
  - mechanical coverage check 1-58 plus float cross-check, both clean
outcome: corrected theorem certifies n 1 to 58 with n 59 as boundary, error preserved in superseded
artifacts:
  - hunts/rh_resolve/enclose_li_mid.py
  - hunts/rh_resolve/superseded/CORRECTION.md
  - hunts/rh_resolve/enclosure_mid_R0.7_n1-16_K16384_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n17-40_K65536_p128.json
  - hunts/rh_resolve/enclosure_mid_R0.8_n41-60_K65536_p128.json
  - hunts/rh_resolve/THEOREM.md
```

```runmanifest
id: rh_resolve-2026-10-03-rival
hunt: rh_resolve
started: 2026-10-03T08:00-05:00
finished: 2026-10-03T09:00-05:00
ran:
  - .venv/bin/python hunts/rh_resolve/probe_rival.py
outcome: both zero sides positive at all widths, control powerless by construction, Weil-distinguishing lane closed
artifacts:
  - hunts/rh_resolve/probe_rival.py
  - hunts/rh_resolve/rival_weil.json
```
