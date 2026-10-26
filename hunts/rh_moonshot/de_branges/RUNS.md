# RUNS: de_branges (hunt #150, mechanism 2)

Single-process Python on the campaign box (`<box>`), commands from the repository root with
`.venv/bin/python`, at `nice 10`, at most four processes of this session alive at once.
Times are UTC from the session clock.

## Estimate written before the grid runs (2026-10-26)

Timed units (one defect evaluation, both routes, at h = 1/4 and 1/2, heights 50 and 95):
mp route 5 to 12 ms for zeta, W_{1/4} and zeta(s - 1/5), 76 ms for DH (after a 0.45 s first
call), and 12 to 18 s for Epstein (1,1,6) by the lattice route at heights 16 to 30 (40 to
83 s at heights 50 to 95, which is why the Epstein grid stops at x = 40 and its mp route
runs on every 16th point); Arb route 1 to 3 ms, 10 to 70 ms for Epstein with the precision
raised to 160 + 3x bits (at 160 bits flat it returned NaN at height 95).
Per kind the grid is 7 values of h, 2 of y and 203 (Epstein 83) values of x, about 2840
(1160) points, plus 120 Arb column points per h. Estimate: zeta, W_{1/4}, zeta(s - 1/5)
about 30 s each, DH about 4 minutes, Epstein about 30 to 40 minutes (112 mp points);
about 45 minutes of one core in all, under one core-hour, so it runs without asking.

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-units
hunt: rh_moonshot
started: 2026-10-26T13:20Z
finished: 2026-10-26T13:34Z
ran:
  - .venv/bin/python -c (dbr_common.conrey_li_numbers, conrey_li_numbers_arb, defect_mp and defect_arb for each kind at (h, x, y) = (1/4, 50.3, 0.1), (1/2, 95.1, 0.05); Epstein's Arb route at 160 and 160 + 3x bits)
outcome: Conrey and Li's -5.389100507182945e-69 and -0.000131957 reproduced by both routes; the timings of the estimate above; Epstein's Arb route returns NaN at height 95 at 160 bits and agrees with the lattice route at 160 + 3x bits
artifacts:
```

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-grid-zeta
hunt: rh_moonshot
started: 2026-10-26T13:36Z
finished: 2026-10-26T13:36Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py zeta > hunts/rh_moonshot/de_branges/data/log_grid_zeta.txt
outcome: 16 s; 2828 points, the defect negative at every one by the Arb route (one undecided ball, the removable point s = 1) with the mp route agreeing to 4.3e-11 (a first run 12 s earlier, identical, was rerun only because its log had no directory to go to)
artifacts:
  - hunts/rh_moonshot/de_branges/data/grid_zeta.json
  - hunts/rh_moonshot/de_branges/data/log_grid_zeta.txt
```

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-grid-dh-wa-zshift
hunt: rh_moonshot
started: 2026-10-26T13:36Z
finished: 2026-10-26T13:38Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py dh > hunts/rh_moonshot/de_branges/data/log_grid_dh.txt
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py wa zshift > hunts/rh_moonshot/de_branges/data/log_grid_wa_zshift.txt
outcome: 155 s (DH), 34 s (W_{1/4}) and 18 s (zeta(s - 1/5)) for 2842 points each; DH positive only at x = 85.5 and 85.699 for h <= 3/10, W_{1/4} positive at zeta ordinates for h <= 1/5 and nowhere at h = 1/4, zeta(s - 1/5) positive everywhere for h <= 1/10; routes agree to 1.6e-11
artifacts:
  - hunts/rh_moonshot/de_branges/data/grid_dh.json
  - hunts/rh_moonshot/de_branges/data/grid_wa.json
  - hunts/rh_moonshot/de_branges/data/grid_zshift.json
  - hunts/rh_moonshot/de_branges/data/log_grid_dh.txt
  - hunts/rh_moonshot/de_branges/data/log_grid_wa_zshift.txt
```

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-grid-epstein
hunt: rh_moonshot
started: 2026-10-26T13:36Z
finished: 2026-10-26T14:10Z
ran:
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py epstein > hunts/rh_moonshot/de_branges/data/log_grid_epstein_part1.txt (h = 1/2 and 3/8 in 471 s, then a ZeroDivisionError at s = 1 in the lattice route; paths in the traceback made repo-relative)
  - the same command restarted at 13:49Z after a wrong limit at s = 1 was found and corrected, stopped within a minute (no output kept)
  - nice -n 10 .venv/bin/python hunts/rh_moonshot/de_branges/dbr_grid.py epstein > hunts/rh_moonshot/de_branges/data/log_grid_epstein.txt (from 13:51Z, with the circle mean at s = 0 and 1; resumed at h = 3/10)
outcome: 1618 s of grid for 7 values of h, 166 points each with 16 by the lattice route, inside the 30 to 40 minute estimate; positive at x = 16.290 for h <= 3/8 and at x = 29.5 for h <= 1/4, routes agreeing to 4.7e-12
artifacts:
  - hunts/rh_moonshot/de_branges/data/grid_epstein.json
  - hunts/rh_moonshot/de_branges/data/log_grid_epstein_part1.txt
  - hunts/rh_moonshot/de_branges/data/log_grid_epstein.txt
```

```runmanifest
id: rh_moonshot-de_branges-2026-10-26-epstein-zero
hunt: rh_moonshot
started: 2026-10-26T14:11Z
finished: 2026-10-26T14:12Z
ran:
  - nice -n 10 .venv/bin/python -c (mp.findroot on the Arb route of s(s-1) Lambda_Q near 0.77 + 29.5i; the lattice route at the root and at the root + 0.01)
outcome: a zero at 0.797997157178680 + 29.551761098629115i, offset 0.2980, with the lattice route at 9e-47 against 1.3e-18 nearby; the pinned zero at 16.29 refound to 15 digits
artifacts:
```
