# RUNS: probe_tower (hunt #150, mechanism 6)

All runs were single-process Python on the campaign box, started at `nice 10`, with at
most two processes of this session alive at once and the 1-minute load average between
37 and 65 while they ran (other sessions' work). Start and finish times are UTC, read
from the session's clock and the scratch files' modification times, to the minute.

Estimate written before the rival scans: one evaluation of L(s, chi) for the mod-5
character at height about 100 took 0.03 to 0.07 s at 10 to 25 digits (measured, ten
calls each), so a scan of 1197 points with two evaluations each was estimated at 70 to
170 s; each took 172 to 193 s.

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-exact
hunt: rh_moonshot
started: 2026-10-21T22:00Z
finished: 2026-10-21T22:34Z
ran:
  - .venv/bin/python -c (import tower_template; verify_citations, the k = 6 reproduction, walls and prices for k = 2..12, symbolic_checks)
  - .venv/bin/python hunts/rh_moonshot/probe_tower/tower_template.py --paper --no-rivals
  - .venv/bin/python -m pytest -q -n0 -m "not slow" hunts/rh_moonshot/probe_tower/test_probe_tower.py
outcome: the order-k template rebuilds every cited constant at k = 6; walls, dual multipliers and prices of 1/2 equal their closed forms for every k checked; 49 of 49 citations sit on their lines; 22 fast tests pass
artifacts:
  - hunts/rh_moonshot/probe_tower/tower_template.py
  - hunts/rh_moonshot/probe_tower/test_probe_tower.py
```

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-rivals
hunt: rh_moonshot
started: 2026-10-21T22:12Z
finished: 2026-10-21T22:31Z
ran:
  - .venv/bin/python -c (dh_at_offline_zero, dh_moebius_sum_check, dh_contraction_scan on Re s = 7/8 for t in [80, 90])
  - .venv/bin/python -c (wa_at_offline_zero, wa_moebius_sum_check, epstein_at_offline_zero)
outcome: DH and Epstein (1,1,6) fail the principal-row reciprocal step at their off-line zeros with H = 0 there and finite probe-visible reciprocals; W_a passes it at its zero 3/4 + 14.1347i with |H_W - 1| = 0.236 and nothing deleted
artifacts:
```

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-dh-scans
hunt: rh_moonshot
started: 2026-10-21T22:17Z
finished: 2026-10-21T22:27Z
ran:
  - .venv/bin/python -c (dh_contraction_scan(0.875, 1, 300, 0.25, delete_upto=S, dps=12) for S = 1, 3, 100), output to the session scratch directory
outcome: on Re s = 7/8 for t in [1, 300], max |H - 1| is 3.68 with nothing deleted (572 of 1197 points above 1/2), 0.276 with the primes 2 and 3 deleted and 0.018 with the primes up to 100 deleted (no point above 1/2 in either)
artifacts:
```

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-literature
hunt: rh_moonshot
started: 2026-10-21T22:15Z
finished: 2026-10-21T22:20Z
ran:
  - WebFetch of the arXiv abstract page of 1112.1650 (Blomer, Goldmakher, Louvel)
  - curl of the arXiv e-print of 1112.1650 into the session scratch directory, read as data
  - WebSearch and WebFetch of the arXiv abstract page of 0807.0783 (Saias, Weingartner)
outcome: Theorem 1.3 of 1112.1650 read in its TeX source (sha256 bd846eb6f570c40cc2b571595260cdd250c633f337c88c33e261e95f7979a6cb), the same M + N + (MN)^(2/3) for every n >= 3; the Saias-Weingartner strip theorem read in its abstract
artifacts:
```

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-report
hunt: rh_moonshot
started: 2026-10-21T22:34Z
finished: 2026-10-21T22:42Z
ran:
  - .venv/bin/python hunts/rh_moonshot/probe_tower/tower_template.py --paper --write
outcome: the report reproduced every number of the exploratory runs exactly (49 of 49 citations found, all symbolic identities true, the three 7/8-line scans at 3.68, 0.276 and 0.018, the three rival zeros as before); an earlier launch at 22:28Z was stopped because it had loaded the code before its last edits
artifacts:
  - hunts/rh_moonshot/probe_tower/results_probe_tower.json
```

```runmanifest
id: rh_moonshot-probe_tower-2026-10-21-tests
hunt: rh_moonshot
started: 2026-10-21T22:35Z
finished: 2026-10-21T22:44Z
ran:
  - .venv/bin/python -m pytest -q -n0 -m slow hunts/rh_moonshot/probe_tower/test_probe_tower.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/probe_tower/test_probe_tower.py
  - .venv/bin/python -m pytest -q -n0 tests/test_hunt_probe_discipline.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_doors.py -m "not slow"
  - .venv/bin/python scripts/make_context.py --check
outcome: 29 of 29 probe_tower tests pass (23 fast, 6 slow, 38 s); the repository's hunt-discipline, huntspec, docs-numbering and doors tests pass in their fast tier, and CONTEXT.md is up to date
artifacts:
```
