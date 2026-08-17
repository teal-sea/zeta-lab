# RUNS — run manifests for the rogue_frontier hunt

```runmanifest
id: rogue_frontier-2026-08-17-campaign1
hunt: rogue_frontier
started: 2026-08-17T01:15Z
finished: 2026-08-17T09:30Z
ran:
  - scripts/science_preflight.py equivalent checks (venv build, Arb backend, fast tier 2504 passed)
  - an 11-way parallel literature survey (166 entries, 87 candidates, data/frontier_surveys.json)
  - hunts/rogue_frontier/sine_gram/ exact engines and Monte Carlo controls
  - hunts/rogue_frontier/window_opt/ optimization, enclosures, and a blinded re-derivation
  - hunts/rogue_frontier/weil_trunc/ replication, enclosures, Davenport-Heilbronn control
  - hunts/rogue_frontier/fkappa/ literal port, audit, corrected table, closed form
  - hunts/rogue_frontier/nyman_beurling/ Vasyunin pipeline and distance ladder
outcome: five studies delivered (one promoted, RH-conditional; one audit with exact witnesses; two hardened instrument sets; one partial), three sessions ended early by a session token limit with all state checkpointed
artifacts:
  - hunts/rogue_frontier/RESULTS_LEDGER.md
  - hunts/rogue_frontier/FAILURE_LEDGER.md
  - hunts/rogue_frontier/REPRODUCE.md
  - hunts/rogue_frontier/data/frontier_surveys.json
  - hunts/rogue_frontier/REPORT.md
```

```runmanifest
id: rogue_frontier-2026-08-17-campaign2
hunt: rogue_frontier
started: 2026-08-17T10:00Z
finished: 2026-08-17T13:30Z
ran:
  - salvage of first-wave checkpoints (window verification replayed, ledgers closed)
  - inline exact control of Bian (11.5) against published and corrected tables
  - FK-THEORY arm (resolvent collapse, Gevrey tail, rows to i = 81)
  - FK-DATA arm (independent extension to i = 40 and 28, structure guessing)
  - DH-NEG arm (first rival positivity-failure cell, enclosure package)
  - WIN-GLOBAL arm (landscape, exact quartic slice, outer bound)
outcome: RF-C007 and RF-C009 delivered, RF-C008 promoted on a two-engine exact cross-check, RF-C003 caveat upgraded to a two-sided exact bracket; issue #57 opened for the rival observation
artifacts:
  - hunts/rogue_frontier/fkappa/theory_notes.md
  - hunts/rogue_frontier/fkappa/coefficients_ext.json
  - hunts/rogue_frontier/weil_trunc/dhneg_scan.json
  - hunts/rogue_frontier/window_opt/global_notes.md
  - hunts/rogue_frontier/REPORT.md
```
