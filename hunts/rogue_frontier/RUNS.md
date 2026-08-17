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
