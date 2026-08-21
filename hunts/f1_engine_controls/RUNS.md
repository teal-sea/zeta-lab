# RUNS: `f1_engine_controls`

```runmanifest
id: f1_engine_controls-2026-08-21-open
hunt: f1_engine_controls
started: 2026-08-21T03:20Z
finished: 2026-08-21T15:50Z
ran:
  - .venv/bin/python hunts/f1_engine_controls/ln2_law.py --max-n 400 --json hunts/f1_engine_controls/results_ln2.json
  - .venv/bin/python hunts/f1_engine_controls/density.py --sizes 100,200,400,800,1200 --json hunts/f1_engine_controls/results_density.json
  - .venv/bin/python hunts/f1_engine_controls/gauntlet.py --json hunts/f1_engine_controls/results_gauntlet.json
  - .venv/bin/python -m pytest -q tests/test_f1_engine_controls.py tests/test_docs_paths.py
outcome: three of the five docs/15 Reality Check critiques were measured; one held, one was replaced by a wider law that it undercounts from N = 338, and one was found to be aimed at the operator while the criticism it makes is false of the predicate.
artifacts:
  - hunts/f1_engine_controls/results_ln2.json
  - hunts/f1_engine_controls/results_density.json
  - hunts/f1_engine_controls/results_gauntlet.json
  - hunts/f1_engine_controls/RESULTS.md
  - tests/test_f1_engine_controls.py
  - tests/test_docs_paths.py
```
