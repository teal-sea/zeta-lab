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

```runmanifest
id: f1_engine_controls-2026-10-21-landing
hunt: f1_engine_controls
started: 2026-10-21T15:49Z
finished: 2026-10-21T16:37Z
ran:
  - .venv/bin/python hunts/f1_engine_controls/gauntlet.py --json hunts/f1_engine_controls/results_gauntlet.json
  - .venv/bin/python hunts/f1_engine_controls/gauntlet.py --json <scratch>/results_gauntlet.json, then compared with the committed file
  - .venv/bin/python hunts/f1_engine_controls/ln2_law.py --max-n 800 --json <scratch>/results_ln2.json, then compared with the committed file
  - .venv/bin/python hunts/f1_engine_controls/density.py --sizes 100,200,400,800,1200 --json <scratch>/results_density.json, then compared with the committed file
  - .venv/bin/python -m pytest -q -n0 -p no:cacheprovider tests/test_f1_engine_controls.py tests/test_docs_paths.py
outcome: re-measured at landing against main, whose battery now carries the shifted-product rival W_a. The predicate rejects the three linear-combination rivals (shift=None) and shares its verdict with W_a on the default battery, so gauntlet.py now records both readings and results_gauntlet.json was regenerated; a second run reproduced it byte for byte. ln2_law.py with --max-n 800 reproduced the committed results_ln2.json byte for byte, so that artifact came from --max-n 800 and not the --max-n 400 the opening manifest records. density.py reproduced every count in results_density.json, with float values differing by at most 1.7e-14 relative. 34 tests passed.
artifacts:
  - hunts/f1_engine_controls/results_gauntlet.json
  - tests/test_f1_engine_controls.py
  - tests/test_docs_paths.py
```
