# Runs

Environment for the local runs: macOS (Darwin 25.5.0, Apple Silicon), CPython 3.12.12 in
a fresh venv from the archive's `requirements.txt` (`python-flint` 0.9.0, `numpy` 2.5.1,
`scipy` 1.18.0), on the archive `bloch-computations-1.0.0.zip` (sha256
`bdaa1ff3…408e7`, verified; all 28 entries of `CHECKSUMS.sha256` verified). Modal runs use
the same pinned packages on `debian_slim` / CPython 3.12, one physical core per container
(`cpu=1.0`), with the archive's `src/` copied in unchanged. The archive lives in a
gitignored directory outside `hunts/` (`.upstream/bloch/`, fetched by
`fetch_upstream.sh`); nothing from it is vendored here.

Modal runs this code about 2.3x slower per core than the local machine (fixed-radius
ceiling witness 8.9 s vs 3.5 s; `verify --mesh 20` 112 s vs 52 s).

```runmanifest
id: bloch_ceiling-2026-08-23-fetch-and-fixed-radius
hunt: bloch_ceiling
started: 2026-08-23T08:04-05:00
finished: 2026-08-23T08:09-05:00
ran:
  - hunts/bloch_ceiling/fetch_upstream.sh (download, sha256, unzip, CHECKSUMS.sha256)
  - .venv/bin/python src/verify_all.py (archive root, pinned venv)
outcome: the zip's sha256 and all 28 internal checksums match; both fixed-radius certificates verify in under a second and every printed enclosure matches expected-output/verification.md to the last printed digit
artifacts:
  - hunts/bloch_ceiling/fetch_upstream.sh
  - hunts/bloch_ceiling/artifacts/local/bloch-verify-fixed.txt
```

```runmanifest
id: bloch_ceiling-2026-08-23-near-branch-and-mesh
hunt: bloch_ceiling
started: 2026-08-23T08:09-05:00
finished: 2026-08-23T08:11-05:00
ran:
  - .venv/bin/python src/variable_radius_certificate.py verify --mesh 20 (52 s)
  - .venv/bin/python src/certify_fixed_radius_ceiling.py (3.5 s)
outcome: uniform positivity margin +0.000936855231, near moment slope margin 0.0331790701855, near centre 0.136904745959 < 0.436558987993, near moment gain 0.0153040536989472, 20x20 mesh away minimum 0.015866072532 in sectors 6 and 18, MESH RESULT PASS > 0.0153; fixed-radius ceiling witness 0.01519720970909415 < 0.0152 with 53302 annulus boxes (33051 terminal); all match the archive's expected output and VARIABLE_RADIUS_FINDINGS.md
artifacts:
  - hunts/bloch_ceiling/artifacts/local/bloch-verify-mesh20.txt
  - hunts/bloch_ceiling/artifacts/local/bloch-ceiling-witness.txt
```

```runmanifest
id: bloch_ceiling-2026-08-23-modal-quick
hunt: bloch_ceiling
started: 2026-08-23T08:14-05:00
finished: 2026-08-23T08:18-05:00
ran:
  - .venv/bin/modal run hunts/bloch_ceiling/modal_reproduce.py::quick
  - .venv/bin/modal run hunts/bloch_ceiling/modal_reproduce.py::collect
  - python hunts/bloch_ceiling/compare_expected.py
outcome: the four sub-minute programs rerun in a Modal container give the same 22 statistics as the local run and as expected-output/verification.md (compare_expected.py, 22 of 22 match); the only textual difference is the twelfth decimal of the mesh minimum, which the findings file quotes rounded
artifacts:
  - hunts/bloch_ceiling/modal_reproduce.py
  - hunts/bloch_ceiling/compare_expected.py
  - hunts/bloch_ceiling/artifacts/modal-reproduce.json
```
