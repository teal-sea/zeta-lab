# RUNS: positivity_geometry (hunt #150, mechanism 4)

Kept in this directory rather than in a hunt-level file, because six sessions share one
worktree and a shared file invites lost writes. Validated by
`test_positivity_geometry.py::test_run_manifests_validate` with the parser of
`tests/test_huntspec.py`.

Estimate before spending (`CLAUDE.md` compute rule 3): one brute-force count over
F_{13^4} (28561 elements) takes about 0.4 s and the whole exploration about 15 s on one
process, so nothing here needed a checkpoint or a detached job.

```runmanifest
id: rh_moonshot-positivity_geometry-2026-10-21-construct
hunt: rh_moonshot
started: 2026-10-21T21:40+00:00
finished: 2026-10-21T22:32+00:00
ran:
  - .venv/bin/python hunts/rh_moonshot/positivity_geometry/explore.py curves
  - .venv/bin/python hunts/rh_moonshot/positivity_geometry/explore.py fakes windows
  - .venv/bin/python hunts/rh_moonshot/positivity_geometry/explore.py quadratic
  - .venv/bin/python hunts/rh_moonshot/positivity_geometry/explore.py rivals
  - .venv/bin/python -m pytest -q -n0 hunts/rh_moonshot/positivity_geometry
outcome: the Frobenius-span Gram matrix has one positive eigenvalue for all 8 test curves and two for every planted fake, and the golden fake meets every arithmetic hypothesis tested while violating RH
artifacts:
  - hunts/rh_moonshot/positivity_geometry/frobenius_span.py
  - hunts/rh_moonshot/positivity_geometry/explore.py
  - hunts/rh_moonshot/positivity_geometry/test_positivity_geometry.py
  - hunts/rh_moonshot/positivity_geometry/NOTES.md
```
