# First checkpoint, 2026-10-02 (America/Bogota)

Research disposition: unresolved. No resolution of RH, no novelty assertion,
and no outside mathematical review. The proof text is an ordinary derivation
with named classical dependencies. Numerical and exact checks are separate.

Environment: Python 3.14.0, mpmath 1.3.0, SymPy 1.14.0, python-flint 0.9.0.
The repository backend check reported python-flint and both installed
backends, python-flint and mpmath.iv. This hunt's Arb computation uses only
python-flint; it is not the repository's two-backend cross-check.

## Observed results

- Two numerical runs, at 50 and 80 decimal digits, each compare 8 moments
  from central derivatives and theta quadrature and 8 matrix determinants.
  All 8/8 determinants are positive in each route and precision.
- Maximum relative moment differences: 4.61716e-48 and 4.72664e-78.
- Two Arb runs, at 256 and 384 bits: 8/8 strictly positive determinant
  enclosures each. Serialized bounds were checked, and a separate Arb
  matrix-determinant algorithm recomputed signs from saved moment intervals.
- The independent symbolic/rational checker passes one symbolic identity,
  three negative determinant witnesses, and eight positive determinants for
  a function with explicitly known off-axis zeros. Its checks also compare
  both floating-point routes with the Arb results.
- Hunt/document checks: 29 passed, 5 slow tests deselected. Generated context
  is current. Python compilation and git whitespace checks passed.
- A separately invoked doors run included slow tests: 26 passed, one failed.
  The failure was the existing bloch evaluation smoke command exceeding its
  180-second timeout. The learn and refute commands passed. No code in that
  environment or in those tests was changed. This is not an all-green suite.

The broad pre-change fast suite was launched in the original shared checkout
at fd04f1fa, before edits. Its result is recorded below when complete. The
research worktree starts from the newer origin/main 783307c8; the broad run
is therefore not a full-suite validation of this worktree.

## Reproduce

    .venv/bin/python hunts/central_moments/probe.py
    .venv/bin/python hunts/central_moments/ball_check.py
    .venv/bin/python hunts/central_moments/check_exact.py
    .venv/bin/python -m pytest -q -o addopts='' -m 'not slow' tests/test_huntspec.py tests/test_docs_numbering.py tests/test_doors.py tests/test_hunt_probe_discipline.py
    .venv/bin/python scripts/make_context.py --check

```runmanifest
id: central_moments-2026-10-02-checkpoint1
hunt: central_moments
started: 2026-10-02, local calendar date; exact start time not recorded
finished: 2026-10-02, local calendar date
ran:
  - .venv/bin/python hunts/central_moments/probe.py
  - .venv/bin/python hunts/central_moments/ball_check.py
  - .venv/bin/python hunts/central_moments/check_exact.py
  - .venv/bin/python -m pytest -q -o addopts='' -m 'not slow' tests/test_huntspec.py tests/test_docs_numbering.py tests/test_doors.py tests/test_hunt_probe_discipline.py
  - .venv/bin/python scripts/make_context.py --check
outcome: RH unresolved; eight finite positive matrix enclosures and exact counterexamples to generic positivity transfer preserved
artifacts:
  - hunts/central_moments/MISSION.md
  - hunts/central_moments/RESULTS.md
  - hunts/central_moments/probe.py
  - hunts/central_moments/results.json
  - hunts/central_moments/control_extension.json
  - hunts/central_moments/ball_check.py
  - hunts/central_moments/ball_results.json
  - hunts/central_moments/check_exact.py
```
