# Bounded checks

## Recorded-run contract

Planned before the durable run: two seeds, three lift depths, `N=2..128`
and `N=1296`, with exact floor/cap checks through 1296. No optimizer,
parameter search, random input, or unbounded loop. An implementation check
took about 13 seconds, so the durable run has a 60-second wall limit,
one requested numerical thread, and a 1 MiB captured-output limit.

The independent algebra review covered the actual `RESULTS.md`, including
the omitted-tail bill, `N>=J^2` range, floor-factorial remainder, and the
support-three restriction on the `N=14` optimum. It found no mathematical
failure. This is a proof-reading check, not kernel checking or external
verification. The numerical checks use separate Arb and mpmath interval
logarithms and exact rational assembly.

The source checker is self-contained. To reproduce the mathematics without
the optional manifest runner:

```bash
.venv/bin/python hunts/paid_shortfall/construction.py --output /tmp/paid-shortfall-results.json
.venv/bin/python -m pytest -o addopts= -q tests/test_paid_shortfall.py
```

The durable run's version-2 manifest also records its exact command, input
hash, result hashes, resource limits, timing, and base commit. The worktree
is intentionally marked dirty because the new source is checked before
commit; its input hash binds the actual source bytes.

## check-001: completed

The durable run took 3.136 seconds including process overhead. Its result
reported PASS: 2 seeds, 36 seed-period rows, 7,776 floor rows, 3,888 exact
base-6 deficit rows, 768 truncation cases, and 1,296 cap integers.
All 3,072 inequalities passed on each of the two backends at each requested
precision, 35 and 70 decimal digits. All 3,072 cross-backend overlaps passed.
The exact `N=14` primal/dual identities passed. Manifest validation passed.

```runmanifest
id: paid-shortfall-2026-09-13-check-001
hunt: paid_shortfall
started: 2026-09-13T23:43:56.736590+00:00
finished: 2026-09-13T23:43:59.872646+00:00
ran:
  - .venv/bin/python hunts/paid_shortfall/construction.py --output hunts/paid_shortfall/computations/check-001/results.json
outcome: All 768 truncation cases and 3072 inequalities passed on both interval backends at both precisions; no asymptotic improvement was claimed
artifacts:
  - hunts/paid_shortfall/computations/check-001/manifest.json
  - hunts/paid_shortfall/computations/check-001/results.json
  - hunts/paid_shortfall/computations/check-001/stdout.txt
  - hunts/paid_shortfall/computations/check-001/stderr.txt
```

## Regression and preservation checks

The final focused command ran sequentially with one numerical thread:

```bash
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 .venv/bin/python -m pytest -q -m 'not slow' -o addopts= tests/test_paid_shortfall.py tests/test_combined_weight_baseline_review.py tests/test_joint_correction_candidate.py tests/test_discovery_knownness.py tests/test_docs_numbering.py tests/test_repo_hygiene.py tests/test_huntspec.py tests/test_hunt_probe_discipline.py tests/test_doors.py
```

Result: **203 passed, 4 deselected in 17.05 seconds**. This includes 29 cases
in the new regression file. The full repository numerical suite was not
rerun locally. Contribution structure and manifest hash validation passed.
The complete lightweight governance command from `checks.yml` separately
passed all 335 tests in 4.69 seconds. `make_context.py --check` and
`git diff --check` also passed.

The preservation regression fixed alongside this study was reproduced before
editing: the restored baseline checker sets global mpmath precision to 60
digits on import, and the joint checker sets it to 80. Either import made a
negative control that assumed 15 ambient digits accept `1/7` to 40 digits.
The tests now restore exact incoming bit precision after the whole checker
test, including on failure. The negative control now explicitly supplies
15-digit data and is tested under ambient precision 15, 60, and 80.
The original checker files, archives, and recorded outputs remain unchanged.
