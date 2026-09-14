# Finite construction run

Base revision: `fd04f1fac9d48a4d769048817e678acdea3b4bdb`.
The mission was the first tracked file created in this hunt. The checkout was
already isolated on its assigned branch. The existing repository Python
environment was reused; an ignored local `.venv` link makes the recorded
computation command reproducible in this worktree. No packages were installed.

Backend preflight returned `python-flint ['mpmath.iv', 'python-flint']`.
The shared pre-push guard was installed from the repository script. The
computation manifest pins Python 3.14.0 and actual library versions; the
discovery optimizer is not a mathematical oracle.

```runmanifest
id: paid-surplus-N144-2026-09-14
hunt: paid_surplus_obstruction
started: 2026-09-14T03:37:41.997803+00:00
finished: 2026-09-14T03:37:42.710317+00:00
ran:
  - .venv/bin/python hunts/paid_surplus_obstruction/construction.py --discover --output hunts/paid_surplus_obstruction/computations/check-001/results.json
outcome: One rational witness passed all 47 prime-power constraints with zero positive surplus and complete cost equal to psi(144)
artifacts:
  - hunts/paid_surplus_obstruction/construction.py
  - hunts/paid_surplus_obstruction/contract.json
  - hunts/paid_surplus_obstruction/computations/check-001/manifest.json
  - hunts/paid_surplus_obstruction/computations/check-001/results.json
  - hunts/paid_surplus_obstruction/computations/check-001/stdout.txt
  - hunts/paid_surplus_obstruction/computations/check-001/stderr.txt
```

The bounded recorded run took 0.712514 seconds and exited 0. It used a
30-second wall limit, a 20-second per-process CPU limit and a cooperative
one-thread library setting. No memory or affinity limit was requested; none
is claimed. All source hashes were unchanged during the run, the declared
result exists, stderr is empty, and the version-2 manifest validator passed
with output hashes and input freshness checked against the project root.

The initial floating feasibility call, the subsequent standalone script
check, and the recorded optional discovery all found the same rational
candidate. The proof and ordinary verification command use the displayed
fixed vector and do not depend on recovering it from a future optimizer run.
There were zero failed mathematical candidate searches, zero bigger cutoffs
tested, zero sub-workers and zero external research calls. No claim of an
unrestricted optimum or a uniform coefficient family is made.

## Validation

- New exact construction suite: **11 passed in 0.48 seconds**. It includes
  separate prime-power and factorial factorizations, exact class checks,
  the coefficient perturbation, zero-vector control, source-prefix inclusion,
  saved-output checks, and precision-state restoration.
- Combined relevant suites: **98 passed in 45.99 seconds**. Command:

  ```sh
  .venv/bin/python -m pytest -q -n 0 tests/test_paid_surplus_obstruction.py tests/test_paid_shortfall_scaling.py tests/test_paid_shortfall.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py tests/test_huntspec.py tests/test_repo_hygiene.py
  ```

- `scripts/make_context.py` regenerated the index, and its `--check` passed.
- The new hunt passed explicit reserved-word, machine-path and em-dash scans;
  `git diff --check` passed. Final staged hygiene and committed secret checks
  are recorded in the handoff.

## Failures and limits of the full-suite check

An initial non-slow suite was started before scientific implementation, but
it continued while this hunt was being written, so it is **not a clean
unchanged-tree baseline**. It completed in 783.00 seconds with **2991 passed,
56 skipped, 6 expected failures and 2 failures**, over 3055 selected cases.
The new construction tests did not exist at collection time and were checked
separately above.

1. `tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
   saw the newly written mission before its case-log entry existed. An early
   targeted run similarly reported 77 passed and this one failure; a direct
   diagnostic stopped at 17 passed and the same failure. Adding the authorized
   case-log entry fixed it, and the final relevant suite passes. This was a
   producer sequencing error, not a pre-existing failure.
2. `tests/test_dossier_hardy_z.py::test_proved_cites_a_watched_dated_kernel_run_the_tree_corroborates`
   fails because its recorded observation is dated 2026-08-13, before the
   referenced Lean file's last change on 2026-09-05. Those files are unchanged
   by this hunt. The unrelated stale record remains unresolved.

The full suite was not rerun after the case-log fix. The 98-case targeted pass
does not turn that earlier two-failure run into a green full-suite result.
The 56 skips are reported as skips; the two log backends used by this hunt
were both explicitly present and ran, with zero skipped log evaluations.

Ordinary proof and executable arithmetic remain separate from outside review.
Independent challenge and any integration belong to the coordinator; this
pass stops at a local commit.
