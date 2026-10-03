# Runs: theta sums and Laguerre inequalities

## Resources and baseline

Fresh isolated worktree, starting at origin/main 8feec794. Shared checkout
and its uncommitted files were left untouched. Python is the repository
venv (3.14); python-flint and mpmath.iv are both installed. This hunt's
numerical probes use mpmath, not interval arithmetic.

Before mathematical implementation, the focused baseline passed 29 tests
with 5 slow tests deselected in 6.95 seconds:

    .venv/bin/python -m pytest -q -n0 -m 'not slow' tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py
    .venv/bin/python scripts/make_context.py --check

The context check passed. This is not a full-suite green claim. The preceding
central_moments/RUNS.md records an existing dossier staleness failure. No
heavy local suite or Lean build is authorized by this hunt.

## Pilot and estimate, before the sweep

A foreground pilot at 40 decimal digits evaluated H_1(200) and its first
two derivatives by incomplete gamma functions in 0.098 seconds. It measured
endpoint slope 0.039498765267749934683 and scaled curvature -1.7401769956.

Planned sweep: N=1,2,3 at t=200,400,800, at 50 and 80 digits, 18 cases.
At average N=2, three times the pilot cost for higher precision gives an
estimate of 18*2*3*0.098 < 11 seconds for that component. Independent
quadratures and actual Xi derivatives get a separate 90-second foreground
cap. No paid compute, detached work, or build is launched. Console progress,
explicit case counts including zero failures, and nonzero exit on any
failed check are required.

## Terminal record

The probe completed in 14.344 seconds. It wrote results.json with 18
truncation evaluations (16 negative L_1, 2 positive), 8 actual-Xi
evaluations (0 negative L_1), 6 independent quadrature/derivative
comparisons, and 2 precision runs of the nonreal-zero control. These are
floating-point checks. The all-N asymptotic sign and the exact rational
control failure are separate ordinary derivations in RESULTS.md.

The initial 14 hunt tests passed in 3.04 seconds. The initial combined check passed
43 tests, with 5 slow tests deselected, in 11.06 seconds. Generated context
was regenerated and remained unchanged. Its check and git whitespace checks
passed. No full local suite, Lean build, paid resource, or detached research
job was run. The repository's existing CI is not included in those local
counts. No external mathematical review was performed.

A subsequent algebraic refinement strengthens the control: for each finite
order cutoff K, C_K passes every order through K at every real argument
while retaining the explicit nonreal zeros. This adds no scan of zeta and
no heavy computation. Three additional test cases check the parameter
bound and exact failures of C_2 at order 3 and C_3 at order 4. The revised
combined suite passed 46 tests with 5 slow tests deselected in 11.34 seconds,
including all 17 hunt cases. The numerical artifact above is unchanged;
it records the original K=1 control. The generalization and its exact
witnesses are reproduced by test_probe.py.

```runmanifest
id: rh_theta_laguerre-2026-10-03-checkpoint1
hunt: rh_theta_laguerre
started: 2026-10-03T04:41:47Z baseline completed; exact session start not recorded
finished: 2026-10-03T05:05:33Z refined local verification recorded
ran:
  - .venv/bin/python hunts/rh_theta_laguerre/probe.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_theta_laguerre/test_probe.py
  - .venv/bin/python -m pytest -q -n0 -m 'not slow' hunts/rh_theta_laguerre/test_probe.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py
  - .venv/bin/python scripts/make_context.py --check
outcome: RH unresolved; finite-theta asymptotic failure and exact finite-order-positive nonreal-zero controls preserved with 46 passing checks
artifacts:
  - hunts/rh_theta_laguerre/MISSION.md
  - hunts/rh_theta_laguerre/RESULTS.md
  - hunts/rh_theta_laguerre/RUNS.md
  - hunts/rh_theta_laguerre/probe.py
  - hunts/rh_theta_laguerre/results.json
  - hunts/rh_theta_laguerre/test_probe.py
```

## CI check and documentation correction

[CI run 37098771010](https://github.com/teal-sea/zeta-lab/actions/runs/37098771010)
finished with 3179 passed, 1 failed, 3 skipped and 6 expected failures in
1041.72 seconds of pytest time. The single failure was this hunt's doors
section: it covered the subjects but did not use the required labels
"constraints" and "information class". The focused command had included
`test_doors.py` (reader entry points), not the different `test_hunt_doors.py`.
This was a missed relevant check, not a baseline defect or a numerical
failure. Only those two prose labels were changed; no test was weakened.

Including the missing test file, the local check on 2026-10-03T05:26:48Z
passed 64 tests, with 5 slow tests deselected and 3 existing expected failures,
in 10.60 seconds. Reproduce with the combined command above plus
`tests/test_hunt_doors.py`. The existing CI rerun is expected to take about
18 minutes, based on the first run's measured 18m7s job duration. It uses
standard Actions runners and is watched to a terminal state. The earlier
superseded run 37098415230 ended cancelled when the control refinement was
pushed; it is not a passing run.
