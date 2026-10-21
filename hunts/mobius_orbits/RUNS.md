# Execution record

Base: `8941a80`. Local serial exact arithmetic only. No paid or hosted run.

Before research code was added, the full fast suite was attempted with
`.venv/bin/python -m pytest -q -n2 -m 'not slow' --maxfail=1`.
The tool timed out after 420 seconds without returning a result; subsequent
process inspection found no surviving zeta-lab pytest or execnet process.
This is not a green full-suite result. Do not retry the full suite locally.

The focused baseline command
`.venv/bin/python -m pytest -q -n0 tests/test_huntspec.py tests/test_docs_numbering.py tests/test_doors.py tests/test_prime_pair_residue.py --maxfail=1`
returned `54 passed in 115.97s`. The shared venv is linked into the isolated
worktree, and the checked code is imported from this worktree.

## Pilot preflight

Start timestamp observed: 2026-09-26T21:35:34-05:00.
Run `probe.py --max-n 100 --large --output hunts/mobius_orbits/pilot.json`.
This is the timing unit, with a 60-second foreground timeout. It enumerates
finite exact sums and no zero search. Price the larger check from this
measurement before launching it.

Pilot returned 388 cases, 1312 exact b-rows, zero defect in 0.1677832920
seconds. For N=4..300 plus 1000 and 10000 at P=2,6,30,210, the candidate-m
loop count rises from 12480 to 244148, a measured-work extrapolation of
3.2824 seconds. Allow 30 seconds to cover rational arithmetic and overhead;
no larger scan is authorized by this record.

## Completed finite run and checks

The full finite run finished at 2026-09-26T21:41:46-05:00. It returned
1196 distinct (N,P) cases, 8412 b-rows, exact maximum defect zero,
5000 trial-division cross-checks, and 4004 coprime-count cross-checks in
0.726038541 seconds. Both planted faults were detected. The recorded
counts were re-aggregated from results.json and matched.

The focused final command
`.venv/bin/python -m pytest -q -n0 hunts/mobius_orbits/test_probe.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py -m 'not slow' --maxfail=1`
returned `41 passed, 5 deselected in 5.14s`. The slow exclusions are
explicit, not counted as passes. `scripts/make_context.py --check` returned
`CONTEXT.md is up to date.` and `git diff --check` was clean.
The full repository suite remains unverified because of the baseline
timeout above. The construction imports no mathematical core code.

Independent model challenge completed; see REVIEW.md. It reviewed the
mathematical brief, not the source files, and is not external peer review.

```runmanifest
id: mobius_orbits-2026-09-26
hunt: mobius_orbits
started: 2026-09-26T21:35:34-05:00
finished: 2026-09-26T21:44:27-05:00
ran:
  - .venv/bin/python hunts/mobius_orbits/probe.py --max-n 100 --large --output hunts/mobius_orbits/pilot.json
  - .venv/bin/python hunts/mobius_orbits/probe.py --max-n 300 --large 1000 10000 --output hunts/mobius_orbits/results.json
  - .venv/bin/python -m pytest -q -n0 hunts/mobius_orbits/test_probe.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py -m 'not slow' --maxfail=1
  - .venv/bin/python scripts/make_context.py --check
  - git diff --check
outcome: exact finite identities passed and the fixed-P argument survived mathematical challenge; the joint RH target remains open
artifacts:
  - hunts/mobius_orbits/probe.py
  - hunts/mobius_orbits/test_probe.py
  - hunts/mobius_orbits/pilot.json
  - hunts/mobius_orbits/results.json
  - hunts/mobius_orbits/RESULTS.md
  - hunts/mobius_orbits/REVIEW.md
```
