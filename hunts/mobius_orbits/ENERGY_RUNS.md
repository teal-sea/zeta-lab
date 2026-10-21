# Controlled-energy run record

This continuation keeps prior fixed-prime evidence unchanged.
No large pre-existing Nyman-Beurling ladder is run.

## Pilot budget

Run `energy_probe.py --max-n 4` at 128 and 192 bits, plus an independent
mpmath check of N=4 and three cotangent-free Gram quadratures. Use a
60-second foreground cap. Measure this unit before the five-shell run.
The maximum proposed full matrix dimension is 128, not the old large ladder.

The web extraction backend lacked its configured API key; the primary
Baez-Duarte criterion was retrieved through the browser instead at
https://arxiv.org/abs/math/0202141v2. Its abstract states exactly the
integer-dilation L2 closure equivalence used here. No novelty claim.

## Full-run price

The N=4 pilot including all fixed-cost independent checks took 1.110506s.
An isolated N=16, 192-bit shell took 0.01972746s. A conservative cubic
scale estimate for N=64 is 1.262558s; charging that cost for all five
shells at both precisions plus fixed checks gives 14.625574s. Allow
30 seconds for the full local serial run. No larger matrix is launched.

## Full run

Command:
`.venv/bin/python hunts/mobius_orbits/energy_probe.py --max-n 64 --output hunts/mobius_orbits/energy_results.json`

Returned five shells at each of 128 and 192 bits in 1.235713416s.
Every block/update identity check passed, and each fixed shell gave positive
descent. The sign-reversed update and omitted-cross-term lesions were
both detected. Independent N=4 mpmath and three Gram quadrature comparisons
passed. Finish timestamp observed: 2026-09-26T22:03:47-05:00.

These checks establish only the finite computations stated here. No
uniform positive lower bound on normalized gain is inferred from them.
The three cotangent-free quadratures have analytic tails but use mpmath;
they are independent numerical comparisons, not rigorous quadrature balls.

## Review-driven recheck

The reviewed variant writes `energy_reviewed.json`, preserving the original
`energy_results.json` and `energy_pilot.json`. Same five shells and two
precisions, no scale expansion. It returned in 1.428995584s, including the
new adaptive-update and trace-denominator checks. The Mobius shell won
the exact gain comparison in every tested case. Independent mpmath checks
were extended to adaptive gain and its trace lower bound.
The revised focused suite returned `49 passed, 5 deselected in 4.50s`;
CONTEXT and whitespace checks passed. Timestamp observed:
2026-09-26T22:09:37-05:00. No full-suite retry or public push.

```runmanifest
id: mobius_orbits-energy-review-2026-09-26
hunt: mobius_orbits
started: 2026-09-26T22:08-05:00
finished: 2026-09-26T22:09:37-05:00
ran:
  - .venv/bin/python hunts/mobius_orbits/energy_probe.py --max-n 64 --output hunts/mobius_orbits/energy_reviewed.json
  - .venv/bin/python -m pytest -q -n0 hunts/mobius_orbits/test_probe.py hunts/mobius_orbits/energy_test.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py -m 'not slow' --maxfail=1
  - .venv/bin/python scripts/make_context.py --check
  - git diff --check
outcome: reviewed adaptive fallback and bounded trace passed finite checks; the cumulative lower-moment estimate is still unproved
artifacts:
  - hunts/mobius_orbits/energy_reviewed.json
  - hunts/mobius_orbits/ENERGY_REVIEW.md
```


Before the review additions, focused checks returned `48 passed, 5 deselected in 5.77s`.
`CONTEXT.md is up to date.` and `git diff --check` was clean.
The five deselected tests are the explicit slow exclusions. The earlier
full-suite timeout is still recorded in RUNS.md, not upgraded to a pass.

```runmanifest
id: mobius_orbits-energy-2026-09-26
hunt: mobius_orbits
started: 2026-09-26T21:57-05:00
finished: 2026-09-26T22:06:59-05:00
ran:
  - .venv/bin/python hunts/mobius_orbits/energy_probe.py --max-n 4 --output hunts/mobius_orbits/energy_pilot.json
  - .venv/bin/python hunts/mobius_orbits/energy_probe.py --max-n 64 --output hunts/mobius_orbits/energy_results.json
  - .venv/bin/python -m pytest -q -n0 hunts/mobius_orbits/test_probe.py hunts/mobius_orbits/energy_test.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_doors.py -m 'not slow' --maxfail=1
  - .venv/bin/python scripts/make_context.py --check
  - git diff --check
outcome: a nonincreasing RH-equivalent error and explicit descent witness were checked on five shells; the all-scale gain inequality remains unproved
artifacts:
  - hunts/mobius_orbits/ENERGY.md
  - hunts/mobius_orbits/energy_probe.py
  - hunts/mobius_orbits/energy_test.py
  - hunts/mobius_orbits/energy_pilot.json
  - hunts/mobius_orbits/energy_results.json
```



