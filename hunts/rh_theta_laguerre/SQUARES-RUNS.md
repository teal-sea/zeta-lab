# Square-construction continuation: runs

Base: origin/main a9f0b38b, isolated worktree. Baseline: 64 passed,
5 slow tests deselected, 3 existing expected failures in 7.37 seconds.
Both python-flint and mpmath.iv are installed; the interval part below uses
Arb, with mpmath as a separate floating-point check, not a second enclosure.
No session-list tool is available. Other working trees were not edited.

## Estimate before the bounded experiment

A single conditional-moment ratio at x=1, order 1, 35 decimal digits,
computed by theta quadrature took 0.494 seconds. It measured
0.02761660955097799652956164. This is a pilot, not a sign proof.

Plan: 12 separations, three moment orders, two decimal precisions. Reusing
kernel evaluations across orders should cost less than three uncached
integrals. Allowing a factor of two for higher precision gives a conservative
estimate 12*3*2*2*0.494 < 72 seconds. Foreground cap: 120 seconds. Each
completed separation reports its count; failure must exit nonzero. A failed
positive-definiteness candidate is a scientific result, not a software error,
and is reported explicitly with its minimum eigenvalue.

The local logarithmic-derivative construction gets two small Arb runs, at
192 and 256 bits, with eight theta terms and an analytic geometric tail
bound. No high-dimensional optimization, Lean build, paid resource, or
unattended research job is launched. The existing PR CI is separate; the
preceding checkpoint measured about 18 to 24 minutes for that suite.

## Follow-up estimate

The planned sweep completed in 3.373 seconds, substantially below the
conservative estimate: two negative score-Gram enclosures, 72 conditional
ratios and 12 ratio-Gram matrices, with 0 negative ratio matrices. Before
attempting a uniform argument for that candidate, a finer first-order matrix
will test frequencies the coarse grid can miss: 24 points at spacing 0.1,
55 digits. Scaling the measured run allows 10 seconds, with a 45-second
foreground cap. This is an adversarial test of the proposed representation,
not an extension of an RH zero scan.

## Finer witness and enclosure estimate

The 24-point, spacing-0.1 probe took 3.779 seconds. It found 7 negative
eigenvalues, minimum about -1.571730889e-6, for the normalized order-one
ratio matrix. The coarse pass was therefore not a positivity conclusion.
Rounding the leading eigenvector at scale 1000 did NOT retain the sign:
its checked quadratic form was +7.712060135e-7. Scale 10000 retained a
negative form about -1.540504202e-6 and is the frozen integer witness.

A separate Arb integration pilot at x=1/2 and 128 bits took 0.00865 seconds.
It encloses the finite-interval ratio to better than 1e-22 before tail
addition. The planned full witness has 24 separations at two precisions;
allowing a factor of ten for refinement gives an estimate below 5 seconds,
with a 30-second foreground cap. The analytic theta and integration tails
will be included before any negative-sign conclusion is drawn.

## Terminal record

- The coarse probe completed in 3.373 seconds: 2 negative score eigenvalue
  enclosures, 72 float conditional ratios, 12 float Gram matrices with zero
  negative minima. That positive coarse record is preserved.
- The frozen 24-point integer witness was enclosed at 128 and 192 bits:
  48/48 ratios evaluated with all tails, 2/2 strictly negative quadratic
  forms, zero failed checks, in 0.316 seconds. Recalculation from the
  serialized enclosures and an independent lag-grouped sum also stay negative.
- The continuation has 16 tests. Independent mpmath checks use 75 digits,
  12 theta terms and integration cutoff 5 for the ratio; the interval route
  uses 8 terms, cutoff 4, and explicit bounds for both omitted tails.
- The combined relevant suite passed 80 tests, with 5 slow tests deselected
  and 3 existing expected failures, in 9.41 seconds. Context and whitespace
  checks passed. No Lean build, paid resource or detached research job ran.
- Two particular square constructions fail. RH is unresolved. No outside
  mathematical review or proof-kernel check was performed.

```runmanifest
id: rh_theta_laguerre-2026-10-03-squares
hunt: rh_theta_laguerre
started: 2026-10-03; exact session start time not recorded
finished: 2026-10-03T15:42:08Z combined local verification completed
ran:
  - .venv/bin/python hunts/rh_theta_laguerre/squares.py
  - .venv/bin/python hunts/rh_theta_laguerre/ratio_witness.py
  - .venv/bin/python -m pytest -q -n0 hunts/rh_theta_laguerre/test_squares.py
  - .venv/bin/python -m pytest -q -n0 -m 'not slow' hunts/rh_theta_laguerre/test_probe.py hunts/rh_theta_laguerre/test_squares.py tests/test_huntspec.py tests/test_docs_numbering.py tests/test_hunt_probe_discipline.py tests/test_hunt_doors.py tests/test_doors.py
  - .venv/bin/python scripts/make_context.py --check
outcome: two specific square constructions fail for the actual theta kernel; negative witnesses enclosed with complete tails; RH unresolved
artifacts:
  - hunts/rh_theta_laguerre/SQUARES.md
  - hunts/rh_theta_laguerre/SQUARES-RUNS.md
  - hunts/rh_theta_laguerre/squares.py
  - hunts/rh_theta_laguerre/squares_results.json
  - hunts/rh_theta_laguerre/ratio_witness.py
  - hunts/rh_theta_laguerre/ratio_witness_results.json
  - hunts/rh_theta_laguerre/test_squares.py
```
