# Scaling experiment run record

Before the first diagnostic: five predetermined cutoffs, `144,576,2304,9216,36864`;
two coefficient families; two capacities; exact rational algebra; two interval
logarithm implementations at 35 and 70 requested digits. No optimizer. One
numerical thread, estimated under 30 seconds. Abort and report rather than
expand if a bounded run cannot finish within 60 seconds.

The diagnostic separates cost above `psi(N)` from cost above `N`. Neither a
small finite ratio nor agreement of the two logarithm implementations is an
asymptotic result. Exact coefficients and rational enclosures are retained;
the pinned source reconstructs the exact prime-log vectors before evaluation.
decimal summaries are display approximations, not interval endpoints.

Initial diagnostic completed in 1.31 seconds. At `N=36864`, the balanced-prefix
raw excess over N was approximately 904.873880 and the perfect-power-cap
excess was 877.252193. This motivated a second, distinct test: uniform averaging
over cutoff choices from `ceil(y/2)` to `y`, keeping the same five N values.
It tests sensitivity to concentration of the balancing correction, not a
larger-N extrapolation. Averaging improved one of five cutoffs. A third
diagnostic compared the finite cutoff choices individually, using the exact
small-integer excess formula. Selection improved two and tied three. The
durable run below includes four families, with the same five N values.

The final diagnostic took about 7.15 seconds. The durable run is capped at
60 seconds and 1 MiB captured output, with one requested numerical thread.
No free-coefficient optimizer, external execution service, or Ostoyae is used.

Independent review of the actual manuscript confirmed the cap and coefficient
bounds but found two scope defects: an undefined cutoff at support two and an
overstated information cutoff outside the square-root regime. Both were fixed.
The averaging range now starts at `max(2,ceil(y/2))`; the general arithmetic
cutoff is `max(y,floor(N/a))`. Regression tests include support two.

The supplementary profile argument in `PROFILE_NOTE.md` is preserved but is
not part of this run's evidence or the main construction's dependencies.

After check-001, a distinct arithmetic discriminator keeps the endpoint
coefficients fixed and excludes composites witnessed by small prime factors.
It uses prime sets `{2}` and `{2,3,5,7}`, tests the cap for every integer
through 4096, and keeps the original five N values. Predicted runtime under
10 seconds, with the same 60-second wall and one-thread durable-run limits.

## Durable scaling run

The scientific baseline is PR 231 (`4efa72a`). The recorded execution base
is PR 232 (`ede6551`), which restores recovered test bytes and relocates their
precision guard without changing the mathematical source.

Check-001 completed in 7.182455 seconds: 257 cap identities, eight averaging
identities, and 191 candidate cutoffs with 764 interval comparisons across
two implementations and two requested precisions. All assertions passed.

```runmanifest
id: paid-scaling-2026-09-14-check-001
hunt: paid_shortfall_scaling
started: 2026-09-14T00:21:57.084779+00:00
finished: 2026-09-14T00:22:04.267234+00:00
ran:
  - .venv/bin/python hunts/paid_shortfall_scaling/scaling.py --output hunts/paid_shortfall_scaling/computations/check-001/results.json
outcome: All finite identities and complete-cost checks passed; the uniform rate remains unproved
artifacts:
  - hunts/paid_shortfall_scaling/computations/check-001/manifest.json
  - hunts/paid_shortfall_scaling/computations/check-001/results.json
  - hunts/paid_shortfall_scaling/computations/check-001/stdout.txt
  - hunts/paid_shortfall_scaling/computations/check-001/stderr.txt
```

## Small-factor runs and source preservation

Check-002 completed in 1.263508 seconds. All 8,192 nested-cap comparisons
through integer 4096 and all five complete-cost evaluations passed. Independent
review then found that a generator argument would be exhausted by validation,
silently disabling exclusions. The recorded tuple inputs were unaffected.
The current function materializes its input once; regression tests exercise
generators and reject a composite divisor supplied through an iterator.

Check-002 is historical, not a fresh-source validation of the fixed script.
Its exact original script bytes are preserved as `check-002/small_factor.source.txt`.
The manifest and outputs were not edited. The preservation test checks that
snapshot against the manifest's original input hash, the other two unchanged
inputs against their hashes, and every recorded output against its hash.
Validating check-002 against current source with `--root` must report the
changed input. Check-003 reruns the fixed script and is the current evidence.

```runmanifest
id: paid-scaling-2026-09-14-check-002
hunt: paid_shortfall_scaling
started: 2026-09-14T00:27:04.952655+00:00
finished: 2026-09-14T00:27:06.216163+00:00
ran:
  - .venv/bin/python hunts/paid_shortfall_scaling/small_factor.py --output hunts/paid_shortfall_scaling/computations/check-002/results.json
outcome: All tuple-input cap and cost assertions passed; original source retained before an iterator-handling correction
artifacts:
  - hunts/paid_shortfall_scaling/computations/check-002/manifest.json
  - hunts/paid_shortfall_scaling/computations/check-002/results.json
  - hunts/paid_shortfall_scaling/computations/check-002/small_factor.source.txt
```

Check-003 completed in 1.370157 seconds with all 8,192 capacity comparisons
and the same five complete costs passing. It records the corrected script.

```runmanifest
id: paid-scaling-2026-09-14-check-003
hunt: paid_shortfall_scaling
started: 2026-09-14T00:28:39.516149+00:00
finished: 2026-09-14T00:28:40.886306+00:00
ran:
  - .venv/bin/python hunts/paid_shortfall_scaling/small_factor.py --output hunts/paid_shortfall_scaling/computations/check-003/results.json
outcome: Corrected iterable handling; all finite cap and complete-cost assertions passed without changing the reported costs
artifacts:
  - hunts/paid_shortfall_scaling/computations/check-003/manifest.json
  - hunts/paid_shortfall_scaling/computations/check-003/results.json
  - hunts/paid_shortfall_scaling/computations/check-003/stdout.txt
  - hunts/paid_shortfall_scaling/computations/check-003/stderr.txt
```

## Verification

The focused sequential suite passed 249 tests, with four slow cases deselected,
in 16.86 seconds. It covered the two new test modules, the prior paid-shortfall
module, all 52 recovered-source hashes, the recovery precision guard, the two
restored checkers, knownness, numbering, hygiene, HuntSpec, probe discipline,
and executable doors. The governance suite passed 335 tests in 3.73 seconds.
The contribution contract passed, including its 21 tests with two deselected.
`scripts/make_context.py --check` passed.

The provided manifest validator passed with current-root hash checks for
check-001 and check-003. Check-002 passed structural validation; its historical
source and output hash checks passed in the preservation regression, as
explained above. Check-002 and check-003 result JSON objects agree exactly
after removing only their runtime field. No prior research outputs were edited.

No local full numerical suite or Lean build was run. Remote full-suite status
is reported separately from these scoped checks and is not inferred from them.
