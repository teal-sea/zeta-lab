# Finite saturation run record

The worktree has no local `.venv`; this run used the repository venv at
`/Users/thomas/Zeta/.venv/bin/python`. Its reported backends were
`python-flint`, with both `mpmath.iv` and `python-flint` available. The
script reconstructs exact rational prime-log vectors first, then evaluates
them through both directed interval routes at 35 and 70 requested digits.

The five selected supports were `12,18,48,95,192`, giving local limits
`12,32,48,97,192`. Ordinary-composite retention failures, prime-power
retention failures, and cap-equality failures were all zero in every case.
The exact saturated repair equals the exact Mangoldt repair on each local
range, so the remaining prime-power surplus is the empty exact vector.

```runmanifest
id: paid-shortfall-saturation-2026-09-13-check-001
hunt: paid_shortfall_saturation
started: 2026-09-13T21:51:14-05:00
finished: 2026-09-13T21:51:18-05:00
ran:
  - /Users/thomas/Zeta/.venv/bin/python hunts/paid_shortfall_saturation/saturation.py --output hunts/paid_shortfall_saturation/results.json
artifacts:
  - hunts/paid_shortfall_saturation/results.json
outcome: Five finite selected-prefix cases passed exact saturation identities and two-backend interval overlap checks
```
