# Finite saturation run record

This run used the repository virtual environment. Its reported backends were
`python-flint`, with both `mpmath.iv` and `python-flint` available. The script
reconstructs exact rational prime-log vectors first, then evaluates them
through both directed interval routes at 35 and 70 requested digits.

The five selected supports were `12,18,48,95,192`, giving local limits
`12,32,48,97,192`. Ordinary-composite retention failures, prime-power
retention failures, and cap-equality failures were all zero in every case.
The saturated repair equals the exact Mangoldt repair on each local range, so
`saturation_repair_residual` is the empty exact vector. Separately, the exact
positive surplus is `S = sum_{d<=N} Lambda(d)(W_d-1)_+`: it is nonzero, and
the current full total remains `factorial + P_Lambda = psi(N) + S`.

```runmanifest
id: paid-shortfall-saturation-2026-09-13-check-001
hunt: paid_shortfall_saturation
started: 2026-09-13T22:28:03-05:00
finished: 2026-09-13T22:28:14-05:00
ran:
  - .venv/bin/python hunts/paid_shortfall_saturation/saturation.py --output hunts/paid_shortfall_saturation/results.json
artifacts:
  - hunts/paid_shortfall_saturation/results.json
outcome: Five finite selected-prefix cases passed exact saturation and surplus identities with two-backend interval overlap checks
```
