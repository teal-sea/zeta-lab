# Hunt R-AC9CA3: Truncated Weil Positivity Failure on Davenport-Heilbronn

Opened 2026-08-18.

## The question

Truncated Weil form: first positivity failure on Davenport-Heilbronn is at (c, N) = (31, 60), tracking the off-line pair.

Observation from `hunts/rogue_frontier/weil_trunc/` (RESULTS.md section 8; data `dhneg_scan.json`; branch `claude/riemann-hypothesis-research-ofds8s`).

```huntspec
id: r_ac9ca3
question: Truncated Weil form: first positivity failure on Davenport-Heilbronn is at (c, N) = (31, 60), tracking the off-line pair
frontier: lower c=30 positive to N=256, upper c=31 negative at N=60 with lambda_min = -1.8739e-31
dead_routes:
  - relying on Li criterion which is blind to the off-line zero
required_oracles:
  - python-flint Arb ball arithmetic LDL^T factorization
  - acb_mat.eig Rump verified eigenvalue enclosure
  - mpmath high-precision float eigendecomposition
kill_conditions:
  - c <= 30 exhibits negativity at N <= 256
  - cell (31, 60) fails to produce a negative eigenvalue under ball enclosure
  - the Riemann zeta control at (31, 60) fails to remain positive
  - removing the off-line zero quadruple does not flip the sign of the form value
agents_may:
  - search
  - derive
  - code
  - attack
  - measure
agents_may_not:
  - claim theorem status
  - use the reserved word
  - modify files outside assigned scope
```

## Protocol and Scope

May write: `hunts/r_ac9ca3/**` and append to `hunts/README.md`.
All numerical assertions are checked with rigorous ball arithmetic (`python-flint`/Arb) and high-precision `mpmath` cross-checks.
The reserved word is not claimed. Nothing here bears on RH (`docs/08`).
