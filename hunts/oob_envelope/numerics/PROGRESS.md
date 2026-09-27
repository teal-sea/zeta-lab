# numerics PROGRESS (oob_envelope)

Worker: Claude Code, Opus. Branch `teal-sea/oob-cert`. Writes only in
`hunts/oob_envelope/numerics/`. Local runs capped at 10 min and 2 GB.

## Status

| phase | state | grade reached | rests on |
|---|---|---|---|
| 1. H with enclosures, L = 0.8, 1.0, 1.19 | started 2026-09-27 | none yet | |
| 2. K3, then L = 0.8 replication with H | not started | | |
| 3. L = 1.19 cost estimate, then stop and ask | not started | | |
| 4. K2 on a rival without Euler product | not started | | |

## Log

- 2026-09-27. Read MISSION, AGENTS, BRIEF, the seed probes, and Zhu
  arXiv:2608.24827v2 sections 1 to 5 and 7 (pdf fetched to scratch, not
  committed). Plan for phase 1: per prime, build the Fejér-smoothed
  Carathéodory-Toeplitz correction in float, freeze its out-of-band
  coefficients as exact dyadic rationals, raise `M_p` by a small margin, and
  prove `Φ_p = M_p − φ_p + h_p ≥ 0` on `[0, π]` by adaptive Arb evaluation
  with a second-derivative remainder. The float construction is only a
  proposal: the enclosure step checks the explicit trigonometric polynomial,
  so nothing depends on the float roots or weights being accurate.
