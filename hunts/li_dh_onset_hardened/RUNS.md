# li_dh_onset_hardened: estimates and run manifests

The box: 32 vCPU, 115 GiB, shared with a campaign pinning Lean jobs. Rules in
`MISSION.md`. Every estimate below was written before the spend it prices.

## Estimate 1 (2026-10-26, before any run)

Timed one unit: `log F(s)` in Arb (four `acb.zeta` Hurwitz values, one
`acb.lgamma`), warm, single process, at four points on or near a circle of
radius about 0.9999: 0.7 to 1.5 ms at 128 bits, 1.1 to 2.4 ms at 200 bits,
1.4 to 2.8 ms at 250 bits, 0.1 to 0.2 ms where Re s is in the thousands.
`acb.dft` on 65536 points at 200 bits: 0.54 s.

First-wave jobs, each single process:

| job | units | estimate |
|---|---|---|
| admissibility (top edge, line grid, two small boxes, sigma bound) | about 2e4 ball evaluations at 128 bits | under 2 min |
| evaluator timing (1000 nodes x 2 precisions, 20 iv nodes, xi control) | 2000 Arb + 20 iv evaluations, one small DFT | under 5 min (iv Euler-Maclaurin about 1 s per node) |
| aliasing-circle cover and sizing | adaptive cover of the circle r', likely 1e4 to 1e5 balls | under 10 min |

All three are far below the one-core-hour gate.
