# PROGRESS: numerics worker

2026-09-23

- [x] Read BRIEF, MISSION, weil_trunc RESULTS s2/s4/s8, THEOREM_FEASIBILITY.
- [x] Solver check: Arb assembly (`enclosures.BallTruncation`) + inverse
  iteration on the midpoint matrix + ball Rayleigh quotient. Reproduces
  DH (31,60) -1.87393568857e-31, DH (31,128) -7.52929737463e-30,
  zeta (31,60) 4.82160175202e-100; each cell under 3 s.
- [x] Task 1: 14 recorded cells reproduced to ~1e-22 (repro.json); mpmath route agrees at fractional c.
- [x] Task 2 grids done for DH N=64,128 and zeta N=64 (grid_*.json); zeta N=128 running. DH cells all hardened (Temple + LDL).
- [x] DH crossing located (crossing.json): c*(N) = 30.818, 30.696, 30.647, 30.629, 30.617 for N = 64..256, both ends hardened, zeta positive at each c_neg. Below 31: no new coefficient enters.
- [ ] Task 3 write-up; edge-law N-ladder (edge.py) running.
- [ ] Task 4: candidate relations tested on DH; RESULTS.md.

Open item: `hunts/README.md` has no case-log entry for `weil_propagation`,
was missing; supervisor approved one entry, committed (402c1cd, e46cf90);
`tests/test_hunt_probe_discipline.py` passes (7/7).
