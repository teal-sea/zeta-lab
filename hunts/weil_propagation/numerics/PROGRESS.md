# PROGRESS: numerics worker

2026-09-23

- [x] Read BRIEF, MISSION, weil_trunc RESULTS s2/s4/s8, THEOREM_FEASIBILITY.
- [x] Solver check: Arb assembly (`enclosures.BallTruncation`) + inverse
  iteration on the midpoint matrix + ball Rayleigh quotient. Reproduces
  DH (31,60) -1.87393568857e-31, DH (31,128) -7.52929737463e-30,
  zeta (31,60) 4.82160175202e-100; each cell under 3 s.
- [x] Task 1: 14 recorded cells reproduced to ~1e-22 (repro.json); mpmath route agrees at fractional c.
- [x] Task 2 grids done for DH and zeta, N=64,128 (grid_*.json); all 196 cells hardened (Temple + LDL).
- [x] DH crossing located (crossing.json): c*(N) = 30.818, 30.696, 30.647, 30.629, 30.617 for N = 64..256, both ends hardened, zeta positive at each c_neg. Below 31: no new coefficient enters.
- [x] Task 3/4 drafted in RESULTS.md (sections 0-5, 7, 8).
- [x] Zeta edge ladder, precision check, Fact A basis-size check (factA_check.py), section 6, summary.json.
- [x] Final: tests/test_hunt_probe_discipline.py run before the last commit (see final commit message).
- [x] Task 4: seven candidates tested on DH (RESULTS.md s4); five-line summary at the top of RESULTS.md.

Open item: `hunts/README.md` has no case-log entry for `weil_propagation`,
was missing; supervisor approved one entry, committed (402c1cd, e46cf90);
`tests/test_hunt_probe_discipline.py` passes (7/7).

## Theory handoff (C2), 2026-09-23 afternoon

- [x] Task A: Epstein (1,1,6) window floor c in [2, 48], N = 64, 128, both
  sectors, hardened; crossings 27.74 (odd) and 29.30 (even) at N = 128;
  Dedekind control positive; off-line zero 0.953 + 16.290i by argument
  principle; C2 refuted as a propagation mechanism (RESULTS s9.2, s9.3).
- [x] Task B: zeta mu_2 (pole-free) vs lambda_1, lambda_2 on c in [2, 60],
  N = 64, 128; mu_2/lambda_2 = 0.639..0.643, all inertias hardened (s9.4).
