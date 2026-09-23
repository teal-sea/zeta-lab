# PROGRESS: numerics worker

2026-09-23

- [x] Read BRIEF, MISSION, weil_trunc RESULTS s2/s4/s8, THEOREM_FEASIBILITY.
- [x] Solver check: Arb assembly (`enclosures.BallTruncation`) + inverse
  iteration on the midpoint matrix + ball Rayleigh quotient. Reproduces
  DH (31,60) -1.87393568857e-31, DH (31,128) -7.52929737463e-30,
  zeta (31,60) 4.82160175202e-100; each cell under 3 s.
- [ ] Task 1: reproduction table (repro.json).
- [ ] Task 2: fine c-grid 29..32, zero-extension and dilation transports.
- [ ] Task 3: decomposition (arch / old-prime rescaling / new primes),
  plus hardened DH crossing location between c = 30 and 31.
- [ ] Task 4: candidate relations tested on DH; RESULTS.md.

Open item: `hunts/README.md` has no case-log entry for `weil_propagation`,
so `tests/test_hunt_probe_discipline.py::test_every_hunt_directory_is_covered_by_the_case_log`
is expected to fail on this branch; editing that file is outside this
worker's write scope. Asked the supervisor.
