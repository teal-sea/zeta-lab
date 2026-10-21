# Run ledger

The run kept no ledger. The first three entries reconstruct its computations on
landing (2026-10-21) from `RESULTS.md`, `results.json` and `HANDBACK.json`; their start
and finish times were not recorded. The last entry is the landing's own checks.

## R-ABF47B-CALIBRATION

```runmanifest
id: r_abf47b-calibration
hunt: r_abf47b
started: unknown
finished: unknown
ran:
  - hunts/r_044dd2/audit.py on orbit18-support-07.json and audit_laurent.py on orbit18-laurent-01.json, as reported
  - hunts/r_044dd2/polynomial_sieve.py at relation caps 3 and 4 on Support 7, as reported
  - probe_6x3.py, a copy of hunts/r_31b6c1/probe.py, for the 6x3 gate and the 8x3 symmetric quotient
outcome: reruns of main's own scripts, not independent routes; cap 3 kept as cap3.json, cap 4 reported without an artifact, and the audit replays left none
artifacts:
  - cap3.json
  - probe_results.json
  - PROBE_RESULTS.md
```

## R-ABF47B-ORBIT-MAP

```runmanifest
id: r_abf47b-orbit-map
hunt: r_abf47b
started: unknown
finished: unknown
ran:
  - map_orbits.py, the 57 H x S2 pair orbits against the 31 S8 x S3 triple orbits over all 105^3 triples
outcome: the run's text records the argument, not the script's output; rerun on landing, the 57 pair orbits map onto all 31 triple orbits, printed to stdout with no artifact
artifacts:
```

## R-ABF47B-GROEBNER

```runmanifest
id: r_abf47b-groebner
hunt: r_abf47b
started: unknown
finished: unknown
ran:
  - run_groebner.py, sympy.groebner in grevlex on the three target brackets entered as zero generators plus 6,558 relations in 138 variables, under a 5-minute alarm
outcome: stopped by its own alarm at 300.03 s; the generators are homogeneous with no constant term, so no outcome could have excluded Support 7; no algebraic conclusion
artifacts:
  - results.json
```

## R-ABF47B-LANDING-CHECKS

```runmanifest
id: r_abf47b-landing-checks
hunt: r_abf47b
started: 2026-10-21T15:33Z
finished: 2026-10-21T15:42Z
ran:
  - map_orbits.py rerun unchanged, 131 s of CPU and 205 MB peak resident set on the swarm box under load
  - polynomial_sieve.py at relation cap 3 on Support 7, compared byte for byte with cap3.json
  - build_system on Support 7, the census of the generators run_groebner.py hands sympy
  - test_orbit_refinement.py, five tests, and five planted faults that each turn it red
outcome: map_orbits.py reproduces 57 onto 31; cap3.json is byte-identical to the rerun; every generator is homogeneous of degree 3 or 4 with no constant term; the slice route agrees with map_orbits.py and with Hunt #71's orbit sizes
artifacts:
  - test_orbit_refinement.py
```
