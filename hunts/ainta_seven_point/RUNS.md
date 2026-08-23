# Runs

Environment for every run below: macOS (Darwin 25.5.0, Apple Silicon), Python 3.14.7,
`python-flint` 0.9.0, `ainta/zeta-simple-zeros` at commit
`040c5e899e658aed7b56a2a87f501798fe10761d` installed editable into a fresh venv.
Timestamps are America/Bogota. Wall times are inflated: the machine was shared with
other agents and the verifier ran at 18-42% of one core.

```runmanifest
id: ainta_seven_point-2026-08-22-three-point
hunt: ainta_seven_point
started: 2026-08-22T23:10-05:00
finished: 2026-08-22T23:11-05:00
ran:
  - .venv/bin/python -m unittest discover -s tests
  - .venv/bin/python -m zeta_simple_zeros three
outcome: their 7 unit tests pass; the 3-point certificate verifies in 0.34 s and every field except elapsed_seconds matches certificates/three-point.txt
artifacts:
  - hunts/ainta_seven_point/artifacts/three-point.local.txt
  - hunts/ainta_seven_point/artifacts/three-point.published.txt
```

```runmanifest
id: ainta_seven_point-2026-08-22-seven-point
hunt: ainta_seven_point
started: 2026-08-22T23:12-05:00
finished: 2026-08-22T23:15-05:00
ran:
  - .venv/bin/python -m zeta_simple_zeros seven
outcome: the 7-point certificate at 19/5000 verifies in 155 s; nodes, pruned, splits, depth, the three pruning counters, kernel_table_sha256 and the surviving gap components all match certificates/seven-point.txt; second_derivative_table_sha256 differs (theirs 7913c551, ours db0327b0) with no effect on any count
artifacts:
  - hunts/ainta_seven_point/artifacts/seven-point.local.txt
  - hunts/ainta_seven_point/artifacts/seven-point.published.txt
```

```runmanifest
id: ainta_seven_point-2026-08-22-table-hashes
hunt: ainta_seven_point
started: 2026-08-22T23:20-05:00
finished: 2026-08-22T23:21-05:00
ran:
  - .venv/bin/python hunts/ainta_seven_point/table_hashes.py
  - .venv-0.7.0/bin/pip install python-flint==0.7.0 (fails to build on Python 3.14, no wheel)
  - .venv-0.6.0/bin/pip install python-flint==0.6.0 (fails to build on Python 3.14, no wheel)
outcome: the second-derivative table hash is deterministic here (db0327b0 on two rebuilds); the Arb-build explanation for the mismatch against theirs could not be tested because older python-flint does not build on this Python, so the cause stays unconfirmed
artifacts:
  - hunts/ainta_seven_point/table_hashes.py
```

```runmanifest
id: ainta_seven_point-2026-08-23-gohms-191-50000
hunt: ainta_seven_point
started: 2026-08-23T00:05-05:00
finished: 2026-08-23T00:24-05:00
ran:
  - .venv/bin/python hunts/ainta_seven_point/gohms.py (sets TARGET_NUMERATOR=191, TARGET_DENOMINATOR=50000 on the pinned verifier, nothing else)
outcome: the 7-point certificate at 191/50000 verifies; nodes 786421, pruned 393575, maximum depth 43 match the three figures Gohms reported in issue #1 exactly; the report's target string still prints the hard-coded 19/5000, as the issue itself notes; wall 1158 s at 18 percent of a core, 210 s of CPU
artifacts:
  - hunts/ainta_seven_point/gohms.py
  - hunts/ainta_seven_point/artifacts/seven-point.gohms-191-50000.local.txt
```

```runmanifest
id: ainta_seven_point-2026-08-23-apparent-minimum
hunt: ainta_seven_point
started: 2026-08-23T00:30-05:00
finished: 2026-08-23T00:31-05:00
ran:
  - python3 hunts/ainta_seven_point/f6min.py (pure float, 600 Nelder-Mead restarts seeded in the verifier's three surviving gap components, no Arb)
outcome: apparent minimum F6 = 0.0038262312114228695 at gaps (1.046081, 1.989132, 1.986415, 1.041603, 1.977024, 1.045002); the next distinct local minimum is 0.0039910746; this is a float search and not a bound in either direction
artifacts:
  - hunts/ainta_seven_point/f6min.py
  - hunts/ainta_seven_point/artifacts/f6-apparent-minimum.txt
```

```runmanifest
id: ainta_seven_point-2026-08-23-kernel-and-bound-check
hunt: ainta_seven_point
started: 2026-08-23T00:35-05:00
finished: 2026-08-23T00:36-05:00
ran:
  - .venv/bin/python (inline) comparing the float kernel used by f6min.py against build_kernel_table(4000, 12000, 128), and evaluating Phi(c, m) at both published points
outcome: the Arb lower table never exceeds the float kernel on any of 12000 cells, max gap 4.65e-4 which is the cell width times the slope; Phi(19/5000, 269) and Phi(191/50000, 267) reproduce both published constants to the last binary64 digit
artifacts:
```

```runmanifest
id: ainta_seven_point-2026-08-23-probes-below-floor
hunt: ainta_seven_point
started: 2026-08-23T00:50-05:00
finished: 2026-08-23T01:05-05:00
ran:
  - .venv/bin/python hunts/ainta_seven_point/probe.py 153 40000 (target 0.003825, 2400 s cap)
  - .venv/bin/python hunts/ainta_seven_point/probe.py 1913 500000 (target 0.003826, 2400 s cap)
outcome: both accepted by the published verifier at grid 4000; 153/40000 with nodes 862825 and depth 51 in 421 s, 1913/500000 with nodes 907537 and depth 58 in 439 s; the second target sits 2.3e-7 below the apparent float floor, so the verifier reaches the floor and is not the limit; a first attempt died on a shell word-splitting error before the verifier ran and produced nothing
artifacts:
  - hunts/ainta_seven_point/probe.py
  - hunts/ainta_seven_point/artifacts/probe-153-40000.txt
  - hunts/ainta_seven_point/artifacts/probe-1913-500000.txt
```

```runmanifest
id: ainta_seven_point-2026-08-23-probe-above-floor
hunt: ainta_seven_point
started: 2026-08-23T01:10-05:00
finished: see RESULTS.md section 3, appended when the run returned
ran:
  - .venv/bin/python hunts/ainta_seven_point/probe.py 38263 10000000 (target 0.0038263, which is 6.9e-8 above the apparent float floor, 2400 s cap)
outcome: kill condition 2 test; the verifier must refuse a target above the true minimum, and a refusal at a terminal cell brackets the floor from above at this grid
artifacts:
  - hunts/ainta_seven_point/artifacts/probe-38263-10000000.txt
```
