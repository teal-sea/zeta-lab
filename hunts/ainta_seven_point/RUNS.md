# Runs

Environment for every run below: macOS (Darwin 25.5.0, Apple Silicon), Python 3.14.7,
`python-flint` 0.9.0, `ainta/zeta-simple-zeros` at commit
`040c5e899e658aed7b56a2a87f501798fe10761d` installed editable into a fresh venv.
Wall times are inflated: the machine was shared with
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
finished: 2026-08-23T01:25-05:00
ran:
  - .venv/bin/python hunts/ainta_seven_point/probe.py 38263 10000000 (target 0.0038263, which is 6.9e-8 above the apparent float floor, 2400 s cap)
outcome: refused in 121 s at the terminal single-cell box (4184, 7960, 7944, 4166, 7909, 4180) on the 1/4000 grid, which is gaps (1.046, 1.990, 1.986, 1.042, 1.977, 1.045), the same configuration the float minimiser found independently; kill condition 2 did not fire, the verifier refuses what the float search says is false, and the two methods agree on the minimiser; a refusal at a grid is not a proof that the target is false, the float evaluation at that cell is what says so
artifacts:
  - hunts/ainta_seven_point/artifacts/probe-38263-10000000.txt
```

```runmanifest
id: ainta_seven_point-2026-08-23-modal-ceiling
hunt: ainta_seven_point
started: 2026-08-23T13:05-05:00
finished: 2026-08-23T13:09-05:00
ran:
  - ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_ceiling.py (app zeta-hunt77-ceiling, python-flint 0.9.0 on debian-slim py3.12, three job families spawned in parallel)
  - rigorous_floor at ball radii 1e-9, 1e-6, 1e-4 about the minimiser, Arb 256 bits
  - n_point_floor for n=7 and n=8 at p=3000, 48 containers each, 60 restarts per container
  - grid_probe at grid 8000 for targets 1913/500000 and 38263/10000000
outcome: F6 at the minimiser encloses to 0.0038262312115073 at 256 bits, a rigorous upper bound on inf F6; the seven-point control on 2880 restarts returns the same floor and minimiser; the eight-point analogue at the same pressure has apparent floor 0.0043887 at a perfect 1-2 alternation; at grid 8000 the target 1913/500000 is accepted (898669 nodes, depth 57) and 0.0038263 is refused at the same configuration; whole run 236 s wall
artifacts:
  - hunts/ainta_seven_point/modal_ceiling.py
  - hunts/ainta_seven_point/artifacts/modal-results.json
```

```runmanifest
id: ainta_seven_point-2026-08-23-modal-sound-cutoff
hunt: ainta_seven_point
started: 2026-08-23T13:40-05:00
finished: 2026-08-23T13:45-05:00
ran:
  - ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_ceiling.py::rerun (five grid_probe jobs in parallel, PRESSURE_CUTOFF_CELLS raised to 46400 at grid 4000 and 92800 at grid 8000, plus a 60000 control)
outcome: every previously accepted raised target is accepted again with a cutoff that is sound for it; 191/50000 786085 nodes depth 43, 153/40000 862961 nodes depth 51, 1913/500000 907799 nodes depth 58, 1913/500000 at grid 8000 899055 nodes depth 57, control at cutoff 60000 907761 nodes depth 58; node counts move by tens against the unsound runs, so the stale prune was never load-bearing, but it was unjustified and is now justified; 266 s wall
artifacts:
  - hunts/ainta_seven_point/artifacts/modal-rerun-sound-cutoff.json
```

```runmanifest
id: ainta_seven_point-2026-08-23-modal-peak-p3200
hunt: ainta_seven_point
started: 2026-08-23T14:05-05:00
finished: 2026-08-23T14:10-05:00
ran:
  - ~/Zeta/.venv/bin/modal run hunts/ainta_seven_point/modal_ceiling.py::peak (five grid_probe jobs at PRESSURE_DENOMINATOR 3200 with cutoff 47200 at grid 4000 and 94400 at grid 8000)
outcome: at the family-maximising pressure the verifier accepts 36369/10000000 at grid 4000 (1045977 nodes, depth 64) and at grid 8000 (1036265 nodes, depth 64), accepts the weaker 909/250000, and refuses both 363695/100000000 and 36370/10000000 at the same terminal cell as at p=3000; with the m-cap at 280 the resulting bound is 0.673027683, which is the ceiling of this certificate family; 302 s wall
artifacts:
  - hunts/ainta_seven_point/artifacts/modal-peak-p3200.json
```
