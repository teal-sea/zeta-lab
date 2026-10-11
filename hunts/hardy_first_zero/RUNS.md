# hardy_first_zero: run manifests

All runs on one 4-core, 15 GB container, 2026-10-11, times UTC. Lean compiles ran one at a
time and never beside the numerics. The Lean environment is the main clone's built
`lean/.lake` (pinned Mathlib `065356127b1d`, toolchain `v4.35.0-rc2`), read-only: each file is
compiled with `lean --root=... -o <scratch>`, which is what `lean/build.sh` does. Nothing was
built inside the worktree and no `lake build` was run. The last run below rebuilt the four
`ZetaLean` dependencies from this commit's own sources, so the theorem is checked against
them and not against the main clone's oleans.

```runmanifest
id: hardy_first_zero-2026-10-11-sizing
hunt: hardy_first_zero
started: 2026-10-11T13:40Z
finished: 2026-10-11T13:58Z
ran:
  - .venv/bin/python hunts/hardy_first_zero/sizing.py --no-write
outcome: order 4 decides the sign at the two-decimal endpoints with 15 terms (27 for margin 10, margin 15.32 at the planned 30), order 2 needs 471, the order-4 bound is about 4.7 times the defect Arb encloses, and the lab's interval mirror decides the sign on rational boxes at N = 30
artifacts:
  - hunts/hardy_first_zero/sizing.py
```

```runmanifest
id: hardy_first_zero-2026-10-11-prior-art
hunt: hardy_first_zero
started: 2026-10-11T13:45Z
finished: 2026-10-11T13:56Z
ran:
  - arXiv API, eight queries listed in RESULTS.md section 6
  - zbMATH Open API, ten queries listed in RESULTS.md section 6
  - web search, about a dozen queries; AFP topic lists for number theory and analysis
outcome: no formal localization of an explicit nontrivial zero of zeta found in the searched set; GitHub code search and the Lean Zulip search were not reachable from this session
artifacts:
  - hunts/hardy_first_zero/RESULTS.md
```

```runmanifest
id: hardy_first_zero-2026-10-11-lean-spine-phase
hunt: hardy_first_zero
started: 2026-10-11T13:59Z
finished: 2026-10-11T14:16Z
ran:
  - lean T0 smoke test importing ZetaLean.HardyZ (cold page cache, 6 min wall, 12 s user)
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/Spine.lean, four compile cycles of about 4 s each
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/Phase.lean, eight compile cycles of about 5 to 20 s each
  - lean CheckAxioms.lean
outcome: exists_zero_of_sign_data, gammaR_re_pos and gammaR_re_pos_first compile with zero sorrys and depend on propext, Classical.choice and Quot.sound only; at this point the target held conditional on the zeta inequality
artifacts:
  - hunts/hardy_first_zero/lean/HardyFirstZero/Spine.lean
  - hunts/hardy_first_zero/lean/HardyFirstZero/Phase.lean
  - hunts/hardy_first_zero/lean/CheckAxioms.lean
```

```runmanifest
id: hardy_first_zero-2026-10-11-decide-one-term
hunt: hardy_first_zero
started: 2026-10-11T14:16Z
finished: 2026-10-11T14:18Z
ran:
  - lean hunts/hardy_first_zero/lean/measure/DecideOneTerm.lean
outcome: the kernel decides a bound on the real part of the m = 29 term box (nLog 40, nExp 24, p 96, kE 8) at s = 1/2 + 14.13i with decide +kernel, standard axioms, 14 s of user time for the whole file including the import
artifacts:
  - hunts/hardy_first_zero/lean/measure/DecideOneTerm.lean
```

```runmanifest
id: hardy_first_zero-2026-10-11-decide-sum30
hunt: hardy_first_zero
started: 2026-10-11T14:18Z
finished: 2026-10-11T14:48Z
ran:
  - timeout 1800 lean hunts/hardy_first_zero/lean/measure/DecideSum30.lean
outcome: one decide +kernel over the recursive 29-term box sum at both endpoints was stopped by its own 30-minute timeout with 29 minutes of CPU spent and nothing printed; the route was replaced by per-term literal tables
artifacts:
  - hunts/hardy_first_zero/lean/measure/DecideSum30.lean
```

```runmanifest
id: hardy_first_zero-2026-10-11-lean-euler-maclaurin
hunt: hardy_first_zero
started: 2026-10-11T14:50Z
finished: 2026-10-11T15:00Z
ran:
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/EulerMaclaurin.lean, five compile cycles
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/BoxSupport.lean, two compile cycles
  - a scratch file checking the m = 29 box against its mirror literal by decide +kernel
outcome: corrected_trapezoid, zeta_em4 and zeta_em4_error (the order-4 representation of riemannZeta on Re s > 0, Im s > 0 with its remainder) and em30_bound compile with standard axioms; the mirror literal for one term box is accepted by the kernel in seconds
artifacts:
  - hunts/hardy_first_zero/lean/HardyFirstZero/EulerMaclaurin.lean
  - hunts/hardy_first_zero/lean/HardyFirstZero/BoxSupport.lean
```

```runmanifest
id: hardy_first_zero-2026-10-11-boxes-and-assembly
hunt: hardy_first_zero
started: 2026-10-11T15:00Z
finished: 2026-10-11T15:06Z
ran:
  - .venv/bin/python hunts/hardy_first_zero/gen_boxes.py
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/Boxes.lean (2 min 48 s wall, 2 min 39 s user)
  - lean --root=hunts/hardy_first_zero/lean HardyFirstZero/FirstZero.lean, two compile cycles of about 10 s
  - lean hunts/hardy_first_zero/lean/CheckAxioms.lean
outcome: first_zero_on_line, the statement that riemannZeta (1/2 + t*I) = 0 for some t strictly between 1413/100 and 707/50, compiles with zero sorrys and depends on propext, Classical.choice and Quot.sound only; the generator's exact pre-check puts the upper end of the product at -1.37863e-5
artifacts:
  - hunts/hardy_first_zero/gen_boxes.py
  - hunts/hardy_first_zero/lean/HardyFirstZero/Boxes.lean
  - hunts/hardy_first_zero/lean/HardyFirstZero/FirstZero.lean
  - hunts/hardy_first_zero/lean/CheckAxioms.lean
```

```runmanifest
id: hardy_first_zero-2026-10-11-clean-build
hunt: hardy_first_zero
started: 2026-10-11T15:02Z
finished: 2026-10-11T15:06Z
ran:
  - LAKE_DIR=/home/user/zeta-lab/lean/.lake bash hunts/hardy_first_zero/lean/build.sh <fresh scratch dir>
outcome: ZetaLean Rigor, IntervalExp, IntervalCExp and HardyZ compiled from this tree's sources, then the six hunt files and the axiom check, 4 min 14 s wall in all; the statement and the axiom list are as above
artifacts:
  - hunts/hardy_first_zero/lean/build.sh
```

```runmanifest
id: hardy_first_zero-2026-10-11-planted-faults
hunt: hardy_first_zero
started: 2026-10-11T15:07Z
finished: 2026-10-11T15:11Z
ran:
  - .venv/bin/python -m pytest hunts/hardy_first_zero -q with the remainder constant 720 changed to 700 in sizing.py, then restored
  - lean on a scratch copy of the m = 29 box theorem with one digit of one literal changed
  - .venv/bin/python hunts/hardy_first_zero/sizing.py
  - .venv/bin/python hunts/hardy_first_zero/gen_boxes.py --check
outcome: the 3 percent change in the remainder constant turns 8 of 28 tests red; the kernel refuses the box with the changed digit; the restored tree passes 28 of 28 and the generator reproduces Boxes.lean byte for byte
artifacts:
  - hunts/hardy_first_zero/artifacts/sizing.json
```

```runmanifest
id: hardy_first_zero-2026-10-11-review-and-module-port
hunt: hardy_first_zero
started: 2026-10-11T15:44Z
finished: 2026-10-11T16:01Z
ran:
  - LAKE_DIR=lean/.lake bash hunts/hardy_first_zero/lean/build.sh on a clean checkout of 6d818a54, by the reviewing session
  - the same build after the nine Lean files took the repository's module header (module, public import, @[expose] public section), which tests/test_palomar_module_port.py requires of every Lean file
  - lean measure/DecideOneTerm.lean after the port, with the two meta imports its #eval lines need
  - lean measure/DecideSum30.lean after the port, stopped at 180 s
  - .venv/bin/python -m pytest hunts/hardy_first_zero -q
  - .venv/bin/python hunts/hardy_first_zero/gen_boxes.py --check
outcome: both builds exit 0 in 3 min 41 s and 3 min 35 s and print the same statement and the same three axioms for all nine theorems; DecideOneTerm compiles and prints -0.166721 twice; DecideSum30 printed nothing in 180 s and was not run to completion, as in the original measurement; 28 of 28 tests pass and the generator reproduces Boxes.lean, now 837 lines
artifacts:
  - hunts/hardy_first_zero/lean/build.sh
  - hunts/hardy_first_zero/lean/HardyFirstZero/Boxes.lean
```

## Notes

- **Timings are wall clock on a shared container** with a warm page cache; the first
  import of Mathlib from a cold cache took 6 minutes of wall time for 12 seconds of CPU.
- **The two background waits that watched the `decide-sum30` run matched their own
  command line** (`pgrep -f` on a string they contained) and had to be stopped by hand;
  they did no work. A `leanchecker --help` probe started a check instead of printing help
  and was stopped after two minutes; no second-kernel check was run. Its child `lean`
  process outlived it and was still running during the first 18-second `pytest` run of the
  planted-fault manifest, the one breach of the one-process rule in this hunt; it was killed
  before the rerun whose numbers are recorded.
