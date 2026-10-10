# epstein_height: run manifests

```runmanifest
id: epstein_height-2026-09-09-surface
hunt: epstein_height
started: 2026-09-09T23:47-05:00
finished: 2026-09-10T00:20-05:00
ran:
  - .venv/bin/python hunts/epstein_height/probe.py --heights 10 20 40 60 80 100 120 160 --dps 15 20 30 50 80
  - .venv/bin/python hunts/epstein_height/from_log.py
  - .venv/bin/python hunts/epstein_height/boundary.py
  - .venv/bin/python hunts/epstein_height/law.py
  - .venv/bin/python hunts/epstein_height/law2.py
outcome: at dps 15 and height 120 the routine returns a value wrong by 2.3e+36 with no exception and no warning; the recorded constant plus a sigma term leaves a per-form bias of 1.6 digits; the loss re-derived from what the routine forms is -log10 t + sigma log10 pi - log10|Gamma(s)| - log10|zeta_Q(s)| with no fitted constant, and it reduces the per-form bias to 0.15, leaving one uniform offset of +1.068 with rms 0.357 over 49 transition cells
artifacts:
  - hunts/epstein_height/artifacts/surface.json
  - hunts/epstein_height/artifacts/boundary.json
  - hunts/epstein_height/artifacts/law.json
  - hunts/epstein_height/artifacts/law2.json
```

```runmanifest
id: epstein_height-2026-09-10-guard
hunt: epstein_height
started: 2026-09-10T00:25-05:00
finished: 2026-09-10T00:35-05:00
ran:
  - .venv/bin/python hunts/epstein_height/guard.py
outcome: six planted faults, all passing, including the one that makes the others mean anything: with the cancellation constant set to zero the guard stops firing
artifacts:
  - hunts/epstein_height/guard.py
```

## Notes

- **The surface run was cut short by its own wall clock** partway through the
  third form, and its JSON is written at the end, so `from_log.py` rebuilds it
  by parsing the printed lines. That is recorded rather than done by hand so the
  reconstruction is reproducible and so the third form's partialness is obvious.
- **The rectangular grid put only twelve of ninety-eight cells where a
  prediction could be tested**, the rest at the oracle's ceiling or flat at
  zero. `boundary.py` places cells where the law says the transition is, which
  is legitimate for measuring a residual and would not be legitimate for
  deciding whether there is an effect; the grid had already answered that.
- `why_it_hangs.py` measures the acceptance probability of the winding
  recursion at both precisions. The conclusion for `hunts/dps_cap`'s open
  question does not depend on the measured value: because the depth limit
  returns a value rather than raising, the cap cannot cost a refusal.

```runmanifest
id: epstein_height-2026-10-10-landing
hunt: epstein_height
started: 2026-10-10T15:44+00:00
finished: 2026-10-10T16:23+00:00
ran:
  - .venv/bin/python hunts/epstein_height/probe.py --heights 10 20 40 60 80 100 120 160 --dps 15 20 30 50 80
  - .venv/bin/python hunts/epstein_height/boundary.py
  - .venv/bin/python hunts/epstein_height/why_it_hangs.py
  - .venv/bin/python hunts/epstein_height/guard.py
  - .venv/bin/python hunts/epstein_height/guard2.py
  - .venv/bin/python hunts/epstein_height/probe.py --heights 40 60 80 120 160 --dps 15 20 30 --forms "1,1,4;2,1,3"
  - .venv/bin/python -m pytest -q hunts/epstein_height
outcome: against epstein_zeta as it was before #291 (the height lift set to zero), the 120 grid cells and the 42 boundary cells reproduce every field except digits_available, which the artifacts carry as dps + 10 from an earlier probe and the current probe writes as dps + 20; why_it_hangs.json and guard2_contract.json reproduce exactly; guard.py passes its six rungs; on the current routine the 30 re-measured cells all read 16.1 to 16.5 digits, guard2.py passes and guard.py fails its second rung; four stated numbers do not reproduce and are marked where stated
artifacts:
  - hunts/epstein_height/test_epstein_height.py
  - hunts/epstein_height/RESULTS.md
  - docs/41-the-module-that-missed-the-guard.md
```

Every script above was run on 2026-10-10 in a scratch copy of this directory,
first with `zeta.epstein.EPSTEIN_DIGITS_PER_UNIT_HEIGHT` set to zero (the
routine before #291, exactly, since `epstein_completed` did not change), then
the last two with the lift in place. Outputs were compared field by field with
the committed artifacts and left in the scratch copy. Measured on a 4-vCPU
container shared with other jobs: the grid took about 15 minutes, the boundary
cells 5, `why_it_hangs.py` 22 (its 48 evaluations at 110 working digits are the
cost), the two guards 1.5, and the lifted grid 14.

- **Landed on main and renumbered #120 to #129, 2026-10-10.** On main #120 is
  `qrh_rival_step`; #127 is `euler_defect_axis` and #128 is `li_dh_onset`
  (#298). The front door, numbered 37 on the branch, is `docs/41`; main uses 37
  for the methods index. `AUDIT.md` keeps the branch numbering and says so.
- **The repair landed before the hunt did, and it is a different repair.** #291
  (2026-10-09, "Fixes #217") lifts `epstein_zeta`'s working precision by the
  leading term, `ceil(0.6822 |t|)`, and pins it with a lattice-sum test of the
  kind this hunt built. It refuses nothing and carries no `sigma` or `zeta_Q`
  term; its docstring says it cannot help at a zero of `zeta_Q`. The surface,
  both laws and the audit's counterexample therefore describe the routine as it
  was, and are reproduced against it; the current routine is recorded beside
  them.
- **`surface.log` was never committed.** The first note above and `AUDIT.md`
  attack 14 describe it; it is not in the tree. `from_log.py` therefore raises
  `FileNotFoundError` before it can write anything, which the test pins.
- **`smoke.json` has no manifest.** Its four rows are identical to the same
  cells of `surface.json`; it reads as the probe's first smoke run, kept.
- **`surface.json` is the grid plus the boundary cells, merged by hand.** 158
  rows: the 120 grid cells and the 38 boundary cells that do not repeat a grid
  cell. No script performs the merge; the test checks its composition.
