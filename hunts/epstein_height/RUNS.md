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
