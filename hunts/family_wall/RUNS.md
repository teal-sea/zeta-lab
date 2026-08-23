# family_wall — run manifests

```runmanifest
id: family_wall-2026-08-23-analytic-limit
hunt: family_wall
started: 2026-08-23T15:40-05:00
finished: 2026-08-23T19:10-05:00
ran:
  - .venv/bin/python hunts/family_wall/verify_chain.py
  - .venv/bin/python hunts/family_wall/structure.py
  - .venv/bin/python hunts/family_wall/witness_bound.py
  - .venv/bin/python hunts/family_wall/envelope_bound.py
  - .venv/bin/python hunts/family_wall/tiled_cover.py
  - .venv/bin/modal run hunts/family_wall/modal_family_limit.py
  - .venv/bin/python hunts/family_wall/compare_modal.py
outcome: the family saturates; its limit is H exactly and its supremum over all n is bounded by 0.6751676, short of the configuration ceiling by more than 0.0068, and the pressure-crossover lead was confirmed with a floor-defect correction of order 1e-6
artifacts:
  - hunts/family_wall/FAMILY-LIMIT.md
  - hunts/family_wall/artifacts/family-limit-modal.json
  - hunts/family_wall/artifacts/witness.json
  - hunts/family_wall/artifacts/compare.json
  - hunts/family_wall/artifacts/tiled-cover.json
  - hunts/family_wall/artifacts/periodic-energy-curve.json
```

## Notes

- The Modal job's `n = 20` cells missed basins that the analytic witness ladder reaches
  directly: at four pressures the ladder returned a lower functional value than the
  multistart search. The raw `Phi_20 = 0.6731391381` from that job is therefore built on a
  value that is not a floor and is not a valid certificate number. Section 3 of
  `FAMILY-LIMIT.md` records the correction (`0.6730928938`). Anyone rerunning the Modal job at
  `k >= 16` should enumerate more of the two-letter word space per shard than the 16000 used
  here, or seed from the ladder.
- The `n = 10 .. 16` sweep running in parallel is a separate measurement; nothing here
  duplicates it, and its peaks are a further check against the section 2.3 bounds.
- Nothing in this hunt was run in exact arithmetic. Section 4 of `FAMILY-LIMIT.md` states
  which direction each float error can move a claim and which numbers would need Arb if the
  barrier is ever leaned on formally.
