# Hunt R-DC6E6F: guard 'scripts/make_context.py --check' does not detect: public functions added under compiler/ (B02)

**Question.** Does `scripts/make_context.py --check` detect public functions, classes, constants, or module additions under `compiler/`, and what is the exact sensitivity boundary?

```huntspec
id: r_dc6e6f
question: Does scripts/make_context.py --check detect public functions, classes, constants, or module additions under compiler/, and what is the exact boundary?
frontier: scripts/make_context.py --check scans zeta/, ontology/, harness/, dossier/, docs/, scripts/, tests/; compiler/ is not indexed (B02 noted in guard ledger)
proposed_attack: synthesize a 22-mutant curated battery and a 37-symbol exhaustive census across compiler/ modules and measure make_context.py --check sensitivity
dead_routes:
  - relying on make_context.py line counts to catch compiler/ changes (compiler/ is unindexed)
required_oracles:
  - AST analysis of compiler/ modules
  - make_context.py execution against sandboxed mutations with diff verification
kill_conditions:
  - the package will not import after install
  - runtime budget exceeded
  - required modifications outside permitted files
agents_may:
  - search
  - derive
  - code
  - attack
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```

## Run Manifest

```runmanifest
id: r_dc6e6f-run1
hunt: r_dc6e6f
started: 2026-08-20T16:27:35-05:00
finished: 2026-08-20T16:36:00-05:00
ran:
  - .venv/bin/python hunts/r_dc6e6f/probe.py
outcome: make_context.py --check is 100% blind to compiler/ (0/17 curated mutants, 0/37 census symbols detected, 0.0% detection rate)
artifacts:
  - hunts/r_dc6e6f/results.json
  - hunts/r_dc6e6f/probe.py
```
