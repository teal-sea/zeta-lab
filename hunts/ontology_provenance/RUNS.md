# RUNS

```runmanifest
id: ontology_provenance-2026-10-27-landing
hunt: ontology_provenance
started: 2026-10-27T22:50:00Z
finished: 2026-10-27T22:58:08Z
ran:
  - python hunts/ontology_provenance/provenance.py ontology --root .
  - python hunts/ontology_provenance/provenance.py zeta --root .
  - python -m pytest hunts/ontology_provenance/test_provenance.py hunts/factorization_vs_position/test_kappa_proportionality.py -q
  - python hunts/factorization_vs_position/diagnose_kappa_scan.py
outcome: Symbol-level scan clears frame 07; five of fifteen files reach a zero-derived name; the kappa scanner's residue table reproduces and its real-part ratio is 1 + KAPPA_REF.
artifacts:
  - hunts/ontology_provenance/RESULTS.md
  - hunts/factorization_vs_position/DIAGNOSIS.md
```
