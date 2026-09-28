# Completed research runs

Base commit: `6139de6173ea7e538db6097170a1ccfe93f311cb`.
The dates below record the research day, not reconstructed wall-clock times.
The retained scripts, numerical outputs, and full prover receipts specify the
inputs and checks. Cloud commands incur another run when repeated.

```runmanifest
id: cycle_moments-2026-09-05-spectral-and-mixed
hunt: cycle_moments
started: 2026-09-05
finished: 2026-09-05
ran:
  - .venv/bin/python hunts/cycle_moments/probe.py
  - .venv/bin/python hunts/cycle_moments/mixed_moments.py --self-check
  - .venv/bin/python hunts/cycle_moments/mixed_moments.py --grid-points 4801 --self-check
  - .venv/bin/python -m modal run hunts/cycle_moments/modal_probe.py
  - .venv/bin/python -m modal run hunts/cycle_moments/modal_mixed_probe.py
outcome: Finite spectral inequalities passed their checks; the tested narrow mixed observers had negative numerators and supplied no asymptotic gain.
artifacts:
  - hunts/cycle_moments/results.json
  - hunts/cycle_moments/mixed_integral_results.json
  - hunts/cycle_moments/mixed_integral_refined.json
  - hunts/cycle_moments/cue_results.json
  - hunts/cycle_moments/mixed_cue_results.json
```

The completed Modal app identifiers are `ap-kczpMD2GBPTaRhTYnB80L2` and
`ap-yxAuPSoMKkEjFs6ZeLYQS2`. The null mixed-observer results are retained in
full. Their interpretation and Fourier support costs are in
[MIXED-MOMENTS.md](MIXED-MOMENTS.md).

```runmanifest
id: cycle_moments-2026-09-05-repeated-indices-and-counts
hunt: cycle_moments
started: 2026-09-05
finished: 2026-09-05
ran:
  - .venv/bin/python hunts/cycle_moments/distinct_cycles.py
  - .venv/bin/python hunts/cycle_moments/same_kernel.py
  - .venv/bin/python hunts/cycle_moments/counting_overlap.py
  - .venv/bin/python hunts/cycle_moments/overlap_bound.py
outcome: Exact repeated-index corrections agreed with enumeration; one fixed Fourier kernel gave equal full spectra but different simple counts, and the overlap bounds passed the retained finite checks.
artifacts:
  - hunts/cycle_moments/distinct_cycle_results.json
  - hunts/cycle_moments/same_kernel_results.json
  - hunts/cycle_moments/counting_overlap_results.json
  - hunts/cycle_moments/overlap_bound_results.json
```

The first same-kernel example had equal simple counts and therefore did not
establish a counting improvement. The subsequent five-occurrence example
does distinguish the counts. Both examples remain in the record.

```runmanifest
id: cycle_moments-2026-09-05-lean
hunt: cycle_moments
started: 2026-09-05
finished: 2026-09-05
ran:
  - AXLE check of SpectralJensen.lean in lean-4.33.0
  - AXLE check of QuarticScore.lean in lean-4.33.0
  - AXLE check of CycleMomentAssembly.lean in lean-4.33.0
  - AXLE check of ThirdMomentObstruction.lean in lean-4.33.0
  - AXLE check of DistinctCycles.lean in lean-4.33.0
  - AXLE check of IsospectralCycles.lean in lean-4.33.0
  - AXLE check of CountingOverlap.lean in lean-4.33.0
  - AXLE check of OverlapBand.lean in lean-4.33.0
outcome: All eight exact source files have successful Lean receipts with no admitted proofs; the printed or guarded theorem audits use only standard axioms.
artifacts:
  - hunts/cycle_moments/FORMAL-CHECKS.json
  - hunts/cycle_moments/receipts/SpectralJensen-axle-receipt.json
  - hunts/cycle_moments/receipts/QuarticScore-axle-receipt.json
  - hunts/cycle_moments/receipts/CycleMomentAssembly-axle-receipt.json
  - hunts/cycle_moments/receipts/ThirdMomentObstruction-axle-receipt.json
  - hunts/cycle_moments/receipts/DistinctCycles-axle-receipt.json
  - hunts/cycle_moments/receipts/IsospectralCycles-axle-receipt.json
  - hunts/cycle_moments/receipts/CountingOverlap-axle-receipt.json
  - hunts/cycle_moments/receipts/OverlapBand-axle-receipt.json
```

Each receipt retains its request identifier, exact input, and toolchain. The
source hashes are indexed in [FORMAL-CHECKS.json](FORMAL-CHECKS.json). The
formal scope is limited to the declarations and their explicit hypotheses;
the Fourier, inertia, and asymptotic connections are separated in the notes.
