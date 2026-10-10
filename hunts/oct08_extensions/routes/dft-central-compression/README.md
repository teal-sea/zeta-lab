# Central-wire compression candidate

The h+1 central roles of the published triple motif reduce to h by reconstructing the total sum from the coordinate sums. The new rational scatter preserves arbitrary auxiliary values. This improves the exact finite budget and works for h>=21. At h24 it gives the exact-complex all-length DFT bound O(n(log n)^(1-51/10^11)), subject to the pinned upstream compiler and transport lemmas. This is not a practical FFT claim or an established novelty claim.

The h-coordinate count is minimal for the same central matrix and fixed side correction, as proved by its rank. This is not a lower bound for other network mechanisms.

- `MISSION.md`: exact target and scope.
- `PROOF.md`: complete new identity, budget, assumptions and fixed-side rank theorem.
- `AUDIT-TARGET.md`: neutral independent audit request.
- `verify.py`: standard-library exact rational checks and falsification controls.
- `result.json`, `manifest.json`: recorded execution and source hashes.
- `../dft/LITERATURE.md`: source and overlap record; the earlier parameter-only extension is an instantiation of the existing mechanism.

Run from the task workspace:

```sh
python3 routes/dft-central-compression/run_evidence.py
python3 routes/dft/validate_manifest.py routes/dft-central-compression/manifest.json --root routes
```

Source snapshots in `../dft/sources/` are read-only inputs, pinned to OpenAI collection fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Finite execution takes under one second on this machine; it is not a construction of the astronomical full network. The symbolic label and recurrence arguments are written proofs, not consequences of sampling the small scalar tests. Independent audit records are maintained separately by the parent.
