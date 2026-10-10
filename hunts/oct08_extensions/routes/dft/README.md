# Fourier network parameter extension

Written result candidate: an h>=22 family replacing a fixed h=100 construction, giving at h=24 an exact-arithmetic DFT bound O(n(log n)^(1-38/10^11)). Depends on the pinned upstream local compiler and all-length transport; independent audit pending. No novelty, practical FFT, stability, or bit-complexity claim.

- `PROOF.md`: quantified result, universal parameter derivation, exact rational exponent proof, dependencies.
- `AUDIT-TARGET.md`: neutral target for fresh independent review.
- `sources/`: authenticated primary-source TeX snapshots.
- `verify.py`: exact finite checks and five negative controls.
- `run_evidence.py`: 10-second timeout wrapper, input hashes before/after and v1 evidence manifest.
- `result.json`, `manifest.json`: successful finite evidence; full recorded run took about 0.063 seconds.
- `validate_manifest.py`: unmodified mathbox computation-audit validator supplied through the skill provider, retained for reproducibility.

From this directory run:

```sh
python3 run_evidence.py
python3 validate_manifest.py manifest.json --root .
```

No dependencies beyond Python's standard library. No large transform arrays are allocated. `verify.py` is the scientific result generator; it performs no writes. `run_evidence.py` replaces only its own result, stderr and manifest files.

Falsification attempts: exact original-versus-reversed scalar schedule with nonzero auxiliary contents, intersection-orbit cancellation including ordered side roles, 8192 exact seven-bit phase cases, and rejection of a missing subtraction, wrong sign, missing doubled loss budget, h=21 saving, and an overstrong rational exponent. The small phase and scheduling tests do not establish universal label geometry; that obligation is in PROOF.md. An initial hand-entered s checksum was wrong and failed immediately; it was corrected from the exact W*m-Delta calculation before the successful recorded run.

The broader ranked slate is `../../fresh-opportunities.md`. The source snapshot and this extension are not committed to Zeta Lab, and the parent must reconcile them with authoritative Ghost state before any lab ingest.
