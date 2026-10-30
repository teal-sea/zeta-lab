```runmanifest
id: gabcke_remainder-2026-10-29-open
hunt: gabcke_remainder
started: 2026-10-29T00:10:00+00:00
finished: 2026-10-29T00:20:00+00:00
ran:
  - .venv/bin/python -m pytest -q tests/test_huntspec.py hunts/gabcke_remainder/test_coefficients.py
outcome: the coefficient recursion matches the seven lambda values printed in Satz 2.1.1; the remainder bound is not proved
artifacts:
  - hunts/gabcke_remainder/MISSION.md
  - hunts/gabcke_remainder/coefficients.py
  - hunts/gabcke_remainder/test_coefficients.py
```

```runmanifest
id: gabcke_remainder-2026-10-29-lambda-kernel
hunt: gabcke_remainder
started: 2026-10-29T00:20:00+00:00
finished: 2026-10-29T00:35:00+00:00
ran:
  - /Users/thomas/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin/lean hunts/gabcke_remainder/lean/Coefficients.lean
outcome: the kernel accepts lambda_printed and lambda_divides with no axioms; the remainder bound is not proved
artifacts:
  - hunts/gabcke_remainder/lean/Coefficients.lean
```
