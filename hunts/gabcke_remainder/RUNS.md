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
  - lean hunts/gabcke_remainder/lean/Coefficients.lean   (toolchain leanprover/lean4:v4.35.0-rc2)
outcome: the kernel accepts lambda_printed and lambda_divides with no axioms; the remainder bound is not proved
artifacts:
  - hunts/gabcke_remainder/lean/Coefficients.lean
```

Landing note, 2026-10-30 (PR #370). The run above was on the file without a `module`
header. The header was added at landing because every tracked `.lean` file needs one
(`tests/test_palomar_module_port.py`), and the file was not re-elaborated on this box,
which has no Lean toolchain. The nightly `full.yml` Lean job now elaborates it and
requires both theorems to print no axioms. It first ran on the landing branch the same day:
GitHub Actions run 41057260555 (`full.yml`, `lean_only`, commit b029bc2c), step "the Gabcke
coefficient recursion" passed, so the file as committed elaborates under v4.35.0-rc2 and
`lambda_printed` and `lambda_divides` print "does not depend on any axioms".

