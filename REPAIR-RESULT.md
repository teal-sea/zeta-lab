# Repair: FourPoint module-root collision

> **Current status (2026-09-28):** the sections below record the module-root repair as it stood when written, before any Lean had run ("No Lake/Lean was run", "Unverified"). Since then the renamed `FourPointCand` package was built to completion on Modal at the pinned toolchain, so the rename is now observed to resolve the ambiguity and the "next cloud compile unit" below has been done. Evidence and its provenance gaps: `hunts/four_point_pressure/evidence/README.md`. Local kernel build only, pending external verification.

## Root cause
`hunts/ainta_seven_point/lean-four-point` requires `Zeta23Bridge` by path
(`../../../lean/bridge`). Lake exposes every `lean_lib` of a required package to
import resolution. `lean/bridge/lakefile.toml` declares `lean_lib FourPoint`
(the registered, proved certificate) and the candidate declared `lean_lib
FourPoint` too, so `import FourPoint.Base` matched two packages:
"could not disambiguate the module FourPoint.Base; multiple packages provide
distinct definitions: FourPoint and Zeta23Bridge@0.1.0" (run 36368994326).
`FourPoint.Base` itself built only because it was built as a direct target
before any import needed disambiguating; every CellsN import failed.
The older green candidate predates the registered transplant into
`lean/bridge`, so it never had a second `FourPoint` root visible.

## Fix (module names only; nothing in lean/bridge touched)
Candidate module root renamed `FourPoint` -> `FourPointCand`:
- `git mv lean-four-point/FourPoint{,.lean}` -> `FourPointCand{,.lean}`; `import FourPoint.` lines rewritten (47 files, import lines only).
- `lakefile.toml`: package name, defaultTargets and `lean_lib` name.
- `four_point_gen.py`: `LIB = "FourPointCand"` (every emitted import/path derives from LIB, so regeneration keeps the fix).
- `four_point_preflight.py`: directory path.
- `.github/workflows/four-point.yml`: build targets and paths (not dispatched).
Unchanged on purpose: Lean namespace `Zeta23Ext.Bridge.FourPoint` (the axiom-audit greps and the mathematical target depend on it; declarations from the two packages are never imported together, so no clash) and all numeric content, so the candidate c = 2330/10^6 target is preserved.

## Regression check
`tests/test_four_point_module_roots.py` (static text scan, no Lake):
module roots of the two lakefiles disjoint; top-level module paths on disk disjoint;
candidate imports stay in own root; generator `LIB` and preflight path match the lakefile.
Run with a bare-function runner because the worktree venv has no pytest (Python 3.10, no tomllib, so the test scans text).
- RED before change: `FAIL test_disk_roots_disjoint ... ['FourPoint']`, `FAIL test_module_roots_disjoint ... ['FourPoint']`, exit=1.
- GREEN after: all 4 PASS, exit=0.

## Unverified
No Lake/Lean was run. That the rename resolves the ambiguity is inferred from the error text and Lake's rule, not observed. The lakefile `name` change could alter the lake-manifest package identity for the cache key; the manifest was not regenerated. No bound is established by this change.

## Next cloud compile unit (Modal or Namespace, after spend approval)
Cheapest: from `hunts/ainta_seven_point/lean-four-point`, `lake build FourPointCand.Base` then `lake build FourPointCand.Cells0` (one cell module, ~6 min at 6.5 s per lemma per RUNS.md). If Cells0 gets past import resolution, the collision is fixed; then the full 3h+ build.
