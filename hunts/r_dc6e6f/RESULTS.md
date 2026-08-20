# Hunt R-DC6E6F: results

**Question.** Does `scripts/make_context.py --check` detect public functions, classes, constants, or module additions under `compiler/`, and what is the exact sensitivity boundary?

**Answer.** It does not detect them. Across all 3 Python modules (`__init__.py`, `catalog.py`, `semantics.py`), 10 LLVM IR fixtures, and 1 documentation file in `compiler/`, every modification, addition, rename, and line-count alteration passes `scripts/make_context.py --check` completely undetected (0 of 17 curated compiler mutants detected, 0.0% detection rate; 0 of 37 public symbols detected across the exhaustive census, 0.0% detection rate). The generated `CONTEXT.md` is byte-identical (0 diff lines) because `compiler/` is omitted from the scanned directory targets in `scripts/make_context.py` (`PKG`, `DISCOVERY`, `HARNESS`, `DOSSIER`, `DOCS`, `SCRIPTS`, `TESTS`) and from `build_flat()`.

Conversely, the guard catches 100% of positive controls in scanned packages (5 of 5 detected, 100.0%), including public symbol additions to `zeta/core.py`, additions to `harness/departments/compiler_department.py`, new documents in `docs/`, new scripts in `scripts/`, and new test files in `tests/`.

Reproduce: `python3 hunts/r_dc6e6f/probe.py` (~15 s, standard library only).
Raw data: `hunts/r_dc6e6f/results.json`.

## Controls

All baseline and undo controls ran and held cleanly across the entire run:

| control | what it rules out | outcome |
|---|---|---|
| Control 1: unmutated sandbox run through guard | catches caused by copy artifacts or tree dirty state | exit 0, `CONTEXT.md is up to date.` |
| Control 2: sandbox state restored and guard re-run after every mutant | cross-mutant contamination or residue | quiet (exit 0) after all 22 curated mutants and 37 census mutants |
| Control 3: positive controls in scanned packages | broken or unresponsive guard invocation | 5 / 5 fired (100.0% caught with diff > 0) |

## The curated battery

`diff` is the number of unified diff lines in regenerated `CONTEXT.md`. `token` is whether the mutated symbol's name appears in that diff.

### Category 1: Public functions added under compiler/

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M01 | `compiler/catalog.py`: append `def new_catalog_probe(): pass` (`__all__` untouched) | no | 0 | no |
| M02 | `compiler/catalog.py`: append `def new_catalog_probe(): pass` (added to `__all__`) | no | 0 | no |
| M03 | `compiler/semantics.py`: append `def new_semantics_probe(): pass` (`__all__` untouched) | no | 0 | no |
| M04 | `compiler/semantics.py`: append `def new_semantics_probe(): pass` (added to `__all__`) | no | 0 | no |
| M05 | `compiler/__init__.py`: append `def new_init_probe(): pass` | no | 0 | no |

**0 / 5 detected (100% blind).**

### Category 2: Public classes and uppercase constants in compiler/

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M06 | `compiler/catalog.py`: add `class ProbeCatalogClass` (added to `__all__`) | no | 0 | no |
| M07 | `compiler/semantics.py`: add `class ProbeSemanticsClass` (added to `__all__`) | no | 0 | no |
| M08 | `compiler/semantics.py`: add constant `PROBE_COMPILER_CONSTANT = 100` | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 3: In-place modifications and renames in compiler/

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M09 | `compiler/catalog.py`: rename `instruction_count` to `probe_inst_count` in place and in `__all__` | no | 0 | no |
| M10 | `compiler/semantics.py`: rename `backend_status` to `probe_backend_status` in place and in `__all__` | no | 0 | no |
| M11 | `compiler/catalog.py`: modify docstring first line of `load_ir` | no | 0 | no |
| M12 | `compiler/semantics.py`: modify signature of `refinement()` in place | no | 0 | no |

**0 / 4 detected (100% blind).**

### Category 4: Module, fixture, and documentation additions under compiler/

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M13 | `compiler/optimizer.py`: create new module with public functions and docstring | no | 0 | no |
| M14 | `compiler/fixtures/probe_fixture.ll`: create new LLVM IR fixture | no | 0 | no |
| M15 | `compiler/FINDINGS.md`: edit title heading and body content | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 5: Line-count variations in compiler/

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M16 | `compiler/catalog.py`: append 20 blank lines (pure line count tell) | no | 0 | no |
| M17 | `compiler/semantics.py`: delete 30 lines (pure line count tell) | no | 0 | no |

**0 / 2 detected (100% blind).**

### Category 6: Positive controls in scanned packages

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| P01 | `zeta/core.py`: append public function `probe_zeta_fn` (added to `__all__`) | yes | 3 | yes |
| P02 | `harness/departments/compiler_department.py`: append public function `probe_dept_fn` (added to `__all__`) | yes | 3 | yes |
| P03 | `docs/probe_test_doc.md`: create new markdown document | yes | 1 | yes |
| P04 | `scripts/99_probe_script.py`: create new runnable script | yes | 1 | yes |
| P05 | `tests/test_probe_case.py`: create new test file | yes | 4 | yes |

**5 / 5 detected (100% caught).**

## Repository census and exhaustive symbol mutation analysis

A full static AST analysis across `compiler/` reveals:

1. **Modules under `compiler/`:** 3 Python modules (`__init__.py`, `catalog.py`, `semantics.py`).
   - `compiler/__init__.py`: 6 lines, 0 functions, 0 classes, 0 constants (module docstring only).
   - `compiler/catalog.py`: 341 lines, 7 public functions, 2 public classes, 5 uppercase constants, declares `__all__` with 14 symbols.
   - `compiler/semantics.py`: 809 lines, 10 public functions, 5 public classes, 8 uppercase constants, declares `__all__` with 21 symbols.
2. **Total public symbols in `compiler/`:** 37 public symbols (17 functions, 7 classes, 13 constants).
3. **Fixtures and docs:** 10 LLVM IR fixtures in `compiler/fixtures/` (`.ll` files), 1 document `compiler/FINDINGS.md` (369 lines).
4. **Exhaustive symbol mutation results:**
   - 17 of 17 public functions: 0 / 17 fired (0.0% detection rate, 100% blind).
   - 7 of 7 public classes: 0 / 7 fired (0.0% detection rate, 100% blind).
   - 13 of 13 constants: 0 / 13 fired (0.0% detection rate, 100% blind).
   - Total symbol census: 0 / 37 fired (0.0% detection rate, 100% blind).

## What the numbers say, in order of how much they matter

1. **The blindness is total across the package.** `scripts/make_context.py` defines explicit scan roots: `PKG` (`zeta/`), `DISCOVERY` (`ontology/`), `HARNESS` (`harness/`), `DOSSIER` (`dossier/`), `DOCS` (`docs/`), `SCRIPTS` (`scripts/`), and `TESTS` (`tests/`). Because `compiler/` is omitted from these roots, every file under `compiler/` is entirely invisible to `scripts/make_context.py --check`.
2. **Line-count tells do not operate on unscanned packages.** In scanned packages, any line count alteration trips the per-module line count in `CONTEXT.md` (`*NNN lines*`). In `compiler/`, neither line counts nor symbol signatures are extracted, so adding, deleting, or reflowing lines in `compiler/` produces zero diff in `CONTEXT.md`.
3. **The wrapper department is guarded, but the subject implementation is not.** While `harness/departments/compiler_department.py` (21 exports) and `tests/test_compiler_candidate.py` (32 tests) are fully indexed and guarded in `CONTEXT.md`, the actual execution engine in `compiler/semantics.py` (809 lines, 21 exports) and catalog in `compiler/catalog.py` (341 lines, 14 exports) have zero presence in the index.
4. **Exclusion from `build_flat()`.** `scripts/make_context.py --flat` concatenates repository source into `CONTEXT_FLAT.md`. The group definitions in `build_flat()` include Package, Discovery layer, Harness, Dossiers, Scripts, Docs, and Tests, but omit `compiler/`. Thus, prompt concatenation also completely omits `compiler/`.

## What I chose, and why

- **Isolated sandbox execution:** Mutating a throwaway copy under `/tmp` prevented any dirty working tree state or residual modifications.
- **Combined curated battery and exhaustive symbol census:** The 22 curated mutants test additions, renames, docstring modifications, signature changes, new modules, new fixtures, and line count variations, while the 37-symbol census verifies every individual public symbol in `compiler/`.
- **Diff verification with token matching:** Checking diff line counts and token presence in `CONTEXT.md` confirms byte-for-byte identity of the regenerated artifact across all compiler mutations.

## What I could not settle

- **Whether `compiler/` should be indexed in `CONTEXT.md`:** `compiler/` is a candidate department (department #3) with provisional findings. Whether candidate departments belong in the primary `CONTEXT.md` index alongside `zeta/` and `harness/` is an architectural design decision for repository maintainers.

## Loose threads

- **Other top-level packages unscanned by make_context.py:** `meta/` (B01) is similarly unscanned. In addition, `interactive_lab/`, `publication/`, and `mathlib-wishlist/` are top-level directories not indexed in `CONTEXT.md`.
  - *Why it might matter:* New contributors or agents reading `CONTEXT.md` have no index visibility into tools or metadata in these directories.
  - *First step:* Review the top-level directory census and decide whether a "Tooling and metadata" section should be added to `scripts/make_context.py`.
- **Exclusion of `compiler/` from `CONTEXT_FLAT.md`:** When `--flat` is used to dump the repository for single-prompt contexts, `compiler/` is omitted entirely.
  - *Why it might matter:* An agent given only `CONTEXT_FLAT.md` will be unaware of compiler semantics and catalog definitions.
  - *First step:* Add `("Compiler", sorted((ROOT / "compiler").glob("*.py")))` to `build_flat()` in `scripts/make_context.py` if candidate departments are intended to be included in full dumps.
