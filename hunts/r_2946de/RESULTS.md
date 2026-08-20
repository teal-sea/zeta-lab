# Hunt R-2946DE: results

**Question.** Does `scripts/make_context.py --check` detect public functions added under `meta/`, and what is the exact boundary of this blind region?

**Answer.** It does not detect them. Across all modules and subpackages in `meta/`, 100% of symbol additions, in-place renames, new modules, new markdown documents, and line-count changes pass `scripts/make_context.py --check` completely undetected (0 / 16 curated mutants fired, 0.0% detection rate; 0 / 32 exhaustive public AST symbols detected, 0.0% detection rate). The generated `CONTEXT.md` is 100% byte-identical (0 diff lines, exit code 0) across every mutant under `meta/`.

The mechanism is architectural exclusion: `scripts/make_context.py` defines hard-coded scan roots (`PKG = ROOT / "zeta"`, `DISCOVERY = ROOT / "ontology"`, `HARNESS = ROOT / "harness"`, `DOSSIER = ROOT / "dossier"`, `DOCS = ROOT / "docs"`, `TESTS = ROOT / "tests"`, `SCRIPTS = ROOT / "scripts"`). Neither `build()` nor `build_flat()` references `meta/` anywhere in its AST extraction pipelines. Consequently, `meta/` forms a total blind region.

Positive controls in scanned packages (`zeta/`, `ontology/`, `harness/`, `docs/`) confirm the guard and probe apparatus have full detection power on in-scope paths (4 / 4 fired, 100.0% caught, diff >= 2 lines).

Reproduce: `python3 hunts/r_2946de/probe.py` (~45 s, standard library only).
Raw data: `hunts/r_2946de/results.json`.

## Controls

Both baseline and undo controls ran and held cleanly across the entire run:

| control | what it rules out | outcome |
|---|---|---|
| Control 1: unmutated sandbox run through guard | catches caused by copy artifacts or dirty tree state | exit 0, `CONTEXT.md is up to date.` |
| Control 2: sandbox state restored and guard re-run after every mutant | cross-mutant contamination or residue | quiet (exit 0) after all 48 evaluated mutants |

## The curated battery

`diff` is the number of unified diff lines in regenerated `CONTEXT.md`. `token` is whether the mutant's new symbol appears in that diff.

### Category 1: Public function additions in `meta/`

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M01 | public function appended to `meta/ledger.py` | no | 0 | no |
| M02 | public function appended to `meta/evals/asymmetry.py` | no | 0 | no |
| M03 | public async function appended to `meta/ledger.py` | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 2: In-place public symbol renames in `meta/`

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M04 | public class `Category` renamed in place in `meta/ledger.py` | no | 0 | no |
| M05 | public function `load_ledger` renamed in place in `meta/ledger.py` | no | 0 | no |
| M06 | public uppercase constant `LEDGER_PATH` renamed in place in `meta/ledger.py` | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 3: Public classes and constants added to `meta/`

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M07 | public class `MetaExperimentRegistry` appended to `meta/ledger.py` | no | 0 | no |
| M08 | public uppercase constant `META_DEFAULT_TIMEOUT` appended to `meta/ledger.py` | no | 0 | no |
| M09 | public uppercase constant `ASYMMETRY_EVAL_VERSION` appended to `meta/evals/asymmetry.py` | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 4: New modules and documentation files in `meta/`

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M10 | new module `meta/new_framework.py` with public functions and classes | no | 0 | no |
| M11 | new module `meta/evals/new_eval_metric.py` added | no | 0 | no |
| M12 | new markdown document `meta/meta_methodology.md` added | no | 0 | no |
| M13 | `meta/README.md` title modified in place | no | 0 | no |

**0 / 4 detected (100% blind).**

### Category 5: Line counts, docstrings, and formatting in `meta/`

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M14 | 5 blank lines appended to `meta/ledger.py` (line-count tell test in unscanned tree) | no | 0 | no |
| M15 | `meta/ledger.py` module docstring first line modified | no | 0 | no |
| M16 | docstring added to empty `meta/evals/__init__.py` | no | 0 | no |

**0 / 3 detected (100% blind).**

### Category 6: In-scope positive controls in scanned directories

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M17 | public function appended to `zeta/core.py` (in-scope control) | yes | 2 | no (line count tell) |
| M18 | public function appended to `ontology/schema.py` (in-scope control) | yes | 3 | yes |
| M19 | public function appended to `harness/protocol.py` (in-scope control) | yes | 3 | yes |
| M20 | new doc `docs/99-positive-control-doc.md` added (in-scope control) | yes | 1 | yes |

**4 / 4 detected (100% caught).**

## Repository census and exhaustive mutation analysis

A full static AST census of all Python source files under `meta/` (`meta/ledger.py`, `meta/evals/asymmetry.py`, `meta/evals/__init__.py`) identifies:

1. **32 public top-level symbols in `meta/`**:
   - 10 classes (`Category`, `Automatability`, `CaughtBy`, `Intervention`, `MetaObservation`, `OperatorFunction`, `Resolution`, `Party`, `Judgment`, `Ledger` in `meta/ledger.py`)
   - 16 functions (including `load_ledger`, `validate_ledger`, `asymmetry_dataset`, `checker_verdict`, `detection_rate`, `false_confidence_rate`, `asymmetry_e0`)
   - 6 module-level uppercase constants (including `LEDGER_PATH`)
2. **Exhaustive symbol mutation results**:
   - Every single one of the 32 public symbols was systematically mutated in-place against the sandbox baseline.
   - Result: 0 / 32 fired (0.0% detection rate, 100% blind).
   - Diff lines in `CONTEXT.md`: 0 lines across all 32 runs.

3. **Historical analysis in git history**:
   - `meta/` was introduced in commit `5a666c0` ("meta: the second laboratory").
   - Across all 14 subsequent commits touching `meta/`, zero commits triggered or required changes to `CONTEXT.md`.
   - `scripts/make_context.py` has never contained references to `meta/` at any commit in repository history.

## What the numbers say, in order of how much they matter

1. **The blind region is total and structural.** `scripts/make_context.py` does not omit `meta/` by filter logic or `__all__` parsing: `meta/` is completely omitted from the directory list `make_context.py` reads. No symbol, class, function, docstring, file, or line-count change under `meta/` will ever trip `scripts/make_context.py --check`.
2. **The line-count tell does not apply to `meta/`.** In scanned packages (`zeta/`, `ontology/`, `harness/`, `dossier/`), adding a line trips the guard even if the symbol is unexported. In `meta/`, adding blank lines or modifying file lengths (M14) produces zero diff because `CONTEXT.md` tracks line counts only for scanned modules.
3. **`CONTEXT_FLAT.md` likewise excludes `meta/`.** In `build_flat()`, `meta/` is not listed among the concatenated source groups (`Operating context`, `Package`, `Discovery layer`, `Harness`, `Dossiers`, `Scripts`, `Docs`, `Tests`). Thus, flat context dumps also omit `meta/`.
4. **Architectural reason: `meta/` is the second laboratory.** Per `meta/README.md`, `meta/` holds evidence about the laboratory and research process, not about the mathematical subject. `CONTEXT.md` was created to index the public mathematical and computational APIs of the laboratory (`zeta/`, `ontology/`, `harness/`, `dossier/`, `docs/`, `scripts/`, `tests/`).

## What I chose, and why

- **Isolated sandbox execution:** Mutating a throwaway copy under `/tmp` prevented any dirty working tree state or interference with concurrent sessions.
- **Combined curated battery and exhaustive symbol census:** The 16 curated mutants test functional additions, renames, classes, constants, docs, and line counts, while the 32-symbol census exhaustively covers every public definition currently in `meta/`.
- **Positive controls:** Evaluating 4 mutants across `zeta/`, `ontology/`, `harness/`, and `docs/` proved that the probe and sandbox apparatus reliably detect in-scope modifications.

## What I could not settle

- **Whether `meta/` should remain unindexed or be added to `CONTEXT.md`:** `meta/` holds operator tooling and intervention ledgers. Whether `CONTEXT.md` should expand to include a "Meta-research layer (`meta/`)" section is an architectural decision for repository maintainers. Leaving it unscanned keeps `CONTEXT.md` focused on mathematical research; adding it would bring `meta/` under the stale-index guard.

## Loose threads

- **`compiler/` is also completely unscanned (known miss B02):** Like `meta/`, `compiler/` is a separate package in the repository root that is not referenced in `scripts/make_context.py`.
  - *Why it might matter:* Changes to public functions in `compiler/` (e.g. `compiler/semantics.py`) are similarly invisible to `make_context.py --check`.
  - *First step:* Run a sibling hunt measuring `compiler/` sensitivity and settle whether `compiler/` should be indexed.
- **Unscanned test utilities:** Test helper files not matching `test_*.py` (e.g. `tests/mutant_helper.py`, known miss B04) are ignored by `test_counts()` which globs `test_*.py`.
  - *Why it might matter:* Adding shared test infrastructure does not update the test function count in `CONTEXT.md`.
  - *First step:* Evaluate whether `test_counts()` should glob `*.py` in `tests/` or maintain the `test_*.py` pattern.
