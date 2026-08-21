# Hunt R-7AD39F: results

**Question.** Does `scripts/make_context.py --check` detect in-place length-neutral private helper renames in modules with `__all__`, and what is the exact boundary?

**Answer.** It does not detect them. Across all 49 modules declaring `__all__` in the scanned repository tree, every length-neutral in-place rename of an unexported private helper (299 of 299 private helpers and classes, 100% of unexported private symbols) passes `scripts/make_context.py --check` completely undetected. The generated `CONTEXT.md` is byte-identical (0 diff lines) because `module_api` filters top-level definitions through `ast.literal_eval(__all__)` when `__all__` is declared, and the line count of the file does not change.

Conversely, the guard catches 100% of renames in modules without `__all__` (4/4, 100%), 100% of renames where `__all__` is updated (4/4, 100%), and 100% of renames that change file line counts (4/4, 100%).

Reproduce: `python3 hunts/r_7ad39f/probe.py` (~45 s, standard library only).
Raw data: `hunts/r_7ad39f/results.json`.

## Controls

Both baseline and undo controls ran and held cleanly across the entire run:

| control | what it rules out | outcome |
|---|---|---|
| Control 1: unmutated sandbox run through guard | catches caused by copy artifacts or tree dirty state | exit 0, `CONTEXT.md is up to date.` |
| Control 2: sandbox state restored and guard re-run after every mutant | cross-mutant contamination or residue | quiet (exit 0) after all 25 curated mutants |

## The curated battery

`diff` is the number of unified diff lines in regenerated `CONTEXT.md`. `token` is whether the mutated symbol's name appears in that diff.

### Category 1: In-place length-neutral private helper renames in `__all__` modules (no `__all__` edit)

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M01 | `zeta/core.py`: `_num` -> `pubnum` in place | no | 0 | no |
| M02 | `zeta/epstein.py`: `_dh_mean_spacing` -> `pdh_mean_spacing` in place | no | 0 | no |
| M03 | `zeta/heatflow.py`: `_xi_local` -> `pxi_local` in place | no | 0 | no |
| M04 | `zeta/zeros.py`: `_rs_theta_local` -> `prs_theta_local` in place | no | 0 | no |
| M05 | `zeta/rigor.py`: `_exact` -> `pexact` in place | no | 0 | no |
| M06 | `ontology/registry.py`: `_role_reasons` -> `prole_reasons` in place | no | 0 | no |
| M07 | `harness/integrity.py`: `_guard` -> `pguard` in place | no | 0 | no |
| M08 | `dossier/report.py`: `_section` -> `psection` in place | no | 0 | no |

**0 / 8 detected (100% blind).**

### Category 2: In-place length-neutral private helper renames in non-`__all__` modules

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M09 | `harness/demo.py`: `_section` -> `psection` in place | yes | 1 | yes |
| M10 | `harness/demo.py`: `_department_block` -> `pdepartment_block` in place | yes | 1 | yes |
| M11 | `harness/demo.py`: `_the_turn` -> `pthe_turn` in place | yes | 1 | yes |
| M12 | `harness/new_department.py`: `_valid_name` -> `pvalid_name` in place | yes | 1 | yes |

**4 / 4 detected (100% caught).**

### Category 3: In-place length-neutral renames in `__all__` modules WITH `__all__` edit

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M13 | `zeta/core.py`: `_num` -> `pubnum` and replace `xi` in `__all__` | yes | 2 | yes |
| M14 | `zeta/epstein.py`: `_dh_mean_spacing` -> `pdh_mean_spacing` added to `__all__` | yes | 1 | yes |
| M15 | `ontology/registry.py`: `_role_reasons` -> `prole_reasons` replaces `validate_domain` in `__all__` | yes | 2 | yes |
| M16 | `harness/integrity.py`: `_guard` -> `pguard` added to `__all__` | yes | 1 | yes |

**4 / 4 detected (100% caught).**

### Category 4: Non-length-neutral renames in `__all__` modules (line-count tell)

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M17 | `zeta/core.py`: `_num` -> `pubnum` + trailing blank line appended | yes | 2 | no |
| M18 | `zeta/epstein.py`: `_dh_mean_spacing` -> `pdh_mean_spacing` + trailing blank line appended | yes | 2 | no |
| M19 | `ontology/registry.py`: `_role_reasons` -> `prole_reasons` with multiline signature | yes | 2 | no |
| M20 | `harness/integrity.py`: `_guard` -> `pguard` with multiline signature | yes | 2 | no |

**4 / 4 detected (100% caught by line count).**

### Category 5: Private classes and constants in `__all__` modules

| id | mutant | fired | diff | token in diff |
|---|---|---|---|---|
| M21 | `zeta/rigor.py`: `class _PrecGuard` -> `class PPrecGuard` (no `__all__` edit) | no | 0 | no |
| M22 | `zeta/rigor.py`: `class _PrecGuard` -> `class PPrecGuard` + added to `__all__` | yes | 1 | yes |
| M23 | `harness/shams.py`: `class _AliasSubject` -> `class PAliasSubject` (no `__all__` edit) | no | 0 | no |
| M24 | `zeta/rigor.py`: `_LOG2_10` -> `PLOG2_10` (uppercase constant) | yes | 2 | yes |
| M25 | `zeta/core.py`: append 1 blank line (control: line-count tell alone) | yes | 2 | no |

## Repository census and exhaustive mutation analysis

A full static AST analysis across all 4 scanned directories (`zeta/`, `ontology/`, `harness/`, `dossier/`) reveals:

1. **Scanned modules:** 67 total Python modules.
   - 49 modules (73.1%) declare `__all__` (`zeta`: 24/25, `ontology`: 10/25, `harness`: 11/13, `dossier`: 4/4).
   - 18 modules (26.9%) do not declare `__all__` (`ontology/01..16_*.py`, `zeta/adele.py`, `harness/demo.py`, `harness/new_department.py`).
2. **Private symbols:**
   - In `__all__` modules: 301 private symbols (287 top-level functions, 14 classes).
   - In non-`__all__` modules: 4 private symbols (4 functions in `harness/demo.py` and `harness/new_department.py`, 0 classes).
3. **Exhaustive mutation results:**
   - 299 of 299 unexported private helpers in `__all__` modules: 0 / 299 fired (0.0% detection rate, 100% blind). (The remaining 2 symbols in `__all__` modules are `__getattr__` and `__dir__` in `zeta/__init__.py`, which are explicitly listed in `__all__`).
   - 4 of 4 private helpers in non-`__all__` modules: 4 / 4 fired (100.0% detection rate).

## What the numbers say, in order of how much they matter

1. **The mechanism is confirmed and complete.** `scripts/make_context.py` defines `module_api(path)` which reads `ast.literal_eval(__all__)`. When `declared` is present, `module_api` unconditionally skips any function or class not in `declared`. When a private helper is promoted to a public name in place without updating `__all__`, `module_api` produces an identical API dictionary. If the edit preserves line count, `CONTEXT.md` is 100% byte-identical.
2. **The line-count tell is what catches almost everything else.** M17 through M20 prove that any edit adding or removing a line trips the `*NNN lines*` tag in `CONTEXT.md`, even when the new symbol itself never reaches the index. The only edits that escape are length-neutral in-place renames in `__all__`-declaring modules.
3. **Upper-case constants behave differently.** In `make_context.py`, constants are matched by `node.id.isupper() and not node.id.startswith("_")`, without filtering against `__all__`. Thus, renaming `_LOG2_10` to `PLOG2_10` in place (M24) fires the guard immediately (diff: 2 lines).
4. **Historical incidence is zero.** A complete scan of `git log -p` across the entire history of `zeta/`, `ontology/`, `harness/`, and `dossier/` found zero instances of length-neutral in-place private-to-public helper renames (`-def _X` to `+def X` or `-class _X` to `+class X`).

## What I chose, and why

- **Isolated sandbox execution:** Mutating a throwaway copy in `/tmp` prevented any dirty working tree state.
- **Combined curated battery and exhaustive census:** The 25 curated mutants test the full spectrum of mechanisms (AST signatures, docstrings, classes, constants, line-count tells), while the exhaustive census tests all 305 private symbols across every module in the repository.
- **Diff verification with token matching:** Recording diff line count and checking whether the mutant's token appeared in `CONTEXT.md` allowed distinguishing between catches due to symbol extraction versus catches due to line-count changes.

## What I could not settle

- **Whether make_context.py should validate top-level public defs against `__all__`:** `make_context.py` currently assumes `__all__` is the authoritative definition of a module's public API. If an unexported public function is added to an `__all__`-declaring module, standard Python conventions treat it as non-public for wildcard imports. Whether `make_context.py` should warn about unexported public functions in `__all__` modules is a design choice for repository maintainers.

## Loose threads

- **Unexported public functions:** In modules with `__all__`, adding a new public function without adding it to `__all__` only trips the guard if it changes file length. If a public function replaces an existing function with equal line count and neither is in `__all__`, it remains unindexed.
  - *Why it matters:* Code consumers inspecting `CONTEXT.md` will not see public functions omitted from `__all__`.
  - *First step:* Add an optional linter check in `scripts/make_context.py` verifying that all public top-level functions in modules with `__all__` are either listed in `__all__` or marked with leading underscores.
