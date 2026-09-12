# Hunt R-C35CD1: test file naming sensitivity and boundary of make_context.py --check

**Status: settled.** The guard `scripts/make_context.py --check` does not detect test files whose names do not match `test_*.py` (such as `tests/mutant_helper.py`, `tests/conftest.py`, or `tests/helper.py`), nor does it detect nested test files inside subdirectories (such as `tests/fixtures/test_sample.py` or `tests/unit/test_unit.py`), non-Python test assets (`tests/test_data.json`, `tests/fixtures/data.csv`), or non-test helper additions inside existing test files.

Across a 25-specimen curated battery in an isolated sandbox:
- 0 of 12 root non-matching test files were detected (0.0% detection rate).
- 0 of 4 nested test files and subdirectories were detected (0.0% detection rate).
- 0 of 4 non-Python test asset files were detected (0.0% detection rate).
- 0 of 2 length and helper modifications within existing test files were detected (0.0% detection rate).
- 3 of 3 in-scope test modifications (`test_` function additions, renames, and new `test_*.py` files) were 100% detected.

An exhaustive repository census shows 77 `test_*.py` files containing 1852 test functions currently in `tests/`. One tracked test asset exists (`tests/fixtures/rung3_ball_term_kernel.json`), which is completely unindexed in `CONTEXT.md`. An audit of 79 historical paths under `tests/` across repository git history confirms zero non-`test_*.py` helper Python files have ever been committed.

Reproduce: `python3 hunts/r_c35cd1/probe.py` (~75 s, standard library only).
Raw data: `results.json`.

## Controls

Both controls ran, held, and verified test isolation:

| Control | What it rules out | Outcome |
|---|---|---|
| Control 1: Unmutated sandbox baseline | A false catch produced by file copying or environment artifacts | Exit 0, `CONTEXT.md is up to date.` |
| Control 2: Per-mutant undo restoration | Cross-contamination between consecutive mutant specimens | Exit 0 and 0 diff lines across all 25 specimens |

All mutations were evaluated strictly within a throwaway sandbox directory in `/tmp`. The live tree was never mutated.

## The Specimen Battery

| ID | Category | Specimen | Fired | Diff Lines | Token in Diff | Notes |
|---|---|---|---|---|---|---|
| M01 | Root non-matching | `tests/mutant_helper.py` (B04 reference) | no | 0 | no | Helper and test functions unindexed |
| M02 | Root non-matching | `tests/conftest.py` | no | 0 | no | Standard pytest fixtures unindexed |
| M03 | Root non-matching | `tests/helper.py` | no | 0 | no | Support utility file unindexed |
| M04 | Root non-matching | `tests/fixtures.py` | no | 0 | no | Test data generator unindexed |
| M05 | Root non-matching | `tests/utils.py` | no | 0 | no | Assertion library unindexed |
| M06 | Root non-matching | `tests/base.py` | no | 0 | no | Base test case class unindexed |
| M07 | Root non-matching | `tests/testsuite.py` | no | 0 | no | Missing underscore delimiter |
| M08 | Root non-matching | `tests/core_test.py` | no | 0 | no | Trailing `_test.py` convention |
| M09 | Root non-matching | `tests/_test_internal.py` | no | 0 | no | Leading underscore prefix |
| M10 | Root non-matching | `tests/TestUnit.py` | no | 0 | no | CamelCase module name |
| M11 | Root non-matching | `tests/check_properties.py` | no | 0 | no | Alternative `check_*` prefix |
| M12 | Root non-matching | `tests/benchmark_runner.py` | no | 0 | no | Benchmark runner script |
| M13 | Nested / Subdir | `tests/fixtures/helper.py` | no | 0 | no | Helper inside existing fixtures subdir |
| M14 | Nested / Subdir | `tests/fixtures/test_sample.py` | no | 0 | no | Shallow glob ignores subdir tests |
| M15 | Nested / Subdir | `tests/unit/test_unit.py` | no | 0 | no | Shallow glob ignores nested test dirs |
| M16 | Nested / Subdir | `tests/integration/test_integ.py` | no | 0 | no | Shallow glob ignores integration dirs |
| M17 | Non-Py Asset | `tests/test_data.json` | no | 0 | no | JSON dataset asset in root tests/ |
| M18 | Non-Py Asset | `tests/fixtures/data.csv` | no | 0 | no | CSV dataset asset in fixtures/ |
| M19 | Non-Py Asset | `tests/README.md` | no | 0 | no | Markdown documentation file |
| M20 | Non-Py Asset | `tests/pytest.ini` | no | 0 | no | Local pytest configuration file |
| M21 | AST Mechanics | `_internal_helper()` added in `test_adele.py` | no | 0 | no | Non-test function in test file ignored |
| M22 | AST Mechanics | 10 commentary lines added in `test_adele.py` | no | 0 | no | No line-count tell for test files |
| P01 | Positive Control | `test_padic_valuation` renamed to `helper_` | **yes** | 15 | yes | Total count drops 1852 -> 1851 |
| P02 | Positive Control | `test_extra_adele_case` added | **yes** | 15 | yes | Total count rises 1852 -> 1853 |
| P03 | Positive Control | `tests/test_new_standalone.py` added (2 tests) | **yes** | 19 | yes | Files 77 -> 78, tests 1852 -> 1854 |

## Findings and Structural Mechanism

1. **The Root Cause.** In `scripts/make_context.py`, the test scanner function `test_counts()` is implemented as:
   ```python
   def test_counts() -> list[tuple[str, int]]:
       out = []
       for path in sorted(TESTS.glob("test_*.py")):
           ...
           n = sum(
               1
               for node in ast.walk(tree)
               if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
               and node.name.startswith("test_")
           )
           out.append((path.name, n))
       return out
   ```
   This implements two separate filters:
   - File level: `TESTS.glob("test_*.py")` matches only files directly under `tests/` whose names begin with `test_` and end with `.py`.
   - Function level: `ast.walk(tree)` counts only function definitions whose names begin with `test_`.

2. **Shallow Glob Misses Subdirectories.** Because `TESTS.glob("test_*.py")` is non-recursive, subdirectories such as `tests/fixtures/` or prospective organizational folders (`tests/unit/`, `tests/integration/`) are completely unvisited. Even a file named `test_sample.py` inside `tests/fixtures/` is ignored.

3. **Absence of the Line-Count Tell in Tests.** For package code (`zeta/`, `ontology/`, `harness/`, `dossier/`), `make_context.py` records `*{api[lines]} lines*` for each module in `CONTEXT.md`. Any edit altering file length trips the guard. For `tests/`, however, `CONTEXT.md` records only the count of `test_*` functions (`- tests/test_foo.py: N`). Adding non-test helpers, fixtures, comments, docstrings, or formatting changes inside an existing test file produces zero diff lines and leaves the guard silent.

4. **Corpus Census and Historical Safety.**
   - The current repository contains 77 matching `test_*.py` files with 1852 test functions.
   - The only non-Python file in `tests/` is `tests/fixtures/rung3_ball_term_kernel.json` (5289 bytes), which is not indexed in `CONTEXT.md`.
   - In git history, across 79 unique historical paths under `tests/`, zero non-`test_*.py` Python helper modules have ever existed. The convention `test_*.py` has been strictly followed for all Python files under `tests/`.

## What I chose and why

1. **Throwaway Sandbox Testing.** Every mutant was evaluated in a temporary copy of the repository tree under `/tmp`. This guarantees that repository working tree state remains clean and uncommitted.
2. **Subprocess Guard Execution.** Exit codes and generated text were obtained by invoking `scripts/make_context.py` and `scripts/make_context.py --check` directly, ensuring empirical fidelity.
3. **Multi-category Specimen Battery.** The battery was structured into 5 distinct categories covering filename patterns, subdirectory structures, non-code assets, AST accounting semantics, and positive controls.

## What could not be settled

- **Desirability of indexing test helpers.** Standard pytest fixtures in `tests/conftest.py` or helper modules are currently invisible to `CONTEXT.md`. Whether `CONTEXT.md` should index test helper modules or continue focusing exclusively on test case counts is an architectural choice.
- **Recursive test directory policy.** The test suite is currently flat (all 77 test files reside at top level in `tests/`). If subdirectories are introduced in the future (e.g. `tests/unit/`), `test_counts()` would need to use `TESTS.rglob("test_*.py")` to avoid dropping them from `CONTEXT.md`.

## Loose threads

1. **`tests/fixtures/rung3_ball_term_kernel.json` is unindexed.** *What it is:* A test fixture data file exists in `tests/fixtures/` but is invisible to `CONTEXT.md`. *Why it might matter:* Agents reading `CONTEXT.md` do not see available test fixtures. *First step:* Determine whether `CONTEXT.md` should include a short test fixtures subsection.
2. **`test_counts()` uses shallow glob rather than recursive glob.** *What it is:* `TESTS.glob("test_*.py")` ignores nested test files. *Why it might matter:* If tests are reorganized into subdirectories, `CONTEXT.md` test counts would silently drop them. *First step:* Evaluate changing `TESTS.glob("test_*.py")` to `TESTS.rglob("test_*.py")` in `scripts/make_context.py`.
3. **Non-test helper functions inside test files have no line-count tell.** *What it is:* Modifying helper routines in `test_*.py` without changing test function counts produces no `CONTEXT.md` diff. *Why it might matter:* A helper change in a test file goes unnoted in `CONTEXT.md`. *First step:* Confirm whether `CONTEXT.md` intentionally omits line counts for test files to minimize churn.
