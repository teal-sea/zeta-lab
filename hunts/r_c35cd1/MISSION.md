# Hunt R-C35CD1: test file naming sensitivity and boundary of make_context.py --check

## The question

`harness/departments/guard_ledger.py` records the guard `scripts/make_context.py --check` with the known miss:

> test files whose names do not match test_*.py, e.g. tests/mutant_helper.py (B04)

The attention queue surfaced this item. This hunt measures the exact structural mechanism behind this miss, maps its empirical boundary across all file types, naming conventions, subdirectories, and AST counting rules in `tests/`, and determines whether non-`test_*.py` files currently exist or have ever existed in repository history.

## Scope

Writes only inside `hunts/r_c35cd1/`, `hunts/README.md` (case-log entry for Hunt #59), `harness/departments/guard_ledger.py` (closing the loop), and telemetry.
Mutations are evaluated inside an isolated temporary sandbox directory, never on the live working tree.
Nothing here is mathematics and nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_c35cd1
question: Does scripts/make_context.py --check detect test files whose names do not match test_*.py, and what is the exact boundary?
frontier: guard ledger entry records fired=True on public symbol addition, with known miss B04 indicating silence on test files not matching test_*.py
proposed_attack: run a 25-specimen curated battery across root test filenames, subdirectories, non-Python assets, AST counting mechanics, and positive controls against an isolated throwaway sandbox copy of the tree
dead_routes:
  - mutating the live repository tree directly during testing
  - evaluating mutants without unmutated baseline and per-mutant undo controls
  - assuming file length changes fire the guard in tests/ as they do in package modules
required_oracles:
  - process exit status of make_context.py --check executed on sandbox trees
  - byte-exact diff comparison between baseline and regenerated CONTEXT.md
  - AST module census across all test files in the tree
kill_conditions:
  - the unmutated sandbox baseline fails make_context.py --check
  - an undo step fails to restore byte-identity with baseline CONTEXT.md
  - a non-test_*.py test file trips make_context.py --check without changing scanned files
agents_may:
  - copy scanned directories into temporary sandbox trees and mutate them
  - execute make_context.py and read exit codes and generated artifacts
  - perform static AST scans across python test files in the tree
  - record measured outcomes in results.json, RESULTS.md, HANDBACK.json, and the guard ledger
agents_may_not:
  - touch hunts/frontier_math/, meta/, lean/, or any root markdown file
  - use the reserved word in probe files or hunt artifacts
  - declare theorem status or cite unproven bounds
```
