# Hunt R-C62E44: doc renaming without number change, and doc content drift

## The question

`harness/departments/guard_ledger.py` records the guard `tests/test_docs_numbering.py::test_no_two_docs_share_a_number` with the known miss:

> a document renamed without its number changing (references stay valid, content drifts from title): no guard reads content

This hunt measures whether `test_no_two_docs_share_a_number` detects a document renamed without its number changing, maps the sensitivity and boundary conditions across all four guards in `tests/test_docs_numbering.py`, and conducts an exhaustive census of `tests/` and `scripts/` for any guard checking document body content, title alignment, or citation semantic validity.

## Scope

Writes only inside `hunts/r_c62e44/`, with two permitted exceptions:
1. One case-log entry in `hunts/README.md` (Hunt #50, assigned next available after #49).
2. Updating the record in `harness/departments/guard_ledger.py` with measured scope and known misses.

Nothing here is mathematics and nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_c62e44
question: Does tests/test_docs_numbering.py::test_no_two_docs_share_a_number detect a document renamed without its number changing, and do any guards in the tree read doc content?
frontier: guard ledger entry records fired=True on duplicate number (05-a.md and 05-b.md), with one stated unmeasured known miss on document renaming and content drift
proposed_attack: apply a 20-mutant battery spanning primary lesions, renames, content replacement, heading changes, sequence gaps, format variations, and phantom references to a temporary sandbox copy of the tree, plus an exhaustive code census across tests/ and scripts/
dead_routes:
  - mutating the live repository directly to test guards, which risks leaving dirty working tree state
  - testing only test_no_two_docs_share_a_number in isolation without checking sibling guards for reference resolution
required_oracles:
  - direct Python execution of test functions in tests/test_docs_numbering.py on sandbox trees
  - make_context.py --check process exit status and diff verification
  - AST and regex census over all test files in tests/
kill_conditions:
  - unmutated baseline sandbox fails the numbering guards or make_context.py check
  - undo check after any mutant fails, leaving sandbox contaminated
  - the primary guard detects a document rename with number preserved, contradicting the declared miss
agents_may:
  - construct sandbox copies of repository trees in temporary directories
  - execute test functions and scripts against mutated sandbox trees
  - perform static AST and regex scans across test and script files
  - record measured outcomes in results.json, RESULTS.md, HANDBACK.json, and the guard ledger
agents_may_not:
  - modify hunts/frontier_math/, meta/, lean/, or root markdown files
  - declare theorem status or cite unproven bounds
  - modify tests outside permitted ledger demonstrations
```
