# Hunt R-2946DE: guard 'scripts/make_context.py --check' does not detect: public functions added under meta/

## The question

`harness/departments/guard_ledger.py` records the guard `scripts/make_context.py --check` with the known miss:

> public functions added under meta/: the package is not scanned at all (B01)

The attention queue in `scripts/70_lab_state.py` surfaced this item. This hunt investigates the structural mechanism behind this miss, maps its exact empirical boundaries across all modules and files in `meta/`, evaluates the sensitivity of `make_context.py` to all categories of edits under `meta/`, and verifies whether public functions or symbols added under `meta/` have ever produced index drift in repository history.

## Scope

Writes only inside `hunts/r_2946de/`, `hunts/README.md` (case-log entry for Hunt #56), `harness/departments/guard_ledger.py` (closing the loop), and telemetry.
Mutations are evaluated inside an isolated temporary sandbox directory, never on the live working tree.
Nothing here is mathematics and nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_2946de
question: Does scripts/make_context.py --check detect public functions added under meta/, and what is the exact boundary?
frontier: guard ledger entry records known miss B01 stating meta/ is not scanned at all
proposed_attack: run a curated 20-mutant battery and an exhaustive AST symbol census across all files in meta/ against a throwaway sandbox copy of the tree
dead_routes:
  - mutating the live repository directly, which risks dirtying worktree state
  - testing only exit codes without diffing generated CONTEXT.md against baseline
  - evaluating mutants without unmutated baseline and per-mutant undo controls
required_oracles:
  - process exit status of make_context.py --check executed on sandbox trees
  - byte-exact diff comparison between baseline and regenerated CONTEXT.md
  - AST module census across all Python files under meta/ and the repository tree
kill_conditions:
  - the unmutated sandbox baseline fails make_context.py --check
  - an undo step fails to restore byte-identity with baseline CONTEXT.md
  - an edit restricted to meta/ trips make_context.py --check on the sandbox tree
agents_may:
  - copy scanned directories into temporary sandbox trees and mutate them
  - execute make_context.py and read exit codes and generated artifacts
  - perform static AST scans across python modules in the tree
  - record measured outcomes in results.json, RESULTS.md, HANDBACK.json, and the guard ledger
agents_may_not:
  - modify hunts/frontier_math/, meta/, lean/, or any root markdown file
  - use the reserved word in probe files or hunt artifacts
  - declare theorem status or cite unproven bounds
```
