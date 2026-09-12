# Hunt R-7AD39F: sensitivity of make_context.py --check to in-place private helper renames

## The question

`harness/departments/guard_ledger.py` records the guard `scripts/make_context.py --check` with the known miss:

> a private helper renamed public *in place*, in a module that declares __all__, by a length-neutral edit: the regenerated CONTEXT.md is byte-identical and the guard is quiet (probe mutant B06, the one miss inside the guard's own subject matter)

The attention queue surfaced this item. This hunt investigates the structural mechanism behind this miss, maps its exact empirical boundaries across all 67 modules scanned by `make_context.py`, isolates the `__all__` filtering mechanism from the line-count tell, and verifies whether length-neutral helper renames have ever occurred in repository history.

## Scope

Writes only inside `hunts/r_7ad39f/`, `hunts/README.md` (case-log entry for Hunt #55), `harness/departments/guard_ledger.py` (closing the loop), and telemetry.
Mutations are evaluated inside an isolated temporary sandbox directory, never on the live working tree.
Nothing here is mathematics and nothing here is evidence for or against RH (`docs/08`).

```huntspec
id: r_7ad39f
question: Does scripts/make_context.py --check detect in-place length-neutral private helper renames in modules with __all__, and what is the exact boundary?
frontier: guard ledger entry records fired=True on public symbol addition, with known miss B06 indicating silence on length-neutral in-place helper renames in __all__ modules
proposed_attack: run a 25-mutant curated battery and an exhaustive automated mutation pass across all private symbols in all 67 scanned repository modules against a throwaway sandbox copy of the tree
dead_routes:
  - mutating the live repository directly, which risks dirtying worktree state
  - testing only exit codes without diffing generated CONTEXT.md against baseline
  - evaluating mutants without unmutated baseline and per-mutant undo controls
required_oracles:
  - process exit status of make_context.py --check executed on sandbox trees
  - byte-exact diff comparison between baseline and regenerated CONTEXT.md
  - AST module census across all scanned directories
kill_conditions:
  - the unmutated sandbox baseline fails make_context.py --check
  - an undo step fails to restore byte-identity with baseline CONTEXT.md
  - a length-neutral in-place private rename in an __all__ module without __all__ edit trips make_context.py --check
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
