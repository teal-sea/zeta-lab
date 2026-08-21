# Hunt R-6F088D: zeta23ext root load, Retention.Aconst / c2 collisions across arms

Run `bc87fba6-95d1-4ce0-a9ef-c7e364c95bcb`, branch `hunt/r-6f088d-bc87fba6`,
budget 30 minutes, no operator supervision. Case log entry: **Hunt #49** (Hunt #46
was assigned in the brief but was already occupied on disk by `r_b9552d/`).

## The question

zeta23ext root could not load: Retention.Aconst / c2 defined in three arms (fixed by scoping; duplication remains).
Settle the mechanism, verify the scope of collision and duplication across the arms, and determine whether the root module can load under Lean 4.

## Scope

Writes confined to `hunts/r_6f088d/`, this directory, and one case log entry in `hunts/README.md`.

```huntspec
id: r_6f088d
question: What caused the root module load failure in zeta23ext for Retention.Aconst and c2 across arms, how was it scoped, and what symbol duplication remains?
frontier: Zeta23Ext.lean imports multiple arms (PairEnergy, EForm, EForm2, EForm3, TruncEst) developed across batches 2-6; 17 symbol collisions exist across modules under namespace Retention
proposed_attack: parse every Lean source file, map the declaration and import DAG, test pairwise module collisions under the Lean 4 compiler, and analyze mathematical equivalence of duplicate definitions
dead_routes:
  - importing colliding arms into a single Lean module without distinct namespace qualification
  - treating syntax differences in equivalent mathematical definitions as separate concepts
required_oracles:
  - the Lean 4 compiler error output on colliding module imports
  - exact AST and regex parsing of declaration namespaces across all 64 Lean files in the package
kill_conditions:
  - the Lean toolchain is unavailable or unexecutable
  - the 30 minute budget is exhausted
  - the symbol collision mechanism cannot be demonstrated mechanically
agents_may:
  - parse and analyze Lean source files
  - compile isolated test modules under Lean
  - produce data artifacts and documentation
agents_may_not:
  - edit lean files outside hunts/r_6f088d/
  - assign epistemic status to their own outputs
  - claim the reserved certification word
```

## Standing rules

Nothing here is evidence for or against RH (`docs/08`). Nothing in `hunts/`
is a result until it has been through the battery or the funnel.
