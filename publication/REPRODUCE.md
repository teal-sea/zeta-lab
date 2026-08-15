# REPRODUCE

Instructions to independently reproduce the claims and verifying the evidence.

## Reproducing the Formalization

The formalization relies on the Lean 4 proof assistant. The repository provides the `lean/ZetaLean` project.

1. **Install Lean 4 and Lake**: Follow standard community instructions at [leanprover.github.io](https://leanprover.github.io/).
2. **Setup Project Environment**:
   ```bash
   cd lean/ZetaLean
   lake exe cache get
   ```
3. **Build the Project**:
   ```bash
   lake build
   ```
   This command will compile all modules in the `Zeta23Ext` package. A successful, error-free compilation confirms that the proofs are valid under the standard axioms.
4. **Verify Axioms**:
   You can verify that no hidden axioms or `sorry`s are used by executing:
   ```bash
   lean --run scripts/verify_axioms.lean
   ```
   Or explicitly inspecting the `print axioms` output for `Zeta23Ext.BandCert.Main`, `Zeta23Ext.RetentionAlgebra`, and `Zeta23Ext.Bridge`.

## Reproducing the Falsification/Methods Finding

The negative finding regarding the validation harness relies on four preregistered experiments using LLM agents.

1. **Inspect the Frozen Protocols**:
   The protocols, prompts, item sets, answer keys, and scorers were committed prior to execution.
   ```bash
   git log -- harness/gate/
   git log -- harness/gate2/
   git log -- harness/gate3/
   git log -- harness/gate4/
   ```
   Verify the frozen SHAs match the executed runs.
2. **Review the Run Artifacts**:
   The raw outputs of the 74 agent runs are stored in the tree. The scoring was mechanical string comparison.
3. **Verify Call Sites**:
   To reproduce the claim that the framework received zero adoption in active research:
   ```bash
   grep -r "run_battery\|validate_battery\|audit_department\|ClaimReport" hunts/
   ```
   This should return no matches, confirming the isolation of the harness from the active `hunts/` research directory.
