# EVIDENCE

This document maps the claims in `CLAIMS.md` to the exact canonical repository evidence supporting them.

## 1. Formalization of the Critical Line Extensions

**Claim**: The `zeta23ext` package builds with zero `sorry`s against Mathlib v4.33.0-rc2, covering the Hardy $Z$-function sign-change proof mechanism, the Davenport-Heilbronn analytic properties, the $k=1$ retention reduction, and `Bridge` identities.

**Canonical Evidence**:
- **Location**: `lean/ZetaLean/`
- **Build Status**: Verified by the operator via `ARISTOTLE-RUNS.md`.
  - The `BandCert` chain (8 modules, 8,704 jobs, `Verify` taking 1,513s) builds cleanly under `v4.33.0-rc2`.
  - `Zeta23Ext/RetentionAlgebra.lean` (Batch 4) builds cleanly under `v4.33.0-rc2`.
  - `Zeta23Ext/Bridge.lean` (Batch 3) builds cleanly under `v4.33.0-rc2`.
- **Axioms**: All declarations use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`). No `sorry`s remain in the `ZetaLean` project tree that builds.
- **Git Provenance**: The migration of these modules to standard Mathlib v4.33.0-rc2 is documented chronologically in `ARISTOTLE-RUNS.md` (Batches 2-6), performed on August 12-13, 2026.

## 2. Necessity of Planted Violations in Verification

**Claim**: Verification harnesses do not inherently improve mathematical claim evaluation compared to naive baselines, and require planted violations to prove discriminative power.

**Canonical Evidence**:
- **Location**: `harness/VERDICT.md`
- **Experimental Protocol**: 74 preregistered agent runs across four independent experimental designs (v1, v2, v3, v4).
- **Result**: The harness never outperformed the naive control. The control baseline was 37 for 37.
- **Planted Violations (v4)**: The final experiment utilized an LLVM IR rewrite dataset where the ground truth was derived from complete enumeration of a 65,536-point input domain. The presence of true positives and false positives (LLVM poison semantics invisible to concrete execution) demonstrated that the control was capable of rejecting flawed reasoning independent of the harness framework.
- **Adoption Metric**: `harness/VERDICT.md` records 0 call sites for `run_battery` / `validate_battery` outside of tests and the harness framework itself. Active research deliberately rebuilt the needed abstractions manually rather than adopting the harness.

## Excluded Evidence (Numerical Candidate)
- The numerical $H = 0.6725106958$ constant is recorded in `hunts/frontier_math/PROOF-LEDGER.md` but is strictly treated as an unsupported candidate. The ledger explicitly states that the assumption "theta enters multiplicatively" is "NOT ESTABLISHED" and "derived nowhere", rendering the candidate numerical result vacuous for publication.
