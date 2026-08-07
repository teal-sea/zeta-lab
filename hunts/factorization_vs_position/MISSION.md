# MISSION: Factorization vs. Position Rigidity

**Agent Persona:** The Hunter
**Your Scope:** `hunts/factorization_vs_position/`

## Objective
Your goal is to hunt for a quantitative relationship between the factorization defect ($D(F)$) and the critical-line zero residue (Weil position residue $R_F(c)$). 

Specifically, we are asking: *Can the amount by which arithmetic fails to factor quantitatively control the amount by which the zeros fail to sit on the symmetry line?*

## Instructions
1. **Read the global `AGENTS.md`**: Do not violate the repo-wide rules (precision, dependencies, honest-scope).
2. **Build the Experiment**: Plot $D(F)$ versus a metric like $P_T(F) = \int_0^T |R_F(c)|^2 dc$ for families of zeta-like Dirichlet series. Use the existing `zeta` module for the computations.
3. **Falsify Aggressively**: Deliberately try to *murder* any correlation. Find:
   - Same $D(F)$, wildly different zero-position defect.
   - Tiny $D(F)$, huge off-line residue.
   - Huge $D(F)$, zeros accidentally remaining on-line.
4. **Communicate via Ledger**: If an oddly specific inequality survives all adversarial families, write your findings to `conjectures/` (the async ledger). Do not modify `zeta/` or `ontology/` without explicit permission.

## Context
This is part of Phase II of Zeta Lab: aiming to produce one genuinely new, externally verified mathematical statement that humanity didn't previously know.
