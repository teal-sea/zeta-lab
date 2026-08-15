# CLAIMS

1. **Formalization of the Critical Line Extensions (Mathlib v4.33.0-rc2)**
   - The `zeta23ext` package, including the $k=1$ retention reduction (`RetentionAlgebra.lean`) and `Bridge.lean` identities, builds with zero `sorry`s against a modern Mathlib.
   - The formalization establishes the Davenport-Heilbronn analytic properties and the Hardy $Z$-function sign-change proof mechanism at kernel grade.

2. **Necessity of Planted Violations in Verification**
   - Autonomous AI verification harnesses do not inherently improve the correctness of mathematical claim evaluation compared to a naive LLM baseline without tooling.
   - Across 74 preregistered agent runs on three subjects, a structured verification framework never outperformed a naive control, yielding identical correctness due to ceiling effects.
   - A verification instrument's silence or failure to find a counterexample is scientifically worthless evidence unless its detection power has been calibrated against explicitly planted violations (e.g., the LLVM IR poison test).

**Excluded Claims**
- Any numerical improvement to the constant $H$ (such as $0.6725106958$) is specifically withheld from publication as it remains a mathematical candidate contingent upon an unproved analytic assumption (multiplicative $\theta$ entry).
