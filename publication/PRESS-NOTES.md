# PRESS NOTES

## One-Sentence Description
Zeta Lab formalized new extensions to the Riemann zeta critical line theorems in Lean 4, while simultaneously proving that AI verification harnesses require explicit "planted violations" to be scientifically useful.

## 50-Word Description
Zeta Lab has successfully kernel-checked extensions to the Riemann zeta critical line theorems in Lean 4. In parallel, rigorous experiments demonstrated that complex AI validation frameworks do not inherently improve mathematical correctness over naive baselines. We establish that verification tools are meaningless unless calibrated against planted structural violations.

## 150-Word Description
Zeta Lab reports two major findings from its AI-assisted computational mathematics exploration of the Riemann zeta function. First, the laboratory formalized critical analytic properties of the Davenport-Heilbronn framework and the Hardy $Z$-function sign-change mechanism into Lean 4, successfully compiling the `zeta23ext` package against modern Mathlib with zero `sorry` axioms. Second, the laboratory rigorously tested the assumption that AI-driven "verification harnesses" improve claim accuracy. Across 74 preregistered agent runs, the harness never outperformed a naive control model, which achieved 100% accuracy. This negative result establishes a critical methodological principle: in automated mathematics, a verification instrument's failure to find an error is not evidence of correctness unless the instrument's power has been explicitly measured against planted structural violations. Notably, the lab maintains strict boundaries, actively withholding an improved numerical candidate for the gap between consecutive zeros because it relies on an unproved analytic assumption.

## Technical Summary
The `zeta23ext` package, encompassing the Davenport-Heilbronn analytic properties, grid-incidence laws, the $k=1$ retention reduction, and the Hardy $Z$-function sign-change mechanism, has been successfully ported and kernel-checked in Lean 4 against Mathlib v4.33.0-rc2 using automated agents. Independent verification experiments using LLM agents over 74 preregistered runs on bounded tasks demonstrated that an extensive validation harness yielded no statistical improvement over a naive control. Consequently, verification instruments lacking measured power against planted violations (e.g., LLVM IR poison semantics) are deemed scientifically insufficient for falsification.

## Nontechnical Summary
Zeta Lab used AI to translate complex mathematics about the famous Riemann zeta function into a computer code that perfectly proves the math is correct without any assumptions. At the same time, we tried using AI "checkers" to automatically find mistakes in math claims. We discovered that these complex AI checkers didn't do any better than a basic AI, and we proved that you can't trust an AI checker unless you first hide a deliberate mistake to ensure the checker can actually find it.

## Key Claims
1. Formalization of key Riemann zeta critical line components (Davenport-Heilbronn framework, $k=1$ retention reduction) into Lean 4 (Mathlib v4.33.0-rc2) is complete and kernel-checked.
2. AI-assisted validation harnesses do not intrinsically improve correctness in mathematical evaluation due to ceiling effects.
3. Verification tools require calibration against explicitly planted violations to establish discriminative power.

## Caveats
- The numerical candidate $H = 0.6725106958$ for the liminf bound on consecutive zeros remains unverified. It rests on the unproved assumption that the retention parameter enters multiplicatively. This is explicitly withheld from the publication's theorems.
- Falsification harness findings are limited to the three experimental subjects and 74 agent runs evaluated.

## Chronology
- The formalization port and harness demotion occurred in August 2026.
- The `ARISTOTLE-RUNS.md` records detail the automated agent porting of `BandCert` and `RetentionAlgebra.lean` on August 12-13, 2026.
- The verification harness verdict was finalized on August 13, 2026, based on frozen protocols.

## Links to Repository Evidence
- Canonical Scientific Source: `teal-sea/zeta-lab`
- Lean proofs: `lean/ZetaLean/`
- Falsification Verdict: `harness/VERDICT.md`
- Porting/Execution logs: `lean/ARISTOTLE-RUNS.md`

## Q&A
**Q: Did you prove the Riemann Hypothesis?**
A: No. We are exploring the critical line and formalizing established analytical properties (like the Hardy Z-function sign-changes), not proving or disproving RH.

**Q: Did you improve the consecutive zero gap constant?**
A: We identified a candidate improvement computationally ($H = 0.6725106958$), but it relies on an unproved analytical assumption. Because we cannot formally prove that assumption, we are not publishing the constant as a theorem.

**Q: Why is the AI validation harness failure important?**
A: It shows that simply adding more complex AI review layers doesn't automatically make math checks more accurate. It introduces the vital scientific standard that automated checks must first prove they can catch deliberate, hidden errors before their "approval" means anything.
