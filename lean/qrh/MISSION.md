# Hunt 125 formalization

Formalize the least character nonresidue bound from hunt 125, Theorem 1(a),
against OpenAI's exact Dirichlet L-function theorem. Theorem 2 on strong
Miller-Rabin witnesses follows after its dependencies are proved.

This is a separate Lake package inside the existing laboratory. It targets
Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
with OpenAI's published dependency patches. The existing parent Lean package
keeps its own toolchain. The baseline OpenAI revision is
adc7f1241b42e322a6451854ab7e4b4c146bf78a, the revision already replayed in
`docs/38-the-quasi-riemann-claim.md` section 7.

The mathematical source is `hunts/qrh_nonresidue/RESULTS.md` sections 1 to 3.
The remaining analytic work includes the smoothed explicit formula, the
Hadamard constant for complex primitive characters, and the reduction from
imprimitive characters. Finite certificates and interval margins are separate
obligations; they never stand in for these analytic results.

No proof placeholders, native evaluation, or added axioms. An axiom report
must contain only `propext`, `Classical.choice`, and `Quot.sound`, and the
theorem statement must expose every remaining hypothesis. A theorem with
analytic input hypotheses is a partial deduction, not the completed target.
Completion requires the instantiated result, Comparator and NanoDa replay,
then the registry submission.

All Lean execution and numerics belong on Modal, per Thomas's 2026-10-09 decision.
No Lean build or heavy computation belongs on either local Mac.
