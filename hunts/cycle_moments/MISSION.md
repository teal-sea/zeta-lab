# Cycle moments and simple-zero counting

Started 2026-09-05 under the operator's instruction to pursue substantive
mathematical research with the available provers and compute resources.

Question: can genuine joint correlation information improve the simple-on-line
zero bound through a higher-degree concave spectral score?

Immediate objects are an exact finite-dimensional counting inequality, its
Montgomery-Taylor triangle term, and the arithmetic estimate needed to use it.
The finite inequality is useful only if it exposes a concrete path to a gain.

Research writes belong in this directory, with one case-log entry in
`hunts/README.md`. Read the existing bridge and public papers;
do not alter established proofs or ongoing reversal-minimax work. External
prover jobs must retain their job identifiers and inputs here. On 2026-09-05,
the operator authorized pushing this research record and merging it into main.
No change to the laboratory's advertised zeta bound is authorized by this hunt.

Proof obligations: retain multiplicities and nonreal conjugate pairs; use the
same operator and height weights for all moments; check Fourier support before
invoking a correlation theorem. A finite or random-matrix example does not
establish an asymptotic zeta estimate.

Validation: independent symbolic identities, exact finite matrix examples,
interval evaluation of explicit constants, and a Lean attempt on the finite
theorem. Record mathematical gaps beside the proposed application.

```huntspec
id: cycle_moments
question: Can joint cycle moments strengthen simple-real counting beyond its quadratic bound?
frontier: The second-moment argument gives the Montgomery-Taylor constant; higher matched moments require separate estimates.
dead_routes:
  - Second and third limits alone cannot force a fixed gain in the signed-vector class, by the exact two-pair construction.
required_oracles:
  - Lean kernel checking with standard axioms only
  - Independent symbolic matrix identities and direct complex cycle sums
  - Interval arithmetic for explicit trigonometric constants
kill_conditions:
  - An admissible finite configuration violates the proposed counting inequality.
  - Fourier support exceeds the correlation theorem being invoked.
  - Moments use incompatible operators, multiplicities, or height windows.
agents_may:
  - Derive and test finite inequalities inside this hunt.
  - Formalize explicit mathematical statements and retain their exact scope.
  - Run bounded numerical experiments on the authorized cloud account.
agents_may_not:
  - Change the advertised zeta proportion without the missing analytic estimates.
  - Claim novelty from an incomplete literature search.
  - Modify other hunts or the core packages.
```
