# Hunt #90: the ceiling of the leading public claim's own family

`AMTOPA/zeta-exact-pressure` holds the leading public claim for the proportion of
simple zeros, `0.6734164909714992949...`, first in the fifteen-claim ranking this
laboratory's own field audit produced (`hunts/field_audit/RESULTS.md`, Hunt #89).
It is a seven-point / six-gap exact-pressure certificate: a 17-term cosine window,
a nonnegative pair-weight vector on a span-capacity polytope, a nonnegative
position-pressure vector of fixed total, an interval-accepted floor for the local
functional, and a scalar-Gram block assembly.

This hunt runs the `ainta_seven_point` playbook against it: reproduce the headline
on a pinned commit, read the verifier for soundness, then hold their method fixed
and push its free parameters to the ceiling. The question is not whether their
number is right. It is whether their number is the *best number their own
construction can produce*, and if it is not, by how much, and if it is, what is
binding.

The analytic bridge from the finite inequality to a statement about zeros of zeta
is inherited from the Anthropic paper and the Ainta stability refinement and is
**not** audited here, exactly as in Hunt #79. Every constant this hunt produces
inherits that unreviewed bridge and is CONDITIONAL on it.

```huntspec
id: amtopa_ceiling
question: Holding the AMTOPA exact-pressure construction fixed - its 17-term cosine window family, its span-capacity-2 pair-weight polytope, its fixed-total position pressure, its scalar-Gram block assembly - what is the supremum of the proportion that family can produce, is 0.6734164909714992949 at that supremum, and which constraint is binding when it stops improving?
frontier: AMTOPA/zeta-exact-pressure 0.6734164909714992949 at commit 7253fdcab9366af45b8c8caf44e408c0af44a1a7 (checked 2026-08-24, leader of fifteen public claims per hunts/field_audit/RESULTS.md); this laboratory's best 0.6730529829896288869 (eight-point, Lean bridge, tenth of fifteen); the window ceiling HD 1 = 0.6725007036794116457 for the single sqrt(2) term; the bandwidth-one configuration ceiling 0.6818286874638 which no certificate reading only bandwidth-one data can pass
proposed_attack: pin and clone the repository; replay their assembly in exact rational arithmetic with a rational under-estimate of the only square root; reimplement window, kernel and functional independently of their code and compare statistic for statistic; read the C++ branch-and-bound and the mpmath.iv table builder for acceptance direction and float traps; then solve the free parameters - the pair-weight polytope and the position-pressure simplex are exactly a concave maximisation, so cutting-plane linear programming gives their optimum rather than an estimate, and the window coefficients enter H as a Rayleigh quotient with a closed-form maximum
dead_routes:
  - re-running their published nine-point-scale branch-and-bound on the authoring host, which is under a hard local-compute cap and has no Lean
  - promoting a float minimum of the local functional to a floor, which is the one step their own verifier exists to perform
  - raising the window constant H by adding harmonics at frequencies 2*j*pi, which is exactly zero-gain and is proved so in probe_window.py
  - reaching past 0.6818286874638 with any certificate reading only bandwidth-one data, excluded by Anthropic Remark 1.1
  - reopening Hunt #82's barrier against this family; that barrier caps a different family and hunts/field_audit/RESULTS.md section 3 already settled the comparison
required_oracles:
  - the AMTOPA repository's own scripts run on the pinned commit, field by field against their committed certificates
  - their six-dimensional C++ interval branch-and-bound, compiled with -ffp-contract=off, run at a rational target, which fails loudly at a terminal cell when a target is not acceptable at its grid
  - exact rational arithmetic on the assembly formula, with a rational lower bound on the square root and the monotonicity direction asserted rather than assumed
  - linear programming duality: the cutting-plane LP value over a set of real gap vectors is an upper bound on the floor the polytope can reach, independent of any minimiser
kill_conditions:
  - their published headline does not reproduce digit for digit from their published inputs
  - a claimed improvement's rational target is refused by their own verifier at a terminal cell, which would mean our minimiser missed a basin
  - the cutting-plane LP upper bound falls below a floor we claim to have achieved, which would mean the same thing from the other side
  - the pair-weight or pressure optimum found here violates a constraint their own check_candidate.py enforces
agents_may:
  - run their verifier, table builder and checkers at modified candidates and record every field
  - minimise the local functional numerically and report the result as apparent, never as a floor
  - solve the pair-weight and pressure axes by linear programming and report the LP value as an upper bound
  - write a candidate in their candidate.json schema and drive their own pipeline with it
  - state a position on whether their number is at their family's ceiling
agents_may_not:
  - call any figure here accepted, or promote a float minimum to a certificate
  - claim the analytic bridge, which is inherited unreviewed from the Anthropic paper and Ainta and belongs to hunts/ainta_seven_point/TRUST-MAP.md
  - post anything to the AMTOPA repository or any other upstream
  - declare novelty for the window Rayleigh identity without a knownness record
  - promote any constant here into README.md, ROADMAP.md or the funnel
```

Related: `hunts/field_audit/RESULTS.md` (the ranking and the soundness-read house
style), `hunts/ainta_seven_point/MISSION.md` (the playbook this repeats),
`hunts/ainta_seven_point/TRUST-MAP.md` (the bridge nobody in this race has),
`hunts/family_wall/` (Hunt #82, the barrier for the *other* family).
