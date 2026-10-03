# Mission: theta sums and the Laguerre inequalities

Target: decide whether every nontrivial zero of the Riemann zeta function
has real part 1/2. Proof and disproof have equal standing. No RH assumption,
equivalent assumption, unproved strengthening, or new axiom may discharge
an open step.

This bounded attempt examines the theta representation of Xi and a proposed
uniform real-rootedness argument. First check the first Laguerre inequality,
then the all-order condition actually sufficient for RH. In particular,
test whether finite theta sums can transfer the needed inequalities to Xi.
Keep any obstruction restricted to the approximation family it concerns.

Compare against the existing central-moment route and arithmetic
log-derivative route before committing further computation. Those records
retain open uniform estimates; repeating their finite scans is not this
hunt's task.

Scope: this directory, its case-log entry, and generated context if needed.
No edits to core mathematics, other hunts, Lean packages, or operating tools.
Use bounded foreground computations only, no paid resources or heavy local
builds. Record estimates and terminal counts in RUNS.md. No formal proof or
external review is presumed. Session-list tooling is not available in this
harness; isolation uses a fresh worktree from fetched origin/main.

```huntspec
id: rh_theta_laguerre
question: Can theta structure establish every Laguerre inequality needed for RH?
frontier: Central moment positivity and arithmetic log-derivative bounds remain open uniformly; this attempt tests a different theta approximation step
proposed_attack: Derive endpoint asymptotics of finite theta sums and test first-order sufficiency with an exact positive-measure control
dead_routes:
  - finite zero or coefficient positivity alone as an unbounded conclusion
  - generic positive-measure structure alone, as tested in central_moments
required_oracles:
  - exact symbolic identities and rational inequalities
  - independent incomplete-gamma and theta-quadrature computations
  - mpmath gamma-zeta evaluations without a supplied zero list
kill_conditions:
  - a proposed sufficient condition holds for a control with explicit nonreal zeros
  - a finite approximation violates the proposed inequality asymptotically
  - independent evaluation routes disagree beyond their stated tolerance
agents_may:
  - derive
  - compute
  - challenge
  - preserve unresolved proof obligations
agents_may_not:
  - declare novelty without a literature search
  - promote an unreviewed claim
  - treat finite sign tests as uniform positivity
```
