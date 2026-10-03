# Central logarithmic moments, 2026-10-02

Target: the standard Riemann Hypothesis, every zero of zeta in
0 < Re(s) < 1 has Re(s) = 1/2. Proof and disproof are equally acceptable.
This checkpoint explores the central logarithmic moment route. It does not
replace that target with finite matrix positivity.

Scope: this directory, its case-log entry, and generated index if changed.
No paid services, extra agents, recurring jobs, or edits to core mathematics.
Use the existing local Python environment. Source base: origin/main 783307c8.
The session-list tool is unavailable in this runtime; git worktrees were inspected.

```huntspec
id: central_moments
question: Can theta-integral structure prove all central logarithmic moment matrices positive, or produce a negative witness?
frontier: no all-orders positivity argument has been established in this attempt
proposed_attack: derive the moment recurrence, compare direct derivatives and theta quadrature, and challenge positivity transfer with exact controls
dead_routes:
  - finite positive matrices alone do not imply the infinite family
  - prior concavity-only theta shortcuts do not supply real-rootedness
required_oracles:
  - exact rational arithmetic for control matrices
  - independent derivative and quadrature evaluations
  - ordinary proof with explicit dependencies and external review still pending
kill_conditions:
  - a positive symmetric measure with nonreal transform zeros passes the proposed finite sufficiency test
  - independent numerical routes disagree beyond their stated precision target
agents_may:
  - derive identities and bounds
  - run bounded local experiments
  - preserve unresolved obligations
agents_may_not:
  - assume RH or the desired infinite positivity
  - claim novelty from an incomplete literature search
  - promote finite numerical signs into a uniform theorem
```
