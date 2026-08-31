# outband_intake — build the machinery that can eat the unconditional out-of-band fact

Every certificate in the current race reads pair-correlation data on `[-1,1]` and
nothing else. The configuration ceiling for that information class is
`0.6818286874638`, and the whole public race is fighting over the interval from
`0.6725007` to `0.6734165`, a span of `9.2e-4`.

One fact is already known outside the band and needs no hypothesis. Baluyot,
Goldston, Suriajaya and Turnage-Butterbaugh (arXiv:2306.04799, Theorem 1) prove the
weighted form factor is nonnegative for every `alpha`, unconditionally, because
conjugate-closure of the zero multiset writes it as an integral of a square and the
Cauchy weight's poles at `±2i` cover every pair of strip zeros. This laboratory
re-derived that before finding it; `hunts/frontier_math/RESULTS-frontier-math.md` §4
records it so nobody derives it a third time.

Chirre, Goncalves and de Laat reach `0.6792` for zeta with two zero-side inputs:
that positivity, and a diagonal-isolation drop. Their positivity input is exactly the
BGSTB fact, so it costs no hypothesis. Their second input does not transfer, and the
reason is one sentence: their argument counts inertia against a kernel that must be
the Gram matrix of a window family, autocorrelations are nonnegative, and a kernel
with `ghat <= 0` outside `[-1,1]` is not one. Their §4 does not apply as written.

**That single obstruction is this hunt.** It is not a ceiling proof and not a bridge
over somebody's theorem. It is a missing argument, and the thing it would buy is
about `6.7e-3` on the unconditional record, roughly seven times the entire public
race's progress to date.

```huntspec
id: outband_intake
question: Is there a diagonal-isolation argument valid for a kernel with ghat <= 0 outside [-1,1], and what unconditional proportion does the resulting certificate deliver for the simple on-line zeros of zeta?
frontier: unconditional record 0.6725007036794116 (AF2026 Theorem D); public race leader 0.6734164909714992949; bandwidth-one configuration ceiling 0.6818286874638; CGdL RH-conditional 0.6792; LP class value with BGSTB positivity added 0.6863 at (X=80, J=320) and descending in X
data_class: bandwidth-one data plus BGSTB out-of-band nonnegativity only. Every input must be traceable to an unconditional source. F1 beyond the band via Farmer-Gonek-Lee Theorem 1.1, and every CGdL constant that uses it, ride on RH and are inadmissible as unconditional input here.
proposed_attack: measured before analytic, analytic before Lean —
  (1) converge the LP in X with the out-of-band constraint on, and extrapolate the class value the information actually supports, so the prize is a measured number rather than an inherited one
  (2) sweep the out-of-band reach A_out to price the information: how much of the gain comes from the first slice past alpha = 1, and where it saturates
  (3) attack the obstruction directly: find an inertia or isolation count that does not require the kernel to be a Gram matrix. Candidate directions are a signed decomposition splitting ghat into an autocorrelation part and a residual whose inertia is counted separately, and replacing the isolation drop with a moment inequality that reads only the positivity
  (4) if (3) yields an argument, realize it as a finite inequality of the shape the existing certificate pipeline already proves, and only then formalize, in CI
dead_routes:
  - Farmer-Gonek-Lee Theorem 1.1 as unconditional input; it is proved under RH
  - re-deriving BGSTB Theorem 1; done twice already in this tree
  - any route to 0.70 for zeta by widening the band; the sieve wall of frontier_math §2 is quantified and 0.70 needs support near 1.04, which is Hardy-Littlewood grade and does not exist unconditionally
  - transplanting CGdL §4 as written; the Gram requirement is the obstruction, not a detail of presentation
required_oracles:
  - the in-band LP reproducing the Montgomery-Taylor dual with the out-of-band constraint off, as a control on every run
  - monotonicity of the class value under grid refinement, in the direction the discretisation forces; a floor that rises under refinement is a defect, as hunts/frontier_math §5 records at cost
  - any candidate isolation argument tested against the Davenport-Heilbronn function through zeta.epstein.battery before it is believed
kill_conditions:
  - the converged LP value with out-of-band positivity lands at or below 0.6725007, so the information buys nothing this certificate class can spend
  - the obstruction is shown to be essential rather than presentational, by exhibiting a kernel with ghat <= 0 out of band whose inertia count provably fails
  - any candidate argument passes the Davenport-Heilbronn control, which means it distinguishes nothing
agents_may:
  - search, derive, code, attack
  - formalize on GitHub Actions only
  - state positions on whether a step is bookkeeping or analysis
agents_may_not:
  - present an RH-conditional input as unconditional, in any sentence
  - claim above measured grade before an artifact exists
  - write language implying any of this bears on RH itself
  - run lake build locally
```
