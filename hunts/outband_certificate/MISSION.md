# outband_certificate: spend the out-of-band fact, or prove it cannot be spent

Hunt #110 (`../outband_intake/`) measured that the unconditional out-of-band positivity of
Baluyot, Goldston, Suriajaya and Turnage-Butterbaugh (arXiv:2306.04799, Theorem 1) is worth
between +0.005 and +0.009 on the unconditional simple-zero proportion, landing the
configuration class in [0.679, 0.682], with 91% of the gain inside the strip alpha in
(1, 1.5]. It also showed why no existing certificate can spend any of it: the inertia lemma
needs a positive semidefinite evaluation form, which forces the window's spectral density
v = phi^2 >= 0 and hence Khat = v*v >= 0 everywhere, and the profile that captures the gain
is not an autocorrelation. Weakening the inner product to an indefinite S breaks the inertia
half of the lemma (witness in #110 section 2). Nothing moved on it between 2026-09-01 and
the day this hunt opened.

This hunt is the step #110 handed forward: either an argument a certificate can use on a
kernel signed only on that strip, or a proof that none can.

**The target is the record, not the whole gain.** The public leader stands at
0.6734164909714992949 (AMTOPA), 0.00036 above this lab's four-point 0.6728470198 and 0.00092
above Theorem D. Spending one eighth of the out-of-band information takes the record. A
finite certificate above 0.6734165 whose only addition to bandwidth-one data is the BGSTB
fact is the whole prize; 0.68 is not required.

**Either answer is a result.** A proof that no inequality reading only the strip positivity
can exceed 0.6725007 is a ceiling theorem of the kind Pub 1 is built on, and it closes the
lane honestly. The hunt is scored on settling the question, not on the sign of the answer.

## What is already known, so nobody rebuilds it

- The LP: `../frontier_math/configuration_lp.py`, `solve(J, X, eps, A_out)`. Out-of-band
  positivity enters as the rows `-(D + tauhat(alpha)) <= 0` for alpha in (1, A_out].
- The measurement and its calibration: `../outband_intake/RESULTS.md` section 1, artifacts
  in `../outband_intake/artifacts/`, every fit in `../outband_intake/refit.py`.
- The obstruction and its witness: `../outband_intake/RESULTS.md` section 2.
- The certificate-to-proportion bridge, proved in Lean for every n >= 2: `../../lean/bridge/`.
  Its hypothesis is the Gram-type finite certificate, which is exactly what a new argument
  has to replace or extend.
- BGSTB Theorem 1, re-derived twice already: `../frontier_math/RESULTS-frontier-math.md`
  section 4. Do not derive it a third time.

## How it runs

This hunt is worked as a node board, `board.json` in this directory, by the lab's runner. A
mapper reads this file, #110, and the two papers, and proposes typed sub-lemmas with edges
between them. Each proposal is judged before the operator confirms it. A prove attempt lands
only when its Lean check passes on a fresh checkout of its branch, with `#print axioms`
reporting only `propext`, `Classical.choice` and `Quot.sound`. An attempt that cannot finish
names what stopped it, and that becomes a task. The root item is a question: it is settled
true by a kernel-checked certificate above 0.6734165 and false by a kernel-checked ceiling at
0.6725007 for the declared class, and both are done.

A candidate inequality is falsified numerically before anyone tries to prove it: on random
configurations, on the #110 witness family, and against the Davenport-Heilbronn rival through
`zeta.epstein.battery`. A candidate that lifts the rival too is prime-blind and dead. Hunt
#110 ran that instrument and did not commit it, so building it, `falsify.py` in this
directory, is the board's first task, checked against the two numbers #110 recorded: the
witness `Q = t[[0,1],[1,0]]`, `S = diag(1,-1)`, `c = 2` at slack +2.0 for t = 1 and -0.5
for t = 1.5, and zero violations of the standard inequality over 4000 random positive
semidefinite pairs.

```huntspec
id: outband_certificate
question: Is there an inertia or isolation argument, valid for a kernel signed only on alpha in (1, 1.5], that lets a finite certificate spend the BGSTB out-of-band positivity, and what unconditional simple-zero proportion does it deliver; or is 0.6725007 a ceiling for every certificate reading only that positivity?
frontier: unconditional record 0.6725007036794116 (AF2026 Theorem D); this lab's four-point 0.6728470198 (Lean, Palomar 000005); public leader 0.6734164909714992949 (AMTOPA); class value with BGSTB positivity measured in [0.679, 0.682] with 91% of the gain inside alpha in (1, 1.5] (hunt #110); bandwidth-one configuration ceiling 0.6818286874638
proposed_attack: (1) signed decomposition, ghat = an autocorrelation part plus a residual supported on the strip, with the residual's inertia counted separately; (2) replace the isolation drop by a moment inequality that reads only the strip positivity; (3) search candidate inequality shapes against the LP scorer, each candidate falsified on random configurations and the #110 witness family before any proof is attempted; (4) whichever survives is realised as a finite inequality of the shape lean/bridge already proves, then formalised in CI; (5) failing (1) to (3), prove the ceiling, that no certificate reading only strip positivity exceeds 0.6725007
dead_routes:
  - Farmer-Gonek-Lee Theorem 1.1 as unconditional input; it is proved under RH
  - re-deriving BGSTB Theorem 1; done twice already in this tree
  - the indefinite-S weakening of the inertia lemma; refuted in hunt #110 section 2 with a two-by-two witness
  - transplanting CGdL section 4 as written; the Gram requirement is the obstruction, not a detail of presentation
  - reading out-of-band data past alpha = 1.5 on the first pass; nine tenths of the value is inside the strip and the rest costs a kernel signed on a half-line
  - any route to 0.70 by widening the band; the sieve wall of frontier_math section 2 stands
required_oracles:
  - the in-band LP reproducing the Montgomery-Taylor dual with the strip constraint off, as a control on every solve
  - the numerical falsifier on random configurations and the hunt #110 witness family, run before any proof of a candidate inequality is attempted
  - zeta.epstein.battery against the Davenport-Heilbronn function, since a candidate that lifts the rival's proportion as well distinguishes nothing
  - a fresh-checkout lake build of the Lean module, with print axioms reporting only propext, Classical.choice and Quot.sound
kill_conditions:
  - a candidate argument passes the Davenport-Heilbronn control, so it is prime-blind and proves nothing about zeta
  - the ceiling is proved, so no certificate reading only strip positivity exceeds 0.6725007; the hunt then closes with that theorem as its result
  - the cumulative spend cap set by the operator is reached with every attempt walled and no sub-lemma landed; the walls are the map and the hunt pauses
agents_may:
  - search, derive, code, attack, falsify numerically
  - propose typed sub-lemmas and edges through the board
  - formalise on GitHub Actions or on a fresh checkout through the board's check, never by reasoning
  - state positions on whether a step is bookkeeping or analysis
agents_may_not:
  - present an RH-conditional input as unconditional, in any sentence
  - claim above measured grade before a kernel-checked artifact exists
  - write language implying any of this bears on RH itself
  - run lake build in the shared checkout; the board's cells build in their own worktrees
  - raise the spend cap, launch a run, or confirm a proposal; those are the operator's
```
