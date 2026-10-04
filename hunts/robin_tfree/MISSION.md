# Robin's inequality beyond the verified range, 2026-10-04

Target: the Riemann Hypothesis, through Robin's criterion (RH iff
`sigma(n) < e^gamma n log log n` for every `n > 5040`). This hunt attacks the
unconditional frontier of that criterion: the largest families of integers for which
the inequality is proved without assuming RH. It does not replace RH with a finite
statement, and a larger family is not a step that converges to RH (RESULTS.md, "The
doors", last paragraph).

Scope: this directory, its case-log entry in `hunts/README.md`, one entry in
`docs/37-methods.md`, and the generated `CONTEXT.md`. No core module edits, no paid
compute, no recurring jobs. Base: origin/main `ef4e0564`. Started from a session asked
to "take a stab at RH"; route chosen because the lab had no Robin-criterion hunt and the
published t-free record (21) sat below what Buthe's 2018 bounds appeared to allow.

```huntspec
id: robin_tfree
question: How far does an explicit upper bound on the primorial Mertens ratio past the verified range push Robin's inequality for t-free integers and valuation-restricted integers?
frontier: Robin proved for 21-free integers (Axler 2023) and for n > 5040 with nu_2(n) <= 20 or similar valuation bounds; verified for every n up to 29996208012611 primorial (Morrill-Platt 2021)
proposed_attack: exact first-order cancellation between Mertens' partial-summation boundary term and the log theta denominator, with Buthe 2018 bounds on theta near the verified range and BKLNW 2021 tables beyond
dead_routes:
  - bounding the boundary and denominator terms separately (costs 2.29e-8 at x0, caps t at 24 even with Buthe's constant)
  - Morrill-Platt v1's monotonicity of R_t at primorials (unproved, withdrawn in their v4)
  - any fixed t-free or valuation family as a route to all n (colossally abundant numbers leave every such family)
required_oracles:
  - Arb ball arithmetic for every evaluated constant
  - exact prime data for the identity and for the true E(x) at small x
  - an independent mpmath quadrature route for the integrals
  - published theorem statements quoted with section numbers
kill_conditions:
  - the identity fails on real primes
  - the bound falls below the true E(x) at any x where E(x) is computable
  - an input is misquoted or its range of validity does not cover its use
  - the t = 25 decision depends on the rounding allowances
agents_may:
  - derive and check identities and bounds
  - run bounded local computations
  - search the literature and record its scope
agents_may_not:
  - assume RH or any consequence of it
  - claim novelty beyond the recorded search
  - promote the candidate past ordinary derivation without independent review
```
