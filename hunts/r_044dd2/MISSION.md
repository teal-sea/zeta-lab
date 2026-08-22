# Hunt R-044DD2: Krenn-Gu 8x3 support frontier

The previous census proved that the choices of one supported monochromatic
perfect matching in each of three colours fall into 31 orbits.  That does not
quotient the full polynomial system.  This hunt asks the narrower next
question: which of those 31 branches survive the support-level necessities
used in the checked 6x3 proof?

```huntspec
id: r_044dd2
question: For each of the 31 S8 x S3 target-matching branches, does any support on the 252 aggregate edge entries survive target nonemptiness, non-target non-singleton cancellation, star-anchor, pair-pencil, and full-column necessities?
frontier: the 8x3 system has 252 complex variables, 6561 degree-four equations with 105 monomials each, and 31 target-matching branches; no support-level cover of those branches is recorded in Zeta Lab
proposed_attack: use lazy exact Boolean constraint generation to minimize support separately in each branch, independently replay every returned support, and retain solver infeasibility only when accompanied by a checkable certificate
dead_routes:
  - treating the 31 target-matching orbits as a quotient of the full polynomial system
  - interpreting a cancellation-closed support as a complex solution
  - accepting solver infeasibility without a replayable certificate
required_oracles:
  - direct enumeration of all 6561 colourings and 105 perfect matchings
  - independent support verifier implemented separately from the optimizer
  - proof certificate checker before any branch is called impossible
kill_conditions:
  - the 6x3 calibration does not reproduce the known support conclusions
  - the independent verifier disagrees with any reported survivor
  - memory exceeds 8 GB without eliminating a branch or returning a verified survivor
agents_may:
  - search
  - derive
  - code
  - attack
  - formalize
agents_may_not:
  - declare novelty
  - declare theorem status
  - promote their own claim
```

## Inherited input

The support necessities are taken from the proof architecture of
`algal/krenn-gu-6x3-certificate`.  They are necessary conditions only.  The
8x3 implementation and replay here are independent code paths.
