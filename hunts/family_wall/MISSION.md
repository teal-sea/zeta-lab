# Hunt #84: the wall of the n-point family

Hunt #79 ended with the lab holding the leading certificate at n = 7 and n = 8 and a Lean
theorem (`n_point_bound`, lean/bridge) that turns any n-point certificate into an
asymptotic bound, for every n. Certificates stand at 0.67303 (n = 7), 0.67305 (n = 8,
bound proved), ~0.67307 (n = 9, float only), against the configuration ceiling
0.6818286874638 that bounds everything reading bandwidth-one data. Nobody has asked the
question that decides whether this family is worth another certificate: does
max_p Phi_n at the floor climb toward the ceiling as n grows, or converge an order of
magnitude short of it? Either answer is a result. Convergence short is a barrier
statement for the entire pressure method; climbing means the race is open and the map is
ours. Two deltas (2.39e-5 at 7→8, 1.77e-5 at 8→9) hint at geometric convergence near
0.6731, and two deltas are not evidence.

```huntspec
id: family_wall
question: As n grows, does the n-point pressure family's best bound max_p Phi_n(c*_n, m_cap, p) converge to a limit short of the 0.6818286874638 configuration ceiling, and if so where and at what rate, and what limiting gap structure attains the floors?
frontier: n=7 floor 0.003469942585928755 at p=3400 giving 0.6730297140 (float, certificate accepted at 34697/1e7); n=8 floor 0.004177322102452557 at p=3200 giving 0.6730536541 (float, certificate accepted at 41763/1e7, bound proved in lean/bridge); n=9 floor 0.003927926119847278 at p=4000 on a coarse grid giving 0.6730713860 (float, prior sweep artifact); configuration ceiling 0.6818286874638 (proved upstream; the 0.68185 in the paper's remark carries no proof)
proposed_attack: float floors for n in {9,10,11,12,14,16} over a 10-value pressure grid by multistart plus exhaustive kernel-zero words with per-n alphabet depth set by a measured one-core benchmark; Arb enclosure at every winning point; fit saturating against climbing models on the peak sequence; read the argmin family structure per cell and test the crossover lead (within a family Phi is monotone in p, so the optimal pressure sits at a family switch)
dead_routes:
  - pushing any single n one decimal further, the per-point purse is of order 2e-5 and shrinking
  - claiming the ceiling is reachable or unreachable from the fit alone, a fit on six points is a lead, not a bound
  - seeding symmetric-only, the seven-point floor is non-palindromic and symmetric seeding missed it (TRUST-MAP.md 1.5)
required_oracles:
  - the control cell n=7 p=3000, which must reproduce the Arb value 0.0038262312115073 to 1e-9
  - the prior-sweep cell n=9 p=4000, which this run's finer search must not exceed
  - Arb 256-bit enclosures at every winning argmin, so every float floor carries a rigorous upper bound on inf F
kill_conditions:
  - the control cell misses the known seven-point floor, which would invalidate the optimiser
  - a floor rises with n at fixed coverage, which would mean the seeding no longer finds the family and the trend is an artifact of search failure
  - the fitted models disagree with the measured deltas by more than the spread across seeds
agents_may:
  - run the float sweep on Modal and report every floor as an upper bound on inf F, never as inf F
  - evaluate Phi_n at float floors and label every such value OPTIMISTIC
  - fit convergence models and label the extrapolated limit INFERRED
  - use the proved n_point_bound formula for Phi_n, citing lean/bridge
agents_may_not:
  - promote a float floor to a certificate, that is phase B and runs the sharded verifier
  - state a limit for the family without the INFERRED label until an analytic bound exists
  - claim anything about n not in the grid
  - spend past the stated Modal budget without a new runmanifest saying so
```

Related: `hunts/ainta_seven_point/MISSION.md` (Hunt #79, the parent), `lean/bridge`
(`n_point_bound`, the proved formula this hunt evaluates), `hunts/ainta_seven_point/artifacts/npoint-sweep.json`
(the prior n = 7, 8, 9 sweep this one extends).
