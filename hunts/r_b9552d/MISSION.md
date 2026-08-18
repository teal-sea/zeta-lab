# Hunt r_b9552d — `k >= 3` via the two-species centre-gas split

**Run** `37fb06a9-44a6-42d5-abc3-4c1342b1287b`, 2026-08-18. Reads
`hunts/frontier_math/K2-TWO-SPECIES.md` (section 5, the T1/T2 split),
`hunts/frontier_math/two_species.py`, `hunts/frontier_math/counting_lemma.py`
(defect #24's exact critical-lattice limit).

This is a **probe, not a proof attempt**. `k >= 2` in full has been open for
the life of the frontier hunt; `k >= 3` is not claimed here and is not
closed here. Nothing in this hunt is evidence for or against RH
(`docs/08`). The reserved certification word is not used.

## The question

`K2-TWO-SPECIES.md` section 5 splits blocker 2 into two obligations. This
hunt attacks the first:

> **(T1), the centre gas.** `2*sum_{p!=q} [Dam(2y, tau_pq) - Kpair(tau_pq)]
> <= 2k*Shq(y)*(1 - rho)` for some atom reserve `rho > 0`.

Settle it, or establish exactly where it resists and say so plainly.

## What this hunt may and may not touch

Its own directory, `hunts/frontier_math/` (per the run's scope override),
and a case-log entry in `hunts/README.md`. **Not**
`hunts/frontier_math/zeta23ext/` (another run is live there), and not
`meta/`, `harness/`, `lean/`, `zeta/`, `ontology/`, or any root markdown
file.

```huntspec
id: r_b9552d
question: does the centre-gas obligation T1 of the two-species split admit a bound with a strictly positive atom reserve rho, over all centre configurations rather than only lattices?
frontier: k=2 equal depths closes under ball enclosures over 6600 cells in three cap modes (run 78b4ce8e, worst margins +0.0677 signed / +0.0146 unsigned); k>=3 open; T1 measured at 87.8% of the per-centre budget on the worst uniform lattice, with defect #24 giving the exact critical-lattice limit lim B/k = c2(0) - A^2 = 0.00517169408367867955 by Poisson summation at spacing 2*pi
dead_routes:
  - per-pair domination, the cap is superadditive above the multiplicity threshold
  - separation hypotheses, real zero gaps have no positive lower bound and a positive fraction of GUE gaps fails at any delta
  - convex relaxation of the atom constraint, only integrality pays back the -nA^2, exact rational witness on file
  - Cauchy-Schwarz on the positive-definite kernel, 18x to 111x too weak
  - repulsion-free accounting, arithmetically dead from n=8
required_oracles:
  - the identity residual against gram_form.slack_direct and kpair_identity.slack_k, which no accounting may contradict
  - defect #24's Poisson-summation limit c2(0) - A^2, derived independently of any search here
  - a planted-fault ladder on the configuration search, which must fire before a no-violation verdict is reported
  - the numpy kernel checked pointwise against gram_form's scalar cmath path
kill_conditions:
  - the reduction GAS = k*Shq - 2B + P fails to be an identity to double-precision rounding
  - the configuration search reports no violation at any planted damage inflation, so it has no demonstrated power
  - the run exceeds its time budget with no measured result
  - a recorded dead route is being re-derived
agents_may:
  - restate T1 exactly against the already-proved budget B and measure the residual
  - search the configuration space for the gas extremum and report the search method and its power
  - assess a named proof route and report it dead or open with the witness
  - report that a recorded number did not reproduce, with every reading tried
agents_may_not:
  - claim k >= 3, or claim T1 proved, from any measurement here
  - use the reserved certification word
  - assert that a recorded number is wrong when only a failure to reproduce it was observed
  - describe a scan sup as an enclosure
```

## Kill conditions actually reached

None of the kill conditions fired. The LP assessment of the certificate
route (item E of `probe.py`) did **not** settle at this cost, which is
reported as such in `RESULTS.md` rather than dressed as a bound.
