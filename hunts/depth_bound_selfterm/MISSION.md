# depth_bound_selfterm: measure the mirror-pair self-term for the outband kernel

**Status, 2026-09-14: closed at measured grade.**

The depth-bound lead identified in `docs/35-the-unspent-fact.md` suggests that the out-of-band positivity might survive under a bound on off-line depth. This hunt measures the mirror-pair self-term $S(y) = g(iy)$ of the strip-signed dual kernel in `hunts/outband_certificate/artifacts/dual-x80.json`, against the in-band control in the same artifact.

```huntspec
id: depth_bound_selfterm
question: What is the mirror-pair self-term S(y) as a function of depth for the strip-signed dual kernel and the in-band control, what are their crossing depths, and in which depth frame is that crossing stated?
frontier: measured crossing depths for dual-x80.json data[1]; in-band control data[0] has no crossing on [0, 1.5]
proposed_attack: (1) S(y) for data[1] by discrete summation with h = X/len(x); (2) the same formula on data[0] (z empty) scanned on [0, 1.5]; (3) first drop below r(0) and below 0 found by a scan of step at most 0.005 then bisection; (4) second route at mp.workdps(40) beside numpy float64
dead_routes:
  - hardcoded None crossings for a cos(sqrt(2) u) window that is not the artifact control
  - root_scalar on hand-picked brackets presented as the smallest y
required_oracles:
  - discrete evaluation of S(y) = g(iy) matching hunts/outband_certificate/dual.py
  - numpy float64 and mpmath workdps 40 as independent routes
kill_conditions:
  - the two routes disagree on a dual crossing by more than 1e-8
  - the in-band control is found to cross on [0, 1.5] after a dense scan
agents_may:
  - read dual-x80.json
  - compute self terms, scan for roots, and write RESULTS
agents_may_not:
  - commit, push or modify git state
  - modify zeta, ontology or harness
  - claim results bear on RH
```
