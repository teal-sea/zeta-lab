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
route (item E of `probe_37fb06a9.py`) did **not** settle at this cost, which
is reported as such in `RESULTS-37fb06a9.md` rather than dressed as a bound.

---

# Run 2 — `113786a8-1f1c-4220-b772-15160a0274fa`, 2026-08-20

Run 1's artifacts are preserved under their run-tagged names
(`RESULTS-37fb06a9.md`, `probe_37fb06a9.py`, `results_37fb06a9.json`,
`HANDBACK-37fb06a9.json`); the unsuffixed files are this run's.

Between the two runs, `main` withdrew the G4 counterexample (`a735965`) and
closed gap B of `hunts/frontier_math/LATTICE-EXTREMALITY-ROUTE.md`
(`7efd506`) with an explicit Fejér majorant. Run 1's threads 1 and 2 are
therefore answered elsewhere, and the same question — T1's gas half — now
sits entirely on that route's **gap A**, the sparse side `rho < 1/(2*pi)`.

```huntspec
id: r_b9552d-run2
question: what must a Cohn-Elkies certificate be to close gap A of the lattice-extremality route (the sparse side rho < 1/(2*pi)), and can the Fejer family that closed gap B be it?
frontier: gap B closed on main 7efd506 with v = K_1(0)*(sin(x/2)/(x/2))^2, so J(T) <= LP_v(rho) for every configuration at rho >= 1/(2*pi), with LP_v(1/(2*pi)) = L = 0.11433003938654052 the uniform-lattice row; gap A open, the route document's own sparse illustration being +2.15 against a true -0.043 at rho*2*pi = 0.4
dead_routes:
  - per-pair domination, the cap is superadditive above the multiplicity threshold
  - separation hypotheses, real zero gaps have no positive lower bound
  - convex relaxation of the atom constraint, exact rational witness on file
  - Cauchy-Schwarz on the positive-definite kernel, 18x to 111x too weak
  - repulsion-free accounting, arithmetically dead from n=8
  - the G4 1,1,2,1,1,2,3 configuration, withdrawn on main a735965 as a two-sided number compared against a one-sided one
required_oracles:
  - the numpy kernel k1_vec checked pointwise against gram_form.kernel's scalar cmath path
  - the closed forms 2*c2(0), K_1(0) and cos^2(sqrt2/2)*(1+cosh 1) re-measured by independent scans rather than quoted
  - two_species.centre_gas_row_closed as the lattice row L, computed on main and not here
  - a planted-fault ladder on the sup f necessary condition, which must fire before a not-excluded verdict is reported
kill_conditions:
  - sup f exceeds L/2, which would exclude every universal certificate and end the route
  - the bound at c = 2*c2(0) fails to be constant in rho, which would mean the pinning argument is wrong
  - the planted inflation of f fails to fire the necessary-condition test
  - a recorded dead route is being re-derived
agents_may:
  - derive the constants any density-independent certificate must hit, and test them
  - report a family as unable to close a gap, with the frequency-domain witness
  - state a bound weaker than the conjecture when it is the first of its kind on that side
agents_may_not:
  - claim gap A closed, lattice extremality proved, T1 proved, or k >= 3
  - use the reserved certification word
  - describe a scan sup as an enclosure
  - present the quoted Paley-Wiener factorisation and sampling steps as proved here
```

## Kill conditions actually reached, run 2

None fired. `sup f = 0.018743` sits below `L/2 = 0.057165` by a factor
3.05, so the route survives its necessary condition; the planted 3.05x
inflation fires the test, so the test has power.
