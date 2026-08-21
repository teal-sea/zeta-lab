# The two-species form of blocker 2, and the k = 2 case closed at measured grade

**2026-08-15.** Reads: `K2-ROUTE.md` (the state it supersedes in part),
`RETENTION-PROBLEM.md` (the k=1 proof whose machinery this transplants),
`gram_form.py` / `kpair_identity.py` (the identity layer).  Instruments:
`two_species.py`, `k2_closure.py` (+ tests).  Nothing here moves the
reading of record; **blocker 2 (all `k >= 2`) remains open**; nothing here
is evidence about RH.

---

## 0. What is new, in one paragraph

`K2-ROUTE.md` section 2 wrote the budget superadditivity
`Psi(tau,y) = -(1/2)[D(0,tau) + D(2y,tau)]` and stopped at "a direction,
not a schedule".  One line was left on the table: **`D(0,tau) =
-Kpair(tau)` exactly** (`Qim` vanishes at depth 0), so `Psi` splits into a
`Kpair` gain and a doubled-depth damage, and the whole `k`-pair slack
becomes a TWO-SPECIES system — centres are atoms of a second kind, with
the SAME repulsion kernel at 400x the rate and the SAME window damage at
doubled depth (`two_species.py`, identity residuals 1.1e-14 equal-depth,
3.6e-15 general-depth).  The k=1 proof's three pillars (window
confinement, `Kpair` floors, the integer trade) then have exact analogues
for the centre species, and they close the `k = 2, equal-depth` case over
a finite tau-table (`k2_closure.py`).  The `k`-large regime reorganises
too: the binding adversary is the centre gas damaging itself through the
depth-`2y` windows (87.8% of the per-centre budget on the worst uniform
lattice), with atoms poisoned off the tight lattice by the signed field.

## 1. The restatement (identity, checked, sufficient)

    4*slack_k =   2k*Shq(y)
                + 2*sum_{p!=q} Kpair(tau_pq)
                + (1/200)*sum_{a!=b} Kpair(x_ab)
                - 4*sum_{a,p} D(y, x_a - t_p)
                - 2*sum_{p!=q} D(2y, tau_pq)

`D <= Dam` and every dropped credit is nonnegative, so

    (Q**)  4*sum_{a,p} Dam(y, x_a-t_p) + 2*sum_{p!=q} Dam(2y, tau_pq)
             <= 2k*Shq(y) + 2*sum_{p!=q} Kpair(tau_pq)
                + (1/200)*sum_{a!=b} Kpair(x_ab)

implies `slack_k >= 0`.  General depths: the inter-pair kernel splits per
pair as `K_{y_p+y_q} + K_{|y_p-y_q|}` (checked against
`kpair_identity.slack_k`).

## 2. The depth-extended landscape (new territory, measured)

Centre-centre damage lives at depth `2y <= 1`, beyond every proved
constant in the tree.  Measured (`two_species.py`, scan grade):

| object | depth 1/2 (known) | depth 1 (new) |
|---|---|---|
| no-damage radius | 6.0653 (> 28/5) | **5.3984 (< 28/5)** |
| window 0 | [6.0653, 7.0514], w 0.986 | [5.398, 7.285], w 1.887 |
| cap profile sup `Dam/y'^2`, window 0 | 1.759e-2 | 2.073e-2 |
| far constant `sup Dam*(s^2-2)/y'^2` | 0.6220 (proved <= 0.637) | **0.6636 (> 0.637)** |

The depth-1 windows NEST the depth-1/2 windows and the profile grows
mildly and (up to a 9.1e-6 wobble near an edge) monotonically with depth.
The two starred entries are corrections a depth-1 argument must carry:
`no_damage`'s `28/5` and `Wt_tail_le`'s `637/1000` do NOT survive at
depth 1.

## 3. The k = 2 case closes (equal depths, measured grade)

`k2_closure.py` proves-by-table, for all atom configurations, all centre
gaps `tau`, all `y in (0, 1/2]`:

* **tau-table [0, 132], 6601 cells, 0 nonpositive**, in BOTH cap modes:
  - signed-field caps (positive part of `D(.5,x)+D(.5,x-tau)`):
    worst margin **+0.0529** at `tau ~ 12.85`;
  - unsigned caps (independent, more conservative): worst **+0.0033** at
    `tau ~ 6.33`, stable under grid refinement (+0.0039 at cell 0.01,
    x-step 0.005, zones 0.15).
* **tau > 114.2 in closed form**: the windows end at 57.07, no
  cross-centre overlap exists, margin >= +0.081.
* **depth uniformity for free**: every deficit piece is convex in
  `v = y^2` and vanishes at `v = 0` (signed caps are `[a*v - b]^+` with
  `b = Kpair >= 0`), the budget floor is the kernel-checked O8 row plus a
  v-free `Kpair` term — the same section-6 argument as the k=1 proof.

The mechanism at the binding cells, named: at `tau ~ 2*pi` (the
difference-resonance) BOTH sign-ladders of windows merge
(`I_{j+1}` against `tau + I_j` and `-I_j` against `tau - I_{j+1}`) while
the centre pair takes its own depth-`2y` damage at the depth-1 window
peak — three charges stack.  What pays for them: the other centre's NEAR
ZONE sits exactly on the first window, where the signed atom field is
`~ -0.85`, so the resonance that stacks the charges also poisons the
richest windows.  The unsigned pass closes without using that fact; the
signed pass shows the true margin is an order larger.

Controls (`k2_closure.py`, `test_k2_closure.py`):

* (R) the module re-derives the k=1 section-7 window total to all printed
  digits (`8.1383160e-2`), far rows conservative by construction;
* (C2) the accounting dominates the greedy adversary pointwise in tau;
* (C3) the adversary-side planted-damage ladder first fires between 1.5x
  and 1.7x, consistent with the measured relative margin at the greedy
  worst (`4*slack = 0.1275` at `tau = 126.06`);
* (C4) inflating the machine's own caps kills the resonance cell at
  1.02x, consistent with its own worst margin (detector has power).

## 4. What is NOT closed, precisely

* **Unequal depths (`y_1 != y_2`).**  Measured `slack >= 0` on a 9x9
  depth grid at the binding taus (weakest values approach 0 only as both
  depths do, which is the trivial scaling).  The proof route written
  down: every piece is convex in `(v_1, v_2)` — the centre-pair charge
  via `Dam(y_1+y_2,tau) <= 2(v_1+v_2)*prof_1(tau)` and
  `(y_1-y_2)^2 <= |v_1 - v_2|` — so the vertex argument would finish it,
  BUT the honest convex majorant at the `(1/4, 0)` vertex is too fat by
  ~0.015 (the exact vertex value closes at +0.0091; the majorant does
  not).  A sharper majorant or a monotone 2-D cell table is the named
  obligation.
* **`k >= 3`.**  Open.  Section 5 states what the two-species frame
  reduces it to.
* **Hardening.**  Every sup is a scan.  The obligation is the interval
  pass over the same finitely many cells — exactly the O9-table
  technology, in the tau dimension.

## 5. The uniform-k reduction (direction with measured obligations)

The two-species form splits blocker 2 into a centre-gas problem and an
atom problem:

* **(T1) the centre gas.**  `2*sum_{p!=q}[Dam(2y,tau_pq) -
  Kpair(tau_pq)] <= 2k*Shq(y)*(1-rho)` for some atom reserve `rho > 0`.
  Measured: on uniform lattices the per-centre row peaks at spacing
  `6.285` (`2*pi` to 0.03%) at **0.1140 = 87.8% of the per-centre
  budget** as `k -> inf`; irregular occupancy exceeds it (the
  `1,1,2,1,1,2,3` pattern at step `2*pi` reaches 0.1200); mixed depth
  relieves (ratio 0.878 -> 0.578 at y = 0.3).  The gas extremum is an
  optimisation obligation, not a formula.

  **Amended 2026-08-20: the uniform-lattice value is now a formula.**
  The row's summand at `y = 1/2` is exactly `-4*kappa(s)`, with `kappa`
  the same kernel `counting_lemma.py` sums — `Kpair(u) = kernel(0,u)`
  by `d_zero_is_minus_kpair`, and `Dam(1,s) = -kernel(1,s)` wherever the
  rectification is idle, which on this lattice is everywhere (0 clips in
  `d = 1..200`). `counting_lemma` already carries the Poisson collapse
  `sum_{d in Z} kappa(2*pi*d) = 2*c2(0)`, so splitting off `d = 0`:

      row(2*pi) = -4*c2(0) + 2*kappa(0) = 0.11433003938654052...

  Two consequences. The recorded `0.1140` is a `dmax = 200` truncation of
  a `1/d`-decaying sum: it approaches the closed form **from below** and
  understates by `2.85e-4`, which flatters the margin. Corrected, the
  ratio against the per-centre budget is `0.88041`, not `0.878` — still
  below 1, so nothing downstream breaks. And the two modules had been
  summing the same kernel with neither one saying so.

  **Attacked 2026-08-20, and it survived.** `lattice_extremality.py`
  maximised the per-centre cost over `P`-periodic configurations with
  `m = 2..6` centres per period, 300 Nelder-Mead restarts, at the
  one-sided convention `centre_gas_row` uses. Every `m` returned to the
  uniform `2*pi` lattice; the residual shortfalls (`3.6e-6` at worst) are
  optimiser tolerance, with the returned offsets multiples of `6.2832`.
  Three structured families were also swept directly, with no optimiser
  in the loop: alternating gaps (strict symmetric maximum at the lattice),
  dimers (monotone in separation up to `2*pi`), and vacancies (every
  density below, deficit diluting from `3.59e-2` at 4 slots to `9.48e-3`
  at 13).

  The negative result is worth exactly what the detector's power is worth,
  so that is measured rather than asserted: perturbations the optimiser
  resolves at `1e-6` move the objective by `1e-2`, four orders larger. A
  search that could not discriminate would also have found nothing.

  This raises no rung. Lattice extremality remains unproved, the family
  searched is small and explicitly cannot express aperiodic or multi-scale
  structure, and a counterexample would most plausibly live there. Read
  `lattice_extremality.NAMED_GAPS` (L1-L6) before quoting any of it.

  **Route, 2026-08-20.** `LATTICE-EXTREMALITY-ROUTE.md` turns the search
  into an argument. The per-centre cost has an exact structure-factor form
  in which every non-zero-frequency term is a subtraction, `kappa_hat` is
  supported on `[-1,1]`, is positive inside (provably: `c2` is the
  autocorrelation of a strictly positive function) and vanishes at `+-1`.
  The `2*pi` lattice is the unique configuration whose only non-zero
  frequency mass sits on that zero, so it pays no penalty and attains the
  bound, and Newton's identities give uniqueness. This closes the case
  `rho >= 1/(2*pi)` with the rectification idle. Two real gaps remain: the
  sparse side `rho < 1/(2*pi)`, where the bound is vacuous, and the
  rectification, which reduces to a concrete one-dimensional majorant
  problem. Not a completed proof.

  What this does **not** do is discharge T1. T1 asks for a bound over all
  centre configurations; this is the uniform lattice at one spacing.
  Lattice extremality still has no proof (G4's withdrawal removed its only
  recorded counterexample, it did not supply one). Measured grade: every
  number here is double precision, and `2*c2(0)` is quoted from
  `counting_lemma`, not re-derived.
* **(T2/A) the atoms.**  Per-atom extraction is bounded by the SIGNED
  field, `4*[sum_p D(y, x-t_p)]^+`, and the mirror trick caps it by
  `2*sum_j c_j + tails ~ 0.062` per atom UNCONDITIONALLY in `k` — but on
  the gas's own worst lattice the signed field is negative at every rich
  window (`-0.85` at the k=1 peak), which is why the measured binding
  configurations (`k_trend.WITNESS_K12`, `shared_repulsion` n=5/k=23)
  sit on the ridge between tight gas and spread farms.  The k=2 zone
  machinery is the per-cluster instrument for (A) at general k; what is
  missing is the split `rho` and the gas bound (T1).

This reframes `EXTREMALITY_CONJECTURE` (the lattice extremum lives in the
spacing parameter): for the GAS the statement is now a concrete
one-parameter sum to bound; for the joint problem section 8 of
`K2-ROUTE.md` stands — occupancy combinatorics carry the difficulty.

## 6. Honest scope

Grade when this page was written: **measured** (one code path, double
precision, scan sups; two cap modes agree on the verdict; the k=1 arithmetic
reproduced to all printed digits as a cross-check).

**Amended 2026-08-17 (`hunts/r_a97060`).**  The tau-table itself is no longer
scan-grade.  An interval pass over the same 6600 cells, in Arb ball arithmetic
at 96 bits, closes it with **0 nonpositive cells in all three cap modes**:
worst margin +0.0677 (signed field), +0.0146 (unsigned), and +0.0016 with the
1.05 cap pad of the measured pass retained on top of the enclosure.  No cap was
widened, no tau-cell needed splitting, and the enclosure costs a factor of
1.0000 to 1.0004 on the near field.  `mpmath.iv` rectangles contain every ball
checked.  So *"no interval enclosures"* no longer describes the table, and
that step is **enclosure-carrying**.

What is still not hardened, and therefore what the composite claim takes its
grade from: the **v-convexity transfer** from `v = 1/4` to all `y in (0,1/2]`
is an argument, not a table, and the hardened pass evaluates at `v = 1/4`
exactly as the measured one does (`k2_closure.NAMED_GAPS` G3 stands verbatim).
The far rows and the O8 floor are used as the surrounding tree's proved
constants, recomputed in exact rationals but not re-derived.  Not
kernel-checked: nothing here compiles to Lean.  The composite claim "k=2
equal-depth retention holds" still takes the grade of its weakest step, and
that step is now the convexity transfer rather than the table.

`hunts/r_a97060/RESULTS.md` also records two load-bearing assumptions of
`k2_closure.py` that were unstated: the pair-charge clamp `Kpair(min(dmax,6))`
is a lower bound only if `Kpair` is monotone out to `dmax`, which holds here
only because the widest near component in the whole table is 1.9894; and the
inner prune of `zone_trade` is a heuristic restricting the *adversary's*
search.  Neither changes a published number.

The second of those is now settled.  `hunts/r_401bbf/` (2026-08-17) re-solved
the trade on **every** cell of both cap modes by exhaustive enumeration over
all multiplicities with `sum m <= 10`, with both of `zone_trade`'s cuts
removed: max `|delta|` 4.4e-16 across 13200 cell evaluations, no cell above
1e-15, no margin moved, both worst cells unchanged at +0.0528969 and
+0.0032601.  The residual is float summation noise and takes both signs, while
a genuine bite could only be positive.  That pass also gives the reason:
`Kpair` is a square, so every pair charge is nonnegative, and with nonnegative
charges both cuts are admissible for *any* caps, not only the ones this table
builds.  The first assumption, the clamp, is still true only by geometry.

**Amended 2026-08-18 (`hunts/r_b9552d`, run `37fb06a9`).**  Section 5's T1
is now known to be two obligations rather than one, and its `rho` has a
closed-form ceiling.  Splitting `gram_form.budget_gram`'s Gram sums into
diagonal and off-diagonal parts is the identity

    sum_{p!=q}[Dam(2y,tau) - Kpair(tau)]  =  k*Shq(y) - 2B + P,
    P := sum_{p!=q} [-D(2y,tau)]^+  >=  0

(residual 8.0e-15 over 300 random configurations).  `B >= 0` already follows
from `Retention.energy_F_ge`, so **T1 with the signed damage and `rho = 0` is
a consequence of a kernel-checked theorem**, and the whole content of T1 is
the strict positivity of `rho` together with `P`, which is exactly the credit
the `D <= Dam` step discards.  T1 then holds with reserve `rho` if and only if
`rho*k*Shq(y) <= 2B - P`, so `rho <= 2B/(k*Shq)`; on the critical `2*pi`
lattice `P = 0` (measured to `d = 4000`) and `B/k -> c2(0) - A^2` exactly by
defect #24, giving

    rho  <=  2 (c2(0) - A^2) / Shq(1/2)  =  0.153216295...

and `0.119590...` against Lean's proved floor `2 Shq y >= 0.51944 y^2`.  That
replaces the measured "87.8% of the per-centre budget" with a closed form.  It
is a ceiling on the reserve, not a floor, so it constrains a future atom
argument and proves nothing about T1.

That run also **failed to reproduce G4**, the `1,1,2,1,1,2,3` row of `0.1200`
that is the only recorded evidence against lattice extremality: under three
readings of the pattern it measures `0.0666` (gaps, averaged over centres),
`0.0902` (gaps, maximised over centres) and `-1.3600` (site multiplicities),
against `0.1143` for the uniform lattice in the same normalisation.  Three
searches — exhaustive periodic occupancy for periods up to 14, free periodic
with up to 8 free positions in a free period, and free finite `k` — all
returned the uniform `2*pi` lattice, with a planted-fault ladder that first
fires at 1.20x damage against a 1.18x measured margin.  The discrepancy is
recorded, not adjudicated: `0.1200` may be a per-centre maximum rather than
an average, in which case it was never a counterexample to T1, which sums
over ordered pairs.  Until it is resolved, G4 should be read as unverified
rather than as established.  Details in `hunts/r_b9552d/RESULTS.md`.

The quantifier discipline of defect #19 applies verbatim: this is the
**first multi-pair case** of blocker 2, not blocker 2.  The blocker's
statement carries every `k` and per-pair depths; what closes here is
`k = 2`, `y_1 = y_2`, at measured grade, with the unequal-depth and
hardening obligations named above.
