**Status, 2026-10-27 (correction; everything below this paragraph is kept as written).** The
fourth unit's reading of run 40371181784 (PREREG row D1 at every c, ε_q a bound, the counts C_N(ε))
is **not established**. The code's Gauss bound was the (n + 1)-point bound applied to n-point rules,
so every quadrature radius, and with them ε_q, was up to ρ² = 225 times too small (BOUNDS.md s5).
**E2 is unresolved again** until a rerun with the corrected bound, at 13 nodes per panel, is read
(RUNS.md s12). The rerun was launched, not read. Lines 1 and 5 below ("priced, not run"; "E2
unresolved, paused by allocation") are the first unit's and were stale after the fourth; this
paragraph gives the state. Nothing here is a claim about RH.

1. **The exact-Gram rebuild is priced, not run.** One block (128 s-nodes, every w-node, 280 modes) costs 258 s at dps 40 and 340 s at dps 60 on one core of the box, under 0.8 GiB. The full 280-mode rebuild on the pre-registered grid (S' = 10^4) is estimated at about **155 core-hours**, including a dps-60 replay of every 16th block. It fits GitHub Actions as 7 jobs of 6 h. The products are 24 times faster per operation than the record's 200 core-hour figure assumed; the wider grid PREREG needs takes most of that back (RUNS s1, s2). Grade: measured timings, estimate by stated scaling.
2. **The reading is fixed before any rebuilt row exists** (PREREG, commit 74c788ded): exact inertia of the rebuilt centre shifted by ε = ε_q + ε_t + ε_aux, on the full space, V_4 and the continuous windows H, with no band. Decision table: D0 (the rebuild does not close), D1 (E2 closes below 1.18e−2, a statement about the 280-mode object only), D2 (closes at or above it), D3 (with a truncation bound, a growth G = C_32 − C_16 ≥ 2 counts against bounded rank under the operator's ruling).
3. **The (U-S) gate now refuses DH as well**, which checker/'s gate never held: a composite atom at n = 6, Λ_DH(6) = (1 + κ²)(log 2 + log 3), decided exactly, and two_adic/'s validator refuses DH's 2-adic data at degree 1. Epstein (1,1,6) (n = 6, n = 8) and W_a (n = 2) are still refused, ζ and Dedekind accepted (`test_exact_gram.py`). Grade: exact.
4. **The truncation lemma, first pass** (LEMMA.md): on the full window space a bound of mechanism 2's shape is at least 0.1313 at 280 modes (bound_trunc/ Prop 4), 11 times the scale, so that route is **obstructed in a restricted class** there, conditional on Prop 4 (unreviewed). On H the size is 0.0063, **unresolved**, and the missing step is named: a Mellin-frequency localization of the prolate tail, by a turning-point bound and non-stationary phase. About two agent-hours of the five-day allowance were used.
5. **Open:** the compute ask (RUNS s4) and the prerequisites P1 to P4 that must be committed before any production block; the mode-count sweep costs 341 to 3,636 core-hours, not the 100 to 300 the brief estimated. ALIGNMENT s5: E2 **unresolved, paused by allocation**. Nothing here is a claim about RH.

# RESULTS: exact_gram/, 2026-10-26

Folder of the compute sweep's C4 resumption (MISSION.md). Pinned by
`test_exact_gram.py`: the block timings and estimates (`price_block.json`,
`estimate.json`), E1 at the registered and stored S, the stored-row context
of PREREG s2.4 (slow test), the gate cases, the guard and checkpoint
behaviour, and LEMMA's readings of Proposition 4.

## The doors

This folder measures a cost ceiling (what the rebuild costs on this
construction), not a mathematical one.

1. **Active constraints at the estimate**, ranked by share of a block:
   the hat products (62 percent at dps 40, ∝ nw · nvec), the Python-level
   phases (37 percent, ∝ nw, independent of nvec), then ρ and the window sums
   (1 percent). Across the build, S' binds: it is set by bound_quad/'s crude
   E1 (m ≤ nvec), and it takes the rebuild from about 20 core-hours at the
   stored S to 155 at S' = 10^4. Across the sweep, Kmax = kmax_for(nvec)
   binds: nw doubles per step.
2. **Frozen constants:** S' = 10^4 (genuine trade: a tail-mass lemma for E1
   trades a derivation for a factor of about 7); block size 128 and w-chunk
   8192 (memory against Python overhead); s-panel width 1/2 with 8 nodes
   (Gauss error against nodes; P3 decides it); dps 40 production with a
   dps-60 replay of one block in 16 (rigour of the replay against 8 percent
   more cost); nvec = 280 (the record's build; the truncation side decides
   whether more modes are needed); the E1 target 7.0e−4 in the sweep.
3. **Information class:** every door stays inside the data the construction
   already reads (the prolate modes, the 2-adic factor of ζ, the windows),
   except the truncation lemma's H restriction, which changes the space
   counted on, not the data. The phase cost could fall by a factored
   (NUFFT-type) evaluation of w^{−is} on dyadic levels: not measured, an
   implementation door, same information.

A measured cost is not a lower bound on cost: candidate, at the parameters
above, estimate grade.

## Update, 2026-10-26 (second unit): the bounds, the toy rebuild, the workflow, the tail mass

Lines 1 to 5 above are kept as written. This section adds; each item gives
its grade.

1. **P1, P2, P3 close** (BOUNDS.md s1 to s3; derived, unreviewed, on two
   cited Bessel inequalities spot-checked against arb). P1 (Gauss panels in
   w, Bernstein ellipse) sums to below 1e−15 per hat on the production grid.
   P2 (integration-by-parts and series remainders) closes at the rebuild's
   choice of M (below 1e−20 at the highest mode). P3 needed PREREG
   amendment 1 (9ab86b1d0, before any row): the Gauss s-panels do not admit
   a usable analytic bound, while the uniform trapezoid at the same 16 nodes
   per unit has an exact Poisson aliasing formula. Its bound is sharp on a
   model case, and its planted variant (e^{−U/2}) is caught.
2. **P4 is half closed.** G_z closes. On four prolates it contains the
   identity in every entry, an independent check, since double
   orthogonality is used nowhere. That check caught a real defect first:
   float64 panel midpoints left ulp gaps the balls could not see, and G_z
   excluded 1 by 2e−16 (BOUNDS s1.1, now a planted-fault test). G_b's
   quadrature region is built; its regions B and C (integration by parts at
   frequency 2^m, m up to about 50) are not, so production stays at
   PREREG row D0.
3. **rebuild.py runs end to end at toy size**: gate, Gram, hats with P1 and
   P2 radii, ρ, window sums, checkpoints, replay, assembly with ε_q. Its
   tests catch a key moved mid-shard, a stale checkpoint, a missing shard,
   a planted hat error (by the dps-60 replay), the rivals at the gate
   (W_a, Epstein (1,1,6), DH) and any provider that is not a bound. The
   guard's first committed version keyed folder-relative paths and so never
   found its root. A test that skipped instead of failing hid it, and the
   test no longer skips.
4. **The workflow** was reviewed with changes requested (resume across
   attempts, a calibration mode, 25 percent headroom, 36 shards at
   max-parallel 6, and memory limits checked fail closed); all are made and
   pinned. No RUN_REQUEST.json exists; the calibration waits for P4.
5. **The tail-mass step closes as an identity** (LEMMA.md s5): with the
   trapezoid, the omitted tail is nvec + alias minus the inner sum the run
   computes, so E1 is a posteriori. Measured for the ζ family at 280
   modes: m_z = 21.8 at S = 2266 (crude: 280). It re-prices the rebuild
   from about 155 to about 28 core-hours and the sweep from
   341 to 3,636 to **72 to 844** core-hours (RUNS.md s8). Grade: identity
   derived and unreviewed; masses measured.

### The doors (updated)

1. **Active constraint:** P4's G_b regions B and C, now the only step
   between the record and a run. After it, the calibration on a real
   runner, which sets the shard count.
2. **Frozen constants, changed:** S' now follows the a posteriori tail
   (2,700 at the E1 target 7.0e−4; genuine trade: target against cost,
   about S'^{−3}). Δ = 1/16 (aliasing about e^{−2π/(3Δ)}, about 1e−4 in norm at
   280 modes; genuine trade against nodes). The rest as before.
3. **Information class:** unchanged. The closed-form ζ hats (Tate) are an
   implementation door: they could replace the ζ half of the w-quadrature
   in the rebuild (no E3, E4 there). The b hats still need it.

## Update, 2026-10-26 (third unit): P4 closed, the disk table

1. **P4 is closed** (BOUNDS.md s4.5, s4.6). G_b's regions B and C are
   built by integration by parts against the expansion of the fast factor,
   using endpoint derivative tables up to R = 120, m_max = 101 and
   t_max = 125 at target 1e−20. The m and t tails are bounded by Landau.
   Each region overlaps direct quadrature at toy size, and each region's
   planted fault is caught. The whole G_b passes a two-route Plancherel
   check against the hats. **PREREG row D0's precondition is lifted.**
   Whether a rebuilt row closes is the run's to say. Grade: ordinary
   argument, unreviewed; the checks are measured.
2. **The toy now runs as a bound**: with the exact provider, 2 modes, it
   assembles with `is_bound` true and a finite ε_q (`test_rebuild.py`,
   slow).
3. **The disk-backed mode table** is built, sha256-checked at open and
   streamed. At 20 modes, measured: 184 bytes per ball in memory against
   40 on disk, plus 67 MB per block streaming. At 280 modes the in-memory
   table would be about 12.8 GB per process, against about 2.6 GiB on disk
   (extrapolated). Its first version truncated a level written in more than
   one chunk, which the toy test caught.
4. **The Gram's production cost** is about 23 to 25 core-hours (estimate
   from 280-mode units measured on this box), sharded into 24 parts with a
   merge job. The calibration ask is sent with its exact request; no
   RUN_REQUEST.json is committed.

## Update, 2026-10-27 (fourth unit): the full rebuild and its rows

Everything above is kept as written; one figure there is superseded below
(item 5).

1. **The full 280-mode rebuild ran** (GitHub Actions run 40371181784,
   success, attempt 1, 11.96 h wall). All 338 blocks finished, all 22
   dps-60 replays intersected the production balls (PREREG s4 item 1),
   and every artifact matched GitHub's digest. The shard processes used
   132.0 CPU core-hours against about 104 projected. The 25 percent
   headroom rule was broken: one job ended 4.2 percent under the 350-minute
   cap. The main cause is contention when three replay blocks share a
   runner, but one job is not explained by that (RUNS.md s11.6). Grade:
   measured.
2. **PREREG row D1 at every c**: ε_q is finite, is a bound
   (`is_bound`), and sits below the 1.18e−2 scale for every N:

   | c | ε_q, max over N | below the scale by |
   |---|---|---|
   | 2.2 | 9.22e−4 | 12.8× |
   | 2.5 | 7.83e−4 | 15.1× |
   | 2.9 | 6.66e−4 | 17.7× |

   ε_t is null, so D3 is not read and no growth G is stated.
3. **The counts C_N(ε) = n_−(R_centre + εI)** at ε = ε_q + ε_aux, plus
   bounds on |Im ΔT| (below 6e−36) and on the asymmetry (0). Each is an
   exact rational inertia; the counts on V_4 are decided by ball
   elimination:

   | c | N = 8 (full, H, V_4) | N = 16 | N = 32 |
   |---|---|---|---|
   | 2.2 | 4, 4, 2 | 7, 6, 4 | 18, 18, 16 |
   | 2.5 | 5, 5, 3 | 10, 9, 8 | 21, 20, 20 |
   | 2.9 | 5, 5, 3 | 11, 10, 8 | 23, 22, 20 |

   By PREREG s2.3, these are **statements about the 280-mode object
   R^(280) = Q − T∞ − ΔT_280,exact only**. Every R within ε of the rebuilt
   centre has at least these many negative eigenvalues on that space.
   They say nothing about R_S: the mode limit stays bound_trunc/ claim (i)'s
   unproven assumption. The stored record's 4, 10, 20 at c = 2.9 were read
   on the stored centre with a band, a different object and a different
   rule, so the two rows are not compared count by count here.
   Grade: the inertia is exact and the ΔT enclosures are carried in balls.
   ε_q rests on BOUNDS.md P1 to P4 and LEMMA.md s5's tail identity, which
   are derived and unreviewed, so the composite takes that grade.
4. **The stored-row comparison** (PREREG s4 item 2, float64, measured):
   ‖centre(ΔT_rb(2.9, 32)) − ΔT_stored(280, 2266)‖₂ = 5.15e−3, inside
   band + ε_q = 8.87e−3. The band did not understate the stored error at
   that build. The two norms are 0.4818 (rebuilt) and 0.4830 (stored).
5. **The calibration's Gram** cost 13.1 core-hours (run 40342895119),
   against the 23 to 25 estimated in the third unit, item 4.
6. **Pinned** (`test_read_rows.py`): the rows file and the exact centres
   (`rows_40371181784.json`, `centres_40371181784.json`) are checked by
   sha256. The D1 rule is re-applied to the recorded ε, with the scale
   added as a planted fault (it must read D2). The N = 8 counts are recounted
   from the centres, and a planted −1e−2·I shift must raise them. The N = 16
   and N = 32 recounts run in the slow tier.

### The doors (updated)

This folder's reading is now a measured bound row, not a ceiling. Rows:
candidate D1 at c = 2.2, 2.5, 2.9, N = 8, 16, 32, 280 modes, S' = 2,700.

1. **Active constraints**, ranked:
   - **ε_t (the truncation lemma) binds the reading.** It alone separates
     D1, about R^(280), from D3, about R_S. LEMMA.md left it unresolved on
     H, with the missing step named.
   - Within ε_q, the a posteriori tail dominates: at (2.9, 32) it is
     6.62e−4 of 6.66e−4, against a P3 alias of 1.3e−6 and a ball radius
     of 2.9e−6.
   - The N = 32 counts are ε-sensitive. R_centre has 25, 25 and 27
     negative eigenvalues at c = 2.9, 2.5 and 2.2 against C_32 = 23, 21
     and 18, so a smaller ε could only raise C_32, by up to 2, 4 and 9.
     At (2.5, 16) the last surviving eigenvalue clears −ε by about 5e−6
     (float, measured).
2. **Frozen constants:**
   - S' = 2,700. A genuine trade: the tail falls about as S'^−3, against
     cost linear in S'.
   - Four processes per runner, with a replay every 16th block. A genuine
     trade, now measured: when replays coincide they cost up to about 1.9×
     wall. Placing the replays apart is free.
   - nvec = 280, the truncation side's to decide.
   - Δ = 1/16, unchanged.
3. **Information class:**
   - S' and the placement of the replays stay inside the data already read.
   - ε_t needs a new derivation, possibly on H only, which changes the
     space counted on but not the data.
   - More modes reads more of the same prolate family.

A finite bound row is not a uniform statement and not an RH result; the
allocation of the next step is the owner's.

## Correction, 2026-10-27: the Gauss bound, what the fourth unit does not establish, and the rerun

Everything above is kept as written. This section supersedes parts of the
fourth unit and of the first unit's top lines, and quotes each part it
corrects. Grade: the defect and its fix are an ordinary argument
(unreviewed) with measured checks; the withdrawal is exact (a stated bound
that was not one).

### 1. The defect

An adversarial review of PR #362 found that `bounds.gauss_panel_error`
coded (h/2)(64/15) M ρ^{−2n}/(ρ² − 1) for the n-point Gauss rule. That is
the bound of the (n + 1)-point rule; the n-point bound is ρ² larger. It was
verified here independently: derived from the Chebyshev expansion, and
broken by T_24 at 12 nodes (error 1.54 against 0.267 at ρ = 3 and 0.0095 at
ρ = 15) and by exp(3x), a non-polynomial integrand (9.1e−20 against
7.4e−21 at ρ = 15). BOUNDS.md s5 has the derivation, the cases and the
fix. It entered P1 (E3, the w-quadrature of the hats) and P4's quadrature
(G_z on [1, 2^14] and G_b's region A). At ρ = 15 it made every committed
`gram.json` radius about 225 times too small: at (0, 0), 9.97e−12 (G_z) and
5.97e−11 (G_b) against about 2.2e−9 and 1.3e−8 under the corrected bound at
12 nodes.

### 2. What is withdrawn

The fourth unit, item 2, as written:

> **PREREG row D1 at every c**: ε_q is finite, is a bound
> (`is_bound`), and sits below the 1.18e−2 scale for every N

**Corrected:** ε_q of run 40371181784 is **not established as a bound**,
so the D1 reading and the counts of item 3 (for example 18, 18, 16 at
c = 2.2, N = 32 and 23, 22, 20 at c = 2.9, N = 32) are not established
either. The doors' "a ball radius of 2.9e−6" at (2.9, 32) was computed with
the defect. The files `rows_40371181784.json` and `centres_40371181784.json`
stay as the record of what that run computed. The defect touches radii only,
so the centres are what the run computed; the ε in the rows file is not a
bound. `test_read_rows.py` pins those files as a record, not as a result.

The review's estimate, which is not a result of this folder: with every
radius 225 times wider at 12 nodes (it added 224 times radius_F to ε, an
upper estimate of the change), the worst ε is about 1.5e−3, still below the
1.18e−2 scale, but several counts drop. At c = 2.2, N = 32 the counts would
fall from (18, 18, 16) to about (15, 15, 13).

### 3. Raised, not reworded: the rerun

The corrected bound at 13 nodes equals the old formula at 12 term by term
(same panels, ρ and M), so a rerun at 13 nodes per panel, in the hat table
and in the Gram, carries the radii run 40371181784 reported, now as bounds,
for 13/12 of the cost of the affected work. The Gram is recomputed: the
committed `gram.json` is not this request's (its key has no
`gram_per_panel`), and its radii are not bounds. The grid, the cells and the
reading (PREREG s2 to s4, `read_rows.py`) are those of run 40371181784.
The rerun is priced and launched in RUNS.md s12, and its outcome is
recorded there and here when it is read. Until then E2 is **unresolved**
(ALIGNMENT s5) and no count is stated.

### 4. Three deviations from PREREG in run 40371181784

The review found these. Each is recorded here; the rerun changes the second
and the third.

1. **S' = 2,700.** PREREG s1 registered S' = 10^4, with S' = 2266.1 as the
   one alternative if a tail-mass lemma was committed before production.
   The run used 2,700, set by the a posteriori tail (LEMMA.md s5, RUNS.md
   s8) for the E1 target 7.0e−4, which is neither registered value. The tail
   term is a posteriori and inside ε_q, so the deviation is in the grid, not
   in what ε_q covers. The rerun keeps 2,700, so the deviation applies to it
   too: at 10^4 it would cost about 5.7 times as much (blocks and w-nodes
   both grow), and its rows would not be comparable with run 40371181784's.
2. **The Gram inverse.** PREREG s1: "each must pass a ball Cholesky
   (positive definiteness decided in balls) or the rebuild stops", and
   "ρ_Q(s) = ŵ(s)* G^{−1} ŵ(s) by triangular solves with the ball Cholesky
   factor". `rebuild.setup` used `Gz.inv()` and `Gb.inv()`. A ball inverse
   also encloses G^{−1}, so this does not by itself invalidate ρ's
   enclosures, but positive definiteness was never decided. The rerun
   decides it by a ball LDLᵀ (`bounds.ball_pd`: every pivot > 0, or the
   rebuild stops), in the merge job and in every process's setup. ρ is
   still formed with the ball inverse; that route deviation stays.
3. **Replay blocks' own sums.** PREREG s6: "Every 16th block (the replay
   set, s4) also keeps its own block sum." The checkpoints kept running
   sums only. Every block's checkpoint was uploaded, so a replay block's sum
   could be recovered as the difference of two running sums, but it was not
   kept as registered. The rerun keeps it in the checkpoint
   (`replay_block_sums`), which also lets the workflow upload only each
   shard's last checkpoint.

### 5. Wording the review asked to fix

Each is quoted, then corrected.

- First unit, lines 1 and 5: "The exact-Gram rebuild is priced, not run"
  and "E2 **unresolved, paused by allocation**". Both were stale after the
  fourth unit. The status paragraph at the top of this file now gives the
  state.
- Fourth unit, item 2: "ε_q is finite, is a bound (`is_bound`)".
  `is_bound` is a flag that the exact Gram provider ran, not the toy
  `toy-region-a`. It records which provider ran and checks nothing about
  ε_q. Whether ε_q bounds anything rests on BOUNDS.md, which this
  correction found wrong at P1 and P4.
- Fourth unit, item 3: "Each is an exact rational inertia; the counts on
  V_4 are decided by ball elimination". The counts on the full space and on
  H are exact rational inertia (LDLᵀ over ℚ). The counts on V_4 are decided
  by ball pivots (`read_rows.v4_inertia`, at the first precision where every
  pivot excludes 0), not exactly. "Each" wrongly covered V_4.
- Fourth unit, doors: "This folder's reading is now a measured bound row,
  not a ceiling". A bound row is not measured. It was a candidate bound row
  (enclosure-carrying, resting on unreviewed derivations), and after this
  correction it is not established.
- `hunts/README.md`, the case-log line "ε_q is a bound, at most 9.2e−4"
  carries a dated correction there.

### 6. The self-stop and the headroom (RUNS.md s11.5, s11.6)

Job 4 of run 40371181784 ended 4.2 percent under the 350-minute cap,
against the 25 percent rule, and the self-stop started after the table
build, so the job cap would have come first. For the rerun the self-stop
counts from job start. The 338 blocks are cut into 88 shards of 4, so each
of the 22 jobs holds exactly one dps-60 replay block (three per runner cost
up to 1.9 times). The worst job is priced at 227 minutes from the worst
blocks seen times 13/12, 35 percent under the cap (RUNS.md s12).

### The doors (updated)

1. **Active constraint:** the rerun. Its D0/D1/D2 reading at the corrected
   bound decides whether E2 closes at 280 modes. After it, as before, ε_t
   (the truncation lemma) separates D1 from D3.
2. **Frozen constants, changed:** nodes per panel, 13 (the corrected bound
   at 13 equals the old radii; at 12 every quadrature term is up to 225
   times wider, which the review estimates costs several N = 32 counts;
   genuine trade: radius against 1/12 more hat and region-A work). Shards
   of 4 blocks with one replay per runner (more jobs and table builds
   against contention). S' = 2,700 stays, now recorded as a deviation from
   PREREG.
3. **Information class:** unchanged. Every door stays inside the data the
   construction reads.
