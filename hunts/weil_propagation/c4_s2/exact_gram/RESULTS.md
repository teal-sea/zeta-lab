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
