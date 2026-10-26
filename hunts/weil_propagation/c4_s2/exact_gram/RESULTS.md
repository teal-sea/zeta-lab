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
