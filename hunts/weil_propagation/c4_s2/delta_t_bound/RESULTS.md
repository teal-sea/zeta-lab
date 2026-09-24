1. **ε does not exist on any build: `eps_upper` is null on all 33 builds in both bound folders, so there is no ε per cell at c = 2.9.** What it would have been made of: eps_trunc (bound_trunc/ 843544a: none; the truncation error is a difference of two divergent traces and the Sonin overlap on the prolate tail does not close), eps_quad (bound_quad/ 3be0dce: none; E2, the Gram under the s cutoff, does not close, ‖X‖ ≥ 9.2e9 on every N = 32 build; its one closed source E1 is 3.7e−3 at N = 8 and **9.2e−3 to 1.46e−2** at N = 32), and the assembler's own terms (Q, T_∞ and float64 rounding), which close at **1.2e−15 to 4.2e−15** per c = 2.9 build.
2. **No count below −ε can be formed on any build; the c = 2.9 count 4, 10, 20 below −band (checker/ s7.9) stands at its grade. What survives is the mode-free floor of bound_trunc/'s Lemma 3: n_−(R_S) ≥ 2, 2, 2 at c = 2.9 (N = 8, 16, 32), ≥ 1, 1, 1 at 2.5, ≥ 0 at 2.2 on the full space, and ≥ 0 on C4's class V_4 at every cell** (exact inertia of Q − κT_∞ at dps 40, κ = (√2 − 1)⁴; the two negatives at c = 2.9, N = 32 are −1.0e−4 and −1.7e−5; the same counts as bound_trunc/'s own at 91ce087). They sit on Q's near-null directions, mostly outside V_4 (measured, s3). Lemma 3's upper half gives nothing: Q − κ^{−1}T_∞ is negative definite on every cell.
3. **Outcome 4 by the rule pre-registered at 81f0b47, on every cell and both spaces: no usable bound on ΔT; the steps that do not close are bound_trunc/'s Sonin overlap and bound_quad/'s E2.** The floor, by Addendum A (e174d19, fixed before those counts ran), reads "floor flat, upper bound open" on every cell: by Lemma 3 a remainder of rank below 2 is ruled out on the full space at c = 2.9, nothing is ruled out on C4's class, and the floor does not bear on the 4, 10, 20 count.
4. **Grade.** Every count is exact (two rational routes that must agree) or ball arithmetic (V_4), on inputs of hardened accuracy; the assembler's rounding terms are exact rationals. Outcome 4 rests on the two folders' ordinary arguments, **unreviewed** (referee/ has committed no review at this commit). The floor is conditional on Lemma 3 (ordinary argument, unreviewed) and on kernel/'s unreviewed derivation of T_∞; weakest step Lemma 3. **This follow-up does not change the grade of 4, 10, 20: measured as a statement about R_S, weakest step ΔT.**
5. **Open.** (a) The size a bound must have (post-hoc, s5): at c = 2.9 a uniform ε below **1.50e−2** on V_4 (1.52e−2 full) gives outcome 1, and s7.9's 20 at N = 32 survives only to **1.18e−2**; bound_quad/'s E1 alone is 9.2e−3 to 1.46e−2 there, and bound_trunc/'s Proposition 4 puts a closed bound along its route at 0.0975 to 0.2125 at N = 32, so the routes tried would not decide it even if they closed. (b) Outcome 2 is unreachable on these stored matrices for any ε (PREREG s6). (c) A defect found post-hoc in the pre-registered outcome-1 test (s5). (d) ALIGNMENT s5: **unresolved, paused by the box and by allocation**, not obstructed. Nothing here is a claim about RH.

# RESULTS: delta_t_bound/, the error bound on ΔT and the recount (assembler/)

Worker assembler/, 2026-09-24, branch `teal-sea/weil-c4-s2`, under
`assembler/BRIEF.md` and `assembler/PREREG.md`. Grades follow the
`AGENTS.md` ladder, weakest step governs. Every number above and below is
pinned by `test_delta_t_bound.py` (this folder) or by the tests of
`assembler/` (`test_assembler.py`, `test_floor_count.py`,
`test_crossover.py`), as named.

## 0. What was fixed before what

| commit | what | before |
|---|---|---|
| 81f0b47 | PREREG (a) to (f): composition, Weyl lower and upper bounds, the four-outcome rule, line 2 wording, grade | any ε; bound folders held only their BRIEF.md |
| e174d19 | Addendum A (labelled post-hoc): the mode-free floor and ceiling from Lemma 3, what each reading means | any floor count at N = 32 or at c = 2.5, 2.2 |
| ddbfd3a | PREREG s6: the harness on synthetic ε (no ε read) | the routed recount |
| 90b73e0 | the floor counts; the crossover (post-hoc) | this file |

The routed recount reads the bound files **as committed** (`git show`):
bound_trunc/ at 843544a, bound_quad/ at 3be0dce (`delta_t_bound.json`
meta, with the sha256 of each blob), never a working tree another worker
is editing.

## 1. The composition, per build (`delta_t_bound.json`)

`assemble.py --routed --trunc-commit 843544a --quad-commit 3be0dce`. For
each of the 33 builds, ε = eps_trunc + eps_quad + the fixed terms of
PREREG (a). Both bound entries are null on every build, so ε is null on
every build and no count is taken [test_every_eps_is_null_and_why].

| source | owner | status at c = 2.9 |
|---|---|---|
| prolate modes beyond nvec | bound_trunc/ | null: the Sonin overlap S_∞F(1 − P)D on the prolate tail does not close (its DERIVATION s1.3, mechanism 2) |
| s cutoff, w quadrature, mode data, Gram, float64 | bound_quad/ | null: E2 does not close, ‖X‖ ≥ 9.2e9 on every N = 32 build; E1 = 3.7e−3 (N = 8), 9.2e−3 to 1.46e−2 (N = 32) [test_quad_blob_figures] |
| Q, T_∞, float64 rounding of Q, T_∞, the sum into T_S and R | assembler/ | closes: 1.2e−15 to 4.2e−15 per build [test_fixed_terms_at_29] |

The assembler's own terms are exact rational upper bounds (r_Q, r_T∞,
r_sub, r_mirror), the binary64 model for r_add, and the stated sizes of
checker/ and kernel/ for e_Q and e_T∞ (hardened). PREREG s6.2 shows they
move no count.

## 2. The rule, applied (PREREG (c))

At every cell (2.2, 2.5, 2.9) and on both spaces: no build has a finite ε at
N = 8, 16 or 32, so **outcome 4** [test_outcome_4_everywhere]. The
falsification check passes vacuously (every lower bound 0, every upper
bound the dimension). ε_grow is not computed: with no bound at N = 16 its
reference count would be the trivial 0.

## 3. The mode-free floor (Addendum A, `assembler/floor_count.json`)

F_N(c) = n_−(Q_mp − κ_lo T∞_mp + η_N I) ≤ n_−(R_S) and
G_N(c) = n_−(Q_mp − K_hi T∞_mp − η_N I) ≥ n_−(R_S), conditional on Lemma 3,
with Q from `checker_q.Q_matrix(c, N, 40)` and T_∞ from
`kernel/sonin.T_inf_matrix(c, N, 40)` (read-only), κ_lo and K_hi rational
brackets of κ = 17 − 12√2 and K = 17 + 12√2 to 2^−256, η_N ≤ 2.2e−26 covering
the inputs' stated sizes.

| c | F at N = 8, 16, 32 (full) | on V_4 | G (full / V_4) | negatives of Q − κT_∞ (N = 8, 16, 32) |
|---|---|---|---|---|
| 2.9 | **2, 2, 2** | 0, 0, 0 | dim / dim | −9.8913e−5, −1.6206e−5; −9.9510e−5, −1.6626e−5; −1.0017e−4, −1.6736e−5 |
| 2.5 | **1, 1, 1** | 0, 0, 0 | dim / dim | −7.1419e−6; −9.4713e−6; −1.0006e−5 |
| 2.2 | 0, 0, 0 | 0, 0, 0 | dim / dim | none |

[`assembler/test_floor_count.py`: test_floor_pinned]. Route 1 (exact
rationals, both routes) and route 2 (arb balls with κ and K as balls)
agree on every cell; F is unchanged at η ± 1e−9; T_∞ from the direct call
matches the moments route that the stored T_S used to below 1e−39.
bound_trunc/'s own count of the same floor at 91ce087 (a separate script on
the same inputs, withdrawn at 843544a so that the count is this folder's)
agrees on all nine cells, V_4 included, and on every negative eigenvalue to
1e−9 [test_floor_agrees_with_bound_truncs_own_count].

**Why the floor is empty on C4's class (measured, float64, one cell):** at
c = 2.9, N = 16 the two negative directions of Q − κT_∞ carry Q's Rayleigh
quotients **4.2e−5 and 4.4e−6** (Q's lowest eigenvalues there are 2.1e−7 and
3.9e−5) and weights **0.44 and 0.93** in the three-dimensional complement of
V_4, against 3/33 = 0.09 for a generic direction [test_floor_mechanism].
So the floor comes from Q's near-null directions, which C4's class mostly
excludes; on V_4, Q exceeds κT_∞.

**Reading (Addendum A.3, fixed before these counts):** with no ε, the
combined bounds are the floor and the ceiling alone; L = F is flat in N and
U = G is the dimension, so reading 3, "floor flat, upper bound open", on
every cell and both spaces [test_floor_combined_rule_reads_flat_floor_everywhere].
It is one-sided: it cannot exclude negatives, so it is not evidence for C4.

## 4. What the stored matrices already imply (PREREG s6, before any ε)

- **Outcome 2 was unreachable at any ε.** Every stored N = 32 matrix has at
  least 27 / 26 / 25 negative eigenvalues at c = 2.2 / 2.5 / 2.9 (V_4: 24 / 24
  / 23), every N ≤ 16 one at most 13 / 13 / 14 (V_4: 10 / 11 / 13). A Weyl
  upper bound cannot remove a negative eigenvalue of the matrix it is
  centred on, so U*_32 > L*_16 for every ε ≥ 0.
- The harness reproduces checker/ s7.9 at ε = band and 2 band (PIN_EXACT,
  PIN_V4), and the falsification check fires at ε = 0 (builds at one N
  disagree about the count), as it should.

## 5. Post-hoc (not in PREREG): the size a bound must have, and a defect in the rule

`assembler/crossover.py`, labelled post-hoc. With one ε for every build of
c = 2.9, L*_N(ε) = max over builds of n_−(RL + εI), interlaced; the float64
profile is exact-checked at the edge.

- **Outcome 1 holds for every uniform ε below 1.50e−2 on V_4 (1.52e−2 on the
  full space).** At the edge the lower bounds are 2, 8, 9 and just above it
  2, 8, 8, both confirmed by exact counts (V_4 by balls) at ε(1 ∓ 1e−6)
  [test_crossover_pinned]. s7.9's 20 at N = 32 survives only up to
  **1.18e−2** (V_4; 1.21e−2 full). The 80-mode N = 16 builds, not converged,
  count highest at N = 16 and so set L*_16.
- **Against the two folders' own figures:** bound_quad/'s E1 alone is
  9.2e−3 to 1.46e−2 on the N = 32 builds, and bound_trunc/'s Proposition 4
  puts a bound along its route, if it closed, at 0.0975 to 0.2125 at N = 32
  (843544a RESULTS line 3: what such a bound "would cost even if it closed"). bound_trunc/ also shows
  that the bounds on two N = 32 builds must sum to at least 4.950e−3, the
  distance between their stored ΔT (same line). Neither route tried comes
  near 1.50e−2 on the stored builds, even if it closed.
- **A defect in the pre-registered outcome-1 test.** It fires on any rise of
  L*_32 over L*_16, including 0, 0, 1: at uniform ε in [7.40e−2, 7.55e−2) on
  V_4 ([1.14e−1, 1.21e−1) full) the rule would say outcome 1 because the
  single deepest eigenvalue deepens with N, which interlacing allows without
  any growth of the count. It does not bite here (ε is null). A successor
  rule should require growth beyond what one eigenvalue can carry (for
  example L*_32 − L*_16 ≥ 2, or growth at the band scale). Recorded for
  referee/; the rule in PREREG (c) is not edited.

## 6. Grades

| statement | grade |
|---|---|
| ε null on every build | the two folders' ordinary arguments, unreviewed |
| assembler's fixed terms | exact rationals (r_Q, r_T∞, r_sub, r_mirror); binary64 model (r_add); hardened stated sizes (e_Q, e_T∞) |
| outcome 4 | follows from the above by the pre-registered rule |
| the floor F, the ceiling G | exact inertia and balls on hardened dps 40 inputs; conditional on Lemma 3 (ordinary argument, unreviewed) and kernel/'s unreviewed T_∞ derivation |
| why the floor is empty on V_4 | measured (float64, one cell) |
| outcome 2 unreachable | exact inertia of the stored matrices plus Weyl (ordinary argument) |
| the crossover 1.50e−2 | float64 profile, exact at the two edge points; post-hoc |
| 4, 10, 20 at c = 2.9 | unchanged: exact on the stored matrices, measured as a statement about R_S, weakest step ΔT |

No prover was used; nothing here is kernel-checked. ALIGNMENT s5 for this
follow-up: **unresolved** (paused by the box and by allocation), not
obstructed: no route to a bound was shown impossible (bound_trunc/ and
bound_quad/ both say so of their own steps).

## 7. Proposed text for `c4_s2/RESULTS.md` line 2 (sent to the coordinator, who writes that file)

"**No usable bound on ΔT: the prolate-mode truncation (bound_trunc/: the
Sonin overlap on the prolate tail does not close) and the Gram under the s
cutoff (bound_quad/: E2) do not close, so ε is null on all 33 builds and
nothing is recounted below −ε (delta_t_bound/, outcome 4 by the rule
pre-registered at 81f0b47).** The c = 2.9 count stays as checker/ s7.9
states it: exact on the stored matrices, measured as a statement about R_S,
weakest step ΔT; a uniform bound below 1.50e−2 would have decided it on
C4's class, and bound_quad/'s one closed source is already 9.2e−3 to
1.46e−2 at N = 32 (post-hoc). By bound_trunc/'s Lemma 3
(T_S ≥ (√2 − 1)⁴ T_∞, ordinary argument, unreviewed), n_−(R_S) ≥ 2 at
c = 2.9 and ≥ 1 at 2.5 at every N (exact inertia of Q − κT_∞ at dps 40), but
only ≥ 0 on C4's class V_4, and this floor does not grow with N: it does not
bear on the 4, 10, 20 count."

## 8. Reproduction

    PY="PYTHONPATH=<worktree root> /Users/thomas/zeta-lab/.venv/bin/python"
    $PY hunts/weil_propagation/c4_s2/assembler/assemble.py --synthetic        # synthetic.json (PREREG s6)
    $PY hunts/weil_propagation/c4_s2/assembler/floor_count.py                 # floor_count.json (Addendum A)
    $PY hunts/weil_propagation/c4_s2/assembler/crossover.py                   # crossover.json (post-hoc)
    $PY hunts/weil_propagation/c4_s2/assembler/assemble.py --routed --trunc-commit 843544a --quad-commit 3be0dce
    $PY -m pytest -q -n 2 hunts/weil_propagation/c4_s2/assembler hunts/weil_propagation/c4_s2/delta_t_bound

On the shared, heavily loaded laptop the most expensive unit was the
floor's c = 2.9, N = 32 cell, 544 s; the routed recount takes seconds
(no ε, no count). Everything checkpoints per unit.
