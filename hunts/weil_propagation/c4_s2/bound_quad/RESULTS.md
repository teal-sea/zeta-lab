1. **The bound per source (DERIVATION.md s2): no complete bound; `eps_upper` is null on all 33 entries and `eps_quad()` returns +∞.** ΔT_stored − ΔT_nvec,exact splits into seven sources (Prop 1). Three close: E1, the window integral beyond the s-grid, ≤ κ(S)·nvec with κ in closed form (Prop 2); E6, the QR and triangular solve, relative error of ρ̃ ≤ about 2η with η = γ_{32mn}·√nvec·cond(F) (Prop 5), which closes only on the N = 8 and 16 builds; E7, the remaining float64 rounding (Prop 6). **E2 does not close: the stored projection is taken in the inner product truncated to [−S, S]** (with two order-1/S tail rows), while the exact object uses the exact Gram (I for ζ, cond ≤ 34 for b). A perturbation bound through the Gram pencil needs ‖X‖ < 1, X = G_S^{−1/2} G_exact G_S^{−1/2} − I, and ‖X‖ ≥ 70 on the best-conditioned build (80, 1200), whose stored Gram has eigenvalues 0.0126 to 3.44 against the identity (Prop 3). E3 to E5 (w panels, the 1/w tail series, mode data) were not bounded in the box.
2. **Values on the c = 2.9 builds:** E1 = **3.70e−3** (N = 8), 4.1e−3 to 1.1e−2 (N = 16), **9.2e−3 to 1.46e−2** (N = 32); E6 = **2.77e−4** at (80, 1200), 1.20e−4 at (80, 1600), 3.14e−2 at (120, 1600), 0.32 at (120, 1200), 41 at (160, 1600), **no bound on any N = 32 build**; E7 ≤ 3.4e−6 on every build and cell; the E2 obstruction ‖X‖ ≥ 70, 8.9, 1.7e4, 3.9e6, 6.1e9 on the N = 16 builds (80|1200, 80|1600, 120|1600, 120|1200, 160|1600) and ≥ **9.2e9** on every N = 32 build. E1 alone is 0.70 times checker/'s band at N = 8 and **1.13 to 1.78 times it at N = 32**: the source that closes cheaply is already band-sized there. The size of E2 itself, measured (not a bound): doubling S from 1200 to 2400 at 200 modes, N = 32, moves T_S by **5.63e−3 / 6.2e−3 / 8.0e−3** at c = 2.2 / 2.5 / 2.9 (two_adic/ s10.3 A4), in the S/nvec² regime (0.030) of the stored 280, 319 and 364-mode builds (0.029, 0.026, 0.023), so this source is plausibly of the size of the band (8.18e−3) on the stored N = 32 builds, and no bound on it can be smaller than the error it bounds.
3. **Grade.** E1, E6, E7: ordinary arguments with arb arithmetic (128 bits), unreviewed, under the numbered assumptions A1 to A9 of DERIVATION s2.0; A6 (LAPACK's backward-error constant fixed at 32) and A8 (libm within 4 ulp) are assumptions about libraries, not proven. Prop 3: an ordinary argument, unreviewed, on measured Gram spectra (float64) at (80, 1200) and (80, 1600) and recorded condition numbers elsewhere. **ALIGNMENT s5: E2 unresolved, not obstructed**: Prop 3 obstructs one route (perturbation through the Gram pencil), and a closing route exists (recompute ΔT with the exact Gram as a ball matrix, s2.8) that was not run, by allocation. For the follow-up this is **outcome 4 for this folder**: no usable bound, and the step that does not close is E2.
4. **Open.** (a) E2 by route (ii) with the exact Gram: the hats alone at the stored grid cost about 7.2e5 core-seconds at (280, 2266) (about 200 core-hours, 9.4 USD) and 2.2e6 at (364, 3060), before the wider, finer s-grid the exact Gram needs; an estimate from a measured arb unit on a loaded laptop, not run (coordinator: no route (ii), nothing to Modal, since eps_trunc is null too). (b) E1 sharpened by an enclosure of the tail mass beyond S (the heuristic tail energy is 3.38 against the bound's 80 at (80, 1200)). (c) E3, E4, E5: the Bernstein-ellipse panel bound, the tail-series remainder and the eigenvector residuals are derivable (s2.4) and were not evaluated; even with them, the sample sensitivity at N = 32 (δ·√nvec·cond(F) of order 30) gives no a priori bound (s2.7). (d) Review of DERIVATION s2 by referee/. (e) A bound below the band at N = 32 needs rebuilt rows at larger S, not only a better proof: the measured E2 on the stored builds is band-sized.
5. **What this folder settles.** The quadrature side of ΔT_stored is not bounded, so the stored build-to-build differences cannot yet be attributed to mode truncation rather than to the s discretization; the measured S responses (6.5e−4 and 1.1e−4 at 80 modes, 1.8e−4 at 160, N = 8; 5.6e−3 to 8.0e−3 at N = 32) say the s discretization is small at N = 8 and band-sized at N = 32. Nothing here is a claim about RH.

# RESULTS: bound_quad/, the quadrature, s cutoff, Gram and rounding errors of ΔT

Folder of the error-bound follow-up of 2026-09-24 (BRIEF.md, MISSION.md last
section). Started 17:35 -0500; plan committed at ab0f8fa (DERIVATION s1),
derivation, code and tests at 747487f.

## What was done

- **The two objects, made precise** (DERIVATION s1.0, s2.1): ΔT_stored is
  `ta_prolate.delta_T_cells` with its defaults (A4); ΔT_nvec,exact uses the
  exact projections onto the first nvec modes and the window integral over
  all of ℝ. The s cutoff enters the stored object twice: in the window
  integral (E1) and in the projection itself (E2), because the Gram is taken
  on the s-grid.
- **Pieces that close**, evaluated in arb for every stored build and cell
  (`eps_quad.py`, `eps_quad.json`): E1 (Prop 2), E6 (Prop 5), E7 (Prop 6).
- **E2, stated as a proposition** (Prop 3) with its numbers per build, and
  the measured evidence that the stored and exact projections really differ
  (`run_bound_quad.py`, `bound_quad_gram.json`): at (80, 1200) the stored
  Gram of ζ has eigenvalues 0.0126 to 3.44 (at (80, 1600): 0.091 to 2.64),
  the leverages sum to 78.99 (A5), and replacing the stored Gram by the
  identity moves the Q_∞ part of ΔT by 3.8e−3 / 4.0e−3 / 4.2e−3 in spectral
  norm (c = 2.2 / 2.5 / 2.9, N = 8). The tail rows overshoot:
  Σ_n A_n²/(πS) = 3.38 at (80, 1200).
- **The cost of the closing route** (`run_unit_cost.py`,
  `bound_quad_unit.json`): 2.2e−5 s per arb phase and 2.2e−7 s per
  (s, w, mode) ball product at 106 bits, at a load average near 60; per build
  2.2e4 core-seconds at (80, 1200), 7.2e5 at (280, 2266), 2.2e6 at
  (364, 3060), for the hats on the stored grid alone.

## The checks the brief asked for (`test_bound_quad.py`)

- **The measured S responses** (two_adic/ s7b: 6.5e−4 for 1200 → 2400 and
  1.1e−4 for 2400 → 4800 at 80 modes, 1.8e−4 for 4800 → 9600 at 160 modes,
  c = 2.2, N = 8), recomputed from `ta_gram_probe.json`. The inequality a
  complete bound must meet is ε(S₁) + ε(S₂) ≥ ‖ΔT(S₁) − ΔT(S₂)‖₂ (triangle
  inequality through ΔT_exact at the same nvec); ε = +∞ meets it trivially.
  E1's bound alone also meets it, by a factor of at least 2, so the
  responses cannot show that E2 is needed: E2 is open because no argument
  here bounds it, not because a measurement exceeds the partial bound. This
  corrects section 1's plan, which expected the opposite (DERIVATION s2.9).
- **The QR route against the 256-bit reference** (two_adic/ s10.3 A2, read
  from `ta_rho_check.json`: deviations 6.8e−9, 1.4e−5, 6.5e−2, 0.21 at
  (80, S) for S = 300, 200, 150, 120, cond(F_z) 5.1e7 to 7.3e14). Prop 5
  does not close at any of them, which is the direction the measurements
  require (the last two are of order 1e−1). Prop 5 is also tested against an
  enclosure of the exact ρ (arb, 256 bits) on a synthetic F with cond about
  1e3, where it closes and dominates.
- κ(S₀) of Prop 2 against the sampled window energy on |s| ∈ [S₀, 6S₀]
  (it dominates, and is within a factor 2 there); the stored s-grid sizes
  and Kmax against two_adic/ and checker/'s snapshot; no s-node within 1e−6
  of a window frequency 2πn/L; the JSON equals what the module computes;
  the folder's text rules.

## Reproduction

    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/bound_quad/eps_quad.py        # seconds
    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/bound_quad/run_bound_quad.py  # 903 s at a load average of 60 to 80
    PYTHONPATH=$PWD <venv python> hunts/weil_propagation/c4_s2/bound_quad/run_unit_cost.py   # seconds
    PYTHONPATH=$PWD <venv python> -m pytest -q -n 2 hunts/weil_propagation/c4_s2/bound_quad

Nothing was run on Modal; `modal/RUNS.md` is untouched.
