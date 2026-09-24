# DERIVATION: bound_quad/, every error of ΔT_stored except the mode truncation

Started 2026-09-24 17:35 -0500, time box 3 hours (BRIEF.md). Section 1 is the
plan (milestone 1), committed before any bound was coded. Section 2 is the
derivation (milestone 2). Numbers here are pinned in `test_bound_quad.py`.

## 1. Plan: the sources, the route for each, and whether it closes

### 1.0 The two objects

**ΔT_stored** is what two_adic/ computes and checker/ stores
(`ta_prolate.delta_T_cells` with its defaults, called by
`checker/run_checker_ts.build_unit`): for the modes n < nvec,

- hats ζ̂_n(s), b̂_n(s) on the s-grid `s_grid(S, width=1, per_panel=8)`
  (Gauss panels on [−S, S]), from Gauss panels in w on [1, 2^Kmax]
  (12 nodes each), the asymptotic 1/w series beyond 2^Kmax (25 terms,
  14 derivatives), and float64 mode data (`ProlateModes`: dps-20
  coefficients rounded to float64, scipy spherical Bessel);
- Gram factors F = [weighted hats; two order-1/S tail rows]
  (`gram_factor_s`), so the Gram matrix is G_S = F* F: **the inner product
  truncated to [−S, S]**, plus a jump and an oscillation correction;
- ρ̃(s) = ŵ(s)* G_S^{−1} ŵ(s) by a Householder QR of F (`ta_mellin.rho`);
- M = (1/2π) Σ_s w_s ρ̃(s) V̂(s) V̂(s)* (`T_from_rho`), ΔT = M_∞ − M_S,
  symmetrized and real part taken.

**ΔT_nvec,exact** is the same finite-mode object without these errors:
the orthogonal projections Q_∞, Q_S onto span{ζ_n}, span{b_n} (n < nvec) in
L²(v ≥ 1), i.e. ρ built from the **exact** Gram matrices, and the window
integral over all of ℝ:
ΔT_exact = (1/2π) ∫_ℝ (ρ_∞ − ρ_S)(s) V̂(s) V̂(s)* ds.

The exact Gram matrices are well conditioned: G_z = I for exact prolates,
cond(G_b) ≤ 34 (two_adic/ s10.1, ordinary argument). The stored ones are
not: cond(G_S) = cond(F)² = 273 at (80, 1200) up to about 4e26 at
(280, 2266) (checker/ snapshot `diag`). So the s cutoff enters ΔT_stored
twice: in the window integral (small, order 1/S³), and **in the projection
itself**, because Q is taken in the inner product truncated to [−S, S].

### 1.1 Sources, route and verdict

| # | source | route | closes? |
|---|---|---|---|
| E1 | s cutoff in the window integral, \|s\| > S omitted from M (exact object) | a priori: ‖tail‖ ≤ κ(S) m(S), κ(S) = sup_{\|s\|≥S} Σ_n \|V̂_n(s)\|² in closed form, m(S) = (1/2π)∫_{\|s\|>S} ρ ≤ Tr Q = nvec | **yes, crudely** (m ≤ nvec); a sharp m(S) needs hat enclosures |
| E2 | s cutoff in the Gram: the projection taken in the truncated inner product (with the order-1/S tail rows) | a perturbation bound needs ‖G_S^{−1}(G_exact − G_S)‖ < 1 | **no.** At (80, 1200), the best-conditioned build, λ(G_S^z) spans [0.0126, 3.44] against G_exact ≈ I: the product is about 190, not below 1 (measured locally, 17:53). At N = 32 cond(G_S) reaches 4e26. Only route (ii) closes it: recompute ΔT with the exact Gram as a ball matrix |
| E3 | w quadrature (Gauss panels on [1, 2^Kmax]) | a priori per panel: Gauss–Legendre error on a Bernstein ellipse, η_n entire of exponential type 2π | derivable, not coded in the box; only useful inside route (ii) |
| E4 | dyadic truncation at Kmax and the 1/w tail series (its term count) | the series is the exact finite IBP expansion of F ξ for a polynomial ξ; the code truncates it at 14 derivatives and 25 asymptotic terms with no remainder bound; a remainder bound exists only where the series converges (kmax_for's ratio rule is a heuristic) | derivable, not coded in the box |
| E5 | mode data: dps-20 coefficients in float64, scipy spherical Bessel | the exact object is defined by exact prolates; bounding ‖ξ_n^stored − ξ_n‖ needs eigenvector residuals of kernel/'s Slepian solve | not in the box; measured agreement of the hats with kernel/'s closed form is 5e−14 to 2e−13 (two_adic/ s10.1), a measurement |
| E6 | the Gram step: Householder QR of F and the triangular solve | a priori backward error, relative error of ρ̃ ≲ 2η, η = γ̃_{mn} √n cond(F) (Higham ch. 19, library constant as a numbered assumption) | **closes where cond(F) is small** (N = 8, 16 builds up to cond(F) of about 1e4); **does not close** at cond(F) ≥ about 1e6 (every N = 32 build: 8.7e5 to 2.1e13) |
| E7 | float64 rounding in the assembly (T_from_rho, symmetrization, T_∞ + ΔT) | a priori: γ_{ns} Σ_s \|terms\| ≤ γ_{ns} L Σ_s leverage(s), leverage sum ≤ nvec + 2 | **yes** (order 1e−9 to 1e−7) |

**Sample propagation.** Even with every hat enclosed, E3 to E5 reach ΔT
through the discretized projection with a worst-case amplification of order
cond(F) (the samples' relative error δ times cond(F)). With δ about 1e−13
and cond(F_z) = 1.9e13 to 2.1e13 on the 280, 319 and 364-mode builds, that
product is of order 1: an a priori sample bound cannot close there either,
independently of E2.

### 1.2 Verdict of the plan

**E2 does not close a priori on any stored build, and it is the source that
matters.** It is not a small perturbation: the stored and the exact objects
project onto different subspaces (G_S has eigenvalues from 0.0126 to 3.44 at
the best build, where the exact Gram is I). The measured size of what E2
does to ΔT is the S response: 6.5e−4 (1200 → 2400) and 1.1e−4 (2400 → 4800)
at 80 modes, N = 8, c = 2.2; 1.8e−4 at 160 modes (4800 → 9600); and at
N = 32, 200 modes, 5.6e−3 / 6.2e−3 / 8.0e−3 from S = 1200 to 2400
(two_adic/ s10.3 A4), which is the S/nvec² regime (0.03) of the stored
280-mode build. So on the stored N = 32 builds this source is plausibly of
the size of the band itself (measured, by analogy of regime; not a bound),
and no bound on it can be smaller than the error it bounds.

The only closing route is (ii) with the exact Gram: enclose ζ̂_n, b̂_n on an
s-grid wider and finer than the stored one (the exact Gram of b needs the
whole line; the window integral needs S' of order 1e4 for 1e−5 at 280
modes), form the exact Gram (well conditioned), and take
ε = ‖center − ΔT_stored‖ + radius.

**Measured unit (this laptop, 2026-09-24 17:56, python-flint 0.9.0 at 106
bits):** one arb phase w^{−1/2−is} with its weight costs 5.8e−5 s per
(s, w) pair, and the ball product against the mode columns 2.4e−7 s per
(s, w, mode). At the stored grids that is, per build, 19200 × 28236 pairs
at (80, 1200) (about 4.2e4 s, 12 core-hours) and 36256 × 238752 pairs at
(280, 2266) (about 1.1e6 s, 300 core-hours, about 14 USD at modal/'s rate
of 0.0473 USD per core-hour), before widening the s-grid for the exact Gram.
ζ̂_n alone has a closed form (kernel/'s Tate route, `zeta_mellin_all`):
4.4 s per s-node for 280 modes in mpmath at dps 20 (measured), which is
not an enclosure; a first arb transcription of its Legendre-moment
recurrence lost its enclosure (radii of 1e26 after 325 steps) and was not
pursued. b̂_n has no closed form (it needs the incomplete transforms
T_n(2^k; s)). **Route (ii) does not fit the box or the 25 USD cap for the
N = 32 builds; it would fit one N = 8 build on Modal, and I do not propose
it, because at N = 8 it would bound a build whose count is not in
question.** Nothing is run on Modal by this folder.

**Plan for the rest of the box:** (1) section 2: the derivation, every
assumption numbered: the decomposition of ΔT_stored − ΔT_exact into E1 to
E7, the bounds that close (E1 crude, E6 where cond(F) is small, E7), and the
non-closure of E2 stated as a proposition with the numbers per build;
(2) `eps_quad.py` / `eps_quad.json`: `eps_upper` is **null** for every build
(E2 open), with the per-source pieces that do close and the reason; (3)
tests: the pieces are pinned, and a test shows that the closing pieces alone
fall below the measured S responses, so a complete ε built from them would
be refuted by the measurements (the null is necessary, not a formality);
(4) RESULTS.md: **outcome 4 for this folder** (no usable bound; the step
that does not close is E2, the Gram under the s cutoff), unless section 2
finds a route that the plan missed.
