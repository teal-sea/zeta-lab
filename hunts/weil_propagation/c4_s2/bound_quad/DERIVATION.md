# DERIVATION: bound_quad/, every error of ΔT_stored except the mode truncation

Started 2026-09-24 17:35 -0500, time box 3 hours (BRIEF.md). Section 1 is the
plan (milestone 1), committed before any bound was coded. Section 2 is the
derivation (milestone 2). Numbers in section 2 are pinned in
`test_bound_quad.py`. Section 1 is the plan as committed (ab0f8fa); its
figures came from scratch measurements and are superseded where section 2
re-measures them (s2.3, s2.8).

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

## 2. Derivation

Written after section 1 was committed (ab0f8fa). Every numbered assumption
is listed in 2.0 and cited where it is used; every number is pinned in
`test_bound_quad.py` and produced by `eps_quad.py` (arb, 128 bits) or
`run_bound_quad.py` (float64, measured). All arguments here are ordinary
arguments, unreviewed.

### 2.0 Setting and assumptions

For w supported on v ≥ 1, ŵ(s) = ∫_1^∞ w(v) v^{−1/2−is} dv and
‖w‖² = (1/2π) ∫ |ŵ|² ds (Plancherel). For a projection Q onto span{w_i}
with Gram matrix G, ρ_Q(s) = ŵ(s)* G^{−1} ŵ(s) and, for a unit coefficient
vector v and g_v(s) = Σ_n v_n V̂_n(s) (V̂_n as `ta_mellin.window_hat`),

    v* M_Q v = (1/2π) ∫ ρ_Q(s) |g_v(s)|² ds.

Two facts used below: (i) ρ_Q(s) = sup over unit f in range Q of |f̂(s)|²,
so ρ_Q ≥ 0 and (1/2π) ∫ ρ_Q = Tr Q = rank Q; (ii) Σ_{n ∈ ℤ} |V̂_n(s)|² = L
(Parseval for the basis U_n of L²[0, L] against e^{ist}), so
|g_v(s)|² ≤ Σ_{|n| ≤ N} |V̂_n(s)|² ≤ L by Cauchy-Schwarz.

- **A1.** The identities of two_adic/ s5 (ΔT(g) = Tr(θ(g)(Q_∞ − Q_S)θ(g)*),
  its Mellin form above, Plancherel) hold as derived there (unreviewed
  there). This folder bounds the numerics of that formula, not the formula.
- **A2.** ΔT_nvec,exact is built from the exact prolate modes n < nvec
  (kernel/'s ξ_n as exact eigenfunctions), so G_z,exact = I; where a
  margin is wanted, ‖G_z,exact − I‖ ≤ d = 0.1 is all that is used.
- **A3.** The nvec modes (and their b_n) are linearly independent, so
  Tr Q_∞ = Tr Q_S = nvec.
- **A4.** The stored rows were computed by the code at checker/'s recorded
  T_S input digest with the defaults of `delta_T_cells`: `s_grid(S, 1, 8)`,
  12 Gauss nodes per w panel, Kmax = `kmax_for(nvec)`, 25 asymptotic terms,
  14 derivatives, ρ by `ta_mellin.rho` (Householder QR of F, `mode="r"`,
  `solve_triangular(trans="C")`, sum of squares). A fact about provenance
  (checker/'s guard), not re-derived here.
- **A5.** The computed leverages w_s ρ̃(s)/2π sum to at most nvec + 2 over
  the s rows. Measured 78.99 at (80, 1200) (`bound_quad_gram.json`);
  implied by Prop 5 wherever E6 closes; assumed at N = 32.
- **A6.** numpy's LAPACK Householder QR and SVD are backward stable with
  ‖ΔF e_j‖₂ ≤ γ_{32 m n} ‖F e_j‖₂ (Higham, *Accuracy and Stability*, 2nd
  ed., Thm 19.4, whose constant is unspecified; 32 is fixed here and is an
  assumption about the library, not proven).
- **A7.** Complex floating-point arithmetic: each real-arithmetic bound γ_k
  used below holds for the complex operation with γ_{4k} (Higham s3.6).
- **A8.** IEEE binary64, round to nearest (u = 2^−53); numpy's exp, log,
  sqrt and division err by at most 4 ulp per real component; BLAS sums in
  any order but without fast (Strassen-type) products.
- **A9.** ΔT_exact is real symmetric, so taking the real part of the
  symmetrized stored matrix does not add error (it is a contraction in
  spectral norm). Not derived here: two_adic/ and checker/ treat ΔT as
  real, and a scratch run of the stored route at (80, 1200) during this
  work saw an imaginary part at rounding level (not kept).

### 2.1 The decomposition (Prop 1)

Define, on the stored s-grid (right end S_r = −S + ⌊2S⌋ ≤ S):

- D̃ = ΔT_stored (computed, float64);
- D_a = the stored formula in exact arithmetic on the computed samples
  (hats, jumps J, oscillation amplitudes A as the float64 numbers);
- D_b = the stored formula in exact arithmetic on the exact samples of the
  modes of A2;
- D_c = (1/2π) ∫_{−S}^{S_r} (ρ_∞ − ρ_S)(s) V̂V̂* ds with the **exact**
  Gram matrices and the exact integral over the grid's range;
- ΔT_exact = the same over all of ℝ.

**Prop 1.** ‖ΔT_stored − ΔT_exact‖ ≤ E1 + E2 + E345 + E6 + E7 with
E1 = ‖D_c − ΔT_exact‖ (window integral beyond the grid), E2 = ‖D_b − D_c‖
(the s discretization: the Gram taken in the truncated inner product with
its tail rows, and the Gauss rule of the window integral), E345 =
‖D_a − D_b‖ (w quadrature, dyadic truncation and tail series, mode data,
propagated through the discretized projection), and E6 + E7 ≥ ‖D̃ − D_a‖
(QR and solve; the rest of the rounding). *Proof:* triangle inequality,
and A9 for the real-part step.

### 2.2 E1, the window integral beyond the grid (Prop 2): closes, crudely

**Prop 2.** E1 ≤ κ(S_r) · nvec, with

    κ(S_0) = Σ_{|n| ≤ N} 4 / (L (S_0 − 2π|n|/L)²),   valid for S_0 > 2πN/L.

*Proof.* For unit v, v*(ΔT_exact − D_c)v = (1/2π) ∫_{outside} (ρ_∞ − ρ_S)
|g_v|², a difference of two non-negative numbers, so its modulus is at most
the larger one, and each is ≤ sup_{|s| ≥ S_r} |g_v(s)|² · (1/2π) ∫ ρ_Q ≤
κ(S_r) · nvec by fact (i) and A3. |V̂_n(s)| = |e^{ikL} − 1| / (√L |k|) with
k = 2πn/L − s gives |V̂_n(s)| ≤ 2/(√L |k|), and |k| ≥ |s| − 2π|n|/L; then
Cauchy-Schwarz. Uses A1, A2, A3.

Values (`eps_quad.json`, `parts_upper.E1`): **3.70e−3** at N = 8 (80, 1200,
c = 2.9), **4.1e−3 to 1.1e−2** at N = 16, **9.2e−3 to 1.46e−2** at N = 32
(c = 2.9). The factor nvec is the crude step: a sharp version needs the
tail mass (1/2π) ∫_{|s| > S} ρ, which the heuristic tail energies
Σ_n (J_n² + A_n²)/(πS) put at 3.38 at (80, 1200) instead of 80, but a
bound on it needs enclosures of the hats beyond S (not done).

### 2.3 E2, the s discretization of the projection (Prop 3): does not close

The stored ρ̃ is the density of the projection onto the modes in the inner
product (1/2π) Σ_s w_s conj(f̂(s)) ĝ(s) on [−S, S_r] plus the two tail rows,
i.e. with Gram G_S = F*F; the exact ρ uses G_exact. The only handle on
ρ_exact − ρ_S from the Grams is the pencil (G_exact, G_S): with
X = G_S^{−1/2} G_exact G_S^{−1/2} − I,

    ρ_exact(s) / ρ_S(s) ∈ [1/(1 + ‖X‖), 1/(1 − ‖X‖)]   (when ‖X‖ < 1),

and the absolute form |ρ_exact − ρ_S| ≤ ‖G_S^{−1}‖ ‖G_S − G_exact‖
‖G_exact^{−1}‖ |ŵ|², which is at least ‖X‖ |ŵ|²-sized. Both need ‖X‖ well
below 1.

**Prop 3.** ‖X‖ ≥ (1 − d)/λ_min(G_S) − 1 (A2), and on every stored build
this is far above 1:

| build (nvec, S) | λ_min(G_S^z) | lower bound on ‖X‖ | source |
|---|---|---|---|
| (80, 1200) | 0.0126 (λ_max 3.44) | 70 | measured, `bound_quad_gram.json` |
| (80, 1600) | 0.091 (λ_max 2.64) | 8.9 | measured, `bound_quad_gram.json` |
| (120, 1200), (120, 1600), (160, 1600) | ≤ λ_max / cond(F_z)² | 3.9e6, 1.7e4, 6.1e9 | recorded cond(F_z), offI, A6 |
| the five N = 32 builds | ≤ λ_max / cond(F_z)² | 9.2e9 to 9.4e10 | recorded cond(F_z), offI, A6 |

(Values at c = 2.9 in `eps_quad.json`, `e2_obstruction_lower`; the bound
does not depend on c. At N = 32 the recorded cond(F_z) of 1.9e13 to 2.1e13
is itself inside the float64 SVD's error, so the lower end of its
enclosure, about 1/γ_{32mn}, is what enters: the true value can only be
larger.)

*Proof of the inequality.* ‖X‖ ≥ λ_max(G_S^{−1/2} G_exact G_S^{−1/2}) − 1
≥ λ_min(G_exact)/λ_min(G_S) − 1. For the recorded builds,
λ_min(G_S) ≤ λ_max(G_S)/cond(G_S), λ_max(G_S) ≤ 1 + nvec · offI (offI the
recorded largest entry of |G_S − I|), cond(G_S) = cond(F_z)², with cond(F_z)
at the lower end of its enclosure from the recorded float64 value (A6 and
Weyl's inequality for singular values).

**This is not an artifact of a weak inequality.** At (80, 1200) the stored
Gram has eigenvalues from 0.0126 to 3.44 where the exact one is I: the
rank-2 tail rows overshoot (Σ_n A_n²/(πS) = 3.38, with A_n² of order
4n + 1: the ratio is 0.89 to 12 over the 80 modes), and one combination of the modes keeps 98.7 % of its energy
beyond S. The projections are different subspaces, and the Q_∞ part of ΔT
alone moves by the probe ‖M_∞(G_S) − M_∞(I)‖ (`bound_quad_gram.json`:
3.8e−3 / 4.0e−3 / 4.2e−3 at c = 2.2 / 2.5 / 2.9, N = 8). The measured S responses of ΔT are smaller (6.5e−4
from 1200 to 2400 at 80 modes) because the discretizations of Q_∞ and Q_S
partly cancel; nothing available here bounds that cancellation. Uses A1,
A2, A6.

**Status of E2 (ALIGNMENT s5): unresolved, not obstructed.** Prop 3 is a
statement about one route (a perturbation bound through the Gram pencil),
and for that route it is a restricted-class obstruction. A route that does
close E2 exists (s2.8: recompute with the exact Gram, which is well
conditioned); it was not run, by allocation (its cost, s2.8).

### 2.4 E3, E4, E5: derivable in principle, not bounded in the box

- **E3 (w panels).** η_n = F ξ_n is entire of exponential type 2π,
  |η_n(w + iy)| ≤ ‖ξ_n‖_{L¹} e^{2π|y|}; w^{−1/2−is} is analytic for Re w > 0
  with |w^{−is}| ≤ e^{|s| |arg w|}; the panel width h = 2π/(2π + S/w) keeps
  |s| |y|/w ≤ πb on an ellipse of semi-minor axis bh/2. So each 12-node panel
  has a Gauss–Legendre bound (64/15) M ρ_B^{−24}/(ρ_B² − 1) · h/2 with
  explicit M. This is a derivation plan; it was not evaluated.
- **E4 (tail series).** For polynomial ξ the 1/w expansion of F ξ is exact
  and finite; the code keeps 14 derivatives and 25 asymptotic terms of
  ∫_W^∞ e^{iaw} w^β dw. The omitted derivative terms are computable from the
  coefficients, and the asymptotic remainder is one more integration by
  parts; neither was evaluated. `kmax_for`'s ratio rule is a heuristic, not
  a convergence proof.
- **E5 (mode data).** Needs ‖ξ_n,stored − ξ_n‖ from eigenvector residuals
  and gaps of kernel/'s Slepian solve at dps 20, then the float64 rounding
  of the coefficients. Measured instead: the float64 hats agree with
  kernel/'s closed form to 3.0e−13 absolute at (80, 300) (two_adic/ s10.3
  A2).

### 2.5 E6, the QR and the triangular solve (Prop 5): closes where cond(F) is small

**Prop 5.** Let η = γ_{32mn} √n cond(F) (m = s-nodes + 2 rows, n = nvec,
cond(F) at the upper end of its enclosure, A6). If 2η + η² < 1 and
η₂ = γ_{4n} √n cond(F)(1 + η)/(1 − η) < 1, the computed ρ̃ satisfies
|ρ̃/ρ − 1| ≤ δ_ρ := max((1 + γ_{8n}) / ((1 − 2η − η²)(1 − η₂)²) − 1,
1 − (1 − γ_{8n}) / ((1 + η)²(1 + η₂)²)), where ρ is the exact discretized
density on the same samples; and E6 ≤ (δ_ρ,z + δ_ρ,b) · L · nvec.

*Proof.* A6: R̃ is the exact R of F + ΔF, ‖ΔF‖₂ ≤ ‖ΔF‖_F ≤ γ_{32mn} √n
‖F‖₂, so G̃ = R̃*R̃ = G^{1/2}(I + Y)G^{1/2} with ‖Y‖ ≤ 2η + η²; the
triangular solve (Higham Thm 8.5, A7) is backward stable,
(R̃ + ΔR)* ỹ = conj(ŵ) with ‖ΔR‖ ≤ γ_{4n} √n ‖R̃‖, relative to
σ_min(R̃) ≥ σ_min(F)(1 − η); the final sum of squares adds γ_{8n}. Then
M̃_Q − M_Q = Σ_s (leṽ − lev)(s) V̂V̂* with |leṽ − lev| ≤ δ_ρ lev, so
‖M̃_Q − M_Q‖ ≤ δ_ρ ‖M_Q‖ ≤ δ_ρ L Σ_s lev ≤ δ_ρ L nvec (facts (i), (ii)).
Uses A1, A4, A6, A7.

Values at c = 2.9: **2.77e−4** (80, 1200), **1.20e−4** (80, 1600),
3.14e−2 (120, 1600), 0.32 (120, 1200), 41 (160, 1600); **no bound** on any
N = 32 build (cond(F_z) = 8.7e5 to 2.1e13 puts 2η + η² above 1). The factor
32 of A6 and the step ‖M_Q‖ ≤ L nvec make these loose; the measured
deviations are far smaller (two_adic/ s10.3 A1).

### 2.6 E7, the rest of the rounding (Prop 6): closes

**Prop 6.** Per entry of each of M_∞, M_S, the float64 assembly
`(conj(V) * (ρ̃ w)) @ V.T / 2π` errs from the same formula in exact
arithmetic on the computed ρ̃ by at most
Σ_s leṽ(s) (γ_{4(ns+8)} (L + 2√L δV + δV²) + 2√L δV + δV²), where leṽ are
the computed leverages, ns the number of s-nodes, and δV the absolute error
of a computed V̂ entry, δV ≤ (5u/k_min + L² u (2πN/L + S)/2)/√L (A8; k_min
the smallest |2πn/L − s| over the grid, computed per build, at least 1e−6
on every build, where the code's switch at 1e−12 is never reached). The
symmetrization adds 2u · 2L(nvec + 2) per entry and T_S = T_∞ + ΔT adds
u · max|T_S entry| (read from the stored row). Spectral norm ≤ (2N + 1) ×
the entry bound, for M_∞ and M_S together. With A5 (Σ_s leṽ ≤ nvec + 2):
see 2.9; at most a few times 1e−6 on every build. Uses A1, A5, A7, A8, A9.

### 2.7 Sample propagation (why enclosing the hats would not suffice at N = 32)

If the samples (rows of F and the hats) carry a relative error δ entrywise,
then ‖ΔF‖₂ ≤ δ √nvec ‖F‖₂ and the discretized ρ moves by a factor in
[(1 + η_δ)^{−2}, (1 − 2η_δ − η_δ²)^{−1}] with η_δ = δ √nvec cond(F) (the
argument of Prop 5 with ΔF in place of the QR error), before the change of
the hats inside the quadratic form itself. With δ of order 1e−13 (the
measured hat accuracy) and cond(F_z) = 1.9e13 to 2.1e13 on the 280, 319 and
364-mode builds, η_δ is of order 30, so even an exact enclosure of every
hat gives no a priori bound on D_a − D_b there. The
measured response is far smaller (two_adic/ s10.3 A3: 3e−12 for a 2^−52
perturbation at (200, 2400)), but a typical response is not a bound.

### 2.8 The route that would close E2, and its cost

Route (ii) with the exact Gram: (1) enclose ζ̂_n (closed form, Tate) and
b̂_n (Gauss panels in w with the E3 bound, the E4 remainder) on an s-grid
with panels narrow enough for the strip |Im s| < 1/2 in which the hats are
analytic (width 1/4 instead of 1, so about 4 times the stored s-nodes) and
wide enough that the window tail is below target (S′ of order 1e4 at
280 modes); (2) form G_b,exact in v-space, where it is well conditioned
(cond ≤ 34, two_adic/ s10.1), not from s-samples, whose tails beyond S′
carry energy of order Σ_n A_n²/(πS′); (3) ρ and M in ball arithmetic; then
ε = ‖center − ΔT_stored‖ + radius. **Cost, an estimate:** the unit
re-measured by `run_unit_cost.py` (`bound_quad_unit.json`, arb at 106
bits, at a load average near 60 on the shared laptop) is 2.2e−5 s per
phase and 2.2e−7 s per (s, w, mode) product; at the stored grids that is
2.2e4 core-seconds at (80, 1200), 7.2e5 at (280, 2266) (about 200
core-hours, 9.4 USD at 0.0473 USD per core-hour) and 2.2e6 at (364, 3060),
for step (1) alone, before the wider and finer grid (panels 4 times
narrower and S′ about 4 times wider: about 16 times the s-nodes, and more
w-nodes, since the w panels are sized to 2π + S′/w). Section 1's first measurement (5.8e−5 s per phase, 2.4e−7 s per
product, a scratch run) is of the same order; timings on this machine move
by a factor 2 to 5 with its load. It does not fit the box or the 25 USD
cap, and it was not run (coordinator, 2026-09-24: no route (ii), nothing to
Modal, since eps_trunc is null too).

**The size of E2 itself, measured (not a bound).** At N = 32, 200 modes,
doubling S from 1200 to 2400 moves T_S by 5.63e−3 / 6.2e−3 / 8.0e−3 in
spectral norm at c = 2.2 / 2.5 / 2.9 (two_adic/ s10.3 A4,
`ta_rho_check.json`, pinned here). (200, 1200) sits at S/nvec² = 0.030, the
regime of the stored 280, 319 and 364-mode builds (0.029, 0.026, 0.023).
So the error this source contributes to the stored N = 32 builds is
plausibly of the size of the band (8.2e−3 at c = 2.9) itself; no bound on
it can be smaller than the error it bounds. This is a reading by analogy of
regime, measured grade.

### 2.9 Summary at c = 2.9 (every value in `eps_quad.json`)

| N | nvec, S | E1 | E6 | E7 | ‖X‖ ≥ (E2 obstruction) | eps_upper |
|---|---|---|---|---|---|---|
| 8 | 80, 1200 | 3.70e−3 | 2.77e−4 | 3.3e−8 | 70 (measured) | null |
| 16 | 80, 1600 | 4.13e−3 | 1.20e−4 | 8.0e−8 | 8.9 (measured) | null |
| 16 | 120, 1600 | 6.19e−3 | 3.14e−2 | 1.2e−7 | 1.7e4 | null |
| 32 | 200, 2400 | 9.22e−3 | none | 5.5e−7 | 1.5e10 | null |
| 32 | 280, 2266 | 1.46e−2 | none | 7.5e−7 | 4.6e10 | null |
| 32 | 364, 3060 | 1.01e−2 | none | 1.2e−6 | 9.2e9 | null |

E1 alone is 0.70 times checker/'s band at N = 8 and 1.13 to 1.78 times it
on the N = 32 builds (c = 2.9, bands from `checker/checker_inertia.json`):
the one source that closes cheaply is already band-sized at N = 32.

**Correction to section 1's plan.** Section 1 said a test would show the
closing pieces alone falling below the measured S responses. They do not:
E1's crude bound at (80, 1200) plus (80, 2400) is above the 1200 → 2400
response (6.5e−4), and likewise for the other two responses. So the
measured responses cannot show that E2 is needed. E2 is open because no
argument here bounds it (Prop 3), not because a measurement exceeds the
partial bound; `test_bound_quad.py` pins both inequalities as they are.
