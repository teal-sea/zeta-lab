# INTERFACE: kernel/ (gap (a), the archimedean Sonin projection S_∞)

For two_adic/ and checker/. Import from the worktree root with
`sys.path.insert(0, "hunts/weil_propagation/c4_s2/kernel")`, then
`import sonin`. Python: `PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python`.
Everything is mpmath; each function takes `dps` and works internally at
`dps + sonin.GUARD` (25 guard digits), returning values at `dps`.

## 1. Conventions (the mission's shared basis)

- Window [0, L], L = log c. Basis U_n(y) = L^{-1/2} e^{2πiny/L}, n = −N … N.
  **Index 0 of every delivered matrix is n = −N.**
- A form F is delivered as the real symmetric (2N+1)×(2N+1) matrix M with
  F(f) = v* M v for f = Σ v_n U_n.
- Every block here is a *kernel form*: for an even kernel K on [−L, L],
  F(f) = ∫ g(x) K(|x|) dx with g the autocorrelation of f, and
  M(n, m) = ∫_0^L K(x) q_nm(x) dx (CCM Lemma 2.3):
  q_nm = (sin ω_m x − sin ω_n x)/(π(n−m)), q_nn = 2(1 − x/L) cos ω_n x,
  ω_k = 2πk/L. So a block is determined by
  s_k = ∫_0^L K sin ω_k x (k = 0 … N, s_0 = 0) and
  d_k = ∫_0^L K · 2(1 − x/L) cos ω_k x (k = 0 … N), and
  `sonin.form_from_moments(s, d, N)` rebuilds it:
  M(n, m) = (s_m − s_n)/(π(n − m)) with s_{−k} = −s_k, M(n, n) = d_|n|.
  The archimedean block A is of the same shape (its d_k carry the
  regularized constant).
- Our f is Connes-Consani's g (arXiv:2006.13771, "CC"); their test function
  f = g ∗ g* is our autocorrelation.

## 2. Functions

| function | returns | source |
|---|---|---|
| `T_inf_matrix(c, N, dps, arch_type=None)` | T_∞(f) = Tr(ϑ(f) S_∞ ϑ(f)*) = A + E | CC Thm 4.7 (eq. 83) |
| `arch_matrix(c, N, dps, parity=0)` | A = W_∞ (mission normalization, theory §0) | CC eq. 53; CCM (3.15) |
| `eps_matrix(c, N, dps, parity=0)` | E(f) = ∫ g(x) ε(e^{\|x\|}) dx | CC eq. 84, 91 |
| `delta_matrix(c, N, dps, parity=0)` | D(f) = ∫ g(x) δ(e^{\|x\|}) dx | CC eq. 49, 56 |
| `pole_matrix(c, N, dps)` | P(f) = 2∫ g cosh(x/2) (theory §0) | = CCM W02 |
| `R_inf_matrix(c, N, dps)` | R_∞ = Q_∞ − T_∞ = P − E | |
| `eps(rho, dps, parity=0)`, `delta(rho, dps, parity=0)` | the scalar kernels, symmetric under ρ → 1/ρ | |
| `prolate_data(dps, parity=0)` | dict: `lam`, `v` = λ²/(1−λ²), `edge` = ξ_n(1), `ks`, `coef` (Legendre coefficients of φ̃_n), `e` (Taylor coefficients of η_n), `alpha` (of A1), `n_max`, `J`, `K` | CC s4 |
| `constraint_rows(c, N, which)`, `null_basis(rows, dim)`, `to_real(M, N)`, `real_basis(N)` | the function class, in the real basis [U_0, C_1..C_N, S_1..S_N] | CC Thm 6.11 |
| `calibrate.analyze_cell(c, N, dps)` | spectra and inertias of T_∞ and R_∞ on the full space and the classes | |

`arch_type`: `None`/`"R"` is the source case (Γ_ℝ(s), even sector, ζ).
`"R_odd"` is the odd sector (Γ_ℝ(s+1), sine transform, odd prolates).
`"C"` is Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1) as the sum of the two. The odd trace
identity is a derivation by analogy in this session, not in CC (RESULTS §4).
The conductor term of a ramified character (log 23 for ζ_{Q(√−23)}) is **not**
archimedean and is not included in any block here.

## 3. S_∞ as a projection (what two_adic/ composes with)

Two Hilbert spaces, identified by CC's unitary w (eq. 17):
L²(ℝ)_ev with ⟨η|ξ⟩ = ∫_0^∞ η̄ξ dx (CC eq. 16) and L²(ℝ*_+, d*u) with
(wξ)(u) = u^{1/2} ξ(u). Fourier: F ξ(y) = ∫ ξ(x) e^{−2πixy} dx (CC eq. 24,
= CCM 2310.18423's e_∞ up to conjugation, which is invisible on even
functions). Cutoff λ = 1 in both x and frequency (CC's Λ = 1; CCM's
S_1(ℝ, e_∞)). Even sector by default (parity 0); parity 1 is the odd
sector with the sine transform. Scaling ϑ_m(λ)g(v) = g(v/λ) on
L²(ℝ*_+, d*u) (CC eq. 30), equivalently (ϑ(λ)ξ)(v) = λ^{-1/2}ξ(v/λ) on
L²(ℝ)_ev (eq. 61).

The projection, in L²(ℝ*_+, d*u):

    S_∞ = 1 − Σ_n ( |x_n⟩⟨x_n| + |z_n⟩⟨z_n| )              (CC eq. 81)
        = M_{1[u ≥ 1]} − Σ_n |z_n⟩⟨z_n|                     (ran P = Sonin ⊕ span z_n)

    x_n(u) = u^{1/2} φ̃_n(u) 1_{u<1}          (CC ξ_n, orthonormal)
    z_n(u) = u^{1/2} η_n(u) 1_{u≥1} / √(1 − λ_n²)   (CC ζ_n, orthonormal)

- φ̃_n = prolate PS_{2n,0}(2π, ·) normalized ∫_0^1 φ̃_n² = 1, φ̃_n(1) > 0:
  `phi_tilde(n, x, dps, parity)` (any real x, analytic continuation).
- η_n = F ξ_n = λ_n φ̃_n, entire: `eta_all(s, dps, parity, nvec)` returns
  [η_0(s) … η_{nvec−1}(s)] for **any** s ≥ 0 (spherical-Bessel route,
  no truncation in s). `sonin_z_all(u, dps, parity, nvec)` returns
  [z_n(u)].
- λ_n: `prolate_data(dps, parity)["lam"]` (CC's printed list reproduced).
- Legendre coefficients: `prolate_vectors(dps, parity, nvec)["coef"]`,
  `["ks"]` (φ̃_n = Σ coef[n][i] P_{ks[i]}).

**Use the second form.** Σ_n |x_n⟩⟨x_n| = M_{1[u<1]} converges only
slowly on window functions (their jump at the window edge), while the z-sum
converges super-exponentially on vectors supported in u ≤ X, because
|η_n| on [1, X] is tiny once n ≫ πX. Measured at dps 40 (sizes |η_n(X)|):

| n | 10 | 20 | 30 | 40 | 50 |
|---|---|---|---|---|---|
| X = √3 | 2.6e−5 | 1.0e−20 | 9.2e−41 | 8.9e−64 | 5.5e−89 |
| X = 3 | 0.23 | 1.2e−10 | 3.9e−25 | 1.1e−42 | 1.8e−62 |

So for supports inside u ≤ X keep n < K with |η_K(X)|² below your target;
`nvec = 60` covers X ≤ 3 at dps 40. For vectors with support beyond u = 3
(for example after a Neumann series in ϑ(2)), K must grow like πX; the
representation stays exact, only the truncation moves. Checked: for
v = 1_{[1, 1.5]}, F(S_∞ v) vanishes on [−1, 1] to 10^{-35} with 40 terms
(`test_projection_maps_into_sonin_space`).

**On the CCM basis.** `S_inf_window_matrix(c, N, dps, u0=None)` returns
(⟨V_m|S_∞|V_n⟩, K, tail) for V_n(u) = U_n(log(u/u0)) on [u0, u0·c]
(default u0 = c^{−1/2}, the CCM placement [λ^{−1}, λ]). S_∞ is not
scale invariant, so this compressed matrix depends on u0. The trace term
does not: Tr(ϑ(g)S_∞ϑ(g)*) = Tr(ϑ(g ∗ g*)S_∞) is a function of the
autocorrelation.

**The trace functional.** For every h ∈ C_c^∞(ℝ*_+) (not only
autocorrelations, not only even h):

    Φ_∞(h) := Tr(ϑ(h) S_∞) = W_∞(h) + ∫ h(ρ) ε(ρ) d*ρ      (CC Thm 4.7)

with ε(ρ) = ρ^{1/2}A(ρ) − ρ^{-1/2}A(1/ρ) for ρ ≥ 1, ε(1/ρ) = ε(ρ),
A = A0 + A1, A0(y) = 2[Si(2π(1−y))/(2π(1−y)) + Si(2π(1+y))/(2π(1+y))],
A1(y) = Σ_n v_n ∫_0^1 η_n(t)η_n(yt) dt (`eps(rho, dps)`), and
ρ^{1/2}A0(ρ) = δ(ρ) (CC eq. 49). For a translated autocorrelation
h(x) = g(x − s) the ε part is ∫ g(u) ε(e^{|u+s|}) du; the shifted W_∞
matrix is not built here (ask through the coordinator if needed).

## 4. The function class (CC Thm 6.11, Thm 1)

`constraint_rows(c, N, which)` returns real row vectors in the real basis:

- `"minus"`: ĝ(−i/2) = 0, i.e. ∫_0^L F(y) e^{−y/2} dy = 0 (Thm 6.11's one
  condition; it kills the pole term P on the class);
- `"plus"`: ∫ F e^{+y/2} = 0 (reflection of "minus"; same spectra);
- `"zero"`: ĝ(0) = ∫ F = 0 (added in Thm 1 / eq. 4).

C1 = {"minus"}, C2 = {"minus", "zero"}. Restrict with
`B = null_basis(rows, 2N+1)`, `B.T * to_real(M, N) * B`.

## 5. JSON files

`cells_dps40.json` and `cells_dps60.json` (written by `run_cells.py --dps D`),
all numbers as decimal strings at that dps:

- `prolate.even` / `prolate.odd`: `lam` (first 8), `sum_lam2`,
  `sum_lam2_closed`, `t_edge` (CC's t(n), first 5), `eps1p_series`,
  `eps1p_split` (even), `n_max`, `J`, `K`; `prolate.eps`, `prolate.delta`,
  `prolate.eps_odd`: ρ → value at ρ ∈ {1.1, 1.2, 1.5, 2, 2.5, 3}.
- `calibration[c][N]` for c ∈ {1.5, 1.9, 2.0}, and `mission[c][N]` for
  c ∈ {2.2, 2.5, 2.9}, N ∈ {8, 16, 32}: `T_low`, `T_inertia`,
  `R_full_low`, `R_full_inertia`, `R_C1_low`, `R_C1_inertia`, `R_C2_low`,
  `R_C2_inertia` (inertia = [negative, zero, positive], zero band
  |λ| ≤ 10^{-(dps−10)}), `cstar` (sup over C1 of E/|∫F|², None when C2 has a
  negative), `thm611_low` (lowest eigenvalue of R + c0|∫F|² on C1,
  c0 = 4·2.94355/log 2), `K_top` (two largest Rayleigh-Ritz values of CC's
  K_I), `seconds`.
- `moments[c]` for the mission cells: `A_even`, `A_odd`, `E_even`, `E_odd`,
  `P`, each `{"s": [s_0..s_32], "d": [d_0..d_32]}`. T_∞ at any N ≤ 32 is
  `form_from_moments(sA + sE, dA + dE, N)` (sums taken entrywise on the
  first N+1 entries); Γ_ℂ adds the odd pair.
