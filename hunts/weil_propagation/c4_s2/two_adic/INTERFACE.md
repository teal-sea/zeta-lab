# INTERFACE: two_adic/ (gap (b), P_2 through E_S, assembly of T_S)

Shared basis and cells as in `../MISSION.md`: U_n(y) = L^{-1/2} exp(2πiny/L)
on [0, L], L = log c, n = −N … N, index 0 = n = −N; a quadratic form F is the
matrix M with F(f) = v* M v for f = Σ v_n U_n; inner products are conjugate
linear in the first slot. Python: `PYTHONPATH=<worktree> <venv python>`;
modules are imported by basename after putting this folder on `sys.path`
(the test files show the pattern).

## Delivered

| function | returns | notes |
|---|---|---|
| `ta_es.shift_corr(c, N, dps, k=1)` | C^{(k)}_{mn} = ⟨U_m, D^k U_n⟩, closed form | D = dilation by 2 = shift by log 2 in y; zero when k log 2 ≥ L |
| `ta_es.theta_gram(c, N, alphas, dps)` | Σ_j Gram of Θ_{α_j} = 1 − α_j 2^{−1/2} D on the window basis | 2 < c < 4 only (three-term form) |
| `ta_es.es_gram(c, N, alphas, dps)` | Σ_j Gram of E_S (the class of 1_{Z_2} ⊗ f), unitary α | 2 < c < 4 only |
| `ta_es.prime_block_from_C(c, N, alphas, dps)` | Wp_α = (log 2/√2) Σ_j (α_j C + ᾱ_j C*) | equals the CCM prime block for real α |
| `ta_es.galerkin_prime_block(c, N, dps)` | the prime block read from `weil_trunc/galerkin.py` | independent route |
| `ta_data.validate(data, degree=None, tol=None)` | `LocalData` or raises `NonUnitaryLocalData` | data = `("satake", alphas)` or `("tower", {k: s_k})` with `degree` |
| `ta_ts.T_S_matrix(c, N, dps, local_data, arch_type="Gamma_R", s_inf=None)` | T_S matrix, or raises | see order of checks below |
| `ta_ts.delta_T_matrix(grid, zetas, alpha, L, N)` | (ΔT, M_inf, M_S) for a finite mode family on a grid | float64; exercised on synthetic modes only |
| `ta_hs.hs2_partial(K, alpha=1, dps=30)` | ‖P F_S P‖²_HS over Euler levels j ≤ K | closed form in Si |
| `ta_local.local_report(K)` | exact local statements at 2 | sympy rationals |

`T_S_matrix` order of checks: (1) local data at 2: `NonUnitaryLocalData`
for any |α| ≠ 1 or a tower that is not a power-sum tower of d unitary
parameters (W_a and the Epstein (1,1,6) tower are refused);
`local_data=None` switches the place 2 off and returns kernel/'s T_inf;
(2) `arch_type`: `"Gamma_R"` accepted, `"Gamma_C"` raises `FrameworkLimit`
(no idele class character of C_S is odd at ∞ and unramified at 2);
(3) kernel/ data: raises `KernelUnavailable` until S_∞ is routed. It never
returns a number it did not compute. Local data at 2 for the controls are in
`ta_data`: `ZETA`, `DEDEKIND_Q_SQRT_M23`, `W_A_QUARTER`, `EPSTEIN_116_TOWER`.

## JSON

`ta_es_cells.json`: `meta.bound_lo`, `meta.bound_hi` (3/2 ∓ 1/√2), and
`cells[]` with keys `c`, `N`, `dps`, `theta_gram_eig_min`,
`theta_gram_eig_max`, `theta_gram_max_imag`, `prime_block_eig_min`,
`prime_block_eig_max`, `identity_defect`, `galerkin_dev`, `seconds`.

`ta_ts_cells.json`: `cells[]` with keys `c`, `N`, `dps` and one entry per
data set (`zeta`, `dedekind_Q_sqrt_m23`, `W_a_quarter`, `epstein_116_tower`,
`place_2_off`), each `{outcome, message}` with outcome one of
`refused_nonunitary`, `framework_limit`, `awaiting_kernel`, `matrix`;
`hs2_P_FS_P` with `archimedean`, `partial_sums` (K → value), `asymptote`.

## Consumed (from kernel/, not yet routed)

The composition (RESULTS.md s5) needs S_∞ through its complement,
1 − S_∞ = P + Q_∞ with Q_∞ the projection onto span{ζ_n} (Connes-Consani
arXiv:2006.13771 Prop 4.5, eq. (81)), in either form:

- ξ_n on [0, 1] (coefficients in a stated basis, or a callable at a stated
  dps) with λ_n, from which ζ_n = (1 − P) F ξ_n / √(1 − λ_n²) and its Mellin
  transform follow; or
- ζ_n on u ≥ 1 together with their Mellin transforms on a stated s-grid.

The number of modes must cover the Mellin band of the window basis (about
2πN/L, i.e. of order 100 modes at N = 32), not only the first few prolates:
the semilocal time-frequency operator is not Hilbert-Schmidt (RESULTS.md s6).
Also `T_inf_matrix(c, N, dps)` on the shared basis, since T_S = T_inf + ΔT.
