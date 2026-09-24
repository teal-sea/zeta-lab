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
| `ta_prolate.ProlateModes(nvec, dps)`, `hats_modes`, `delta_T_cells(pm, cells, N, S)` | kernel/'s prolate modes in float64; ζ̂_n, b̂_n; ΔT per cell, and diagnostics `gram_z_offI`, `cond_Gb` (formed G_b, float64; saturates near 1e16 above 1/eps), `cond_Fz`, `cond_Fb` (the Gram factors, from singular values; cond(G) = cond(F)², reliable while cond(F) is well below 1/eps). Reading rule (RESULTS.md s10.3 A2): ρ measured good to 1.4e−5 relative at cond(F) = 6.7e11 and off by 6.5e−2 at 3.8e14; a build with cond(F) above about 4e14 is not determined by its float64 samples; between the two, not measured | Mellin route, measured grade |
| `ta_mellin.rho(hat_rows, *, factor)` | ρ(s) = x* G⁻¹ x, x = conj(ŵ(s)), for G = F* F, from a Householder QR of F and a triangular solve; G is never formed | since 2026-09-24 (RESULTS.md s10); `factor` is keyword-only so that a Gram matrix cannot be passed as a factor by mistake; arithmetic error grows like eps·cond(F) |
| `ta_mellin.rho_inv(hat_rows, G)` | the route before 2026-09-24, `np.linalg.inv` of the formed G | kept as the reference; error grows like eps·cond(G) = eps·cond(F)² |
| `ta_prolate.gram_factor_s(H, sw, J, S, A, dil)`, `ta_mellin.gram_factor_v(fns, Kmax, per_panel)` | F with `gram_s(...)` = F* F (weighted samples plus the two tail rows), resp. `gram_v(fns)` = F* F | `gram_s`, `gram_v` unchanged |
| `ta_rho_diag` parts, `ta_rho_check` parts | the diagnosis of cond(G) (s10.1) and the acceptance runs of the QR route (s10.3) | one part per process; JSON below |
| `ta_ts.KernelProvider(nvec=None, S=None)` | `T_inf_matrix` (kernel/'s moments JSON) and `delta_T` | the provider `T_S_matrix` uses by default |
| `ta_gram_probe.run(nvec, S)` | on c = 2.2, N = 8: ΔT, the Gram probe, T_S's lowest eigenvalues, max \|G_z^s − I\| | measurement for RESULTS.md §7b |
| `ta_gram_probe.merge_modal(out)` | copies modal/out/gram_*.json runs into `out` unchanged, with `source`; adds `modal_calibration` | reads only; idempotent |
| `ta_gram_probe.band_terms(runs, nvec, S=4800)` | the §7b band's three terms at nvec (`S`, `nvec`, `probe`; None where no run forms one), `band`, `binding`, `complete` | `band` is a lower bound unless `complete` |
| `ta_hs.hs2_partial(K, alpha=1, dps=30)` | ‖P F_S P‖²_HS over Euler levels j ≤ K | closed form in Si |
| `ta_local.local_report(K)` | exact local statements at 2 | sympy rationals |

`T_S_matrix` order of checks: (1) local data at 2: `NonUnitaryLocalData`
for any |α| ≠ 1 or a tower that is not a power-sum tower of d unitary
parameters (W_a and the Epstein (1,1,6) tower are refused);
`local_data=None` switches the place 2 off and returns kernel/'s T_inf;
(2) `arch_type`: `"Gamma_R"` accepted, `"Gamma_C"` raises `FrameworkLimit`
(no idele class character of C_S is odd at ∞ and unramified at 2);
(3) builds T_S = T_inf (kernel/) + ΔT and returns a float64 numpy array
(ΔT is of measured grade, error band 3.5e−3 to 8.2e−3 by (c, N), RESULTS.md §5b
and its correction notice; this line said "about 6e−3" before the Kmax rerun;
on c = 2.2, N = 8 the mode truncation is larger, 4.5e−3 in spectral norm from
80 to 100 modes, RESULTS.md §7b);
`dry_run=True` stops after the checks. It never returns a number it did not
compute. Defaults: nvec = max(80, 8N/L + 40) prolate modes and
S = max(1200, 24πN/L); at N = 32 use at least 200 modes (130 leave
spurious residual pairs; rechecked under the Kmax rule, it stands). The
default nvec at N = 32 is up to 364 modes (Kmax 15), by extrapolation well past the 10-minute
local limit: pass nvec and S to `KernelProvider` explicitly. The w-range
must satisfy 2^Kmax ≳ n_max²/(2π) (`ta_prolate.kmax_for`, guarded in
`hats_modes`): the asymptotic tail in 1/w has term ratio about
(2n)²/(4π(m+1)W) and diverges in practice below that (at W = 2^10 and
n = 199 its terms reach about 1 against a first term of 4e−5). Local data at 2 for the controls are in
`ta_data`: `ZETA`, `DEDEKIND_Q_SQRT_M23`, `W_A_QUARTER`, `EPSTEIN_116_TOWER`.

## JSON

`ta_es_cells.json`: `meta.bound_lo`, `meta.bound_hi` (3/2 ∓ 1/√2), and
`cells[]` with keys `c`, `N`, `dps`, `theta_gram_eig_min`,
`theta_gram_eig_max`, `theta_gram_max_imag`, `prime_block_eig_min`,
`prime_block_eig_max`, `identity_defect`, `galerkin_dev`, `seconds`.

`ta_ts_cells.json`: `cells[]` with keys `c`, `N`, `dps` and one entry per
data set (`zeta`, `dedekind_Q_sqrt_m23`, `W_a_quarter`, `epstein_116_tower`,
`place_2_off`), each `{outcome, message}` with outcome one of
`refused_nonunitary`, `framework_limit`, `awaiting_kernel`, `matrix`
(ζ and place 2 off are `matrix`);
`hs2_P_FS_P` with `archimedean`, `partial_sums` (K → value), `asymptote`.

`ta_ts_prolate.json`: `tate_check_max_abs`, `seconds_total`, and `rows[]`
with keys `nvec`, `S`, `N`, `c`, `T_inf_eig_min`, `T_inf_eig_max`,
`T_S_eig_low3`, `T_S_eig_max`, `T_S_n_below_m002`, `gram_sensitivity`,
`resid_top8` (eigenvalues of ΔT + Wp largest in modulus, signed),
`resid_n_above_01`, `resid_n_below_m01`, `seconds_hats`, and `Kmax` on the rows
rerun under `kmax_for` (configurations 2 to 4; `seconds_by_config` records
those reruns). Since the regeneration of 2026-09-24 under the QR route of
`rho` (RESULTS.md s10.5) every row also carries `cond_Fz`, `cond_Fb` and `Kmax`. Delivered rows: (nvec, S) = (80, 1200) for N = 8,
(120, 1600) for N = 16, (200, 2400) for N = 32. Converged to what (checker/'s
measurement, RESULTS.md correction notice; this paragraph listed all four as
"converged" before): (80, 1200) to about 5.6e−3 at N = 8 and **not** at
N = 16 (80 → 120 modes moves T_S by up to 7.8e−2); (120, 1600) to 1.6e−2 at
c = 2.2 and within the probe at 2.5 and 2.9; (200, 2400), under the QR route
of `rho` (checker/ s7.8, 3e36fa4): to 3.0e−2 at c = 2.2 and 1.4e−2 at 2.5 (set by
the 240 and the 319-mode refinement respectively) and within the probe (8.2e−3) at 2.9, where no
refinement moves T_S by more than 4.95e−3. On the old route (checker/ s7.7,
3dc0a74) its 240-mode refinement moved T_S by 3.9e−2, 2.4e−2, 3.2e−2, and
checker/ read that row as not a clean refinement. For checker/: R_S = Q − T_S with Q = Q_∞ − Wp, so
R_S = R_∞ − (ΔT + Wp).

`ta_gram_probe.json`: `c`, `N`, `Q_low` (checker/'s value), and `runs`
keyed `"nvec,S"` with `nvec`, `S`, `Kmax`, `dT` (the matrix), `dT_probe_maxentry`,
`dT_probe_norm2`, `TS_low3`, `gz_dev`, `gz_dev_diag_max`, `seconds`, and
`source` (`file`, `platform`, `python`; for modal/'s runs also `tree_commit`,
`blas_core`, `avx512`, `cpu_seconds`, `peak_rss_mib`). `modal_calibration`:
modal/'s copy of run `80,4800` against the local one (`max_abs_diff_dT`,
`max_abs_diff_scalars`, `file`, `tree_commit`, `platform`).

## Consumed (from kernel/, routed 2026-09-23 22:10)

Used as routed: kernel/INTERFACE.md §3 (`prolate_vectors`, `prolate_data`,
`zeta_mellin_all` as the independent check, `form_from_moments` with the
`moments` of `cells_dps40.json`). The composition (RESULTS.md s5) needs S_∞
through its complement,
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

## JSON of follow-up 3 (RESULTS.md s10)

`ta_rho_diag.json`: `toeplitz_cond_ratio` (33.97); `scan80`, `scan200` with
`nvec`, `Smax`, `Kmax`, `hats`, `seconds`, `rows[]` of `S`, `S_over_nvec2`,
and per family `z`, `b`: `eig_min`, `eig_max`, `cond_formed` (float64 G),
`cond_F`, `cond_F_sq`; `refine` (`rows[]` with `label`, `s_per_panel`,
`w_per_panel`, `Kmax`, `S`, `z`, `b`); `lowdir`; `hats_accuracy` (float64
hats against kernel/'s closed form at dps 30: `nodes[]`, `max_abs`,
`max_rel`); `node_counts[]`.

`ta_rho_check.json`: `eps`; `A1` keyed `"nvec,S"` (`cond_Fz`, `cond_Fb`, per
family `max_dev`, `max_rho`, `bound`, `ratio_to_eps_condG_rho`, and
`dT_change_norm2` keyed `"c|N"`); `A2` keyed by S (`cond_Fz`,
`new_max_rel_dev`, `old_max_rel_dev`, `sample_max_abs_dev`, `J_max_abs_dev`,
`A_max_abs_dev`, `max_rho_ref`, `n_nodes`, `n_compared`); `A3` (`old`, `new`
keyed by c: spectral change of ΔT under a 2^−52 relative perturbation);
`A4` (`cond_Fz`, `cond_Fb`, `band`, `cells` keyed by c with `new_low3`,
`old_low3`, `new_n_below_band`, `old_n_below_band`, `new_2400_low3`,
`new_S_response_norm2`); `gram_probe_dependence` keyed `"nvec,S"`.
