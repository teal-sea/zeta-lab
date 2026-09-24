1. **Built: S_∞ (the archimedean Sonin projection) on windows, with no numerically identified data, and `T_inf_matrix(c, N, dps)` = A + E on the shared CCM basis (CC Thm 4.7).** The ε-kernel splits exactly into a closed form in Si plus a prolate series with weights λ_n²/(1−λ_n²). **Grade: derivation, unreviewed; numerics hardened by independent routes.** S_∞ is also delivered as a projection on L²(ℝ*_+, d*u), for two_adic/.
2. **Calibration against Connes-Consani arXiv:2006.13771 (measured, dps 40, confirmed at dps 60 to 5.1e−39).** CC's printed prolate numbers are reproduced, including ε'(1+) = 22.99648. T_∞ is positive semidefinite at every cell. At the Thm 6.11 window (c = 2), the Galerkin lower bounds for CC's λ_max(K_I) are 1.0403, 1.0460 and 1.0488 (N = 8, 16, 32). Their first-order extrapolation is 1.05160; CC give 1.05158 ± 0.00122. The best constant c*(N) is 12.43, 13.88 and 14.56, inside CC's (13, 17).
3. **R_∞ = Q_∞ − T_∞ = P − E, count of negative eigenvalues (measured, the same at N = 8, 16, 32 and at dps 40 and 60).** Full space / Thm 6.11 class C1 / Thm 1 class C2: c = 1.5: 0/0/0; c = 1.9: 2/1/0; c = 2.0: 2/1/0, in agreement with Thm 6.11 and Thm 1. Mission cells, archimedean part only: c = 2.2 and 2.5: 2/1/0; c = 2.9: 2/2/1. The second eigenvalue of K crosses 1 between c = 2.5 and 2.9.
4. **The Γ_ℂ type (Dedekind ζ_{Q(√−23)}) is supported as the even plus odd sectors.** The odd-sector trace identity is a derivation by analogy with CC, unreviewed. T_odd is positive semidefinite on every cell tested. The odd archimedean block matches weil_trunc's DH block minus log 5 to below 10^{−36}.
5. **Open:** the composition with P_2 (two_adic/) and the cutoff question (cutoff/). Not built here: the shifted W_∞ matrix for translated autocorrelations. The disk (complex-place) Sonin alternative to "even + odd" is also not built. ALIGNMENT s5: gap (a) is **closed as a construction** (no longer an obstruction). The C4 question itself remains **unresolved** and is not addressed by this folder.

# RESULTS: kernel/, gap (a), the archimedean Sonin projection S_∞ on windows

Worker session of 2026-09-23 on branch `teal-sea/weil-c4-s2`, folder
`hunts/weil_propagation/c4_s2/kernel/`. Nothing here is a claim about RH.
Grades follow the `AGENTS.md` ladder. Every number below is asserted by
`test_sonin.py` in this folder (the pinning test is named in brackets, or
in the table of s7). Code: `sonin.py` (construction), `calibrate.py` (class
analysis), `run_cells.py` (writes `cells_dps40.json`, `cells_dps60.json`).
Interface for two_adic/ and checker/: `INTERFACE.md`.

## 0. Status (ALIGNMENT s5)

- **Gap (a): closed as a construction.** S_∞ is computable on window
  functions, both as the trace functional that T_∞ needs and as a
  projection on L²(ℝ*_+, d*u).
- **C4 (theory §7.2): unresolved.** Nothing in this folder composes S_∞
  with the place 2. That is two_adic/'s gap (b).
- The S = {∞} calibration agrees with every statement of the source it was
  compared with (s3). Nothing was refuted.

## 1. The objects, from the source

All from Connes-Consani arXiv:2006.13771 ("CC"), read in full for s1-s6
and Thm 6.11; PDF in the session scratchpad, not committed.

| object | CC reference | statement |
|---|---|---|
| Hilbert space | eq. (16), (17) | L²(ℝ)_ev with ⟨η\|ξ⟩ = ∫_0^∞ η̄ξ; unitary w: L²(ℝ)_ev → L²(ℝ*_+, d*λ), (wξ)(λ) = λ^{1/2}ξ(λ) |
| Fourier | eq. (24) | F ξ(y) = ∫ ξ(x) e^{−2πixy} dx, unitary, F² = 1 on even functions |
| scaling ϑ | eq. (61), (30) | (ϑ(λ)ξ)(v) = λ^{−1/2}ξ(v/λ); ϑ(f) = ∫ f(λ)ϑ(λ) d*λ |
| Sonin space, S_∞ | Def 4.4, eq. (72), Thm 4.7 | S(1,1) = {ξ even: ξ = 0 and Fξ = 0 on [−1,1]}; S_∞ its orthogonal projection |
| prolate data | eq. (66)-(70), Prop 4.5 | φ_n = PS_{2n,0}(2π, ·), ∫_{−1}^{1} φ_n e^{2πixω} dx = λ_n φ_n(ω); ξ_n = φ_n on [−1,1] normalized; η_n = Fξ_n; ζ_n = η_n 1_{\|x\|≥1}/√(1−λ_n²) |
| spectral form of S_∞ | eq. (81) | P P̂ P = Σ λ_n² \|ζ_n⟩⟨ζ_n\| + S_∞, P = 1_{\|x\|≥1} |
| trace term | Thm 4.7, eq. (83)-(84) | Tr(ϑ(f)S_∞) = W_∞(f) + ∫ f(ρ^{−1}) ε(ρ) d*ρ, ε(ρ) = Σ λ_n(1−λ_n²)^{−1/2}⟨ξ_n\|ϑ(ρ^{−1})ζ_n⟩ for ρ ≥ 1, ε(ρ^{−1}) = ε(ρ) |
| W_∞ | eq. (53), (39), (163) | W_∞ = −W_R, τ(ρ) = ρ^{1/2}/2 (1/(1+ρ) + 1/\|1−ρ\|) (principal value), equivalently ∫ f̂(t) 2θ'(t) dt/2π |
| trace remainder δ | Def 2.1 eq. (41), eq. (49), (89) | δ(ρ) = 2ρ^{1/2}[Si(2π(1+ρ))/(2π(1+ρ)) + Si(2π(ρ−1))/(2π(ρ−1))], ρ ≥ 1; δ = Σλ_n²⟨ζ_n\|ϑζ_n⟩ + ε |
| function class, Thm 6.11 | eq. (141) | support in [2^{−1/2}, 2^{1/2}] (our c = 2), **one** condition ĝ(−i/2) = 0; then W_∞(g∗g*) ≥ Tr(ϑ(g)S_∞ϑ(g)*) − c₀\|ĝ(0)\|², c₀ = 4γ/log 2, γ ≈ 2.94355 (Lemma 6.10) |
| best constant | Rem 6.12 | 13 < c* < 17 |
| Thm 1, eq. (4) | Intro | adding ĝ(0) = 0 removes the remainder: W_∞(g∗g*) ≥ Tr(ϑ(g)S_∞ϑ(g)*) |
| K_I | Prop 5.5, s6.1-6.2, eq. (134) | E∘Q on L²(I) is −2ε'(1+)(Id − K_I); for \|I\| = log 2, λ_max(K_I) = 1.05158 (within 0.00122), next 0.687925 |

**Translation to the mission notation** (our f is CC's g). A window
function F on [0, L], L = log c, sits in L²(ℝ*_+, d*u) as u ↦ F(log u)
(any translate gives the same traces). Its autocorrelation g is CC's
f = g∗g*, and d*ρ = dx. Then:

- A(f) of theory §0 is CC's W_∞. It is the digamma form
  (ψ(1/4) − log π)g(0) + ∫_0^∞ 2[g(0) − g(x)] e^{−x/2}/(1−e^{−2x}) dx,
  which equals the §0 formula through ψ(1) − ψ(1/4) and the tail
  −log(1 − e^{−2L}) (pinned in [test_arch_block_matches_theory_s0_formula_verbatim]).
- **T_∞(f) := Tr(ϑ(f)S_∞ϑ(f)*) = A(f) + E(f)**, where
  E(f) = ∫_{−L}^{L} g(x) ε(e^{|x|}) dx.
- **R_∞ := Q_∞ − T_∞ = (P + A) − (A + E) = P − E.** The pole block P
  vanishes on the class C1 (ĝ(−i/2) = 0 means ∫F e^{−y/2} = 0). So on C1,
  R_∞ = −E, and Thm 6.11 reads E ≤ c₀|∫F|² there.
- ĝ(0) = ∫_0^L F dy.

## 2. The construction (gap (a))

**The kernel of E in closed form plus a fast series (derivation, this
session, unreviewed).** With η_n = Fξ_n = λ_n φ_n (entire, CC after
Prop 5.3), CC's ε is Σ_n λ_n²/(1−λ_n²) ρ^{1/2}∫_{1/ρ}^{1} φ_n(x)φ_n(ρx) dx
(their proof of Lemma 5.4). Splitting ∫_{1/ρ}^1 = ∫_0^1 − ∫_0^{1/ρ}:

    ε(ρ) = ρ^{1/2}A(ρ) − ρ^{−1/2}A(1/ρ),   A(y) = Σ_n (1−λ_n²)^{−1} ∫_0^1 η_n(t)η_n(yt) dt.

Write 1/(1−λ²) = 1 + λ²/(1−λ²). The "1" part sums by completeness of
{ξ_n} in L²[0,1], because Σ_n η_n(t)η_n(s) = 4∫_0^1 cos(2πxt)cos(2πxs) dx:

    A0(y) = 2[Si(2π(1−y))/(2π(1−y)) + Si(2π(1+y))/(2π(1+y))],   ρ^{1/2}A0(ρ) = δ(ρ) exactly,
    A1(y) = Σ_n v_n ∫_0^1 η_n(t)η_n(yt) dt,   v_n = λ_n²/(1−λ_n²).

The weights v_n decay super-exponentially, with 20 terms at dps 40 and
23 at dps 60 [prolate block in the JSON]. A1 is stored as an even
polynomial from the Taylor moments of η_n. So the only non-elementary
input to S_∞ is the standard prolate eigenproblem (a tridiagonal
Legendre-Galerkin matrix), solved to the working precision. No
"numerically identified" data enter: CC s6 identifies data only for the
constant c, not for S_∞.

**Checks of the split (independent routes, hardened):**

- Σ_n of the prolate Taylor data reproduces A0 to 10^{−30}.
- ρ^{1/2}A0 equals CC eq. (49) to 10^{−35} [test_completeness_part_is_delta_closed_form].
- ε from the split equals CC's own series ε = Σ v_n ρ^{1/2}∫_{1/ρ}^1 φ̃φ̃(ρ·), by direct quadrature at ρ = 1.6, to 10^{−30} [test_eps_basic_properties].
- ε'(1+) by CC Lemma 5.4 (Σ v_n ξ_n(1)²) and by differentiating the split agree to 10^{−30} [test_edge_terms_and_eps_derivative_match_cc].

**The Galerkin blocks.** A form ∫ g(x) K(|x|) dx has matrix
M(n,m) = ∫_0^L K q_nm (CCM Lemma 2.3). It is built from two moment
sequences s_k, d_k (`form_from_moments`), computed by Gauss-Legendre with
192 or 384 nodes. Doubling the rule changes no moment by more than 10^{−40}
at dps 40 [test_quadrature_rule_by_doubling].

- **A** is built from the digamma form at interior nodes with expm1.
  The x → 0 limit is removable, so no finite difference is taken
  anywhere; this is the defect of the rejected prior attempt, not repeated.
  A agrees with the CCM closed forms of `hunts/rogue_frontier/weil_trunc/galerkin.py`
  to below 10^{−36} at c = 1.5 and 2.5, N = 8, dps 40
  [test_arch_block_matches_ccm_closed_forms].
- **P** matches CCM's W02 to below 10^{−36} [test_pole_block_matches_w02].

**S_∞ as a projection (for two_adic/, INTERFACE §3).** ran P equals Sonin
⊕ span{ζ_n}: a vector of ran P orthogonal to both would satisfy
‖P̂v‖² = ⟨v, PP̂Pv⟩ = 0, and ran P ∩ ker P̂ = 0 by uncertainty. Hence

    S_∞ = 1_{|x|≥1} − Σ_n |ζ_n⟩⟨ζ_n|    (ordinary argument from CC eq. (81), unreviewed).

The sum converges super-exponentially on vectors supported in |x| ≤ X.
η_n is computed for every s by a spherical-Bessel sum. It agrees with the
Taylor route to below 10^{−34} for s ≤ 2.5
[test_eta_bessel_route_matches_taylor_route]. For v = 1_{[1,1.5]}, the
Fourier transform of S_∞v vanishes on [−1,1] to below 10^{−35} with 40
terms [test_projection_maps_into_sonin_space]. The compressed matrix
⟨V_m|S_∞|V_n⟩ on the CCM basis at [c^{−1/2}, c^{1/2}] has its spectrum in
[0, 1], with truncation tail below 10^{−45} at K = 20 (c = 2.5)
[test_window_projection_matrix].

For two_adic/'s composition through the Mellin variable, the transforms
M_n(s) = ∫_1^∞ ζ_n(v) v^{−1/2−is} dv are given in closed form by Tate's local
functional equation (`zeta_mellin_all`). They are checked three ways
[test_zeta_mellin_closed_form]: the moment recurrence against quadrature
to 10^{−38}, the Tate constant on 1_{[0,1]} to 10^{−38}, and a direct
integral over [1, V], whose error falls like V^{−2} and is below 10^{−4} at
V = 60. Any number of modes is available (`prolate_vectors`, orthonormal to
10^{−40} for 150 modes [test_many_modes_orthonormal]). λ_n is resolved
only for n below `n_max`; beyond it the interface uses η_n directly.

## 3. Calibration against CC (S = {∞}), measured

Prolate data (CC s4, Rem 4.6, Lemma 5.4, footnote 7), dps 40:

- λ_0 … λ_5 reproduce CC's printed 0.999971, −0.979485, 0.524086,
  −0.0589766, 0.00273233, −0.0000762914 within half a unit of the last
  printed digit [test_prolate_eigenvalues_match_cc_list].
- Σλ_n² = 2.237484835 = 2(Si(4π)/(4π) + 1) to 10^{−35}
  [test_sum_lam2_equals_delta_at_1_closed_form].
- Even plus odd sums to 4 (CC footnote 7) [test_even_plus_odd_sum_is_4].
- t(n) = v_n ξ_n(1)² reproduce CC's 11.9719, 8.77574, 2.20528, 0.0433983,
  0.000125459, and ε'(1+) = 22.99648 (CC: 22.9965).

Positivity statements (N = 16 at every cell, both parities; N = 8, 16, 32
in the JSON):

- T_∞ = A + E ⪰ 0 (Thm 4.7).
- A + D ⪰ 0 (Cor 2.3).
- D − E ⪰ 0 (eq. (90)) [test_T_inf_psd_and_D_minus_E_psd].

**The Thm 6.11 window, c = 2** [test_calibration_statements]:

| N | λ_max(K_I) (lower bound) | next | c*(N) (lower bound) | neg. eig. of R_∞ on C1 |
|---|---|---|---|---|
| 8 | 1.040345 | 0.6578403 | 12.42835 | −0.06921652 |
| 16 | 1.046028 | 0.6720548 | 13.87771 | −0.07804222 |
| 32 | 1.048814 | 0.6792478 | 14.55663 | −0.08222624 |
| CC | 1.05158 ± 0.00122 | 0.687925 | 13 < c* < 17 | |

- λ_max(K_I) is a Rayleigh-Ritz value on {h: h/2 − h' ∈ C1 ∩ band}, via
  E(F) = 2ε'(1+)(⟨h|K_I h⟩ − ‖h‖²) with F = h/2 − h' (CC Prop 5.5,
  Lemma 3.3), so it increases in N.
- The first-order (1/N) extrapolation 2·(N=32) − (N=16) gives 1.05160
  and 15.236. This is a measured heuristic, not a bound.
- R_∞ + c₀|∫F|² ⪰ 0 on C1 and R_∞ ⪰ 0 on C2 hold at every N, as Thm 6.11
  and Thm 1 require.

**The calibration cells c = 1.5 and 1.9** (N = 8, 16, 32, same counts
at every N):

| c | T_∞ lowest (N = 32) | R_∞ negatives full/C1/C2 | C1 negative (N = 8, 16, 32) | c*(N) | λ_max(K_I) |
|---|---|---|---|---|---|
| 1.5 | 0.03772234 | 0/0/0 | none | −93.13, −81.06, −75.26 | 0.807, 0.827, 0.837 |
| 1.9 | 0.003925064 | 2/1/0 | −0.02820, −0.03582, −0.03931 | 7.422, 9.510, 10.49 | 1.023, 1.030, 1.033 |
| 2.0 | 0.002550097 | 2/1/0 | see above | see above | see above |

At c = 1.5, R_∞ ⪰ 0 already on the full space. At c = 1.9, λ_max(K_I) > 1,
so the one remainder direction of Thm 6.11 is present below log 2. This
agrees with CC's Figure 11 (PDF page 36, read off the plot, no printed
number): their largest eigenvalue crosses 1 between a = 0.5 and 0.6, below
log 1.9 = 0.642, and stays below 1 at log 1.5 = 0.405. The positive part of R_∞'s spectrum accumulates at 0
like N^{−2} (for example 1.871e−4 at c = 1.5, N = 32). That is the
essential spectrum of −E at high frequency (ε has the kink ε'(1+) > 0),
not a remainder direction. What is N-stable is the inertia and the
negative eigenvalues.

## 4. The Γ_ℂ type (task 4)

Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1), so the archimedean block is A_{a=1/4} + A_{a=3/4}.
The Sonin term is taken as S_ev ⊕ S_odd, the Sonin projection of all of
L²(ℝ) split by parity. The odd sector uses the sine transform, the odd
prolates (μ_0 … = 0.99878, −0.84956, 0.20740) and A0_odd with the sign of
the second Si term flipped.

**Grade: derivation by analogy with CC s1-s4 (cos → sin), unreviewed.**
The checks are:

- A_odd − A_even = ∫ g/(2cosh(x/2)) to below 10^{−36}. This is CC's τ
  with the sine kernel.
- A_odd equals weil_trunc's DH archimedean block minus log 5 to below
  10^{−36} [test_odd_arch_block_matches_dh_route_and_sech_identity].
- T_odd ⪰ 0, A_odd + D_odd ⪰ 0 and D_odd − E_odd ⪰ 0 at all six c (N = 16).
- Σμ² = 1.762515165 = 2(1 − Si(4π)/(4π)), and ε'_odd(1+) = 16.73365.

`T_inf_matrix(c, N, dps, arch_type="C")` returns T_ev + T_odd.

**Not included, deliberately:** the conductor term of Dedekind ζ_{Q(√−23)}
(log 23 · g(0)). It belongs to the ramified place 23, which is not in
S = {∞, 2}. Whether the complex-place (disk) Sonin space should replace
S_ev ⊕ S_odd for GL₁ over Q(√−23) is not decided here.

## 5. The mission cells c ∈ {2.2, 2.5, 2.9} (archimedean part only)

These are the S = {∞} objects that two_adic/ composes. They are not R_S.

| c | T_∞ lowest, N = 32 | R_∞ = P − E negatives full/C1/C2 | C1 negatives (N = 32) | λ_max, λ_2 of K (N = 32) |
|---|---|---|---|---|
| 2.2 | 0.001198416 | 2/1/0 | −0.1716829 | 1.068616, 0.811608 |
| 2.5 | 0.0004740128 | 2/1/0 | −0.2981016 | 1.082943, 0.9320488 |
| 2.9 | 0.0001832311 | 2/2/1 | −0.4395782, −0.01635431 | 1.08903, 1.022986 |

The counts are identical at N = 8, 16, 32 and at dps 40 and 60. Thm 6.11's
inequality with c₀ fails at all three windows, as expected: they lie outside
its support [2^{−1/2}, 2^{1/2}]. For S = {∞} alone, the remainder of
bounded rank grows from one direction (c ≤ 2.5) to two (c = 2.9); a
second vanishing condition would be needed there. The generating moments
of A, E and P (both parities) for k ≤ 32 are in `moments[c]` of both JSON
files (INTERFACE §5).

## 6. Numerics

- **Precision response.** Over every stored eigenvalue, c*, Thm 6.11 value
  and K value, dps 40 against dps 60 differ by at most 5.1e−39 (at c = 2.2,
  N = 32, c*). All inertias are identical [test_precision_response_40_vs_60].
- **Recompute.** `analyze_cell` at N = 8 reproduces the stored cells to
  10^{−30} [test_json_recompute_N8]. The N = 32 check at c = 2 is marked slow.
- **Truncations** (JSON `prolate`): 20 weighted prolates, 74 Taylor terms
  and a 76-function Legendre basis at dps 40; 23 prolates at dps 60.
- **Runtime.** One run each, single process on the operator laptop:
  `run_cells.py --dps 40` about 216 s, `--dps 60` about 365 s, both under
  the 600 s limit (the stored `seconds_total` is checked against that
  limit). The kernel test tier runs under pytest `-n 2` (s9).

## 7. Grades

| statement | grade |
|---|---|
| objects and class of Thm 6.11, s1 | read from the source, section and equation cited |
| ε = ρ^{1/2}A(ρ) − ρ^{−1/2}A(1/ρ), A0 closed form, ρ^{1/2}A0 = δ | derivation, unreviewed; hardened numerically (three routes, s2) |
| S_∞ = 1_{\|x\|≥1} − Σ\|ζ_n⟩⟨ζ_n\| | ordinary argument from CC eq. (81), unreviewed; FT check measured |
| T_∞ = A + E, R_∞ = P − E | CC Thm 4.7 used as published; translation derived here |
| A, P blocks | hardened (two independent implementations agree to 10^{−36}) |
| calibration tables s3, s5 | measured (one Galerkin route at dps 40, precision response 5.1e−39; the N-truncation is the uncertainty, and K and c* are lower bounds) |
| Richardson values 1.05160, 15.236 | measured heuristic |
| Γ_ℂ as even + odd | derivation by analogy, unreviewed; the checks in s4 are measured |

No prover was used; no statement is kernel-checked.

## 8. Threads (observations, not pursued)

- **The window where each remainder direction appears.** For S = {∞}, the
  first negative of R_∞ on C1 appears between c = 1.5 and 1.9 (CC's
  Figure 11 puts it between a = 0.5 and 0.6, that is c ≈ 1.65 to 1.82). The second,
  on C2, appears between 2.5 and 2.9. A bisection at N = 32 would locate
  both. This is the S = {∞} version of the mission's "bounded rank" count,
  and it gives two_adic/ a baseline.
- **Shifted W_∞ matrix.** Needed only if the semilocal Γ-sum produces
  translated autocorrelations h(x) = g(x − k log 2) inside the trace
  against S_∞. It would be the §0 formula applied to the even part of h.
- **Complex-place Sonin (disk prolates)** as the alternative Γ_ℂ model.
- **N-convergence is first order** in 1/N for λ_max(K_I), c* and the C1
  negative eigenvalue. This is consistent with the jump of the periodic
  Fourier basis at the window edge. A basis with edge functions would
  converge faster.

## 9. Reproduction

From the worktree root, with `PY="PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python"`:

    $PY hunts/weil_propagation/c4_s2/kernel/run_cells.py --dps 40
    $PY hunts/weil_propagation/c4_s2/kernel/run_cells.py --dps 60
    $PY -m pytest -q -n 2 hunts/weil_propagation/c4_s2/kernel tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py
