# PREREG: ghost zeros of the DH ground-state transform at the off-line ordinate

Written 2026-10-21 on branch `hunt/weil-ghost-zeros` (from `origin/main`
fb647bfc7), lane "ghost-zeros" of the existing hunt `weil_propagation`. This
is the smallest check that `../theory/RESULTS.md` s4 C3 names. **Committed
before any ground state, transform value or zero count of this lane exists.**
Everything below is fixed from this commit on; anything decided after the
numbers goes in `RESULTS.md` under a heading that says so, never here.
Nothing here is a claim about RH.

Read before writing this file: `../MISSION.md`, `../theory/RESULTS.md` (s0,
s1, s4 C3, s5), `../numerics/RESULTS.md` (s0 to s3, s9),
`../numerics/wp_common.py`, `../numerics/grid_dh_N128.json` (its stored
zero-side split), `../numerics/crossing.json`, `../numerics/epstein_N128.json`,
`../numerics/epstein_offline.json`. **This file is not blind** to the stored
values of the off-line quadruple term Q1 at the grid windows
(`../numerics/RESULTS.md` s3.3); expectation S2 below was derived from them.

## 0. Inputs taken as given (sources, not recomputed here)

- CvS (arXiv:2511.23257, CMP 406, 2026), as the theory worker records it in
  `../theory/RESULTS.md` s1: if the lowest eigenvalue of the truncated Weil
  form on a window is simple and isolated with an even eigenvector v, the
  transform F_v has only real zeros.
- DH's continuum form is negative on every window c >= 30.617188
  (`../numerics/RESULTS.md` s3.2: hardened cell at N = 256 plus the nesting
  argument, ordinary and unreviewed).
- The band N = 128 even-sector crossing c*_128 lies in
  (15691/512, 31383/1024] = (30.646484375, 30.6474609375]
  (`../numerics/crossing.json`, both ends hardened).
- Xi_DH(z) vanishes at z_1 = gamma_1 - i delta_1 with
  gamma_1 = 85.69934848537759..., delta_1 = 0.3085171824566374...
  (`GAMMA_OFF`, `DELTA_OFF` in `../numerics/wp_common.py`, 50 digits; the
  zero is s = 1/2 + i z_1). The second pair z_2 = 114.1633427308 - 0.1508300806 i
  (`GAMMA_OFF2`, `DELTA_OFF2`).
- DH's on-line gap around gamma_1 is (83.10884108474983, 87.64747633255973),
  consecutive entries of `data/dh_zeros_online_T120.json` (float64 scan,
  completeness not checked here).
- zeta: gamma_23 = 84.73549298051705, gamma_24 = 87.42527461312523
  (`mpmath.zetazero`).
- Epstein (1,1,6): off-line zero 0.953260474794661 + 16.2902157203904 i
  (`../numerics/epstein_offline.json`, measured), so z_E = gamma_E - i delta_E
  with gamma_E = 16.2902157203904, delta_E = 0.453260474794661. Its N = 128
  even crossing lies in (29.303711, 29.304199] (`../numerics/epstein_crossing.json`).

## 1. Objects

- **Windows.** C = {29, 30, 61/2, 245/8, 31, 63/2, 47}, exact rationals,
  L = log c. The windows at or before c*_128 are {29, 30, 61/2, 245/8}; the
  windows after it are {31, 63/2, 47}. (245/8 = 30.625 is above the continuum
  bound 30.617188 and below c*_128.)
- **Kinds.** `dh` (the subject); `zeta` (negative control at the same
  height); `epstein` (rival with its own off-line zero, Q = x^2 + xy + 6y^2);
  `dedekind` (negative control sharing Epstein's completion: the Dedekind
  zeta of Q(sqrt(-23))).
- **Matrices.** Band N = 128, even sector, the CCM basis of
  `../numerics/wp_common.py`: `wp_common.build` for `dh` and `zeta`,
  `wp_common.epstein_matrices` for `epstein` and `dedekind`, all ball
  matrices (Arb). Odd-sector matrices from the same assemblies.
- **Ground state.** v = the unit eigenvector of the lowest eigenvalue
  lambda_1 of the even matrix; x = an inverse-iteration vector for it.
- **Transform.** F_v(z) = `wp_common.F_even_acb(v, L, z)`
  = 2 sin(zL/2) [v_0/z + sum_k sqrt2 v_k z/(z^2 - omega_k^2)],
  omega_k = 2 pi k/L. F_v is entire, even, and real on the real line.

## 2. The CvS hypotheses, decided per (kind, c) for the band-N matrix

- **H1 simple.** A ball LDL^T of A - sI, at a shift s with RQ(x) < s, is
  conclusive with exactly one negative pivot. Then lambda_1 < s < lambda_2.
- **H3 isolated.** In band N the spectrum is finite, so isolated is H1 with
  gap at least s - RQ(x). Isolation of the continuum operator is not decided
  here.
- **H2 even** (in CvS's sense: the lowest eigenvector of the whole form,
  both sectors, is even). Holds if the ball LDL^T of A_odd - s_e I is
  conclusive and positive definite, s_e the upper end of the even lambda_1
  bracket. Fails if A_odd - s_l I has a negative pivot, s_l the lower end of
  that bracket. Otherwise undecided.

## 3. A derivation written before computing (ordinary argument, unreviewed)

The band-N even space V_N is exactly the set of transforms
F(z) = 2 sin(zL/2) p(z^2) / (z q(z^2)) with q(w) = prod_{k=1..N} (w - omega_k^2)
and p any polynomial of degree at most N (the map v -> p is a linear
bijection, fixed by the values of p at 0 and omega_k^2). For a root w_0 of
p, the multiplier (z^2 - conj(w_0)) / (z^2 - w_0) maps V_N (complexified)
to itself, and |F(t)| is unchanged for real t. The form is Q(f) = W(f * f~)
(`../numerics/RESULTS.md` s0, Fact A), which depends on F only through
|F(t)|^2 on the real line; the norm is unchanged by Plancherel. So if the
lowest even-sector eigenvalue is simple, the multiplied function is a second
minimiser unless w_0 is real, and **every zero of F_v is real or purely
imaginary**. This is the CvS multiplier argument carried to V_N, and it needs
only H1, not H2. Its consequence, tested as S1: in every rectangle below
where H1 holds, the argument-principle count equals the number of real
sign changes. A failure would be a defect in the code or in this argument,
and would be reported as such.

## 4. The counter

- **Eigenvector enclosure.** Davis-Kahan from the ball residual
  eps = ||Ax - RQ(x)x|| / ||x|| and the gap g = s - RQ(x) (H1's shift):
  ||v - x/||x|| || <= sqrt(2) eps / g, with the sign of v chosen so that
  <v, x> > 0. Propagated into F by Cauchy-Schwarz,
  |F_v(z) - F_{x/||x||}(z)| <= eta ||a(z)||_2, a_k(z) the basis transforms.
- **Argument principle (Arb).** On each boundary segment of a rectangle
  R = [a, b] x [-h, h], a Taylor model of F at the segment centre (exact
  centre, coefficients in balls) plus a Cauchy remainder from an explicit
  bound on |F| in a disk, plus the eigenvector term. A segment is accepted
  when the model excludes 0 and keeps F inside a sector of half-angle below
  pi/4; otherwise it is bisected. The arg changes come from endpoint values
  of `F_even_acb`; the winding number must be a ball containing exactly one
  integer, n_AP. The vertical sides avoid every omega_k by at least 1/32 and
  avoid real zeros: a side is moved inward in steps of 1/512 until both
  hold and the count closes. The sides used are reported.
- **Real-axis sign changes.** F_v at exact rationals of step 1/512 on the
  nominal interval, each sign from a ball that excludes 0 after the
  eigenvector term; n_SC = number of sign changes. Each bracket is bisected
  to width 2^-40 for the location. If n_AP = n_SC, every zero in R is real,
  simple and inside one bracket.
- **Second precision.** The whole chain (assembly, eigenvector, counts) is
  rerun at a second precision: 640 bits for `dh`, `epstein`, `dedekind`
  (primary 400), and 1300 bits for `zeta` (primary 900; LDL steps at 3200).
- **Independent float route.** mpmath only, sharing no code with the Arb
  route below the assembly formulas: `galerkin.Truncation` matrices (the
  lab's second assembly), mpmath inverse iteration seeded from a float64
  spectrum, the transform in the sinc form
  F_v(z) = L [v_0 sinc(zL/2) + sqrt2 sum_k (-1)^k v_k z sinc((z - omega_k)L/2)/(z + omega_k)],
  sign changes plus a sampled winding number with an integrality guard.
  Working precision: dps 60 (`dh`, `epstein`, `dedekind`), dps 320 (`zeta`).
- **Planted control for the counter.** An element of V_N built from a
  chosen p with known roots in the same rectangles (real roots, a planted
  non-real pair at gamma_1 +- 0.3 i, and a root within 0.02 of some omega_k)
  must be counted exactly by the same code. Done in `test_ghost.py`.

## 5. Windows and rectangles

| kind | rectangle | x-range | half-height h |
|---|---|---|---|
| dh | R_gap | [83.109, 87.647] | 1/2 |
| dh | R_ghost | [gamma_1 - 0.3, gamma_1 + 0.3] | 1/2 |
| dh | R_ctx | [80.5, 90.5] | 1/2 |
| zeta | R_gap | [gamma_23 + 0.01, gamma_24 - 0.01] | 1/2 |
| zeta | R_ghost | [gamma_1 - 0.3, gamma_1 + 0.3] | 1/2 |
| zeta | R_ctx | [80.5, 90.5] | 1/2 |
| epstein | R_gap | the on-line gap of Z_epstein around gamma_E | 3/5 |
| epstein | R_ghost | [gamma_E - 0.3, gamma_E + 0.3] | 3/5 |
| epstein, dedekind | R_ctx | [12, 21] | 3/5 |
| dedekind | R_ghost | [gamma_E - 0.3, gamma_E + 0.3] | 3/5 |

The Epstein gap and the on-line zeros of zeta_K = zeta(s) L(s, chi_-23) in
[12, 21] are located after this commit: Epstein by sign changes of
`zeta.epstein.Z_epstein` (dps 40, step 1/100, then bisection), zeta_K both
from Z_(1,1,6) + 2 Z_(2,1,3) and from mpmath's zeta and Dirichlet L zeros.
An F-zero x is **accounted for** by an on-line zero gamma of its own
function if |x - gamma| <= 0.15. A **ghost** is a real zero of F_v within
0.3 of the off-line ordinate (gamma_1 for `dh` and `zeta`, gamma_E for
`epstein` and `dedekind`) that no on-line zero accounts for.

## 6. Prediction and decision rule

**P (the campaign's prediction, recorded here as given).** "A real ghost
zero within 0.3 of 85.699 appears at or before the even-sector crossing."

- **Confirmed** if for at least one c in {29, 30, 61/2, 245/8} H1 holds and
  the enclosure-carrying sign-change count of F_v on
  [gamma_1 - 0.3, gamma_1 + 0.3] is at least 1 (`dh`, N = 128).
- **Refuted** if for all four of these c, H1 holds and n_AP(R_ghost) = 0.
- **Undecided** otherwise (H1 fails, or a count does not close).
- Reported with it: the first c in C with a ghost, whether it persists at
  31, 63/2 and 47, and its location and distance from gamma_1 at each c.

## 7. Secondary expectations (exploratory, graded as such)

- **S1 (reality, from s3).** n_AP = n_SC in every rectangle where H1 holds.
- **S2 (ghost and Q1, derived from the stored Q1 values).** To first order
  at the real zero x_g nearest gamma_1,
  Q1 = (4/L) Re F_v(z_1)^2 ~ (4/L) F_v'(x_g)^2 [(gamma_1 - x_g)^2 - delta_1^2],
  so sign(Q1) = sign(|gamma_1 - x_g| - delta_1) whenever
  ||gamma_1 - x_g| - delta_1| > 0.05. A negative Q1 means a ghost within
  delta_1 = 0.3085 of gamma_1.
- **S3 (zeta control).** At every c in C: n_AP(R_gap) = 0, no ghost, and in
  R_ctx exactly one real zero of F_v within 0.01 of each zeta zero in
  [80.5, 90.5] and no other zero.
- **S4 (Epstein, the rival with its own off-line zero).** A ghost within 0.3
  of gamma_E at every c in C where the Epstein even lambda_1 < 0 (all c >= 30
  here); at c = 29 reported without expectation.
- **S5 (Dedekind control).** No ghost at any c in C, and every real zero of
  F_v in R_ctx accounted for by an on-line zero of zeta_K.
- **S6 (lesion).** Replace the DH matrix A by A - M_Q1, where
  M_Q1 = (4/L) Re(a(z_1) a(z_1)^T) is the matrix of the off-line quadruple
  term (its value at the stored ground states is the `zero_side` Q1 of
  `../numerics/grid_dh_N128.json`, checked). At every c where the unlesioned
  F_v has a ghost, the lesioned ground state has no real zero within 0.3 of
  gamma_1, or its zero nearest gamma_1 moved by more than 0.1. A sham lesion
  of the same kind at an on-line ordinate (the DH zero 89.43924..., matrix
  (2/L) a(gamma) a(gamma)^T) is run alongside and reported without
  expectation.
- **S7 (precision response).** Identical counts at the second precision,
  zero locations agreeing to 1e-20 (`dh`) and 1e-40 (`zeta`); the float
  route gives the same counts and locations to 1e-8.
- **Exploratory scan.** `dh` at c in {14, 18, 22, 25, 27, 28} (N = 128),
  ghost present or not, to see where it first appears below 29. No
  expectation.

## 8. Not claimed

The ghost is a statement about the band-128 ground state, not about the
continuum minimiser. No convergence in N is claimed. H1 to H3 are decided for
the band-N matrix only. Nothing here bears on RH for zeta; DH, Epstein and
zeta_K enter as rivals and controls.
