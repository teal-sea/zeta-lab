1. **Built and evaluated: T_S for ζ on all nine mission cells, on the module form (Π_S = orthogonal projection onto Θ·range S_∞, CCM arXiv:2310.18423 Thm 4.6), as T_S = T_∞ (kernel/) + ΔT (this folder). No eigenvalue of T_S is below −0.02 on any cell. The smallest are 1.5e−3 to 3.5e−3, inside ΔT's error band of 3.5e−3 to 8.2e−3 by (c, N) (corrected, see the notice below; was "about 6e−3"; that band is the Gram step; on c = 2.2, N = 8, measured through 200 modes with Modal's runs, §7b's accuracy band stays above Q's lowest eigenvalue 2.57e−4 at every mode count, no band below 6.5e−4 (140 modes, a lower bound there), while T_S's lowest eigenvalue there, 2.298e−3 at 160 modes, clears that cell's complete band 9.6e−4), so positive semidefiniteness holds at that resolution only (measured, float64).** Also built: the exact place-2 analysis, the refusal gate (W_a and the Epstein (1,1,6) tower refused, exact), and P_2 through E_S in closed form on the shared basis.
2. **Main measurement: ΔT cancels the 2-adic atom up to a residual whose large eigenvalues (beyond ±0.1) do not grow with N. ΔT + Wp has 1, 2, 3 ± pairs beyond 0.1 at c = 2.2, 2.5, 2.9, identical at N = 8, 16 and 32 on the delivered truncations (80, 1200), (120, 1600) and (200, 2400) (this said "converged" before checker/'s refinement; which rows are converged, and to what, is in the correction notice), leading values stable to 1e−2 (c = 2.9: +0.48, −0.46, +0.38, −0.32, +0.17, −0.16; the fourth read −0.31 before the rerun of the notice below); the next pairs are near 0.08.** With T_∞ alone the residual is Wp itself, whose multiplicity near ±0.49 grows with N (cutoff/). Grade: measured (ζ̂ hardened, two routes to 9e−14); not a proof of bounded rank. Exact companion: −Wp = log 2 (Gram(θ_S) − 3/2 I) on 2 < c < 4 (hardened against `galerkin.py`, 4.5e−40).
3. **Structural fact: the semilocal time-frequency operator P F_S P is not Hilbert-Schmidt (HS² = K/2 + 1.07079 over Euler levels j ≤ K, against 2.23748 archimedean; ordinary argument plus measured partial sums).** Hence ΔT needs Sonin data across the Mellin band: at N = 32, 200 prolate modes were needed; 130 left spurious residual pairs (rechecked under the Kmax rule of the notice below: stands).
4. **Refuted: theory §7.3 item 2 (exact: time and frequency limiting to Z_2 differ, commute, and meet in 1_{Z_2}), and the literal Π_S of §7.3 has infinite trace on X_S (ordinary argument).** Positive control not exercised: Γ_C data cannot be realized over Q with S = {∞, 2}, since no idele class character of C_S is odd at ∞ and unramified at 2.
5. **ALIGNMENT s5: §7.3 item 2 refuted; product-ball Π_S obstructed; C4 on the module form at S = {∞, 2} unresolved. Line 2 covers only the eigenvalues of ΔT + Wp beyond ±0.1 and cannot see negative eigenvalues of R_S = Q − T_S of size 1e−2, so it is not evidence for bounded rank. checker/ measures those (its RESULTS lines 2 and 3, s7.3a and s7.7): n_−(R_S) below −band is 4, 4 (c = 2.2), 4, 9 (2.5) and 4, 10 (2.9) at N = 8, 16; at c = 2.9 the N = 16 count is 10 at both 120 and 160 modes, its last pair 1.4 to 1.5 times the band, while at 2.2 and 2.5 the N = 16 count falls as modes rise (truncation). At c = 2.9 that measurement runs against bounded rank. At N = 32 the count is undecided on checker/'s route in float64: the 240-mode refinement moves T_S by 3.9e−2, 2.4e−2, 3.2e−2, more than every top-half depth of the 200-mode row, and sets the band; below it the 200 and 240-mode rows count 0, 2, 2 and 0, 5, 4, while the 240-mode row still holds 19 and 23 negatives (2.5, 2.9) at the old band, so the band rose and the negatives did not leave; the 280-mode row at c = 2.9 counts 22 but inverts a Gram matrix of condition 1.1e17, above 1/eps.** (Corrected: this line said line 2 points to a bounded remainder; until checker/'s N = 32 re-grade it quoted 3, 20, 20 at N = 32, counts at the earlier proxy band.) Open: R_S and its inertia (checker/'s), ΔT accurate below Q's smallest eigenvalue (not met on c = 2.2, N = 8 at any mode count from 80 to 200 at S = 4800, §7b, measured with Modal's runs: the nvec response falls only to 3.5e−4 per 20 modes at 180 → 200, and from 160 modes the criterion's probe term binds; the 0.36-per-20-modes prediction is refuted; the next test, (200, 9600) and (220, 9600), is estimated there, not run), and a proof.

## Correction notice (2026-09-23, 23:20 and 23:45, and 2026-09-24, 00:30 after checker/'s refinement; reruns under 8dc8525)

- **Claimed** (88d9dd1, §5b): at 200 modes and N = 32 the Gram probe "itself
  fails (5.5e−1, the top modes' s-side norms are not captured)", so the error
  there was substituted by agreement with N = 16, "at most 7e−3"; and ΔT's
  error band was "about 6e−3" everywhere.
- **Why it was wrong.** The 120-, 130- and 200-mode rows were computed with
  the w-range fixed at [1, 2^10]. The asymptotic 1/w tail of ζ̂_n and b̂_n has
  term ratio about (2n)²/(4π(m+1)W): at W = 2^10 that is 4.4, 5.2 and 12.3 for
  n_max = 119, 129, 199. At 200 modes the truncated tail returned O(1) values
  for the top modes and the probe, which swaps a Gram matrix for the identity,
  amplified them. The 0.55 was that divergence, not uncaptured s-side norms.
- **What replaces it.** `ta_prolate.kmax_for` (Kmax = 12, 12, 13 for 120, 130,
  200 modes) and a guard in `hats_modes` that refuses a smaller Kmax (8dc8525,
  `test_ta_kmax.py`); configurations 2, 3, 4 rerun. The 200-mode probe is
  8.2e−3, 7.6e−3, 8.2e−3 at c = 2.2, 2.5, 2.9, above the 7e−3 substitute, and
  it replaces it. The 200-mode values moved by at most 5.1e−4 (T_S lowest
  three) and 1.0e−3 (ΔT + Wp leading eigenvalues); counts beyond ±0.1 are
  unchanged. The 120- and 130-mode values moved by at most 5e−7 and 4e−5.
- **ΔT's band per (c, N)** (probe on the most converged row, c = 2.2, 2.5,
  2.9): N = 8 (80 modes) 3.8e−3, 3.5e−3, 3.8e−3; N = 16 (120 modes) 5.9e−3,
  5.4e−3, 5.9e−3; N = 32 (200 modes) 8.2e−3, 7.6e−3, 8.2e−3. The probe grows
  with nvec (6.3e−4 at 40 modes to 8.2e−3 at 200): it measures the Gram step
  at a given truncation, not the truncation error in nvec, which the drift of
  T_S's lowest eigenvalue across nvec shows is of order 1e−3 (c = 2.2:
  5.7e−3, 3.5e−3 at 40, 80 modes, N = 8; 3.5e−3, 2.6e−3 at 80, 120, N = 16).
- **Rechecked and standing.** "130 modes left spurious residual pairs" (line 3,
  §5b): the pairs near 0.15 to 0.18 persist at Kmax 12 to 4e−5, so they are the
  Mellin-band truncation §5b names, not the tail. "At N = 32 use at least 200
  modes" (INTERFACE.md): stands for the same reason.
- **§7's accuracy diagnosis.** Claimed (88d9dd1): "the limiting error is the
  Gram matrix of the b_n", to be removed by an exact v-side Gram. Measured on
  c = 2.2, N = 8 (§7b, new): at fixed nvec the s-side Gram error falls about
  eightfold per doubling of S and ΔT converges in S (1.1e−4 in spectral norm
  from S = 2400 to 4800), while adding prolate modes at S = 4800 moves ΔT by
  4.5e−3 (80 → 100) and 1.6e−3 (100 → 120). The limiting error is the mode
  truncation. The Gram probe above does not see it, so on that cell the band
  is at least 4.5e−3 in spectral norm at 80 modes; the other cells' nvec
  response was not measured.
- **Converged rows.** Claimed (88d9dd1, line 2, §5b, INTERFACE.md): (80, 1200)
  converged at N = 8 and 16, (120, 1600) at N = 16, (200, 2400) at N = 32.
  checker/ measured otherwise (its RESULTS line 1, line 3 before 8d66d09, and
  s7.2, spectral norm of the change of T_S): at N = 16, 80 → 120 modes moves
  T_S by 7.8e−2, 4.5e−2, 2.4e−2 at c = 2.2, 2.5, 2.9, so **(80, 1200) is not converged at N = 16**;
  120 → 160 moves it by 1.6e−2, 5.2e−3, 3.7e−3, so **(120, 1600) is converged
  to 1.6e−2 at c = 2.2** (above the 5.9e−3 probe) **and to within the probe at
  2.5 and 2.9**. At N = 8, checker/'s refinement of the (80, 1200) row against
  (160, 1600, 16) is 5.6e−3, 5.5e−3, 5.3e−3, so it is converged to about
  5.6e−3, above its probe (3.5e−3 to 3.8e−3); §7b's 80 → 100 at S = 4800 on
  c = 2.2 (4.5e−3) agrees in size. At N = 32, (200, 2400) has no measured
  refinement (checker/'s 240-mode unit ran past the 10-minute limit): its
  convergence is not measured. (Updated 2026-09-24 after checker/'s s7.7: the
  240-mode unit has since run on Modal and moves T_S by 3.9e−2, 2.4e−2,
  3.2e−2 at c = 2.2, 2.5, 2.9; checker/ reads it as not a clean refinement,
  T_S's lowest eigenvalue there being −7.3e−3 to −8.9e−3.) Line 2's ±0.1
  counts are measured on the delivered rows only (at N = 16 the (80, 1200) and
  (120, 1600) rows give the same counts); they were not recomputed at 160
  modes.
- **Line 5's reading.** Claimed (88d9dd1): line 2 points to a bounded
  remainder. Line 2 measures only eigenvalues of ΔT + Wp beyond ±0.1; the
  negative eigenvalues of R_S of size 1e−2 are checker/'s, and at c = 2.9 they
  grow 4 → 10 from N = 8 to 16 at a setting checker/ calls resolved. Line 5
  now says so.
- **Also corrected**: one headline value (c = 2.9, fourth residual eigenvalue
  −0.3152, stated −0.31, now −0.32), the lowest T_S eigenvalue range (1.6e−3
  became 1.5e−3 after the rerun), and the runtimes of §7 and §9 (146 s for the
  whole run was Kmax-10 cost).

# RESULTS: two_adic/, gap (b), P_2 through E_S and the assembly of T_S

Worker `two_adic/`, 2026-09-23, branch `teal-sea/weil-c4-s2`, time box
21:10 to 00:10, closed at about 22:45 with T_S evaluated. Nothing here is a claim about RH. Positivity on c ∈ [2, 3)
is already known (Zhu arXiv:2608.24827); this folder builds the 2-adic half
of the C4 trace term. Grades follow the `AGENTS.md` ladder. No
kernel-checked statement is made (AXLE not attempted: nothing here reduced
to a lemma small enough to be worth it within the box). Every number below is
pinned by a test in this folder; raw values are in `ta_es_cells.json`,
`ta_ts_cells.json` and `ta_ts_prolate.json`. The rejected cabinet attempt (`req-c4-s2-remainder/a1`)
was read and not reused: its split of Q is superseded by §3's closed form.

## 0. Sources and conventions

- Connes arXiv:math/9811068 §VII: X_S = A_S/O_S^*, eq. (5) (the Hilbert space
  as the completion of S(A_S) under the Γ-periodized norm), (7) (scaling),
  (12)-(13) (cutoffs by the module), Theorem 4 (semilocal trace formula),
  (17) (trace on X_S as a sum over S-units).
- Connes-Consani arXiv:2006.13771: Sonin space S(1,1), Prop 4.5 and eq. (81)
  (S_∞ = 1 − Σ_n(|ξ_n⟩⟨ξ_n| + |ζ_n⟩⟨ζ_n|)), Theorems 4.7 and 6.11.
- Connes arXiv:2602.04022 §7.2-7.4, eq. (22) and its footnote 11 (the
  projections P^S_T, P̂^S_W are defined with the module).
- **Connes-Consani-Moscovici arXiv:2310.18423 §4** (not in the brief; found
  while fixing the objects, cited as [29] in 2602.04022): the unitary
  w_S : L²(X_S)^{K_S} → L²(ℝ_+^*, d^*u) (eq. (42)); E_S = η_S, the class of
  1_{Z_2} ⊗ f (eqs. (44)-(47)); the local Sonin space at p (Def 4.4, Prop
  4.5); θ_S, the class of σ_2 ⊗ f (Prop 4.6, eqs. (57)-(58)); F_S ∘ θ_S =
  θ_S ∘ F (Prop 4.7); and **Thm 4.6: θ_S maps S_λ(ℝ) onto the semilocal
  Sonin space S_λ(X_S), boundedly with bounded inverse.**

S = {∞, 2}, Γ_S = {±2^n}, C_S = (ℝ^* × Q_2^*)/Γ_S, module |x|_S =
|x_∞||x_2|_2, K_S = its kernel ≅ Z_2^*. In the log variable x = log u of
L²(ℝ_+^*, d^*u), scaling is translation, D := translation by log 2 (CCM's
g(λ) ↦ g(λ/2)), and P := time limiting to u ≤ 1 (the module ball; on this
sector it is the archimedean interval cutoff).

## 1. Task 1: the objects, and the recheck of theory §7.3 item 2

At the place 2 alone (`ta_local.py`, exact rational arithmetic on the
Z_2^*-invariant sector, ball basis B_r = 1_{|x|_2 ≤ 2^r}, F(B_r) = 2^r B_{−r}):

| statement | value |
|---|---|
| F unitary, F² = 1, F(1_{Z_2}) = 1_{Z_2}, F(σ_2) = σ_2, F(ε_0) ≠ ε_0 | all true |
| P_2 := multiply by 1_{Z_2}, P̂_2 := F P_2 F: both orthogonal projections | true |
| P_2 = P̂_2 | **false** |
| P_2 P̂_2 = P̂_2 P_2 = rank one projection onto 1_{Z_2} | true |
| P_2 ∨ P̂_2 = 1 (closed ball \|x\|_2 ≤ 1) | true: local Sonin space dim **0** |
| open ball \|x\|_2 < 1 (CCM Def 4.4) | local Sonin space dim **1**, spanned by σ_2 = ε_0 − ε_1/2 |
| ‖σ_2‖², ‖1_{Z_2}‖² | 3/4, 1 |

Pinned by `test_ta_local_and_data.py` for truncations K = 3, 5, 6, 8 (the
span V_K of the balls is invariant under P_2, P̂_2 and F, so the kernels are
not truncation artefacts). **Grade: exact.** Theory §7.3 item 2 ("1_{Z_p} is
its own Fourier transform, so time and frequency limiting to Z_p are the
same projection") is **refuted**: self-duality is a statement about one
vector. What is true is that the two projections commute and meet in that
vector, so the p-adic uncertainty is exact with a one-dimensional joint range.

## 2. The product-ball obstruction (graded result on its own)

Ordinary argument, unreviewed. cutoff/ reached the same conclusions in its
milestone 1 (its RESULTS lines 1 and 4):

1. The product ball B = [−λ, λ] × Z_2 is not Γ_S-invariant (2B ≠ B), so
   multiplication by 1_B is not an operator on L²(X_S), where eq. (22) and
   the prime term live (Connes (17): the trace on X_S is a sum over S-units).
2. Pushed through the periodization J = E_S (Connes (5)), the ranges of the
   product-ball time and frequency limits become the module ranges: every
   f supported in B has J f supported in |x|_S ≤ λ, and every function on
   {|x|_S ≤ λ} is J of its restriction to the shell |x_2|_2 = 1 times
   1_{|x_∞| ≤ λ}. F commutes with J (Connes Lemma 1(b)), so the same holds
   for the frequency side.
3. The summand 1 ⊗ (1 − P_2) is pushed onto all of L²(X_S) (every Γ_S-orbit
   meets the shell |x_2|_2 = 2), so the literal Π_S of theory §7.3 has
   trace +∞ against ϑ(g)ϑ(g)^*. The brief's "start with the 1 ⊗ (1 − P_2)
   piece" therefore has no finite matrix entries to deliver.
4. The finite, positive, E_S-compatible object is the one CCM Thm 4.6
   supplies: the semilocal Sonin space is θ_S(S_λ(ℝ)), i.e. S_∞ tensored
   with the open-ball 2-adic Sonin vector σ_2 and periodized. This is the
   T_S built below (coordinator decision on milestone 1).

## 3. Task 2: P_2 through E_S on the shared basis (closed form)

In the w_S picture θ_S = Θ_α := 1 − α 2^{−1/2} D (Mellin multiplier
1 − α 2^{−1/2−is}, CCM (57)-(58)) and E_S = Σ_{k≥0} (ᾱ 2^{−1/2})^k D^{−k}
(multiplier L_2(1/2 − is), CCM (47)). On a window of length L,
⟨f, D^k f⟩ = 0 once k log 2 ≥ L, so for 2 < c < 4 every Gram form of θ_S or
E_S on window functions is built from one matrix,

    C_{mn} = ⟨U_m, D U_n⟩ = e^{−2πinh/L} (1 − e^{2πi(n−m)h/L}) / (2πi(n−m)),   m ≠ n,
    C_{nn} = e^{−2πinh/L} (L − h)/L,                                           h = log 2,

and:

- Gram(Θ_α) = (1 + |α|²/2) I − 2^{−1/2}(α C + ᾱ C*);
- Gram(E_S) = 2 I + √2 (ᾱ C + α C*) for |α| = 1;
- the CCM prime block of the atom n = 2 is Wp = (log 2/√2)(C + C*);
- hence **−Wp_α = log 2 · (Σ_j Gram(Θ_{α_j}) − Σ_j (1 + |α_j|²/2) I)**, and for
  ζ, **−Wp = log 2 · (Gram(θ_S) − 3/2 I)**.

The 2-adic atom of the Weil form on these windows is the failure of the
Sonin map θ_S to be a multiple of an isometry on window functions. The
orientation for complex α is fixed by matching Θ_α's multiplier; no mission
cell uses complex α.

Checks (`test_ta_es.py`, dps 40; tolerance = measured deviation rounded up):

| check | measured max deviation | test tolerance |
|---|---|---|
| closed form C against direct quadrature (dps 50), 25 entries per cell | 2.1e−42 | 1e−39 |
| Wp from C against `galerkin.py`'s prime block (independent code) | 4.5e−40 | 5e−39 |
| identity −Wp_α = log 2 (Gram − shift), α ∈ {(1), (1,1), (−1), (i)} | 1.2e−41 | 1e−39 |
| Gram(E_S) closed form against its operator series (140 terms), α ∈ {1, −1, i} | 4.6e−41 | 5e−39 |

**Grade: the identity is exact algebra from the closed form; the closed
form is hardened (quadrature and an independent implementation agree to
working precision).**

Mission cells (`ta_es_cells.json`, dps 40, runtime 13 s for all nine):

| c | N | Gram(θ_S) min | Gram(θ_S) max | Wp min | Wp max |
|---|---|---|---|---|---|
| 2.2 | 8 | 0.80547231866512626 | 2.19834594065960534 | −0.48405651982368832 | 0.48140990413810388 |
| 2.2 | 16 | 0.79293162516069561 | 2.20708619002499827 | −0.49011479902870128 | 0.49010245048296641 |
| 2.2 | 32 | 0.79289321910867856 | 2.20710678105946315 | −0.49012907164618542 | 0.49012907152963847 |
| 2.5 | 8 | 0.79290766300001662 | 2.20708688175546311 | −0.49011527849972269 | 0.49011905978708118 |
| 2.5 | 16 | 0.79289321890453224 | 2.20710678106376477 | −0.49012907164916708 | 0.49012907167114192 |
| 2.5 | 32 | 0.79289321881345248 | 2.20710678118654752 | −0.49012907173427360 | 0.49012907173427360 |
| 2.9 | 8 | 0.79289323304064058 | 2.20710673297045489 | −0.49012903831342493 | 0.49012906187273828 |
| 2.9 | 16 | 0.79289321881345310 | 2.20710678118654718 | −0.49012907173427336 | 0.49012907173427316 |
| 2.9 | 32 | 0.79289321881345248 | 2.20710678118654752 | −0.49012907173427360 | 0.49012907173427360 |

The band is [3/2 − 1/√2, 3/2 + 1/√2] = [0.79289321881345248, 2.20710678118654752]:
window and shifted window overlap in less than half when c < 4, so
|Re⟨f, Df⟩| ≤ ‖f‖²/2 (Cauchy-Schwarz; ordinary argument). Every cell lies in
it; at N = 32 the ends are on it to 1e−18 (c = 2.5, 2.9) and 3e−10 (c = 2.2).
Correspondingly Wp's spectrum fills [−log 2/√2, log 2/√2] = ±0.49012907173.
**Grade: measured spectra (mpmath eigsy at dps 40) of hardened matrices.**

## 4. Kill-control 2: the refusal gate (`ta_data.py`)

Local data at 2 enter as Satake parameters or as a tower s_k(2) =
Λ(2^k)/log 2 with degree d. The gate checks |s_k| ≤ d, recovers the α_j
by Newton's identities, checks |α_j| = 1, and requires the α_j to reproduce
every given s_k. Exact arithmetic (sympy); float inputs need an explicit
tolerance, which is recorded.

| data at 2 | outcome |
|---|---|
| ζ, α = (1) | accepted |
| Dedekind ζ_{Q(√−23)}, α = (1, 1); also its tower s_k = 2 (k ≤ 7, numerics `us_check.json`) | accepted, α = (1, 1) |
| W_a, a = 1/4: α = 2^{±1/4} | **refused** (\|α\| ≠ 1); its tower refused at k = 1 (s_1 = 2^{1/4} + 2^{−1/4} = 2.030103 > 2; theory §7.1 prints 2.0303, a slip in the fourth digit that changes nothing) |
| Epstein (1,1,6) tower (0, 2, 6, 2, 0, 2, 0) | **refused** at k = 3 (\|s_3\| = 6 > 2, n = 8) |
| Epstein's s_1, s_2 alone | accepted as α = (1, −1): the window c < 4 sees only s_1, so detecting Epstein needs the tower beyond the window, as the mission says |
| synthetic tower (0, 2, 1), d = 2 | refused: not a power-sum tower |

`T_S_matrix` runs the gate before anything else, so no code path returns a
trace term for W_a or Epstein data (`test_ta_ts.py`). **Grade: exact.**
Why the gate is a correctness condition and not a guard: T_S uses the local
data only through Θ_α, and the trace term is a diagonal (nonnegative)
quantity only when α enters as a unitary twist of the scaling action; for
W_a the form is a pairing of two different vectors (theory §4, C2).

## 5. Task 3: the assembly of T_S

Definition (module/quotient form, coordinator decision): on
L²(X_S)^{K_S} = L²(ℝ_+^*, d^*u),

    T_S(g) = Tr(ϑ(g) Π_S ϑ(g)^*),   Π_S = orthogonal projection onto Θ(range S_∞),
    Θ = Π_j (1 − α_j 2^{−1/2} D) per Satake parameter (degree d: sum over j).

Derivations (ordinary arguments, unreviewed):

1. **Finite and nonnegative.** ϑ(g)Π_S = Θ·ϑ(g)S_∞·G^{−1}S_∞Θ^* with
   G = S_∞Θ^*ΘS_∞ invertible on range S_∞ (Θ is bounded with bounded
   inverse since ‖2^{−1/2}D‖ < 1). So T_S(g) is finite whenever
   T_∞(g) = ‖ϑ(g)S_∞‖²_HS is, and T_S ≥ 0 by construction.
2. **Composition with kernel/'s data.** Θ^* maps range P onto itself
   (D^{−1} moves support towards u = 0), and 1 − S_∞ = P + Q_∞ with Q_∞ the
   projection onto span{ζ_n} (CC (81)). Hence

       1 − Π_S = P + Q_S,   Q_S = projection onto span{(1 − P) Θ^{*−1} ζ_n},
       Θ^{*−1} = Σ_{k≥0} (ᾱ 2^{−1/2})^k D^{−k},
       T_S = T_∞ + ΔT,   ΔT(g) = Tr(ϑ(g)(Q_∞ − Q_S)ϑ(g)^*).

   ΔT is the whole 2-adic part of T_S; it needs P, F and Θ only, plus the
   ζ_n from kernel/.
3. **Only |Θ| matters.** Θ = W|Θ| with W unitary and both commuting with
   ϑ(g); trace is invariant under unitary conjugation, so T_{ΘV} = T_{|Θ|V}.
   T_S depends on α only through |1 − α 2^{−1/2−is}| on the critical line.
   (For complex unitary α the twisted semilocal Fourier transform was not
   rechecked here; every mission data set has real α.)
4. **Place 2 off.** α = 0 (or `local_data=None`) gives Θ = 1, Q_S = Q_∞,
   ΔT = 0, T_S = T_∞.
5. **The oblique projection carries no 2-adic content.** ΘS_∞Θ^{−1} has
   range Θ(range S_∞) and Tr(ϑ(f)ΘS_∞Θ^{−1}) = Tr(ϑ(f)S_∞): the 2-adic part
   of T_S is entirely the difference between the orthogonal and the oblique
   projection onto the same space (cutoff/ line 4 says the same).
6. **Γ_C is a framework limit.** A component of L²(X_S) with archimedean
   parity ε is an idele class character χ_∞ ⊗ χ_2 trivial on Γ_S; at −1 this
   forces (−1)^ε χ_2(−1) = 1, so an odd component is ramified at 2 and has no
   Satake parameter. L(s, χ_{−23}) (odd, unramified at 2) needs 23 ∈ S, or
   the construction over K = Q(√−23). The Dedekind positive control is
   therefore **not exercised** here (`FrameworkLimit`, message in
   `ta_ts_cells.json`).

Implementation (`ta_ts.py`): `delta_T_matrix` builds Q_∞ and Q_S from a
finite mode family on a uniform log grid with spacing log 2/m (D is an
exact grid shift) and returns ΔT with its two PSD pieces. It was exercised
on **synthetic** smooth modes only; no synthetic number is a value of T_S.
Checks (`test_ta_ts.py`, float64): α = 0 gives ΔT = 0 exactly (measured
0.0); both pieces Hermitian PSD for α ∈ {1, i, −1}; the direct trace route
agrees with an independent FFT route to 5.9e−16 relative. **The grid form
does not suit real ζ_n**: ζ_n(v) oscillates like sin(2πv)/v, which a log
grid cannot resolve beyond u of a few tens; the evaluation has to be done in
the Mellin variable, which is what §5b does.

`T_S_matrix` on the mission cells (`ta_ts_cells.json`): ζ and place 2 off
→ `matrix` (§5b); Dedekind with Γ_C → `framework_limit`; W_a and the
Epstein tower → `refused_nonunitary`.

## 5b. T_S for ζ on the mission cells (`ta_prolate.py`, `ta_run_prolate.py`)

kernel/ was routed at 22:10 (its INTERFACE.md s3, commit af756a5; read-only
import of `kernel/sonin.py`). ΔT is computed in the Mellin variable
(`ta_mellin.py` has the formulas): for each prolate mode, ζ̂_n(s) and
b̂_n(s) = Σ_k (2^{−1/2+is})^k T_n(2^k; s), T_n(W; s) = ∫_W^∞ ζ_n(w) w^{−1/2−is} dw,
from Gauss panels on [1, 2^Kmax], Kmax = `kmax_for(nvec)` = 10, 10, 12, 12, 13 for the five configurations below (η_n in float64 through scipy's spherical
Bessel functions, agreeing with kernel/'s mpmath η_n to 7e−15) plus the
asymptotic tail from φ̃_n's derivatives at 1. Densities ρ = ŵ^T G^{−1} conj ŵ
with Gram matrices taken on the same s-quadrature plus the order-1/S tails
(jump at u = 1 and the sin(2πv)/v oscillation). T_S = T_∞ (kernel/'s
moments, dps 40) + ΔT.

Checks: ζ̂_n against kernel/'s closed-form Tate route (`zeta_mellin_all`),
max 8.8e−14 (hardened: two routes); on a synthetic ξ = (1 − y²)², ζ̂ against
Tate to 1.4e−17, ‖ζ‖² against Plancherel to 6.7e−7, and both pieces of ΔT
against a direct v-domain quadrature to 2.7e−8 and 2.2e−7 (run once, about
150 s, not in the suite). The error of ΔT is set by the Gram matrices: the
probe replacing Q_∞'s Gram by the exact identity moves ΔT by 3.5e−3 to
5.9e−3 up to 130 modes and by 7.6e−3 to 8.2e−3 at 200 modes. (Corrected: 88d9dd1
said the probe fails at 200 modes, 5.5e−1; that was the divergent Kmax-10
tail, see the correction notice.)

| nvec | S | N | c | T_∞ min eig | T_S lowest three | Gram probe | ΔT + Wp, largest in modulus | beyond ±0.1 |
|---|---|---|---|---|---|---|---|---|
| 40 | 800 | 8 | 2.2 | 1.23e−03 | 0.0057, 0.0290, 0.2054 | 6.3e−04 | +0.321, −0.258, −0.089, +0.077, +0.035, +0.031 | 1+1 |
| 40 | 800 | 8 | 2.5 | 4.92e−04 | 0.0050, 0.0130, 0.0825 | 7.3e−04 | +0.442, −0.387, +0.206, −0.184, +0.088, −0.060 | 2+2 |
| 40 | 800 | 8 | 2.9 | 1.92e−04 | 0.0047, 0.0074, 0.0310 | 7.5e−04 | +0.488, −0.453, +0.363, −0.305, +0.174, −0.137 | 3+3 |
| 80 | 1200 | 8 | 2.2 | 1.23e−03 | 0.0035, 0.0265, 0.2002 | 3.8e−03 | +0.318, −0.259, +0.074, −0.072, +0.025, +0.022 | 1+1 |
| 80 | 1200 | 8 | 2.5 | 4.92e−04 | 0.0028, 0.0107, 0.0793 | 3.5e−03 | +0.439, −0.390, +0.204, −0.191, +0.077, −0.064 | 2+2 |
| 80 | 1200 | 8 | 2.9 | 1.92e−04 | 0.0025, 0.0052, 0.0284 | 3.8e−03 | +0.485, −0.456, +0.360, −0.312, +0.171, −0.144 | 3+3 |
| 80 | 1200 | 16 | 2.2 | 1.21e−03 | 0.0035, 0.0254, 0.1982 | 3.8e−03 | +0.318, −0.274, −0.087, +0.086, −0.060, −0.058 | 1+1 |
| 80 | 1200 | 16 | 2.5 | 4.78e−04 | 0.0028, 0.0104, 0.0778 | 3.5e−03 | +0.439, −0.397, +0.217, −0.191, +0.078, −0.074 | 2+2 |
| 80 | 1200 | 16 | 2.9 | 1.85e−04 | 0.0025, 0.0051, 0.0276 | 3.8e−03 | +0.485, −0.458, +0.372, −0.312, +0.171, −0.152 | 3+3 |
| 120 | 1600 | 16 | 2.2 | 1.21e−03 | 0.0026, 0.0244, 0.1962 | 5.9e−03 | +0.317, −0.273, +0.086, −0.075, +0.029, +0.026 | 1+1 |
| 120 | 1600 | 16 | 2.5 | 4.78e−04 | 0.0019, 0.0094, 0.0765 | 5.4e−03 | +0.438, −0.398, +0.216, −0.194, +0.075, −0.073 | 2+2 |
| 120 | 1600 | 16 | 2.9 | 1.85e−04 | 0.0017, 0.0042, 0.0266 | 5.9e−03 | +0.484, −0.460, +0.371, −0.314, +0.170, −0.155 | 3+3 |
| 130 | 1800 | 32 | 2.2 | 1.20e−03 | 0.0025, 0.0236, 0.1954 | 5.5e−03 | +0.317, −0.282, −0.179, −0.177, +0.150, +0.140 | 3+3 |
| 130 | 1800 | 32 | 2.5 | 4.74e−04 | 0.0018, 0.0091, 0.0759 | 5.1e−03 | +0.438, −0.402, +0.223, −0.194, −0.152, −0.152 | 4+6 |
| 130 | 1800 | 32 | 2.9 | 1.83e−04 | 0.0016, 0.0040, 0.0263 | 5.5e−03 | +0.484, −0.461, +0.376, −0.315, +0.170, −0.159 | 3+3 |
| 200 | 2400 | 32 | 2.2 | 1.20e−03 | 0.0024, 0.0236, 0.1950 | 8.2e−03 | +0.316, −0.280, +0.090, −0.076, +0.028, −0.026 | 1+1 |
| 200 | 2400 | 32 | 2.5 | 4.74e−04 | 0.0018, 0.0091, 0.0759 | 7.6e−03 | +0.438, −0.402, +0.222, −0.194, −0.076, +0.075 | 2+2 |
| 200 | 2400 | 32 | 2.9 | 1.83e−04 | 0.0015, 0.0040, 0.0263 | 8.2e−03 | +0.484, −0.461, +0.376, −0.315, +0.169, −0.160 | 3+3 |

Readings (all measured):

- **T_S has no eigenvalue below −0.02 on any row**, and its lowest
  eigenvalue (1.5e−3 to 3.5e−3 on the delivered rows) sits inside the error
  band. Its inertia is therefore 0 negative at the resolution −0.02 and not
  resolved below the row's band (3.5e−3 to 8.2e−3). T_∞'s own lowest eigenvalue (1.8e−4 to 1.2e−3)
  is below that band, so the comparison T_S against T_∞ at the bottom of the
  spectrum is not resolved either.
- **The residual ΔT + Wp is N-independent at the top.** Its eigenvalues come
  in ± pairs whose sizes decay (c = 2.9: 0.47, 0.34, 0.16, 0.08); on the
  delivered rows (see the notice for which are converged) the count beyond ±0.1 is 1, 2, 3 pairs at c = 2.2, 2.5, 2.9
  for N = 8, 16, 32 alike, and the leading values agree across N = 16 and 32
  to 7.4e−3. The count grows with c. The threshold 0.1 falls in a gap at every
  cell but the next pairs (about 0.075 to 0.09) are also stable, so the
  statement is about a decaying profile, not a sharp rank.
- **Truncation matters.** At N = 32 with 130 modes (s up to about 260, the
  window band edge at c = 2.2 is about 255) spurious pairs near 0.15 to 0.18
  appear and vanish at 200 modes: §6 in practice (rechecked at Kmax 12: unchanged to 4e−5).
- **Precision response.** kernel/ reports T_∞ at dps 40 and 60 agreeing to
  5.1e−39; ΔT is float64 with the truncation errors above, so the dps 40
  against 60 response of T_S is below its resolution and was not measured
  separately.
- **What this says about C4 here.** Q = Q_∞ − Wp and T_S = T_∞ + ΔT, so
  R_S = R_∞ − (ΔT + Wp). With T_∞ alone the prime atom leaves Wp in R_S with
  growing multiplicity (cutoff/ line 2); with T_S the part of the residual
  above 0.1 has an N-independent size. Whether R_S has bounded negative index
  depends on how this residual meets R_∞'s spectrum, which is checker/'s
  measurement: n_−(R_S) below −band grows 4 → 10 from N = 8 to 16 at c = 2.9
  and holds at 10 under 120 → 160 modes (checker/ RESULTS line 2, s7.3a).

## 6. The semilocal time-frequency operator is not Hilbert-Schmidt (`ta_hs.py`)

For real α (all mission data; F Θ = Θ^* F uses FD = D^{−1}F and a real),
F_S = Θ F Θ^{−1} = U_2 F, U_2 = −aD + (1 − a²) Σ_{j≥0} a^j D^{−j},
a = α/√2 (CCM Prop 4.7 (i)), P F_S P = Σ_{j≥−1} c_j A_j with A_j := P D^{−j} F P,
whose kernel is K(2^j u v), K(t) = 2 t^{1/2} cos 2πt. Exactly,

    ⟨A_j, A_l⟩_HS = 2 · 2^{(j+l)/2} [S(2π|2^j − 2^l|) + S(2π(2^j + 2^l))],   S(w) = Si(w)/w, S(0) = 1,

so the diagonal terms c_j²⟨A_j, A_j⟩ tend to 1/2 each. Measured at dps 30
(`test_ta_hs.py`):

| K (Euler levels j ≤ K) | 0 | 8 | 16 | 24 | 32 | 40 |
|---|---|---|---|---|---|---|
| ‖P F_S^{(K)} P‖²_HS | 0.405037 | 5.052145 | 9.070653 | 13.070786 | 17.070787 | 21.070787 |

The partial sums lie on K/2 + 1.0707867954 (within 2e−5, 1e−7, 4e−9 at
K = 24, 32, 40); the archimedean value (α = 0, place 2 off) is
Tr(P P̂ P) = 2 + 2 Si(4π)/(4π) = 2.23748483494183. The kernel of P F_S P is
the lacunary series Σ_j c_j K(2^j uv), whose coefficients c_j 2^{j/2} = 1/2
are not square summable, so P F_S P is bounded but not Hilbert-Schmidt and
P P̂^S P is not trace class. **Grade: closed form, ordinary argument
(unreviewed), partial sums measured.** Consequence for the mission: the
semilocal Sonin problem has no super-exponential eigenvalue decay; the 2-adic
dilation copies of the prolate problem at scales 2^j each contribute. Any
truncation of the data feeding ΔT must be by Mellin band. T_S itself stays
finite (§5, item 1).

## 7. What is open, and the next step

- **ΔT below the error band.** 88d9dd1 said here: "The limiting error is the
  Gram matrix of the b_n." Corrected by §7b: at S = 4800 the Gram step is below
  1.1e−4 and the mode truncation is the limiting error; the exact Gram route
  below was not built and is kept as a reference. An exact route exists (derivation, not implemented): with |α| = 1,
  ‖(1 − P)Θ^{*−1}ζ‖² = ⟨ζ, |Θ|^{−2}ζ⟩ − ‖b 1_{[1,2)}‖², because the pieces of
  PΘ^{*−1}ζ on the dyadic shells [2^{−l}, 2^{1−l}) are rescaled copies of
  b on [1, 2) with weights 2^{−l}; ⟨ζ_i, |Θ|^{−2}ζ_j⟩ = 2 Σ_k 2^{−|k|/2}⟨ζ_i, D^k ζ_j⟩
  needs only dilation correlations of the modes. 88d9dd1 continued: "That
  would bring ΔT to the level of T_∞'s smallest eigenvalue (1.8e−4) and
  resolve T_S's inertia"; §7b shows it would not, since the mode truncation
  (still 3.5e−4 per 20 modes at 180 → 200 modes) stays.
- **R_S on the cells**: checker/'s (R_S = R_∞ − (ΔT + Wp) in this folder's
  terms). The numbers of §5b are the input.
- **Why the top of ΔT + Wp is N-independent** (a candidate: the residual is
  compact with a c-dependent profile, which is what "bounded rank" in C4
  would need): not proved.
- **Positive control** needs S ∋ 23 or the construction over Q(√−23).
- **Cost** (measured on this laptop at the Kmax rule; corrected, 88d9dd1 said
  64 s and 146 s, which was Kmax-10 cost): 200 modes, S = 2400, Kmax 13, all
  three cells at N = 32 in 178 s (ζ_n on the 139,716 w-nodes alone 48 s; 2.5 GB
  peak); 130 modes 52 s; 120 modes 193 s on a loaded machine; the whole
  `ta_run_prolate.py` about 8 minutes. N = 64 would need about 400 modes
  (Kmax 15, about 490,000 w-nodes, S about 4800): extrapolated from the
  measured unit, not measured, about 30 minutes and several GB, a CI job
  rather than a local run.

## 7b. The accuracy item on c = 2.2, N = 8 (`ta_gram_probe.py`, `ta_gram_probe.json`)

Target: Q's lowest eigenvalue on this cell, 2.5738e−4 (checker/'s
`checker_q_cells.json`, dps 40; the 2.33e−4 quoted for c = 2.2 is the N = 32
value). The criterion was fixed in the script's docstring before the S = 4800
runs were read. It is a spectral norm, so that Weyl's inequality turns it into
an eigenvalue error:

    band(80, 4800) = max( ‖ΔT(80, 4800) − ΔT(80, 2400)‖₂,  ‖ΔT(100, 4800) − ΔT(80, 4800)‖₂,  probe₂(80, 4800) ).

At another nvec n the same three terms are taken at n (`band_terms`, as the
follow-up in BRIEF.md names it): the nvec response n → n + 20 at S = 4800,
the S response at n (against 2400 as above, or against 9600 where that is the
run there is), and probe₂(n, 4800). A term with no run to form it is left out,
and the band is then a lower bound.

Runs 80 to 120 are this laptop's. The runs 140 to 200 at S = 4800 and 160 at
S = 9600 are modal/'s units (tree 284eff6, Linux x86_64, Python 3.12;
provenance and cost in `modal/RUNS.md`), merged unchanged by
`ta_gram_probe.py --merge-modal`, each run carrying its source. Modal's copy of
the (80, 4800) run reproduces the laptop's to 8.2e−15 (ΔT) and 7.6e−15 (the
scalars): the same code on two machines, not a second route.

| nvec | S | Kmax | probe, ‖·‖₂ | max \|G_z^s − I\| | T_S lowest | seconds | where |
|---|---|---|---|---|---|---|---|
| 80 | 1200 | 10 | 3.8e−3 | 8.9e−2 | 3.523e−3 | 15 | laptop |
| 80 | 2400 | 10 | 4.9e−4 | 3.5e−2 | 3.500e−3 | 30 | laptop |
| 80 | 4800 | 10 | 2.5e−5 | 8.4e−3 | 3.486e−3 | 107 | laptop |
| 100 | 4800 | 11 | 1.2e−4 | 1.8e−2 | 3.001e−3 | 107 | laptop |
| 120 | 4800 | 12 | 3.3e−4 | 2.8e−2 | 2.671e−3 | 516 wall, 161 CPU | laptop |
| 140 | 4800 | 12 | 6.1e−4 | 3.7e−2 | 2.480e−3 | 274 (644 CPU) | Modal, SkylakeX |
| 160 | 4800 | 12 | 9.6e−4 | 4.5e−2 | 2.298e−3 | 298 (637 CPU) | Modal, Haswell |
| 180 | 4800 | 13 | 1.4e−3 | 5.2e−2 | 2.156e−3 | 471 (980 CPU) | Modal, Haswell |
| 200 | 4800 | 13 | 1.8e−3 | 5.9e−2 | 2.074e−3 | 623 (1254 CPU) | Modal, SkylakeX |
| 160 | 9600 | 12 | 1.2e−4 | 1.8e−2 | 2.299e−3 | 793 (1858 CPU) | Modal, SkylakeX |

SkylakeX and Haswell are the OpenBLAS kernel families Modal's hosts selected
(AVX-512 present and absent); a Modal row's seconds are `run()`'s wall time.

Responses of ΔT, spectral norm: to S at 80 modes, 6.5e−4 (1200 → 2400) and
1.1e−4 (2400 → 4800); at 160 modes, 1.8e−4 (4800 → 9600). To nvec at
S = 4800, per 20 modes from 80 to 200: **4.5e−3, 1.6e−3, 1.22e−3, 6.5e−4,
5.2e−4, 3.5e−4**, every one above the target.

| n | S term | nvec term, n → n + 20 | probe₂(n, 4800) | band(n, 4800) | binding |
|---|---|---|---|---|---|
| 80 | 1.1e−4 | 4.48e−3 | 2.5e−5 | 4.48e−3 | nvec |
| 100 | no run | 1.60e−3 | 1.2e−4 | ≥ 1.60e−3 | nvec |
| 120 | no run | 1.22e−3 | 3.3e−4 | ≥ 1.22e−3 | nvec |
| 140 | no run | 6.49e−4 | 6.13e−4 | ≥ 6.49e−4 | nvec |
| 160 | 1.82e−4 (against 9600) | 5.21e−4 | 9.59e−4 | 9.59e−4 | probe |
| 180 | no run | 3.46e−4 | 1.36e−3 | ≥ 1.36e−3 | probe |
| 200 | no run | no run (needs 220) | 1.80e−3 | ≥ 1.80e−3 | probe |

**Outcome: not met at any nvec from 80 to 200 at S = 4800.** Every band,
complete or a lower bound, is above 2.57e−4, so the missing terms cannot change
it. The band is complete at 80 (4.48e−3) and 160 (9.59e−4); no band is below
6.49e−4, the lower bound at 140 modes (its S term was not run), 2.5 times the
target. Readings (all measured, float64,
one route):

- **The 0.36-per-20-modes prediction is refuted.** The last paragraph of this
  section, written before the Modal runs, took the ratio of the first two nvec
  responses (0.36) and predicted 5.7e−4 at 120 → 140 and 2.0e−4 at 140 → 160,
  below the target, with a tail near 1e−4 from 160. Measured: 1.22e−3 and
  6.5e−4; the single step 160 → 180 is 5.2e−4, and the step 180 → 200, 3.5e−4,
  is still 1.35 times the target. The ratios per 20 modes are 0.76, 0.53, 0.80,
  0.67. The response keeps falling, but six differences establish no rate, so
  no crossing nvec is predicted here. Slow decay is what §6 allows (P F_S P is
  not Hilbert-Schmidt, so nothing forces fast decay in nvec); that is a
  reading, not a derivation of the rate.
- **Which term binds.** Under the fixed criterion the nvec response binds
  through 140 modes and the probe from 160: at S = 4800 the probe grows with
  nvec and is above the target from 120 modes on (1.80e−3 at 200). The probe
  overstates what S changes in ΔT. For the ζ_n the exact Gram is the identity,
  and max |G_z^s − I| falls 8.9e−2, 3.5e−2, 8.4e−3 as S doubles at 80 modes;
  with both Grams on the same s-grid most of it cancels in ΔT. At 160 modes the
  S response (4800 against 9600) is 1.8e−4, below the target and 5.3 times
  smaller than the probe there, and doubling S cut the probe 7.8-fold. The
  criterion keeps the probe term, and the verdict does not depend on it: every
  nvec response through 200 modes is above the target on its own. What the
  target misses is still the mode truncation.
- **Adding modes lowers ΔT.** Each 20-mode step from 120 → 140 on is negative
  definite (largest eigenvalue −1.9e−4, −1.8e−4, −1.4e−4, −8.2e−5). The steps
  80 → 100 and 100 → 120 are not (+4.6e−5, +3.1e−4), though 80 → 120 is, and
  80 → 200 is, with largest eigenvalue −1.41e−3. T_S's lowest eigenvalue falls
  from 3.486e−3 to 2.074e−3 over 80 to 200 modes (by 4.85e−4, 3.30e−4, 1.91e−4,
  1.82e−4, 1.42e−4, 8.2e−5 per 20 modes) and stays positive; S = 9600 moves it
  by 8.7e−7 at 160 modes. At 160 modes it exceeds the complete band by
  1.34e−3, so on this cell its sign is resolved at that band's resolution
  (Weyl applied to a measured band, which is not a bound); at 80 modes it lay
  inside the band, by 1.0e−3.
- For §5b: on this cell the (80, 1200) row's error is at least 4.5e−3 in
  spectral norm, above its probe (3.8e−3, max entry). The ±0.1 counts and the
  leading residual values (a 1e−2 scale) are not affected, and T_S's lowest
  eigenvalue moved by 1.45e−3 from (80, 1200) to (200, 4800), far from the
  −0.02 of the PSD statement. The nvec response of the other eight cells was
  not measured.
- **Platform.** The differences from 140 modes on mix the two kernel families.
  Their kernel sensitivity was not measured; checker/'s 200-mode unit moves by
  at most 3.3e−7 when only the kernels change (`modal/out/`, Sandybridge
  against the calibration unit), 9.5e−4 of the smallest difference used here.
- **Cost against the estimate.** The estimate below (3 to 10 CPU minutes and
  2 to 5 GB per run, about 40 CPU minutes) was on the laptop's scale. Modal,
  4 vCPU per unit, measured 637 to 1858 CPU seconds and 1281 to 2064 MiB peak
  per run, 5373 CPU seconds in all (89.5 minutes); its 80-mode calibration took
  426 CPU seconds against 107 s of laptop wall, so the two scales differ. Money:
  `modal/RUNS.md` §5.
- **Next test (a proposal; not run, not requested).** band(200, 9600) in the
  docstring's own shape (S against S/2, nvec 200 → 220) needs two runs,
  (200, 9600) and (220, 9600), Kmax 13 both. Scaled from the Modal run times
  (at 160 modes S = 9600 took 2.66 times S = 4800; 180 → 200 modes took 1.32
  times at Kmax 13): about 1660 s and 2190 s, 3850 s in all, 0.34 USD at
  `modal/RUNS.md`'s computed rate. It would say whether raising S with nvec
  brings the probe term below the target while the nvec response, 3.5e−4 at
  180 → 200 on S = 4800, keeps falling. Estimate only.
- **Written before the Modal runs, kept as the record (its prediction is
  graded above).** Measured unit cost, and a CI estimate for meeting the
  target. The exact v-side Gram route of §7 was not built, because at
  S = 4800 the Gram step is already below the target and the route leaves the
  mode truncation untouched. `ProlateModes.zeta` costs 9.6e−5 s per w-node for
  all 80 modes together. One (nvec, S = 4800) run costs 107 s at 80 and 100
  modes, and 161 s CPU at 120 modes (1.9 GB peak). The 120-mode run took 516 s
  of wall time because this laptop was loaded, which puts 140 modes and more
  past the 10-minute local limit, so they were not run. Suppose the nvec
  response keeps its measured ratio (0.36 per 20 modes, from two differences
  only). Then it drops below 2.57e−4 between 140 and 160 modes, with a
  remaining tail near 1e−4 from 160. The runs that test this are nvec = 140,
  160, 180, 200 at S = 4800 (Kmax 12, 12, 13, 13; corrected 2026-09-24, this
  said 12, 12, 12, 13, and `kmax_for(180)` is 13), plus an S = 9600 check at
  160 modes, since the probe grows with nvec (2.5e−5, 1.2e−4, 3.3e−4 at 80,
  100, 120). Scaled from the measured CPU time, which grows roughly as
  nvec × w-nodes × s-nodes (the (200, 2400) row of §5b took 135 s CPU and
  2.5 GB), each run takes 3 to 10 CPU minutes and 2 to 5 GB: about 40 CPU
  minutes in all. That is one GitHub Actions job, free for this public
  repository, and it needs no paid provider. Estimate only; the runs were
  made on Modal instead (operator's approval, BRIEF.md follow-up).

## 8. Grading and ALIGNMENT s5 status

| statement | grade |
|---|---|
| §1 local facts at 2; refutation of theory §7.3 item 2 | exact |
| §2 product-ball obstruction, infinite trace of the literal Π_S | ordinary argument, unreviewed (cutoff/ reached the same) |
| §3 closed form of C, Gram forms, −Wp = log 2 (Gram(θ_S) − 3/2) | exact algebra; closed form hardened (two routes) |
| §3 cell spectra, band ends reached | measured, on hardened matrices |
| §4 refusal outcomes | exact |
| §5 items 1 to 6 | ordinary arguments, unreviewed; item 6 uses only the definition of C_S |
| §5 grid implementation | tested on synthetic modes only |
| §5b ζ̂_n | hardened (two routes, 8.8e−14) |
| §7b S- and nvec-responses of ΔT on c = 2.2, N = 8 through 200 modes (80 to 120 on the laptop, 140 to 200 and (160, 9600) on Modal); target not met at any nvec; the 0.36 prediction refuted | measured (float64, one route; Modal's calibration run reproduces the laptop's to 8.2e−15, same code); the next-run estimate is an extrapolation, not run |
| §5b T_S spectra, residual profile, counts | measured (float64, one route for the Gram matrices; error band 3.5e−3 to 8.2e−3 by (c, N)) |
| §6 closed form for ⟨A_j, A_l⟩_HS and the divergence | ordinary argument, unreviewed; partial sums measured |

Original to this session (novelty not searched): the identity of §3 in
matrix form (first derived here, f1e912d; cutoff/ rechecked it by a third
route, e678d94), the Hilbert-Schmidt divergence of §6, and the Γ_C
framework limit, the Mellin route for ΔT from prolate data and the
measurement of §5b. The objects are Connes', Connes-Consani's and
Connes-Consani-Moscovici's; S_∞ and T_∞ are kernel/'s.

ALIGNMENT s5: theory §7.3 item 2 **refuted** (exact). The product-ball Π_S
**obstructed** (infinite trace; no finite reading carries the place 2 except
the module one). C4 on the module form at S = {∞, 2} **unresolved**: T_S is
built and evaluated, T_S ≥ −0.02 on every cell, and the residual against the
prime atom has an N-independent top beyond ±0.1. That top is not bounded
rank of R_S: checker/ counts n_−(R_S) below −band at 4, 10 (c = 2.9, N = 8,
16), the 4 → 10 step stable under 120 → 160 modes, and at c = 2.9 its
measurement runs against bounded rank (checker/'s grade: measured, weakest step ΔT).
At N = 32 the count is undecided on checker/'s route in float64 (its s7.7:
the band rose past the negatives, and the negatives did not leave).

## 9. Reproduction

    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_local.py
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_run_es.py   # 13 s
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_run_ts.py   # 2 s
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_run_prolate.py   # about 8 min, needs kernel/; arguments 0 to 4 rerun those configurations only
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_gram_probe.py 80 4800   # one (nvec, S) per process: 80 1200, 80 2400, 80 4800, 100 4800, 120 4800; 15 s to about 9 min
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python hunts/weil_propagation/c4_s2/two_adic/ta_gram_probe.py --merge-modal   # merges modal/out/gram_*.json (140 to 200 at 4800, 160 at 9600); reads, computes nothing; the units themselves are modal/run_modal.py's
    PYTHONPATH=$PWD /Users/thomas/zeta-lab/.venv/bin/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/two_adic tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # about 30 to 70 s

## 10. Follow-up 3 (2026-09-24): rho without the explicit inverse

BRIEF.md "Follow-up 3" (32b8112). checker/ s7.7 found cond(G_b) of 3.9e9 to
2.8e18 on the N = 32 rows and T_S failing T_S >= 0 by 14 to 37 at 319 and
364 modes; `ta_mellin.rho` inverted G with `np.linalg.inv`. This section is
written in the order the work was done: s10.1 (diagnosis) and s10.2 (the
acceptance for the fix) were committed before `rho` was changed.

### 10.1 Diagnosis: the cutoff S of the s-side Gram, not the functions

`ta_rho_diag.py`, `ta_rho_diag.json`, `test_ta_rho_diag.py`. Measured,
float64, one route, except where stated.

**Which Gram.** T_S's Gram matrices are not `gram_v`'s. `ta_prolate.delta_T_cells`
takes both on the s side (`gram_s`): G = (1/2π) H* W_s H + (J Jᵀ + dil A Aᵀ)/(πS)
from the hats H on `s_grid(S, 1, 8)`. `gram_v` serves only the synthetic route
`ta_mellin.delta_T_mellin`. The coordinator's trap (i) holds for `gram_s` all
the same: G = F* F with F the weighted sample matrix plus two tail rows, so
cond(G) = cond(F)².

| row (nvec, S) | S/nvec² | s-nodes of G | w-nodes of the hats | gram_v's w-nodes (not on T_S's path) |
|---|---|---|---|---|
| (200, 2400) | 0.060 | 38400 | 139716 | 196596 |
| (240, 2400) | 0.042 | 38400 | 241200 | 196596 |
| (280, 2266) | 0.029 | 36256 | 238752 | 196596 |
| (319, 2633) | 0.026 | 42128 | 245484 | 196596 |
| (364, 3060) | 0.023 | 48960 | 454044 | 196596 |

Every Gram is formed from far more nodes than functions; the node count is
not the problem.

**Not intrinsic.** The exact Gram matrices are well conditioned: G_z = I (the
ζ_n are orthonormal on v >= 1), and cond(G_b) <= ((1 + 2^−1/2)/(1 − 2^−1/2))²
cond(G_z) = 33.97, because b_n = K ζ_n with K the compression of Θ^{*−1} to
x >= 0, whose singular values lie in [0.586, 3.414] (ordinary argument,
unreviewed, in `ta_rho_diag.py`'s docstring; checked on a synthetic family on
`ta_ts`'s grid, where the singular values fall inside that interval). On a
grid that holds the modes, the s-side G_b agrees: cond 13.2 at 80 modes and
S = 2400.

**Produced by the quadrature: the cutoff S, not the resolution inside
[−S, S].** cond(G) = cond(F)² (from the singular values of F; the formed
float64 G reads the same below 1e14):

| nvec | S | S/nvec² | cond(G_z) | cond(G_b) |
|---|---|---|---|---|
| 80 | 150 | 0.023 | 7.8e28 | 1.6e18 |
| 80 | 200 | 0.031 | 4.5e23 | 5.3e14 |
| 80 | 300 | 0.047 | 2.6e15 | 1.1e10 |
| 80 | 600 | 0.094 | 5.6e6 | 2.9e6 |
| 80 | 1200 | 0.19 | 273 | 280 |
| 80 | 2400 | 0.38 | 4.6 | 13.2 |
| 200 | 300 | 0.0075 | 1.1e30 | 1.4e30 |
| 200 | 600 | 0.015 | 2.5e28 | 2.1e28 |
| 200 | 1200 | 0.030 | 7.8e25 | 2.0e16 |
| 200 | 2400 | 0.060 | 7.6e11 | 3.9e9 |

At (80, 300), a finer s-grid (8 to 12 nodes per panel), a finer w-grid for
the hats (12 to 16) and Kmax 10 to 11 each leave cond(G_z) = 2.577e15 and
cond(G_b) = 1.084e10 unchanged to four digits; doubling S takes them to
5.6e6 and 2.9e6. The lowest direction u of G_b at (80, 1200) has its s-energy
rising towards the cutoff (8.4e−4, 5.0e−3, 7.9e−3, 1.1e−2 on |s| in [0, 100),
[100, 500), [500, 1000), [1000, 1200]) and |A·u| = 2e−5: a combination whose
norm lies mostly beyond S, which the order-1/S tail rows do not see. The
controlling ratio is about S/nvec²: the span of nvec prolates holds
combinations concentrated within about 1/nvec² of y = 1, whose transforms
reach s of order nvec² (ordinary argument). The default rule
(`KernelProvider`: nvec = 8N/L + 40, S = 24πN/L) keeps S proportional to
nvec, so the ratio falls as N grows: 0.029, 0.026, 0.023 on the three
default-rule rows.

**What this changes in the record.**

- G_z, whose condition nobody recorded, is the worse of the two: 7.6e11 at
  (200, 2400) against G_b's 3.9e9, so eps × cond(G_z) = 1.7e−4 on the
  delivered N = 32 row.
- A float64 G formed from its samples reads its condition only below about
  1e14; above 1/eps its eigenvalue ratio saturates near 1e16 (1.9e16 formed
  against 7.8e25 at (200, 1200)). checker/'s cond(G_b) of 1.1e17, 2.8e18 and
  5.1e17 for the default-rule rows are therefore lower bounds, not values.
- The samples carry their own error: the float64 hats agree with kernel/'s
  closed form (`zeta_mellin_all`, dps 30) to 5.2e−14 to 2.1e−13 absolute over
  s in [−2400, 600] (relative 1.2e−13 at s = 0, 2.8e−11 at |s| = 2400). Call
  the relative error of F δ. Any solve, however stable, determines the
  discretized projection only while cond(F) δ is well below 1, and cond(F)
  is about 1e13 for Z at S/nvec² = 0.03.

**Decision.** The ill-conditioning is produced by the quadrature (the cutoff S
of the s-side Gram relative to nvec²), not by the functions. The fix has two
parts. (1) The solve: rho from a QR factorization of F, never forming G, so
that the arithmetic error scales with cond(F) and not with cond(F)². (2) The
grid: S must grow like nvec², and each build must report cond(F) for Z and B
so that a row whose projection its samples do not determine can be refused.
Part (2) raises the cost of the N = 32 rows; its numbers are in s10.3.

### 10.2 Acceptance for the fix, fixed before it was run

Written before the new `rho` was run on any case. Grades: measured unless
stated.

- **A1, agreement where the old route is sound.** At the delivered
  truncations (80, 1200), (120, 1600), (200, 2400) (s-grid width 1, 8 nodes
  per panel), for Z and for B: max_s |rho − rho_inv| <= 10 eps cond(G)
  max_s |rho|, with cond(G) = cond(F)² from the singular values of F. The
  measured ratio is reported, and so is the change of ΔT (spectral norm) on
  each delivered (c, N).
- **A2, an end-to-end raised-precision reference at an ill-conditioned
  case.** (80, 300), Z: cond(G_z) = 2.6e15, near 1/eps. Reference: ζ̂ at all
  4800 s-nodes from kernel/'s closed form at dps 30, J and A at dps 30, G and
  the solve at 60 digits, rho on 64 of the s-nodes. Pass:
  max |rho − rho_ref| <= 1e−4 max |rho_ref| on those nodes (prediction from
  δ of order 1e−13 and cond(F_z) = 5.1e7: order 1e−5). Reported beside it:
  rho_inv's deviation (prediction: order 1e−2 or more, since
  eps cond(G_z) = 0.57). **Where it stops:** the same at (80, 200), cond(G_z)
  = 4.5e23, cond(F_z) = 6.7e11; prediction: a deviation of order
  cond(F_z) δ, between 1e−3 and 1. No pass criterion there; it is the
  measured stopping point.
- **A3, the platform drift.** At (200, 2400), N = 32: an entrywise relative
  perturbation of 2^−52 (fixed seed) on Z, B, J and A, and the spectral change
  of ΔT on c = 2.2, 2.5, 2.9, old route against new. Pass: the old route's
  change lies between 1e−8 and 1e−5 (the order of modal/'s 2.3e−7 to 2.9e−7),
  and the new route's is at least 100 times smaller. If the old route's
  change does not reach that order, the drift is not shown to come from the
  inverse. This is a proxy for the cross-platform rebuild, which needs
  modal/.
- **A4, the falsifier's regime, prediction recorded here.** (200, 1200),
  N = 32, is the regime of the 280, 319 and 364-mode rows (S/nvec² = 0.03,
  cond(G_z) = 7.8e25, cond(G_b) = 2.0e16), from hats already computed.
  Prediction: rho_inv's T_S fails T_S >= 0 by order 1 or more; the new rho's
  T_S has no eigenvalue below −1 (the leverages it sums are at most 1) but is
  not clean, with eigenvalues below −band(c, 32) (3.92e−2 / 2.37e−2 /
  3.16e−2) possible, because there the samples do not determine the Z
  projection. If the new route's T_S at (200, 1200) has no eigenvalue below
  −band(c, 32), this prediction is refuted.
