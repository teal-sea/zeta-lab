# RESULTS: checker/ (independent verification and kill-controls)

1. **T_S reached the checker, and R_S = Q - T_S is measured on all nine cells, now under two_adic/'s QR rho** (c3dca00; all eleven units rebuilt on Modal, s7.8). The band per row is **5.3e-3 to 1.6e-2** at N = 8 and 16 and **3.0e-2 / 1.4e-2 / 8.2e-3** at N = 32 (c = 2.2 / 2.5 / 2.9; two_adic/'s probe, the checker's refinement and quadrature responses). That is above Q's lowest eigenvalues (1.9e-7 to 2.6e-4) and T_S's own (1.5e-3 to 3.5e-3), so T_S >= 0 is not decided at the band; no eigenvalue of T_S lies below -band on any row. two_adic/'s (80, 1200) is not converged at N = 16: 80 -> 120 modes moves T_S by 7.8e-2 / 4.5e-2 / 2.4e-2 (s7.2). Grade: measured.
2. **The c = 2.9 count is exact on the stored matrices (s7.9): n_-(R_S) below -band is 4, 10, 20 at N = 8, 16, 32** (10 on the 160-mode N = 16 build; 20, 20, 20, 21 on the 240, 280, 319 and 364-mode N = 32 builds). Two exact rational routes agree, and every counted eigenvalue is bracketed strictly below -band, the smallest margin 2.4e-4 (364 modes). Grade: **hardened on the stored matrices** (exact inertia); this hardens the inertia of the stored matrices, not of the exact R_S, whose float64 assembly error (Delta_T) is still graded by the band, so as a statement about R_S of the construction it stays **measured, weakest step Delta_T**; the growth is evidence against bounded rank on this construction, not a refutation, since C4 fixes no bound. **What it is made of:** at 2x band the count is **4, 8, 6** (2 to 8 on the N = 32 builds), at 5x band 2 and at 10x band 1 on every build, so the N = 16 to 32 growth lies entirely between -2 band and -band, while the N = 8 to 16 growth (4 to 8) survives at 2x. On the C4 class V_4 (g-hat = 0 at +i/2, -i/2 and 0) the count is **3, 8, 20** (ball arithmetic, same grade).
3. **T_S removes depth; at N = 32 under the QR rho the growth survives at c = 2.9 and falls at 2.5 and 2.2**, by the reading committed before any rebuilt row was analysed (49db49f, s7.8). lambda_min goes from -0.30 to -0.49 (Q - T_inf) to **-0.026 / -0.039 / -0.097 to -0.12** (c = 2.2 / 2.5 / 2.9). At N = 8, 16, n_-(R_S) below -band is **4, 4** (2.2) and **4, 9** (2.5); as modes go 120 -> 160 at N = 16 it runs 4, 3 and 9, 8: truncation, in part or whole (s7.3a); at 2.9 it is 10 at both. At N = 32 at 2.9 the band is the probe (8.2e-3), no refinement moves T_S by more than 4.95e-3, and none of the 12 top-half negatives (-1.45e-2 to -1.21e-2) is shallower than a response. At 2.5 the refined rows count 6 and 5 against 9, at the band 1.4e-2 that the 319-mode row sets; at the 240-mode row's band (1.1e-2) they would count 14 and 12, so that verdict rests on the band rule. At 2.2 every build counts 0. The falsifier passes on every N = 32 build (T_S lowest +1.1e-3 to +4.4e-3; the old route failed by 14 to 37). Grade: measured, float64, one route.
4. **Kill-controls:** 1 passes; 2 passes; 3 not exercised (Gamma_C framework limit). 4, the lesion, is **refused twice**: NonUnitaryLocalData at the gate, then NotImplementedError in `KernelProvider.delta_T` once the gate is bypassed. Below both guards (a formula never validated off |alpha| = 1), T_S has no eigenvalue below -band, and n_-(R) rises from 4 to 5 / 6 / 6 (s7.4).
5. **Q** (phase 1) is unchanged: it matches the CCM Galerkin matrix entrywise (5.5e-40 at dps 40) and `zeta.weil.weil_functional` spot checks (1e-18 to 4e-14), and Q > 0 on every cell. ALIGNMENT s5 status: **unresolved** for C4 at S = {inf, 2}. At c = 2.9 the evidence runs against bounded rank from N = 8 to 32 (4, 10, 20, exact on the stored matrices and measured as a statement about the construction), stable under 120 -> 160 modes at N = 16 and on four refined builds at N = 32 (20, 20, 20, 21). By min-max (ordinary argument, unreviewed, s7.9), any remainder absorbing R_S there needs rank >= 20 at N = 32 if the assembly error is below |lambda_20| = 1.2e-2 (1.48 band), a proviso that is not established; at 2x band the N = 32 count is 6, below N = 16's 8. At 2.5 and 2.2 the N = 32 count does not exceed N = 16's. Delta_T is measured grade and the band indicates, it does not bound. Product-side C4 is **refuted** on these cells (with cutoff/).

Phases 1 to 3 of 2026-09-23, branch `teal-sea/weil-c4-s2`. Nothing here is
a claim about RH. Grades follow the `AGENTS.md` ladder. Every number above is
pinned by a test in this folder (`test_checker_q.py`, `test_checker_gate.py`,
`test_checker_rs.py`, `test_checker_ts.py`, `test_checker_inertia.py`).

## 1. Q, built independently

`checker_q.py` implements theory `RESULTS.md` s0 (Zhu arXiv:2608.24827 eq.
(2)-(3)) and nothing else; `galerkin.py` is read only as an oracle in tests.

- **Basis kernel (derivation, done here):** for f = sum v_n U_n, the form sees
  w(x) = g(x) + g(-x) = v^* K(x) v, with K_ab = (sin w_a x - sin w_b x)/(pi(b-a))
  and K_aa = 2(1 - x/L) cos w_a x. The prime block on c in [2, 3) is
  -(log 2/sqrt 2) K(log 2).
- **The x -> 0 limit of A is analytic, not a finite difference.** The
  integrand is rearranged as
  [e^{-2x} D(x) + w(x) e^{-x/2} expm1(-3x/2)] / (-expm1(-2x)), with
  D = w(0) - w(x) in closed form. Nothing cancels near 0. The limits
  1/L - 3/2 (diagonal) and 1/L (off-diagonal) are stated, and a test checks
  them at x = 1e-30.
- **Pole block in closed form.** Structural test: v^* P v = 2 Re(F_+ conj F_-),
  where F_+ and F_- are the integrals of f against e^{+y/2} and e^{-y/2}
  (1.8e-40). P vanishes on the class g-hat(-i/2) = 0 (3e-43).
- **Quadrature:** composite Gauss-Legendre with nodes shared across k. The
  degree-5 against degree-6 difference is at most 1.1e-50. A tanh-sinh route
  agrees to 1e-38 at N = 4.

| check (dps) | measured | pinned at |
|---|---|---|
| CCM `galerkin.py`, entrywise, N = 6 and 32, c in {1.5, 1.9, 2.2, 2.5, 2.9} (40) | <= 5.5e-40 | 4e-39 |
| `weil_functional`, sin^4 bump in span, three cells (30) | <= 9.95e-19 | 1e-17 |
| `weil_functional`, sin^2 bump in span, c = 2.5 (30) | 4.6e-15 (3.7e-14 at 2.2) | 4e-13 |
| `weil_functional`, Fejer b = L/2 (f = L^{-1/2} U_0), three cells (30) | <= 3.5e-16 | 4e-15 |
| `weil_functional`, Fejer b = 0.3, 0.4 (support < L), via the scalar functional (30) | <= 9e-16 | 1e-14 |
| dps 40 against 60, N = 32, entry drift | <= 3.9e-41 | 1e-38 |

## 2. Q on the cells (eigenvalues: mpmath, measured at two precisions)

Three lowest eigenvalues at dps 40. `full` is the whole (2N+1)-dimensional
space. V_- is the class g-hat(-i/2) = 0 of Connes-Consani Thm 6.11. V_-0 is
V_- with v_0 = 0 as well (g-hat(0) = 0).

| c | N | full | V_- | V_-0 |
|---|---|---|---|---|
| 2.2 | 8 | 2.5738e-4, 2.1421e-2, 0.35304 | 2.1155e-2, 0.26137 | 0.26137, 0.79756 |
| 2.2 | 16 | 2.3742e-4, 1.969e-2, 0.34804 | 1.9443e-2, 0.25798 | 0.25798, 0.79367 |
| 2.2 | 32 | 2.3258e-4, 1.8715e-2, 0.34627 | 1.8478e-2, 0.25673 | 0.25673, 0.79146 |
| 2.5 | 8 | 1.3829e-5, 2.1843e-3, 8.0235e-2 | 2.1521e-3, 5.5138e-2 | 5.5138e-2, 0.48896 |
| 2.5 | 16 | 1.1098e-5, 1.9918e-3, 7.7612e-2 | 1.9622e-3, 5.3387e-2 | 5.3387e-2, 0.45639 |
| 2.5 | 32 | 1.046e-5, 1.8576e-3, 7.6817e-2 | 1.8299e-3, 5.2848e-2 | 5.2848e-2, 0.44069 |
| 2.9 | 8 | 2.5499e-7, 3.9469e-5, 4.5617e-3 | 3.8818e-5, 2.9672e-3 | 2.9672e-3, 0.10597 |
| 2.9 | 16 | 2.0821e-7, 3.8923e-5, 3.6482e-3 | 3.8281e-5, 2.3763e-3 | 2.3763e-3, 9.1039e-2 |
| 2.9 | 32 | 1.8681e-7, 3.7391e-5, 3.4452e-3 | 3.6773e-5, 2.2452e-3 | 2.2452e-3, 8.387e-2 |

Full values (25 digits, both precisions, and the calibration cells c = 1.5,
1.9) are in `checker_q_cells.json`. An observation, not pursued: the lowest
eigenvalue on V_-0 equals the second on V_- to all printed digits, on every
cell, because the second eigenvector on V_- has v_0 = 0 (measured: 7.5e-40
at c = 2.9, N = 8; 5.8e-42 at c = 2.2, N = 16).

## 3. The (U-S) gate (kill-control 1)

`checker_gate.py` computes Lambda_F(n) as rational vectors in the log-prime
basis, for n <= 200. Two exact routes agree: the recursion, and the formal
logarithm. Coefficients: zeta a_n = 1; Dedekind a_n = sum_{d|n} chi_{-23}(d),
which agrees with the sum over the three reduced forms divided by 2;
Epstein a_n = r_{1,1,6}(n)/2, from its own representation counter, which
matches `zeta.epstein` for n <= 200. W_a's tower p^{ka} + p^{-ka} is decided
exactly: it exceeds 2 iff ka != 0.

| object | first composite atom | tower violations | window gate on [2, 3) | place gate S = {inf, 2} |
|---|---|---|---|---|
| zeta | none | none | accept | accept |
| Dedekind Q(sqrt -23) | none | none (s_k(2) = s_k(3) = 2, s_k(5) = 0, 2, 0) | accept | accept |
| Epstein (1,1,6) | n = 6 (31 in all) | n = 8 (s_3(2) = 6), n = 27 (s_3(3) = 6) | accept (atom 2 has Lambda = 0) | **reject** |
| W_a, a = 1/4 | none | every prime power; first n = 2 (s_1(2) = 2.0301) | **reject** | **reject** |

Compared after the gate passed, as the brief orders: it agrees entry for entry
with numerics `us_check.json` (branch `teal-sea/weil-propagation`) on the
composite atoms, the tower violations and the small-p towers. The test
re-reads that file with `git show` and skips if the branch is absent.

## 4. Properties the T_S tests assert (written before reading kernel/, two_adic/)

The derivations and their grades are in `checker_props.py`. In brief:

- P1: T_S is Hermitian (elementary).
- P2: T_S is PSD, because Pi_S is an orthogonal projection and
  Tr(A Pi A^*) = ||Pi A^*||^2 (elementary).
- P3: the N = 8 matrix is the central block of the N = 16 matrix
  (elementary).
- P4: n_-(R_S) is nondecreasing in N (interlacing).
- P5: n_-(R_S) is the same at N = 8, 16, 32. This is C4's bounded-rank
  prediction, not a theorem.
- P6: switching place 2 off gives T_inf (definitional).
- P7: Connes-Consani Thm 6.11 at c = 1.5 and 1.9, with
  kappa = 4 gamma/log 2 and gamma = 2.94355 (a published theorem; its
  transcription to this basis is a derivation, unreviewed).
- P8: Q > 0 (consequence of Zhu Thm 1.2).
- Kill-control 2: the builder must refuse the data of W_a and Epstein.
- Kill-control 3: Dedekind runs only if the builder accepts it. Otherwise
  "positive control not exercised".

The tolerance policy was fixed before any provider number existed (test file
header): 10x the dps 40/60 response. A precision response above 1e-20
relative fails.

**A discrepancy in the source.** Connes-Consani Thm 6.11 (p. 48) imposes
g-hat(-i/2) = 0, while their Theorem 1 (p. 2) says +i/2 and 0. Both
reflected classes are reported (`INTERFACE.md`).

## 5. Phase 2: routed code (tests in `test_checker_rs.py`, WRITTEN AFTER ROUTING)

Routed by the coordinator: kernel/ af756a5 (`sonin.T_inf_matrix`), two_adic/
f1e912d and c7e9f57 (`ta_ts.T_S_matrix`, `ta_data.validate`), cutoff/
22f6e1c. After routing, only `checker_glue.py` changed among the phase 1
files. `test_checker_rs.py` is new and says so in its header; no phase 1
property was edited.

**Definition change.** The mission's product-ball Pi_S is superseded
(cutoff/ and two_adic/: at 2, time- and frequency-limiting to Z_2 differ, and
the product ball is not Gamma_S-invariant). two_adic/ now uses Pi_S = the
orthogonal projection onto Theta(range S_inf) (CCM arXiv:2310.18423 s4). P2's
derivation needs only that Pi_S is an orthogonal projection, so it still
applies. P6 is unchanged.

### 5.1 What ran, and against what

| property / control | owner | status |
|---|---|---|
| P1, P2 for T_inf (c = 1.5, 1.9, 2.2, 2.5, 2.9, N = 8) | kernel/ | **pass**: Hermitian defect 0; lambda_min > 0 |
| P3 for T_inf (N = 8, 16 are central blocks of N = 32) | kernel/ | **pass**: defect < 1e-35 |
| P6 place 2 off = T_inf | two_adic/ | **pass**, exact (drift 0). The builder's `local_data=None` path, with kernel/'s module passed as the provider. |
| P7 Connes-Consani Thm 6.11, c = 1.5, 1.9, N = 8, 16 | kernel/ (with checker Q) | **pass** (table 5.3) |
| P1 to P5 for T_S, R_S = Q - T_S | two_adic/ | phase 2: **not run** (`T_S_matrix` raised KernelUnavailable). Phase 3: run, s7. |
| kill-control 1, (U-S) gate | checker/ | **pass** (s3) |
| kill-control 2, refusal of non-unitary data | two_adic/ | **pass**: W_a refused (\|alpha\| != 1); Epstein refused at \|s_3(2)\| = 6 > 2, using the checker's own tower |
| kill-control 3, Dedekind positive control | two_adic/ | **positive control not exercised**: FrameworkLimit for Gamma_C (s5.4) |
| kill-control 4, lesion (optional) | | phase 2: **not run** (no T_S). Phase 3: run, s7.4. |

Also checked: cutoff/'s Gram(Theta_1) = 3/2 - W_2/log 2. two_adic/'s
`ta_es.theta_gram` equals 3/2 I - sqrt2 H, built from the checker's own
atom block, to 2.3e-41 at dps 40 (c = 2.2, 2.5, 2.9; N = 8, 16). Not
checked: two_adic/'s claims that T_S depends on alpha only through
|1 - alpha 2^{-1/2-is}|, and that P F_S P is not Hilbert-Schmidt. The
first needs T_S; the second needs its operator definitions, which the
checker did not re-derive.

The refusal reads the tower outside the window. On c in [2, 3) the only
atom is n = 2, where Epstein has s_1(2) = 0. two_adic/'s validator accepts
the tower cut at k = 2 (alpha = +-1) and refuses the whole tower at n = 8.
A window-only check could not refuse Epstein here.

### 5.2 kernel/'s T_inf and the product-side remainder R = Q - T_inf

Q is the checker's own. T_inf is kernel/'s, at dps 40. C1 = V_- (g-hat(-i/2) = 0)
and C2 = V_- with v_0 = 0 as well. Inertia uses tol = 10 x the dps 40/60
eigenvalue drift for N <= 16, and 1e-30 x max|R| at N = 32. No eigenvalue
is undecided. H is the shift form of the atom at 2, from the checker's
prime block: H = -prime / (sqrt2 log2).

| c | N | T_inf lowest | R full: n_-, lowest | R on C1: n_-, lowest | R on C2: n_-, lowest | #eig(H) > 1/4 |
|---|---|---|---|---|---|---|
| 1.5 | 8 | 3.8014e-2 | 0, 2.4594e-3 | 0, 3.0019e-3 | 0, 3.0019e-3 | (no atom) |
| 1.5 | 16 | 3.779e-2 | 0, 7.3218e-4 | 0, 7.4875e-4 | 0, 7.4875e-4 | (no atom) |
| 1.5 | 32 | 3.7722e-2 | 0, 1.8629e-4 | 0, 1.8708e-4 | 0, 1.8708e-4 | (no atom) |
| 1.9 | 8 | 4.0004e-3 | 2, -2.8389e-2 | 1, -2.8201e-2 | 0, 7.5225e-3 | (no atom) |
| 1.9 | 16 | 3.941e-3 | 2, -3.6078e-2 | 1, -3.5818e-2 | 0, 1.8764e-3 | (no atom) |
| 1.9 | 32 | 3.9251e-3 | 2, -3.9604e-2 | 1, -3.9307e-2 | 0, 4.6881e-4 | (no atom) |
| 2.2 | 8 | 1.2324e-3 | 5, -0.30383 | 4, -0.27828 | 3, -0.27828 | 2 |
| 2.2 | 16 | 1.2054e-3 | 7, -0.46471 | 6, -0.46465 | 5, -0.46416 | 3 |
| 2.2 | 32 | 1.1984e-3 | 11, -0.48799 | 10, -0.48798 | 9, -0.48798 | 7 |
| 2.5 | 8 | 4.9155e-4 | 7, -0.42746 | 6, -0.42676 | 5, -0.42676 | 4 |
| 2.5 | 16 | 4.7756e-4 | 11, -0.48123 | 10, -0.48123 | 9, -0.48117 | 8 |
| 2.5 | 32 | 4.7401e-4 | 19, -0.48857 | 18, -0.48857 | 17, -0.48857 | 15 |
| 2.9 | 8 | 1.9171e-4 | 9, -0.4377 | 8, -0.43752 | 7, -0.43713 | 5 |
| 2.9 | 16 | 1.8495e-4 | 15, -0.48113 | 14, -0.48113 | 13, -0.48113 | 11 |
| 2.9 | 32 | 1.8323e-4 | 25, -0.48846 | 24, -0.48846 | 23, -0.48846 | 23 |

For c < 2 this is R_inf = P - E exactly (no atom). Its negative index is
stable in N: 0 at c = 1.5; 2, then 1 on C1, then 0 on C2 at c = 1.9. That
is the S = {inf} content of CC's Theorems 1 and 6.11. For c in [2, 3), n_-
grows with N on every space, and lambda_min approaches -sqrt2 log 2 / 2 =
-0.4901. That is cutoff/'s decomposition -sqrt2 log2 H + (compact), seen
through an independent Q and an independent atom block. **Product-side C4
is refuted on these cells** (measured at two precisions, with an ordinary
argument from cutoff/). The semilocal T_S is meant to cancel exactly this,
and it is the object not yet delivered.

### 5.3 Connes-Consani Thm 6.11 in the mission basis (P7)

kappa = 4 gamma / log 2 = 16.99 (gamma = 2.94355, CC Lemma 6.10). kappa_star
is the least kappa with R + kappa L v_0^2 >= 0 on C1. "Reflected C2" is
int f e^{+y/2} = 0 with v_0 = 0 (their Theorem 1 as printed).

| c | N | min on C1 of R + kappa L v_0^2 | min on C2 | min on reflected C2 | kappa_star | largest dps 40/60 drift |
|---|---|---|---|---|---|---|
| 1.5 | 8 | 3.0019e-3 | 3.0019e-3 | 3.0019e-3 | 0.0 | 2.9e-41 |
| 1.5 | 16 | 7.4875e-4 | 7.4875e-4 | 7.4875e-4 | 0.0 | 5.2e-42 |
| 1.9 | 8 | 7.5225e-3 | 7.5225e-3 | 7.5225e-3 | 7.422 | 5.3e-42 |
| 1.9 | 16 | 1.8764e-3 | 1.8764e-3 | 1.8764e-3 | 9.51 | 5.4e-42 |

The two reflected classes give identical minima, so the Thm 6.11 / Theorem 1
sign discrepancy (s4) makes no difference here. kappa_star grows with N at
c = 1.9 and stays below 16.99. CC's Remark 6.12 puts the best constant for
the full window log 2 in (13, 17).

### 5.4 Kill-control 3: the Gamma_C framework limit, checked independently

Over Q with S = {inf, 2}, Gamma_S = {+-2^n} contains -1, embedded
diagonally in R* x Q_2*. A character of C_S is trivial on it, so
chi_inf(-1) chi_2(-1) = 1. A component odd at inf therefore needs
chi_2(-1) = -1. That is impossible for chi_2 unramified at 2, since
-1 is in Z_2^*. chi_{-23} is odd (negative discriminant) and unramified
at 2 (chi(2) = +1, and 2 splits), so L(s, chi_{-23}) has no component on
L^2(X_S). The argument holds (elementary; arithmetic pinned in
`test_gamma_c_framework_limit_arithmetic`). The Dedekind control needs
23 in S, or the construction over K = Q(sqrt -23). **Positive control not
exercised.** The Dedekind data at 2 are unitary (alpha = (1, 1),
s_k(2) = 2), so this refusal is about the archimedean parity, not about
the local data.

### 5.5 kernel/ milestone 2, verified with the checker's Q

`run_checker_kernel_m2.py` produces `checker_kernel_m2.json`.

- **A block.** kernel/'s `arch_matrix` equals the checker's quadrature route
  after rounding to dps 40, at c = 1.5, 2.2 and 2.9 (N = 32).
- **Best constant at c = 2.0** (the full window log 2). kappa_star =
  12.428, 13.878, 14.557 at N = 8, 16, 32. kernel/ reports 12.43, 13.88,
  14.56. It is increasing in N, toward CC's interval (13, 17).
  R_inf = P - E has 2/1/0 negatives on full/C1/C2 at every N.
- **Archimedean-only remainder P - E on the mission cells.** Negatives on
  full/C1/C2 are 2/1/0 at c = 2.2 and 2.5, and 2/2/1 at c = 2.9, the same
  at N = 8, 16 and 32. This agrees with kernel/. The S = {inf} content of
  C4 (bounded negative index) holds on these windows once the atom is
  removed. The growth in s5.2 comes entirely from the atom at 2.

### 5.6 Positive controls: what ran, and what that allows

Forge's ruling (relayed 2026-09-23): S stays {inf, 2}. S is not extended
to 23, and the construction is not moved to K.

- **Ran:** zeta, the only object the construction is built for. Dedekind
  zeta_{Q(sqrt -23)} was accepted by the checker's (U-S) gate (phase 1,
  exact, n <= 200). Its unitary data at 2 (alpha = (1, 1)) pass two_adic/'s
  validator.
- **Not exercised at S = {inf, 2}:** the Dedekind positive control as a
  trace-term build. The reason: no idele class character over Q is odd at
  inf and unramified at 2 (s5.4; ordinary argument, elementary, checked
  independently here, arithmetic pinned by a test).
- **What this costs.** Kill-control 2 shows the builder refuses the rivals.
  Nothing shows that it accepts, and behaves correctly on, a unitary
  degree-2 object other than zeta. So any statement about T_S or R_S at
  S = {inf, 2} is a statement about zeta alone. It cannot be read as
  distinguishing (U-S) objects from non-(U-S) ones beyond the refusal
  itself.

## 6. Reproduction

    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_q.py   # ~3 min
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_rs.py  # ~8 min (shared laptop)
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_kernel_m2.py  # ~3 min
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_ts.py --routed 8dc8525 --units 0,1,3,4,5,6   # ~5 min
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_ts.py --routed 8dc8525 --units 2 --analyse 015895f  # ~4 min + ~3 min
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_lesion.py   # ~1 min
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_ts.py --merge-modal --analyse 015895f  # ~1 min, reads modal/out
    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_inertia.py  # ~2 min, exact inertia at c = 2.9 (s7.9)
    PYTHONPATH=$PWD <venv>/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/checker \
        tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # 2 min

At the phase 3 commits: 168 passed, 10 skipped (9 phase 1 tests that need dps 60 T_S at
N >= 16, 1 positive control), 3 strict xfail (phase 1 P3, s7.2). Once
two_adic/ commits a change to a file T_S imports, the snapshot no longer
matches: tests that serve T_S from it skip with that reason (by design), and
the pins of the JSON files keep holding for the recorded inputs. (From
2026-09-24 such a commit also turns one test red, s7.1.)
After the Modal merge (s7.7), the same command: 202 passed, 10 skipped, 3
xfailed (18 new tests; the skips and xfails are those of s7.1). After
follow-up 3 (s7.9): 270 passed, 10 skipped, 3 xfailed, the same skips and
xfails; `test_checker_inertia.py` carries 34 of the passes.

## 7. Phase 3: T_S and R_S = Q - T_S (tests in `test_checker_ts.py`, WRITTEN AFTER ROUTING)

Routed: two_adic/ 8dc8525 (T_S for zeta, Kmax rule); its probe read from
015895f. T_S = T_inf + Delta_T is float64; Delta_T is of measured grade
(two_adic/ RESULTS s5b). The mission's dps 40 / 60 precision response cannot
bite on it, so the mode-count and quadrature responses replace it (routing).

### 7.1 The snapshot, and why it fails closed

`run_checker_ts.py` builds T_S once per unit into `checker_ts_snapshot.json`
and `checker_glue.T_S` serves it. The earlier snapshot (an orphaned run from
22:37 with bare python3, stopped at 7 of 15 units, keyed to HEAD while
`two_adic/ta_prolate.py` was modified, its 200-mode entry built by a tail
that diverges there) was deleted, and no entry of it was reused.

- **Key (until 2026-09-24, see the re-key below):** a digest of the HEAD blobs of every file T_S imports or reads:
  the non-test `.py` files under two_adic/ and kernel/, and `kernel/*.json`.
  Commits of two_adic/'s RESULTS, INTERFACE or JSON do not move it (015895f
  did not).
- **Refusal:** building or serving refuses while `git status --porcelain`
  shows any of those files changed (modified, staged, deleted, renamed). A
  git error raises; it is never read as clean. Untracked files are not key
  inputs: the routed clause names tracked files, and an untracked module
  matters only if T_S imports it. So after each unit, every module actually
  loaded from two_adic/ or kernel/ must be a clean tracked input, or the
  unit is refused. (Counting untracked `.py` as dirty stopped one run on
  two_adic/'s new `ta_gram_probe.py`, which T_S never imports.)
- **No live fallback:** `T_S()` raises `SnapshotUnavailable` (a `NotRouted`)
  instead of building live, so phase 1's tests skip with the reason.
- **Route:** one `ta_prolate.delta_T_cells` call per (nvec, S, N) serves the
  three cells, composed exactly as `KernelProvider` / `T_S_matrix` compose
  it. One unit equals a live `T_S_matrix` call bitwise (a test).

Estimate, written before launch: 20.8 s for the measured unit (80, 1200, 8),
about 7.5 min in total by a scaling model. Measured: (80, 1200, 8) 20.8 s,
(120, 1600, 16) 73.7 s, (200, 2400, 32) 246.8 s at Kmax 13, (80, 1600, 16)
28.5 s, (120, 1200, 16) 50.4 s, (80, 1200, 16) 20.8 s, (160, 1600, 16)
107.6 s. The (240, 2400, 32) unit at Kmax 14 was predicted at 320 s. It was
stopped at 16 min wall (9.2 min CPU, load average 8 to 9 on the shared
laptop) under the 10-minute rule (s7.6).

**Re-keyed 2026-09-24: the key is T_S's import closure.** The folder rule
above keyed every non-test `.py` under two_adic/ and kernel/, so two_adic/
fd9b0bf, which adds `ta_gram_probe.py` (a file T_S never imports), moved the
digest from 02f12c86 to 323b8a07 and the committed snapshot stopped being
served. At aeacda0 the suite gave 158 passed, 23 skipped, 0 xfailed (21 "no
snapshot unit" skips, the bitwise live-provider test, and the 3 strict xfails
among them), against 168 / 10 / 3 at dab5f74. `checker_glue.ts_closure` now
keys the import closure of `two_adic/ta_ts.py`, found by an AST scan that
includes imports inside functions and follows names into both folders, plus
`kernel/cells_dps40.json` and `cells_dps60.json`. At HEAD that is ta_ts,
ta_data, ta_prolate, ta_mellin and kernel/sonin, pinned by exact equality. A
module entering the closure or a changed blob in it moves the key, a file
outside it does not, and a load the scan cannot name (a non-literal
`__import__`, or `spec_from_file_location` as in ta_es) raises; planted edits
in a temporary copy test all three. The dirty-tree refusal and
`loaded_inputs_outside_key` read the same closure, and an untracked file
shadowing a name the closure imports counts as dirty. The closure digest is
1dcab230 both at 8dc8525, where the snapshot was built, and at c069f15, so
only the snapshot's meta was rewritten: the new key, the folder-rule digest
beside it, both commits; `T_S` and `units` are unchanged.
`checker_ts_cells.json` and `checker_lesion.json` keep the folder-rule
digest they were built under, as records. A later commit that changes a
closure file now turns `test_snapshot_key_is_the_built_commits_and_heads`
red instead of letting the snapshot's tests skip. After: 184 passed, 10
skipped, 3 xfailed (16 new tests; the 10 skips are the phase 1 tests that
phase 3's snapshot does not serve: 9 need dps 60 units at N = 16, which were
never built, and 1 is the Gamma_C positive control).

**Rebuilt 2026-09-24 under the QR rho (s7.8).** two_adic/ c3dca00 changed
`ta_mellin.rho`, a closure file, so the key moved to b2e7787bce7a and that
test turned red as designed. `run_checker_ts.py --rebuild-rho` now builds the
snapshot from `modal/out_rho/` only: all eleven units, each built on Modal by
`build_unit` from the tree e2b46a5 (closure digest b2e7787bce7a there, at
c3dca00 and at HEAD), each checked by `rho_unit` (status, in-container guard,
digest, calibration, unit, S and row shapes; a test plants each fault) and
recorded with its source file, sha256, platform and tree. No laptop row is
kept. The old snapshot (laptop rows plus the first Modal merge, digest
1dcab230) and the old cells JSON are at 3dc0a74 (both last written 8d66d09);
s7.7 below cites them from there. The live-provider check now reads the
laptop half of modal/'s calibration: it equals a live `T_S_matrix` call
bitwise, and the Modal row differs from it by 5.8e-15.

### 7.2 Responses of T_S (spectral norm of the difference, Weyl)

| c | quadrature, N = 16 | 80 -> 120, N = 16 | same, its N = 8 block | 120 -> 160, N = 16 | P3, delivered rows | P3, equal settings | dps 60 drift, N = 8 |
|---|---|---|---|---|---|---|---|
| 2.2 | 1.62e-03 | 7.83e-02 | 5.25e-03 | 1.59e-02 | 5.27e-03 | 4.7e-15 | 0 |
| 2.5 | 1.77e-03 | 4.54e-02 | 5.40e-03 | 5.24e-03 | 5.45e-03 | 4.4e-15 | 0 |
| 2.9 | 1.91e-03 | 2.40e-02 | 4.30e-03 | 3.69e-03 | 3.71e-03 | 6.2e-15 | 0 |

- **80 modes are not converged at N = 16.** two_adic/'s INTERFACE lists
  (80, 1200) as converged there. 80 -> 120 moves T_S by up to 7.8e-2, 90 to
  96 percent of it at |n| >= 12, while the N = 8 block moves 4.3e-3 to
  5.4e-3. The response shrinks with c (larger L), as under-coverage of the
  Mellin band 2 pi N / L predicts. two_adic/'s own default rule
  nvec = 8N/L + 40 asks for 202 / 179 / 160 modes at N = 16 and 364 / 319 /
  280 at N = 32. The delivered rows (120 and 200) sit below it.
- **P3** holds when N = 8 and N = 16 use the same settings: exactly (defect
  0) on the laptop rows of the old route, 4.4e-15 to 6.2e-15 since s7.8,
  where the (80, 1200, 8) unit ran on OpenBLAS's SkylakeX kernels and the
  (80, 1200, 16) unit on its Haswell kernels (the same order as modal/'s
  laptop against Modal calibration, 7.1e-15). Across the delivered rows it fails at phase 1's 1e-30
  tolerance, by the settings change: 3.7e-3 to 5.4e-3 in spectral norm
  (the table), 3.1e-3 to 5.3e-3 as the largest entry. That phase 1 test
  is now a strict xfail with this reason; its assertion is unchanged since
  ebf0eae.
- **dps:** T_S at dps 60 and dps 40 are bitwise equal at N = 8 (only T_inf
  changes, below float64 rounding). The phase 1 precision test passes
  vacuously. Phase 1's P2 at N = 16 and its P4 and P5 need dps 60 matrices
  at N = 16 and 32; those were not built, so the tests skip with the reason.
  Their banded versions are below.

### 7.3 R_S on the cells

band(c, N) = max(two_adic/'s probe for the row, the row's refinement
response, the quadrature response at N = 16). Refinement means the N = 8 row
against the central block of (160, 1600, 16), and the N = 16 row against
(160, 1600). At N = 32 it is the largest ||T_S(X) - T_S(200, 2400)||_2 over
the cell's admitted refined rows X, (240, 2400) and the cell's default-rule
row, by the reading of s7.8 (committed 49db49f before any rebuilt row was
analysed). Since that rebuild every row is on two_adic/'s QR rho, and the
probe is read at c3dca00. History of the N = 32 band: the N = 16 proxy of
535882e, 1.59e-2 / 7.55e-3 / 8.18e-3; the old route's (240, 2400) response
(s7.7), 3.92e-2 / 2.37e-2 / 3.16e-2; now **2.97e-2 / 1.41e-2 / 8.18e-3**. No
N = 8 or N = 16 row changed band by more than 3.5e-8 (s7.8). A refinement
response indicates the truncation error; it does not bound it. What sets the
band: the refinement response on every N = 8 row, at c = 2.2 for N = 16 and
at 2.2 and 2.5 for N = 32 (the 240-mode row at 2.2, the 319-mode row at 2.5);
two_adic/'s Gram probe at 2.5 and 2.9 for N = 16 and at 2.9 for N = 32. No
row is called converged: the mode responses in s7.2, s7.3a and s7.8 do not
support it. Eigenvalues: numpy on float64 R = Q - T_S, with Q rounded from
dps 40. Counts use -band. Eigenvalues with |lambda| <= band are undecided.

| c | N | row (nvec, S) | probe | refinement | band | T_S lowest | Q - T_inf: n_-, lowest |
|---|---|---|---|---|---|---|---|
| 2.2 | 8 | (80, 1200) | 3.75e-03 | 5.58e-03 | 5.58e-03 | 3.52e-03 | 4, -0.3038 |
| 2.2 | 16 | (120, 1600) | 5.85e-03 | 1.59e-02 | 1.59e-02 | 2.62e-03 | 6, -0.4647 |
| 2.2 | 32 | (200, 2400) | 8.16e-03 | 2.97e-02 | 2.97e-02 | 2.45e-03 | 10, -0.488 |
| 2.5 | 8 | (80, 1200) | 3.48e-03 | 5.55e-03 | 5.55e-03 | 2.81e-03 | 6, -0.4275 |
| 2.5 | 16 | (120, 1600) | 5.42e-03 | 5.24e-03 | 5.42e-03 | 1.93e-03 | 10, -0.4812 |
| 2.5 | 32 | (200, 2400) | 7.55e-03 | 1.41e-02 | 1.41e-02 | 1.76e-03 | 18, -0.4886 |
| 2.9 | 8 | (80, 1200) | 3.76e-03 | 5.32e-03 | 5.32e-03 | 2.55e-03 | 7, -0.4377 |
| 2.9 | 16 | (120, 1600) | 5.86e-03 | 3.69e-03 | 5.86e-03 | 1.67e-03 | 12, -0.4811 |
| 2.9 | 32 | (200, 2400) | 8.18e-03 | 4.95e-03 | 8.18e-03 | 1.50e-03 | 23, -0.4885 |

| c | N | full: n_- / undecided / n_+ | full: three lowest | V_-: n_- / undecided | V_-0: n_- / undecided | n_- on \|n\| > N/2 |
|---|---|---|---|---|---|---|
| 2.2 | 8 | 4 / 1 / 12 | -0.02691, -0.01452, -0.008617 | 4 / 0 | 3 / 0 | 2 |
| 2.2 | 16 | 4 / 19 / 10 | -0.02602, -0.01936, -0.01934 | 4 / 18 | 3 / 18 | 2 |
| 2.2 | 32 | 0 / 57 / 8 | -0.02569, -0.0176, -0.0173 | 0 / 56 | 0 / 55 | 0 |
| 2.5 | 8 | 4 / 3 / 10 | -0.04015, -0.02129, -0.01329 | 4 / 2 | 4 / 1 | 2 |
| 2.5 | 16 | 9 / 7 / 17 | -0.03914, -0.02481, -0.01788 | 9 / 6 | 9 / 5 | 4 |
| 2.5 | 32 | 8 / 41 / 16 | -0.039, -0.02579, -0.01829 | 8 / 40 | 8 / 39 | 2 |
| 2.9 | 8 | 4 / 2 / 11 | -0.09654, -0.0456, -0.01307 | 4 / 1 | 4 / 1 | 2 |
| 2.9 | 16 | 10 / 4 / 19 | -0.1127, -0.04522, -0.01806 | 10 / 3 | 9 / 3 | 5 |
| 2.9 | 32 | 20 / 20 / 25 | -0.1203, -0.0451, -0.01726 | 20 / 19 | 20 / 18 | 12 |

Undecided eigenvalues (all of them, per class, are in
`checker_ts_cells.json` under `undecided`):

| c | N | band | undecided on the full space (negative ones, then the range) |
|---|---|---|---|
| 2.2 | 8 | 5.58e-03 | -0.002301 |
| 2.2 | 16 | 1.59e-02 | 9 negative of 19, from -0.01564 to 0.01554 |
| 2.2 | 32 | 2.97e-02 | 29 negative of 57, from -0.02569 to 0.02517 |
| 2.5 | 8 | 5.55e-03 | -0.002722, -0.001354, 0.001348 |
| 2.5 | 16 | 5.42e-03 | 3 negative of 7, from -0.001489 to 0.004895 |
| 2.5 | 32 | 1.41e-02 | 25 negative of 41, from -0.01406 to 0.01225 |
| 2.9 | 8 | 5.32e-03 | -0.002539, -0.001979 |
| 2.9 | 16 | 5.86e-03 | 2 negative of 4, from -0.001655 to 0.004036 |
| 2.9 | 32 | 8.18e-03 | 10 negative of 20, from -0.007705 to 0.008137 |

What this measures:

- **T_S removes the depth of the product-side remainder.** Q - T_inf has
  lambda_min -0.30 to -0.49 and a negative count growing in N (4, 6, 10 /
  6, 10, 18 / 7, 12, 23 at this band). R_S has lambda_min -0.026 / -0.039 /
  -0.097 to -0.12.
- **The count, from N = 8 to 16.** n_-(R_S) goes 4 -> 9 at c = 2.5 and
  4 -> 10 at 2.9, the same on V_- and V_-0 within one; 4, 4 at 2.2.
- **The count at N = 32** (s7.8) is 0 / 8 / 20 on the delivered row, with
  57 / 41 / 20 eigenvalues undecided; 12 of the 20 at 2.9 carry more than
  half their weight on |n| > N/2. At 2.9 the refined rows count 20 (240,
  280 modes) at the same band, so the N = 16 to 32 growth there survives
  the reading of s7.8; at 2.5 they count 6 and 5, and it falls. On the old
  route (s7.7) the counts were 0 / 2 / 2 at a band that the explicit
  inverse had inflated.
- **Where the growth lives.** Negatives with most of their weight on
  |n| <= N/2: 2, 5 at 2.5 and 2.9 (2, 2 at 2.2) at N = 8 and 16; at N = 32,
  0 / 6 / 8.
- **Two deep negatives at c = 2.9** (about -0.1 and -0.045, -0.07 and -0.038
  on V_-0) sit below -3.7e-2 on every class and every N. Against the
  largest band of the cell, now the probe 8.18e-3 at N = 32, the second
  sits 4.6 to 5.6 times below it and the first 8.3 to 14.7 times (on the
  old route, against 3.16e-2: 1.2 to 1.4 times). A bounded count, measured.
- **Banded P4** (one threshold per cell, `band_cell` = the largest band of
  the cell): 0, 0, 0 / 2, 6, 8 / 4, 9, 20, nondecreasing on every cell. At
  the proxy band_cell of 535882e it ran 1, 4, 3 at 2.2, a failure of banded
  P4 asserted before the data. The delivered rows use different settings
  per N and are not nested, so interlacing does not apply to them.
- **T_S >= 0** is not decided at the band: its lowest eigenvalue (1.5e-3 to
  3.5e-3) is inside every band. No eigenvalue of T_S lies below -band.

**Grade of the whole: measured.** Q is measured at two precisions with an
oracle; T_S rests on Delta_T (measured, one route, float64). The band is an
indicator, not a bound. Every row is a Modal build of one route (s7.8); the
refined N = 32 rows at 280, 319 and 364 modes sit beyond the last case
two_adic/ checked against a raised-precision reference (cond(F) 1.9e13 to
2.1e13, against 6.7e11). The weakest step governs.

### 7.3a Growth or truncation: two discriminators from units already built

Routed by the coordinator after the first read of s7.3: a count below -band
that grows with N, mostly on |n| > N/2, is what under-resolved modes would
produce. Two checks, eigenvalues only, from units already built.

**(1) Mode count at fixed N = 16.** One threshold, band(c, 16), for every
build. (80, 1600) isolates the mode count at S = 1600.

| c | build at N = 16 | n_- below -band(c, 16) | of them on \|n\| > 8 | lowest three | last two counted |
|---|---|---|---|---|---|
| 2.2 | (80, 1200) | 5 | 4 | -0.04566, -0.04125, -0.02608 | -0.02238, -0.02006 |
| 2.2 | (120, 1600) | 4 | 2 | -0.02602, -0.01936, -0.01934 | -0.01934, -0.01634 |
| 2.2 | (160, 1600) | 3 | 1 | -0.02651, -0.0168, -0.01621 | -0.0168, -0.01621 |
| 2.2 | (80, 1600) | 5 | 4 | -0.04624, -0.04189, -0.02596 | -0.02237, -0.02014 |
| 2.5 | (80, 1200) | 10 | 6 | -0.04036, -0.03367, -0.03273 | -0.01254, -0.009513 |
| 2.5 | (120, 1600) | 9 | 4 | -0.03914, -0.02481, -0.01788 | -0.01151, -0.005946 |
| 2.5 | (160, 1600) | 8 | 5 | -0.03985, -0.02518, -0.01747 | -0.008922, -0.008375 |
| 2.5 | (80, 1600) | 10 | 6 | -0.04027, -0.03368, -0.03277 | -0.0125, -0.00961 |
| 2.9 | (80, 1200) | 12 | 8 | -0.1143, -0.04659, -0.034 | -0.009739, -0.009137 |
| 2.9 | (120, 1600) | 10 | 5 | -0.1127, -0.04522, -0.01806 | -0.008965, -0.007802 |
| 2.9 | (160, 1600) | 10 | 5 | -0.1133, -0.04592, -0.01834 | -0.008883, -0.008285 |
| 2.9 | (80, 1600) | 12 | 7 | -0.1142, -0.04648, -0.03398 | -0.009552, -0.009024 |

At c = 2.2 the count falls with every step (5, 4, 3): truncation. At 2.5 it
falls from 120 to 160 modes (9 to 8): partly truncation. **At 2.9 it is 10
at both 120 and 160 modes**, with 5 of them on |n| > 8 both times, where
T_S moves only 3.7e-3 between the two (s7.2) and 160 is two_adic/'s own
mode rule for N = 16. So at c = 2.9 the growth from 4 (N = 8) to 10
(N = 16) is measured at a setting this test calls resolved. The last pair
counted sits at -8.9e-3 and -8.3e-3, 1.4 to 1.5 times the band. The N = 8
count is 4 at 2.5 and 2.9 in every build (the N = 8 blocks, s7.3 table).

**(2) R_S compressed to span{U_n : |n| <= N/2}**, at the row's band, next to
the weight-based split of s7.3:

| c | N | span{U_n : \|n\| <= N/2}: dim | n_- / undecided | lowest three | full space: n_- | weight-based: n_- mostly on \|n\| <= N/2 |
|---|---|---|---|---|---|---|
| 2.2 | 8 | 9 | 2 / 1 | -0.02519, -0.01327, -0.002267 | 4 | 2 |
| 2.2 | 16 | 17 | 1 / 6 | -0.02553, -0.01317, -0.005198 | 4 | 2 |
| 2.2 | 32 | 33 | 0 / 25 | -0.02553, -0.01573, -0.01502 | 0 | 0 |
| 2.5 | 8 | 9 | 2 / 1 | -0.03981, -0.014, -0.002505 | 4 | 2 |
| 2.5 | 16 | 17 | 4 / 3 | -0.03905, -0.01978, -0.009967 | 9 | 5 |
| 2.5 | 32 | 33 | 6 / 13 | -0.03898, -0.0241, -0.01631 | 8 | 6 |
| 2.9 | 8 | 9 | 2 / 2 | -0.06871, -0.04266, -0.002535 | 4 | 2 |
| 2.9 | 16 | 17 | 4 / 2 | -0.09499, -0.04441, -0.01088 | 10 | 5 |
| 2.9 | 32 | 33 | 8 / 6 | -0.1123, -0.045, -0.01724 | 20 | 8 |

At c = 2.2 the compressed count is 2, 1, 0. At 2.5 it goes 2, 4, 6 and at
2.9 2, 4, 8 (on the old route, at its N = 32 band: 2, 4, 2), and so does
the weight-based count (2, 5, 6 and 2, 5, 8). The bands differ by row.
**One range, one threshold:** on |n| <= 16 at band(c, 16), the 80, 120 and
160-mode N = 16 builds and the 200-mode N = 32 build give 5, 4, 3, 1 at
c = 2.2; 10, 9, 8, 8 at 2.5; 12, 10, 10, 10 at 2.9. The last pair counted at
2.5 and 2.9 sits at -6.7e-3 to -8.9e-3, 1.2 to 1.6 times the band.

**Reading.** From N = 8 to N = 16 at c = 2.9 the count grows 4 -> 10 and
does not move under 120 -> 160 modes: measured, at a resolved setting by
(1), on a last pair 1.4 to 1.5 times a band that indicates and does not
bound. At 2.5 the same growth is partly truncation; at 2.2 it is
truncation. **(3) N = 32 against more modes** is s7.8 (on the old route,
s7.7): at 2.9 the count of 20 holds on every refined row, and the
growth continues; at 2.5 the 319-mode row's response is larger than most
top-half depths, and the N = 32 count falls to at most the N = 16 count.

### 7.4 Kill-control 4 (lesion, optional, labelled as such)

`run_checker_lesion.py` feeds W_a's data at 2 (a = 1/4, alpha = 2^{+1/4},
2^{-1/4}). N = 8, (80, 1200), Kmax 10, built from committed inputs (HEAD
8dc8525, no dirty input), 60 s.

1. **Builder with the gate:** `T_S_matrix(c, 8, 40, W_A_QUARTER)` raises
   `ta_data.NonUnitaryLocalData`: "Satake parameter alpha_1 = 2**(1/4) has
   |alpha| != 1 (non-unitary)". This is kill-control 2.
2. **Gate bypassed, the routed provider:** `KernelProvider(80, 1200).delta_T`
   raises `builtins.NotImplementedError`: "Delta_T is wired for real unitary
   alpha only (all mission data)", for both alphas. **The construction as
   delivered refuses the lesion at a second, independent layer.** This is
   the kill-control 4 finding.
3. **Below both guards (LESION ONLY):** `ta_prolate.delta_T_cells` called
   with the non-unitary alpha and composed as the builder would. two_adic/
   never validated that formula off |alpha| = 1 (its Gram weight
   1/(1 - |alpha|^2/2) was written for unitary alpha). The numbers say what
   the unguarded formula does. Q_les = 2 Q_inf - s_1(2) Wp. The archimedean
   factor of the real W_a is not modelled. Band 6e-3 is two_adic/'s band at
   alpha = 1; none exists for the lesion.

| c | T_S zeta: lowest | T_S lesion: lowest, n below -band | R zeta: n_- / in band | R lesion: n_- / in band | lesion against 2 Q_zeta: n_- | max \|dT(alpha) - dT(1)\| |
|---|---|---|---|---|---|---|
| 2.2 | 3.52e-03 | 7.66e-03, 0 | 4 / 1 | 5 / 0 | 4 | 1.30e-02 to 1.34e-02 |
| 2.5 | 2.81e-03 | 6.23e-03, 0 | 4 / 3 | 6 / 1 | 5 | 2.40e-02 to 2.78e-02 |
| 2.9 | 2.55e-03 | 5.70e-03, 0 | 4 / 2 | 6 / 1 | 5 | 3.16e-02 to 3.74e-02 |

The lesion moves Delta_T by 2 to 6 times the band. T_S keeps no eigenvalue
below -band; its lowest is positive, above the band at 2.2 and 2.5, inside
it at 2.9. n_-(R) rises from 4 to 5 / 6 / 6 against the lesion's own Q, and
to 4 / 5 / 5 against 2 Q_zeta. Grade: measured, one route, lesion only.

### 7.5 Kill-controls, all four

| control | what it tests | outcome |
|---|---|---|
| 1, (U-S) gate | exact, n <= 200 | **pass**: rejects Epstein (n = 6, 8) and W_a (n = 2), accepts zeta and Dedekind (s3) |
| 2, refusal | the builder given W_a or Epstein's 2-adic tower | **pass**: both refused (NonUnitaryLocalData) (s5.1) |
| 3, positive control | Dedekind zeta_{Q(sqrt -23)} through the builder | **not exercised**: Gamma_C framework limit at S = {inf, 2} (s5.4). Any T_S or R_S statement here is about zeta alone (s5.6) |
| 4, lesion (optional) | gate bypassed, W_a's data | **refused at the provider** (NotImplementedError); below both guards T_S has no eigenvalue below -band and n_-(R) rises 4 -> 5 / 6 / 6 (s7.4) |

### 7.6 What would decide it, and a CI proposal

The binding constraint is the accuracy of Delta_T at the top frequencies of
each N. Q and T_inf are known far below float64 and enter R_S at float64
rounding (1e-16 relative).

- **The door:** the N = 32 row against more modes, and two_adic/'s own
  default rule (364 / 319 / 280 modes, S = 24 pi N / L). If the 12 to 14
  top-half negatives at N = 32 move by more than their depth (about 1.2e-2
  to 1.8e-2), the growth is truncation. If they stay, P5 fails at the
  measured grade on c = 2.5 and 2.9. (Written 2026-09-23. It ran; the
  outcome is s7.7.)
- **Ran on Modal, not CI** (operator's approval, 2026-09-24): (240, 2400, 32)
  and the three default-rule rows, all three cells per unit, 844 to 1784 s
  each in the child process (`modal/RESULTS.md`). The laptop estimate had failed at Kmax 14.
- **The door now is the route, not the mode count.** `ta_mellin.rho`
  inverts Gb with `np.linalg.inv`, and cond(Gb) grows 3.9e9, 4.9e12, 1.1e17
  as modes go 200, 240, 280 (s7.7). More modes on this route cannot resolve
  N = 32 in float64. Evaluating rho without the explicit inverse (a
  factorization, or that one step at higher precision) is two_adic/'s code;
  reported to the coordinator, not fixed here. (Done: two_adic/ c3dca00
  evaluates rho by a QR of the Gram factor; every unit was rebuilt on
  Modal and re-graded in s7.8.) Optional, if the 200 -> 240
  response is to be split into arithmetic and truncation: (240, 2400, 32)
  again on Modal with the Sandybridge kernels, about 890 s and 0.078 USD
  computed at the rates of `modal/RUNS.md` s2, as its first run. The grade below does not
  need it.
- **After s7.8, the door at c = 2.5 is S, not the route.** band(2.5, 32) is
  the 319-mode row's response, and that row changes the mode count and
  lowers S/nvec^2 to 0.026 at once; the verdict turns on 7 to 8 eigenvalues
  between the band it sets and the 240-mode band. two_adic/'s batch 2 (the
  default-rule rows at S/nvec^2 = 0.04; the 319-mode unit about 1600 s,
  two_adic/ s10.5) would separate the two. It is not asked for: the
  falsifier did not fail, and the reading does not need it. c = 2.9 does not
  depend on it (its band is the probe).
- **The positive control** needs 23 in S or the construction over
  K = Q(sqrt -23) (s5.4). Forge's ruling keeps S = {inf, 2}.

### 7.7 The Modal N = 32 rows (follow-up, 2026-09-24)

*Old route (rho by `np.linalg.inv`). Superseded at N = 32 by s7.8. Every
number in this section is read from the snapshot and cells JSON at 3dc0a74
(last written 8d66d09), and its tests read them from there.*

**Reading of the s7.6 criterion, committed before any eigenvalue of R_S on a
Modal row was computed.** s7.6, written on 2026-09-23 before these runs
existed: if the 12 to 14 top-half negatives at N = 32 move by more than their
depth (about 1.2e-2 to 1.8e-2), the growth is truncation; if they stay, P5
fails at the measured grade on c = 2.5 and 2.9. It is applied as follows and
not moved after the numbers:

1. **Band.** band(c, 32) = max(two_adic/'s probe for (200, 2400, 32), the
   refinement response ||T_S(240, 2400) - T_S(200, 2400)||_2, the quadrature
   response at N = 16). The refinement response replaces the N = 16 proxy.
   No probe exists for the new rows (`ta_ts_prolate.json` holds N = 32 rows
   only at (130, 1800) and (200, 2400)), so one threshold per cell serves
   every N = 32 build, as band(c, 16) did in s7.3a (1).
2. **Weyl clause.** ||T_S(X) - T_S(200, 2400)||_2 against the actual depths
   of the 200-mode row's top-half negatives (14 at c = 2.5, 12 at 2.9), and
   which of those depths it exceeds. An eigenvalue deeper than -band by more
   than the response cannot cross -band (Weyl); a shallower one can.
3. **Recount clause.** On every N = 32 build (laptop 200, Modal 200, Modal
   200 with the Sandybridge kernels, 240, and the default-rule rows): n_-
   below -band(c, 32), the top-half count, the lowest three, the last pair
   counted. A top-half negative has moved by more than its depth when it is
   no longer below -band(c, 32).
4. **Verdict**, on the refined rows, against the N = 16 counts (9 at 2.5, 10
   at 2.9): the count **survives** if it still exceeds the N = 16 count
   outside the platform-undecided eigenvalues, **falls** if it is at most
   the N = 16 count, and is **undecided** if the difference lives inside
   flagged eigenvalues.
5. **Which rows are refined rows.** (240, 2400), and the default-rule rows
   (364, 3060) at 2.2, (319, 2633) at 2.5, (280, 2266) at 2.9, each only if
   its T_S passes P2 at the band (no eigenvalue of T_S below -band(c, 32)),
   the test s7.3 applied to every delivered row.
6. **Platform flag.** An eigenvalue within 2.93e-7 + 3.39e-7 = 6.32e-7 of
   -band(c, 32) is platform-undecided. That bound was measured on the
   200-mode unit (cond_Gb 3.9e9). For units whose cond_Gb is larger it is a
   floor, not a measurement. The three 200-mode builds are also
   eigendecomposed directly.

Visible when this reading was written: each Modal unit's cond(Gb), and the
first few entries of the first row of T_S for the 200, 240 and 280-mode units.
No eigenvalue of T_S or R_S on a Modal row had been computed.

Grade of everything in this section: measured, float64, one route. Modal and
the laptop are the same route on two platforms, not independent routes.

**What ran.** `run_checker_ts.py --merge-modal` copied the four Modal units
into `checker_ts_snapshot.json` under the same T_S input digest (1dcab230),
refusing any file whose status, in-container guard, digest or unit key is
off (a test plants each). Each unit records its source file, sha256,
platform (Linux x86_64, Python 3.12, OpenBLAS) and the calibration bounds.
The laptop (200, 2400, 32) rows are unchanged since 535882e, and `T_S()`
still serves them; the Modal builds of that unit are read from `modal/out`
for the platform check only.

**Every N = 32 build at one threshold, band(c, 32)** (3.92e-2 / 2.37e-2 /
3.16e-2), and at the proxy band of 535882e (1.59e-2 / 7.55e-3 / 8.18e-3).
Counts are n_- / top half (more than half the weight on |n| > 16).

| c | build (nvec, S) | cond(Gb) | T_S lowest | \|\|T_S - T_S(200)\|\|_2 | at band(c, 32) | at the proxy band | last two counted |
|---|---|---|---|---|---|---|---|
| 2.2 | (200, 2400) laptop | 3.9e+09 | 2.45e-03 | 0.00e+00 | 0 / 0 | 3 / 2 | none |
| 2.2 | (240, 2400) | 4.9e+12 | -7.35e-03 | 3.92e-02 | 0 / 0 | 9 / 6 | none |
| 2.2 | (280, 2266) | 1.1e+17 | 4.60e-02 | 1.25e+00 | 20 / 8 | 25 / 9 | -0.04542, -0.04094 |
| 2.2 | (319, 2633) | 2.8e+18 | -1.43e+01 | 1.81e+01 | 19 / 13 | 22 / 14 | -0.0489, -0.04533 |
| 2.2 | (364, 3060) | 5.1e+17 | -2.22e+01 | 2.61e+01 | 25 / 12 | 27 / 14 | -0.06993, -0.05272 |
| 2.5 | (200, 2400) laptop | 3.9e+09 | 1.76e-03 | 0.00e+00 | 2 / 0 | 20 / 14 | -0.039, -0.02579 |
| 2.5 | (240, 2400) | 4.9e+12 | -8.45e-03 | 2.37e-02 | 5 / 1 | 19 / 8 | -0.02638, -0.02481 |
| 2.5 | (280, 2266) | 1.1e+17 | 3.03e-02 | 1.09e+00 | 22 / 12 | 27 / 13 | -0.03662, -0.03215 |
| 2.5 | (319, 2633) | 2.8e+18 | -1.36e+01 | 1.74e+01 | 22 / 12 | 27 / 15 | -0.03494, -0.02422 |
| 2.5 | (364, 3060) | 5.1e+17 | -3.37e+01 | 3.73e+01 | 28 / 16 | 29 / 17 | -0.03457, -0.03406 |
| 2.9 | (200, 2400) laptop | 3.9e+09 | 1.50e-03 | 0.00e+00 | 2 / 0 | 20 / 12 | -0.1203, -0.0451 |
| 2.9 | (240, 2400) | 4.9e+12 | -8.93e-03 | 3.16e-02 | 4 / 2 | 23 / 13 | -0.03476, -0.03339 |
| 2.9 | (280, 2266) | 1.1e+17 | 1.97e-02 | 1.32e+00 | 22 / 13 | 28 / 16 | -0.0356, -0.03353 |
| 2.9 | (319, 2633) | 2.8e+18 | -1.41e+01 | 1.78e+01 | 20 / 12 | 26 / 16 | -0.04614, -0.04048 |
| 2.9 | (364, 3060) | 5.1e+17 | -3.66e+01 | 3.99e+01 | 28 / 17 | 30 / 18 | -0.05155, -0.0404 |

**Outcome, by the reading above.**

- **Band.** The refinement response is 3.92e-2 / 2.37e-2 / 3.16e-2, 2.5 to
  8.6 times the N = 16 response it replaces, and it sets band(c, 32) on
  every cell. The laptop and Modal 200-mode rows differ by 2.3e-7 to
  2.9e-7, nothing at this scale.
- **Weyl clause.** The response exceeds the depth of every top-half negative
  of the 200-mode row: 14 of 14 at 2.5 (from -1.83e-2 to -8.0e-3), 12 of 12
  at 2.9 (from -1.45e-2 to -1.21e-2). It holds only the deepest eigenvalue
  at 2.9 (-0.12) below -band.
- **Recount.** 0 / 2 / 2 on the 200-mode row, 0 / 5 / 4 on the 240-mode
  row, against 4 / 9 / 10 at N = 16.
- **Platform.** No eigenvalue of any build lies within 6.32e-7 of -band (the
  closest is 5.0e-4 away, 319 modes at 2.5; 5.9e-4 on the 240-mode row).
  The laptop, Modal and Modal Sandybridge builds of the 200-mode unit give
  the same counts at both bands, eigenvalues within 2.8e-7.
- **Verdict.** c = 2.5: **falls** (240 modes: 5, at most 9; the 319-mode
  row is not admitted, T_S lowest -13.6). c = 2.9: **split**. The 240-mode
  row falls (4, at most 10); the 280-mode row passes P2 at the band (T_S
  lowest +2.0e-2), so it is admitted, and survives (22). The reading does
  not say how two admitted rows that disagree combine, so by the letter
  c = 2.9 is **undecided**. c = 2.2 is outside the criterion: 0 on the 200
  and 240-mode rows, the 364-mode row not admitted.

**What "falls" means here.** The band rose past the negatives; the
negatives did not leave. At the proxy band the 240-mode row still holds 19
(2.5) and 23 (2.9) negatives, 8 and 13 of them on the top half. So the
N = 16 to 32 growth is not supported at N = 32's own band, and it is not
refuted: n_-(R_S) at N = 32 is undecided on this route in float64. P5's
failure at c = 2.9 from N = 8 to 16 (s7.3a) is untouched; it rests on
N = 16 rows.

**Neither refined row is a clean refinement.** Measured; the conclusions
drawn from the numbers are ordinary arguments, stated as such.

- **240 modes.** T_S has lowest eigenvalue -7.3e-3 / -8.5e-3 / -8.9e-3.
  Since T_S >= 0 (P2, elementary), this row is off by at least that much in
  spectral norm (Weyl); the 200-mode row is positive (1.5e-3 to 2.4e-3). It
  moves the N = 8 block by 1.6e-2 to 1.8e-2, 10 to 15 times what 120 -> 160
  moved it at N = 16 (1.1e-3 to 1.7e-3), and at 2.5 and 2.9 the direction it
  moves most carries weight 0.06 and 0.29 on |n| > 16 (0.99 at 2.2).
  Top-frequency truncation does not have that shape. cond(Gb) is 4.9e12;
  eps x cond(Gb) = 1.1e-3 is an estimate of its arithmetic floor (on the
  200-mode unit the measured floor was 0.34 of that product), not a
  measurement. At that floor the counts range 0 / 4 to 6 / 4, all at most
  the N = 16 counts, so the verdict does not depend on it.
- **The default-rule rows.** `ta_mellin.rho` inverts Gb with
  `np.linalg.inv`; cond(Gb) is 1.1e17 (280), 2.8e18 (319) and 5.1e17
  (364), above 1/eps = 4.5e15, where the float64 inverse is not determined
  by Gb. T_S at 319 and 364 modes fails P2 by 13.6 to 36.6. At 280 it
  passes P2 but moves T_S by 1.09 to 1.32 from the 200-mode row, 32 to 46
  times the 240-mode step, and moves the N = 8 block by 9.1e-2 to 0.13.
  **The 280-mode row that survives at c = 2.9 is this row.** Its eps x
  cond(Gb) is 24: if the calibrated scaling holds there, every eigenvalue
  lies inside its floor. That argument was not part of the reading fixed
  before the numbers; with it, c = 2.9 falls on the same terms as 2.5.

Grade of everything in s7.7: measured, float64, one route on two platforms.
The door is s7.6's last bullet: rho without the explicit inverse.

### 7.8 Follow-up 2 (2026-09-24): the rows under the QR rho

two_adic/ replaced the explicit inverse in `ta_mellin.rho` by a QR of the
Gram factor (c3dca00, eea7eab; its RESULTS s10). T_S's input digest moved
from 1dcab230 to b2e7787bce7a (the closure digest is b2e7787bce7a at
c3dca00, eea7eab, e2b46a5 and HEAD caef639; the guard reads it, dirty list
empty). modal/ rebuilds all eleven units into `modal/out_rho/` (modal/RUNS.md
s7). Everything in s7.1 to s7.7 above was measured on the old route; its
snapshot and cells JSON stay citable from git history at 3dc0a74 (both last
written at 8d66d09).

**Reading, committed before any eigenvalue of T_S or R_S on a rebuilt row
was computed.** The s7.6 criterion is carried over unchanged: if the 12 to 14
top-half negatives at N = 32 move by more than their depth, the growth is
truncation; if they stay, P5 fails at the measured grade on c = 2.5 and 2.9.
The s7.7 reading is carried over with the changes marked *new*; none is moved
after the numbers.

1. **Probe and route.** two_adic/'s probe is read from `ta_ts_prolate.json`
   at c3dca00, where it was regenerated under the QR route (015895f's rows are
   the old route). N = 8 and 16 keep their band rule exactly (s7.3).
2. **Refined rows at N = 32, per cell:** (240, 2400) and the cell's
   default-rule row, (364, 3060) at 2.2, (319, 2633) at 2.5, (280, 2266) at
   2.9 (s7.7 clause 5). The other two default-rule builds of each cell are
   reported, not used for the band or the verdict. The delivered row stays
   (200, 2400).
3. **Row-independent band** (*new*, closes a circularity): band_0(c) =
   max(probe(200, 2400, 32), quadrature response at N = 16). s7.7 tested P2
   at a band that contained the 240-mode row's own response; since
   lambda_min(T_S(X)) >= lambda_min(T_S(200)) - ||T_S(X) - T_S(200)||_2,
   that test is vacuous for the row that sets the band. Admission is tested
   at band_0.
4. **Determinacy gate** (*new*; s7.7 used this kind of argument only after
   the numbers, this one is fixed before them). cond_F(X) = max(cond_Fz,
   cond_Fb) of the unit, as `delta_T_cells` reports it. A row with
   cond_F >= 1e14 is past two_adic/'s measured stopping point (s10.4:
   "a row above about 1e14"; A2: rho off by 1.4e-5 at cond(F) = 6.7e11 and by
   6.5e-2 at 3.8e14). Such a row is reported, and neither sets the band nor
   enters the verdict. A row between 6.7e11 and 1e14 is admitted and marked
   "beyond A2's last clean case".
5. **Admission:** a refined row is admitted when it passes the gate and P2 at
   band_0 (lambda_min(T_S(X)) >= -band_0(c)).
6. **The band at N = 32** (*new*: the response that replaces "the 240-mode
   refinement"). band(c, 32) = max(band_0(c), ||T_S(X) - T_S(200, 2400)||_2
   over the admitted refined rows X of the cell): the largest measured
   response, as P1's rule has it at every N. The default-rule row's response
   enters, following the N = 16 precedent (the delivered row against
   two_adic/'s own rule, 160 modes); the 240-mode response stays in, as the
   pure mode count at equal S. With no admitted refined row, band(c, 32) =
   band_0(c) and the N = 32 verdict is "undecided, no admitted refinement".
   One threshold per cell serves every N = 32 build (s7.7 clause 1).
7. **The falsifier** (two_adic/ s10.4; P2 on every N = 32 build, the four
   rebuilt refinements on all three cells), at band_0(c), in bins fixed now:
   **pass**, lambda_min(T_S) >= -band_0; **fails at order 1e-2**,
   -0.1 <= lambda_min < -band_0; **fails at order 1e-1**, -1 <= lambda_min
   < -0.1; **fails at order 1 or more**, lambda_min < -1 (the old route gave
   -13.6 to -36.6 at 319 and 364 modes): the fix did not work on that row.
   If 280, 319 or 364 fails at order 1e-2 on any cell, `worker_done` asks
   for two_adic/'s batch 2 (the default-rule rows at S/nvec^2 = 0.04) and
   nothing is run here. Each result is also stated against the numbers
   two_adic/ quoted before the run, the old band(c, 32) 3.92e-2 / 2.37e-2 /
   3.16e-2; where the two thresholds disagree, both outcomes are said.
   cond_Fz and cond_Fb are reported beside each result and move no bin.
   two_adic/'s predictions, tested as written: 280 passes; the order-10
   failures at 319 and 364 are gone, with order 1e-2 possible; the 240-mode
   row comes within about 1e-2 of the 200-mode row and band(c, 32) falls.
8. **The criterion's referent.** The rebuilt 200-mode row's top-half
   negatives (more than half the weight on |n| > 16) below the proxy band
   max(probe(200, 2400, 32), refinement response at N = 16, quadrature
   response). Expected to be the old set (14 at 2.5 from -1.83e-2 to
   -8.0e-3, 12 at 2.9 from -1.45e-2 to -1.21e-2), since A1 moves that row by
   1.8e-7 to 2.0e-7; any change in the set is reported.
9. **Weyl, recount and verdict, as s7.7 clauses 2 to 4.** Weyl: each admitted
   row's ||T_S(X) - T_S(200)||_2 against those depths. Recount: on every
   N = 32 build, n_- below -band(c, 32), the top-half count, the lowest three
   and the last pair counted, and the same at the proxy band, so that "the
   band rose" and "the negatives left" stay apart. Per admitted refined row,
   against the rebuilt N = 16 count n16 (9 at 2.5 and 10 at 2.9 on the old
   route): **survives** if the count exceeds n16 outside the
   platform-undecided eigenvalues, **falls** if it is at most n16, and is
   **undecided** otherwise. *New*, the gap s7.7 found: the cell's verdict is
   survives if every admitted refined row survives, falls if every one
   falls, and **split** otherwise, reported as undecided with the rows
   named. c = 2.2 lies outside the criterion and is reported the same way.
10. **Platform flag** (*new* size). The drift under the QR route is
    3.2e-12 (two_adic/ A3: a 2^-52 relative perturbation of every sample
    moves Delta_T by 2.9e-12 to 3.2e-12 at (200, 2400), N = 32; a proxy, not
    a rebuild on another platform). flag(X) = 3.2e-12 x max(1, cond_F(X) /
    cond_F(200, 2400)): the scaling is an estimate (the QR route's arithmetic
    error grows like eps x cond(F), two_adic/ s10.3). The one cross-platform
    measurement on the new route is (80, 1200, 8), 7.1e-15 (modal/RUNS.md
    s7.4), and it is checked here against `out_rho/local_checker_80_1200_8.json`.
    Every row of the new snapshot is a Modal build; no laptop build of
    (200, 2400, 32) exists on the new route, so s7.7's three-build platform
    check of that unit has no analogue and is dropped. An eigenvalue within
    flag of -band is platform-undecided.
11. **N = 8 and 16.** Every count and band is compared with the old cells
    JSON (3dc0a74). "Moved" means an integer count changed; the largest change
    of each band and of the listed eigenvalues is reported. two_adic/ expects
    changes of 1e-7 at most (A1: Delta_T moves by at most 2.7e-13 there).
12. **When the grade is final:** when all eleven units are in `out_rho/` or
    recorded as timed out in modal/RUNS.md s7.6. Before that, N = 8 and 16
    are analysed and N = 32 is marked pending.

**Visible when this reading was written** (19:22 UTC): seven rebuilt units
in `out_rho/`, (80, 1200, 8), (80, 1200, 16), (80, 1600, 16),
(120, 1200, 16), (120, 1600, 16), (160, 1600, 16) and (200, 2400, 32), and
`local_checker_80_1200_8.json`. Of these, one file (80, 1200, 16) was opened
for its key names only: its unit diag carries `cond_Fz`, `cond_Fb`, `cond_Gb`
and `gram_z_offI`, and its calibration block no longer carries
`weyl_bound`. No T_S entry, cond value or eigenvalue of a rebuilt row was
read. No 240, 280, 319 or 364-mode unit had landed. Read: two_adic/ RESULTS
s10 in full (A1 to A4, including its own T_S lowest eigenvalues at
(200, 1200) and (200, 2400) on the QR route) and modal/RUNS.md s7 to the
unit log. The key names of the regenerated `ta_ts_prolate.json` were read,
not its values.

Grade of everything in s7.8: measured, float64, one route. The rebuilt rows
are all Modal builds of one route; no independent route exists for Delta_T.

**What ran.** `run_checker_ts.py --rebuild-rho --analyse c3dca00`, locally,
about 25 s a run, nothing built: N = 8 and 16 first (19:27 UTC, with the
319 and 364-mode units still out), then c = 2.9 and 2.5 as their refined
rows landed, then all eleven (the 364-mode unit landed at 19:48 UTC; none
timed out). The analysis code is s7.3's, with the N = 32 part replaced by
the reading above; the s7.7 version is at 3dc0a74.

**N = 8 and 16 did not move** (clause 11). Every count equals the old
route's: the delivered rows on all three classes, the top-half and
resolved-half splits, Q - T_inf, and the four discriminator builds at
N = 16. The delivered rows' listed eigenvalues move by at most 2.8e-14
(N = 8) and 2.1e-13 (N = 16). The bands move by at most 3.5e-8, through
the 160-mode build (cond_F 4.4e5, the largest at N = 16), whose eigenvalues
move by 3.7e-8 to 4.7e-8. two_adic/ expected 1e-7 at most. s7.2, s7.3 and
s7.3a print the same digits at N = 8 and 16, except P3 at equal settings
(s7.2).

**Platform** (clause 10). The (80, 1200, 8) unit, laptop against Modal:
7.1e-15. At N = 32 one cross-platform datum exists after all: two_adic/
built (200, 2400, 32) on the laptop under the QR route (`ta_rho_check.json`,
A4), and its three lowest T_S eigenvalues differ from the Modal row's by at
most 2.5e-12, where A3's proxy said 3.2e-12. No eigenvalue of R_S on any
N = 32 build lies within its flag of -band. The flags run from 3.2e-12 (200
modes) to 7.7e-5 (319 modes, the scaled estimate); the smallest gap is
1.8e-5, on the delivered row at 2.5, whose flag is 3.2e-12.

**The falsifier** (clause 7) passes on all fifteen N = 32 builds, at band_0
and at the old band(c, 32): T_S's lowest eigenvalue lies between +1.09e-3
and +4.41e-3 (the old route: -13.6 to -36.6 at 319 and 364 modes).
two_adic/'s predictions, as written: 280 passes, yes. The order-10
failures at 319 and 364 are gone, yes, and no order-1e-2 failure appears
either, so batch 2 is not asked for. "The 240-mode row comes within about
1e-2 of the 200-mode row and band(c, 32) falls": the band fell on every
cell, and the 240-mode response is 2.3e-3 at 2.9 and 1.08e-2 at 2.5, but
2.97e-2 at 2.2; that half is refuted at 2.2.

**The gate** (clause 4). cond_F is 8.7e5 (200 modes), 1.1e9 (240), 1.9e13
(280) and 2.1e13 (319, 364). None reaches 1e14. The 280, 319 and 364-mode
rows lie beyond A2's last clean case (6.7e11): admitted, and marked.

Every N = 32 build at band(c, 32), and at the proxy band. Counts are n_- /
top half (more than half the weight on |n| > 16).

| c | build (nvec) | cond_F | T_S lowest | falsifier | \|\|T_S - T_S(200)\|\|_2 | at band(c, 32) | at the proxy band | last two counted |
|---|---|---|---|---|---|---|---|---|
| 2.2 | 200 | 8.7e+05 | 2.45e-03 | pass | 0.00e+00 | 0 / 0 | 3 / 2 | none |
| 2.2 | 240 | 1.1e+09 | 2.03e-03 | pass | 2.97e-02 | 0 / 0 | 1 / 0 | none |
| 2.2 | 280 | 1.9e+13 | 2.40e-03 | pass | 2.31e-02 | 0 / 0 | 3 / 0 | none |
| 2.2 | 319 | 2.1e+13 | 2.87e-03 | pass | 2.16e-02 | 0 / 0 | 1 / 0 | none |
| 2.2 | 364 | 2.1e+13 | 4.41e-03 | pass | 2.15e-02 | 0 / 0 | 2 / 0 | none |
| 2.5 | 200 | 8.7e+05 | 1.76e-03 | pass | 0.00e+00 | 8 / 2 | 20 / 14 | -0.01541, -0.01465 |
| 2.5 | 240 | 1.1e+09 | 1.34e-03 | pass | 1.08e-02 | 6 / 0 | 14 / 7 | -0.01557, -0.01482 |
| 2.5 | 280 | 1.9e+13 | 1.69e-03 | pass | 1.28e-02 | 6 / 0 | 14 / 6 | -0.01632, -0.01536 |
| 2.5 | 319 | 2.1e+13 | 2.20e-03 | pass | 1.41e-02 | 5 / 0 | 14 / 7 | -0.01557, -0.01428 |
| 2.5 | 364 | 2.1e+13 | 3.71e-03 | pass | 1.49e-02 | 6 / 0 | 14 / 8 | -0.01511, -0.01457 |
| 2.9 | 200 | 8.7e+05 | 1.50e-03 | pass | 0.00e+00 | 20 / 12 | 20 / 12 | -0.01236, -0.01214 |
| 2.9 | 240 | 1.1e+09 | 1.09e-03 | pass | 2.26e-03 | 20 / 12 | 20 / 12 | -0.01123, -0.01084 |
| 2.9 | 280 | 1.9e+13 | 1.42e-03 | pass | 4.95e-03 | 20 / 12 | 20 / 12 | -0.01053, -0.01028 |
| 2.9 | 319 | 2.1e+13 | 1.98e-03 | pass | 4.37e-03 | 20 / 12 | 20 / 12 | -0.008939, -0.008736 |
| 2.9 | 364 | 2.1e+13 | 3.42e-03 | pass | 4.91e-03 | 21 / 12 | 21 / 12 | -0.008646, -0.008418 |

**Outcome, by the reading.**

- **Band** (clause 6). Every refined row is admitted on every cell.
  band(c, 32) is 2.97e-2 at 2.2 (the 240-mode response), 1.41e-2 at 2.5
  (the 319-mode response) and 8.18e-3 at 2.9 (band_0, the probe: the 240
  and 280-mode rows move T_S by 2.3e-3 and 4.95e-3, both below it).
- **Referent** (clause 8). The delivered row's top-half negatives at the
  proxy band are the old set: 14 at 2.5 from -1.83e-2 to -8.0e-3, 12 at 2.9
  from -1.45e-2 to -1.21e-2 (2 at 2.2).
- **Weyl.** At 2.9 no response exceeds any of the 12 depths, on any build.
  The 240-mode response keeps all 20 negatives of the delivered row below
  -band by Weyl; the 280-mode response keeps 10, and the other 10 stay by
  measurement. At 2.5 the 319-mode response exceeds 12 of the 14 depths,
  the 240-mode response 2.
- **Recount.** 2.9: 20 / 12 on the 200, 240, 280 and 319-mode builds, 21 / 12
  on 364. 2.5: 8 / 2 on the delivered row; 6 / 0, 6 / 0, 5 / 0, 6 / 0 on
  240, 280, 319, 364. 2.2: 0 on every build.
- **Verdict.** c = 2.9 **survives** (240: 20, 280: 20, against 10 at
  N = 16). c = 2.5 **falls** (240: 6, 319: 5, against 9). c = 2.2 **falls**
  (0 and 0, against 4). No count is platform-undecided.

**What each verdict rests on.**

- **c = 2.9.** The band is the probe, and no refinement is needed to set
  it: dropping every row beyond A2's last clean case, the 240-mode row alone
  gives the same band and the same 20. The last pair counted sits at
  -1.03e-2 to -1.24e-2 (1.26 to 1.51 times the band) on the delivered,
  240 and 280-mode builds, and the first eigenvalue not counted at -7.7e-3,
  inside it. By s7.6 the top-half negatives stay, so **P5 fails at the
  measured grade on c = 2.9**: n_-(R_S) = 4, 10, 20 at N = 8, 16, 32, each
  count unchanged under the refinements run at its N. The 280-mode row is
  not a pure mode refinement: its S is 2266, below the delivered 2400, and
  its response sits on the low modes (weight 0.0 on |n| > 16 in the
  direction it moves most; the N = 8 block carries all 4.95e-3 of it). That
  is the shape of an S change; two_adic/'s A4 measured S = 1200 -> 2400 at
  200 modes moving T_S by 5.6e-3 / 6.2e-3 / 8.0e-3.
- **c = 2.5.** Falls by the reading, and the verdict rests on the band
  rule. *Sensitivity, computed after the numbers and not part of the
  reading:* at the band s7.7's rule would give, the 240-mode response alone
  (1.08e-2), the refined rows count 14 (240) and 12 (319), above 9; 8 and 7
  of their eigenvalues lie between -1.41e-2 and -1.08e-2. The depth clause
  agrees with the verdict: at the fixed proxy band (7.55e-3) the count drops
  from 20 on the delivered row to 14 on each refined row, and the top half
  from 14 to 6 to 8, so negatives did leave; the band did not only rise.
  The band is set by a row beyond A2's last clean case (319 modes, cond_F
  2.1e13). The delivered row counts 8, one eigenvalue 1.8e-5 from -band.
- **c = 2.2.** 0 on every build at 2.97e-2, and 1 to 3 at the proxy band;
  at most 4 either way.

**Changed keys of `checker_ts_cells.json`**, because two_adic/'s
`test_ta_checker_citations.py` pins some of them. Removed: `band_32_before_merge`,
`band_cell_before_merge`, every row's `refinement_proxy`; under `modes_N32`:
`band_before_merge`, `platform_flag`, `platform_200`,
`top_half_depths_200_before_merge`, the builds `200_modal` and
`200_modal_sandybridge`, and per build `P2_at_band`, `eps_cond_estimate`,
`n_minus_range_at_eps_cond`, `n_minus_at_band_before_merge` and
`n_minus_top_half_at_band_before_merge` (the last two are now
`n_minus_at_proxy_band` and `n_minus_top_half_at_proxy_band`). Added:
`band_0_32`, `band_32_proxy`, `vs_old_route`; under `modes_N32`: `band_0`,
`band_proxy`, `old_band_32`, `refinement_response`, `admitted`,
`cond_F_200`, `cell_verdict`, `top_half_depths_200_at_proxy_band`,
`sensitivity_band_240_only`, and per build `cond_Fz`, `cond_Fb`, `cond_F`,
`past_gate`, `beyond_A2_last_clean`, `P2_bin`, `P2_bin_at_old_band`,
`platform_flag` and `sensitivity_n_minus_at_band_240_only`. Changed values
(beyond 1e-6 relative): at N = 32 every count, eigenvalue and band of the
delivered row, `32.probe` (by at most 6.4e-8), `refinement_response.32`
and `band_cell`; every value under `modes_N32.builds`, the verdict labels
(`240` at 2.9 now survives; `319` and `364` now admitted); at N = 8 and 16
the bands, `refinement_response.8` and `.16` and the 120 -> 160 responses
(by at most 3.7e-8), `n_minus_at_band_cell` wherever it appears, the
160-mode discriminator's eigenvalues, and `P3_same_settings_defect` (0 ->
4.4e-15 to 6.2e-15). The pins of two_adic/ that break: `32.full.n_minus`
(0, 2, 2 -> 0, 8, 20), `modes_N32.builds.*.n_minus` and the renamed
proxy-band keys, the 2.9 verdict of the 240-mode row, `builds.280.n_minus`
(22 -> 20) and `cond_Gb` (1.1e17 -> 2.9e17), `refinement_response.32` and
`32.band` (their equality fails at 2.9, where the probe sets the band), and
`builds.240.T_S_low` (now positive, 1.09e-3 to 2.03e-3).

Grade of the outcome: measured, float64, one route, one platform for every
row; the band indicates and does not bound. A composite claim takes its
weakest step: at 2.9 that is the band (the probe), at 2.5 the 319-mode row.

### 7.9 Follow-up 3 (2026-09-24): exact inertia of the stored c = 2.9 matrices

Operator request via the coordinator (BRIEF follow-up 3 and its addendum):
harden the c = 2.9 count (n_- = 4, 10, 20 at N = 8, 16, 32) on the matrices
already produced. No new modes, no Modal. Code `run_checker_inertia.py`,
tests `test_checker_inertia.py`, output `checker_inertia.json` (a new file).
The snapshot and `checker_ts_cells.json` are read and not written, so no key
of `checker_ts_cells.json` changes.

**Reading, committed with its test before any inertia of a stored matrix was
computed.** The pre-registered test is `test_the_count_holds`; the tests of
group 2 of that file encode clauses 1 to 7.

1. **The matrix.** Per build, R = Q - T_S formed in numpy exactly as
   `run_checker_ts.analyse` forms it: Q is the checker's Q at dps 40 rounded
   to float64 (its central block for N < 32), T_S the snapshot row (digest
   b2e7787bce7a). numpy's eigh reads the lower triangle, so the matrix whose
   inertia is computed is R's lower triangle mirrored. Every entry is a
   float64, hence an exact dyadic rational, converted by
   `float.as_integer_ratio` without rounding. The exact symmetry defect
   max |R_ij - R_ji| is recorded; if it is not 0, the upper mirror is run at
   the band as well and reported. A test rebuilds R, checks its sha256
   against the JSON, and checks that its float64 eigenvalues give the stored
   count.
2. **Builds, band source, count source.** All eight c = 2.9 builds of the
   snapshot: (80, 1200, 8); (120, 1600, 16), (160, 1600, 16); (200, 2400,
   32), (240, 2400, 32), (280, 2266, 32), (319, 2633, 32), (364, 3060, 32).
   The shift is the band stored in `checker_ts_cells.json`, read as a float64
   and never re-derived: `cells['2.9']['8']['band']` = 5.3175684479389584e-3
   at N = 8; `['16']['band']` = 5.8631887276274774e-3 for both N = 16 builds
   (the one threshold of s7.3a (1)); `['modes_N32']['band']` =
   8.179786419034496e-3 for every N = 32 build (one threshold per cell,
   s7.8 clause 6; equal to `['32']['band']`). The float counts tested
   against come from the same file: `['8']['full']['n_minus']`,
   `['16']['full']['n_minus']`, `['modes_N16_S1600']['160']['N16_n_minus']`
   and `['modes_N32']['builds'][nvec]['n_minus']`, that is 4; 10, 10; 20,
   20, 20, 20, 21.
3. **Exact inertia** of R + band I, by two routes over the rationals
   (python-flint 0.9.0 `fmpq`; `rigor.available_backends()` lists
   python-flint, and a test asserts it): (a) symmetric elimination with
   diagonal pivoting, counting pivot signs (Sylvester's law of inertia), with
   the congruence e_i -> e_i + e_j when every remaining diagonal entry is 0
   and an off-diagonal one is not; (b) the characteristic polynomial and
   Descartes' rule of signs, exact because every root of a symmetric
   matrix's characteristic polynomial is real (the three counts must add up
   to the dimension). The routes must agree at every shift evaluated; a
   disagreement is a defect here and stops the run. By Sylvester,
   n_-(R + band I) is the number of eigenvalues of R strictly below -band,
   and n_0 the number exactly at it.
4. **Brackets.** count_below(t) = n_-(R - t I), exactly; lambda_k (the k-th
   smallest) lies in [lo, hi) exactly when count_below(lo) <= k - 1 and
   count_below(hi) >= k. For k = 1 to n_- + 1 (every counted eigenvalue and
   the first one not counted): seeds are the float64 eigenvalue plus and
   minus 2^-41; each end is widened by doubling until the exact counts
   confirm it; the shift is bisected until hi - lo <= 2^-40; and if -band
   lies strictly inside, it is tested and becomes an end. Both routes
   evaluate every end, and the seeds only save work. The margin below -band,
   -band - lambda_k, lies in (-band - hi, -band - lo] and is reported as that
   interval.
5. **Sensitivity row**, reported and not a criterion: n_- of R + m band I for
   m = 2, 5, 10, both routes.
6. **The C4 class V_4** (theory s7.2: g-hat vanishing at +i/2, -i/2 and 0,
   where g is the window function itself, the factor in g * g^*). By
   `checker_q.transform_rows`, "plus" is (e^{L/2} - 1) L^{-1/2} / (1/2 + i
   w_n) and "minus" a real multiple of its complex conjugate (w_n = 2 pi n /
   L), so both vanish exactly when v is orthogonal to the real vectors
   h_n = 1/(L^2 + 16 pi^2 n^2) and n h_n; "zero" is L^{1/2} v_0. So V_4 is
   the complexification of a real subspace of codimension 3, and a real
   symmetric form has the same inertia on both (derivation, elementary; a
   test checks it against the dps 40 rows). V_4 is not the class s7.3 calls
   V_-0 (g-hat(-i/2) = g-hat(0) = 0), which contains it with codimension 1.
   Its basis Z keeps the coordinates |n| >= 2 free and solves for v_1 and
   v_{-1} (v_0 = 0). Z's entries involve pi and L = log(29/10), so Z is
   enclosed in arb balls, and In(Z^T (R + band I) Z) is computed by
   elimination in ball arithmetic with every pivot required to exclude 0, at
   256 bits and then at 512; otherwise the class count is reported as
   undecided. It is reported at the band and at the three multiples, beside
   the codimension bound n_-(R + band I) - 3 <= n_-(on V_4) <=
   n_-(R + band I) (min-max, checked by a test), and beside a float64 count
   on V_4 (QR of Z's midpoints, measured).
7. **What "holds" means.** On a build, the count holds when the two routes
   agree, n_0(R + band I) = 0, n_-(R + band I) equals the stored float count,
   and every counted eigenvalue's bracket ends at or below -band
   (lambda_k < hi <= -band). A counted negative **fails to stay below
   -band** when its bracket does not end there, or when the exact count is
   below the float count (the float-counted eigenvalues past the exact count
   are then listed). An exact count above the float count is also a failure
   and is reported as one.
8. **Grade, fixed now in the addendum's wording.** If the count holds on
   every build: *hardened on the stored matrices (exact inertia): the
   negative count of the stored R_S at c = 2.9 is 4, 10, 20 at N = 8, 16, 32
   (10 on the 160-mode N = 16 build, and 20, 20, 20, 21 on the refined
   N = 32 builds); this hardens the inertia of the stored matrices, not of
   the exact R_S, whose float64 assembly error (Delta_T) is still graded by
   the band, so as a statement about R_S of the construction it stays
   measured, weakest step Delta_T; the growth is evidence against bounded
   rank on this construction, not a refutation, since C4 fixes no bound.* If
   some fail, they are listed and the measured grade is kept. The V_4 count
   takes the same grade (ball arithmetic on the stored matrices, for the
   exact class at c = 29/10).
9. **The min-max argument** (ordinary argument, unreviewed; written now).
   Let A be Hermitian on a space of dimension n with k eigenvalues below 0,
   and E any operator of rank r with v^*(A + E)v >= 0 for every v. Then
   r >= k. Proof: the span W of the eigenvectors of A for its negative
   eigenvalues has dimension k, and v^*Av < 0 for every nonzero v in W;
   ker E has dimension n - r. If r < k, then dim W + dim ker E > n, so some
   nonzero v lies in both, and v^*(A + E)v = v^*Av < 0, a contradiction. The
   proof uses only that E vanishes on a subspace of codimension r, so E need
   not be Hermitian or semidefinite. Application: C4 asks for a remainder E
   with Q - T_S + E >= 0 as forms on the window's class, which the checker
   writes R_S + E >= 0. A remainder of rank r on the whole function space
   restricts to a form of rank at most r on span{U_n : |n| <= N}, and
   positivity restricts too. So if the construction's exact R_S' satisfies
   ||R_S' - R_S||_2 < |lambda_k| (lambda_k the k-th counted eigenvalue of
   the stored R_S, bracketed in clause 4; the band is below |lambda_k| on
   every counted eigenvalue exactly when the count holds), then by Weyl R_S'
   has at least k eigenvalues below 0, and any remainder absorbing R_S' on
   this construction has rank >= k there. **The proviso is not
   established:** Delta_T's band is a measured response that indicates and
   does not bound, which is why the composite stays measured. On V_4 the
   same argument gives rank >= the V_4 count, and the codimension bound
   gives at least k - 3 without the ball computation.

**Visible when this reading was written.** The stored float counts and
eigenvalues in `checker_ts_cells.json` (s7.3, s7.3a, s7.8): at N = 32 the
last pair counted runs from -1.24e-2 to -8.4e-3, and `min_gap_to_band` from
2.4e-4 (364 modes) to 5.6e-4; at N = 16 the last pair counted is -8.96e-3,
-7.80e-3 (120 modes) and -8.88e-3, -8.28e-3 (160 modes); at N = 8 the float
eigenvalues of s7.3. No exact inertia of a stored matrix had been computed,
and no symmetry defect of R had been looked at. The routes were timed on a
random 65 x 65 float64 matrix only (elimination 0.47 s, characteristic
polynomial 0.03 s), and group 1 of `test_checker_inertia.py` ran on planted
matrices (19 passed; the 9 reading tests skipped, no JSON).

**What ran.** `run_checker_inertia.py` (reading and test at 50a104e, output
at 4b20a89), locally, 115 s in all: 0.1 s at N = 8, 0.8 s per N = 16
build, 22 to 24 s per N = 32 build. R is bit-symmetric on every build
(symmetry defect 0), so the upper-mirror clause was vacuous. Every seed was
confirmed by the exact counts at the first try (two exact evaluations per
eigenvalue, each by both routes, no widening and no bisection step), so
every float64 eigenvalue of these matrices lies within 2^-41 = 4.5e-13 of
the exact one. Grade of each number below: exact inertia (hardened) on the
stored matrices; the V_4 counts by ball arithmetic, every pivot deciding at
256 bits.

**Outcome, by the pre-registered test.** Columns: the band (stored, clause
2); the stored float count; the exact n_- / n_0 / n_+ of R + band I;
lambda_1; lambda_k, the last counted eigenvalue (bracket midpoints; each
bracket is at most 2^-40 wide); the margin below -band of lambda_k (the
smallest margin of the build); how far lambda_{k+1} lies above -band; the
sensitivity row (n_- at 2x / 5x / 10x band); and n_- on V_4 at 1x / 2x /
5x / 10x band.

| N | build (nvec, S) | band | float count | exact n_- / n_0 / n_+ | lambda_1 | lambda_k | margin of lambda_k | lambda_{k+1} above -band by | 2x / 5x / 10x | V_4: 1x / 2x / 5x / 10x |
|---|---|---|---|---|---|---|---|---|---|---|
| 8 | (80, 1200) | 5.3176e-03 | 4 | 4 / 0 / 13 | -0.0965449044 | -1.084204e-02 | 5.524e-03 | 2.78e-03 | 4 / 2 / 1 | 3 / 2 / 1 / 1 |
| 16 | (120, 1600) | 5.8632e-03 | 10 | 10 / 0 / 23 | -0.1126794656 | -7.801699e-03 | 1.939e-03 | 4.21e-03 | 8 / 2 / 1 | 8 / 8 / 1 / 1 |
| 16 | (160, 1600) | 5.8632e-03 | 10 | 10 / 0 / 23 | -0.1133297846 | -8.284600e-03 | 2.421e-03 | 3.66e-03 | 8 / 2 / 1 | 8 / 8 / 1 / 1 |
| 32 | (200, 2400) | 8.1798e-03 | 20 | 20 / 0 / 45 | -0.1203077259 | -1.213552e-02 | 3.956e-03 | 4.74e-04 | 6 / 2 / 1 | 20 / 5 / 1 / 0 |
| 32 | (240, 2400) | 8.1798e-03 | 20 | 20 / 0 / 45 | -0.1202289997 | -1.083936e-02 | 2.660e-03 | 4.98e-04 | 6 / 2 / 1 | 20 / 6 / 1 / 0 |
| 32 | (280, 2266) | 8.1798e-03 | 20 | 20 / 0 / 45 | -0.1206366446 | -1.028480e-02 | 2.105e-03 | 5.14e-04 | 8 / 2 / 1 | 20 / 8 / 1 / 0 |
| 32 | (319, 2633) | 8.1798e-03 | 20 | 20 / 0 / 45 | -0.1206053421 | -8.735686e-03 | 5.559e-04 | 7.17e-04 | 2 / 2 / 1 | 20 / 2 / 1 / 0 |
| 32 | (364, 3060) | 8.1798e-03 | 21 | 21 / 0 / 44 | -0.1208816525 | -8.417989e-03 | 2.382e-04 | 1.54e-03 | 6 / 2 / 1 | 20 / 6 / 1 / 0 |

- **The count holds on all eight builds.** The two exact routes agree at
  every shift evaluated, no eigenvalue lies exactly at -band, the exact
  count equals the stored float count, and every counted eigenvalue lies
  strictly below -band. **No counted negative fails.** The smallest margins
  are 2.4e-4 (364 modes) and 5.6e-4 (319 modes), both N = 32 refined rows;
  on the delivered rows the smallest margins are 5.5e-3, 1.9e-3 and 4.0e-3
  at N = 8, 16, 32.
- **Grade, as fixed in clause 8.** Hardened on the stored matrices (exact
  inertia): the negative count of the stored R_S at c = 2.9 is 4, 10, 20 at
  N = 8, 16, 32 (10 on the 160-mode N = 16 build, and 20, 20, 20, 21 on the
  refined N = 32 builds); this hardens the inertia of the stored matrices,
  not of the exact R_S, whose float64 assembly error (Delta_T) is still
  graded by the band, so as a statement about R_S of the construction it
  stays measured, weakest step Delta_T; the growth is evidence against
  bounded rank on this construction, not a refutation, since C4 fixes no
  bound.
- **What the count is made of** (the sensitivity row, clause 5, not a
  criterion). At 2x band the counts are 4 (N = 8), 8 and 8 (N = 16), and 6,
  6, 8, 2, 6 on the five N = 32 builds; at 5x band 2 on every build, and at
  10x band 1. So the growth from N = 8 to 16 persists at 2x band (4 to 8),
  and **the growth from N = 16 to 32 does not**: 14 of the 20 negatives of
  the delivered N = 32 row lie between -2 band and -band (12 to 18 on the
  refined rows), and lambda_k sits at 1.48 band on the delivered row and at
  1.03 to 1.33 band on the refined ones. At 5x band what remains are the two
  deep negatives of s7.3 (about -0.1 and -0.045), and at 10x band the deeper
  one.
- **The C4 class V_4**: n_- is 3 at N = 8, 8 on both N = 16 builds and 20 on
  all five N = 32 builds (the 21st negative of the 364-mode build is not on
  V_4). Every count lies within the codimension bound (k - 3 to k) and
  agrees with the float64 count on V_4; on the delivered rows it lies within
  one of the float count on V_-0 of s7.3 (4, 9, 20), which contains V_4 with
  codimension 1. At 2x band
  it is 2, 8, 8 and 5, 6, 8, 2, 6; at 10x band 1 at N = 8 and 16 and 0 at
  N = 32, so on V_4 at N = 32 no eigenvalue lies below -10 band. Grade: ball
  arithmetic on the stored matrices, for the exact class at c = 29/10, with
  the class derivation of clause 6 (elementary, checked at dps 40).
- **The rank bound (clause 9 applied).** For the stored matrices themselves,
  the min-max argument gives exactly: any E with R_S + E >= 0 on
  span{U_n : |n| <= N} has rank at least 4, 10, 20 at N = 8, 16, 32, and at
  least 3, 8, 20 when the inequality is asked only on V_4. For the
  construction's R_S', rank >= k follows when ||R_S' - R_S||_2 < |lambda_k|:
  1.08e-2 at N = 8, 7.80e-3 at N = 16 and 1.21e-2 at N = 32 on the delivered
  rows (2.04, 1.33 and 1.48 band), 8.42e-3 on the 364-mode row. At an error
  of up to 2x band the same argument gives only 4, 8, 6, and at up to 5x band
  2 at every N. **Whether ||R_S' - R_S||_2 is below the band is not
  established**: Delta_T's band is a measured response that indicates and
  does not bound. This is the weakest step, and it is why the composite
  stays measured.

**Changed keys of `checker_ts_cells.json`: none.** The follow-up writes only
the new file `checker_inertia.json`; the snapshot and the cells JSON are
read. two_adic/'s `test_ta_checker_citations.py` pins nothing that moved.
