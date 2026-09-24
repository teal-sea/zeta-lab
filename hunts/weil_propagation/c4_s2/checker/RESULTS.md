# RESULTS: checker/ (independent verification and kill-controls)

1. **T_S reached the checker, and R_S = Q - T_S is measured on all nine cells; C4's prediction is not decided at this band** (two_adic/ 8dc8525, float64). The band per row is **5.3e-3 to 1.6e-2** (two_adic/'s probe, the checker's refinement and quadrature responses). That is above Q's lowest eigenvalues (1.9e-7 to 2.6e-4) and above T_S's own lowest (1.5e-3 to 3.5e-3), so T_S >= 0 is not decided at the band. Grade: measured.
2. **T_S removes depth, not count.** lambda_min goes from -0.30 to -0.49 (Q - T_inf) to **-0.026 / -0.039 / -0.097 to -0.12** (c = 2.2 / 2.5 / 2.9). But n_-(R_S) below -band on the full space is **4, 4, 3** (2.2), **4, 9, 20** (2.5) and **4, 10, 20** (2.9) at N = 8, 16, 32. At N = 32, 14 and 12 of the 20 live on |n| > N/2, where Delta_T is least resolved. C4's bounded-rank prediction (P5) is **not supported and not decided** at 2.5 and 2.9. Grade: measured, weakest step Delta_T; the N = 32 refinement was not run.
3. **The provider's convergence claim fails at N = 16.** two_adic/ lists (80, 1200) as converged there. 80 -> 120 modes moves T_S by **7.8e-2 / 4.5e-2 / 2.4e-2** (spectral norm), 90 to 96 percent of it at |n| >= 12. 120 -> 160 moves it by **1.6e-2 / 5.2e-3 / 3.7e-3**. The 240-mode N = 32 unit ran past the 10-minute limit and is a CI proposal (s7.6).
4. **Kill-controls:** 1 passes; 2 passes; 3 not exercised (Gamma_C framework limit). 4, the lesion, is **refused twice**: NonUnitaryLocalData at the gate, then NotImplementedError in `KernelProvider.delta_T` once the gate is bypassed. Below both guards (a formula never validated off |alpha| = 1), T_S has no eigenvalue below -band, and n_-(R) rises from 4 to 5 / 6 / 6 (s7.4).
5. **Q** (phase 1) is unchanged: it matches the CCM Galerkin matrix entrywise (5.5e-40 at dps 40) and `zeta.weil.weil_functional` spot checks (1e-18 to 4e-14), and Q > 0 on every cell. ALIGNMENT s5 status: **unresolved** for C4 at S = {inf, 2}; product-side C4 **refuted** on these cells (with cutoff/).

Phases 1 to 3 of 2026-09-23, branch `teal-sea/weil-c4-s2`. Nothing here is
a claim about RH. Grades follow the `AGENTS.md` ladder. Every number above is
pinned by a test in this folder (`test_checker_q.py`, `test_checker_gate.py`,
`test_checker_rs.py`, `test_checker_ts.py`).

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
    PYTHONPATH=$PWD <venv>/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/checker \
        tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # 2 min

At the phase 3 commits: 162 passed, 10 skipped (9 phase 1 tests that need dps 60 T_S at
N >= 16, 1 positive control), 3 strict xfail (phase 1 P3, s7.2). Once
two_adic/ commits a change to a file T_S imports, the snapshot no longer
matches: tests that serve T_S from it skip with that reason (by design), and
the pins of the JSON files keep holding for the recorded inputs.

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

- **Key:** a digest of the HEAD blobs of every file T_S imports or reads:
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

### 7.2 Responses of T_S (spectral norm of the difference, Weyl)

| c | quadrature, N = 16 | 80 -> 120, N = 16 | same, its N = 8 block | 120 -> 160, N = 16 | P3, delivered rows | P3, equal settings | dps 60 drift, N = 8 |
|---|---|---|---|---|---|---|---|
| 2.2 | 1.62e-03 | 7.83e-02 | 5.25e-03 | 1.59e-02 | 5.27e-03 | 0 | 0 |
| 2.5 | 1.77e-03 | 4.54e-02 | 5.40e-03 | 5.24e-03 | 5.45e-03 | 0 | 0 |
| 2.9 | 1.91e-03 | 2.40e-02 | 4.30e-03 | 3.69e-03 | 3.71e-03 | 0 | 0 |

- **80 modes are not converged at N = 16.** two_adic/'s INTERFACE lists
  (80, 1200) as converged there. 80 -> 120 moves T_S by up to 7.8e-2, 90 to
  96 percent of it at |n| >= 12, while the N = 8 block moves 4.3e-3 to
  5.4e-3. The response shrinks with c (larger L), as under-coverage of the
  Mellin band 2 pi N / L predicts. two_adic/'s own default rule
  nvec = 8N/L + 40 asks for 202 / 179 / 160 modes at N = 16 and 364 / 319 /
  280 at N = 32. The delivered rows (120 and 200) sit below it.
- **P3** holds exactly (defect 0) when N = 8 and N = 16 use the same
  settings. Across the delivered rows it fails at phase 1's 1e-30
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
(160, 1600). The N = 32 row's own refinement (240 modes) was launched and
killed at 16 min wall under the 10-minute rule, unfinished (s7.1). The
N = 16 response of the same cell is carried in parentheses as a stated
proxy. A refinement response indicates the truncation error; it does not
bound it. Eigenvalues: numpy on float64 R = Q - T_S, with Q rounded from
dps 40. Counts use -band. Eigenvalues with |lambda| <= band are undecided.

| c | N | row (nvec, S) | probe | refinement | band | T_S lowest | Q - T_inf: n_-, lowest |
|---|---|---|---|---|---|---|---|
| 2.2 | 8 | (80, 1200) | 3.75e-03 | 5.58e-03 | 5.58e-03 | 3.52e-03 | 4, -0.3038 |
| 2.2 | 16 | (120, 1600) | 5.85e-03 | 1.59e-02 | 1.59e-02 | 2.62e-03 | 6, -0.4647 |
| 2.2 | 32 | (200, 2400) | 8.16e-03 | (1.59e-02) | 1.59e-02 | 2.45e-03 | 10, -0.488 |
| 2.5 | 8 | (80, 1200) | 3.48e-03 | 5.55e-03 | 5.55e-03 | 2.81e-03 | 6, -0.4275 |
| 2.5 | 16 | (120, 1600) | 5.42e-03 | 5.24e-03 | 5.42e-03 | 1.93e-03 | 10, -0.4812 |
| 2.5 | 32 | (200, 2400) | 7.55e-03 | (5.24e-03) | 7.55e-03 | 1.76e-03 | 18, -0.4886 |
| 2.9 | 8 | (80, 1200) | 3.76e-03 | 5.32e-03 | 5.32e-03 | 2.55e-03 | 7, -0.4377 |
| 2.9 | 16 | (120, 1600) | 5.86e-03 | 3.69e-03 | 5.86e-03 | 1.67e-03 | 12, -0.4811 |
| 2.9 | 32 | (200, 2400) | 8.18e-03 | (3.69e-03) | 8.18e-03 | 1.50e-03 | 23, -0.4885 |

| c | N | full: n_- / undecided / n_+ | full: three lowest | V_-: n_- / undecided | V_-0: n_- / undecided | n_- on \|n\| > N/2 |
|---|---|---|---|---|---|---|
| 2.2 | 8 | 4 / 1 / 12 | -0.02691, -0.01452, -0.008617 | 4 / 0 | 3 / 0 | 2 |
| 2.2 | 16 | 4 / 19 / 10 | -0.02602, -0.01936, -0.01934 | 4 / 18 | 3 / 18 | 2 |
| 2.2 | 32 | 3 / 48 / 14 | -0.02569, -0.0176, -0.0173 | 3 / 47 | 3 / 46 | 2 |
| 2.5 | 8 | 4 / 3 / 10 | -0.04015, -0.02129, -0.01329 | 4 / 2 | 4 / 1 | 2 |
| 2.5 | 16 | 9 / 7 / 17 | -0.03914, -0.02481, -0.01788 | 9 / 6 | 9 / 5 | 4 |
| 2.5 | 32 | 20 / 25 / 20 | -0.039, -0.02579, -0.01829 | 20 / 24 | 20 / 23 | 14 |
| 2.9 | 8 | 4 / 2 / 11 | -0.09654, -0.0456, -0.01307 | 4 / 1 | 4 / 1 | 2 |
| 2.9 | 16 | 10 / 4 / 19 | -0.1127, -0.04522, -0.01806 | 10 / 3 | 9 / 3 | 5 |
| 2.9 | 32 | 20 / 20 / 25 | -0.1203, -0.0451, -0.01726 | 20 / 19 | 20 / 18 | 12 |

Undecided eigenvalues (all of them, per class, are in
`checker_ts_cells.json` under `undecided`):

| c | N | band | undecided on the full space (negative ones, then the range) |
|---|---|---|---|
| 2.2 | 8 | 5.58e-03 | -0.002301 |
| 2.2 | 16 | 1.59e-02 | 9 negative of 19, from -0.01564 to 0.01554 |
| 2.2 | 32 | 1.59e-02 | 26 negative of 48, from -0.01573 to 0.01401 |
| 2.5 | 8 | 5.55e-03 | -0.002722, -0.001354, 0.001348 |
| 2.5 | 16 | 5.42e-03 | 3 negative of 7, from -0.001489 to 0.004895 |
| 2.5 | 32 | 7.55e-03 | 13 negative of 25, from -0.005818 to 0.007314 |
| 2.9 | 8 | 5.32e-03 | -0.002539, -0.001979 |
| 2.9 | 16 | 5.86e-03 | 2 negative of 4, from -0.001655 to 0.004036 |
| 2.9 | 32 | 8.18e-03 | 10 negative of 20, from -0.007705 to 0.008137 |

What this measures:

- **T_S removes the depth of the product-side remainder.** Q - T_inf has
  lambda_min -0.30 to -0.49 and a negative count growing in N (4, 6, 10 /
  6, 10, 18 / 7, 12, 23 at this band). R_S has lambda_min -0.026 / -0.039 /
  -0.097 to -0.12.
- **It does not remove the count.** n_-(R_S) grows 4 -> 9 -> 20 at c = 2.5
  and 4 -> 10 -> 20 at c = 2.9. At c = 2.5, N = 32 it exceeds the product
  side (20 against 18). The same counts hold on V_- and V_-0, within one.
  At c = 2.2 the count is 4, 4, 3, but the band there is 1.6e-2 and 48
  eigenvalues are undecided at N = 32.
- **Where the growth lives.** At N = 32, 14 (2.5) and 12 (2.9) of the 20
  negatives have more than half their weight on |n| > N/2. That is where
  every refinement response concentrates. The rest (6 and 8) have most
  of their weight on |n| <= N/2 and grow too (2, 5, 6 and 2, 5, 8 over
  N = 8, 16, 32).
- **Two deep negatives at c = 2.9** (about -0.1 and -0.045, -0.07 and -0.038
  on V_-0) sit below -3.7e-2 on every class and every N, 4.5 times the
  largest band of the cell. A bounded count, measured.
- **Banded P4** (one threshold per cell, `band_cell` = the largest band of
  the cell): nondecreasing at 2.5 and 2.9. At 2.2 it runs 1, 4, 3 (one
  eigenvalue, -1.63e-2 at N = 16, against the threshold -1.59e-2). The
  delivered rows use different settings per N and are not nested, so
  interlacing does not apply to them. This was asserted before the data
  and failed at 2.2; it is pinned as measured.
- **T_S >= 0** is not decided at the band: its lowest eigenvalue (1.5e-3 to
  3.5e-3) is inside every band. No eigenvalue of T_S lies below -band.

**Grade of the whole: measured.** Q is measured at two precisions with an
oracle; T_S rests on Delta_T (measured, one route, float64). The band is an
indicator, not a bound, and at N = 32 it rests on a proxy. The weakest step
governs.

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
  measured grade on c = 2.5 and 2.9.
- **CI proposal (GitHub Actions, not local):** units (240, 2400, 32) and the
  default-rule rows at N = 32, all three cells per unit. Measured per-unit
  cost: (200, 2400, 32) 246.8 s. (240, 2400, 32) exceeded 9.2 CPU-min and
  did not finish, against a model estimate of 320 s, so the scaling model
  does not hold at Kmax 14. A CI job should time one unit first. Each unit
  checkpoints (`run_checker_ts.py --units`).
- **The positive control** needs 23 in S or the construction over
  K = Q(sqrt -23) (s5.4). Forge's ruling keeps S = {inf, 2}.
