# RESULTS: checker/ (independent verification and kill-controls)

1. **T_S (S = {inf, 2}) has not reached the checker.** two_adic/'s `T_S_matrix` raises KernelUnavailable for zeta's data: its provider is unwired, and no folder exposes the `delta_T` it calls. So P1 to P5 on T_S and R_S = Q - T_S are **not run**; their 21 tests skip with that reason.
2. **What was run against routed code passes.** kernel/'s T_inf (af756a5) is Hermitian and PSD at all five c. Placing 2 off in two_adic/'s builder gives T_inf exactly. Connes-Consani Thm 6.11, transcribed to the basis, holds at c = 1.5 and 1.9 (N = 8, 16) with margins about 1e38 times the dps 40/60 drift; the least constant it needs, **kappa_star = 7.42 (N = 8), 9.51 (N = 16)** at c = 1.9, stays below their 16.99. Grade: measured at two precisions.
3. **Product-side remainder, independently measured: its negative index grows with N**, confirming cutoff/'s refutation of product-side C4. n_-(Q - T_inf) on the full space is **5, 7, 11** (c = 2.2), **7, 11, 19** (2.5) and **9, 15, 25** (2.9) at N = 8, 16, 32, with lambda_min tending to -sqrt2 log2 / 2 = -0.490. The checker's own atom block reproduces cutoff/'s shift-form counts (2, 3, 7 / 4, 8, 15 / 5, 11, 23). On S = {inf} (c < 2) the index is stable: 0 at c = 1.5, 2 at c = 1.9.
4. **Kill-controls:** 1 passes (exact gate, hardened by numerics' `us_check`); 2 passes (two_adic/ refuses W_a, and refuses Epstein fed the checker's own exact 2-tower, at s_3(2) = 6); 3 **not exercised at S = {inf, 2}** (Gamma_C framework limit; the argument checked independently, s5.4). **That missing positive control limits any T_S result to zeta alone** (s5.6). 4 not run (no T_S to lesion). kernel/'s milestone 2 numbers are reproduced (s5.5).
5. **Q** (phase 1): matches the CCM Galerkin matrix entrywise (one route, 5.5e-40 at dps 40), plus spot checks against `zeta.weil.weil_functional` on test functions (1e-18 to 4e-14). Q > 0 on every cell. ALIGNMENT s5 status: **unresolved** for C4 at S = {inf, 2} (T_S not delivered); product-side C4 **refuted** on these cells (with cutoff/).

Phase 1 of 2026-09-23, branch `teal-sea/weil-c4-s2`. Nothing here is a
claim about RH. Grades follow the `AGENTS.md` ladder. Every number above is
pinned by a test in this folder (`test_checker_q.py`, `test_checker_gate.py`,
`test_checker_rs.py`).

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
| P1 to P5 for T_S, R_S = Q - T_S | two_adic/ | **not run**: `T_S_matrix` raises KernelUnavailable. Its provider is unwired, and it needs `provider.delta_T(c, N, dps, alpha, parity)`, which kernel/ does not expose. |
| kill-control 1, (U-S) gate | checker/ | **pass** (s3) |
| kill-control 2, refusal of non-unitary data | two_adic/ | **pass**: W_a refused (\|alpha\| != 1); Epstein refused at \|s_3(2)\| = 6 > 2, using the checker's own tower |
| kill-control 3, Dedekind positive control | two_adic/ | **positive control not exercised**: FrameworkLimit for Gamma_C (s5.4) |
| kill-control 4, lesion (optional) | | **not run**: there is no T_S to build with the gate bypassed |

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
    PYTHONPATH=$PWD <venv>/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/checker \
        tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py   # 8.3 min with routed providers, shared laptop
