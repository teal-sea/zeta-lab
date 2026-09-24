# RESULTS: checker/ (independent verification and kill-controls)

1. **Phase 1 built:** an independent Q on the shared basis, the property tests for T_S and R_S = Q - T_S (P1-P8, derived before reading kernel/ or two_adic/), and the exact (U-S) gate. **R_S is not measured yet:** T_S has not been routed, so the 36 provider tests skip with reason "NotRouted".
2. **Q is hardened entrywise** (three routes agree). It matches the CCM Galerkin matrix to 5.5e-40 at dps 40, N = 32, on all five c. Against `zeta.weil.weil_functional` it agrees to 1e-18 (sin^4 bump), 4e-14 (sin^2 bump) and 3.5e-16 (Fejer, b = L/2), set by that oracle's own quadrature.
3. **Q is positive on every cell (measured eigenvalues at dps 40 and 60, consistent with Zhu's theorem).** lambda_min at N = 32: **2.3258e-4** (c = 2.2), **1.046e-5** (2.5), **1.8681e-7** (2.9). It is nonincreasing in N, and dps 40 and 60 agree to better than 1e-20 relative.
4. **The (U-S) gate works as the mission requires (exact arithmetic, n <= 200; hardened, because it agrees entry for entry with numerics' `us_check`).** Epstein (1,1,6) is rejected from **n = 6** (composite atom, the first of 31) and **n = 8** (s_3(2) = 6); W_a from **n = 2**. zeta and Dedekind Q(sqrt -23) are accepted throughout. On c in [2, 3) the window alone cannot see Epstein's failure; the place-mode gate, which reads the whole 2-tower, can.
5. **Open:** phase 2 and 3 (T_S, R_S inertia, kill-controls 2 to 4) wait on routing. ALIGNMENT s5 status: **unresolved** (the construction under test has not been delivered to the checker yet).

Phase 1 of 2026-09-23, branch `teal-sea/weil-c4-s2`. Nothing here is a
claim about RH. Grades follow the `AGENTS.md` ladder. Every number above is
pinned by a test in this folder (`test_checker_q.py`, `test_checker_gate.py`).

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

## 5. Reproduction

    PYTHONPATH=$PWD <venv>/python hunts/weil_propagation/c4_s2/checker/run_checker_q.py   # ~3 min
    PYTHONPATH=$PWD <venv>/python -m pytest -q -n 2 hunts/weil_propagation/c4_s2/checker \
        tests/test_hunt_probe_discipline.py tests/test_docs_numbering.py                  # ~75 s
