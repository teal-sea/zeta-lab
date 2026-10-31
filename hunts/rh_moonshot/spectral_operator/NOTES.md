# spectral_operator: the CCM zeta spectral triple, built, regularized and checked

**Hunt #150 (`rh_moonshot`), mechanism 5. Built 2026-10-26. Status: constructed, measured
and pushed to a located obstruction; not challenged yet; unreviewed by any person.**
Nothing here is a result until the case log in `hunts/README.md` says how this hunt ended.
Files: `spo_common.py` (the definition, the measurements, the comparison, in that order),
`spo_run.py` (the cells), `test_spectral_operator.py` (the pins), `data/` (every number
below), `RUNS.md`, this page.

Grades are the hunt's (`MISSION.md`, top): *measured*, *hardened*, *derived* with its review
status, *kernel-checked*; *cited* marks a statement read in a primary source at the stated
place. An inertia from Arb ball LDL^T with every pivot conclusive is ball-carried and is
graded hardened for the truncated matrix it is computed on. Nothing here is kernel-checked.
A composite claim takes the grade of its weakest step.

## 1. Target and the candidate

A self-adjoint operator whose spectrum is the set of ordinates of the nontrivial zeros.
The candidate is one published construction, taken as published: Connes, Consani and
Moscovici, "Zeta spectral triples", arXiv:2511.22755 (TeX source read, e-print SHA-256
`96c884864b0bc49da6e41fcd0b235fc970af3fe2c4e6a5276f191b0e81f3bf4a`), *cited* at:

- section 3.1 (Lemma "basicexpli"): the truncated Weil form T = QW_lambda^N on
  E_N = span{V_n : |n| <= N} is real symmetric with T_ii = a_i and T_ij = (b_i - b_j)/(i - j);
- section 3.2 (Lemma "basics", Lemma "key"): with D = diag(n), DT - TD = |beta><eta| -
  |eta><beta|, eta = sum V_j; if T >= 0 with Ker T = C xi, xi even, <xi | eta> = 1, then
  D' = D - |D xi><eta| induces a self-adjoint D'' on E_N / C xi for <f | g>_T, and
  Det(D'' - s) = Det(D - s) sum_j xi_j / (j - s);
- Theorem "finmain" (stated in the introduction): with eps_N the smallest eigenvalue,
  assumed simple with an even eigenvector, D'' is self-adjoint for the form
  QW^N - eps_N, and its spectrum is the zero set of the transform of xi, all real.

The positive intertwiner of the template is **W = T - eps_N**: W D' = D'^T W, so D' is
self-adjoint for W. Its positivity is not Weil's criterion: W >= 0 holds for every real
symmetric T, because eps_N is T's smallest eigenvalue. The abstract says the construction
"only involves the Euler products over the primes p <= x"; the paper's section "The missing
steps" leaves the convergence of the spectrum to the zeros as the open step.

## 2. Construction, traced to its data

Window [0, L], L = log c (CCM's lambda = sqrt(c), L = 2 log lambda). T is assembled in Arb
balls by `hunts/rogue_frontier/weil_trunc/enclosures.BallTruncation` (read-only): the
archimedean block (digamma at 1/4 + i omega/2, or 3/4 for DH, with a ball tail), the pole
block W02 (zeta only) and the prime block from Lambda(n), n <= c (DH: its own coefficients,
from the Dirichlet series). In the V_n basis the full matrix is `bt.entry(n, m)`, and it
splits into the even (N + 1) and odd (N) sectors used for the inertias. Then xi is the even
ground state (float-grade eigenvector refined at the assembly precision), xi_n = v_0,
v_|n| / sqrt 2 normalized by sum xi_n = 1, and D' = diag(n) - (n xi_n)(1, ..., 1). The
spectrum is in z = 2 pi s / L.

**Provenance, checked by hand and by test.** The functions in `spo_common.DEFINITION`
(`prec_for`, `sectors`, `full_matrix`, `ground`, `xi_full`, `operator`) and the code they
call (`BallTruncation`, `ccm_common.lowest_pairs`, `ccm_common.to_mp`) were read line by
line: they read c, N, the precision, the prime powers n <= c with their weights, the
digamma function and the pole, and nothing else. No zero, zero list, Riemann-Siegel or xi
phase, completed function or radical vector enters. `test_provenance_of_the_definition`
scans their source for those reads and `test_provenance_scan_catches_a_planted_import` shows
the scan flags a planted `mp.zetazero` call. The zeros enter only in the comparison section
(`zeta_ordinates`, `gram_points`, the DH zero list), after the spectrum is computed.
Provenance: clean.

## 3. Measurements

Per cell (`spo_run.py`): five Arb LDL^T inertias (even and odd sectors at shift 0, the even
sector at eps - rho and eps + rho, the odd one at eps + rho, rho half the gap to the next
eigenvalue from midpoint estimates); the eigenvalues of D' by `acb_mat.eig` at 500 bits; the
real zeros of F_xi as the second route; the table against the zeros; for zeta the Gram-point
control. The pattern (N+1, 0), (N, 1), (N, 0), all conclusive, places exactly one eigenvalue
of T below eps + rho, and it is even: T is even-simple, the hypothesis of Theorem "finmain".

| kind | (c, N) | eps_N | inertia of T at 0 (even; odd) | even-simple (hardened) | largest abs Im of the spectrum | eigenvalues vs F_xi zeros | zeros compared | residual at n = 1, 10, 30, 50, 100 | Gram control, median | time |
|---|---|---|---|---|---|---|---|---|---|---|
| zeta | (13, 50) | 2.95e-57 | (51, 0); (50, 0) | yes | 9.2e-103 | 33 = 33, 2.1e-26 | 33 | 4.3e-41, 4.5e-35, 2.7e-12, -, - | 0.97 | 37 s |
| zeta | (13, 100) | 3.72e-59 | (101, 0); (100, 0) | yes | 0 | 85 = 85, 2.1e-26 | 90 | 4.3e-41, 4.2e-37, 4.5e-15, 2.1e-3, - | 0.76 | 172 s |
| zeta | (60, 100) | 2.22e-167 | (101, 0); (100, 0) | yes | 1.6e-65 | 46 = 46, 2.0e-26 | 46 (to 138) | 4.3e-41, 2.2e-41, 1.3e-40 (all 46 within 4.6e-40) | 0.95 | 180 s |
| zeta | (13, 200) | 2.85e-59 | (201, 0); (200, 0) | yes | 0 | 92 = 92, 2.0e-26 | 100 | 4.3e-41, 3.3e-37, 3.6e-15, 1.8e-3, 0.22 | 0.73 | 890 s |
| DH | (13, 100) | 8.25e-11 | (101, 0); (100, 0) | yes | 0 | 48 = 48, 2.1e-26 | 64 on-line zeros to 120 | 1.4e-9, 0.12, 0.48, 0.068, - | - | 70 s |
| DH | (60, 100) | -0.9432 | (99, 2); (98, 2) | yes | 0 | 77 = 77, 2.1e-26 | 64 | 0.053, 0.042, 1.5e-4, 0.61, - | - | 93 s |
| DH | (13, 200) | 8.08e-11 | (201, 0); (200, 0) | yes | 0 | 48 = 48, 1.9e-26 | 64 | 1.3e-9, 0.12, 0.50, 0.040, - | - | 464 s |

The agreement of the two spectrum routes, 2e-26, is the bisection floor of the F_xi route.
The target zeta zeros carry 42 digits, which floors the residuals near 1e-41. "-" means the
zero is above the comparison range (0.9 omega_N). At (13, 200) the operator has 92
eigenvalues below 237 against 100 zeros, so above the 50th to 60th zero it does not track
them, not even in number (residual 1.8e-3 at n = 50, 0.43 at n = 60).

Readings:

- **The hypothesis holds for DH, and so does self-adjointness.** At c = 60, N = 100, DH's T
  has 2 negative directions in each sector (Weil positivity fails on E_N, hardened), its
  smallest eigenvalue eps_N = -0.9432 is simple and even (hardened), W = T - eps_N >= 0, and
  D'' is self-adjoint with real spectrum (largest imaginary part 0 at 500 bits). The same at
  c = 13, where T is positive. **Self-adjointness is arithmetic-free**: it holds for every real
  distribution whose truncated form is even-simple.
- **For zeta the spectrum is the zeros, far beyond the counting function.** At (13, 100) the
  residuals against the zeros are 4.3e-41 (n = 1), 4.2e-37 (n = 10), 3.8e-24 (n = 20),
  4.5e-15 (n = 30), 2.1e-7 (n = 40), 2.1e-3 (n = 50) and 0.49 (n = 60), against a Gram-point
  control (the counting function's prediction) whose median distance is 0.76. So the kill
  "eigenvalues that match only the counting function" does not apply. CCM report errors from
  2.5e-55 (first zero) to about 1e-3 (fiftieth) with primes up to 13; the 1e-3 at n = 50 is
  reproduced; the first-zero precision here is set by the band and by the 42-digit target.
  At (13, 200) the first 100 zeros are compared: the residual reaches 1.8e-3 at n = 50 and
  0.22 to 0.64 from n = 60 on; at (60, 100), with primes up to 60, all 46 zeros below 138
  are matched to within 4.6e-40. Enlarging the window, not the band, is what moves the
  accurate range up.
- **For DH the spectrum cannot be its zeros.** Being real, it carries no off-line pair: at
  (13, 100) it puts real eigenvalues 84.912 and 86.572 inside the on-line gap
  (83.109, 87.647) where DH's zeros are 85.699 +- 0.3085i, and at (60, 100) 83.187 and
  85.703; its residuals against DH's on-line zeros are 1.4e-9 for the first and 0.1 to 0.9
  from the tenth on.

## 4. The distinguishing step and the rival gate

Three links: (1) T even-simple; (2) D'' self-adjoint, spectrum real (CCM, from (1));
(3) the spectrum converges to the zeros as N, c -> infinity. Links (1) and (2) hold for DH on
the cells measured, (2) for every even-simple real distribution, so neither can distinguish
zeta from DH. The DH analogue must fail at (3), and it does, at the off-line pair: a real
spectrum cannot converge to 85.699 +- 0.3085i, and the measured DH spectrum puts real points
in the gap instead. The step where the Euler product would have to enter is (3), the
convergence, which is `ccm_arithmetic`'s step 2 in operator language (CCM Theorem "finmain"
(iii): the spectrum is the zero set of F_xi, the object `ccm_arithmetic` measures).

| rival | link (1) even-simple | link (2) self-adjoint | link (3) | grade |
|---|---|---|---|---|
| DH (no Euler product) | holds at (13, 100), (60, 100), (13, 200) | holds | fails at the off-line pair: real eigenvalues in the gap | hardened (1); measured (3) |
| Epstein (1,1,6) | not run | (follows from (1)) | not run | none |
| W_{1/4} | not run | (follows from (1)) | not run | none |
| zeta(s - delta) | not run | (follows from (1)) | not run | none |

The other three rivals were not run here; `ccm_arithmetic` measured their ground states,
which are this operator's input (Epstein (1,1,6) and W_{1/4} lose capture at c = 59/2 and
between 2 and 3), and by link (2) their operators would be self-adjoint wherever even-simple.

## 5. Known obstructions

- **Arithmetic-free self-adjointness (the kill "W_DH >= 0 by the same argument").**
  Triggered for the self-adjointness step: W_DH = T_DH - eps_N >= 0 by construction, and the
  measured DH operator is self-adjoint. As a source of RH this step is a reformulation: real
  spectrum is automatic, and all of RH's content sits in link (3).
- **Weil positivity is not used and not needed.** T itself (unshifted) is positive for zeta
  on every cell measured and not for DH at c = 60; positivity of T for every (c, N) would be
  Weil's criterion, but the operator does not use it.
- **docs/09 section 5.1.** Zero-importing: absent (section 2). Finite approximants: the
  operator is a finite approximant and the limit is the open step, as CCM say.
  Counting-function-only: excluded by the residuals.
- **Hilbert-Polya proper** needs one operator whose spectrum is all the zeros; here every
  (c, N) gives a different finite operator, and nothing is uniform in (c, N).

## 6. Tests run

`test_spectral_operator.py`: the provenance scan and its planted fault; Lemma "key" (ii),
W D' = D'^T W to 1e-60 relative for zeta and DH, broken by a wrong shift; the even-simple
inertia pattern at (13, 16) for zeta and DH and at (60, 64) for DH with T not positive; the
spectrum by two routes at (13, 16) with zeta's first three zeros; and every number from
`data/cell_*.json` quoted here.

## 7. Disposition (proposed by the builder; the challengers decide)

**Located obstruction, recorded as a reformulation for the self-adjointness step:** the
CCM operator's self-adjointness and real spectrum hold for DH exactly as for zeta
(hardened on the cells measured, and by CCM's lemma for every even-simple real
distribution), so they carry no arithmetic; the RH content is the convergence of the
spectrum, which is `ccm_arithmetic`'s step 2 and is *unresolved*. Provenance is clean, and
the zeta spectrum matches the zeros far beyond the counting function.

## 8. Furthest true statement, with its grade

On the cells (13, 50), (13, 100), (60, 100), (13, 200) for zeta and (13, 100), (60, 100),
(13, 200) for DH, the truncated Weil form is even-simple (**hardened**, Arb LDL^T), so the
CCM operator D'' is self-adjoint for W = T - eps_N (CCM, *cited*; Lemma "key" (ii) checked
numerically), and its spectrum, computed by two routes agreeing to 2e-26, matches zeta's
zeros (to within 4.6e-40 for all 46 zeros below 138 at (60, 100); to 1.8e-3 for the first 50 at
(13, 200), and not past the 60th there) (**measured**: float-grade eigenvector, target zeros at 42 digits), while
DH's real spectrum places eigenvalues inside the gap of its off-line pair (**measured**).
No novelty is claimed: the construction and its accuracy are CCM's, reproduced.

## 9. Next step

The open step is (3). Two cheap measurements would sharpen it: (a) the residual of the n-th
eigenvalue as a function of (c, N), to see whether the error at fixed n falls like the
compact error of `ccm_arithmetic` (kappa t^2 / (4 pi^2 c)) or faster; (b) run Epstein (1,1,6)
and W_{1/4} through the operator below and above their capture-loss windows, to see whether
the spectrum detaches from their zeros exactly where their ground states leave the radical
subspace.
