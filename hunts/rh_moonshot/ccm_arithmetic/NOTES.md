# ccm_arithmetic: CCM step 2, the convergence of the window ground state's transform to Xi

**Hunt #150 (`rh_moonshot`), mechanism 1. Built 2026-10-21, written up 2026-10-26 when the
owner resumed the hunt in place. Status: constructed and measured; not challenged yet;
unreviewed by any person.** Nothing here is a result until the case log in
`hunts/README.md` says how this hunt ended. Files: `ccm_common.py` (assembly, transform,
radical vectors), `measure.py` (the grid), `rigidity.py` (moving one prime atom),
`wa_threshold.py` and `wa_dial.py` (the W_a rival), `capture_m4.py` (the m = 4 capture bound), `summarize.py` (prints the
tables below from `data/`), `test_ccm_arithmetic.py` and `test_ccm_arithmetic_data.py` (the pins),
`data/` (every number below), `RUNS.md`, this page.

Grades are the hunt's (`MISSION.md`, top): *measured*, *hardened*, *derived* with its
review status, *kernel-checked*. Nothing here is kernel-checked. Eigenvectors are float
grade, refined by inverse iteration at 400 to 1600 bits; a Rayleigh quotient printed as a
ball is an Arb ball for that stated vector (an honest value of the form at that vector, so
a negative ball is a negative value of the form), but it does not bracket an eigenvalue
(that would need a Temple bound, not done). A sign of a truncated matrix read from Arb
`LDL^T` inertia with conclusive pivots is hardened. Everything else is measured. A
composite claim takes the grade of its weakest step.

## 1. Target

Connes, Consani and Moscovici (arXiv:2511.22755, section 8) and Connes (arXiv:2602.04022,
section 6) reduce RH to two steps about the truncated Weil quadratic form Q_c on the
window [0, L], L = log c (prime sum over n <= c):

1. for every c, the lowest eigenvalue of Q_c is simple and isolated with an even
   eigenfunction v_c;
2. the transforms F_{v_c}, suitably normalized, converge to Xi uniformly on compact sets
   (of a neighbourhood of the real axis that contains the critical strip's image
   |Im z| < 1/2).

Connes and van Suijlekom (arXiv:2511.23257, Prop. 4.1) prove that under step 1 F_{v_c} has
only real zeros, for any real distribution. Hurwitz's theorem then turns step 2 into RH.
This mechanism attacks step 2: measure how F_v approaches Xi as c grows, against the
rivals, and locate the arithmetic input that would make zeta's convergence provable.
Relation to RH: steps 1 and 2 for every c imply RH (with the cited Prop. 4.1 and
Hurwitz); neither step is proved here for any infinite family of c.

## 2. Construction

Even sector, basis e_0 = L^{-1/2}, e_k = sqrt(2/L) cos(2 pi k y / L), k <= N (band N),
nodes om_k = 2 pi k / L. The matrices are assembled in Arb balls by the validated routines
of `hunts/rogue_frontier/weil_trunc` (`enclosures.BallTruncation`) and
`hunts/weil_propagation/numerics` (`wp_common`): archimedean block, pole block, prime block.
The transform of a vector v is

    F_v(z) = 2 sin(zL/2) [ v_0/z + sum_k sqrt2 v_k z / (z^2 - om_k^2) ],

sqrt(L) times the Fourier transform of the centred window function, so F_v(om_j) =
L (-1)^j v_j / sqrt2. The comparison object is the **radical vector** r of a function X
with completed entire function Xi_X: r_0 = L^{-1/2} Xi_X(0), r_k = sqrt(2/L) (-1)^k
Xi_X(om_k), the Fourier coefficients of the L-periodisation of the kernel whose transform
is Xi_X. F_r interpolates sqrt(L) Xi_X at every node, so v near r means F_v near Xi_X on
the band. The **radical subspace** R_m = span(r^(0..m)), r^(j)_k = om_k^{2j} r_k, holds the
vectors whose transform is Xi_X times an even polynomial of degree <= 2m. The radical
vector is a diagnostic: it reads Xi_X values but never enters the form, which reads only
primes, the archimedean place and the pole.

New assembly here: W_a = zeta(s+a) zeta(s-a) (`wa_matrix`), two archimedean blocks with
digamma parameters 1/4 +- a/2, four pole vectors and the prime block of
Lambda(n)(n^a + n^-a); its general-parameter archimedean routine matches BallTruncation's
zeta (1/4) and DH (3/4) blocks entry by entry, and its pole routine matches W02
(`test_ccm_arithmetic.py`). At a = 0 its form equals 2 Q_zeta entry by entry to 3.9e-180
(`data/wa_dial.json`).

Measured per cell (c, N): the four lowest eigenpairs, the radical misfit 1 - cos^2(v_1, r),
the squared distance of v_1 from R_2 and R_4, the ratio profile
rho_j = (F_v1/Xi)(om_j) / (F_v1/Xi)(0) with the fit log rho = a2 om^2 + a4 om^4 on om <= 13,
sup |F/F(0) - Xi/Xi(0)| on [0, 30] (abs) and on Im z = 0.45 (relative), the real zeros of
F_v1 against Xi's below min(0.9 om_N, 100), Sturm counts (extra real zeros of F_vk on
[0, 40], k = 1..3) and the capture quantities at m = 2: mu = bottom of the form on
R_2-perp, eta = ||(1 - P_R) A P_R||, and the perturbation bound eta / (mu - lambda_1) on
dist(v_1, R_2).

## 3. Results for zeta (measured)

From `summarize.py zeta` (all 30 cells in `data/measure_zeta.json`; rows at N = 128 and
the N = 32 contrast):

| c | N | lambda_1 | lambda_2 | misfit r | dist^2 R_4 | kappa | sup abs err [0,30] | rel err Im 0.45 | zeros matched |
|---|---|---|---|---|---|---|---|---|---|
| 6 | 128 | 7.900e-23 | 1.350e-16 | 2.72e-03 | 9.24e-13 | 0.83 | 5.77e-02 | 2.34e+01 | 6/29 |
| 13 | 128 | 3.299e-59 | 1.292e-51 | 5.08e-04 | 5.16e-16 | 0.80 | 2.48e-02 | 3.11e+00 | 29/29 |
| 25 | 128 | 1.657e-120 | 4.851e-112 | 1.24e-04 | 3.99e-19 | 0.78 | 1.23e-02 | 1.03e+00 | 29/29 |
| 37 | 128 | 1.497e-156 | 3.869e-148 | 2.13e-05 | 2.04e-23 | 0.48 | 5.07e-03 | 3.42e-01 | 29/29 |
| 43 | 128 | 1.628e-168 | 3.434e-160 | 3.31e-06 | 1.23e-26 | 0.22 | 2.00e-03 | 1.21e-01 | 29/29 |
| 50 | 128 | 6.482e-180 | 1.267e-171 | 1.24e-06 | 6.79e-27 | -0.16 | 1.22e-03 | 7.27e-02 | 29/29 |
| 60 | 128 | 1.206e-192 | 2.311e-184 | 2.35e-05 | 2.63e-24 | -0.83 | 5.32e-03 | 2.74e-01 | 29/29 |
| 50 | 32 | 9.819e-78 | 5.999e-71 | 4.94e-03 | 1.39e-11 | -10.84 | 7.63e-02 | 9.96e-01 | 8/8 |
| 60 | 32 | 2.164e-80 | 8.043e-74 | 6.93e-03 | 8.23e-11 | -15.69 | 9.03e-02 | 9.99e-01 | 8/8 |

kappa = a2 4 pi^2 c (degree 1, conductor 1). Measured on every one of the 30 cells:

- lambda_1 > 0 (Rayleigh ball of the computed vector) and lambda_2 / lambda_1 >= 1.6e6;
- v_1 is radical times an even polynomial: dist^2(v_1, R_4) <= 8.3e-11, down to 6.8e-27;
- Sturm counts are [0, 1, 2]: v_k has k - 1 real zeros beyond Xi's on [0, 40];
- at every cell with N >= 64 and c >= 13, every zero of Xi below min(0.9 om_N, 100) is
  matched by a real zero of F_v1 to within 7.8e-16 (29 of 29 below 100 at N = 128).

**Convergence needs the band to grow with the window.** At fixed N the compact error falls
and then rises with c (N = 32: minimum 7.1e-3 at c = 19, back to 9.0e-2 at c = 60), and
kappa turns negative as c grows at fixed N. That is read here as the band edge
om_N = 2 pi N / log c no longer covering the heights Xi needs (inferred; the saturation
ratio was not tabulated separately). On saturated cells kappa sits near 0.8 (0.78 to 0.83 at N = 128 for
c <= 25), so on the band F_v1 / Xi behaves like exp(kappa t^2 / (4 pi^2 c)): an approach to
Xi at rate O(t^2 / c) on compacts, measured. The off-axis approach is weaker: the relative
error on Im z = 0.45 is at best 7.3e-2 (c = 50, N = 128).

**Capture by perturbation is vacuous.** The bound eta / (mu - lambda_1) on dist(v_1, R_2)
is at least 2.8e4 on every cell (7.4e133 at c = 60, N = 128), while the actual distance is
at most 6.6e-4: mu, the bottom of the form on R_2-perp, is itself exponentially small
(1.2e-169 at c = 60, N = 128) because lambda_2's eigenvector is also radical times a
polynomial (its Sturm count is 1), and the leakage eta is about 1e-35. A Davis-Kahan
argument at m = 2 proves nothing on this grid. At m = 4 (`capture_m4.py`, run 2026-10-26
with its prediction pre-registered in `RUNS.md`) it still proves nothing on the three
largest windows: the bound is 5.9e96, 1.1e108 and 5.4e120 at c = 43, 50, 60 (N = 128),
with mu up about 13 orders of magnitude from m = 2 and eta still about 1e-35.

## 4. The distinguishing step and the rivals

The chain has three links: (1) simplicity and evenness of the ground state, (2) capture of
v_c by the radical subspace with F_v -> Xi on compacts, (3) Hurwitz. Link (1)'s conclusion
(real zeros of F_v) holds for every real distribution by the cited Prop. 4.1, so it cannot
distinguish zeta from DH. Link (2) must fail for DH: its Xi has the zeros
85.699 +- 0.3085i, and a locally uniform limit of functions with only real zeros cannot
have them (Hurwitz). The step that uses the Euler product, if the chain works, is (2).

| function | Euler product | form at the windows measured | capture (misfit of v_1 against its own radical) | the ground-state transform |
|---|---|---|---|---|
| zeta | yes, unitary local roots | lambda_1 > 0 on all 30 cells, c <= 60 | captured on all 30 cells (misfit <= 6.9e-3) | matches Xi's zeros below 100 |
| DH | no | negative from c = 31 (N = 64: Rayleigh ball -3.8e-30; weil_propagation's hardened bracket is [30.617, 30.818]) | captured to c = 31 (misfit 1.1e-4 at N = 64 although lambda_1 < 0), lost by c = 33 (misfit 0.9999) | a real zero between 85.729 and 85.735 at every cell with c in [29, 33] and N in {64, 128} (two, 85.096 and 85.761, at c = 30, N = 64), inside the on-line gap (83.109, 87.647) where Xi_DH has only the off-line pair |
| Epstein (1,1,6), disc. -23 | no | negative from c = 59/2 (ball -1.9e-2, N = 64) | misfit 0.08 to 0.11 for c <= 29, 0.986 at c = 59/2 | not compared (no zero list) |
| Dedekind zeta of Q(sqrt -23) | yes, unitary | lambda_1 > 0 on all 26 cells, c <= 60 (3.4e-9 at c = 60) | captured on all 26 cells (misfit <= 0.04) | not compared |
| W_{1/4} | yes, local roots p^{+-1/4}, not unitary | negative at c = 19581/8192 = 2.39026 (N = 32) and 4893/2048 = 2.38916 (N = 64), positive truncation just below; Arb LDL^T conclusive, hardened for the negative side | misfit 0.19 at c = 2, 0.999 at c = 3 | not compared |
| zeta(s - delta) | not run | not run | not run | not run |

Readings, each measured:

- **The approach rate is not arithmetic.** DH's kappa below its crossing is 0.80 to 0.94
  (normalized with conductor 5, N = 128), Dedekind's 0.85 to 0.93 for c >= 25 (1.25 at
  c = 19) and Epstein's 0.73 to 1.01 for 19 <= c <= 29 (2.57 at c = 13), close to zeta's
  0.8. The kappa law is a shared lemma: a rival passes
  it, so it gives no verdict.
- **What separates the rivals is whether capture survives every window**, and on this
  grid capture is lost, in every rival, at the window where the form turns negative or
  just after it. Dedekind (Euler product, degree 2) stays captured to c = 60 where
  Epstein (1,1,6) (same discriminant, no Euler product) is lost from c = 59/2.
- **The unitarity dial** (`wa_dial.py`, N = 32, LDL^T conclusive): W_a's form is negative
  from c_a with c_a in (2.3887, 2.3906), (2.5449, 2.5469), (2.6914, 2.6934),
  (2.8711, 2.8730), (3.0137, 3.0156) for a = 1/4, 1/8, 1/16, 1/32, 1/64, about +0.15 per
  halving of a, and at a = 0 the form is 2 Q_zeta to 3.9e-180. A scalar Euler product with
  nonnegative coefficients is not enough; the distance of the local roots from the unit
  circle sets the first window that fails.
- **Rigidity** (`rigidity.py`, zeta, atom at log 2 moved by eps): positivity is lost at
  |eps| ~ lambda_1 / |d lambda_1 / dy| (4.2e-49 at c = 13, N = 32; 1.5e-103 at c = 31,
  N = 64), while capture (dist^2 to R_4 and the Sturm count) survives until eps reaches
  the gap scale (lambda_2 - lambda_1) / ||dA/dy|| (6.6e-45; 8.6e-99). Both are
  fine-tuned to the exact prime locations at a scale that shrinks exponentially in c: any
  input that proves capture has to read the prime powers exactly, not a statistic of them.
  (At c = 31 the LDL^T inertia was inconclusive for most rows; the signs there rest on
  Rayleigh balls.)

## 5. Known obstructions engaged

- **Weil's criterion.** Positivity of the Weil form on every window is equivalent to RH.
  Prop. 4.1 does not need positivity, but on this grid capture tracks positivity to
  within the gap scale (section 4), so a proof of link (2) for every c would, on this
  evidence, have to deliver all-window positivity up to an exponentially small slack:
  the target risks being an RH-equivalent restatement (kill condition 3) unless the
  input that proves it is a new estimate. No such input is proposed yet.
- **docs/09 section 5.1.** Finite approximants: the construction is a sequence of finite
  approximants and the limit is the whole content; no statement here is uniform in c.
  Zero-importing: absent from the form; the radical vector and the zero comparisons read
  Xi only as diagnostics.
- **Hurwitz needs the strip.** Locally uniform convergence is needed on a neighbourhood
  of |Im z| < 1/2; the measured relative error at Im z = 0.45 is 7.3e-2 at best, and its
  decay in c is not established.
- **Simplicity** is measured (lambda_2 / lambda_1 >= 1.6e6), not bracketed: no Temple
  bound was computed.
- **Perturbative capture fails at m = 2** on every cell, and at m = 4 on the three
  largest windows (section 3).

## 6. Tests run

`test_ccm_arithmetic.py` (the assembly pieces against weil_trunc, the radical vector as a
near-null vector with two planted faults that must break it, zeta's ground-state
structure at (13, 32), the kappa law at two cells, the DH, W_{1/4} and Dedekind versus
Epstein rival gates) and `test_ccm_arithmetic_data.py` (every number this page quotes from
`data/`, read back). Both run with `-n0` and write nothing into the tree. On 2026-10-26
three cells were recomputed with the current code (W_{1/4} at (3, 32), Dedekind at
(19, 64), zeta at (13, 32)) and every recorded field came back identical (`RUNS.md`).

## 7. Disposition (proposed by the builder; the challengers decide)

**Unresolved.** No step is refuted for zeta on the grid, and every rival tested loses
capture at a located window while zeta and the Dedekind zeta of Q(sqrt -23) keep it to
c = 60. But the distinguishing step co-locates with window positivity, the perturbative
route to capture is vacuous, and nothing here is uniform in c.

## 8. Furthest true statement, with its grade

On the grid c in {6, 9, 13, 19, 25, 31, 37, 43, 50, 60}, N in {32, 64, 128}, zeta's
even-sector truncated Weil form has a lowest eigenpair, simple by a factor >= 1.6e6, with a
positive Rayleigh ball, whose eigenvector lies within squared distance 8.3e-11 of Xi times
even polynomials of degree <= 8 and whose transform has real zeros at Xi's zeros below
100 to within 7.8e-16 at every cell with N >= 64 and c >= 13; and each of DH,
Epstein (1,1,6) and W_{1/4} loses this capture at a located window (between 31 and 33,
between 29 and 59/2, between 2 and 3) where its form takes a negative value. **Grade:
measured** (the negative values are ball-carried for stated vectors, W_{1/4}'s sign change
is hardened, and everything else is one float route). No novelty search was made; the
matching of ground-state zeros with zeta's zeros is the phenomenon CCM report, reproduced
here, and these numbers were not compared with their tables.

## 9. Next step

1. Done 2026-10-26: the capture bound at m = 4 on (43, 128), (50, 128), (60, 128) is
   vacuous, as pre-registered. A perturbative proof of capture would need a subspace
   whose complement has a gap above the leakage; R_m with m <= 4 does not give one, and
   the next attempt should bound the leakage eta directly rather than raise m.
2. A fine c-grid for DH on (30.6, 33) at N = 64: locate the loss of capture against the
   sign change and the gap scale, to decide whether capture is positivity or something
   strictly weaker.
3. Run the zeta(s - delta) rival and record whether it meets the construction's
   hypotheses (the functional equation the even sector uses).
4. Test the candidate arithmetic input, an Euler product with unitary local roots (the
   semilocal unitary decomposition U-S of `weil_propagation/theory/RESULTS.md` section
   7.1), directly on v_c: does U-S hold for zeta's and Dedekind's ground states and fail
   for W_a's at c_a?
