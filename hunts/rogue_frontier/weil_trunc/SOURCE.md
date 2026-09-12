# SOURCE.md: what the primary sources actually say

Step-0 verification record, written before any implementation. All PDFs were
fetched 2026-08-17 and read; page/equation citations below are from those
copies (stored in the session scratchpad, not committed).

## 1. Verification of the survey's two claims

The survey handed to this study claimed:

> (a) arXiv:2605.20224 = "Connes-van Suijlekom, a Galerkin/truncation
> construction for the Weil quadratic form with an open convergence question
> posed by Connes around Feb 2026". (b) arXiv:2607.02828 = "July 2026 posting
> with claims about the archimedean tail order and a critical-line
> ground-state property, reporting first-zero errors like 2e-55 at cutoff
> c=13, N=100 and 1.5e-168 at c=67 (attributed to a 'Groskin')".

Verdict: **both arXiv IDs exist and are on-topic; the attributions are
partly scrambled.** Corrections:

- **arXiv:2605.20224** is *not* by Connes-van Suijlekom. It is Akiva
  Groskin, "High-Precision Approximation of Riemann Zeros via the Truncated
  Weil Form" (v1 May 2026, v4 of 2026-08-14), an independent implementation
  of the Connes-van Suijlekom Galerkin matrix. The numeric claims the survey
  attached to 2607.02828 (first-zero error ~2.005e-55 at c=13, N=100;
  ~1.478e-168 at c=67, N=100) are in *this* paper (its Tables 3 and 20),
  not in 2607.02828.
- **arXiv:2607.02828** is Groskin, "A finite Guinand-Weil dictionary and
  archimedean tail order for the truncated Weil quadratic form" (v1 July
  2026, v3 of 2026-08-14). The "archimedean tail order" claim does belong
  here (its Theorem 3.2 and Corollary 3.3).
- The "critical-line ground-state property" is stated in 2605.20224's
  abstract as a property inherited from the CvS/CCM theory (ground-state
  Fourier-Mellin zeros lie on the critical line for every finite cutoff),
  with the convergence of those zeros to the Riemann zeros as c grows open.
- The actual construction papers, cited by both Groskin postings, are:
  - **Connes, van Suijlekom**, "Quadratic forms, real zeros and echoes of
    the spectral action", Comm. Math. Phys. 406 (2025) 312,
    arXiv:2511.23257. Proposition 4.1 defines the divided-difference
    Galerkin matrix (fetched; 26 pp).
  - **Connes, Consani, Moscovici**, "Zeta spectral triples", EMS Lectures
    (2026), arXiv:2511.22755. Sections 3-5 define the Weil form assembly and
    the closed-form matrix entries used below (fetched; 34 pp).
  - **Connes**, "The Riemann Hypothesis: Past, present and a letter through
    time", arXiv:2602.04022 (Feb 2026). Its Section 6 poses the open
    convergence question and s6.4 carries the heuristic eigenvalue
    prediction that 2605.20224 tests at c=100.

So the survey conflated author (Groskin vs Connes-van Suijlekom), paper
(which posting carries which numbers), but pointed at real, current work.
The open question attributed to "Connes around Feb 2026" is real
(arXiv:2602.04022, s6).

## 2. The construction, exactly

Notation follows CCM arXiv:2511.22755 (= [CCM]) and Groskin arXiv:2607.02828
(= [G2]); Groskin arXiv:2605.20224 = [G1], CvS arXiv:2511.23257 = [CvS].

Fix a cutoff c > 1 (need not be prime), set L = log c, and a band N. The
form acts on the span of the orthonormal Fourier basis
U_n(y) = L^{-1/2} exp(2*pi*i*n*y/L) of L^2([0, L]), n in {-N, ..., N}
(equivalently V_n = kappa(U_n) on L^2([lambda^-1, lambda], du/u) with
lambda = sqrt(c), L = 2 log lambda; [CCM] Prop 3.2). Dimension 2N+1.

**Correlation kernel** ([CCM] Lemma 2.3): for y in [0, L],

- q_{nm}(y) = [sin(2*pi*m*y/L) - sin(2*pi*n*y/L)] / (pi*(n-m)),  n != m
- q_{nn}(y) = 2*(1 - y/L)*cos(2*pi*n*y/L)

**Assembly** ([CCM] eq. (3.10)-(3.11)): the truncated Weil form is the
(2N+1) x (2N+1) matrix

    Q(n,m) = W02(n,m) - WR(n,m) - Wp(n,m)

with the three blocks:

1. **Pole block** ([CCM] Lemma 4.1, eq. (4.2)):

       W02(n,m) = 32 L sinh^2(L/4) (L^2 - 16 pi^2 m n)
                  / ((L^2 + 16 pi^2 m^2)(L^2 + 16 pi^2 n^2)).

   [G2] Corollary 2.7 gives the identical matrix as the divided-difference
   matrix of the source psi_0 with beta = L/(4 pi),
   C_c = L (sqrt(c) + 1/sqrt(c) - 2) / (2 pi^2).

2. **Prime block** ([CCM] eq. (3.16), (4.3)):

       Wp(n,m) = sum_{prime powers k <= c} Lambda(k) k^{-1/2} q_{nm}(log k).

3. **Archimedean block** ([CCM] eq. (3.15) and (4.4); [CCM] Prop 4.2/4.3
   give closed forms): with rho(x) = e^{x/2} / (e^x - e^{-x}),

       WR(n,m) = (omega(0)/2) * [gamma_E + log(4 pi)]
                 - (omega(0)/2) * log((e^L + 1)/(e^L - 1))
                 + omega(0) * ctilde(L)
                 + int_0^L rho(x) (omega(x) - omega(0)) dx,

   where omega = q_{nm}, and ctilde(L) = int_0^L (e^{x/2} - 1)/(2 sinh x) dx.
   (Derived here directly from [CCM] (3.15); the printed [CCM] (4.4) drops
   the omega(0)*ctilde(L) term relative to (3.15), and the printed (4.14)
   double-counts a constant; both are display slips that cancel in their
   Prop 4.3 table, whose off-diagonal (alpha_L(m) - alpha_L(n))/(n - m) and
   diagonal 2 gamma_L(n) - 2 beta_L(n) agree with the (3.15)-derived form.
   Our implementation works from (3.15) and validates every entry against
   direct quadrature; see RESULTS.md.)

   Off-diagonal (omega(0) = 0): WR(n,m) = (S_m - S_n)/(pi (n - m)) with
   S_k = int_0^L sin(2 pi k x / L) rho(x) dx = pi alpha_L(k) in [CCM]
   (4.12). Diagonal (omega(0) = 2): reduces to elementary integrals of
   e^{-mu x} sin / cos / x cos with mu_j = 2(j + 1/4), plus digamma and
   trigamma values at 1/4 + i pi n / L; equivalent to [CCM] Prop 4.2's
   2F1 / Lerch-Phi forms (their z = e^{-2L} series and our geometric series
   are the same expansion).

**Divided-difference presentation** ([CvS] Prop 4.1; [G1] s2.2 eq. (3)-(4);
[G2] s2.1 eq. (1)-(3)): the same matrix is Q_psi with
(Q_psi)_{mn} = (psi(m) - psi(n))/(m - n), (Q_psi)_{nn} = psi'(n), summed
over the three sources

    psi_p^(c)(x) = -(1/pi) sum_{q = p^a <= c} Lambda(q) q^{-1/2}
                    sin(2 pi x (1 - log q / L)),
    psi_0(x)     = (1/pi) int_0^L 2 cosh(y/2) sin(2 pi x (1 - y/L)) dy,
    psi_{R,T}(x) = (1/(2 pi^2)) int_{-T}^{T} h_+(r) S(r, x, L) dr,
    S(r,x,L)     = int_0^L sin(2 pi x (1 - y/L)) cos(r y) dy,
    h_+(r)       = Re psi_Gamma(1/4 + i r/2) - log pi,

with Q_infty := Q_prime + Q_pole + Q_arch,infty (entrywise T-limit).
[G2] Lemma 2.1: Q_pole = W02 as matrices, Q_prime = -Wp, Q_arch,infty = -WR,
so Q_infty = Q. [G1] s2.3 shows the CCM Lemma 5.1 matrix tau_{ij} =
(b_i - b_j)/(i - j) coincides entrywise (b_n = psi(n)).

**Parity.** Under y -> L - y the form splits into an even sector (constant
mode plus (e_k + e_{-k})/sqrt(2), dimension N+1) and an odd sector
((e_k - e_{-k})/sqrt(2), dimension N); off-diagonal parity blocks vanish
identically ([G1] s3.4). The even-sector embedding is u_0 = v_0,
u_{+-k} = v_k / sqrt(2) ([G2] s2.1). Only the even sector carries the
ground state of interest ([CCM] Thm 1.1 hypotheses; [G1] Remark 2.1).

**Zero extraction** ([CCM] Thm 1.1(iii); [G1] s2.4, s3.5): the ground-state
eigenvector xi_N of the even sector defines the Fourier-Mellin transform
hat-xi_N(z) = int xi_N(u) u^{-iz} du/u; its real zeros approximate the
Riemann ordinates gamma_k. In the Fourier coordinates this is, up to a
nonvanishing phase and constant,

    F_v(z) = 2 sin(z L / 2) * sum_{k=-N}^{N} u_k / (z - 2 pi k / L),

an entire function, real and even for real z and real even u.

## 3. The precise claims to test

From [G1] (all at archimedean cutoff T = 800 unless said):

- (c, N) = (13, 100): lambda_min^even = 2.865e-59, |gamma_1 error| =
  2.005e-55 (Table 3 / Table 20; T = 400 gave 2.077e-59 and 1.455e-55,
  s4.4 Table 2). Published cluster at c = 13: Connes 2.6e-55, CCM
  intro 2.5e-55, CCM s6 (N = 120, 200 digits) 2.44e-55, [G1] 2.005e-55
  (Table 1); spread is a factor of 1.3.
- c-sweep at N = 100: |gamma_1 error| falls monotonically from 2.005e-55
  (c = 13) to 1.478e-168 (c = 67); fifteen cutoffs (Table 3).
- N-ladder at c = 13 (T = 400, dps 80): |gamma_1 err| = 3.355e-44 (N=30),
  4.22e-55 (N=60), 1.455e-55 (N=100) (Table 2). Saturation at
  k_eff ~ 45 modes.
- The fit |log10 lambda_min| ~ 13.24 c^0.634 (c <= 67, N = 100) is a
  finite-N artifact, falsified at c = 100, N = 200 by 49 orders (abstract,
  point (i)).
- Negative-sign eigenvalue blocks at finite T (c = 100, and L(s, chi_3) at
  c = 23, 29) are artifacts of the archimedean cutoff, absent as T grows
  (v4 notes; [G2] s3 is the theorem behind this).

From [G2]:

- Theorem 2.5 (finite dictionary): <v, Q_infty v> equals the Guinand-Weil
  zero-side sum of the induced band-limited test function g_v, exactly;
  worked example at (c, N) = (13, 4), pole-neutral
  v = (-0.0859452, 1.4749860, 0.7071068, 0, -2.1213203):
  <v, Q_infty v> = 0.049968414571096979730..., partial zero-side sums over
  the first 512 zeros converge with raw residual -4.7e-11 (Table 1).
- Figure 2 (c = 13, N = 4, even sector): finite-T lambda_min = -1.9e-2 at
  T = 11, -5.3e-7 at T = 14, -3.9e-10 at T = 18; cutoff-free limit
  lambda_min(Q_infty) = +9.7e-15.
- Lemma 2.1 numeric check: closed-form assembly vs source assembly agree to
  2.0e-10 at (c, N) = (29, 6) on a generic vector, 2.1e-15 at (13, 4).
- Theorem 3.2 / Corollary 3.3: for T2 > T1 > max(2 pi N / L, 7) the
  archimedean increment is positive definite (strictly totally positive),
  so lambda_j(Q_tot,T) increases strictly in T to lambda_j(Q_infty), with
  explicit budget B_T ~ (2N+1) rho (log(T/(2 pi)) + 1) / (pi^2 T),
  rho = 2 pi / L. Decision rule: finite-T lambda_j >= 0 settles cutoff-free
  positivity of lambda_j; lambda_j < -B_T settles negativity; the band
  [-B_T, 0) settles nothing.
- Their flagship deep-sign computation: at (c, N) = (100, 200) an interval
  LDL^T factorization of the cutoff-free matrix at 9000 bits returns
  n_minus = 0 (all 401 eigenvalues positive).

Open question this study does NOT touch: convergence of the ground-state
zeros as c -> infinity (Connes arXiv:2602.04022 s6; [G1] abstract). Nothing
here bears on RH (docs/08 discipline applies).

## 4. Davenport-Heilbronn portability (battery)

The assembly needs three inputs: (i) explicit-formula prime-side
coefficients, (ii) a pole term, (iii) the archimedean density h(r) from the
functional equation's Gamma factor. For the lab's DH function
(`zeta/epstein.py`): completed form F(s) = (pi/5)^{-(s+1)/2}
Gamma((s+1)/2) f(s), F(s) = F(1-s), f entire, coefficients period-5
(1, kappa, -kappa, -1, 0), kappa = (sqrt(10 - 2 sqrt 5) - 2)/(sqrt 5 - 1).
Hence: (i) Lambda_f(n) from the log-derivative recursion
Lambda_f(n) = a_n log n - sum_{d | n, 1 < d < n} Lambda_f(d) a_{n/d},
supported on ALL n >= 2 (no Euler product), still band-limited to n <= c;
(ii) no pole block (f entire); (iii) h_DH(r) = Re psi_Gamma(3/4 + i r/2)
- log(pi/5), i.e. the x-space kernel rho_1(x) = e^{-3x/2}/(1 - e^{-2x})
and constant -log(pi/5) + psi_Gamma(3/4) in place of rho and
-log(pi) + psi_Gamma(1/4). [G2] Lemma 2.3 (finite source calculus) admits
arbitrary finite signed measures, so the construction ports; the structural
differences (no pole block; prime block supported off prime powers) are
recorded as findings in RESULTS.md.
