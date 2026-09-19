# DH dictionary, constructive: the Davenport-Heilbronn Guinand-Weil explicit formula

Constructive derivation of the Guinand-Weil explicit formula for the
Davenport-Heilbronn function in repository normalization, with the exact
statement of what is proved, the finite-pairing bridge, and the complete proof
of the archimedean pairing (OBL-3 closed). Scope is DH only. No claim about zeta
or RH is made here. No novelty claim is made. Ordinary proof in this document is
distinct from enclosure-carrying computation and from kernel checking; each
statement carries its own grade label.

Grade labels used below: [ordinary proof] (proved line by line here),
[cited] (primary source with identifier), [measured] (float evidence),
[hardened] (enclosure-carrying evidence), [open] (not established).

## 0. Verdict and map

OBL-1 (Guinand-Weil explicit formula for DH): CLOSED as ordinary proof.
Theorem E in section 4 proves the formula for the test function g_v,
including completed-function normalization, entirety, functional equation,
multiplicities and symmetry, the admissible class, contour and
horizontal-segment estimates, limiting and zero-sum convergence, and the
gamma and arithmetic terms with all constants.

OBL-3 (Galerkin assembly pairing): CLOSED as ordinary proof.
The prime pairing is closed here (Lemma F, ordinary proof). The pole
pairing is vacuous (F is entire, proved in section 1). The archimedean
pairing is Lemma W, derived term by term and proved line by line in section 6
with exact off-diagonal and diagonal closed forms, explicit Fubini
domination, all constants, and the negative sign matching -WR.
Even-sector embedding into E = -WR - Wp completes the identity
<v, E v> = W_DH(g_v) (Theorem OBL-3, ordinary proof).

OBL-2 (Paley-Wiener support): proved by construction; restated with proof
in section 3.4. OBL-4, OBL-5, OBL-6 (zero enclosures, completeness, tail
majorant): untouched here, still open. They are not needed for the
existence corollary (section 5), which needs no zero coordinates at all.

Overall dictionary disposition: Two-track resolution:
- Track 1 (Qualitative Existence): GO / PROVED. OBL-1, OBL-2, and OBL-3 are CLOSED
  as ordinary proof. Corollary C (existence of an off-line zero for the
  Davenport-Heilbronn function) is an unconditional theorem from (H1) hardened,
  (H2) proved, and (H3) proved. No zero coordinates, completeness checks, or tail
  bounds are needed.
- Track 2 (Quantitative Attribution): INCONCLUSIVE / ATTEMPT_UNRESOLVED. Zero
  attribution coordinates (OBL-4, OBL-5, OBL-6) remain blocked by unhardened float
  zeros, unverified completeness, and lack of a valid DH counting majorant.
Repair 2026-09-18: Lemma 4.3 integrates (f'/f) with its true negative
sign and the Theorem E proof decomposes F'/F explicitly, per independent
adversarial review. Section 6 contains the complete ordinary proof of
Lemma W and Theorem OBL-3. Muse review repairs incorporated: Lemma 3.2
near-x bound split, Lemma K Lam-factor independence via Dirichlet
coefficients n=1,2, explicit Step 7 sum-integral domination, and
analytic/float/ball tier distinctions clarified.

## Conventions

Fourier transform on the line: ghat(xi) = int_R g(r) e^{-i r xi} dr.
The repo test-function normalization is g_repo = ghat / (2 pi), reconciled
in section 4.6. Log is the principal real log. psi = Gamma'/Gamma.
Zeros are counted with multiplicity m_rho >= 1 unless stated.

## 1. The DH function, its completion, and its functional equation

Let chi be the odd Dirichlet character mod 5 with chi(2) = i, and chibar
its conjugate. Both are primitive and nonprincipal. Put

    f(s) = c L(s, chi) + cbar L(s, chibar),   c = (1 - i kappa)/2,

with kappa in (0, 1) fixed in Lemma K below. [ordinary proof]

Lemma 1.1 (Dirichlet series, real coefficients). For Re(s) > 1,
f(s) = sum_{n>=1} a_n n^{-s} with a_n = 2 Re(c chi(n)), real and
periodic mod 5: (a_1..a_5) = (1, kappa, -kappa, -1, 0). The series
converges absolutely for Re(s) > 1 since |a_n| <= 1. [ordinary proof]
Proof. chi(1..4) = 1, i, -i, -1 (oddness gives chi(3) = chi(-2) = -i),
chi(5) = 0. Then a_1 = 2 Re(c) = 1; a_2 = 2 Re(c i) = kappa;
a_3 = 2 Re(-c i) = -kappa; a_4 = 2 Re(-c) = -1; a_5 = 0.
|a_n| <= 1 uses 0 < kappa < 1 (Lemma K). Absolute convergence for
sigma > 1 follows by comparison with zeta(sigma).

Lemma 1.2 (entirety). f is entire. [ordinary proof]
Proof. Write each L(s, chi) = 5^{-s} sum_{r=1}^5 chi(r) zeta_H(s, r/5)
with zeta_H the Hurwitz zeta. zeta_H has one simple pole, at s = 1,
residue 1, independent of r. The residue of L(., chi) at s = 1 is
5^{-1} sum_r chi(r) = 0 (chi nonprincipal), so each L is entire, and
f is a linear combination of entire functions. This matches the repo
construction (zeta/epstein.py dh_f; dh_minus_heat/RESULTS.md section 1
records the same cancellation).

Completed normalization (repo convention, THEOREM_FEASIBILITY.md 1.1):

    F(s) = (pi/5)^{-((s+1)/2)} Gamma((s+1)/2) f(s) =: G(s) f(s).

Lemma 1.3 (completed combination). F(s) = c Lam(s, chi) + cbar Lam(s, chibar)
where Lam(s, chi) = (5/pi)^{((s+1)/2)} Gamma((s+1)/2) L(s, chi) is the
completed primitive odd L-function. [ordinary proof]
Proof. Gamma((s+1)/2) L(s, chi) = (5/pi)^{-((s+1)/2)} Lam(s, chi), so the
(pi/5) and (5/pi) prefactors cancel exactly.

Lemma 1.4 (L-factor functional equations). With q = 5, a = 1 (odd),
tau(chi) = sum_{r mod 5} chi(r) e^{2 pi i r/5}, and
W(chi) = tau(chi)/(i sqrt(5)):
Lam(s, chi) = W(chi) Lam(1-s, chibar),
Lam(s, chibar) = W(chibar) Lam(1-s, chi),
W(chibar) = conj(W(chi)) = W(chi)^{-1}, |W(chi)| = 1. [cited: standard
primitive Dirichlet L functional equation; see the assembled DH case in
Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., section 10.25;
original: Davenport and Heilbronn, J. London Math. Soc. 11 (1936), 181-185.]

Lemma 1.5 (Gauss sum, exact). With A = sqrt(10 - 2 sqrt(5)) and
B = sqrt(10 + 2 sqrt(5)): tau(chi) = -A/2 + i B/2, and
W(chi) = (B + i A)/(2 sqrt(5)), |W(chi)| = 1. [ordinary proof]
Proof. zeta5 = e^{2 pi i/5}: zeta5 - zeta5^4 = 2 i sin(72 deg),
zeta5^2 - zeta5^3 = 2 i sin(144 deg). So
tau = zeta5 + i zeta5^2 - i zeta5^3 - zeta5^4
    = 2 i sin72 - 2 sin144 = -A/2 + i B/2,
using sin72 = B/4, sin144 = sin36 = A/4. |tau|^2 = (A^2+B^2)/4 = 5.
Divide by i sqrt(5): W = tau/(i sqrt(5)) = (B + i A)/(2 sqrt(5)).
Check: (B^2+A^2)/20 = 20/20 = 1.

Lemma K (kappa condition and closed form). F(s) = F(1-s) for all s iff
W(chi) = cbar/c = (1 + i kappa)/(1 - i kappa), i.e. iff
kappa = tan(phi/2) with W(chi) = e^{i phi}. This gives
kappa = A/(2 sqrt(5) + B) = (A - 2)/(sqrt(5) - 1)
      = (sqrt(10 - 2 sqrt(5)) - 2)/(sqrt(5) - 1),
in (0, 1). [ordinary proof]
Proof. From Lemmas 1.3 and 1.4:
F(1-s) = cbar W(chibar) Lam(s, chi) + c W(chi) Lam(s, chibar).
Equality with F(s) = c Lam(s, chi) + cbar Lam(s, chibar) for all s is:
(c - cbar W(chibar)) Lam(s, chi) + (cbar - c W(chi)) Lam(s, chibar) = 0.
Divide by the non-vanishing factor (pi/5)^{-((s+1)/2)} Gamma((s+1)/2) to get:
(c - cbar W(chibar)) L(s, chi) + (cbar - c W(chi)) L(s, chibar) = 0.
For Re(s) > 1, expand as a Dirichlet series sum_{n>=1} d_n n^{-s} = 0 with
d_n = (c - cbar W(chibar)) chi(n) + (cbar - c W(chi)) chibar(n).
By uniqueness of Dirichlet series, d_n = 0 for all n. Evaluating at n = 1
(chi(1) = chibar(1) = 1) and n = 2 (chi(2) = i, chibar(2) = -i) yields:
(c - cbar W(chibar)) + (cbar - c W(chi)) = 0,
i [(c - cbar W(chibar)) - (cbar - c W(chi))] = 0.
The 2x2 system is non-singular (determinant -2i != 0), so Lam(s, chi) and
Lam(s, chibar) are linearly independent, forcing c = cbar W(chibar) and
cbar = c W(chi). Since W(chibar) = W(chi)^{-1}, both conditions are equivalent
to W(chi) = cbar/c. Since cbar/c = (1+i kappa)/(1-i kappa) = e^{2 i arctan kappa},
kappa is forced to tan(phi/2) = sin(phi)/(1+cos(phi)) = A/(2 sqrt(5)+B).
The second equality is 2B = A(1+sqrt(5)), which holds: both sides are
positive and squares agree, 4(10+2 sqrt(5)) = (10-2 sqrt(5))(6+2 sqrt(5)).
Numerically kappa = 0.28407..., agreeing with KAPPA_REF in
zeta/epstein.py and the lab-derived value to 1e-41 (RESULTS.md Gate F)
[measured cross-check]. The closed form is the Titchmarsh section 10.25
value [cited].

Theorem FE. F is entire of order <= 1 and F(s) = F(1-s). [ordinary proof]
Entirety: Lemma 1.2 plus G analytic (Gamma has no zeros). Order: Lemma G
below. Functional equation: Lemmas 1.3, 1.4, K.

Lemma G (growth). F(s) << exp(C_0 |s| log(2+|s|)) (order <= 1), and
(G'/G)(s) = -(1/2) log(pi/5) + (1/2) psi((s+1)/2) = O(log|s|) for
Re(s) >= 2. [ordinary proof]
Proof. For sigma >= 2, |f| <= sum n^{-2} = pi^2/6, and Stirling bounds
log Gamma; FE plus Stirling extends the bound left of sigma = 2; the
log-derivative formula is direct differentiation of log G.

## 2. Zeros: location, symmetry, multiplicity, counting

Write Z(F) for the zero set of F with multiplicities m_rho.

Lemma 2.1 (domination; no zeros at Re(s) >= 2). For sigma >= 2,
|f(s)| >= 1 - sum_{n>=2} n^{-sigma} >= 2 - pi^2/6 > 0.355 > 0.
Hence F != 0 for sigma >= 2 (G never vanishes). [ordinary proof]
The repo pins the sharper sum 0.2666... (zeta/epstein.py); the crude
pi^2/6 - 1 < 1 suffices here.

Lemma 2.2 (strip confinement; clean boundary). Every zero of F lies in
the open strip -1 < sigma < 2, and F != 0 on both boundary lines.
[ordinary proof]
Proof. sigma >= 2: Lemma 2.1. sigma <= -1: FE reflects to sigma >= 2.
Line sigma = 2: Lemma 2.1. Line sigma = -1: F(-1+it) = F(2-it) != 0
by FE and Lemma 2.1. In particular F(-1) = F(2) != 0.

Lemma 2.3 (trivial points). f vanishes at s = -1, -3, -5, ... (G has
simple poles there and F = G f is entire). None of these is a zero of F
in [-1, 2]: s = -1 lies on the contour with F(-1) != 0 (so f has exactly
a simple zero at s = -1); the rest lie outside the rectangle. No
trivial-zero sum appears in Theorem E; the gamma contribution is carried
entirely by the archimedean integral. [ordinary proof]

Lemma 2.4 (symmetries; quadruples). (i) Schwarz: F(conj s) = conj F(s)
(real Dirichlet coefficients, G(conj s) = conj G(s)): rho in Z(F) iff
conj rho in Z(F), same multiplicity. (ii) FE: rho iff 1 - rho, same
multiplicity. Hence orbits {rho, conj rho, 1-rho, 1-conj rho},
degenerating on the line (pairs gamma <-> -gamma) and on the real axis.
[ordinary proof]

Lemma H0 (Hadamard product; counting). F has order <= 1 (Lemma G), so
genus <= 1: F(s) = s^m e^{a+bs} Prod_rho E(s/rho, 1) with
sum_rho m_rho |rho|^{-2} < infinity. Consequently, with s = 3 + it,
#{rho: |gamma - t| <= 1} << log(|t|+2), N(T) << T log T, and there is a
sequence T_k -> infinity with dist(T_k, ordinates) >> 1/log T_k.
[ordinary proof from the cited Hadamard factorization theorem for
finite-order entire functions, e.g. Titchmarsh, The Theory of Functions.]
Proof sketch. At s = 3 + it, Re(1/(s-rho)) >= 4/17 for |gamma-t| <= 1
(minimize u/(u^2+1) on u = 3-sigma in (1,4)); compare against
|F'/F(3+it)| << log|t| (Lemma D at sigma = 3 plus Lemma G) and absorb
the near 1/rho terms, which cost n_near/(|t|-1). Cover [-T, T] by O(T)
windows. Good T_k exist by pigeonhole since ordinates are isolated with
finite count in bounded sets.

Lemma H (horizontal bound). For the good sequence T_k,
(F'/F)(sigma +- i T_k) << log^2 T_k uniformly for sigma in [-1, 2].
[ordinary proof]
Proof. Differentiate the Hadamard product: near terms (<= O(log T_k) of
them) contribute <= 1/dist << log T_k each; far terms contribute
O(log T_k) by the standard estimate. The m/s term is bounded.

## 3. The admissible class and the test function g_v

Fix c > 1, L = log c, N >= 0. For real even-sector v = (v_0..v_N),
u_0 = v_0, u_{+-k} = v_k/sqrt(2), omega_k = 2 pi k/L, define

    F_v(z) = 2 sin(z L/2) sum_{k=-N}^{N} u_k/(z - omega_k),
    g_v(z) = F_v(z)^2 / L.

At the record cell (c, N) = (31, 60), v is the recorded exact dyadic
vector (dhneg_scan.json "confirm_cell", "rayleigh_vector_dyadic"); all
lemmas in this section hold for any real v. [ordinary proof]

Lemma 3.1 (F_v entire, even, real on R). The poles at z = omega_k and
z = 0 are removable: sin(zL/2) has simple zeros exactly at omega_k with
F_v(omega_j) = (-1)^j L u_j, and F_v(0) = L u_0. F_v(-z) = F_v(z) by
u_{-k} = u_k, and F_v is real on R. [ordinary proof]

Class A_L: even entire g with |g(x+iy)| <= C_g (1+|x|)^{-2} e^{L|y|}.

Lemma 3.2 (decay; g_v in A_L). g_v is even and entire, and for an
explicit C from v: |g_v(x+iy)| <= C (1+|x|)^{-2} e^{L|y|}. Hence
g_v in A_L. [ordinary proof]
Proof. Put R_N = max(2 omega_N, 1) >= 1. For |x| >= R_N, we have
|omega_k| <= omega_N <= R_N/2 <= |x|/2 for all k in {-N..N}, so
|z - omega_k| >= |x - omega_k| >= |x| - |omega_k| >= |x|/2.
Since |x| >= 1, |x|/2 >= (1+|x|)/4, so |sum u_k/(z - omega_k)| <= 4 sum |u_k| / (1+|x|).
With |sin(z L/2)| <= e^{|y| L/2}, squaring and dividing by L yields
|g_v(x+iy)| <= C_far (1+|x|)^{-2} e^{L|y|}.
For the near-x region |x| <= R_N, split into large-|y| and compact regions:
(i) If |y| >= 1, then for every k, |z - omega_k| = sqrt((x - omega_k)^2 + y^2) >= |y| >= 1.
Hence |sum u_k/(z - omega_k)| <= sum |u_k| / |y| <= sum |u_k| =: C_1.
Then |F_v(z)| <= 2 C_1 e^{|y| L/2}, giving |g_v(z)| <= (4 C_1^2 / L) e^{L|y|}.
Since |x| <= R_N, (1+|x|)^2 <= (1 + R_N)^2, which yields
|g_v(z)| <= C_{near,1} (1+|x|)^{-2} e^{L|y|} with C_{near,1} = (4 C_1^2 / L)(1 + R_N)^2.
(ii) If |y| <= 1, the domain K = [-R_N, R_N] x [-1, 1] is compact in C.
Since F_v is entire (removable singularities at omega_k, Lemma 3.1), g_v is continuous
on K, hence bounded by M = max_K |g_v(z)|. On K, (1+|x|)^{-2} >= (1 + R_N)^{-2}
and e^{L|y|} >= 1, so |g_v(z)| <= M (1 + R_N)^2 (1+|x|)^{-2} e^{L|y|}.
Taking C = max(C_far, C_{near,1}, M (1 + R_N)^2) yields the bound uniformly
on all of C. Evenness and entirety pass from F_v to its square.

Lemma P (positivity). For real r, g_v(r) = F_v(r)^2/L >= 0, and
g_v(conj z) = conj g_v(z). [ordinary proof]

Lemma 3.3 (basis expansion; algebraic). With q_{nm} the CCM Lemma 2.3
kernel and K_{nm}(r) = int_0^L q_{nm}(y) cos(r y) dy:
g_v(r) = sum_{m,n} u_m u_n K_{nm}(r) (finite sum). Each K_{nm} is even,
entire of exponential type L, and K_{nm}(x+iy) = O((1+|x|)^{-2})
uniformly in bounded strips, so each K_{nm} is in A_L. [ordinary proof;
the identity is the in-code g_even construction, gate record
PROVED_ANALYTIC.]
Proof of decay: q_{nm} is smooth on [0, L] with q_{nm}(L) = 0 in all
cases (diagonal: 2(1-1)cos = 0; off-diagonal: sin(2 pi k) = 0), so two
integrations by parts give O(x^{-2}); the y-integral over [0, L] gives
type L.

Lemma 3.4 = OBL-2 (Fourier support). ghat_v(xi) = int_R g_v(r) e^{-ir xi} dr
is supported in [-L, L]. [ordinary proof: proved by construction.]
Proof. By Lemma 3.3 it suffices to see it for each K_{nm}: K_{nm} is the
cosine transform of the compactly supported L^1 function q_{nm} 1_{[0,L]},
so its Fourier transform is the distribution pi(q_{nm}(xi)1_{(0,L]}(xi)
symmetrized), supported in [-L, L]. Finite sums preserve support.

## 4. Contour proof: Theorem E (OBL-1 closed)

Put Phi(s) = g_v((s-1/2)/i). Then Phi(1-s) = Phi(s) (evenness), and
Phi(sigma+it) = g_v(t - i(sigma-1/2)).

Rectangle Gamma_T: vertices A +- iT, 1-A +- iT with A = 2, T = T_k
from Lemma H0. Orientation positive.

Lemma 4.1 (residues). (1/2 pi i) oint Phi (F'/F) = sum_{inside} m_rho Phi(rho).
No poles of F'/F other than zeros occur (F entire), and F != 0 on the
contour: verticals by Lemma 2.2, horizontals by the good-T_k choice and
isolated zeros. [ordinary proof]

Lemma 4.2 (horizontals vanish). Top + Bottom -> 0 as k -> infinity.
[ordinary proof]
Proof. On s = sigma +- iT_k: |Re((s-1/2)/i)| = T_k, so Lemma 3.2 gives
|Phi| <= C T_k^{-2} e^{3L/2}; length 3; |F'/F| << log^2 T_k (Lemma H).
Product O(log^2 T_k / T_k^2) -> 0.

Lemma D (log-derivative Dirichlet series). For sigma >= 2,
-(f'/f)(s) = sum_{n>=2} Lambda_f(n) n^{-s} with absolute convergence,
where Lambda_f(1) = 0 and
Lambda_f(n) = a_n log n - sum_{d|n, 1<d<n} Lambda_f(d) a_{n/d}.
This is exactly the galerkin.dh_lambda_coeffs recursion. [ordinary proof]
Proof. E(s) = -sum_{n>=2} a_n n^{-s} satisfies |E| <= pi^2/6 - 1 < 1 for
sigma >= 2; 1/f = sum_{k>=0} E^k converges absolutely as a Dirichlet
series (k-fold convolution majorized by B(sigma)^k); multiply by
-f'(s) = sum a_n log n n^{-s} (absolutely convergent); compare
coefficients using a_1 = 1. Lambda_f is supported on all n >= 2 (no
Euler product).

Lemma 4.3 (right line, prime part). With mu = A - 1/2 = 3/2:
(1/2 pi i) int_{(A)} Phi(s) (f'/f)(s) ds
  = -(1/2 pi) sum_{2<=n<=c} Lambda_f(n) n^{-1/2} ghat_v(log n).
[ordinary proof]
Proof. By Lemma D, (f'/f)(s) = -sum_{n>=2} Lambda_f(n) n^{-s} with absolute
convergence, and Phi = O(t^{-2}), justifying termwise integration. Term n:
-(1/2 pi) Lambda_f(n) n^{-A} int_R g_v(t - i mu) e^{-it log n} dt. Shift
t -> t + i mu (g_v entire, O(t^{-2}) uniform in the strip, vertical sides
vanish): picks up e^{mu log n} = n^{3/2}; n^{-2} n^{3/2} = n^{-1/2}, giving
-(1/2 pi) Lambda_f(n) n^{-1/2} ghat_v(log n). Support (Lemma 3.4) cuts
n <= e^L = c.

Lemma 4.4 (right line, gamma part). (1/2 pi i) int_{(A)} Phi (G'/G) ds
= (1/4 pi) int_R g_v(r) [Re psi(3/4 + ir/2) - log(pi/5)] dr.
[ordinary proof]
Proof. (G'/G)(2+it) = (1/2)[psi(3/2+it/2) - log(pi/5)] (Lemma G), so the
line integral is (1/4 pi) int_R g_v(t-3i/2)[psi(3/2+it/2)-log(pi/5)] dt.
Shift t -> t + 3i/2: psi is analytic for 3/4 <= Re <= 3/2 (poles at
0,-1,...), g_v decay is uniform, sides vanish; psi(3/2+it/2) becomes
psi(3/4+it/2). The imaginary part of psi is odd in t and g_v is even
with |g_v Im psi| in L^1, so only Re psi survives.

Lemma 4.5 (left line equals right line). With downward orientation on
sigma = 1 - A absorbed, the left-line integral of Phi(F'/F) equals the
right-line integral. [ordinary proof]
Proof. Substitute s' = 1 - s: Phi(1-s') = Phi(s') (evenness),
(F'/F)(1-s') = -(F'/F)(s') (differentiate FE), ds = -ds'; the two minus
signs cancel and the path becomes the upward sigma = A line.

Lemma Z (zero-sum convergence). sum_rho m_rho |Phi(rho)| < infinity.
[ordinary proof]
Proof. (rho-1/2)/i = gamma - i(sigma-1/2) with |Im| <= 3/2 on the Lemma 2.2
strip; Lemma 3.2 gives |Phi(rho)| <= C(1+gamma^2)^{-1} e^{3L/2}; and
(1+gamma^2)^{-1} <= 4|rho|^{-2} there, with sum m_rho|rho|^{-2} < infinity
by Lemma H0. The rectangle exhausts Z(F) since all zeros lie in
-1 < sigma < 2 (Lemma 2.2).

Theorem E (DH Guinand-Weil formula for g_v). For every real even-sector v,
with L = log c:

  sum_{rho in Z(F)} m_rho g_v((rho-1/2)/i)
    = (1/2 pi) int_R g_v(r) [Re psi(3/4+ir/2) - log(pi/5)] dr
      - (1/pi) sum_{2<=n<=c} Lambda_f(n) n^{-1/2} ghat_v(log n).

Both sides converge absolutely. [ordinary proof: Lemmas 4.1-4.5, Z.]
Proof. (1/2 pi i) oint = R + L + horiz = 2R + o(1) (Lemmas 4.1, 4.2, 4.5);
R = (1/2 pi i) int_{(A)} Phi (F'/F) ds
  = (1/2 pi i) int_{(A)} Phi (G'/G) ds + (1/2 pi i) int_{(A)} Phi (f'/f) ds
  = gamma part + prime part (Lemmas 4.4, 4.3, times 2); residues exhaust
the zero sum (Lemma Z). The factor 2: left line equals right line.

Section 4.6 (repo normalization). With g_repo = ghat/(2 pi), the prime
term reads -2 sum_{n<=c} Lambda_f(n) n^{-1/2} g_repo(log n), matching the
zeta/weil.py convention (pole + arch + prime, no zeros used). The arch
density is h_DH(r) = Re psi(3/4+ir/2) - log(pi/5), matching
THEOREM_FEASIBILITY.md 1.4 and galerkin._hplus. No pole term: F entire.

Zero-side unpacking (explicit off-line treatment). On-line rho = 1/2+igas:
Phi = g_v(gamma) >= 0 (Lemma P); pairs +-gamma (gamma > 0) contribute
2 m_rho g_v(gamma); rho = 1/2 contributes m g_v(0). Off-line orbit with
beta > 1/2 member beta + i gamma (delta = beta - 1/2 > 0): by evenness
and Schwarz, rho and 1-rho contribute g_v(gamma - i delta), conj rho and
1-conj rho contribute g_v(gamma + i delta); total per orbit
m_orbit 2(g_v(gamma-i delta) + g_v(gamma+i delta))
  = m_orbit 4 Re g_v(gamma - i delta).
For the first DH pair (gamma approx 85.6993, delta approx 0.3085,
[measured] dhneg_scan.json; independent: Spira, Math. Comp. 63 (1994),
747-748 [cited]) the attribution factor 4 assumes simplicity m = 1
[measured: winding 1 in the zeta/epstein.py OFFLINE_ZERO derivation].
Theorem E itself carries m_rho and needs no simplicity input.

## 5. Existence corollary (Theorem 2 shape)

Corollary C. Assume (H1) <v, E v> < 0 for the recorded (31, 60) dyadic v
[hardened: Theorem 1, three routes]; (H2) <v, E v> = W_DH(g_v), the
arithmetic side of Theorem E [ordinary proof: Theorem OBL-3, section 6]; (H3)
Theorem E [ordinary proof: Theorem E, section 4]. Then F has an off-line
zero. [ordinary proof]
Proof. If all zeros of F were on the line, every zero-side term would be
m_rho g_v(gamma) >= 0 (Lemma P), so W_DH(g_v) >= 0, contradicting
<v,Ev> < 0 via (H2). No zero coordinates, no completeness input, no
multiplicity input are used. This establishes Track 1 (Qualitative Existence:
GO / PROVED) unconditionally, matching THEOREM_FEASIBILITY.md 6.2.

## 6. Finite pairing bridge: OBL-3 inputs and Lemma W

Apply W_DH linearly to the Lemma 3.3 expansion (finite sum, no analysis):
W_DH(g_v) = sum_{m,n} u_m u_n W_DH(K_{nm}).
Each K_{nm} is even, belongs to A_L, and by Lemma 3.4 has Fourier transform
Khat_{nm} compactly supported in [-L, L] (as the cosine transform of q_{nm} 1_{[0,L]}),
so all hypotheses of Theorem E are satisfied and Theorem E applies termwise.

Lemma F (prime pairing; proved). For all n, m:
-(1/pi) sum_{2<=k<=c} Lambda_f(k) k^{-1/2} Khat_{nm}(log k)
  = -Wp(n,m),
Wp(n,m) = sum_{k<=c} Lambda_f(k) k^{-1/2} q_{nm}(log k) (galerkin entry
formula). [ordinary proof]
Proof. Khat_{nm}(xi) = lim_{R->oo} int_{-R}^{R} K_{nm}(r) e^{-ir xi} dr
with K_{nm}(r) = int_{-L}^{L} qtilde(y) e^{iry} dy, qtilde the even
extension of q_{nm}/2. qtilde is of bounded variation (piecewise C^1,
continuous: q_{nm}(L) = 0, even at 0), so Dirichlet-Jordan gives
Khat_{nm}(xi) = 2 pi qtilde(xi) = pi q_{nm}(xi) at every continuity point,
including xi in (0, L) and the endpoint xi = L (log k = L only for k = c,
where q = 0 continuously). The -(1/pi) times pi q_{nm} gives -Wp exactly.
[Dirichlet-Jordan test: cited standard Fourier analysis, exact statement
as used here.]

Pole pairing: vacuous for DH. The zeta-only identity 2 g_v(i/2) = <v,W02 v>
(Gate B) has no DH analogue since F is entire. [ordinary proof]

Lemma W (archimedean pairing; proved). For a = 3/4 and all n, m in {-N, ..., N}:

    (1/2 pi) int_R K_{nm}(r) h_DH(r) dr = -WR_DH(n, m),

where h_DH(r) = Re psi(3/4 + ir/2) - log(pi/5) and -WR_DH(n, m) is the
exact Galerkin archimedean block:
- Off-diagonal (n != m): -(S_m - S_n) / (pi (n - m)) with S_{-k} = -S_k.
- Diagonal (n == m): const - D(|n|) + 2 tail, with const = psi(3/4) - log(pi/5).
The torus sums S_k, D(k), and tail are defined per galerkin._arch_sums.
The minus sign is proved by derivation. [ordinary proof]

Proof of Lemma W. The proof proceeds in seven steps.

Step 1: Archimedean kernel decomposition and x-space representation.
The archimedean density in repository normalization is
h_DH(r) = Re psi(a + ir/2) - log(pi/5) with a = 3/4.
Write h_DH(r) = const + [Re psi(a + ir/2) - psi(a)], where
const = psi(a) - log(pi/5).
From the Weierstrass partial-fraction expansion of the digamma function,
for any Re(z) > 0:
    psi(z) - psi(a) = sum_{j>=0} (1/(j + a) - 1/(j + z)).
Taking z = a + ir/2:
    Re psi(a + ir/2) - psi(a) = sum_{j>=0} ( 1/(j + a) - (j + a)/((j + a)^2 + r^2/4) )
                              = sum_{j>=0} ( 2/mu_j - 2 mu_j / (mu_j^2 + r^2) )
                              = 2 sum_{j>=0} r^2 / (mu_j (mu_j^2 + r^2)),
where mu_j = 2(j + a) = 2j + 3/2.
Using the elementary Laplace transform integral:
    2/mu_j - 2 mu_j / (mu_j^2 + r^2) = 2 int_0^infty e^{-mu_j y} (1 - cos(ry)) dy.
Summing over j >= 0: with rho_a(y) = sum_{j>=0} e^{-mu_j y} = e^{-2ay}/(1 - e^{-2y}),
the sum converges uniformly on every compact subset of (0, infty).
Since 1 - cos(ry) >= 0 and e^{-mu_j y} > 0, Tonelli's theorem gives:
    Re psi(a + ir/2) - psi(a) = 2 int_0^infty rho_a(y) (1 - cos(ry)) dy.
Thus the archimedean density splits into a constant and a singular integral:
    h_DH(r) = const + 2 int_0^infty rho_a(y) (1 - cos(ry)) dy.

Step 2: Fourier cosine transform of K_{nm}(r).
Recall from Lemma 3.3 that K_{nm}(r) = int_0^L q_{nm}(y) cos(ry) dy.
Let qtilde_{nm} be the even extension of q_{nm} to R, defined by
qtilde_{nm}(y) = q_{nm}(|y|) for |y| <= L and 0 for |y| > L.
Since q_{nm} is continuous on [0, L] and q_{nm}(L) = 0, qtilde_{nm} is
continuous on R and piecewise C^1, hence of bounded variation on R.
Writing K_{nm}(r) = (1/2) int_{-L}^L qtilde_{nm}(y) e^{iry} dy,
the Fourier inversion theorem (Dirichlet-Jordan test) gives:
    (1/2 pi) int_R K_{nm}(r) dr = (1/2) qtilde_{nm}(0) = q_{nm}(0)/2.
Since q_{nm}(0) = 2 delta_{nm} (q_{nn}(0) = 2(1 - 0) cos(0) = 2, while
q_{nm}(0) = (sin(0) - sin(0))/(pi(n - m)) = 0 for n != m), we have:
    (const / 2 pi) int_R K_{nm}(r) dr = const * delta_{nm}.
Similarly, for any fixed y > 0:
    (1/2 pi) int_R K_{nm}(r) cos(ry) dr = (1/2) qtilde_{nm}(y)
                                        = (1/2) q_{nm}(y) 1_{[0, L]}(y).
Subtracting this from the r-integral at y = 0:
    (1/2 pi) int_R K_{nm}(r) (1 - cos(ry)) dr = (1/2) [q_{nm}(0) - q_{nm}(y) 1_{[0, L]}(y)].

Step 3: Justification of integral interchange (Fubini and Dominated Convergence).
We justify:
    (1/2 pi) int_R K_{nm}(r) [ 2 int_0^infty rho_a(y) (1 - cos(ry)) dy ] dr
    = 2 int_0^infty rho_a(y) [ (1/2 pi) int_R K_{nm}(r) (1 - cos(ry)) dr ] dy.
We show that the double integrand F(r, y) = |K_{nm}(r)| rho_a(y) (1 - cos(ry))
belongs to L^1(R x (0, infty)).
(a) Decay of K_{nm}(r): By Lemma 3.3, q_{nm} is piecewise C^2 on [0, L] with
    q_{nm}(L) = 0. Integrating by parts twice:
    K_{nm}(r) = [q_{nm}(y) sin(ry)/r]_0^L - (1/r) int_0^L q'_{nm}(y) sin(ry) dy
              = [q'_{nm}(y) cos(ry)/r^2]_0^L - (1/r^2) int_0^L q''_{nm}(y) cos(ry) dy.
    Thus |K_{nm}(r)| <= C_K / (1 + r^2) for all r in R.
(b) Oscillation bound: 0 <= 1 - cos(ry) <= min(2, r^2 y^2 / 2).
(c) Integrating over r for fixed y:
    For y in (0, 1], split the integral at |r| = 1/y:
    int_{|r| <= 1/y} C_K (1 + r^2)^{-1} (r^2 y^2 / 2) dr <= (C_K y^2 / 2) (2/y) = C_K y.
    int_{|r| > 1/y} 2 C_K (1 + r^2)^{-1} dr <= 4 C_K int_{1/y}^infty r^{-2} dr = 4 C_K y.
    Hence int_R |K_{nm}(r)| (1 - cos(ry)) dr <= 5 C_K y for all y in (0, 1].
    For y >= 1, int_R |K_{nm}(r)| (1 - cos(ry)) dr <= 2 C_K int_R (1 + r^2)^{-1} dr = 2 pi C_K.
(d) Integrating against rho_a(y) over (0, infty):
    Near 0, rho_a(y) = e^{-2ay}/(1 - e^{-2y}) <= C_0 / y on (0, 1].
    The inner r-integral is bounded by 5 C_K y, so the product is <= 5 C_0 C_K,
    which is bounded and integrable on (0, 1]: int_0^1 (5 C_0 C_K) dy < infty.
    On [1, infty), rho_a(y) <= C_infty e^{-2ay} = C_infty e^{-3y/2}, which decays
    exponentially, and the inner r-integral is <= 2 pi C_K:
    int_1^infty 2 pi C_K C_infty e^{-3y/2} dy < infty.
Thus F(r, y) is in L^1(R x (0, infty)). Fubini's theorem applies unconditionally,
justifying the interchange.

Step 4: Evaluation of the pairing integral.
Applying the Fubini interchange and Step 2:
    (1/2 pi) int_R K_{nm}(r) h_DH(r) dr
    = const * delta_{nm} + 2 int_0^infty rho_a(y) [ (1/2 pi) int_R K_{nm}(r) (1 - cos(ry)) dr ] dy
    = const * delta_{nm} + int_0^L rho_a(y) [q_{nm}(0) - q_{nm}(y)] dy
      + q_{nm}(0) int_L^infty rho_a(y) dy.

Step 5: Off-diagonal evaluation (n != m).
For n != m, q_{nm}(0) = 0 and delta_{nm} = 0.
The constant term and the tail term vanish identically.
The formula reduces to:
    (1/2 pi) int_R K_{nm}(r) h_DH(r) dr = - int_0^L q_{nm}(y) rho_a(y) dy.
Substituting q_{nm}(y) = (sin(omega_m y) - sin(omega_n y)) / (pi (n - m)):
    - int_0^L q_{nm}(y) rho_a(y) dy
    = - (1 / (pi (n - m))) int_0^L [sin(omega_m y) - sin(omega_n y)] rho_a(y) dy
    = - (S_m - S_n) / (pi (n - m)),
where S_k = int_0^L sin(omega_k y) rho_a(y) dy.
This matches the off-diagonal entry of -WR in galerkin.py line 208 with the
mandatory minus sign.

Step 6: Diagonal evaluation (n == m).
For n == m, q_{nn}(0) = 2 and delta_{nn} = 1.
The pairing integral becomes:
    (1/2 pi) int_R K_{nn}(r) h_DH(r) dr
    = const + int_0^L rho_a(y) [2 - q_{nn}(y)] dy + 2 int_L^infty rho_a(y) dy.
Define tail = int_L^infty rho_a(y) dy = sum_{j>=0} int_L^infty e^{-mu_j y} dy
            = sum_{j>=0} e^{-mu_j L} / mu_j.
Define the diagonal difference integral:
    D(n) = int_0^L (q_{nn}(y) - 2) rho_a(y) dy.
Then int_0^L rho_a(y) [2 - q_{nn}(y)] dy = - D(n).
Substituting this into the pairing integral gives:
    (1/2 pi) int_R K_{nn}(r) h_DH(r) dr = const - D(n) + 2 tail.
In Step 7, we prove analytically that this integral D(n) evaluates to the closed form
2 sum_{j>=0} I_{cos1}(mu_j, omega_n) - (2/L) sum_{j>=0} I_{xcos}(mu_j, omega_n),
establishing the identity with self._archdiag[n] in galerkin.py line 173 as a proved
theorem rather than a definition.

Step 7: Partial-fraction closed forms, sum-integral domination, and exact identity.
We verify that S_k, D(k), and tail match the closed-form expressions:
(a) Expansion and domination of S_k: For k != 0, write
    S_k = int_0^L sin(omega_k y) (sum_{j>=0} e^{-mu_j y}) dy.
    On [0, L], |sin(omega_k y)| <= |omega_k| y. For each term j >= 0:
        int_0^L |sin(omega_k y)| e^{-mu_j y} dy <= |omega_k| int_0^infty y e^{-mu_j y} dy
                                                = |omega_k| / mu_j^2.
    Since mu_j = 2(j + a) = 2j + 3/2, the series sum_{j>=0} |omega_k| / mu_j^2 converges.
    Moreover, the majorant |omega_k| y rho_a(y) is continuous and bounded on [0, L]
    (since rho_a(y) = e^{-2ay}/(1 - e^{-2y}) <= C_0/y near 0), hence in L^1([0, L]).
    By Lebesgue dominated convergence, sum and integral interchange:
        S_k = sum_{j>=0} int_0^L e^{-mu_j y} sin(omega_k y) dy
            = sum_{j>=0} omega_k (1 - e^{-mu_j L}) / (mu_j^2 + omega_k^2).
    Summing the E-free part over j >= 0:
        sum_{j>=0} omega_k / (4(j + a)^2 + omega_k^2)
          = (1/2) sum_{j>=0} (omega_k/2) / ((j + a)^2 + (omega_k/2)^2)
          = (1/2) Im psi(a + i omega_k / 2).
    Subtracting the geometric remainder sum_{j>=0} e^{-mu_j L} omega_k / (mu_j^2 + omega_k^2)
    gives S[k] in line 120 of galerkin.py.
(b) Expansion and domination of D(n): With q_{nn}(y) = 2(1 - y/L) cos(omega_n y),
    q_{nn}(y) - 2 = 2(cos(omega_n y) - 1) - (2/L) y cos(omega_n y).
    Near y = 0, 2(cos(omega_n y) - 1) = O(y^2) and (2/L) y cos(omega_n y) = O(y), so
    |q_{nn}(y) - 2| <= C_D y on [0, L] for an explicit constant C_D.
    For each j >= 0:
        int_0^L |q_{nn}(y) - 2| e^{-mu_j y} dy <= C_D int_0^infty y e^{-mu_j y} dy = C_D / mu_j^2.
    Since sum_{j>=0} mu_j^{-2} < infty and the majorant C_D y rho_a(y) is bounded and integrable
    on [0, L], Lebesgue dominated convergence justifies the sum-integral interchange:
        D(n) = sum_{j>=0} int_0^L [2(cos(omega_n y) - 1) - (2/L) y cos(omega_n y)] e^{-mu_j y} dy
             = 2 sum_{j>=0} I_{cos1}(mu_j, omega_n) - (2/L) sum_{j>=0} I_{xcos}(mu_j, omega_n).
    Summing the building blocks over j >= 0 yields:
    - sum_{j>=0} I_{cos1} = -(1/2) [Re psi(a + i omega_n/2) - psi(a)] + geometric remainder.
    - sum_{j>=0} I_{xcos} = (1/4) Re psi'(a + i omega_n/2) - geometric remainder.
    Combining these gives D(n) = 2 sum_cos1 - (2/L) sum_xcos, proving the integral identity
    analytically and matching lines 124-132 of galerkin.py.
(c) The tail sum sum_{j>=0} e^{-mu_j L} / mu_j matches line 111.
Every term is derived without approximation, completing the proof of Lemma W. [ordinary proof]

Theorem OBL-3 (Assembly pairing identity; CLOSED). For any even-sector vector
v = (v_0, ..., v_N) and test function g_v:
    W_DH(g_v) = <v, E v>,
where E is the exact (N+1) x (N+1) even-sector Galerkin matrix E = -WR_DH - Wp_DH.
[ordinary proof]

Proof. By Lemma 3.3, g_v(r) = sum_{n, m=-N}^N u_n u_m K_{nm}(r).
By linearity of W_DH:
    W_DH(g_v) = sum_{n, m=-N}^N u_n u_m W_DH(K_{nm}).
For each pair (n, m), Theorem E decomposes W_DH(K_{nm}) into gamma, pole,
and prime parts:
    W_DH(K_{nm}) = (1/2 pi) int_R K_{nm}(r) h_DH(r) dr + 0
                   - (1/pi) sum_{2<=k<=c} Lambda_f(k) k^{-1/2} Khat_{nm}(log k).
By Lemma W, the archimedean term equals -WR_DH(n, m).
By Lemma F, the prime term equals -Wp_DH(n, m).
The pole term is 0 since F is entire.
Therefore:
    W_DH(K_{nm}) = -WR_DH(n, m) - Wp_DH(n, m) = Q_{DH}(n, m).
Hence:
    W_DH(g_v) = sum_{n=-N}^N sum_{m=-N}^N u_n u_m Q_{DH}(n, m).
Finally, by the even-sector basis change v_0 = u_0, v_k = sqrt(2) u_k (k >= 1),
and the symmetry Q_{DH}(n, m) = Q_{DH}(-n, -m) = Q_{DH}(m, n):
    sum_{n, m=-N}^N u_n u_m Q_{DH}(n, m)
    = u_0^2 Q(0, 0) + 2 sum_{k=1}^N u_0 u_k (2 Q(0, k))
      + sum_{j, k=1}^N 2 u_j u_k (Q(j, k) + Q(j, -k))
    = v_0^2 E_{00} + 2 sum_{k=1}^N v_0 v_k E_{0k} + sum_{j, k=1}^N v_j v_k E_{jk}
    = <v, E v>.
This completes the proof of Theorem OBL-3. [ordinary proof]

6.1 Discrepancy resolution. THEOREM_FEASIBILITY.md 1.4 wrote WR(n,m) = +(1/2 pi) int h K
with Q_DH = -WR - Wp. Under the G2 template that integral is Q_arch = -WR, so
1.4 had a sign slip in the WR naming. Lemma W proves that (1/2 pi) int h K is
identically -WR_DH, matching the code's added block and confirming Q_DH = -WR - Wp.

6.2 Measured shadow (not a proof). Gate H validates the DH diagonal constant
to ~1e-30 code-vs-code; replication Gates B-E validate the zeta assembly
including the pole identity (dev 2.1e-50) and the T-route limit. Lemma W
proves the underlying identity analytically.

6.3 Numerical diagnostic shadow. A preliminary floating-point quadrature
check of (1/2 pi) int K_00 h_DH against galerkin._archdiag[0] at c = 31
served as an unvalidated numerical diagnostic during investigation. Per
repository discipline, unvalidated floating-point quadratures carry no theorem
status; the ordinary proof of Lemma W in Steps 1-7 is strictly analytical
and does not depend on quadrature.

6.4 Computational and analytic tiers (float truncation versus analytic and ball exactness).
(1) Exact analytic matrix: Theorem OBL-3 is an exact mathematical equality on the
    analytic operator E = -WR_DH - Wp_DH, whose entries are given by the closed forms
    proved in Lemma W and Lemma F.
(2) Floating-point truncation: The class galerkin.Truncation computes E in mpmath
    floating-point arithmetic by truncating the infinite geometric tail sums at index
    J = ceil((dps + 12) log 10 / (2L)) + 3, leaving a truncation defect < 10^{-dps}.
    This is an accurate numerical realization, not an enclosure.
(3) Ball-arithmetic enclosures: For Hypothesis (H1) (<v, E v> < 0), the laboratory does
    not rely on floating-point truncation. Instead, enclosures.py computes rigorous
    interval and ball bounds on all matrix entries and validates negativity through three
    independent routes (LDL inertia, Rayleigh quotient upper endpoint, Rump eigenvalue
    enclosure; Theorem 1 [hardened]).
Thus the analytic pairing identity (H2, ordinary proof) is completely decoupled from
floating-point truncation, while the negativity verification (H1, hardened) is carried
by rigorous enclosures.

6.5 OBL-3 closure checklist. (i) Theorem E [proved]. (ii) Finite-linear
expansion [algebraic]. (iii) Prime pairing = -Wp [Lemma F, proved].
(iv) Pole vacuous [proved]. (v) Arch pairing = -WR [Lemma W, proved].
(vi) Even-sector restriction is exact linear algebra [Theorem OBL-3, proved].
(vii) Vector consistency: closed with the recorded dyadic vector.
OBL-3 is CLOSED as ordinary proof.

## 7. What is not claimed

OBL-4/5/6 are untouched: no zero enclosures, no completeness argument, no
DH counting majorant are constructed here. Consequently, Track 2 (quantitative
attribution) remains INCONCLUSIVE / ATTEMPT_UNRESOLVED. By contrast, Track 1
(qualitative existence) is GO / PROVED via Corollary C. No finite computation
here is presented as a uniform theorem. No statement about zeta or RH is made.
No novelty is claimed for Theorem E as a method (it is the textbook contour
argument in DH normalization); its value is pinning every constant the
dictionary needs.

## 8. Sources

Primary DH: Davenport-Heilbronn, J. London Math. Soc. 11 (1936), 181-185;
Titchmarsh 2nd ed. section 10.25 (DH construction, kappa, FE);
Spira, Math. Comp. 63 (1994), 747-748 (first off-line zero).
Method template: Davenport, Multiplicative Number Theory, Ch. 19
(explicit formula contour argument); Weil 1952 with 1972 refinement
(Guinand-Weil framework, as cited by zeta/weil.py).
Truncation: CCM arXiv:2511.22755 (3.10)-(3.16), Lemma 2.3, Prop 4.2/4.3;
CvS arXiv:2511.23257 Prop 4.1; Groskin arXiv:2605.20224;
Groskin arXiv:2607.02828 Thm 2.5, Lemma 2.1/2.3, Thm 3.2 (all via SOURCE.md).
Standard analysis (exact statements in-document): Hadamard factorization
(e.g. Titchmarsh, The Theory of Functions); Stirling psi bounds;
Dirichlet-Jordan test.
Local: zeta/epstein.py (dh_f, dh_coefficient, Z_dh, KAPPA_REF,
OFFLINE_ZERO_RE/IM); zeta/weil.py (pole/arch/prime convention);
hunts/rogue_frontier/weil_trunc/{galerkin,enclosures,dhneg_scan,
dhneg_confirm,dhneg_localize}.py, dhneg_scan.json, THEOREM_FEASIBILITY.md,
tail_bound.py, gate_checker.py, gate_31_60.json, test_gate_31_60.py,
SOURCE.md, RESULTS.md (read-only).

## 9. Frozen constants and information class

Frozen: contour A = 2 (strip (-1, 2)); mu = 3/2 shifts; cell (31, 60),
L = log 31; dyadic v; kappa closed form; a = 3/4; log(pi/5); T = 120 and
the 64-seed list belong to attribution only, not to Theorem E. Lemma W is
purely archimedean analysis (special functions plus one distribution
justification); it needs no zero data. Its information class is disjoint
from OBL-4/5/6, which is why the existence corollary can close before any
zero is enclosed.
