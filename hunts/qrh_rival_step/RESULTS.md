# RESULTS: where the quasi-Riemann argument spends its Euler product, and a rival that cannot pay

**Hunt #120, 2026-10-08.  Status: measured and read; nothing here is evidence
about the truth of the paper's theorem.**  Grades used: *cited* (a page of the
paper or a published theorem), *measured* (one float route), *hardened*
(independent routes agree, or balls carry the step), *ordinary argument* (a
derivation written here, unreviewed).  A composite claim takes the grade of its
weakest step.

The one-paragraph answer.  The OpenAI argument never consumes the Euler product
inside its continuation criterion (Proposition 2.1 of the 7/8 paper), which is
an abstract statement about the reciprocal of a function with two Mellin
estimates and survives, with trivial edits, for any function whose reciprocal
is bounded on Re s >= 2.  It consumes the Euler product where those two
estimates are manufactured: in the 11/12 paper at the one display that writes
1/L_K^S(s, nu) as the Dirichlet series of mu(n) nu(n) (Section 3, page 12),
which is what makes the object being bounded a twisted Moebius sum with
coefficients of modulus at most one, supported on squarefree ideals and
multiplicative apart from mu; and in the 7/8 paper at Lemma 7.1, the scalar
Euler identity (Section 7.2, page 53), which factors the Poisson-dual series
prime by prime into a quotient of Hecke L-functions times a local Euler product
H, and whose u = 1 case is the hypothesis (2.2) of Proposition 2.1 (page 71,
display (10.1) and (10.2)).  A finite linear combination of two nonproportional
Hecke L-functions has no such identity: its reciprocal's coefficients are
measured here to be non-multiplicative and unbounded.  The rival in the paper's
own vocabulary, zeta_Q(s) = zeta(s) L(s, chi_-15) + L(s, chi_-3) L(s, chi_5)
for Q = x^2 + xy + 4y^2, has zeros measured at 0.92746 + 15.49663i,
0.91294 + 47.53316i and 1.02597 + 61.42280i (twelve beyond 7/8 below height
300.5, two of them past 1), the third inside the paper's region of absolute
convergence, each a cancellation between two nonvanishing
products of Dirichlet L-functions.  The rival fails the distinguishing step and
is therefore not a counterexample (docs/08 section 4.3, second line); what it
shows is where a reviewer should look.

---

## 1. The claim and its object class

The 7/8 paper (OpenAI, 2026-09-30, 199 pages) states, Theorem 1.1 page 4:
every finite-order Hecke L-function over F = Q(sqrt(-3)) has no zero in
Re s > 7/8, and the same holds for every Dirichlet L-function including zeta.
The 11/12 paper (2026-10-05, 49 pages, "written with human assistance") proves
the same statement with 11/12 by the first of the two stages.  The transfer to
Dirichlet L-functions is quadratic base change: for a Dirichlet character chi,
L_F(s, chi o N) = L(s, chi) L(s, chi chi_-3) up to finitely many nonzero Euler
factors (11/12 paper page 12; 7/8 paper Proposition 11.3, page 84, display
(11.2)).  *Cited.*

The lab's rival class (`zeta/epstein.py`, `docs/08` section 4.1): the Epstein
zeta function zeta_Q(s) = sum over (m, k) != 0 of Q(m, k)^{-s} of a positive
definite binary quadratic form of class number h > 1.  It is (w/h) times a sum
over the class-group characters psi of L(s, psi) weighted by conj(psi(Q)), so a
finite linear combination of Hecke L-functions of the imaginary quadratic field
of discriminant D; it has the functional equation of a degree-two L-function of
conductor |D|, real coefficients (the representation numbers), no Euler
product, and infinitely many zeros in Re s > 1 (Davenport and Heilbronn 1936,
J. London Math. Soc. 11, part II; Titchmarsh section 10.25).  *Cited, not
re-derived.*  For D = -15 the two class-group characters are the trivial one
and the genus character, and the two Hecke L-functions are products of
Dirichlet L-functions:

    zeta_Q0(s) = zeta(s) L(s, chi_-15) + L(s, chi_-3) L(s, chi_5),   Q0 = x^2 + xy + 4y^2,
    zeta_Q1(s) = zeta(s) L(s, chi_-15) - L(s, chi_-3) L(s, chi_5),   Q1 = 2x^2 + xy + 2y^2.

*Hardened*: this identity (route C) agrees with the lab's lattice route (A)
and with the Fourier-Bessel expansion (B) to 1e-18 at twenty digits at the
points pinned in `test_rival_step.py`; the three routes share no code.  So the
rival is, in the paper's own words, a sum of two products of objects each of
which Theorem 1.1 declares zero-free in Re s > 7/8.

## 2. The distinguishing step, with citations

### 2.1 Proposition 2.1 is a shared lemma, not the step

7/8 paper, Section 2, page 8.  beta_* is defined in (2.1) as the supremum of
1/2 and the real parts of zeros in 1/2 <= Re s <= 1 of L_F(s, eta) over
primitive finite-order Hecke characters eta, with the sentence "Absolute
convergence of the Euler product excludes zeros in Re s > 1, so
1/2 <= beta_* <= 1."  A superscript S deletes finitely many Euler factors:
L_F^S(s, eta) = L_F(s, eta) prod_{p in S} (1 - eta(p) Np^{-s}).

Proposition 2.1 (Continuation from a common signal), page 8, hypotheses: for
every primitive finite-order Hecke character eta there are a finite set S, a
holomorphic H_eta on Re s > sigma_0 with sup |H_eta - 1| <= 1/2 (display 2.2),
and a function J_eta(Z) such that, with

    f_eta(Z) = (1 / 2 pi i) int_{Re s = 2} Z^{C(s)} e^{(s - 5/6)^2} H_eta(s) / L_F^S(s, eta) ds     (2.3),

one has |J_eta(Z)| << Z^{C(sigma_0) + omega} (2.4) and
|J_eta(Z) - f_eta(Z)| << Z^{C(beta_*) - sigma} (2.5), with omega, sigma > 0
independent of eta.  Conclusion: these contradict beta_* > sigma_0.

Its proof, page 9, touches the Euler product in exactly two sentences: "The
reciprocal Euler product is absolutely and uniformly bounded on Re s >= 2"
(to move the contour right for the small-Z bound) and "Both sides are
holomorphic on Re s > 1, so the identity theorem gives F_eta(s) =
e^{(s - 5/6)^2} H_eta(s) / L_F^S(s, eta) (Re s > 1)".  Everything else is
Mellin inversion, Fourier inversion on the line Re s = 2, and the definition of
beta_*.  *Cited.*

Read against the rival (*ordinary argument, with measured inputs*).  Put
F = zeta_Q0 for D = -15 and let beta_F be the supremum of the real parts of
its zeros.  (i) F/2 = 1 + sum_{n >= 4} (r(n)/2) n^{-s}, and the real series
takes the value zeta_Q0(2) = 2.68461677469 at s = 2 (measured, route B), so
|F(s)/2 - 1| <= 0.3423 on Re s >= 2 and 1/F is bounded there by 0.76; the same
triangle inequality gives F != 0 on Re s >= sigma_1 where zeta_Q0(sigma_1) = 4,
sigma_1 = 1.52709889569 (measured), so beta_F <= 1.5271.  (ii) 1/F is
holomorphic on Re s > beta_F.  With "Re s > 1" replaced by "Re s > beta_F" and
"L_F^S" by "F", every line of the proof of Proposition 2.1 goes through
unchanged: the Mellin transform F_eta converges on Re s > beta_F - epsilon_*,
the identity theorem applies on Re s > beta_F, and a zero with real part above
beta_F - epsilon_* contradicts the continuation.  So the proposition, as a
mechanism, does not distinguish a single Hecke L-function from a finite
combination.  As a *statement* it does not apply to the rival at all, because
its integrand is 1/L_F^S(s, eta) for one primitive character and the rival is
not one; that is a scope restriction, not a step the rival fails.  The kill
condition "Proposition 2.1 applies verbatim to a linear combination" therefore
does **not** fire, and the proposition is a shared lemma in the sense of
`docs/08` section 4.3.  The paper says the same thing in its own words: the
proposition "compares a normalized character sum with a Mellin integral
containing 1/L_F(s, eta)" (page 5), and the content lies in producing the two
estimates.

### 2.2 The 11/12 paper: the Moebius identity, Section 3, page 12

The object the whole analytic machine bounds is the nu-twisted Moebius sum,
Section 2.1, page 4:

    A_1(D) = sum_n mu(n) nu(n) W(N(n) / D),    target  A_1(D) << D^{1 - delta + epsilon}     (2.1),

introduced with the remark that "the implication from (2.1) to a zero-free
half-plane is the smoothed Hecke version of the classical relation between
Moebius sums and zero-free regions" due to Littlewood.  The implication is
carried out on page 12 (proof of Theorem 1.1 from Proposition 3.1), and the
display is the step:

    "Termwise integration for Re s > 1 gives
     M_W(s) = W^(s) sum_{(n, S) = 1} mu(n) nu(n) / N(n)^s = W^(s) / L_K^S(s, nu),
     where L_K^S is the Euler product outside S."

That identity, 1/L_K^S = sum mu nu N^{-s}, holds because L_K(s, nu) is an
Euler product with completely multiplicative coefficients, so the Dirichlet
inverse of nu is mu nu.  It is what makes the coefficients of the Mellin
signal (a) of modulus at most one, (b) supported on squarefree ideals, (c)
multiplicative apart from the sign mu.  Each of the three is consumed
downstream, and each consumption is a place a combination cannot enter:

- (2.2), page 4: the family A_u(D) = sum mu(n) nu(n) chi_n(u) W(N(n)/D) with
  the sextic symbol chi_n(u) = (u/n)_6 "extended multiplicatively"; the mean
  square over u (Proposition 3.1, page 11) is the whole of Sections 4 to 7.
- Page 5: "Following the work of Hasse and Heath-Brown, we derive the
  following identity in Appendix A.1, valid for squarefree primary n away from
  a fixed set of excluded primes: mu(n) gamma_{-1}(n) =
  chi_n(-1) G(n)^{-1} conj(alpha(n)) gamma_2(n)."  This converts "mu times a
  Gauss sum" into a cubic Gauss sum, hence a Fourier coefficient of Kubota's
  theta function (2.10).  It is an identity about mu on squarefree n; the
  Dirichlet inverse of a combination has no Gauss-sum expression.
- (2.17), page 8: "Each factor in (2.17) is completely multiplicative in b.
  ... Moebius inversion gives (2.18)", the removal of the cube factors.
- (7.3), page 30, the paired identity used in the second Poisson summation,
  a_xi(u_1) conj(a_xi(u_2)) gamma(chi_{u_1} conj(chi_{u_2})) =
  mu(u_1) mu(u_2) (xi G)(u_1 u_2^{-1}), and (7.4), page 31, where "the second
  Poisson summation turns the Moebius coefficients back into cubic Gauss-sum
  coefficients."

*Cited.*  For the rival the analogue of A_1(D) is sum_n b(n) W(n / D) with b
the Dirichlet inverse of r(n)/2.  Section 4 measures b.

### 2.3 The 7/8 paper: the scalar Euler identity, Section 7.2, Lemma 7.1, page 53

Page 50, Section 7: "We will factor each row into Hecke L-functions and a
holomorphic Euler product; the row u = 1 will contain the reciprocal of the
target function."  Page 51, Section 7.2: "Our objective is to prove that the
high series is a scalar Euler product for the target eta."  The coefficient
(7.4) carries the target as eta(A) with A = c n^3, a completely multiplicative
function of the completed index.  Page 53: "The coefficient in Equation (7.4)
has therefore separated into prime factors.  In absolute convergence, its
factor at p is the series (7.10)."  Lemma 7.1 (The complete local identity)
then states, display (7.13),

    F_{eta, u}(x, w, z) = zeta_F^S(6z) L^S(w, chi_•(u)) / L^S(x, eta conj(chi_•(u))) · H_{eta, u}(x, w, z),

with H a product of local factors (7.12) converging normally in the regions
(7.14) and (7.15), the latter being x_r >= 7/8, z_r >= 33/200, w_r >= 19/20,
and "for u = 1 in the second region, H_{eta, 1} = 1 + O(P_0^{-c_H})" (page 54).
Page 55: "For u = 1, Equation (7.13) contains 1/L^S(x, eta), and its numerator
has the two principal factors zeta_F^S(6z) and zeta_F^S(w).  Their residues will
produce the target Mellin signal."  Section 10.1, page 71, defines
H_eta(s) = H_{eta, 1}(s, 1, 1/6) (10.1) and fixes P_0 so that
sup_{Re s > 7/8} |H_eta(s) - 1| <= 1/2 (10.2), which is hypothesis (2.2) of
Proposition 2.1; the proof of Theorem 3.1 on page 85 says "Lemma 7.1 and
Equation (10.2) give the required holomorphic, nonzero H_eta on Re s > 11/12
for every primitive target."  *Cited.*

This is the step.  The series (7.3) separates into prime factors because every
arithmetic function in its coefficient, eta(A) among them, is multiplicative;
the local identity (7.11) is then a computation at one prime.  For a target
F = c_1 L(s, eta_1) + c_2 L(s, eta_2) with eta_1, eta_2 nonproportional, the
coefficient would carry c_1 eta_1(A) + c_2 eta_2(A), which is not
multiplicative in A, the series does not separate, and there is no local
identity to state; and what the principal row would then contain is not
1/F but a sum of two reciprocals 1/L^S(x, eta_1), 1/L^S(x, eta_2) with
different numerators, so the residue calculation of Section 10 would not
produce a scalar multiple of a Mellin integral of 1/F.  *Ordinary argument*,
stated at the level of the paper's own displays; it is where a reviewer
should look, and what they should check is that (7.13) is exact and H_{eta,1}
is holomorphic and within 1/2 of 1 on Re s > 7/8, since that single lemma is
the one place the arithmetic of a single character becomes the analytic input
of Proposition 2.1.

## 3. The measured rival

Instrument: `probe.py`.  Zeros are counted by the lab's argument-principle
routine `zeta.epstein.count_zeros_box` (forced subdivision plus adaptive
bisection, integer check at 1e-6) in windows of height 10, located by a
grid-seeded Newton iteration with deflation, polished separately on two
routes, and each located zero is checked by a winding count in a square of
side 0.1 on mpmath and, for D = -15, by a winding number on python-flint balls
in which every segment of the square is enclosed (the segment ball excludes
zero, so the argument moves by less than pi along it) and the increments come
from point balls (Section 3.3).  Every scan range is the scan's limit.

### 3.1 Discriminant -15, Q0 = x^2 + xy + 4y^2, class number 2

Box [0.8751, 1.6] x [0.5, 300.5] on route C at fifteen digits, located at
twenty.  The right edge is above sigma_1 = 1.5271, beyond which the triangle
inequality leaves no zero.  The real axis: zeta_Q0 is real there, negative on
[0.875, 1) (zeta is negative on (0, 1) and L(1, chi_-15) = 1.622 > 0 while the
genus product is 0.26 at 1), and positive on (1, 1.6]; the segment
0 < t < 0.5 was not scanned.

| window | located zero (route C, twenty digits) | Re s | mpmath winding |
|---|---|---|---|
| [10.5, 20.5] | 0.9274608807556767112 + 15.496634067901130613i | 0.927461 | 1 |
| [40.5, 50.5] | 0.9129364012498515931 + 47.533162611865967388i | 0.912936 | 1 |
| [60.5, 70.5] | 1.0259726162187534587 + 61.422798308789397105i | 1.025973 | 1 |
| [110.5, 120.5] | 0.8758727322992154756 + 110.77795340738078210i | 0.875873 | 1 |
| [130.5, 140.5] | 0.9265846323553476706 + 138.22488912340182573i | 0.926585 | 1 |
| [160.5, 170.5] | 0.9741991963234244458 + 170.19070397317808286i | 0.974199 | 1 |
| [180.5, 190.5] | 0.8802982435910100229 + 184.28429694618574729i | 0.880298 | 1 |
| [180.5, 190.5] | 0.8909421422270621602 + 187.66579052572042931i | 0.890942 | 1 |
| [200.5, 210.5] | 0.9070546356201938789 + 205.69694326558172698i | 0.907055 (relocated, RUNS.md) | 1 |
| [240.5, 250.5] | 1.0267748672021328832 + 246.99363615893182523i | 1.026775 | 1 |
| [290.5, 300.5] | 0.9103840133351492982 + 292.97956002825989272i | 0.910384 | 1 |
| [290.5, 300.5] | 0.9099701528937347036 + 296.36856104603011507i | 0.909970 | 1 |

**12 zeros** in the box below height 300.5, all twelve located inside their
windows with |f| below 7e-24 at twenty digits and mpmath winding 1 in a square
of side 0.1; **2 of them have Re s > 1** (heights 61.42 and 246.99); the
largest real part is **1.026775** at height 246.99; 20 of the 30 windows are
empty.  The top window [290.5, 300.5] recounted at half the forced
subdivision step gives the same 2 (and 0 above Re s = 1), the control against
contour aliasing.  Elapsed 1622 s on one core, plus 40 s for the one
relocation.  *Measured.*

The independent count in [1.0003, 1.6] x [0.5, 300.5], which shares the
routine but not the box, found **2** zeros, in the windows [60.5, 70.5] and
[240.5, 250.5], the same two windows as the located zeros with Re s > 1.  *Measured, two contour counts.*

### 3.2 Discriminant -23, Q0 = x^2 + xy + 6y^2, class number 3

Box [0.8751, 1.5] x [0.5, 60.5] on route B at fifteen digits (route B at
fifteen digits is reliable to height about 60, RUNS.md).  sigma_1 =
1.42171147228.  **1 zero**, in the window [10.5, 20.5], at
0.9532604747946606863 + 16.290215720390390793i (Re s = 0.953260), |f| = 8.5e-24
at twenty digits, mpmath winding 1; the other five windows are empty; 103 s.
*Measured*; confirmed on route A at the located zero (Section 3.3).

### 3.3 Hardening of the located zeros

D = -15, all twelve zeros (`results_confirm_d15.json`, 170 s in all).
Columns: the distance between the route C and route B polished roots (thirty
digits; route B on mpmath only below height 100), the residuals |f| on routes
C, B and A (with the digits used), the segment-enclosed ball winding on route
C with the number of segments it needed, the same on the square displaced by
0.15, the point winding on route B balls over 256 points with its largest
increment (below height 100), and the upper bounds of |f| from the route B
and route C point balls at the root rounded to twelve digits.

| height | C root minus B root | residual on C | residual on B (digits) | residual on A (digits) | ball winding on C (segments) | displaced | point winding on B balls (max increment) | ball values at the root, B and C |
|---|---|---|---|---|---|---|---|---|
| 15.4966 | 2.5e-41 | 3.3e-40 | 4.7e-42 (32) | 5.6e-42 (35) | 1 (128) | 0 | 1 (0.032) | 3.2e-12, 3.2e-12 |
| 47.5332 | 2.9e-40 | 2.4e-40 | 1.7e-41 (58) | 1.7e-41 (58) | 1 (128) | 0 | 1 (0.032) | 8.5e-11, 8.5e-11 |
| 61.4228 | 9.5e-41 | 7.4e-40 | 3.1e-41 (69) | 3.1e-41 (67) | 1 (128) | 0 | 1 (0.033) | 2.6e-11, 2.6e-11 |
| 110.7780 | not run | 2.7e-39 | not run | not run | 1 (128) | 0 | not run | 1.1e-09, 1.1e-09 |
| 138.2249 | not run | 2.2e-39 | not run | not run | 1 (128) | 0 | not run | 8.8e-10, 8.8e-10 |
| 170.1907 | not run | 5.5e-39 | not run | not run | 1 (128) | 0 | not run | 5.1e-10, 5.1e-10 |
| 184.2843 | not run | 1.1e-39 | not run | not run | 1 (256) | 0 | not run | 4.2e-10, 4.2e-10 |
| 187.6658 | not run | 4.9e-39 | not run | not run | 1 (128) | 0 | not run | 1.1e-09, 1.1e-09 |
| 205.6969 | not run | 1.2e-39 | not run | not run | 1 (128) | 0 | not run | 1.2e-09, 1.2e-09 |
| 246.9936 | not run | 8.3e-40 | not run | not run | 1 (128) | 0 | not run | 1.8e-10, 1.8e-10 |
| 292.9796 | not run | 7.7e-40 | not run | not run | 1 (256) | 0 | not run | 6.9e-10, 6.9e-10 |
| 296.3686 | not run | 1.0e-38 | not run | not run | 1 (128) | 0 | not run | 1.0e-10, 1.0e-10 |

At every zero the two ball routes overlap at the root, the mirror point
1 - conj(rho) has |f| below 2.2e-32 on route C, and the two constituent
products are equal in modulus and opposite in sign: |zeta L(chi_-15)| =
|L(chi_-3) L(chi_5)| runs from 0.626 (height 138) to 0.961 (height 296).  The
faulted route B reads 0.67 to 0.77 (scale 4) and 1.34 to 1.55 (sine) at the
three low zeros, and the function at rho + 10^{-3} reads 2.2e-3 to 3.8e-3 at
all twelve.  The ball point values at the root are bounded by the twelve-digit
rounding of the root, not by the arithmetic (radii below 6e-41 at up to 2626
bits).

D = -23, the zero at height 16.29.  Route B polish at 33 digits:
0.953260474794660686250509013566 + 16.2902157203903907929631726452i with
|f| = 3.6e-41; route A at the same point and 36 digits: |f| = 3.6e-41 (7 s);
the faulted route B reads 0.728 (scale 4) and 1.455 (sine) there and the
function at rho + 10^{-3} reads 3.9e-3; the point winding on route B balls at
386 bits is 1 over 256 points with largest increment 0.033; the point ball at
the root has |f| <= 3.8e-11 (root rounded to twelve digits) with radius 7e-45.
No segment-enclosed winding for this form (no ball route C).

Grades.  Each located zero is *hardened*: two evaluation routes sharing no
code agree on its position to at least 1e-25, the lattice route vanishes
there to the stated residual where it was run, the mpmath winding in a square
of side 0.1 is 1, and for D = -15 the segment-enclosed ball winding on route C
is 1 with a displaced square giving 0.  The ball winding is enclosure-carrying
only relative to Arb's correctness and to the identity that route C computes
zeta_Q0; that identity is itself *hardened* (three routes, 1e-18) and
classical, not kernel-checked, so the composite stays at *hardened*.  The
rival has twelve zeros beyond 7/8 below height 300.5, two of them beyond 1
(heights 61.4 and 247.0, real parts 1.02597 and 1.02677): **the rival is a
rival to the 7/8 conclusion and to the Re s > 1 region**, at the heights stated.

### 3.4 The Davenport-Heilbronn function, for the record

Box [0.8751, 2.0] x [0, 300] on `zeta.epstein.dh_f` (f != 0 for Re s >= 2 is
pinned by `tests/test_epstein.py`): **0** zeros in thirty windows (367 s).  The battery's
pinned zero has Re s = 0.80851718, below 7/8 by 0.0665.  The deepest pair in
the lab's census (`hunts/flow_repair`, height 240.4) re-polished here lands at
0.869530579640643 + 240.404672351441i with |f| = 2.3e-30 and winding 1,
below 7/8 by 0.0055.  So **no Davenport-Heilbronn zero known to this lab has
real part above 7/8**, and none exists below height 300 (*measured*).  Zeros
with real part up to the Bombieri-Ghosh supremum 1.12036 exist at some height
(cited from `hunts/lambda_dh_bounds/GATE.md`; Davenport and Heilbronn 1936
part I for Re s > 1), none located.  The Davenport-Heilbronn function is
therefore not a measured rival to 7/8 at any height the lab has reached; the
Epstein functions are, at height 15.

## 4. What the Moebius input becomes for the rival

The paper's twisted Moebius sum has coefficients mu(n) nu(n).  The rival's
Mellin signal would need the Dirichlet inverse b of a(n) = r_Q0(n)/2 (a(1) = 1
for the principal form), computed exactly by sieve to n = 10^6
(`probe.py inverse`, 2 s).

- b(1..12) = 1, 0, 0, -3, 0, -2, 0, 0, -1, -2, 0, 0.  b(4) = -3 while
  b(2)^2 = 0, and b(6) = -2 while b(2) b(3) = 0: **b is not multiplicative**
  (**460** of 3406 coprime pairs with mn <= 2000 fail), and it is
  supported on non-squarefree n.  *Measured, exact integers.*
- max_{n <= 10^6} |b(n)| = **39504** (at n = 734400), against 5136 below 10^5
  and a divisor function that never exceeds 240 below 10^6: **b is unbounded**.  The
  class-number-one control x^2 + xy + 5y^2 (D = -19), whose zeta_Q is
  2 zeta(s) L(s, chi_-19) and has an Euler product, gives an inverse that is
  multiplicative (0 failures of 3406) and bounded by the divisor function
  (maximum 16 below 10^5 against d(n) <= 128).  *Measured.*
- The partial sums B(x) = sum_{n <= x} b(n): since 1/zeta_Q0 has a pole at
  rho = 1.02597 + 61.4228i, the Dirichlet series sum b(n) n^{-s} has abscissa
  of convergence at least 1.02597, so B(x) is not O(x^theta) for any
  theta < 1.02597 (*ordinary argument*: a bound B(x) << x^theta would make the
  series converge, hence be holomorphic, on Re s > theta).  The paper's
  hypothesis (2.1) with delta = 1/12 asks for the Moebius-side sum to be
  O(D^{11/12 + epsilon}); the rival's analogue fails it by the amount of its
  zero, which is the Littlewood equivalence running backwards and is not an
  independent fact.  Measured over 10^3 <= x <= 10^6, the envelope of |B(x)|
  grows with exponent **0.886**, and the explicit-formula contribution
  2 Re sum x^rho / (rho F'(rho)) of the **16** located off-line zeros (six in
  the strip [0.55, 1.6] below height 60.5 and the twelve beyond 7/8 below
  300.5, two of them in both lists) has, over the top decade, an rms residual
  **0.50** of the rms of B(x)/sqrt(x) itself (25.3 before, 12.8 after).  Read that as *observed and inconclusive at this range*:
  the on-line and near-line zeros contribute at the x^{1/2} scale with a
  density that grows with height, and 0.0234 x^{0.927} (the amplitude of the
  first located zero) only clears that noise by a factor of ten beyond
  x ~ 10^8, outside what was computed.  The exponent statement above rests on
  the located zero, not on this fit.

## 5. Controls

- **Positive control.**  The same count-locate-wind pipeline on Riemann's zeta
  in [0.3, 0.9] x [10, 20] counts 1 and locates 1/2 + 14.134725141734694i
  (|Im - gamma_1| = 2.1e-16, Re = 1/2 to 1e-30); the ball winding at gamma_1 is
  1 with a ball of width 1e-73 (256 segments), and 0 on the square displaced by
  0.15.  *Measured.*
- **Planted faults.**  Route B with its factor 8 replaced by 4 differs from
  route A by at least 7.8e-7 at the four test points where the true routes
  agree to 9.6e-22; at the located zeros the faulted route B reads 0.67 (scale
  4) and 1.34 (sine for cosine) where the true one reads 1e-41; the function at
  rho + 10^{-3} is 2.8e-3, so the residual check is not satisfied by a nearby
  point; the displaced squares wind 0.  *Measured.*
- **Perturbed form.**  The class-number-one form (1, 1, 5) in the same box
  [0.8751, 1.6] x [0.5, 60.5] with the same detector counts **0**
  zeros in six windows.  *Measured*; consistent with GRH for L(s, chi_-19) at these heights,
  which is not claimed here.
- **Cross-backend.**  At each located zero the route B point ball on
  python-flint has |f| <= 4e-12 (the root rounded to twelve digits) with
  radius 1e-40, and for D = -15 overlaps the route C point ball; the point
  winding on route B balls is 1 with every increment below 0.04 (D = -15) and
  0.033 (D = -23).  *Measured on the second backend.*
- **Precision response.**  Route B at fifteen and thirty digits agree to
  1e-19 at height 50 and disagree by 0.04 at height 100 (RUNS.md); the census
  of Section 3.1 therefore runs on route C, which agrees with route B at thirty
  digits to 1e-20 at height 50 and with route A to 1e-22 where route A was run.
  The located zeros move by less than 1e-25 between twenty and thirty digits.

## 6. What this shows, and what it does not

**Shows.**  (1) The Euler product of the target enters the argument at
Lemma 7.1 of the 7/8 paper (page 53, used at (10.1) and (10.2), page 71) and at
the Moebius identity on page 12 of the 11/12 paper, not inside the
continuation criterion Proposition 2.1, which is a shared lemma.  (2) An object
with the functional equation, real coefficients and the same L-function
building blocks, but without an Euler product, has measured zeros at real
parts 0.9275, 0.9129 and 1.0260 below height 62 for D = -15 (twelve
beyond 7/8 below height 300.5 in all, two beyond 1, the largest 1.02677 at
height 247.0) and 0.95326 for D = -23, each one a cancellation between two nonvanishing
Euler products.  (3) Its reciprocal's coefficients, the only candidate for
the paper's Moebius input, are non-multiplicative and unbounded, so neither
the sextic-family embedding nor the local identity has an analogue, and the
power saving (2.1) is false for it by the amount of its zero.

**Does not show.**  That the paper's proofs of Lemma 7.1 and of Proposition
3.1 are correct, or that they are wrong: nothing here checks an estimate.  That
7/8 is true or false for zeta.  That the rival is a counterexample: it is not,
because it lacks a hypothesis the proof uses (docs/08 section 4.3, second
line), and its zeros are consistent with each constituent L-function being
zero-free, as section 6 of 38-the-quasi-riemann-claim.md already records for Davenport-Heilbronn.
Novelty of anything: nothing was searched; the Davenport-Heilbronn theorem
is ninety years old and the zeros of Epstein zeta functions of small
discriminant are surely tabulated somewhere not consulted here.

## 7. Kill conditions

| condition | fired | evidence |
|---|---|---|
| Proposition 2.1 applies verbatim to a linear combination | no | its statement is for 1/L_F^S(s, eta) of one primitive character; its proof survives with "1" replaced by beta_F, which makes it a shared lemma, not a verbatim application (Section 2.1) |
| routes disagree at a located zero beyond tolerance | no | agreement 1e-25 or better at every located zero (Section 3.3) |
| positive control fails or a planted fault goes undetected | no | Section 5 |
| no zero beyond 7/8 below the height bound | no | twelve zeros beyond 7/8 below 300.5 for D = -15, two of them beyond 1; one beyond 7/8 below 60.5 for D = -23 |

## 8. Limitations

- Heights: 300 for D = -15 beyond 7/8 and beyond 1, 60.5 for D = -23 and for
  the strip census, 300 for Davenport-Heilbronn.  Nothing is claimed above.
- The ball winding is segment-enclosed only for D = -15 (route C on balls);
  for D = -23 the ball check is point-sampled.  Route A and the route B mpmath polish were run only at
  zeros below height 100 (0.7 digits per unit height makes it slow).
- The real-axis neighbourhood 0 < t < 0.5 was not scanned; the pole at s = 1
  sits on the real axis.
- The explicit-formula comparison of Section 4 is inconclusive at x <= 10^6
  and is reported as such.
- Reading of the papers: Sections 1 to 3 and 7 of the 11/12 paper, and pages
  4 to 10, 50 to 55, 71 to 72 and 84 to 85 of the 7/8 paper.  The 180 pages of
  estimates were not read; the citations above are to statements, not to
  their proofs.
- Everything is float or ball grade; nothing is kernel-checked.
- `38-the-quasi-riemann-claim.md`, the lab's reading of the release, is cited
  from the branch `claude/openai-math-release-2026-10-06` of the main
  checkout; it was not on `main` when this hunt was written.

## The doors

This hunt measures a boundary rather than a ceiling, the lowest height at
which a rival of the stated class has a zero past 7/8 and past 1, so the
section is short, but it is owed.

### Active constraints at the optimum

What binds, ranked by how much it moves the answer:

1. **The scan height.**  The smallest real part the rival shows past 7/8 is
   fixed by the first located zero at height 15.5 and will not move; the
   largest real part found, 1.02677 at height 247.0, is a lower bound on
   beta_F that a longer scan can only raise, toward the triangle-inequality
   ceiling 1.5271.  Every unit of height costs about 0.1 s per contour point
   at height 300 on route C and the window cost grows like log t.
2. **The class of rival.**  Only principal forms of two discriminants were
   scanned.  Non-principal forms (their leading coefficient r(1) = 0 changes
   the reciprocal's shape: 1/zeta_Q1 is 2^s/2 times a Dirichlet series) and
   larger class numbers were not.
3. **The depth of the paper reading.**  Lemma 7.1 was identified as the
   step from its statement and the paper's own signposts; its proof (pages
   51 to 55) was read for structure, not checked.

### The frozen-constant inventory

| frozen | value | where | what relaxing it trades |
|---|---|---|---|
| window height | 10 | `census` | shorter windows cost more contour per unit height but isolate zeros for the locator; 10 never held more than three zeros in the strip |
| left edge of the box | 0.8751 (and 1.0003) | `census` | set 1e-4 above the thresholds so a zero on the threshold is not on the contour; the nudge list handles the rest; no trade shape |
| right edge | 1.6 and 1.5 | `census` | anything above sigma_1 is free of zeros by the triangle inequality; a lower edge saves a little contour |
| count precision | 15 digits | `census` | the winding integer check at 1e-6 passed everywhere; more digits cost linearly and buy nothing seen |
| locate precision | 20 digits, polish 30 | `locate_zeros`, `confirm` | the two-route agreement is at the polish precision; genuine trade against time only above height 100 where route B needs 0.8 t digits |
| ball precision | 256 bits (route C), 256 + 8 t bits (route B) | `confirm` | route B balls need the extra bits for the Gamma-Bessel cancellation; route C does not; both decided at first try |
| square half-side | 0.05, displaced by 0.15 | `confirm` | smaller squares need finer subdivision for the segment exclusion; 0.05 decided at 32 to 128 segments per side |
| inverse range | 10^6 | `inverse` | 10^7 would cost about 15 s and 1 GB and would still not separate the located zero from the x^{1/2} noise (Section 4) |
| strip floor for the prediction | 0.55 | strip census | zeros nearer the line were left out of the explicit-formula sum on purpose; including them means locating every on-line zero to height 60, which is a different instrument |

### The information class of each door

**Inside the current data, recomputation only.**  Re-counting any window at
half the forced step; polishing the three D = -15 zeros beyond height 100 on
route A; the point-sampled D = -23 ball check at more points.  None changes a
statement above.

**Inside the current family, more height.**  Scanning D = -15 above 300 to
raise the lower bound on beta_F; scanning D = -23 above 60.5, which needs
route B on balls or a Hecke-L route for the cubic character (not available in
python-flint) because route B on mpmath fails above height 100.

**Reading more.**  Whether Lemma 7.1 is exact and H_{eta,1} is within 1/2 of
1 on Re s > 7/8 is a question about pages 51 to 55 and 71 of the 7/8 paper,
and it is the question this hunt hands to a reviewer.  No computation in this
directory bears on it.
