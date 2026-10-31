# positivity_geometry: Weil's proof for curves, carried over

Hunt #150 (`hunts/rh_moonshot/`), mechanism 4, built in the session of 2026-10-21.

Files: `frobenius_span.py` (the computation), `explore.py` (prints every table below and
writes nothing), `test_positivity_geometry.py` (58 tests, about 9 s with `-n0`; every
number in this file is asserted there), `RUNS.md` (run manifest).

Grades follow `MISSION.md`: *measured*, *hardened*, *derived* (with review status),
*kernel-checked*. Nothing here is kernel-checked. Every derivation below is
**self-reviewed only**: no second session has read it. A composite claim takes the grade
of its weakest step. Nothing here is a proof of RH or a step of one.

## 0. Verdict

1. **The target is a reformulation.** The arithmetic positivity statement this mechanism
   asks for, an arithmetic Hodge index on the span of the scaling graphs (H_Q, section
   1.2), is equivalent to RH (derived, self-reviewed). Taken alone it is a restatement,
   and the hunt's kill condition for RH-equivalent restatements applies to it. Its only
   possible content is a proof from an ambient geometry, and that geometry does not
   exist.
2. **The shadow holds exactly.** Its finite-field shadow H_F is Weil's theorem. Here it is
   checked without any zeta function. For 8 curves of genus 1 and 2, the intersection Gram
   matrix of {F1, F2, Frobenius graphs} on C x C, built from brute-force point counts, has
   exactly one positive eigenvalue. Every planted violation gets two (hardened: exact
   integer arithmetic and two independent inertia routes).
3. **In the shadow, one window decides.** Positivity on the first 2g Frobenius powers is
   equivalent to RH for C, and 2g is sharp in genus 2 and 3 (derived, self-reviewed;
   exact examples). This mechanism rests on finite rank, and ζ has infinitely many zeros,
   so it has no number-field counterpart.
4. **The located obstruction is the golden fake** (original to this session; novelty not
   established, section 12). Over F_5, take
   Z(T) = (1 - 5T + 5T^2)/((1 - T)(1 - 5T)). It is rational, satisfies the curve
   functional equation and has the curve's pole structure. In every degree it has
   nonnegative integer closed-point counts and an Euler product over the places of F_5(t)
   with quadratic-character local factors and conductor 4. Yet its Frobenius eigenvalues
   satisfy |alpha|/sqrt(5) = phi^(+-1), with phi the golden ratio. So in the function-field
   world no combination of these arithmetic hypotheses implies RH: Weil's proof gets its
   positivity from the surface C x C and from nothing else. (Derived for all degrees,
   self-reviewed; exact integer checks below the derived thresholds.)
5. **The rival gate.** The Euler product enters this mechanism at the Lefschetz step:
   proper intersections of distinct Frobenius graphs are point counts (G1). The pole
   structure enters as one hyperbolic plane (G2). The rivals split as follows:
   - DH fails both: Lambda_DH(3) < 0, Lambda_DH(6) != 0, and no pole.
   - Epstein (1,1,6) fails G1 (at n = 6 and n = 48) and passes G2.
   - W_{1/4} passes G1 and fails G2: two poles, so signature (2, 2).
   - The golden fake passes both and fails RH.

   The step that does the work, Hodge index on an ambient surface, uses no Euler product,
   and for ζ itself it is missing. **Disposition: unresolved**, with a restricted-class
   obstruction for arguments confined to G1, G2, the functional equation and finiteness
   of the rationality type (section 9).

## 1. The exact target and its relation to RH

### 1.1 The finite-field shadow (a theorem)

Take a smooth projective curve C of genus g over F_q, and let S = C x C over F_q. Set
F1 = {pt} x C and F2 = C x {pt}. For n >= 0 let G_n be the graph of the n-th power of
Frobenius Phi, so G_0 is the diagonal. For n < 0 let G_n be the transpose of G_{|n|}.
Write N_k = #C(F_{q^k}) and N_0 := 2 - 2g. The Hodge index theorem says the intersection
form on NS(S) tensor R has signature (1, rho - 1). So the Gram matrix of any finite
family of classes has at most one positive eigenvalue
(Hartshorne V.1.9; the route to Weil's bound through Castelnuovo-Severi is
Mattuck-Tate 1958 and Grothendieck 1958).

**H_F:** for every window, the Gram matrix of {F1, F2, G_n : n in the window} has exactly
one positive eigenvalue.

### 1.2 The number-field target

Let V be the real vector space spanned by symbols F1, F2 and gamma_f, for real f in
C_c^infty(R_+^*). Write f^(s) = int_0^infty f(x) x^s d*x and f*(x) = f(1/x). Let W be the
Weil functional, W(h) = sum over nontrivial zeros rho of h^(rho - 1/2). The explicit
formula computes it from primes, the pole and the archimedean term, in the convention
`zeta/weil.py` calibrates. Put

    <F1, F1> = <F2, F2> = 0,   <F1, F2> = 1,
    <gamma_f, F1> = f^(-1/2),   <gamma_f, F2> = f^(1/2),
    <gamma_f, gamma_g> = f^(1/2) g^(-1/2) + f^(-1/2) g^(1/2) - W(f * g*).

Formally, f = delta at q^n reproduces the normalized finite-field table of section 2.2.
In the ratio variable, the off-diagonal "intersection number" of two scaling graphs at
ratio n is the explicit-formula atom Lambda(n) n^(-1/2).

**Target H_Q:** this form has at most one positive direction on every finite-dimensional
subspace of V.

**Relation to RH (derived, self-reviewed): H_Q is equivalent to RH.** Projecting
gamma_f off the hyperbolic plane <F1, F2>, by gamma_f -> gamma_f - f^(1/2) F1 - f^(-1/2) F2,
leaves <gamma_f^0, gamma_g^0> = -W(f * g*). The plane itself contributes exactly one
positive direction. So H_Q holds if and only if W(f * f*) >= 0 for every real f, and
that is Weil's criterion (Weil 1952; Bombieri 2000), subject to the admissible-class
hedge recorded in `zeta/weil.py`. Hence H_Q is RH in intersection language. **As a
target it is a reformulation, and it is recorded as one, not as progress.**

What the restatement does buy: an item-by-item list of the structure that would prove it
(section 3), and a concrete rival gate (section 6).

## 2. The construction on the finite-field side

### 2.1 Intersection numbers (derived, self-reviewed)

    F1.F1 = F2.F2 = 0,   F1.F2 = 1
    G_n.F1 = deg(pr1 on G_n) = 1,   G_n.F2 = deg(pr2 on G_n) = deg Phi^n = q^n   (n >= 0)
    G_{-n}.F1 = q^n,   G_{-n}.F2 = 1
    G_a.G_b = q^b N_{a-b}          (a >= b >= 0, and symmetrically for a, b <= 0)
    G_{-a}.G_b = N_{a+b}           (a, b >= 1)

The two cases of the derivation:

- **Same sign.** (Phi^b x 1)^* G_{a-b} = G_a and (Phi^b x 1)^* G_0 = G_b: the local
  equation y - x^(q^(a-b)) pulls back to the reduced equation y - x^(q^a). Since
  Phi^b x 1 is finite of degree q^b, the projection formula gives
  G_a.G_b = q^b (G_{a-b}.G_0). For a > b, G_{a-b} meets the diagonal transversally in
  the N_{a-b} fixed points of Phi^(a-b). For a = b, G_0^2 = deg T_C = 2 - 2g, which is
  why N_0 := 2 - 2g.
- **Opposite signs.** {(Phi^a y, y)} and {(x, Phi^b x)} meet where x = Phi^(a+b) x. One
  tangent line is vertical and the other horizontal, so every meeting is transversal.

The exact test `test_transposes_obey_the_second_intersection_formula` checks the two
formulas against each other. The symmetric window G_{-2..2}, which uses both formulas,
must have the inertia of the one-sided window G_0..G_4, which uses only the first. It
does, for all 8 curves.

### 2.2 Projection and the Weil form

P(D) = D - (D.F2) F1 - (D.F1) F2 kills both rulings, and

    P(D).P(E) = D.E - (D.F1)(E.F2) - (D.F2)(E.F1).

In the basis (F1, F2, P(G_n)) the Gram matrix is block diagonal: the hyperbolic plane,
plus the projected block. So inertia(full) = (1, 1, 0) + inertia(projected), and H_F is
the statement that the projected block is negative semidefinite. Normalizing by
q^(-|n|/2):

    P(G_a).P(G_b) = -q^((|a|+|b|)/2) t_{a-b},
    t_k = q^(-|k|/2) (q^|k| + 1 - N_|k|) = sum_i (alpha_i / sqrt q)^|k|,   t_0 = 2g.

The last equality is the Lefschetz formula. So on the Frobenius span the intersection
form is minus a Toeplitz form in the normalized Frobenius eigenvalues u_i = alpha_i/sqrt(q),
and that Toeplitz form is exactly the explicit-formula form of the function field.
Hodge index on this span is therefore Weil positivity, which is RH for C.

### 2.3 Castelnuovo-Severi as 2x2 minors

The projected block restricted to {G_0, G_n} is
[[-2g, -(q^n + 1 - N_n)], [-(q^n + 1 - N_n), -2g q^n]]. It is negative semidefinite
exactly when |N_n - q^n - 1| <= 2g q^(n/2), which is Weil's bound over F_{q^n}.
`castelnuovo_severi_margins` returns 4 g^2 q^n - (q^n + 1 - N_n)^2. For y^2 = x^3 - x at
p = 11, which is supersingular, the margins are [44, 0, 5324, 0]: the bound is attained
at even n, because alpha^2 = -11 makes u^2 = -1 lie on the circle.

### 2.4 One window decides in the shadow (derived, self-reviewed)

**Claim.** Let T_m = [t_{a-b}] for 0 <= a, b < m, the projected form on G_0..G_{m-1}.
Then T_{2g} is positive semidefinite if and only if every |alpha_i| = sqrt(q).

**Proof.**

- *If.* When every |u_i| = 1, the quadratic form is f^T T_m f = sum_i |F(u_i)|^2 >= 0,
  where F(z) = sum_a f_a z^a.
- *Only if.* Suppose some |u| != 1. The multiset {u_i} has 2g elements and is closed
  under conjugation and inversion. Let G be the orbit of u: either {u, 1/u}, or
  {u, conj u, 1/u, 1/conj u}. Let R be the set of distinct remaining values. Then
  |R| + |G| <= 2g. Take the real interpolating polynomial F of degree <= 2g - 1 that
  vanishes on R and takes the value 1 at u and conj u, and -1 at 1/u and 1/conj u.
  Then f^T T_{2g} f = sum_i F(u_i) F(1/u_i). Every term from R vanishes, and each copy
  of the orbit contributes -2 (real u) or -4 (complex u), so the sum is negative.

**Sharpness (hardened, exact inertia):**

- *Genus 2.* The fake P = (1 + 3T + 5T^2)(1 - 5T + 5T^2) passes windows 2 and 3 = 2g - 1
  and is refused at window 4.
- *Random family.* In a seeded family of Weil-type polynomials (on/off-circle
  classification by mpmath roots at 40 digits), every off-circle case is refused by
  window 2g and every on-circle case is positive on every window tested (up to 2g + 2).
  The first refusing windows were:
  - q = 5, g = 2: {2: 7, 3: 10, 4: 6}
  - q = 7, g = 2: {2: 8, 3: 8, 4: 9}
  - q = 5, g = 3: {2: 1, 3: 19, 4: 10, 5: 1, 6: 1}
  - q = 7, g = 3: {2: 11, 3: 16, 4: 5, 5: 2, 6: 1}

So 2g is attained in genus 3 as well.

**What it says.** In the shadow there is a window-propagation mechanism: finite rank.
The form on the Frobenius span has rank 2 + 2g, so positivity on one window of length
2g log q forces it on every window. For ζ the rank is infinite, and no finite window is
known to decide. Bombieri 2000 (Thm 10 and the numerics of section 13, as read in
`weil_propagation/theory/RESULTS.md` section 1) finds that small windows cannot see
off-line zeros in the band limit: below a critical window the negative eigenvalue tends
to 0 as the band grows. The measured detection windows
there are of order log c ~ 3.4, for DH at height 85.7 and for Epstein (1,1,6) at height
16.3. This places the all-windows frontier in geometric terms: it is the
infinite-dimensionality of H^1. The claim is original here, but it is very likely known
in the language of positive Toeplitz forms (Caratheodory, Toeplitz, Fejer); novelty is
not established.

### 2.5 What was computed (hardened)

All point counts are by literal enumeration over F_{p^n}: a table of squares, Horner
evaluation, and the point at infinity, with no character sums or eigenvalues.

**Cross-checks on the counting and the fields:**

- **Elliptic curves.** The counts equal `zeta.finitefield.count_points` (N_1),
  `count_points_fp2` (N_2) and the Lefschetz prediction `point_counts_over_extensions`
  (N_3, N_4). This was checked for (a, b, p) = (1, 1, 5), (2, 3, 7), (-1, 0, 11),
  (1, 6, 13), and for N_1 also at (3, 5, 101).
- **Genus 2.** The brute-force N_3 and N_4 equal the values that N_1 and N_2 predict
  through the Weil polynomial (rationality, checked on brute-force data).
- **The fields.** Every extension field passes the check x^(p^n - 1) = 1 for all
  nonzero x, and a deliberately reducible modulus fails it.
- **Inertia.** Exact inertia comes from flint's integer characteristic polynomial with
  Descartes' rule, which is exact for real-rooted polynomials. It is cross-checked
  against symmetric elimination over Q with 2x2 pivots, which shares no code with the
  first route, and against float eigenvalues on 60 random rank-deficient matrices.

| curve | p | g | N_1..N_4 (brute force) | Weil polynomial | full inertia, window 5 | CS margins n = 1..4 |
| --- | --- | --- | --- | --- | --- | --- |
| y^2 = x^3 + x + 1 | 5 | 1 | 9, 27, 108, 675 | 1 + 3T + 5T^2 | (1, 3, 3) | 11, 99, 176, 99 |
| y^2 = x^3 + 2x + 3 | 7 | 1 | 6, 60, 378, 2400 | 1 - 2T + 7T^2 | (1, 3, 3) | 24, 96, 216, 9600 |
| y^2 = x^3 - x | 11 | 1 | 12, 144, 1332, 14400 | 1 + 11T^2 | (1, 3, 3) | 44, 0, 5324, 0 |
| y^2 = x^3 + x + 6 | 13 | 1 | 13, 195, 2236, 28275 | 1 - T + 13T^2 | (1, 3, 3) | 51, 51, 7344, 31875 |
| y^2 = x^5 - x + 1 | 5 | 2 | 11, 31, 101, 651 | 1 + 5T + 15T^2 + 25T^3 + 25T^4 | (1, 5, 1) | 55, 375, 1375, 9375 |
| y^2 = x^5 + x + 3 | 7 | 2 | 11, 55, 371, 2419 | 1 + 3T + 7T^2 + 21T^3 + 49T^4 | (1, 5, 1) | 103, 759, 4759, 38127 |
| y^2 = x^5 + 2x^3 + x + 3 | 11 | 2 | 9, 133, 1296, 14809 | 1 - 3T + 10T^2 - 33T^3 + 121T^4 | (1, 5, 1) | 167, 1815, 20000, 206367 |
| y^2 = x^5 + x^2 + 2 | 13 | 2 | 12, 178, 2148, 29038 | 1 - 2T + 6T^2 - 26T^3 + 169T^4 | (1, 5, 1) | 204, 2640, 32652, 230400 |

In every case the projected block has no positive eigenvalue and rank exactly 2g. An
independent route, the roots of the Weil polynomial, gives |alpha|/sqrt(p) = 1 within
1e-25 for every curve.

## 3. Weil's ingredients and their number-field counterparts

| # | Weil's proof (C over F_q) | number-field counterpart | status |
| --- | --- | --- | --- |
| 1 | the curve C over a base field | Spec Z over a base "F1" | missing (`docs/11` sections 2-3) |
| 2 | the surface S = C x_{F_q} C | Spec Z x_{F1} Spec Z | missing: Z tensor_Z Z = Z collapses; candidates without an intersection theory are the square of the Connes-Consani arithmetic site and Z tensor_S Z over the sphere spectrum |
| 3 | graphs G_n of Frobenius powers | scaling correspondences Psi(lambda), lambda in R_+^* | exist as correspondences on the square of the arithmetic site (Connes-Consani 2014) |
| 4 | G_a.G_b = q^min N_|a-b| (fixed points are points) | the Weil distribution as the trace of the scaling action (Connes 1999, semilocal trace formula); off-diagonal entries Lambda(n) n^(-1/2) | exists as a trace formula; G1 holds for ζ (section 6) |
| 5 | rulings F1, F2 and the ample class F1 + F2 | the pole functionals f^(+-1/2) | the hyperbolic plane exists (G2 holds for ζ); ampleness is missing, since V has no effective cone |
| 6 | Hodge index on NS(S) | H_Q | missing, and equivalent to RH |
| 7 | its proof: Riemann-Roch on S, Serre duality, and positive degree of effective classes | Riemann-Roch on the square | missing; Riemann-Roch exists one dimension down (Arakelov divisors on Spec Z, van der Geer-Schoof; Connes-Consani's Riemann-Roch for Spec Z and on the periodic orbits of the scaling site) |
| 8 | base change to F_{q^n} keeps the genus, so one 2x2 minor per n suffices | F_{1^n} extensions are Z[mu_n], whose zeta functions gain zeros | missing |
| 9 | finite-dimensional H^1: window 2g decides (section 2.4) | infinitely many zeros; no finite window is known to decide | missing: this is the all-windows frontier |

The shadow test (sections 4-5) shows that rows 3, 4 and 5, together with the functional
equation and rationality, are also present for fakes that violate RH. Rows 1, 2, 6 and 7
are what separate.

## 4. Planted violations: fake curves

### 4.1 The golden fake

Z(T) = (1 - aT + qT^2)/((1 - T)(1 - qT)) with a^2 > 4q has rationality, the curve
functional equation (the numerator is self-reciprocal) and poles exactly at T = 1 and
T = 1/q. At (q, a) = (5, 5) the inverse roots are alpha = sqrt(5) phi and
beta = sqrt(5)/phi, with phi = (1 + sqrt 5)/2. So |alpha|/sqrt(5) = phi and 1/phi to 25
digits, and in s-coordinates the zeros sit at Re s = 1/2 +- log(phi)/log(5)
= 0.79899 and 0.20101. The counts are

    N_n = 5^n + 1 - t_n,   t = 2, 5, 15, 50, 175, 625, ...   (t_n = 5^(n/2) L_n for even n,
                                                              5^((n+1)/2) F_n for odd n)
    N_1..N_4 = 1, 11, 76, 451
    b_1..b_6 = 1, 5, 25, 110, 500, 2215      (closed points: Z = prod_d (1 - T^d)^(-b_d))

### 4.2 Nonnegative closed-point counts in every degree (derived, self-reviewed)

For 2 sqrt(q) < a < q + 1, with alpha the larger root of x^2 - ax + q and rho = alpha/q:

- N_e = (q^e - alpha^e)(1 - alpha^(-e)) >= 0, and N_e <= q^e + 1.
- d b_d >= N_d - sum_{e <= d/2} N_e >= q^d (1 - rho^d - alpha^(-d)) - q^(d/2+1)/(q-1) - d/2.

So b_d > 0 as soon as 1 - rho^d - alpha^(-d) > q^(1-d/2)/(q-1) + (d/2) q^(-d). This
condition is monotone in d. For a < 0 the same argument works with |alpha|, the parity
cases of N_e, and a factor 3 on the sum. `fake_genus1_threshold` locates the first d
where it holds (D0 = 2 for the golden fake, at most 3 for all 8 fakes tested), and the
smaller degrees are checked exactly. The tests check b_d >= 0 exactly to d = 60 for
(q, a) = (5, +-5), (7, 6), (7, 7), (11, 7), (11, 10), (13, 8) and (13, 13). For
(5, -5) the minimum is b_2 = 0, so b_d >= 0 can be attained with equality.

### 4.3 Refusal (hardened)

Every genus-1 fake has full inertia (2, 2, 0) already at window 2, that is on
{F1, F2, G_0, G_1}, and (2, 2, 3) at window 5. The golden fake's 2x2 minor margin is
4 * 5 - 25 = -5.

### 4.4 Genus-2 fakes and windows (hardened)

Take P = (1 - a1 T + 5T^2)(1 - a2 T + 5T^2) with |a1| <= 4 honest and a2 = +-5 fake.
Among these, the ones with b_d >= 0 for every d <= 40 are refused first at window 3 or
window 4.

**The tested example.** P = (1 + 3T + 5T^2)(1 - 5T + 5T^2) = 1 - 2T - 5T^2 - 10T^3 + 25T^4.

- min b_d (d <= 60) = 4.
- The general tail threshold is 5 (`fake_threshold_general`, same argument with
  |s_e| <= 2g A^e), so b_d > 0 in every degree.
- Windows 2 and 3 pass, and windows 4 and 5 are refused.
- The Castelnuovo-Severi margins are 76, 204, -2624, -5876.

So the n = 1 and n = 2 minors and the first two windows all accept it, and the
violation appears only at n = 3. Weil's route through base change needs every n; the
Toeplitz route needs window 2g.

## 5. The base-field Euler product: quadratic-character local factors over F_q(t)

### 5.1 The decomposition

A degree-2 numerator P(T) should be the L-function of a quadratic character of F_q(t):
P(T) = prod over unramified places v of (1 - chi(v) T^(deg v))^(-1), with chi(v) = +-1
and r_d ramified places of degree d. Conductor sum d r_d = deg P + 2 = 4.

All places of degree d carry the same local factor shape, so only the counts matter:
s_d places with chi = +1 and i_d with chi = -1. Comparing
Z_{P^1} P = prod_d (1 - T^d)^(-(2 s_d + r_d)) (1 - T^(2d))^(-i_d) with
prod_d (1 - T^d)^(-(pi_q(d) + c_d)), where P = prod_d (1 - T^d)^(-c_d), gives

    s_d = (pi_q(d) + c_d - r_d - i_{d/2}) / 2,      i_d = pi_q(d) - r_d - s_d.

Here pi_q(d) is the number of places of F_q(t) of degree d.

### 5.2 Controls (hardened)

- **Honest curves.** For y^2 = x^3 + x + 1 (p = 5), x^3 + 2x + 3 (7), x^3 - x (11) and
  x^3 + x + 6 (13), with their actual ramification, the recursion yields nonnegative
  integers to degree 40.
- **Brute force.** For three of them, the split and inert counts in degrees 1, 2 and 3
  equal a direct count of places: the orbits of exact-degree x in F_{q^d}, classified
  by whether f(x) is a nonzero square. So the recursion counts actual places.

### 5.3 The golden fake, every degree (derived, self-reviewed; exact to degree 40)

**Exact.** With ramification {one place of degree 1, one of degree 3}, the golden fake's
recursion gives:

- split counts 0, 0, 12, 50, 250, 1094, 5000, 22500;
- inert counts 5, 10, 27, 100, 374, 1486, 6160, 26250;
- places 6, 10, 40, 150, 624, 2580, 11160, 48750.

This continues with nonnegative integers through degree 40. Every other ramification
configuration fails parity at degree 1.

**Integrality in every degree (the mod-2 argument).** Let P and P' have the same
ramification data, and set delta = c' - c. Along each chain m, 2m, 4m, ... with m odd,
s'_{2^k m} = s_{2^k m} + S_k / 2^(k+1), where S_k = sum_{j<=k} 2^j delta_{2^j m}.

Now reduce mod 2. In F_2[[T]] one has (1 - T^(2^k m)) = (1 - T^m)^(2^k), so P mod 2
equals prod_{m odd} (1 - T^m)^(-sigma_m), with sigma_m = sum_k 2^k c_{2^k m} in Z_2.
The map from (sigma_m) to this product is injective. (At the least odd m with
sigma_m != 0, write sigma_m = 2^k u with u a unit. Then the coefficient of T^(2^k m) is
odd, and no factor with a larger odd index reaches that degree.)

Hence P' congruent to P mod 2 forces S_k divisible by 2^(k+1) for every k and m, which
gives integrality in every degree.

The reference curve is y^2 = x^3 + x + 1 over F_5. Its P = 1 + 3T + 5T^2 is congruent to
1 - 5T + 5T^2 mod 2, and its ramification is {degree 1 (infinity), degree 3 (f
irreducible)} (`mod2_reference_curve`).

**Nonnegativity past D1.** It suffices that pi(d) - r_d >= |c_d| + pi(d/2), and with
d |c_d| <= 2g (A^d + A^(d/2+1)/(A-1)) this holds for d >= D1 = 4
(`quadratic_tail_threshold`). Below D1 it is checked exactly.

**The other fakes.** All 8 genus-1 fakes tested have an admissible configuration to
degree 40 that comes with a cubic mod-2 reference curve, and D1 <= 8. So each of them
has a quadratic-character Euler product in every degree.

### 5.4 What this shows, and its scope

In the function-field world, the following hypotheses do not imply RH, even taken
together:

- the Euler product in its strongest local form (degree-1 local factors with
  |chi(v)| <= 1 at every place of the base, and the right conductor);
- the counting form (nonnegative integer closed-point counts);
- the functional equation;
- the pole structure;
- rationality.

The ±1 place function of the golden fake is not a character: by Weil it cannot be, since
its L-function violates RH. What the fake lacks is periodicity, that is automorphy
(compatibility with twists), or equivalently a curve.

**Why the shadow is weak exactly here.** The variable T = q^(-s) aggregates all places of
one degree, roughly q^d/d of them, and the Euler product constrains only those
aggregates. Over Q each norm carries one prime: the Dirichlet series sees every local
factor separately, and the degree-1 Selberg class is classified (Kaczorowski-Perelli
1999). So a degree-1 Q-analogue of the golden fake cannot exist without contradicting
that classification together with GRH for Dirichlet L-functions. The obstruction
therefore transfers only to arguments that use the Euler product through per-norm
aggregates and through properties with function-field counterparts. The same
aggregation lets DH's construction, a combination of two L-functions with one
functional equation, land on Euler-product objects over F_q(t): the golden fake equals
2 L_{a=4} - L_{a=3}, an integer combination of two honest numerators. Over Q, DH's
multiplicativity fails visibly (a_6 = 1, a_2 a_3 = -kappa^2).

## 6. The distinguishing step and the rival gate

### 6.1 Where the Euler product enters

In Weil's proof the Euler product enters exactly once, at the Lefschetz identification:
the off-diagonal intersection numbers G_a.G_b = q^min N_|a-b| are point counts, and
N_k = sum_{d|k} d b_d with b_d >= 0 closed points. This is **G1**. The trivial part
enters as **G2**: H^0 and H^2 are one-dimensional of weights 0 and 2, which gives one
hyperbolic plane. The positivity, Hodge index on S (**G3**), uses no Euler product. It
uses Riemann-Roch and ampleness on the surface.

The number-field forms tested here are:

- **G1:** Lambda_F(n) >= 0, and Lambda_F is carried by prime powers.
- **G2:** exactly one pole in Re s > 1/2. Each simple pole s0 adds the pair
  f^(s0 - 1/2) f^(1/2 - s0), so k poles give signature (k, k) in the trivial part.

### 6.2 The table

Measured with `nf_rival_table(n_max = 60, dps = 30)`. Lambda_F is read off the Dirichlet
coefficients alone (`zeta.epstein.log_derivative_coefficients`), and the residues are
eps F(s0 + eps) with eps = 1e-15.

| function | G1 sign: first n <= 60 with Lambda_F(n) < 0 | G1 support: first non-prime-power n with Lambda_F(n) != 0 | poles in Re s > 1/2 (residue) | G2 | RH |
| --- | --- | --- | --- | --- | --- |
| ζ | none | none | s = 1 (1.000) | one plane | open |
| DH | 3: -kappa log 3 | 6: (1 + kappa^2) log 6 | none | empty trivial part | fails (0.808517 + 85.699348i) |
| Epstein (1,1,6) | 48 | 6 | s = 1 (2 pi/sqrt 23 = 1.310135) | one plane | fails (0.953260 + 16.290216i) |
| W_{1/4} | none | none | s = 5/4 (zeta(3/2) = 2.612375), s = 3/4 (zeta(1/2) = -1.460355) | two planes, (2, 2) | fails (rho +- 1/4) |
| golden fake, over F_5(t) | none (b_d >= 0; ±1 local factors) | closed points only | T = 1 and T = 1/5 | one plane | fails (alpha/sqrt 5 = phi) |

G1 and G2 together separate ζ from all three number-field rivals. In the shadow, though,
G1 and G2 together with the functional equation and rationality are met by the golden
fake. So G1 and G2 are preconditions of the mechanism, not its engine.

### 6.3 DH

DH fails both testable preconditions. Its log-derivative coefficients are signed
(Lambda_DH(2) = kappa log 2, Lambda_DH(3) = -kappa log 3) and supported off prime powers
(Lambda_DH(6) = (1 + kappa^2) log 6). In the dictionary, two distinct scaling graphs
would have negative intersection, which is impossible for effective curves meeting
properly. DH is entire, so it has no H^0 or H^2, no rulings and no ample class.

Its Weil form is indefinite: `weil_propagation` hardened a sign change at
c in [30.617, 30.818]. DH is like the L-function of a fake character, and in a
geometric picture it would be a piece of H^1 of something, not a curve. A linear
combination of L-functions is not the L-function of any motive, since the zeta function
of a sum of motives is a product. This is why "no curve and no Frobenius" bites at G1
and G2 before positivity is ever reached.

### 6.4 W_{1/2} is the zeta function of the projective line over Z (derived, elementary; coefficients checked)

W_{1/2}(s - 1/2) = zeta(s) zeta(s - 1) = Z(P^1_Z, s). The coefficients are sigma(n),
checked for n <= 30 with `zeta.epstein.shifted_coefficient`. So the W_a rival at
a = 1/2 is the Hasse-Weil zeta function of a two-dimensional arithmetic scheme with
mixed weights. In this mechanism's terms, W_a fails "the trivial part is one hyperbolic
plane of weights (0, 2)". Any Hodge-index statement that sees the poles as classes
excludes W_a on its trivial part alone: signature (2, 2) already exceeds (1, *). At
a = 1/4, W_a also fails the integrality refinement of G1, since Lambda_W(p^k)/log p is
not an integer.

### 6.5 What a number-field H_Q would need

1. An ambient object containing the scaling correspondences, with a symmetric pairing
   whose values on them are the Weil distribution. It must reproduce the G1 numbers
   (Lambda(n) n^(-1/2) at ratio n, nonnegative, carried by prime powers) and the G2
   plane.
2. A notion of effective class and an ample class, with positive degree on effective
   classes.
3. A Riemann-Roch inequality on that object, strong enough to run the Hodge index proof
   of Hartshorne V.1.9.
4. A construction that cannot be granted to:
   - DH (it fails 1 at G1 and G2);
   - Epstein (1,1,6) (it fails 1 at G1);
   - W_a (its trivial part violates the signature);
   - and, by the golden fake, anything that only shares G1, G2, the functional equation
     and finiteness. The ingredient must carry information that the zeta function of a
     golden-type fake does not.

## 7. Known obstructions, and what differs from refuted forms

- **Weil positivity is equivalent to RH** (Weil 1952; Bombieri 2000). H_Q is a
  restatement of it.
- **The evasions of `docs/09` section 5.1.** Building V from W by a GNS-type completion
  would be "tautological completion" (positivity assumed). A positive state declared on
  the convolution algebra of R_+^* would be "formal C*-positivity". An ambient object
  matched on finitely many windows would be a "finite approximant". This construction
  claims none of them; it names the missing ambient space.
- **The collapse of the square.** Z tensor_Z Z = Z (`docs/11` section 2).
- **Faltings-Hriljac.** The arithmetic Hodge index of Faltings (1984) and Hriljac (1985)
  holds on arithmetic surfaces X -> Spec Z, where it gives positivity of the Neron-Tate
  height. It is about a curve over a number field, not Spec Z x Spec Z, and it does not
  touch RH.
- **`local_positivity` (hunt 5).** It found that place-by-place norms of the prime side
  exist and do not assemble. The golden fake sharpens this into an exact statement in
  the shadow. The strongest local data, nonnegative integer closed-point counts and ±1
  local factors at every place, coexist with global failure. Global positivity cannot
  be assembled from local data without the surface.
- **EPP/Herglotz (refuted by W_a).** It relied on prime-side positivity. Here G1 is shown
  insufficient in both worlds: W_{1/4} over Q and the golden fake over F_5(t).
- **`weil_propagation` C1-C4.** It found no window-to-window mechanism in its searched
  set. In the shadow the only propagation mechanism is finite rank (section 2.4), and
  the genus-2 and genus-3 fakes show exactly that positivity on windows below 2g does
  not propagate. ζ has infinite rank.
- **Bombieri-Stepanov** (Bombieri 1973) proves Weil's bound with Riemann-Roch on C alone
  and an auxiliary function built from the additive Frobenius x -> x^q, without the
  surface. Its number-field shadow would be a one-sided bound
  psi(x) <= x + O(x^(1/2+eps)). By Landau's theorem that bound is equivalent to RH,
  since ζ has no real zeros in (0, 1) (classical, derived here only in outline). Z has
  no additive Frobenius, and one-sided prime bounds of that strength lie beyond sieve
  methods (parity). This is recorded as a different mechanism and not worked here.

## 8. Tests run

`test_positivity_geometry.py` has 58 tests, run with `.venv/bin/python -m pytest -q -n0
hunts/rh_moonshot/positivity_geometry`: 58 passed, about 9 s.

**Instruments**

- The two exact inertia routes agree with each other and with float eigenvalues on 60
  random rank-deficient matrices.
- The extension fields are fields, and the field check fails on a reducible modulus.
- The brute-force counts equal `zeta.finitefield` and the Lefschetz predictions.

**The shadow**

- The brute-force counts are the pinned ones and are rational.
- Hodge index holds on the Frobenius span of all 8 curves, with the pinned inertias and
  projected rank 2g.
- Symmetric and one-sided windows agree.
- The Castelnuovo-Severi margins are nonnegative, including the supersingular equality
  case.
- The eigenvalue route and the Toeplitz symbols agree.

**Planted violations and windows**

- All the golden fake facts.
- All 8 genus-1 fakes: counting Euler product to d = 60, tail threshold at most 3, and
  refusal at window 2.
- b_2 = 0 for (5, -5).
- The genus-2 fake: passes windows 2 and 3, refused at 4, with the pinned margins.
- Window 2g decides on four seeded random families, and is sharp.

**The base field**

- Honest curves decompose.
- The recursion equals direct place counts.
- The golden fake's quadratic decomposition, its reference curve and D1 = 4.
- Every genus-1 fake has a configuration with a reference curve.

**Number field**

- ζ meets G1 and G2.
- DH fails both, with Lambda_DH(2), Lambda_DH(3) and Lambda_DH(6) in closed form.
- Epstein (1,1,6): (48, 6), one pole with residue 2 pi/sqrt 23.
- W_{1/4} meets G1, with two poles at the residues zeta(3/2) and zeta(1/2).
- W_{1/2}(s - 1/2) has coefficients sigma(n).

**House rules**

- No reserved word and no em dash in this directory.
- The run manifest validates.

## 9. Disposition: unresolved, with a located restricted-class obstruction

- **The target H_Q** is equivalent to RH. Taken alone it is a reformulation, recorded as
  such.
- **The mechanism's real step** is an ambient surface whose Hodge index follows from a
  Riemann-Roch theorem. It was not built. Nothing here shows that it cannot be built,
  and no global no-route claim is made (`ALIGNMENT.md` section 5.1).
- **Restricted-class obstruction (an exact witness; derived, self-reviewed).** The class
  is every argument that derives RH for ζ from G1, G2, the functional equation and
  finiteness of rationality type, and that transfers verbatim to global function
  fields. Every such argument is invalid, because the golden fake meets the
  function-field versions of all of them and violates RH. The scope is set by section
  5.4: arguments that use the Euler product only through per-norm data. Over Q, where
  each norm carries one prime and degree 1 is classified, the shadow does not model the
  Euler product, and the obstruction does not reach arguments that use that rigidity.

## 10. Furthest true statements, with grades

1. **(hardened, exact integer arithmetic, two inertia routes)** For 8 curves of genus 1
   and 2 over F_5, ..., F_13, the Gram matrix of {F1, F2, G_0..G_4} built from
   brute-force point counts has exactly one positive eigenvalue, and the projected block
   has rank 2g. Every planted fake has two positive eigenvalues.
2. **(derived, self-reviewed; sharpness hardened)** In the shadow, positivity on the
   first 2g Frobenius powers is equivalent to RH for C, and 2g is attained in genus 2
   (an exact example) and genus 3 (random-family examples).
3. **(derived for all degrees, self-reviewed; exact below the derived thresholds)** The
   golden fake has rationality, the curve functional equation, poles at T = 1 and 1/5,
   nonnegative integer closed-point counts in every degree, and a quadratic-character
   Euler product over F_5(t) of conductor 4 in every degree. Its eigenvalues have
   |alpha|/sqrt 5 = phi^(+-1), and its Frobenius-span form has two positive eigenvalues
   at window 2. Hence, in the function-field world, Weil positivity is not implied by
   the Euler product (in both forms), the functional equation, rationality and the pole
   structure.
4. **(measured)** The number-field G1/G2 table of section 6.2.
5. **(derived, elementary; coefficients measured to n = 30)** W_{1/2}(s - 1/2) =
   Z(P^1_Z, s).

The located obstruction, the golden fake as a witness against the restricted class,
takes the weakest grade among its steps: derived, self-reviewed.

## 11. Next step

1. **The decisive question for this mechanism.** Does any proposed square of Spec Z
   (Connes-Consani's square of the arithmetic or scaling site, or Z tensor_S Z over the
   sphere spectrum) carry a symmetric pairing on the span of its Frobenius
   correspondences that passes G1 and G2 with the numbers of section 6.2?
   - **First concrete step:** in the published scaling-site formalism, compute the
     pairing of two Frobenius correspondences Psi(lambda) and Psi(lambda'), and compare
     it with the explicit-formula entry Lambda(n) n^(-1/2) at lambda/lambda' = n.
   - **What decides it:** a mismatch in sign or support refutes that candidate as the
     ambient space. A match moves the problem to Riemann-Roch on the square, which is
     row 7 of section 3.
   - **Cost:** a reading task plus a small exact computation, with no heavy compute.
2. **In the shadow: find the smallest datum beyond the zeta function that refuses
   golden-type fakes.** The fake's ±1 place function is fixed only per degree. Twist it
   by an honest quadratic character and ask whether any distribution of signs keeps the
   twisted Euler products rational of bounded degree up to a fixed degree. By Weil's
   theorem and the function-field converse theorem, some twist must fail. The degree and
   conductor at which every distribution fails measure how much family information
   (automorphy) the positivity needs, and that is what a number-field twist test would
   have to read. This is an exact combinatorial computation, well within the box limits.

## 12. Sources and novelty

Cited from memory and **not re-read in this session**. The statement attributed to each
is the standard one; check before quoting further.

- **Weil and the curve.** A. Weil, *Sur les courbes algebriques et les varietes qui s'en
  deduisent* (1948). A. Mattuck and J. Tate, *On the inequality of Castelnuovo-Severi*
  (1958). A. Grothendieck, *Sur une note de Mattuck-Tate* (1958). R. Hartshorne,
  *Algebraic Geometry*, V.1 (Hodge index, Thm 1.9; graph of Frobenius, Ex. 1.10).
- **Weil positivity.** A. Weil, *Sur les "formules explicites" de la theorie des nombres
  premiers* (1952). E. Bombieri, *Remarks on Weil's quadratic functional in the theory
  of prime numbers I*, Rend. Lincei 11 (2000), read here only through
  `weil_propagation/theory/RESULTS.md`.
- **Stepanov's method.** E. Bombieri, *Counting points on curves over finite fields
  (d'apres S. A. Stepanov)*, Sem. Bourbaki 430 (1973).
- **Trace formula and F1.** A. Connes, *Trace formula in noncommutative geometry and the
  zeros of the Riemann zeta function*, Selecta 5 (1999). A. Connes and C. Consani,
  *The arithmetic site* (C. R. 2014), *Geometry of the scaling site* (Selecta 2017),
  and their Riemann-Roch papers for Spec Z (2022-2023). A. Connes, C. Consani and M.
  Marcolli, *The Weil proof and the geometry of the adeles class space* (2008).
- **Arakelov theory.** G. Faltings, *Calculus on arithmetic surfaces* (1984). P.
  Hriljac, *Heights and Arakelov's intersection theory* (1985). G. van der Geer and R.
  Schoof, *Effectivity of Arakelov divisors* (2000).
- **The degree-1 Selberg class.** J. Kaczorowski and A. Perelli, *On the structure of the
  Selberg class I: 0 <= d <= 1*, Acta Math. 182 (1999).

**Novelty search.** Two web searches were run on 2026-10-21: one for function-field
"fake" zeta functions with an Euler product and a functional equation that violate RH,
and one for a function-field analogue of the Selberg class with RH failing. They
returned expositions of the Weil conjectures and of the Selberg class, and no
construction of this kind. arXiv, zbMATH and MathSciNet full-text were not searched.

The golden fake with its quadratic-character Euler product, the window-2g statement and
its sharpness examples, and the G1/G2 reading of the rival gate are **original to this
session**. Their novelty is **not established**. The window statement in particular is
probably known in the language of positive Toeplitz forms.
