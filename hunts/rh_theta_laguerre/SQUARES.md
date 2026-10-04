# Exact square constructions: two candidates tested on the full theta kernel

**RH remains unresolved.** Two concrete square constructions were developed
and both fail for the actual theta kernel. The failures concern those
representations, not the signs of the Laguerre expressions themselves.
In particular, no negative L_n[Xi] and no off-critical zeta zero were found.

The status is ordinary derivations plus finite Arb-enclosed witnesses,
including theta and integration tails. The mathematics has not been externally
reviewed or checked by a proof kernel. Two Arb precisions are not two
independent interval libraries. mpmath provides a separate floating-point
cross-check. No external literature search or novelty claim is made.

## 1. Exact target, with no truncated kernel in the argument

Use the full even theta kernel from RESULTS.md:

    k(u)=2 Phi(u/2)>0,
    Xi(t)=integral_R k(u) exp(itu) du,
    K_n(x)=1/(2(2n)!) integral_R
           k((x-w)/2) k((x+w)/2) w^(2n) dw.

The exact identities are

    L_n[Xi](t)=integral_R K_n(x) exp(itx) dx,
    K_0=k*k,  Fourier(K_0)=Xi^2.

Here L_n is the coefficient of y^(2n) in |Xi(t+iy)|^2. Checkpoint 1 states
and proves the equivalence of all-order, all-real-t nonnegativity with RH,
including the correspondence to the original zeta zeros. That positivity
is not assumed below. The full modular identity supplies k(-u)=k(u).
Numerical truncation is allowed only with its error included where a sign
is claimed from an enclosure.

## 2. Candidate A: cancel the moment weight by integration by parts

Set r(u)=-k'(u)/k(u), the odd logarithmic derivative, and write

    v=u-x,  w=u+v,  S=r(u)+r(v),
    A_n(u,v)=w^(2n)/S,  D=partial_u+partial_v.

Where this quotient is defined or has a removable extension,

    B_n := D A_n
         =4n w^(2n-1)/S-w^(2n)(r'(u)+r'(v))/S^2.           (1)

Since D(k(u)k(v))=-S k(u)k(v), the EXACT finite-interval identity is

    integral_a^b w^(2n) k(u)k(u-x) du
      = integral_a^b B_n(u,u-x) k(u)k(u-x) du
        - [A_n(u,u-x) k(u)k(u-x)]_a^b.                    (2)

No boundary term has been dropped. To take a,b to infinity one must establish
that the quotient extends across every encountered zero of S, that the
integrals converge, and that the displayed boundary term vanishes. Global
monotonicity of r is not assumed as an unproved property of the theta kernel.
The candidate already fails a necessary Gram condition locally, before
those global obligations would matter.

Why try (2)? If B_n admitted a positive Gram representation
B_n(u,v)=integral g_a(u) conjugate(g_a(v)) dnu(a), nu>=0, with justified
integrability, its contribution would become

    1/(2n)! integral |Fourier(k g_a)(t)|^2 dnu(a),

a genuine integral of squares. Merely B_n(u,u)>=0 would not suffice; every
finite Gram matrix must be positive semidefinite.

### 2.1 The construction succeeds exactly for a Gaussian control

For k(u)=exp(-a u^2/2), a>0, r(u)=a u. The removable extension gives

    A_n=w^(2n-1)/a,
    B_n=2(2n-1) w^(2n-2)/a,
    K_n=K_(n-1)/(an),
    L_n[f](t)=f(t)^2/(a^n n!),  f=Fourier(k).               (3)

The boundary terms vanish by Gaussian decay. Equation (3) works at every
order and is a square, not a finite sign experiment. This is a control
calculation, not a substitution of a Gaussian for the zeta kernel.

### 2.2 An exact two-point obstruction for the proposed Gram kernel

For n=1, evaluate B=B_1 at the two points h and -h. Assume r(h)!=0 and
r'(h)>0. Oddness of r gives the removable cross-diagonal value

    B(h,-h)=B(-h,h)=2/r'(h),
    B(h,h)=B(-h,-h)=4h/r(h)-2h^2 r'(h)/r(h)^2.

The smaller eigenvalue of this 2 by 2 matrix is EXACTLY

    B(h,h)-B(h,-h)
       = -2(h r'(h)-r(h))^2 / (r(h)^2 r'(h)).              (4)

It is strictly negative unless h r'(h)=r(h). Thus this pointwise Gram
construction is Gaussian-rigid on any symmetric neighborhood where
r'>0: positivity would force (r(h)/h)'=0 and hence a linear score.
This does not obstruct other choices of the integration-by-parts term,
other Gram kernels, or positivity after performing the integral.

For the actual theta kernel at h=1/10, Arb enclosures with all omitted
theta terms included give

    r(h) = 1.8964019529449634053...,
    r'(h) = 19.435852649680436226...,
    B(h,h)-B(h,-h)
      in [-6.37004434513108164359479042011189950884734804e-5
          +/- 4.69e-50].                                  (5)

The enclosure is strictly below zero at both 192 and 256 bits. The saved
strings use 45 significant digits, so printed rounding dominates their
widths; they are not claimed to be independent interval implementations.
As a local nonlinearity check, r(u)=a u+b u^3+O(u^5) has enclosed positive
coefficients a=18.7269049295... and b=23.8358229603.... Thus (4) also rules
out this Gram condition in every sufficiently small symmetric neighborhood.

## 3. Candidate B: a positive average of shifted Xi squares

The second construction is nonlocal and avoids dividing by the score. Since
k>0, K_0(x)>0 for every real x. Define the exact conditional-moment ratios

    R_n(x)=K_n(x)/K_0(x)
          = integral_0^infinity w^(2n) p_x(w) dw
            / ((2n)! integral_0^infinity p_x(w) dw),
    p_x(w)=k((x-w)/2) k((x+w)/2).                           (6)

The half-line form uses the evenness in w of the product. Suppose one could
construct a finite positive measure mu_n satisfying

    R_n(x)=integral_R exp(isx) dmu_n(s).                    (7)

Then Fubini, using the integrability of K_0 and the finite measure, gives

    L_n[Xi](t)=integral_R Xi(t+s)^2 dmu_n(s) >= 0.           (8)

This is an exact all-order square template. Equation (7) is the unproved
construction step, not an assumption used to announce RH. Bochner's theorem
identifies it with positive definiteness of the continuous R_n. Necessity
alone is elementary: (7) implies

    sum_(i,j) c_i conjugate(c_j) R_n(x_i-x_j)
      = integral |sum_i c_i exp(is x_i)|^2 dmu_n(s) >= 0.   (9)

### 3.1 The coarse pass and its failure at finer resolution

A float probe checked 8 by 8 Toeplitz matrices for n=1,2,3, with spacings
1/4 and 1/2, at 35 and 55 decimal digits. All 12 matrices had positive
minimum eigenvalues. That is preserved in squares_results.json, not
rewritten as a negative result. It did not prove (7).

A finer order-one matrix, 24 points at spacing 1/10, had 7 measured negative
eigenvalues. The minimum was about -1.571730889e-6 after normalization by
R_1(0). A rounded eigenvector at scale 1000 failed to preserve the negative
sign and was rejected. The following scale-10000 INTEGER vector did:

    c = (627, -2154, 1692, 1729, -1773, -2321, 1223, 3028,
         -52, -3258, -1433, 2691, 2691, -1433, -3258, -52,
         3028, 1223, -2321, -1773, 1729, 1692, -2154, 627),
    sum c_i^2 = 99984942,  x_i=i/10,  0<=i<24.

The decisive check uses this fixed vector, not numerical eigenvalue signs.
At 192 bits, enclosing the actual infinite-kernel ratios gives

    Q := sum_(i,j) c_i c_j R_1((i-j)/10)
          / (99984942 R_1(0))
       in [-1.5405042018696452776016e-6 +/- 4.79e-29].       (10)

A 128-bit run also gives a strictly negative interval. Reconstructing Q
from the serialized ratio enclosures remains strictly negative. Therefore
(7) is false already for n=1 for this actual kernel, conditional on the
stated analytic bounds and correctness of the Arb implementation.

This excludes the specific positive-average construction (8): Fourier
uniqueness and K_0(x)>0 would force the multiplier of any such finite
positive measure to equal R_1. It does NOT say L_1[Xi] is negative. A
positive-definite K_1 can have a quotient K_1/K_0 that is not positive
definite. Division by a positive-definite kernel does not preserve the
property.

### 3.2 Control for that implication direction

The distinction is mathematical, not just a disclaimer. In the broader
class of real entire Fourier transforms, take

    k_b(u)=exp(-u^2/2) cosh(bu),  b^2=log(6).

Its Fourier transform is a nonzero constant times exp(-t^2/2) cos(bt),
with only real zeros. Its full Laguerre hierarchy is nonnegative, since
both factors' squared moduli have nonnegative coefficients in y^2.
A direct Gaussian integral instead gives

    R_1(x)=1+2b^2 exp(b^2)/(cosh(bx)+exp(b^2)),
    R_1''''(0)=-12(log(6))^3/343 < 0.

For points -h,0,h and vector (1,-2,1), the Gram quadratic form is
6R_1(0)-8R_1(h)+2R_1(2h)=R_1''''(0)h^4+O(h^6), negative for small h.
Thus the ratio condition can fail even when every required Laguerre sign
holds. This Gaussian control has order two, not the order-one zeta
normalization; it is an implication-direction control, not a rival sharing
all of zeta's hypotheses.

## 4. How the enclosures include the infinite kernel

These computations do not repeat the unchecked truncation step rejected in
checkpoint 1. Here every omitted contribution enters an explicit error bound.

### 4.1 Score derivatives

For u>=0, set a_n=pi n^2, X_n=a_n exp(2u). A summand of k is

    k_n(u)=exp(u/2) (4X_n^2-6X_n) exp(-X_n).

Define rational-coefficient polynomials

    P_0(X)=4X^2-6X,
    P_(j+1)(X)=(1/2-2X)P_j(X)+2X P_j'(X).

Then k_n^(j)(u)=exp(u/2)P_j(X_n)exp(-X_n). If P_j has degree p and
C_j is the sum of the absolute values of its coefficients, then for X>=1,
|P_j(X)|<=C_j X^p. With N retained terms put

    X_*=pi (N+1)^2 exp(2u),
    q=((N+2)/(N+1))^(2p) exp(-pi exp(2u)(2N+3)).

The ratio of consecutive majorant terms for n>N is at most q. When q<1,
the entire omitted derivative tail has absolute value at most

    exp(u/2) C_j X_*^p exp(-X_*)/(1-q).                    (11)

The code establishes X_*>=1 and q<1 with outward bounds. It uses N=8 and
includes (11) before computing r and r'. Termwise differentiation is valid
by local uniform convergence of the theta sum. The central cubic coefficient
uses exact evenness and b=-k''''(0)/(6k(0))+k''(0)^2/(2k(0)^2).

### 4.2 Uniform theta-tail and integration-tail bounds for (10)

Write S_2=sum_(n>=1) a_n^2 exp(-a_n). A finite sum plus the same geometric
tail at p=2 proves 4S_2<2. For u>=0, the upper bound
4a_n^2 exp(9u/2-a_n exp(2u)) decreases with u, because a_n>=pi>9/4.
Consequently

    0<k(u)<2,
    0<=k(u)-k_N(u)<=epsilon_N:=4 sum_(n>N) a_n^2 exp(-a_n), (12)

where epsilon_N is enclosed by the geometric tail, not left as an infinite
unevaluated number. The same sum also gives

    k(u)<=2 exp(pi) exp(9u/2-pi exp(2u)).                   (13)

For real 0<=x<=W and w>=W, apply (13) to (w+x)/2 and k<2 to the other
factor, using evenness. This gives

    p_x(w)<=4 exp(pi) exp(9w/4-pi exp(w))
           <=C_W exp(-lambda_W(w-W)),
    C_W=4 exp(pi+9W/4-pi exp(W)),
    lambda_W=pi exp(W)-9/4>0.

Here exp(w-W)>=1+(w-W) supplies the last inequality. Hence the omitted
integration tails for the zeroth and second moments are at most

    T_0=C_W/lambda_W,
    T_2=C_W(W^2/lambda_W+2W/lambda_W^2+2/lambda_W^3).        (14)

On [0,W], positivity and (12) bound the product error by 4epsilon_N. Thus
the finite-interval theta errors are at most 4epsilon_N W and
4epsilon_N W^3/3 for the zeroth and second moments respectively.

The computation uses N=8, W=4. Arb integrates the finite sums separately
on [0,x] and [x,4], reflecting the negative argument by the EXACT evenness
of the full kernel. Each finite-sum callback is analytic; no absolute value
or real-part projection is applied to its complex integration argument.
One complex integral carries both real moments via the factor 1+i w^2.
For conditioning only, both integrands and all error bounds are divided
by the same positive k_N(x/2)^2. This cancels from the final ratio.
The errors in (12)-(14) are added before division. Every denominator is
proved positive by its enclosure. The fixed quadratic form then uses only
integer coefficients and interval arithmetic.

## 5. Reproduction and independent checks

From the repository root:

    .venv/bin/python hunts/rh_theta_laguerre/squares.py
    .venv/bin/python hunts/rh_theta_laguerre/ratio_witness.py
    .venv/bin/python -m pytest -q -n0 hunts/rh_theta_laguerre/test_squares.py

The first script completed in 3.373 seconds: two score enclosures, 72
floating conditional ratios, and 12 coarse Gram matrices. The witness
script completed in 0.316 seconds: 48 ratio enclosures and two strictly
negative quadratic-form enclosures, zero failed checks. The saved artifacts
contain the raw values, precision, cutoffs, and each ratio's error bounds.

The 16 continuation tests check the arbitrary-order identity, the exact
negative-square formula, the Gaussian recurrence, derivative-polynomial
normalizations, nonzero tails, and the integer witness using a separate
summation by lag. Independent mpmath quadrature at 75 digits, using 12 theta
terms and cutoff 5, lies in the Arb enclosures at x=0,1/2,23/10. Direct
mpmath derivatives using 16 theta terms check the score enclosures.
The coarse positive matrices remain in the record alongside their finer
negative witness. None is represented as a global positivity test.

Dependencies: the full theta Mellin representation and modular symmetry
from checkpoint 1, ordinary differentiation/integration by parts, Fourier
convolution and uniqueness, and finite-measure Fourier positivity. Bochner's
theorem explains the candidate equivalence but is not needed to verify the
negative quadratic form. Enclosure claims additionally rely on python-flint's
Arb quadrature and arithmetic, plus the explicitly derived tails above.

## 6. What remains open

No sum-of-squares representation for the actual complete hierarchy was
obtained. The local score-cancellation Gram ansatz and the shift-only
positive-average ansatz are now specifically refuted. Their failure does
not imply RH is false or impossible. It also does not prove that K_1 or any
other K_n lacks a different positive Gram representation.

A further construction must allow more freedom than a pointwise Gram
factorization of (1), or than one positive spectral multiplier of K_0.
The negative R_1 witness is a necessary challenge for a proposed replacement:
it must not quietly reimpose that disproved multiplier condition. No such
replacement is supplied by this checkpoint. More computation of positive
coarse matrices would not repair either invalid construction.
