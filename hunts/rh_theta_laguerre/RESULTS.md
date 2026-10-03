# Theta sums and Laguerre inequalities: first checkpoint

**RH is unresolved. No proof or disproof is claimed.** This checkpoint gives
ordinary proofs of two scoped intermediate statements, exact algebra checks,
and bounded floating-point comparisons. The proofs have not been externally
reviewed or checked by a proof kernel. No novelty is asserted, and no external
literature search for these constructions was conducted.

1. Every fixed finite partial sum of the half-line theta kernel has a cosine
   transform that eventually violates the first Laguerre inequality. It has
   infinitely many nonreal zeros. This concerns those approximants, not Xi.
2. For any fixed finite order cutoff K, an explicit six-atom positive-measure
   transform satisfies all Laguerre inequalities through K on the WHOLE real
   axis and still has nonreal zeros inside the corresponding critical strip.
   For K=1 it fails the second inequality exactly. This is a uniform
   construction, not a finite point scan.

Neither conclusion closes the theta route. The unresolved task is to prove
all the necessary inequalities for the actual infinite arithmetic kernel,
or find a rigorously negative one for that kernel.

## 1. Target and statement correspondence

Use the standard completion and critical-line variable:

    xi(s) = s(s-1) pi^(-s/2) Gamma(s/2) zeta(s) / 2,
    Xi(t) = xi(1/2 + it).

Xi is a real even entire function of order one, with Xi(0)>0. Its zeros
correspond, with multiplicity, to the nontrivial zeros of zeta. Explicitly,
if rho=beta+i gamma then the corresponding t is

    t = gamma - i(beta-1/2).

Thus RH is exactly that every zero of Xi is real. This includes multiple
zeros and asserts neither simplicity nor a spacing law. No zero list is
supplied to the computations. This paragraph is an informal statement
comparison with the original problem, not a formal-statement audit of a
Lean encoding. No formal resolution artifact was produced.

Three mechanisms were compared before selecting this trial: central moment
positivity (the prior checkpoint retains an all-matrix-size gap), arithmetic
log-derivative positivity (the prior record retains a uniform cancellation
gap), and theta-transform inequalities. The third gives an explicit
approximation step that can be checked analytically, not just by extending a
finite scan. The other records are not assumed to obstruct their routes.

## 2. Which inequalities would actually suffice

For a real entire f define L_n[f](x) by the entire expansion in y

    f(x+iy) f(x-iy) = sum_(n>=0) L_n[f](x) y^(2n),
    L_n[f](x) = (-1)^n sum_(j=0)^(2n)
        (-1)^j f^(j)(x) f^(2n-j)(x) / (j! (2n-j)!).          (1)

For real y the left side is |f(x+iy)|^2. In particular,

    L_0=f^2,  L_1=(f')^2-ff'',
    L_2=ff''''/12-f'f'''/3+(f'')^2/4.

For Xi, RH is equivalent to

    L_n[Xi](x) >= 0 for every real x and every n>=0.          (2)

Here is the dependency-explicit equivalence, not a proof of (2).

**RH implies (2).** Under RH, paired Hadamard factorization gives
Xi(z)=Xi(0) product_(gamma>0)(1-z^2/gamma^2), with multiplicities.
The sum of gamma^(-2) converges. Each finite factor satisfies

    |1-(x+iy)^2/gamma^2|^2
      = ((gamma^2-x^2)^2+2(gamma^2+x^2)y^2+y^4)/gamma^4.

All its coefficients in y^2 are nonnegative. Finite products retain this
property. The products converge locally uniformly, so their Taylor
coefficients converge and are nonnegative. RH is assumed only in this
necessary direction, not as an input to the attempt to establish (2).

**(2) implies RH.** If f=Xi had a nonreal zero x+iy with real y!=0,
all nonnegative terms in (1) would sum to zero. But some coefficient is
strictly positive: if f has a zero of finite multiplicity m at x, the first
nonzero coefficient is L_m=(f^(m)(x)/m!)^2>0; if f(x)!=0, L_0>0.
A nonzero entire function cannot have an infinite-multiplicity zero.
This contradicts the proposed nonreal zero. No growth hypothesis is needed
for this direction.

Dependencies of this equivalence: the classical analytic continuation,
functional equation and order of xi, its zero correspondence, Hadamard
factorization paired using evenness, and elementary power-series facts.
The inequality is the unproved part, not an extra axiom being adopted.

## 3. The finite theta approximation fails at infinity

Write, for u>=0 and a_n=pi n^2,

    phi_n(u)=(2 a_n^2 exp(9u)-3 a_n exp(5u)) exp(-a_n exp(4u)),
    Phi_N(u)=sum_(n=1)^N phi_n(u),
    H_N(z)=integral_0^infinity Phi_N(u) cos(zu) du.

For the full sum Phi, the classical theta Mellin identity gives

    H(z)=integral_0^infinity Phi(u) cos(zu) du = Xi(z/2)/8.   (3)

The scale matters: an ordinate in the H variable is twice its Xi ordinate.
All statements below concerning H_N are about the approximation, never the
actual Xi. The numerical normalization check uses (3).

### 3.1 The exact boundary cancellation lost by every finite N

Let omega(x)=sum_(n>=1) exp(-pi n^2 x) and f(u)=exp(u)omega(exp(4u)).
Direct differentiation gives f''-f=8 Phi. The theta modular identity implies

    f(-u)=f(u)+sinh(u).

Applying D^2-1 shows Phi(-u)=Phi(u), hence Phi'(0)=0. The sums and their
real derivatives converge locally uniformly near u=0, justifying this
calculation term by term. In fact every odd derivative of Phi at zero
vanishes, although the first is enough here.

Direct differentiation of one term gives

    phi_n'(0)=a_n(-8a_n^2+30a_n-15) exp(-a_n).               (4)

For n>=2, a_n>=4pi>12. For a=12+v, v>=0, the polynomial in brackets is

    -8a^2+30a-15 = -807-162v-8v^2 < 0.

Consequently, for EVERY integer N>=1,

    d_N := Phi_N'(0) = -sum_(n>N) phi_n'(0) > 0.            (5)

This strict sign is an infinite-sum deduction from modularity and the signs
of all omitted terms, not an inference from a finite computation of d_N.

### 3.2 Remainder-carrying asymptotics

Fix N and put phi=Phi_N, d=d_N. Every derivative of phi and every
polynomial times such a derivative is integrable and vanishes at infinity,
by its double-exponential decay. Repeated integration by parts gives, for
real t>0,

    H_N(t)  = -d/t^2  + r_0(t),  |r_0(t)| <= A_0/t^4,
    H_N'(t) =  2d/t^3 + r_1(t),  |r_1(t)| <= A_1/t^5,
    H_N''(t)= -6d/t^4 + r_2(t),  |r_2(t)| <= A_2/t^6,       (6)

with finite, explicitly defined constants

    A_0 = |phi'''(0)| + integral_0^infinity |phi''''(u)| du,
    A_1 = |(u phi)''''(0)| + integral_0^infinity |(u phi)'''''(u)| du,
    A_2 = |(u^2 phi)'''''(0)| + integral_0^infinity |(u^2 phi)''''''(u)| du.

These derivative expansions follow by applying integration by parts to the
integrals for each derivative, not by differentiating an uncontrolled
big-O remainder. For example,

    H_N(t)=-phi'(0)/t^2+phi'''(0)/t^4
              +t^(-4) integral phi''''(u) cos(tu) du.

Expanding the curvature, with no term discarded, now gives

    L_1[H_N](t) = -2d^2/t^6 + E_N(t),
    |E_N(t)| <= B_1/t^8 + B_2/t^10,                         (7)
    B_1=d(4A_1+A_2+6A_0),  B_2=A_1^2+A_0 A_2.

In particular it is strictly negative for

    t > max(1, sqrt((B_1+B_2)/d^2)).                        (8)

The constants in (8) were not numerically evaluated; the measured points
below are not asserted to satisfy that sufficient bound. Equations
(5)-(8) prove eventual failure for each fixed N, with no uniform-in-N
threshold claimed. Increasing N can delay the failure, not eliminate it.

### 3.3 Infinitely many nonreal zeros of each approximant

H_N is nonzero and entire, by locally dominated differentiation under the
integral; it is even and H_N(0)>0. Bounding its integrand by
C_N exp((9+|z|)u-pi exp(4u)) and substituting v=pi exp(4u) gives

    log max_(|z|<=r) |H_N(z)| = O_N(r log(r+2)).

Thus its order is at most one. By (6), H_N(t)<0 for all sufficiently large
real |t|, so it has only finitely many real zeros. If it had only finitely
many zeros altogether, Hadamard factorization would give
H_N(z)=exp(az+b)P(z). Its zeros come in opposite pairs, so P may be chosen
even. Evenness of H_N then forces a=0. That would make H_N a polynomial,
inconsistent with its nonzero t^(-2) decay along the real axis. Therefore
it has infinitely many nonreal zeros.

This is a restricted approximation-family obstruction. The H_N converge to
H locally uniformly, together with derivatives, by dominated convergence.
Nonreal zeros of the approximants can escape compact sets. No implication
from their nonreal zeros to nonreal zeros of H has been claimed.

## 4. Even global first-order positivity is insufficient

Consider the explicitly normalized real even entire function

    C(z) = ((17/16)+cos(z)) cos(4z) / (33/16)
         = (17 cos(4z)+8 cos(5z)+8 cos(3z))/33.              (9)

It is the Fourier transform of a positive probability measure: masses
17/66 at each of +/-4, and 4/33 at each of +/-3 and +/-5. It has order one,
C(0)=1, and C(iu)>0 for real u. Its positive even moment structure is
therefore genuine, not chosen independently of the function.

Put c=17/16, v=1+cos(t)>=0, q=cos(4t). The product identity for L_1 gives

    (c+1)^2 L_1[C](t)
      = q^2(1+c cos(t))+16(c+cos(t))^2
      = (1-q^2)/16 + v(2+17q^2/16) + 16v^2 >= 0           (10)

for EVERY real t, with equality at t=pi.

Nevertheless C has zeros

    z=(2k+1)pi +/- i alpha,
    alpha=acosh(17/16)=log((17+sqrt(33))/16)>0,

as well as the real zeros of cos(4z). Since
cosh(1/2)>1+1/8>17/16, we have alpha<1/2 exactly. Thus all its zeros lie in
|Im z|<1/2, the strip that corresponds to 0<Re s<1 under s=1/2+iz, but
some are not real. They are zeros of the control function, NOT of zeta.

The next condition detects this control without approximating its zeros:

    C(pi)=1/33, C'(pi)=C''(pi)=C'''(pi)=0,
    C''''(pi)=-432/11,
    L_2[C](pi)=-12/121 < 0.                                (11)

The exact algebra checker verifies (10) and (11). This refutes only the
specified generic sufficiency claim. The control has no zeta Euler product
or exact arithmetic theta kernel, so it does not refute a proof that uses
those additional properties. No standing rival is claimed to be excluded;
this construction itself matches every hypothesis of the implication being
challenged.

### 4.1 Strengthening: any fixed finite number of orders can pass globally

The control extends beyond first order. For an integer K>=1 let M=4K and

    C_K(z)=(c+cos(z)) cos(Mz)/(c+1),  c=17/16.               (13)

It has the same positive weights as (9), now at frequencies M,M-1,M+1,
and the same explicit nonreal zeros with |Im z|=alpha<1/2. Nevertheless

    L_n[C_K](x)>=0 for every real x and every 0<=n<=K.       (14)

Here is a direct proof. Put delta=c-1=1/16. The coefficients of y^(2j)
in |c+cos(x+iy)|^2 are

    h_0=(c+cos(x))^2 >= delta^2,
    h_1=1+c cos(x) >= -delta,
    h_j=(2c cos(x)+2^(2j-1))/(2j)! > 0 for j>=2.

The last sign follows from 2^(2j-1)>=8>2c. For |cos(M(x+iy))|^2 they are

    q_0=cos(Mx)^2 in [0,1],
    q_j=(2M)^(2j)/(2(2j)!) > 0 for j>=1.

The product coefficient is sum_(j=0)^n h_j q_(n-j), divided by (c+1)^2.
For n=1 its numerator is at least delta^2 M^2-delta=(K^2-1)/16>=0.
For 2<=n<=K it is at least delta^2 q_n-delta q_(n-1), which is
nonnegative since

    delta q_n/q_(n-1)=4K^2/(2n(2n-1)) > 1.

This proves (14), including every real x, without numerical signs.
For concrete checks at x=pi, C_2 fails L_3 with exact value -2806/495,
and C_3 fails L_4 with exact value -407815057/1372140. Both identities
are pinned by exact coefficient convolution and separate numerical derivatives.

The quantifiers matter: for every K there is a DIFFERENT C_K. No one
control passes all orders. Its exponential type grows with K; it has no
arithmetic theta identity or zeta zero-density law. This is not a no-go
for finite reductions that exploit additional properties of Xi. It does
rule out replacing the all-order obligation by an arbitrary fixed cutoff
using only the generic hypotheses these controls share.

## 5. The attempted positive representation and its remaining gap

For the actual Xi, put k(u)=2 Phi(u/2), using the even extension of Phi.
Then Xi(t)=integral_R k(u) exp(itu) du. All exponential moments of k exist.
Expanding the product at t+iy and t-iy, and setting x=u+v, w=v-u, gives

    L_n[Xi](t)=integral_R K_n(x) cos(tx) dx,
    K_n(x)=1/(2 (2n)!) integral_R
        k((x-w)/2) k((x+w)/2) w^(2n) dw.                   (12)

Dominated convergence and the linear change of variables justify the
expansion and its factor 1/2. This derivation keeps the infinite theta sum.
It exposes a concrete constructive target: a positive-definite or
convolution-square representation for EACH K_n, which would prove (2).
No such representation is obtained here.

The apparent shortcut, pointwise K_n>=0, is not Fourier positivity.
Positive kernel mass alone does not control the sign of its cosine
transform. The control in section 4 shows that even recovering the entire
n=1 condition is insufficient. At n=0, K_0=k*k and the Fourier transform
is Xi(t)^2, so that one condition has the required square structure. The
extension to every n is precisely the missing step, not a consequence
being inferred from that base case.

## 6. What was computed, and how to repeat it

From the repository root:

    .venv/bin/python hunts/rh_theta_laguerre/probe.py
    .venv/bin/python -m pytest -q -n0 hunts/rh_theta_laguerre/test_probe.py

The first run finished in 14.344 seconds. For N=1,2,3 and H-arguments
200,400,800, at 50 and 80 decimal digits, it measured 16 negative L_1 values
among 18 evaluations (8 of 9 distinct points). N=3,t=200 remains positive
at both precisions; no asymptotic onset is inferred from those finite points.
The maximum relative change among saved H, L_1 and d_N values under this
precision increase is below 1e-30, as checked by a test.

At N=1,t=800, the ratios tending to -1 and -2 in (6)-(7) are measured as

    t^2 H_N(t)/d_N = -0.9983330308439361...,
    t^6 L_1[H_N](t)/d_N^2 = -1.9833504621609844....

An independent finite-interval theta quadrature checks the incomplete-gamma
route for H_N and its first two derivatives at (N,t)=(1,40),(2,80), six
comparisons. The largest relative discrepancy is below 1.05e-52. Quadrature
ends at u=2; these are float diagnostics, not interval sign proofs. The
ordinary proof of (7) uses no quadrature or numerical tail truncation.

For actual Xi, only t=0,7,20,50 are evaluated, at both precisions: 8/8
positive L_1 values. These are four isolated points, not a zero census,
continuous interval verification, or evidence establishing (2). The control's
nonreal-zero residual is below 2.3e-81 at 80 digits, while its exact negative
L_2 is established algebraically rather than by that residual.

The 17 hunt tests include symbolic endpoint differentiation, the exact
nonnegative decomposition, the rational L_2 failure, a separate polynomial
expansion of (1), the remainder algebra, direct derivative and omitted-tail
comparisons, theta normalization/evenness diagnostics, precision response,
and recomputation of the negative controls. Two additional cross-checks
verify the integration-by-parts identities on an exponential and the
Jacobian/factorial normalization in (12) on a Gaussian. The finite-order
control extension has three further checks of its bound algebra and exact
higher-order failures. These tests do not verify the
entire-function proofs by a kernel or constitute an independent mathematical
review. Dependencies are SymPy and mpmath plus the standard analytic results
named in sections 1-3. No Lean build or paid computation ran.

## The doors

1. **Active constraints:** this is not a measured optimum. In the exact finite-N
   family the first surviving odd endpoint derivative produces an algebraic
   tail of the wrong sign. In the proposed generic implication, stopping at
   any fixed order K leaves the explicit control (13). Neither obstruction
   applies to all representations or to the full arithmetic kernel.
2. **Frozen parameters:** the computations use N=1,2,3, H-arguments
   200,400,800, 50/80 digits, and a separate quadrature cutoff u=2 at 60
   digits. Raising N buys compact-set accuracy and costs cancellation digits;
   it cannot make a fixed raw truncation satisfy all real-axis inequalities.
   Higher precision tests arithmetic stability, not missing hypotheses.
   The control frequencies 3,4,5 and c=17/16 were chosen for an exact
   n=1 equality and n=2 negative witness, not optimized.
3. **Information class:** a modularity-preserving construction or a
   direct argument with the infinite kernel must retain the endpoint
   cancellations rather than truncate them away. Proving nonnegative Fourier
   transforms in (12) would suffice; it is currently unresolved. Corrections
   to approximants might help, but none has been proved here. This is a
   reason to work on the representation, not a claim that no alternative
   estimate or RH proof is possible.
