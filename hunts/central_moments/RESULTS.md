# Central logarithmic moments: first checkpoint

**RH remains unresolved.** This is an ordinary derivation, exact rational
controls, a bounded numerical experiment, and eight finite matrix signs
checked with Arb enclosures. No external proof review or formal proof was performed.
No novelty is claimed. The control below defeats a proposed generic positivity
transfer, not the possibility of exploiting the particular arithmetic theta sum.

## Route selection and statement check

The target is exactly: if zeta(s)=0 and 0<Re(s)<1, then Re(s)=1/2.
Define

    xi(s) = s(s-1) pi^(-s/2) Gamma(s/2) zeta(s) / 2,
    F(w) = xi(1/2 + sqrt(w)) / xi(1/2).

The functional equation makes F single-valued and entire: its definition is
the even power series, not a choice of square-root branch. xi's zeros are
exactly the nontrivial zeros of zeta, including multiplicity. Consequently
RH says exactly that every zero of F lies on the negative real axis.
For a zero rho, w=(rho-1/2)^2 is negative real precisely when
Re(rho)=1/2 and Im(rho) is nonzero. The central point is not a zero.
No extra axiom or zero-location hypothesis enters this dictionary.

Three mechanisms were considered: signed arithmetic cancellation (whose prior
record retains a square-root error gap), theta Fourier real-rootedness, and
central logarithmic moment positivity. This pass chose the last because its
quantities can be computed without supplying presumed critical-line zeros,
and its candidate inequalities admit exact controls. This is a choice of a
bounded experiment, not evidence that it is the best route to RH.

## 1. Derivation from theta

Let omega(x)=sum_{n>=1} exp(-pi n^2 x), f(u)=exp(u) omega(exp(4u)), and

    Phi(u) = sum_{n>=1} (2 pi^2 n^4 exp(9u) - 3 pi n^2 exp(5u))
                         exp(-pi n^2 exp(4u)),  u>=0.

The classical theta Mellin formula gives, with s=1/2+z,

    xi(1/2+z) = 1/2 + (4z^2-1) integral_0^infinity f(u) cosh(2zu) du.

Direct differentiation gives f''-f=8 Phi. Differentiating the theta modular
identity theta(x)=x^(-1/2)theta(1/x) at x=1 gives f'(0)=-1/2.
Two integrations by parts therefore give

    xi(1/2+z) = 8 integral_0^infinity Phi(u) cosh(2zu) du.       (1)

All boundary terms at infinity vanish, and differentiation and integration
are justified locally uniformly in z by the double-exponential decay.
At u>=0 each summand is positive because 2 pi n^2 exp(4u)>3.
Thus xi(1/2)>0. Write I_k=integral u^(2k) Phi(u) du. Then

    F(w) = sum_{k>=0} a_k w^k,
    a_k = 4^k I_k / ((2k)! I_0),  a_0=1.                     (2)

This derives the factor of 4; it is also checked numerically against direct
central derivatives, without using the heatflow module's normalization.

## 2. The exact missing positivity

Define m_n by the convergent local expansion

    F'(w)/F(w) = sum_{n>=0} (-1)^n m_n w^n.

Let b_n=(-1)^n m_n. Multiplication of power series gives

    b_n = (n+1)a_(n+1) - sum_{k=1}^n a_k b_(n-k).             (3)

The matrices to establish as positive semidefinite, for EVERY r>=1, are

    H_(r,0) = (m_(i+j))_(0<=i,j<r),
    H_(r,1) = (m_(i+j+1))_(0<=i,j<r).                       (4)

For the actual F, positivity of all these matrices is equivalent to RH.
Here is the dependency-explicit argument, not a proof of their positivity.

Forward: under RH, the entire function F has order 1/2, so its Hadamard
factorization has genus zero and no nonconstant exponential factor:

    F(w)=product_j (1+w/gamma_j^2),
    m_n=sum_j gamma_j^(-2n-2).

The positive ordinates are counted with multiplicity. The sums converge.
These are moments of the finite positive measure
sum_j gamma_j^(-2) delta_(gamma_j^(-2)). A quadratic form in (4) is
the integral of p(t)^2 or t p(t)^2 against this measure and is nonnegative.
RH is used here only to prove this direction of an equivalence.

Reverse: suppose all matrices (4) are positive semidefinite. The classical
Stieltjes moment existence theorem gives a positive measure mu on [0,infinity)
with moments m_n. F'/F is analytic in a disk about zero. Cauchy's estimates
give |m_n|<=C R^(-n) for any fixed sufficiently small R>0. The measure has
support in [0,1/R]: any mass beyond L>1/R would force m_(2n)>=c L^(2n),
contradicting the estimate. Thus

    F'(w)/F(w) = integral_[0,1/R] (1+tw)^(-1) dmu(t)          (5)

near zero. The right side is analytic off the negative real axis. The identity
principle, applied to meromorphic functions on that connected slit plane,
implies F'/F has no poles there. Every zero of F creates a pole of F'/F with
positive integer residue; cancellation cannot remove it. Hence all zeros of
F are negative real, which is the original RH by the dictionary above.
This argument does NOT assume (4) has been proved. That is its open step.

Dependencies: analytic continuation and functional equation for xi, the theta
Mellin identity and modular identity, the order-one growth of xi, Hadamard
factorization for an entire function of order below one, the Stieltjes moment
existence theorem, Cauchy's estimates, and the identity principle. These are
classical results, not newly proved dependencies of this checkpoint.

Related primary literature: Masatoshi Suzuki,
[Aspects of the screw function corresponding to the Riemann zeta-function](https://doi.org/10.1112/jlms.12785),
Theorem 1.8 and section 7.3, supplies a different Hankel moment criterion.
His moments are not the m_n used here. Its cited classical moment reference
is M. G. Krein and A. A. Nudelman, *The Markov Moment Problem and Extremal
Problems*, Chapter V, section 1. This establishes relevant prior art, not
novelty or a complete literature review for the present formulation.

### A reduction specific to the known sign of F on the positive axis

The shifted family H_(r,1) is actually redundant for this F. It is enough
to prove H_(r,0) positive semidefinite for every r. This observation reduces
the open obligation; it does not establish it.

Proof: the Hamburger moment existence theorem, using just H_(r,0), supplies
a positive measure on the whole real axis with moments m_n. The same even
moment bound used above confines its support to [-1/R,1/R]. Its transform
integral (1+tw)^(-1) dmu(t) agrees locally with F'/F. It is analytic on each
of the upper and lower half-planes, so meromorphic continuation excludes
every nonreal zero of F. Equation (2) gives F(w)>0 for real w>=0, excluding
the remaining unwanted zeros. Therefore all zeros are negative real, hence
RH. The converse is the positive-measure argument already given. The extra
dependency is the classical Hamburger moment existence theorem. Positive
semidefiniteness of every matrix is the condition here, not merely
nonnegative leading determinants in potentially singular finite matrices.

The raw theta positivity thus does real work: it excludes positive real
zeros of F and eliminates one matrix family from the sufficient criterion.
It still does not prove positivity of the unshifted matrices. The shifted
matrices remain useful additional numerical diagnostics and controls.

## 3. Attempted positivity transfer and exact failure

Positive Phi proves positivity of the raw moment matrices of I_k. Equation
(3) involves subtractions, so that fact alone does not prove (4). In detail,

    m_0=a_1,
    m_1=a_1^2-2a_2,
    m_2=a_1^3-3a_1 a_2+3a_3,
    det H_(2,0)=a_1^2 a_2+3a_1 a_3-4a_2^2.                 (6)

For the symmetric probability distribution with X=+/-2u induced by Phi,
write mu_k=E[X^k]. Then (6) is

    det H_(2,0) = (15 mu_2^2 mu_4+3 mu_2 mu_6-10 mu_4^2)/1440.

Ordinary moment Cauchy-Schwarz only gives mu_2 mu_6>=mu_4^2;
it does not establish the displayed inequality. The following exact control
shows that generic symmetric positive-measure structure is insufficient.

For c>1 set F_c(w)=(c+cosh(sqrt(w)))/(c+1). This is the moment generating
function in sqrt(w) of masses c/(c+1) at 0 and 1/(2(c+1)) at +/-1.
It is entire of order 1/2 in w, normalized at zero. Its zeros obey

    sqrt(w) = +/-acosh(c) + (2k+1) pi i,

so it has zeros off the negative real axis. Direct rational algebra gives

    m_1=(2-c)/(12(c+1)^2),
    det H_(2,0)=(8-7c)/(1440(c+1)^3).

At c=6/5, m_1>0 but det H_(2,0)=-5/191664<0. Thus even the first
nontrivial scalar sign does not imply the next matrix condition.
This is a counterexample to the proposed transfer, not a zeta counterexample.
It has no Euler product or the specific arithmetic theta kernel.

## 4. Why arbitrarily many finite positive tests can still mislead

There is a stronger, precisely scoped observation. For every fixed matrix
size bound M, some c>1 makes both families (4) positive definite through M,
while F_c still has the off-axis zeros just described.

Proof: at c=1, F_1(w)=cosh(sqrt(w)/2)^2. Its negative real zeros are
-pi^2(2j+1)^2, j>=0, with multiplicity two. The classical cosh product gives

    m_n(1)=2 sum_(j>=0) [pi^2(2j+1)^2]^(-n-1).

The corresponding positive moment measure has infinitely many distinct
positive support points. Every nonzero polynomial has only finitely many
zeros, so the integrals of p^2 and t p^2 are strictly positive. All finite
matrices at c=1 are therefore positive definite. For finitely many sizes,
their finitely many leading principal determinants stay positive in a
common neighborhood of c=1 by continuity. Choose c>1 in that neighborhood.
Sylvester's criterion proves the claim. This proof is an ordinary derivation
awaiting outside review; it is not a theorem about finite information of
every kind, nor does it close the theta-specific route.

The exact bounded search in probe.py finds c=1000000001/1000000000 passing
all eight leading determinants for sizes 1 through 4 and shifts 0 and 1.
The rational values are saved in results.json. The search stops at its first
successful value among c=1+10^(-k), 1<=k<=24; no optimality is claimed.
Both size-five determinants for this same c are strictly negative; their
exact values are in control_extension.json and the independent checker
verifies them. Thus this control also checks that the detector eventually
reports a violation, rather than being programmed to report positive signs.
For this near-one c, acosh(c)<1/2, so the associated zeros in the s-plane
all lie inside 0<Re(s)<1 and off its central line. This follows, without
rounding, from c<1+1/8<cosh(1/2). These remain zeros of a control function,
not zeros of zeta.

## 5. Reproduction and next obligation

Run from the repository root with its installed dependencies:

    .venv/bin/python hunts/central_moments/probe.py
    .venv/bin/python hunts/central_moments/ball_check.py
    .venv/bin/python hunts/central_moments/check_exact.py

The probe computes a_0 through a_8 by direct derivatives of the gamma-zeta
formula and independently by theta quadrature. It compares m_0 through m_7
and eight determinants at 50 and 80 decimal digits. Determinants are scaled
using m_n/m_0^(n+1); this is a positive diagonal congruence times a positive
scalar for each matrix, so it preserves their signs.
The theta sum uses 12 terms and quadrature ends at u=2. Numerical agreement
checks this truncation empirically; no interval error bound is supplied.
These calculations use no list of critical-line zeros and cannot acquire
RH by silently omitting hypothetical off-line zeros.

Observed maximum relative differences between the two moment routes are
4.61716e-48 at 50 decimal digits and 4.72664e-78 at 80 decimal digits.
All eight tested matrices have positive leading determinants in both runs.

A third computation, ball_check.py, uses Arb power series for zeta, gamma,
and the exponential, followed by power-series division and an explicit
permutation-sum determinant. Every arithmetic step carries an enclosure.
At 256 and 384 bits, all eight determinant enclosures lie strictly above
zero, including after serialization. It does not use theta truncation or
numerical derivatives. The checker recomputes determinants from the saved
moment enclosures using Arb's separate matrix-determinant implementation.
The scaled size-four determinants at 384 bits are enclosed by

    H_(4,0): [1.78524390367089248283527244328937525251018665e-15 +/- 3.92e-60]
    H_(4,1): [4.91649526287125458705619910684065688654798195e-21 +/- 4.20e-66].

These are finite sign enclosures conditional on the correctness of the
Arb implementation and the supplied formulas, not a uniform claim about
all matrix sizes. The two Arb precisions are precision-response checks,
not two independent arithmetic libraries. The independent mpmath formulas
provide a separate floating-point cross-check, not interval coverage of
the theta quadrature.

The remaining mathematical task is to prove the unshifted part of (4) at ALL orders using the
specific theta/arithmetic structure, or to find a rigorously negative matrix
for the actual xi. Neither is established here. Increasing the finite matrix
cutoff alone is not the next proof step, as the exact control demonstrates.
The constructive obligation is a theta-specific representation of each
quadratic form as nonnegative terms, with every remainder included. No such
representation has yet been obtained. The attempt is unresolved, not a
proof that this route or RH is impossible.
