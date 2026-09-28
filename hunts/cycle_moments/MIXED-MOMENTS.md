# A finite improvement from mixed moments

This note gives a finite counting improvement whose denominator uses a narrow
fourth moment. Its first Montgomery-Taylor profiles do not produce a positive
numerator. The numerical statements below are measured integral evaluations,
not a new zeta proportion. The general finite hypotheses and the operator A are
those of `FINITE-THEOREM.md`, Section 1.

## 1. An exact mixed inequality

Put E = tr(A^2) - 2N + s. Let B be any self-adjoint operator on a finite
dimensional space containing the counting vectors. Define

    J = 3 tr(A B^2) - tr(A^2 B^2) - 2 tr(B^2).

Then, when tr(B^4)>0,

    s >= 2N - tr(A^2) + max(J,0)^2 / [9 tr(B^4)].          (1)

If B=0, use gain zero. No positivity of A or B is assumed.

Proof. Use the adapted subspaces U subset V subset W from the finite theorem,
and set X=2P_U+P_(V intersect U-perp), extended by zero outside W. Its eigenvalues
belong to {0,1,2}. Direct expansion gives

    E - ||A-X||_F^2
      = 2 tr(P_U A) - 2 tr(P_(W intersect V-perp) A)
        - 4 dim U + s - dim(V intersect U-perp)
      >= 0.

The last inequality uses exactly the multiplicity and signed-pair estimates
in the adapted-subspace proof. In particular the negative h contributions have
not been omitted. Write H=A-X and Q=B^2. Both Q and X^2-3X+2I are positive
semidefinite, so

    tr Q(A^2-3A+2I)
      >= tr H(XQ+QX-3Q).

Here tr(QH^2)>=0 was also dropped. In an eigenbasis of X, the matrix entry Q_ij
is multiplied by x_i+x_j-3, whose absolute value is at most 3. Consequently

    J <= 3 ||Q||_F ||H||_F <= 3 sqrt(tr(B^4)) sqrt(E).

Taking the positive part and squaring proves (1). This also proves the more
general statement with any positive semidefinite Q and denominator 9 tr(Q^2).
The same argument using X^2-X>=0 allows the numerator tr Q(A-A^2).

A strict finite example uses two unit simple vectors with Gram eigenvalues
1/2 and 3/2, and no multiple or nonreal vectors. Let R project onto the 3/2
eigenspace and B=RAR. Then N=s=2, tr(A^2)=5/2, J=9/16, tr(B^4)=81/16. Formula
(1) gives 3/2+1/144, strictly improving the second-moment answer 3/2. The
script checks this exact rational calculation numerically as a secondary check.

## 2. Frequency profiles and the support that they actually spend

Let p>=0 be the normalized wide frequency profile, supported inside
(-lambda,lambda). Let r>=0 be supported inside (c-mu,c+mu), a subinterval of the
wide interval, and put q=sqrt(p r). Require r=0 almost everywhere where p=0
and require multiplication by sqrt(r/p) to be defined on the counting
vectors; bounded r/p is a sufficient condition. The tested positive cosine
profiles satisfy it. On the frequency space take R to be multiplication by
sqrt(r/p), and B=R A_p R. A signed real R is also possible:
then r=p R^2 and q=p R. A shifted r need not be even, because (1) accepts
arbitrary self-adjoint B. One may use the complexification of the original
real counting space.

The mixed trace profiles are obtained by multiplying the square-root profiles
at each vertex. They are

    tr(B^2)       : (r,r),
    tr(A B^2)     : (q,r,q),
    tr(A^2 B^2)   : (p,q,r,q),
    tr(B^4)       : (r,r,r,r).

In particular, (p,p,r,r) is not the profile of tr(A_p^2 A_r^2) for these
operators. The cross vertices have profile q.

For a cycle, its zero-side Fourier variables satisfy xi_j=u_j-u_(j-1).
In the mixed fourth cycle only one u is wide; the other three lie in the
narrow interval. Therefore

    sum_j |xi_j| <= 2 lambda + 2 |c| + 6 mu.               (2)

The bound follows by bounding the two edges adjacent to the wide vertex by
lambda+|c|+mu and the other two by 2mu. The all-narrow fourth cycle has bound
8mu. Both quantities must be strictly less than 2. For lambda=.499, the
central choices mu<=.16 satisfy this support check. Two separated symmetric
bumps spend their entire combined support; their individual widths cannot be
inserted into (2).

[Rudnick and Sarnak, Theorem 3.1, equations (3.8)-(3.9)](https://www.math.tau.ac.il/~rudnick/papers/nlevelDuke.pdf)
gives an unconditional all-index formula with these support restrictions.
It permits nonsymmetric translation-invariant tests and individual entire
height cutoffs h_j, each the Fourier transform of a smooth compactly supported
function. The sum retains the complex ordinates gamma_rho=-i(rho-1/2).
When summing over distinct zero locations, the weight is the product of their
multiplicities, including when locations coincide. The height factor in the
main term is integral product_j h_j. The error is O(T), against leading scale
T log(T)/(2pi). Hard interval cutoffs are not furnished unconditionally by that
statement. These are correlation constants until the same operator and height
weights have been matched to the counting inequality.

## 3. Complete constants, with no pairing term suppressed

For any real compactly supported profiles, write

    G_a(x) = integral |x-y| a(y)dy,
    L(a,b) = integral a(x) G_b(x)dx.

The all-index constants are

    C2(a,b) = integral a b + L(a,b),

    C3(a,b,c) = integral [a b c + b c G_a + a c G_b + a b G_c].

For four profiles, in their cyclic order,

    C4(a,b,c,d) = integral a b c d
      + L(a,bcd)+L(b,acd)+L(c,abd)+L(d,abc)
      + L(ab,cd)+L(bc,ad)
      + integral [bd G_a G_c + ac G_b G_d]
      + integral_(t,v,w) |v w| a(t+v)b(t+v+w)c(t+w)d(t) dt dv dw.   (3)

The second and third lines of (3) contain all six single pairings. Its last
two lines contain all three double pairings. For example, the common Fourier
density before applying the pairing formula is

    Phi(xi) = integral a(t+xi_1)b(t+xi_1+xi_2)
                         c(t+xi_1+xi_2+xi_3)d(t)dt,
    sum xi_j=0.

Substituting each of the six vectors v(e_i-e_j) and each of the three disjoint
pairings into Phi gives (3). This is also an independent way to check the
cyclic order in the executable implementation.

The numerator in (1), at the level of these constants, is

    J(p,r) = 3 C3(q,r,q) - C4(p,q,r,q) - 2 C2(r,r).         (4)

For a uniform normalized profile on an interval of length w, direct integration
of (3) gives the independent reference values

    C2 = 1/w + w/3,
    C3 = 1/w^2 + 1,
    C4 = 1/w^3 + 2/w + 4w/15.                             (5)

For an application of the full fourth correlation formula use w<1/2 and smooth
interior approximations. Equation (5) itself is simply an integral identity.

## 4. The pair term that changes the first proposed sign

Consider normalized r concentrated around c, with width tending to zero, and
continuous p near c. In C4(p,q,r,q), the single pairing

    L(p,q r q) = integral p r^2 G_p

has the same leading order as the zero-frequency term integral p^2 r^2. It
cannot be discarded. Together these give

    J(p,r) = [p(c)(3-p(c)-G_p(c))-2] integral r^2
             + lower-order terms.

For the exact Montgomery-Taylor endpoint profile, G_p=c2-p on its support.
Thus the coefficient becomes p(c)(3-c2)-2. At the center it is negative.
The tempting positive expression -(p(c)-1)(p(c)-2) omits that single pairing.
This asymptotic observation concerns the displayed shrinking-window family;
it is not a theorem ruling out arbitrary mixed scores or profiles.

## 5. Measured profiles and deterministic centering

The executable uses a normalized cosine wide profile at lambda=.499 and
r proportional to (1-((x-c)/mu)^2)^2 inside the narrow interval. These piecewise
endpoint profiles are integral probes, and need smooth interior approximation
before using the analytic theorem. With 2401 grid points, the central widths
mu=.04,.08,.12,.16 give J approximately

    -3.14045, -1.53017, -0.97627, -0.68718.

Shifted single intervals (mu,c)=(.11,.15),(.06,.30),(.025,.42) give approximately

    -1.34256, -3.99496, -13.98380.

Every listed interval passes both support checks in Section 2. There is no
positive gain in these instances. A bounded four-term signed polynomial R
search on the central interval mu=.16 improved the measured raw J to about
-0.52519. This was a search result, not a global optimization theorem.

A finite sampled feature model also allows testing Q=(B-D)^2 with a fixed real
diagonal D. This requires additional normalization: the frequency sampling
must give normalized diagonal traces as integrals. It is not legitimate to
treat multiplication by a nonzero function on a continuum as a finite-trace
operator. In such a matched sampled model, let D have profile d and set

    e = 3p-p^2-p G_p-2,
    w = q^2(3-p-G_p)+q[(3-p)G_q-G_(pq)]-2r.

Then the formal numerator is

    J_d = J - 2 integral w d + integral e d^2.             (6)

All terms follow from the two- and three-cycle formulas above plus diagonal
frequency insertions. If e<0 pointwise, the best such deterministic profile is
d=w/e, giving J_opt=J-integral w^2/e. Centering by the mean uses d=r.
This is optimization over deterministic diagonal profiles for the specified
sampled constants; it is not a zeta transfer theorem.

For the same central cases, the measured optimally centered values are

    -0.00302732, -0.00579535, -0.00806289, -0.00961783.

The shifted cases also remain negative. Taking Q=(B-bI)^2 in an unspecified
ambient space is more delicate: span(A)+span(B) can have dimension up to 2N,
so a replacement dim(H)<=N needs its own proof.

## 6. Reproduction and remaining work

Run

    .venv/bin/python hunts/cycle_moments/mixed_moments.py --self-check

The checks compare (5) with the complete integral implementation, compare a
direct potential quadrature with its cumulative-sum implementation, check
cyclic invariance, and check the strict finite example in Section 1. Repeating
at a denser grid is a numerical convergence check, not an asymptotic zero
estimate. The JSON output separates the four contributions to C4.

Equation (1) is an actual finite strengthening whenever J>0. Equations (2)-(4)
identify correlation statistics within published unconditional Fourier support.
The tested near-full-width Montgomery-Taylor profiles do not make J positive.
No general impossibility claim about other mixed constructions is established.
