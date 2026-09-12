# A higher-cycle-moment extension of simple-real counting

This note derives a finite-dimensional extension of the counting mechanism in
Proposition 2.1 of Youness Lamzouri, *A new proof that more than 2/3 of the zeros of
the Riemann zeta function are simple and on the critical line*,
[arXiv:2609.02882v1](https://arxiv.org/html/2609.02882v1).
The adapted subspaces are taken from that proof. The general concave spectral
score and the quartic perturbation below were derived here. Novelty has not been
established. The proofs below are ordinary mathematical proofs, not Lean proofs.

The strongest consequence is conditional but concrete: if matched first three
cycle moments have limits with third-moment discrepancy different from zero,
then any finite bound for the normalized fourth cycle moment gives a strict
improvement over the second-moment counting bound. The required matched
fourth-moment estimate for zeta is not proved in this note.

## 1. Finite-dimensional hypotheses

Let H be a finite-dimensional real inner-product space. Choose:

- s unit vectors v_1,...,v_s, representing simple real elements;
- r unit vectors w_1,...,w_r with integer multiplicities m_j >= 2;
- k pairs of vectors g_l,h_l with integer multiplicities n_l >= 1 and
  ||g_l||^2 - ||h_l||^2 = 1.

The application has g_l perpendicular to h_l, but the theorem does not need that
additional property. No positivity of the eventual operator is assumed.

Write u tensor u for the operator x |-> <x,u>u, and set

    A = sum_i v_i tensor v_i
        + sum_j m_j w_j tensor w_j
        + 2 sum_l n_l (g_l tensor g_l - h_l tensor h_l),

    N = s + sum_j m_j + 2 sum_l n_l,
    M_j = tr(A^j), j >= 1.

A is self-adjoint, possibly indefinite, and M_1 = N exactly.

## 2. Headline theorem: a quartic perturbation

For any real t satisfying |t| <= sqrt(5/8), define

    D_t = 1 + t^2 / (4(1-t^2)),
    Delta_3 = M_3 - 3M_2 + 2N,
    Delta_4 = 2N - 5M_2 + 4M_3 - M_4.

Then

    s >= [2N - M_2 - t Delta_3 + t^2 Delta_4] / D_t.       (1)

The parameter t may have either sign, and t=0 recovers s >= 2N-M_2.
Equation (1) is an exact finite-dimensional inequality under Section 1's
hypotheses. In particular, nonreal-pair contributions have not been discarded.

## 3. The general concave-score theorem

Let f:R->R be globally concave with f(0)=f(2)=0 and f(x)<=1 for all real x.
Functional calculus for the self-adjoint A then gives

    tr f(A) <= s.                                        (2)

Proof. Set

    U = span(w_1,...,w_r,g_1,...,g_k),
    V = U + span(v_1,...,v_s),
    W = V + span(h_1,...,h_k).

Let d_U,d_V,d_W be their dimensions. Choose an orthonormal basis
(e_1,...,e_dW) of W adapted to U subset V subset W, and put
alpha_j = <Ae_j,e_j>. On W-perp the operator is zero, and f(0)=0, so working on W
loses no trace term.

First, the sum of the diagonal entries in U satisfies

    sum_{j<=d_U} alpha_j
      = sum_i ||P_U v_i||^2 + sum_j m_j
        + 2 sum_l n_l (||g_l||^2 - ||P_U h_l||^2)
      >= sum_j m_j + 2 sum_l n_l
      >= 2(r+k) >= 2d_U.                                 (3)

Here the full g_l contribution belongs to U, while projection can only decrease
the squared norm of h_l. This is where the negative part of A is controlled.

Second, d_V-d_U <= s. Third, if j>d_V then e_j is orthogonal to every v_i,w_j,g_l,
so

    alpha_j = -2 sum_l n_l <h_l,e_j>^2 <= 0.              (4)

Global concavity and f(0)=f(2)=0 imply f(x)<=0 outside [0,2]. For example, if x>2,
write 2=(2/x)x+(1-2/x)0 and apply concavity. The argument for x<0 is identical
with 0 between x and 2.

If d_U>0, scalar Jensen and (3) therefore show

    sum_{j<=d_U} f(alpha_j)
      <= d_U f((sum_{j<=d_U}alpha_j)/d_U) <= 0.

The middle block contributes at most d_V-d_U<=s, since f<=1. The final block
contributes at most zero by (4). Empty blocks contribute zero.

It remains to compare the diagonal with the spectrum; the direction matters.
Let lambda_i be the eigenvalues of A on W and let Q be the orthogonal
change-of-basis matrix. Then alpha_j=sum_i Q_ji^2 lambda_i. Concavity gives

    f(alpha_j) >= sum_i Q_ji^2 f(lambda_i).

Summing over j and using sum_j Q_ji^2=1 gives

    tr f(A) = sum_i f(lambda_i) <= sum_j f(alpha_j) <= s.

This proves (2).

## 4. Polynomial verification of the headline theorem

Use the polynomial

    q_t(x) = x(2-x)[1+t(x-1)+t^2(x-1)^2].

With y=x-1 its expansion is

    q_t(x) = 1+t y+(t^2-1)y^2-t y^3-t^2 y^4.

For t!=0 its second derivative is exactly

    q_t''(x)
      = -12t^2 (y+1/(4t))^2 + 2t^2 - 5/4.

For t=0 the second derivative is -2. Thus q_t is globally concave whenever
|t|<=sqrt(5/8). Also q_t(0)=q_t(2)=0.

To check the global upper bound, note that 1+t y+t^2 y^2>0 for all real y.
Consequently q_t<=0 for |y|>=1. For |y|<=1 its larger value at the two arguments
y and -y occurs when t y>=0. Writing a=|t| and z=|y| at that argument,

    q_t <= 1+a z-(1-a^2)z^2
         = 1+a^2/[4(1-a^2)]
           -(1-a^2)(z-a/[2(1-a^2)])^2
         <= D_t.

The negative cubic and quartic terms were simply dropped in the first line.
The permitted range of t has |t|<1, so all denominators are positive. Therefore
f_t=q_t/D_t satisfies every hypothesis of (2).

Finally,

    x(2-x)(x-1)   = -x^3+3x^2-2x,
    x(2-x)(x-1)^2 = 2x-5x^2+4x^3-x^4.

Taking traces and using M_1=N yields (1).

## 5. A simpler fourth-moment bound and a guaranteed wrapper

For 0<=epsilon<=1 the polynomial

    f_epsilon(x)
      = 1-(1-epsilon)(x-1)^2-epsilon(x-1)^4
      = x(2-x)[1+epsilon(x-1)^2]

is globally concave, has roots 0 and 2, and is bounded above by 1. Hence

    s >= 2N-M_2 + epsilon(2N-5M_2+4M_3-M_4).

At epsilon=1 this is

    s >= 4N-6M_2+4M_3-M_4.                               (5)

Taking the better endpoint gives an inequality that never weakens the
second-moment answer:

    s >= 2N-M_2 + max(0, 2N-5M_2+4M_3-M_4).             (6)

## 6. An exact example with positive gain

Take H=R^2, two simple vectors

    v_1=(1,0),  v_2=(1/2,sqrt(3)/2),

and no other vectors. Then s=N=2 and

    A = [[5/4, sqrt(3)/4], [sqrt(3)/4, 3/4]].

Its eigenvalues are 3/2 and 1/2, so

    M_2=5/2,  M_3=7/2,  M_4=41/8.

The second-moment lower bound is 3/2. Formula (5) gives 15/8, an exact increase
of 3/8. Both inequalities are valid lower bounds for s=2. This establishes
strict finite-dimensional strengthening; it does not establish any zeta
asymptotic estimate.

## 7. An explicit asymptotic sufficient condition

Consider a sequence of the finite-dimensional configurations in Section 1 with
N tending to infinity. Assume the matched moments satisfy

    M_2/N -> c_2,
    M_3/N -> c_3,
    limsup M_4/N <= B < infinity.

Set

    S_0 = 2-c_2,
    delta_3 = c_3-3c_2+2,
    delta_4(B) = 2-5c_2+4c_3-B.

For every fixed permitted t, (1) implies

    liminf s/N >= L_B(t)
      := [S_0-t delta_3+t^2 delta_4(B)]/D_t.             (7)

If delta_3!=0, then there is a permitted t with L_B(t)>S_0 for every finite B.
Indeed, L_B(0)=S_0 and L_B'(0)=-delta_3, so a sufficiently small t with sign
opposite to delta_3 improves the bound.

For an entirely explicit choice, put

    C = |delta_4(B)| + |S_0|/3,
    a = min(1/2, |delta_3|/[2(C+1)]),
    t = -sign(delta_3) a.

Since a<=1/2,

    D_t[L_B(t)-S_0]
      = a|delta_3| + a^2[delta_4(B)-S_0/(4(1-a^2))]
      >= a|delta_3| - a^2 C
      >= a|delta_3|/2 > 0.

This explains why an upper bound, rather than an exact evaluation, of the
fourth moment would suffice.

## 8. The Montgomery-Taylor triangle discrepancy is exactly negative

This section evaluates explicit integrals. It does not assert that a particular
zeta cycle sum has already been shown to equal these integrals.

Put u=1/sqrt(2), k=u cot(u), c_2=k+1/2, and let

    p(x)=cos(sqrt(2)x)/(sqrt(2)sin(u)), |x|<=1/2,
    p(x)=0 otherwise.

The function p has integral one. Define

    A_2 = integral p(x)^2 dx,
    A_3 = integral p(x)^3 dx,
    G(x) = integral |x-y|p(y)dy,

and the triangle expression

    c_3 = A_3 + 3 integral p(x)^2 G(x)dx.

On [-1/2,1/2], direct differentiation and the boundary value G(1/2)=1/2 give

    G(x)=c_2-p(x).

Elementary trigonometric integration gives

    A_2=(2k^2+2k+1)/4,
    A_3=k^2+1/3,
    c_3=3c_2 A_2-2A_3.

Therefore the discrepancy factors exactly as

    delta_3 = c_3-3c_2+2
      = (6k-5)(6k^2+6k-1)/24.                           (8)

Its sign can be established without a decimal computation. The inequalities
sin(u)<u and cos(u)>1-u^2/2 give k>3/4. For 0<x<pi, set

    F(x)=(1-x^2/3)sin(x)-x cos(x).

Then

    F'(x)=x[sin(x)-x cos(x)]/3 > 0,

because the bracket vanishes at zero and has derivative x sin(x)>0. Hence
F(u)>0 and k<1-u^2/3=5/6. In (8), the first factor is strictly negative and the
second strictly positive. Thus delta_3<0 exactly.

If the matched zeta moments attain c_2,c_3 from this section and have a finite
normalized fourth-moment upper bound, (7) therefore improves the
Montgomery-Taylor second-moment bound for sufficiently small positive t.

## 9. What the zeta application still requires

The finite-dimensional theorem is independent of any correlation conjecture.
Its analytic application requires all moments to describe the same operator,
normalization, height window, multiplicity convention, and smoothing.

In particular, a Rudnick-Sarnak formula for a weighted, smoothed, distinct-index
correlation sum does not automatically evaluate the unweighted cycle trace of
a hard-truncated zero multiset. Coincident-index contributions, the treatment
of zeros away from the critical line, admissible Fourier support, and transfer
between smooth and hard height cutoffs must all be justified where needed.

An independent estimate of the matched full-bandwidth quantity M_4=tr(A^4)
with limsup M_4/N finite is still required for the sufficient condition above.
No such zeta estimate, and no improved unconditional zeta percentage, is claimed
here. The finite-dimensional inequalities and the exact sign (8) are the results
proved in this note.

## 10. Exact finite kernel cycles, including nonreal points

Let p be nonnegative, even, compactly supported, and have integral one.
Put K(z)=integral p(u) exp(-2 pi i u z) du. Let Z be a finite multiset
invariant under complex conjugation, retaining every multiplicity. Define

    C_j(Z,p) = sum_{z_1,...,z_j in Z}
                  K(z_1-z_2) K(z_2-z_3) ... K(z_j-z_1).

All indices may repeat. These cycle sums are real, even though individual
summands can be complex. If s is the number of simple real elements, then
the exact conclusion (1) holds with M_j=C_j(Z,p) and N=|Z|.
In particular,

    s >= 4|Z| - 6C_2(Z,p) + 4C_3(Z,p) - C_4(Z,p).

Here is the operator identification needed for this statement. In the
complexification of the real Hilbert space of functions satisfying
conj(phi(u))=phi(-u), put f_z(u)=sqrt(p(u)) exp(-2 pi i u z).
Write f_z=g_z+i h_z for its real and imaginary parts with respect to this
real structure, so f_conj(z)=g_z-i h_z. The operator

    A(x) = sum_{z in Z} <x,f_conj(z)> f_z

uses the inner product linear in its first argument. A conjugate pair
contributes 2(g_z tensor g_z - h_z tensor h_z), and a real point contributes
f_z tensor f_z. Moreover <f_z,f_conj(z)>=K(0)=1, giving the required norm
difference. Thus A is exactly an operator from Section 1 on its finite
range. The rank-one trace identity, together with

    <f_z,f_conj(s)> = K(z-s),

gives tr(A^j)=C_j(Z,p). This proves the kernel statement without discarding
nonreal pairs or replacing a transpose by a conjugate transpose.

`probe.py` checks this identification independently using an even atomic
probability measure, real sine/cosine feature coordinates, and direct sums
over every ordered tuple. Its multiset includes a double real point and a
nonreal conjugate pair. The same algebra applies to the integral profile.
This finite statement does not supply the asymptotic estimates in Section 9.
