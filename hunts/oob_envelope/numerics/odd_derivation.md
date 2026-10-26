# Odd reduction and tail bounds

Ordinary derivation, self-reviewed, pending independent reproduction.
Source checked on 2026-09-28: Zhu, arXiv:2608.24827v2,
<https://arxiv.org/html/2608.24827v2>, equations (6), (12), (13), Lemma 6.1
and section 6.2. Only this source and the hunt's existing theory were checked;
no novelty search. No source copy is retained in this restricted write area.
The source's odd benchmark is a measured matrix value 9.1183e-15 and a
full-space lower bound 8.2065e-15 at L=4/5, T#=150, H=0, N=200.

## 1. Cross terms and the reduction

The theory file RESULTS.md, pole calculation at lines 182 onward and its
section 1.5 parity row, supports the odd application. Here are both missing
cross-term calculations explicitly, without editing the theory lane.

Use F(t)=integral f(x) exp(itx) dx. For real f=e+o, F_e is real even and
F_o imaginary odd, so Re(F_e conj(F_o))=0 pointwise. The pole is
2(c^2-s^2), c=integral e cosh(x/2), s=integral o sinh(x/2), and contains
no mixed term. Thus Q(e+o)=Q(e)+Q(o). For complex f=u+iv with u,v real,
the Fourier cross term is odd in t, because F_u(-t)=conj(F_u(t)) and
likewise for v. It integrates to zero against the real even symbol.
The pole 2|c|^2-2|s|^2 also splits into real and imaginary parts.
Consequently Q(f)=Q(u)+Q(v), and orthogonality splits the squared norms.
For an infinite positive archimedean integral, interpret Q as an extended
closed form; alternatively first prove this on its finite form domain.

The sine:16 H is a real even sum of out-of-band cosines. Its full-line
integral against |F|^2 vanishes by Fourier support, independently of parity.
With S bounding P_L-H globally, T>=15/4 and
beta=log(T/(2pi))-1/T-S>0, the increasing lower envelope gives

    Q_odd >= R_odd = beta I + C - 2 s s^T,
    C_ij = (1/pi) integral_0^T (Psi_L+H-beta) v_i v_j dt.

This uses the existing envelope result; it is not a new verification of H.

## 2. Basis and pole from Rodrigues' formula

For n=2i+1 put nu=n+1/2 and T_i(x)=sqrt(nu/L) P_n(x/L).
Legendre orthogonality makes these an orthonormal basis of the real odd
subspace. The general Fourier identity is

    integral_-1^1 P_n(y) exp(izy) dy = 2 i^n j_n(z).

Hence F_i(t)=i v_i(t), v_i(t)=(-1)^i 2 sqrt(L nu) j_(2i+1)(Lt).
The matrix uses F_i conj(F_j)=v_i v_j. Multiplying F_i F_j would introduce
the wrong minus sign in the entire multiplier matrix.

Let a=L/2. The odd integral against cosh(ay) vanishes, so the sinh moment
equals the exp(ay) moment. Rodrigues and n integrations by parts give

    integral_-1^1 P_n(y) exp(ay) dy
      = a^n/(2^n n!) integral_-1^1 (1-y^2)^n exp(ay) dy
      = 2 sqrt(pi/(2a)) I_(n+1/2)(a).
    s_i = 2 sqrt(L nu) sqrt(pi/(2a)) I_nu(a).

There is no (-1)^i in s_i. The head pole is -2 s_i s_j.

## 3. Odd tail sequences and indices

The same Rodrigues integral at z=x real gives
|j_n(x)| <= x^n/(2n+1)!!, since the beta integral of (1-y^2)^n is
2^(n+1) n!/(2n+1)!!. For the real exponential, exp(ay)<=exp(a) gives
|i_n(a)| <= exp(a) a^n/(2n+1)!!. Thus for odd integer n,

    a_n = 2 sqrt(L(n+1/2)) (LT)^n/(2n+1)!!,
    pi_n = 2 sqrt(L(n+1/2)) exp(L/2) (L/2)^n/(2n+1)!!.

These majorize |v_n(t)| for 0<=t<=T and |s_n|, respectively.
For i=0,...,N-1 the orders are 1,...,2N-1. The first discarded order is
n0=2N+1, whose denominator is (4N+3)!!.
The helper dfact_log(n)=lgamma(2n+2)-n log(2)-lgamma(n+1) computes
log((2n+1)!!), with n the polynomial order, not the basis index.

The step-two ratios are, with x=LT or L/2 respectively,

    r_x(n) = x^2/((2n+3)(2n+5)) sqrt((n+5/2)/(n+1/2)).

Both factors decrease with n>=0, so checking r_x(n0)<1 in Arb licenses
alpha=sum a_n <= a_n0/(1-r_LT(n0)) and
pis=sum pi_n <= pi_n0/(1-r_(L/2)(n0)), sums over odd n>=n0.
This is also why a_n0 and pi_n0 bound each tail coefficient.

Let K=(T/pi) sup_[0,T]|Psi_L+H-beta|,
b_i=2 sqrt(L nu_i), b_max=max b_i, b_sum=sum b_i,
s_max=max |s_i| and s_sum=sum |s_i|. All maxima use ball upper bounds.
Absolute entry bounds, including the negative pole diagonal, give

    eps_D = K a_n0 alpha + 2 pi_n0 pis,
    B1 = K b_max alpha + 2 s_max pis,
    Binf = K a_n0 b_sum + 2 pi_n0 s_sum,
    eps_B = sqrt(B1 Binf).

The tail satisfies D>= (beta-eps_D)I and the coupling norm is <=eps_B.
The pole sign disappears only inside these absolute-value estimates.
It remains negative in the retained matrix.

## 4. Quadrature and head positivity

The Poisson integral yields |v_i(z)|<=2 sqrt(L nu_i) exp(L|Im z|)
for both odd and even n. Therefore the existing ellipse and node-shift
derivation applies after substituting the odd nu_i. With h=1/2 and
rho=1+sqrt(2), the rectangle has half-width h/sqrt(2), height h/2.
The radius-0.1 disk around each real node lies in this rectangle, so the
Cauchy derivative bound used for snapping nodes remains valid.

The reducer encloses the head, subtracts a proposed shift, constructs an
exact dyadic lower-triangular factor and bounds its Arb residual by the
maximum absolute row sum r. The head radius plus quadrature has operator
norm at most e. Therefore

    lambda_min(R_odd) >= min(lambda0-r-e, beta-eps_D)-eps_B.

The reported decimal is rounded downward from the exact Arb lower endpoint.
The inverse-iteration value and sign-flip comparison are measurements.
For a failed Cholesky pivot, a reconstructed Schur vector is evaluated
against the ball matrix plus quadrature error, distinguishing a numerical
refusal from an enclosed negative Rayleigh quotient.

If both sectors succeed, the weaker endpoint bounds all complex f by
section 1. This remains a fixed-window candidate, with the ordinary
reduction and shared numerical implementation pending independent review.
