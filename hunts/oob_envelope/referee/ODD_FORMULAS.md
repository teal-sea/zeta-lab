# Frozen independent odd reduction

Frozen before reading the odd worker implementation or its result artifacts.
Input revision: 06fdc801d58fe19977dd865134487bfdbf07cecd. The endpoint printed
in ODD_BRIEF.md is known; no numerical algorithm from that lane is used.
This is an ordinary derivation, pending external verification. Numerical
premises remain unestablished until the saved executions close their gates.

## Basis, sign, and domain

Use F(t)=integral f(x) exp(itx) dx. The orthonormal odd basis on [-L,L] is
u_i(x)=sqrt((4i+3)/(2L)) P_(2i+1)(x/L), i=0,1,... . Integrating Rodrigues'
formula by parts gives integral P_n(y) exp(izy) dy=2 i^n j_n(z).
Thus F_i(t)=i h_i(t), where
h_i(t)=(-1)^i sqrt(2L(4i+3)) j_(2i+1)(Lt).
All h_i(0)=0. Products in the real odd matrix are h_i h_j, not F_i F_j.
The pole vector is p_i=integral u_i(x) sinh(x/2) dx
=sqrt(2L(4i+3)) i_(2i+1)(L/2), with i_n the modified spherical Bessel
function. There is no alternating sign in p_i.

For complex f, put c=integral f cosh(x/2), s=integral f sinh(x/2).
The autocorrelation transform is F(z) conjugate(F(conjugate(z))). Its two
pole evaluations sum to 2 Re[(c-s) conjugate(c+s)]=2(|c|^2-|s|^2).
For real odd f this is -2 s^2. Parity cross terms in the Fourier multiplier
are odd in t and vanish against its real even symbol. Real and imaginary
parts also decouple: their cross term is odd. Consequently Q(f) is the sum
of its four real parity forms, as is the squared L2 norm.

These statements hold on the form domain
integral log(2+|t|)|F(t)|^2 dt < infinity. Outside it the archimedean positive
part is infinite; bounded prime and pole terms cannot cancel it, so the
extended-value lower inequality still holds. A finite even bound and a
finite odd bound therefore imply the complex bound with their minimum.
No parity gap invalidates that implication. Both numerical premises are
needed; the present document by itself establishes neither.

## Support and reduction

For L2 compactly supported f, its autocorrelation g is continuous by
continuity of translations in L2 and Cauchy-Schwarz. At |a|>=2L the overlap
of the supports has measure zero, hence g(a)=0, including equality. Since
|F|^2 is L1, Fourier inversion gives integral |F(t)|^2 exp(iat) dt/(2pi)
=g(-a). Every term of the finite cosine correction H therefore integrates
to zero for complex as well as real f. This cancellation does not alter
the pole term.

Use the exact sine:16 envelope already frozen and independently checked by
the even referee. Its positive atomic-measure construction and coefficient
residual checks are in l119.envelope and REVIEW.md. They are rerun in Arb.
For the Zhu validation use H=0 and S=sum 2 Lambda(n)/sqrt(n).
From the digamma lower estimate and P-H<=S,
beta=log(T/(2pi))-1/T-S is a lower bound for the symbol outside [-T,T].
Plancherel gives Q>=R, whose head is
A_ij=beta delta_ij-2 p_i p_j+integral_0^T (arch-P+H-beta) h_i h_j dt/pi.
Reference for the analytic digamma inequality and the finite reduction:
[Zhu v2, sections 3, 4 and 6](https://arxiv.org/html/2608.24827v2).
The derivation above supplies the complex conjugations explicitly.

## Independent errors

CC panels have width 1/2 and degree q=192, rho=1+sqrt(2), and lie inside
|Im t|<=1/4. Re(1/4 +/- it/2)>=1/8. The digamma series, with its first
term separated and the remaining reciprocal series bounded by an integral,
gives |psi(z)|<=9+2|z| on this strip; |z|<=T+2 suffices here.
Bound every cosine by cosh(frequency/4). Set
M_symbol=9+2(T+2)+log(pi)+|beta|+sum |coefficient| cosh(frequency/4).
Poisson's integral for j_n gives |j_n(z)|<=exp(|Im z|), so
M_entry=2L(4N-1) exp(L/2) M_symbol covers every odd head product.
Chebyshev coefficients are bounded by 2M rho^-k. Interpolation aliases the
tail with at most twice its uniform norm, and integrating the interpolant
over each panel gives per-entry error
eps_Q=4T M_entry/[pi (rho-1) rho^q]. Add it as a ball to each entry.

Spherical Bessel seeds use the referee power series at orders 2N+64 and
2N+65, followed by downward recurrence. Its absolute term ratio is
x^2/[2(k+1)(2n+2k+3)], decreasing with k. Once below 1/2, twice the first
omitted absolute term covers the remaining sum. Check j0 against sinc and
j1 against (sin x-x cos x)/x^2 at each nonzero node. All arithmetic uses Arb.

The first omitted odd order is n=2N+1, hence 1001 at N=500.
Poisson's weighted integral after Rodrigues' integration by parts gives
|j_n(x)|<=x^n/(2n+1)!! for real x>=0 and
i_n(x)<=exp(x) x^n/(2n+1)!!. Define
a_n(x)=sqrt(2L(2n+1)) x^n/(2n+1)!! and
r_n(x)=x^2 sqrt((2n+5)/(2n+1))/[(2n+3)(2n+5)].
These successive same-parity ratios decrease. If r_n<1, let
U=a_n(LT)^2/(1-r_n(LT)^2) and
V=exp(L) a_n(L/2)^2/(1-r_n(L/2)^2).
They bound the squared Fourier and pole tail norms uniformly.
Writing K=(T/pi) sup_[0,T]|arch-P+H-beta|, Bessel's inequality gives
head Fourier norm <=sqrt(2L), while the total squared odd pole norm is
integral sinh(x/2)^2 dx=sinh(L)-L. Therefore
eps_D=K U+2 V and eps_B=K sqrt(2L U)+2 sqrt((sinh(L)-L)V).
The negative pole tail must be charged in eps_D. Copying the even
eps_D=K U would drop a required term.

For the head, propose a Cholesky factor of its midpoint minus exact shift s,
freeze that factor to exact dyadics, and enclose the full product residual
with Arb. Symmetric maximum absolute row sums r and e bound respectively
the residual and all entry errors. Then A>=(s-r-e)I. The full lower bound
is min(s-r-e,beta-eps_D)-eps_B by the norm of the off-diagonal block.
The exact dyadic lower endpoint is saved separately from printed balls.

## Frozen decisions and controls

| case | L | T | N | bits | exact shift | outward target |
|---|---|---|---|---|---|---|
| Zhu | 4/5 | 150 | 200 | 768 | 8e-15 | 7.99e-15 |
| main | 119/100 | 500 | 500 | 1280 | 3e-44 | 2.99e-44 |

Zhu section 6.2 is the comparison for the first case. No target tuning after
failure. Numerical failure is inconclusive unless a counterexample is enclosed.
For the main case flip -2 pp^T to +2 pp^T. Evaluate the change on an exact
dyadic vector aligned with p, and test against the independently integrated
first-mode pole. The sign gate must reject, with a strictly positive enclosed
change of the quadratic form, even if the damaged head remains positive.
Separately shift R by -1e-42 I. An exact dyadic inverse-iteration vector must
have negative enclosed Rayleigh quotient, and the same factor step must
return no positive bound. This is an artificial negative-operator control,
not a rival L-function and not a claim that the original Weil form is negative.
Freeze the result artifacts before reading the odd worker output for comparison.
