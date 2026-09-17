# Analytic packet: second Davenport-Heilbronn heat flow

Status: candidate ordinary argument with enclosure-carrying numerical steps.
Independent Muse and Gemini reviews found no analytic or implementation defect
in the complete packet. Model agreement is not an oracle. This document is not
a kernel-checked result, and no novelty claim is made.

## Candidate result

For `phi=(1+sqrt(5))/2` put `tau_plus=sqrt(1+phi^2)-phi` and
`tau_minus=-phi-sqrt(1+phi^2)`, so `tau_plus=-1/tau_minus`. For either
choice `tau`, use the period-five real coefficients
`a_tau=(1,tau,-tau,-1,0)` mod 5, with `D_tau`, `F_tau`, `omega_tau`,
`g_tau`, `H_{plus,t}`, `H_{minus,t}` defined in section 1. In the narrow
coordinate `s=1/2+iz`, the calculation supports

    217/200 < Lambda_minus <= 567009/320000 = 1.771903125.

The wide coordinate `s=(1+iz)/2` multiplies heat times by four:

    217/50 < Lambda_minus_wide <= 567009/80000 = 7.0876125.

In the same narrow frame, the plus function supports
`Lambda_plus <= 1/2` (section 6), hence `Lambda_plus_wide <= 2` in the
wide frame by the same unchanged factor of four.

The lower step uses two explicit disks, not a finite scan upgraded into a
uniform zero statement. The upper step uses a zero-free half-plane argument
and de Bruijn's strip contraction theorem. That theorem allows a complex
Hermitian kernel; it does not require a real even kernel.[1]

## 1. Fourier and Mellin normalization

Fix `phi=(1+sqrt(5))/2`, `tau_plus=sqrt(1+phi^2)-phi`,
`tau_minus=-phi-sqrt(1+phi^2)`. For either `tau`, let
`a_tau=(1,tau,-tau,-1,0)` mod 5, and define

    omega_tau(x) = sum_{n>=1} n a_tau(n) exp(-pi n^2 x/5),
    D_tau(s) = sum_{n>=1} a_tau(n)n^(-s),
    F_tau(s) = (5/pi)^((s+1)/2) Gamma((s+1)/2) D_tau(s).

All of section 1 works in the narrow frame `s=1/2+iz`. The series for
`D_tau` is absolutely convergent for `Re(s)>1`. Its expression
`5^(-s) sum_{r=1}^4 a_tau(r) zeta(s,r/5)` continues it; the residues at 1
cancel. The Mellin transform gives

    F_tau(s) = integral_0^infty omega_tau(x) x^((s-1)/2) dx.

To determine the sign, use the finite Fourier transform
`ahat(b)=sum_{c mod5}a(c) exp(-2pi i bc/5)/5`. Put
`v=sin(2pi/5)` and `w=sin(4pi/5)`. Oddness of `a` gives

    ahat(1) = -2i(v+tau*w)/5,
    ahat(2) = -2i(w-tau*v)/5.

The eigenvector equation is `w*tau^2+2v*tau-w=0`. Since `v/w=phi` and
`v^2+w^2=5/4`, its two roots are the stated `tau_plus` and `tau_minus`.
For the plus root, `v+tau_plus*w=+sqrt(5)/2`, hence
`ahat=-i*a/sqrt(5)`. Poisson summation applied to
`x exp(-pi t x^2/5)` gives

    omega_plus(x) = -i sqrt(5) x^(-3/2) sum_{n>=1} n ahat(n) exp(-pi n^2/(5x)),
    omega_plus(1/x) = +x^(3/2) omega_plus(x).

Consequently `g_plus(u)=exp(3u/2)omega_plus(exp(2u))` is real and even.
Splitting the Mellin integral at 1 and substituting `x=exp(2u)` yields

    F_plus(1/2+iz) = 4 integral_0^infty g_plus(u) cos(zu) du.

Define the plus heat flow by

    H_plus,t(z) = 4 integral_0^infty exp(tu^2) g_plus(u) cos(zu) du.

Thus `H_plus,0=F_plus(1/2+iz)`. Its whole-line Fourier kernel is the real
even function `K_plus(u)=2 g_plus(u)`.

For the minus root, `v+tau_minus*w=-sqrt(5)/2`, hence
`ahat=+i*a/sqrt(5)`. Poisson summation gives

    omega_minus(x) = i sqrt(5) x^(-3/2) sum_{n>=1} n ahat(n) exp(-pi n^2/(5x)),
    omega_minus(1/x) = -x^(3/2) omega_minus(x).

Consequently `g_minus(u)=exp(3u/2)omega_minus(exp(2u))` is real and odd.
Splitting the Mellin integral at 1 and substituting `x=exp(2u)` yields

    F_minus(1/2+iz) = 4i integral_0^infty g_minus(u) sin(zu) du.

Define

    H_minus,t(z) = 4 integral_0^infty exp(tu^2) g_minus(u) sin(zu) du.

Thus `H_minus,0=-i F_minus(1/2+iz)`. Its whole-line Fourier kernel is
`K_minus(u)=-2i g_minus(u)`: `K_minus(u)=conj(K_minus(-u))`. The rest of
this packet writes `H_t`, `g`, `omega`, `F`, `D` for the minus objects
`H_minus,t`, `g_minus`, `omega_minus`, `F_minus`, `D_minus`. The sign and
factor are pinned against an independent Hurwitz-zeta evaluation and by
the odd modular identity; the plus sign and cosine identity are pinned by
the `even_theta_transform` and `plus_zero_time_cosine_identity` checks in
`verify.py` and the two new tests in `test_heat.py`. The minus
coefficients are bounded by `M=abs(tau_minus)`, which is greater than one;
the plus coefficients satisfy `abs(a_n)<=1` since `0<tau_plus<1`.

At positive infinity, `g(u)` decays as a polynomial exponential times
`exp(-pi exp(2u)/5)`; at negative infinity use oddness. This proves the
required super-Gaussian decay, integrability, entire dependence on `z`, and
locally uniform dependence on every real heat parameter `t`.

## 2. Two local disks, with the stronger one at time 217/200

The time-one disk used the exact rational values

    c = 7.646830873064 + 0.425938287679 i,
    r = 1/10000000.

The disk avoids the real axis. `odd_ball.py` encloses the infinite heat
integral and its first derivative at c, and an upper bound `M2` for
`abs(H_1''(z))` throughout this disk. The exact dyadic endpoints in
`rouche.json`, rechecked as rational inequalities by `verify.py`, imply

    abs(H_1(c)) < 1/10^14,
    abs(H_1'(c)) > 15/1000,
    M2 < 235/100.

Taylor's integral remainder on each straight segment from c gives

    abs(H_1(z)-H_1(c)-H_1'(c)(z-c)) <= M2*r^2/2.

On the disk boundary, compare H_1 with `H_1'(c)(z-c)`. Their difference
has magnitude at most `abs(H_1(c))+M2*r^2/2`, strictly less than
`r*abs(H_1'(c))`. The coarse rational lower bound on this margin is

    5999913/4000000000000000 > 0.

Rouche's theorem therefore gives exactly one zero counted with multiplicity
in the disk. It is simple and non-real. A rounded root-finder residual alone
would not establish this statement.

The stronger disk uses

    t = 217/200,
    c = 7.543145542463 + 0.072646330251 i,
    r = 1/10000000.

It remains disjoint from the real axis. Four enclosure configurations of the
same Arb calculation, at 96, 128 and 160 bits, imply the coarse bounds

    abs(H_t(c)) < 1/10^14,
    abs(H_t'(c)) > 28/10000,
    M2 < 19/10.

The corresponding exact coarse margin is

    559961/2000000000000000 > 0.

The same Taylor/Rouche argument therefore places exactly one simple non-real
zero in this later disk. This proves only survival at `t=217/200`; the measured
approach to the real axis between this time and `1.09` is not promoted to a
collision-time statement.

## 3. Error bounds actually consumed

For derivative order `k=0,1,2`, put `y=abs(Im(c))+r` when bounding the disk,
and `y=abs(Im(c))` at the centre. On a real integration path, the wave factor
and its k-th derivative are bounded by `u^k exp(yu)`.

For the theta tail after n=N, set `rho=exp(-pi(N+1)/5)`. Since
`n^2>=n(N+1)` for `n>N`, the omitted omega terms on `u>=0` have absolute sum
at most

    M (N+1) rho^(N+1)/(1-rho)^2.

On `[0,U]` multiply this by
`4 U^(k+1) exp(tU^2+(3/2+y)U)`. The calculation uses `t>=0`.

For the integral after U, assume `U>=1` and set

    V=exp(2U),
    C=pi/5-(tU^2+(3/2+y)U)/V > 0.

The code also checks `exp(-pi V/5)<29/100`, giving
`sum n exp(-pi n^2 exp(2u)/5)<=2exp(-pi exp(2u)/5)`. The decreasing functions
`u exp(-2u)` and `u^2 exp(-2u)` give the integrand bound
`8M u^k exp(-C exp(2u))`. Substitution `v=exp(2u)` and the fact that
`(log v)^k/v` decreases for `log v>=k` bound the tail by

    4 M U^k exp(-CV)/(CV).

The finite integrand is entire. Arb's complex integrator encloses its finite
integral; both explicit errors are added to both complex components. The
second-derivative majorant replaces every coefficient by M and the sine by
`exp(yu)`, a nonnegative real integrand. It bounds the whole disk, not sampled
boundary points. An insufficient theta cutoff returns an inconclusive local
inequality. It does not silently discard a tail.

## 4. Upper strip from prime phases

Let chi be the primitive quartic character modulo 5 with `chi(2)=i`, and
`A=(1-i*tau_minus)/2`. The coefficient identity gives

    D(s)=A L(s,chi)+conj(A)L(s,conj(chi)).

For `Re(s)>1`, both Euler products are nonzero. A zero of D would force their
ratio to equal `-conj(A)/A`. Writing `kappa=tau_plus=-1/tau_minus`, its
smallest absolute phase is `2 atan(kappa)`.

The primes congruent to 1 or 4 modulo 5 contribute ratio one, as does 5.
Each remaining prime contributes `(1+u)/(1-u)` with `abs(u)=p^(-sigma)`.
Its phase has magnitude at most `2 atan(p^(-sigma))`. Thus a zero is
excluded if

    Theta(sigma)=2 sum_{p=2,3 mod5} atan(p^(-sigma)) < 2 atan(kappa).

This is the necessary Euler-factor argument recorded in
`../lambda_dh_bounds/STRIP2.md`, not a new phase-obstruction theorem. Here a
simpler tail replaces that instrument: above the integer cutoff P,

    2 sum_{p>P} atan(p^(-sigma)) <= 2 P^(1-sigma)/(sigma-1).

An exact sieve through `P=10000` and two independent interval backends decide
the inequality at `sigma=953/400`. The lower endpoint of the phase margin
is positive on both backends. The mpmath interval implementation uses an
arctangent Taylor series with an explicit remainder, not a float arctangent.
Monotonicity excludes every `Re(s)>=953/400`. The functional equation
reflects this exclusion to the left. Since the gamma factor has no zeros or
poles in the right region, every zero of the entire completed F lies in
`abs(Im(z))<753/400`.

De Bruijn's contraction therefore makes all zeros real by
`(753/400)^2/2=567009/320000`.[1] The sharper sibling abscissa recorded in
the older hunt is not required and has not been rerun here.

## 5. Threshold and strict lower bound

Let S be the real times at which all zeros of H_t are real. It is nonempty
by section 4. De Bruijn's theorem makes S upward closed: for a real-rooted
H_t, apply the strip theorem with arbitrarily small positive strip widths
to its Hermitian kernel `exp(tu^2)K(u)`.[1]

S is closed. Indeed, H_t varies locally uniformly with t, and no H_t is
identically zero, by injectivity of the Fourier transform of the nonzero
integrable kernel. If `t_n in S` tends to t and H_t had a non-real zero,
choose a small disk avoiding the real axis and with a zero-free boundary.
Uniform convergence and Rouche would put a non-real zero of H_(t_n) there,
a contradiction. The stronger zero in section 2 implies `217/200 notin S`. Upward closure
then excludes all times at most `217/200` from S, and closedness gives

    S=[Lambda_minus,infinity),    217/200<Lambda_minus<=567009/320000.

This argument uses the Hermitian strip theorem directly. It does not need
an even-kernel restriction, a proof that all zero trajectories have been
tracked, or the assumption that no pair enters from infinity.

## 6. Controls and exact scope

`verify.py` repeats both local enclosures at 96, 128 and 160 bits, with theta
cutoffs 24, 26 and 28 and integration cutoffs 4 and 7/2. Direct mpmath
quadrature at 55 digits agrees with the Arb values of H and H' at both times.
This is a floating-point independent check, not a second enclosure backend
for the quadrature. The prime-strip sign is enclosed on both Arb and
mpmath.iv. Moving the centre outside the tiny disk and underresolving the
theta series both prevent the local decision. Normalization tests reject a
factor-of-two error and the wrong modular sign.

The subject is itself the second Davenport-Heilbronn rival. No implication
from shared symmetries to RH is proposed, so a generic rival-passing test
would not strengthen the analytic argument. The relevant comparison is the
first DH function with the opposite theta parity, in the same heat frame.

That comparison does not need the inherited first-function bound. At
`sigma=3/2`, sum the plus-function coefficients through `N=20` and use
`abs(a_n)<=1` for the rest:

    sum_{n>=2} abs(a_n)n^(-3/2)
      <= sum_{n=2}^20 abs(a_n)n^(-3/2)
         + integral_20^infinity x^(-3/2) dx
      = head + 1/sqrt(5) < 1.

Both Arb and mpmath.iv enclose this strict inequality in
`first_comparison.json`. First-term domination and the plus functional
equation put all zeros of `F_plus`, hence of `H_plus,0`, in a narrow
z-strip of half-width one. The same de Bruijn contraction applied to the
plus cosine flow `H_plus,t` gives

    Lambda_plus <= 1/2 < 217/200 < Lambda_minus,

in the narrow frame, i.e. `Lambda_plus_wide <= 2` by the same unchanged
factor of four. `Lambda_plus` here is the threshold of `H_plus,t`, not of
the generic or minus flow.

Thus the two conductor-five heat constants are separated by this packet if
the ordinary analytic argument and enclosed computations survive review. The
sharper inherited upper bound for the first function is not needed.

The claim concerns a heat threshold for this explicitly defined function,
not zeta's RH, the location of every second-DH zero at time zero, the exact
landing time of the observed pair, or novelty in the literature.

A bounded search for second-DH heat bounds did not locate a directly relevant
prior bracket. That does not establish absence of prior art. The finite
Fourier calculation, Mellin representation, Rouche theorem and strip
contraction are existing mathematics; any original contribution here is the
explicit new application and reproducible numerical packet, subject to review.

Sources:
[1] https://arxiv.org/html/2005.05142v2 - Dobner, extended Selberg class, version 2

## The doors

### Active constraints at the optimum

There is no numerical optimizer in this hunt, so “optimum” means the binding
inequalities in each endpoint of the bracket. For the lower endpoint, the
active constraint is the local Taylor/Rouche margin. The linear boundary term
is about `2.86e-10` at the later disk; the centre and remainder contributions
total about `1.37e-14`. The radius is therefore not close to its mathematical
limit, but the derivative is shrinking as the conjugate pair approaches the
real axis. For the upper endpoint, the active constraint is the Euler-phase
budget at `sigma=953/400`. Its enclosed margin is about `9.89e-5`; the simple
all-integer tail above 10000, rather than the finite prime head, is the part
most open to sharpening. Neither constraint says the current bracket is exact.

### Frozen-constant inventory

The frozen constants are the narrow frame `s=1/2+iz`, heat multiplier
`exp(tu^2)`, `tau_plus=sqrt(1+phi^2)-phi`,
`tau_minus=-phi-sqrt(1+phi^2)`, the time-one centre and radius,
the coarse Rouche bounds `1e-14`, `0.015`, and `2.35`, theta cutoffs 24, 26,
and 28, integration cutoffs 4 and 7/2, phase cutoff 10000, and strip abscissa
`953/400`. The first-function comparison freezes `sigma=3/2` and `N=20`.
Changing any of these requires rerunning the exact checker rather than carrying
the displayed conclusion forward. The wide-frame values are derived by the
fixed factor four and are not an independent computation.

### Information class of each door

The first door is a later rational heat time for the same conjugate pair. Its
information class is local analytic data: Arb enclosures of one value, one
derivative, and a disk-wide second-derivative majorant. A successful later disk
raises the lower bound; a failed disk leaves the attempt unresolved. The
second door is a sharper zero strip. Its information class is the quartic
mod-five Euler products plus an explicit prime-phase tail. It can improve the
upper endpoint but cannot determine the heat constant by itself. The third
door is structural: compare the even and odd conductor-five kernels under the
same deformation and seek a theorem explaining their separated thresholds.
Its information class must include the theta-transform sign, not merely shared
gamma factors or finite zero counts. A zero-counting experiment may scout that
door, but no asymptotic counting law is asserted here. Prior-art search remains
a separate door before any novelty language.
