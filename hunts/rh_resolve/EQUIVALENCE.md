# Equivalence: RH iff the logarithmic derivative stays positive

Grade: ordinary argument, unreviewed, recording a known result. The
equivalence is classical, not new and not this hunt's: main states it in
`hunts/epp_herglotz/RESULTS.md` (its verdict paragraph); see Lagarias,
Acta Arith. 89 (1999), 217-234, cited as a reference, not for priority.
What this file adds is a written derivation for the hunt's own use, with
numerical spot checks in `check_logderiv.py`; the numbers quoted below are
pinned by `tests/test_rh_resolve.py` unless marked otherwise. Not a
resolution of RH. Not kernel-checked. Nothing in this file is an enclosure.

Statement under test, unchanged: every nontrivial zero of zeta
has real part 1/2.

## Statement (classical)

Let L(s) = xi'(s)/xi(s). The following are equivalent.

1. Every nontrivial zero has real part 1/2.
2. Re L(s) > 0 whenever Re s > 1/2 and xi(s) != 0.

Zeros are counted with multiplicity in all sums below.

## Dependencies

D1. xi is entire of order 1, xi(s) = xi(1-s), and xi is real on
    the real axis. Standard, and the functional equation is the
    content of `zeta.core.theta_mellin_xi`.

D2. Hadamard factorization of genus 1:
    xi(s) = xi(0) exp(b s) prod_rho (1 - s/rho) exp(s/rho),
    product grouped so that it converges, with
    b = xi'(0)/xi(0).

D3. Explicit logarithmic derivative, checked in
    `check_logderiv.py` against a difference quotient at s = 2:
    L(s) = 1/s + 1/(s-1) - (1/2) log pi + (1/2) psi(s/2) + zeta'(s)/zeta(s).
    The s -> 0 limit, using zeta(0) = -1/2,
    zeta'(0) = -(1/2) log(2 pi), and
    psi(s/2) = -2/s - gamma + O(s), is
    b = -gamma/2 - 1 + log 2 + (1/2) log pi.

D1 and D2 are classical analytic inputs, not established by the numerical
spot checks. The derivation below is conditional on those inputs in their
stated form. No growth bound for L on circles at infinity is needed.

## Derivation (ordinary argument, unreviewed; records the known result)

(2) implies (1). A zero of multiplicity m at rho with
Re rho > 1/2 contributes m/(s-rho). On the open half-plane,
points immediately to the left of rho have
Re(m/(s-rho)) < 0, and the rest of L is holomorphic there.
So (2) forbids every such rho. By xi(s)=xi(1-s), a zero to the
left of 1/2 would reflect to one on the right, so it too is forbidden.

(1) implies (2). Differentiating the genus-1 product locally away
from its zeros gives

    L(s) = b + sum_rho (1/(s-rho) + 1/rho).

Each summand is O_s(1/|rho|^2) in the tail, and order 1 ensures
sum |rho|^{-2} < infinity. Thus evaluation at s=1 is legitimate.
The functional equation gives L(1)=-L(0)=-b. Therefore

    -b = b + sum_rho (1/(1-rho) + 1/rho),
    sum_rho 1/(rho(1-rho)) = -2b.

This replaces the former argument using unspecified contours at infinity.

Under (1), rho(1-rho) = |rho|^2 and Re(1/rho) = (1/2)/|rho|^2,
so sum_rho Re(1/rho) = -b. The symmetrized Hadamard derivative
then collapses to

    Re L(sigma+it) = sum_gamma (sigma-1/2) / ((sigma-1/2)^2 + (t-gamma)^2),

every term positive for sigma > 1/2. Absolute convergence of
the symmetrized series is the 1/gamma^2 tail.

Spot check, not a derivation of this direction: at 0.8+10i the
real part of L is 0.03177, and the Poisson sum over the first
200 ordinates is 0.03054. Those 200 ordinates end at
gamma_200 = 396.38 (mpmath `zetazero(200)`). The residual 0.00124 is
the tail beyond gamma_200, not a second formula: with d = 0.3 and the
zero density (1/2pi) log(t/2pi), the tail is about
(d/pi)(log(T/2pi) + 1)/T at T = gamma_200, which is also 0.00124.
A wrong sign would miss by the whole real part. `check_logderiv.py`.

## What this does not do

The identity sum 1/(rho(1-rho)) = -2b is unconditional. The
collapse to a sum of positive Poisson kernels uses (1). Proving
Re L > 0 without locating the zeros is still the hypothesis.

On sigma > 1 the Dirichlet series is available, and
Re psi(sigma+it) - psi(sigma) = sum_{k>=0} t^2 / ((k+sigma)((k+sigma)^2+t^2)) >= 0
is elementary. Inside the strip the two sides nearly cancel.
Measured at 0.51+17.5i: archimedean real part 0.512, zeta'/zeta
real part -0.510. The sign of that remainder, uniformly, is
the open step.

## Conditional obstruction: log-concavity of Phi

Each summand of the theta weight is strictly log-concave where
it is positive. With v = n^2 exp(4u),

    (log f_n)''(u) = 16 pi n^2 exp(4u)
        (-4 pi^2 v^2 + 12 pi v - 15) / (2 pi v - 3)^2.

The quadratic 4 pi^2 v^2 - 12 pi v + 15 has discriminant
144 pi^2 - 240 pi^2 < 0 and positive leading coefficient, so
the numerator factor never changes sign. For the n = 1 term,
(log f_1)'' + 70 has numerator, after clearing a positive
denominator,

    N(v) = -64 pi^3 v^3 + 472 pi^2 v^2 - 1080 pi v + 630.

N'(v) = -8 pi (24 pi^2 v^2 - 118 pi v + 135), whose roots are
both below 1, and the quadratic factor is positive for v >= 1,
so N' < 0 on [1, infinity). N(1) < 0, hence N < 0, hence
(log f_1)'' < -70 for every u >= 0.

The measured ratio of the n >= 2 terms to the n = 1 term is a
few thousandths near u = 0 (the n = 2 factor is order
exp(-3 pi)); no uniform tail bound is supplied here. Their contribution to (log Phi)'' near u = 0 is
about +3.3, measured, and appears negligible at sampled u >= 0.3.
These observations do not prove a uniform concavity margin for the sum:
small component weights alone do not bound their derivatives. The closed
bound above is only for f_1. Strict log-concavity of Phi with a uniform
margin remains an unproved input to the following obstruction.

Multiplying the weight by exp(t u^2) adds 2t to (log)''. If
(log Phi)'' <= -70 uniformly, every t < 35 gives strict
log-concavity of the flowed weight. This corrects the former reversed
inequality t > -35. The sufficient interval includes negative times.
Rodgers-Tao (2020) says every t < 0 already has a
non-real zero of H_t. A sufficient condition that survives
exp(-eps u^2) cannot prove the hypothesis: it would force
Lambda < 0. Applying that obstruction to log-concavity of this Phi
requires the uniform bound just identified; it is conditional here.

Dependency: Rodgers-Tao is a published theorem about this Phi,
checked against [arXiv:1801.05914v5](https://arxiv.org/html/1801.05914v5),
Theorem 1 and equations (1)..(4), on 2026-10-04. The conventions match:
H_0(z)=xi(1/2+iz/2)/8 and the flow multiplier is exp(t u^2). It is
used here only in the conditional obstruction, not as a
hypothesis of RH.

## Killed sufficient condition: positivity of the weight

An even positive rapidly decaying weight need not have a
cosine transform with only real zeros. Witness, measured at
25 decimals in the session and re-checked by
`check_logderiv.py` at working precision:

    Phi(u) = exp(-(u-0.3)^2/0.02) + exp(-(u+0.3)^2/0.02)
           + 0.3 [exp(-(u-2)^2/0.05) + exp(-(u+2)^2/0.05)]

is positive, and its cosine transform vanishes at
1.620045852500311 + 0.641606247831350 i.
Positivity of the theta weight is not the missing step.
Davenport-Heilbronn already kills functional equation plus
Hadamard product. Beurling systems kill an Euler product alone.
The two have to be entangled. The equivalence above is that
entanglement written as one inequality, not a proof of it.

## Formal-statement check

(1) is the original problem: nontrivial zeros, real part 1/2.
(2) is classically equivalent to (1); the derivation above records that
under D1-D2, and (2) is not adopted in place of (1).
No resolution is claimed, and no new result.
