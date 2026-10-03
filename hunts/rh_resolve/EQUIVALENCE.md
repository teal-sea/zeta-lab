# Equivalence: RH iff the logarithmic derivative stays positive

Grade: derived argument, with two numerical spot checks in
`check_logderiv.py`. Not a resolution of RH. Not kernel-checked.
The reserved enclosure word is not used: nothing in this file is
an enclosure.

Statement under test, unchanged: every nontrivial zero of zeta
has real part 1/2.

## Theorem

Let L(s) = xi'(s)/xi(s). The following are equivalent.

1. Every nontrivial zero has real part 1/2.
2. Re L(s) > 0 whenever Re s > 1/2.

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

D4. Growth: off small disks about the zeros, L(z) = O(log |z|).
    This is the classical convex bound, used only to kill the
    integral at infinity. It is not re-proved here.

## Proof

(2) implies (1). A zero of multiplicity m at rho with
Re rho > 1/2 contributes m/(s-rho). On the open half-plane,
points immediately to the left of rho have
Re(m/(s-rho)) < 0, and the rest of L is holomorphic there.
So (2) forbids every such rho.

(1) implies (2). The functional equation gives L(s) = -L(1-s),
so L(1) = -b. Integrate L(z)/(z(1-z)) over circles of radius
tending to infinity that pass between zeros. The integrand is
O(log |z| / |z|^2), so the integral vanishes (D4). Residues:
1/(rho(1-rho)) at each zero, b at z = 0, and b at z = 1
(residue of 1/(z(1-z)) at z = 1 is -1, times L(1) = -b).
No other poles: the trivial zeros of zeta are cancelled by
the gamma factor inside xi. Therefore

    sum_rho 1/(rho(1-rho)) = -2b.

Under (1), rho(1-rho) = |rho|^2 and Re(1/rho) = (1/2)/|rho|^2,
so sum_rho Re(1/rho) = -b. The symmetrized Hadamard derivative
then collapses to

    Re L(sigma+it) = sum_gamma (sigma-1/2) / ((sigma-1/2)^2 + (t-gamma)^2),

every term positive for sigma > 1/2. Absolute convergence of
the symmetrized series is the 1/gamma^2 tail.

Spot check, not a proof of this direction: at 0.8+10i the
real part of L is 0.03177, and the Poisson sum over the first
200 ordinates is 0.03054. The residual 0.00124 is the tail
beyond ordinate 541, not a second formula. A wrong sign would
miss by the whole real part. `check_logderiv.py`.

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

## Killed sufficient condition: log-concavity of Phi

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

The ratio of the n >= 2 terms to the n = 1 term is at most a
few thousandths for u >= 0 (the n = 2 factor is order
exp(-3 pi)). Their contribution to (log Phi)'' near u = 0 is
about +3.3, measured, and negligible for u >= 0.3. So Phi is
strictly log-concave, with margin about 70. The +3.3 figure is
measured, not the closed bound; the closed bound above is only
for f_1.

Multiplying the weight by exp(t u^2) adds 2t to (log)''. For
every t > -35 the flowed weight remains strictly log-concave
if the measured margin holds. That interval includes negative
times. Rodgers-Tao (2020) says every t < 0 already has a
non-real zero of H_t. A sufficient condition that survives
exp(-eps u^2) cannot prove the hypothesis: it would force
Lambda < 0. Log-concavity is such a condition. It is killed.

Dependency: Rodgers-Tao is a published theorem about this Phi,
used here only to kill a sufficient condition, not as a
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
(2) is proved equivalent to (1), not adopted in place of (1).
No resolution is claimed.
