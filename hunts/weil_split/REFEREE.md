# Referee check of the per-place identity

Independent recomputation from the specification, 2026-10-30. Nothing here is a
result about the Riemann Hypothesis. This note only checks one identity for one
family of test functions.

## Verdict

Agree, at b = 3 and at b = 6.

sum_p cost_p equals -prime_term. prime_term is the signed sum
-2 sum_n Lambda(n) n^{-1/2} g(log n), the sign zeta.weil.explicit_formula_sides
returns.

At 50 decimal digits the residual sum_p cost_p + prime_term is
-1.4967482376516295618e-49 at b = 3 and -4.2764235361475130338e-49 at b = 6.
A repeat at 25 digits leaves +1.0339757656912845936e-25 and
-9.9261673506363320985e-24. The residual tracks the working precision. It does
not bind at 1e-16. The shift-series tail is below 1e-57 and does not bind.
Own rounding binds near 10^{-dps}.

If the right-hand side is taken to be that formula without the outer minus, the
two sides disagree by a global sign. The discrepancy is 8.1706874546148593931
at b = 3 and 40.317870967746705295 at b = 6. The first place is p = 2, where
the local discrepancy is twice the place cost: 2.60656932103 at b = 3 and
4.18678271705 at b = 6. The specification was not adjusted. The named identity
negates the formula, and that is the reading that agrees.

## Route

f is b^{-1/2} on [-b/2, b/2]. g is the convolution triangle (1 - |x|/b)_+ of
half-width b. Phi_p f is the sum over m >= 0 of p^{-m/2} f shifted by m log p.
The logarithm is natural throughout. ||Phi_p f||^2 was computed three ways: a
piecewise integral of the squared truncated sum, a truncated sum of exact
interval overlaps, and 3-point Gauss quadrature on each piece with the integrand
rebuilt from f. The truncation tail was bounded by the L2 triangle inequality.
cost_p = log p * ((1 - 1/p) ||Phi_p f||^2 - 1), summed over primes with
log p < b. The prime term was summed twice from the same definition: once by
walking prime powers from an independent sieve, once by scanning every integer
n < e^b with an independent Lambda. A third pass replaced the closed triangle
by a numerical convolution. A separate ball enclosure covers the full
prime-power sum, and the rectangle integral at p = 2, 3 and 5. The three norm
routes agree to about 1e-49. The prime-term routes agree to about 1e-50.
Afterwards zeta.weil.explicit_formula_sides was called with this g (support
hint b, dps 30). Only the prime term was compared, so the zero ordinate cap
was 30. The library returned the same prime term to its returned precision,
a difference of about 3e-31, with tail bound 0 and n_max = 20 and 403.

## Numbers

b = 3, eight primes, n <= 20. Sum of cost:
4.085343727307429696561618503698417636452.
prime_term:
-4.085343727307429696561618503698417636452.
Residual: -1.4967482376516295618e-49.

b = 6, 79 primes, n <= 403. Sum of cost:
20.15893548387335264729736861988705707285.
prime_term:
-20.15893548387335264729736861988705707285.
Residual: -4.2764235361475130338e-49.

Place costs in the landed table agree with these to one unit in the last float
place. The worst absolute difference is 2.2e-16, at p = 7, b = 6. The landed
cost sums are the float values of the sums above (difference 0). The landed
decomposition gaps, about -6.8e-17 at b = 3 and -3.6e-16 at b = 6, are that
float floor. They are not a gap in the identity.

## What is suspicious in the specification

The formula written beside the identity is prime_term, and prime_term is
negative for this g. The identity is the negation of that formula. Equating the
cost sum to the formula without the minus fails at every contributing place,
first at p = 2, by twice the place cost. Both comparisons are in the verdict.
The specification was not changed to force a match.

The given transform h(r) = (2/b)(1 - cos(br))/r^2 matches the integral of
g(x) cos(r x) to about 1e-51 at the sample points checked for b = 3, including
the r = 0 limit h(0) = b. It is not an input to this identity.

Each cost is a finite combination of log p, p^{-1/2} and b, not a rational.
The overlap sum is finite because g(k log p) vanishes for k log p >= b, and the
rectangle integral reproduces it. That checks the reduction for this family. It
is not a statement about a general test function.
