# MISSION: the prime side, place by place, for a compactly supported test function

**Scope:** `hunts/weil_split/`. Nothing outside this directory is modified.
**Status:** exploratory. Nothing here is a result about the Riemann Hypothesis.

## Why this differs from `local_positivity`

`hunts/local_positivity` decomposed the prime side into local norms `Q_p` and
found that every place is positive (given Ramanujan-type bounds) and that the
local norms do not assemble globally. It could not say *where the covering mass
sits*, because its gate works on Toeplitz sections of local coefficients, not on
an `L^2` norm of a concretely shifted function.

For a **compactly supported** `f` the shift operator is finite:
`Phi_p f = sum_{m>=0} p^{-m/2} f(. - m log p)` has finitely many overlapping
terms, so `||Phi_p f||^2` is an exact finite sum of rectangle overlaps. With
`f = b^{-1/2} 1_{[-b/2, b/2]}` and `g = f * f` (the triangle), every `Q_p` is
an exact finite sum (not rational: it carries `p^{-1/2}`, `log p` and `b`;
corrected 2026-10-30), and the per-place energy

    cost_p = log p * (Q_p - 1),     Q_p = (1 - 1/p) ||Phi_p f||^2

is exact, and is non-negative wherever the shifted copies pile up. Then

    W(h) = pole + arch - sum_p cost_p,

and the question this hunt asks is: **how is the cost distributed over the
primes, and does the distribution move as the test function widens?**

## Check that must pass first

`E` computed place by place must equal `-prime_term` from
`zeta.weil.explicit_formula_sides`, which computes the prime side as a sum over
prime powers. If they disagree the decomposition is wrong and nothing else here
counts. The zero side gives a second, independent check on `W` itself.

## What this may not claim

- Not evidence for RH. `E <= pole + arch` on finitely many `b` is what it says.
- The test functions are a one-parameter family of rectangles; no statement
  survives outside it.
- Raghavan/Ramanujan-type bounds are not proved here; where `Q_p > ||f||^2` the
  place is reported with a negative `e_p` rather than hidden.

## HuntSpec

```huntspec
id: weil_split
question: How is the prime side of the Weil functional distributed over places, for a compactly supported test function?
frontier: measured here, the per-place cost spreads from 4 places carrying 98 percent in their top three to 429 places carrying 13 percent, while the covering margin falls from 3.0e-2 to 1.6e-4
proposed_attack: exact rectangle-overlap norms of the shift operator, giving each place an exact closed-form cost (not rational: it carries log p and p^(-1/2); corrected 2026-10-30)
dead_routes:
  - finitely many important primes doing the covering, killed here by the falling top three share
required_oracles:
  - exact closed-form rectangle overlap sums
  - equality of the per place sum with the explicit formula prime term to 1e-16
  - the verified zero list for the covering ratio
kill_conditions:
  - the per place sum disagrees with the prime term
  - the covering ratio is quoted from the slow quadrature instead of the zero side
agents_may:
  - decompose
  - measure
  - compare
  - code
agents_may_not:
  - declare a bound
  - promote an observation to a result
  - use the reserved vocabulary of zeta/rigor.py
```
