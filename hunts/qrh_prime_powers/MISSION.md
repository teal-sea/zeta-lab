# Primes between consecutive k-th powers from the 7/8 half-plane

Base commit: `ef4e0564` (origin/main), branch `hunt/qrh-prime-powers`.
Status: construction hunt. Its claims are candidates pending external review.

## Question and scope

OpenAI's quasi-Riemann theorem (zeta has no zero with real part above 7/8;
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` in the lab's Lean
statement, kernel-checked on two kernels per the lab record on the unmerged
PR #271) is new input. Its argument has no human review. This hunt
uses the theorem as a hypothesis and does not re-check it.

The target: the least k for which a prime lies strictly between n^k and
(n+1)^k for every n >= 1, with every constant explicit and every numerical
step carried by Arb enclosures. Since (n+1)^k - n^k is about k x^(1-1/k) at
x = n^k, a 7/8 half-plane can only decide k with 1 - 1/k > 7/8, so k = 9 is
the floor of the method. By-products: an explicit short-interval theorem
and an explicit pointwise bound for psi(x) - x of size x^(7/8) log^2 x.

The comparison record is unconditional: k = 86 (E. S. Lee, arXiv:2602.14340),
before that k = 90 (Cully-Hugill and Johnston, Funct. Approx. 73 (2025)).
Every external input is cited from a located source in `RESULTS.md`.

## Alternatives inspected

A truncated explicit formula with an explicit O(x log^2 x / T) error
(Cully-Hugill and Johnston) loses a logarithm and needs T < x; a smooth
compactly supported weight gives an exact, absolutely convergent formula
with no truncation error, so it is the route chosen. Explicit zero-density
estimates would lower k below 9 but are a separate information class; they
are recorded as a door, not attempted.

## Resource boundary

Serial pilots only, one process, pytest `-n0`, under 3 GB and about 60
CPU-minutes in total, no paid compute, no Lean build. Write only in this
directory, its case-log entry in `hunts/README.md`, one entry in
`docs/37-methods.md`, and `CONTEXT.md` via `scripts/make_context.py`.
No push and no pull request: the lead reviews and pushes.

```huntspec
id: qrh_prime_powers
question: Given zeta has no zeros with real part above 7/8, what is the least k with a prime between n^k and (n+1)^k for every n >= 1, with explicit constants?
frontier: unconditional record k = 86 (Lee, arXiv:2602.14340v2, Theorem 1.2); k = 90 before it (Cully-Hugill and Johnston, arXiv:2402.04272v3, Theorem 1.4); the half-plane method cannot go below k = 9
proposed_attack: exact explicit formula for a quadratic B-spline weight, zeros split at the verified RH height, zero sums bounded through explicit N(T) bounds in closed form, an Arb interval cover in log n, an analytic tail, and Pratt-certificate witnesses for small n
dead_routes:
  - truncated explicit formula with O(x log^2 x / T) error, which costs a logarithm and caps the truncation height below x
required_oracles:
  - Arb ball arithmetic for every numerical inequality, decided only by certain comparisons
  - Pratt certificates checked by integer arithmetic alone
  - direct prime-power summation against the explicit formula with 1000 tabulated zeros
  - mpmath quadrature of the zero-sum integrals as a second route to the closed forms
kill_conditions:
  - the explicit-formula normalisation disagrees with a direct prime-power sum
  - a closed-form zero-sum integral disagrees with quadrature
  - some interval of the cover or the tail fails its margin under enclosure
  - the weakened abscissa 15/16 does not move the least k from 9 to 17
agents_may:
  - search
  - derive
  - code
  - attack
  - run bounded serial pilots
agents_may_not:
  - declare novelty without a recorded search
  - declare theorem status beyond the written proof and its review state
  - promote their own claim
  - edit shared mathematical implementations
```
