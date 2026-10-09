# Small witnesses from the 7/8 half-plane, with explicit constants

Base commit: `ef4e0564` (origin/main). Branch `hunt/qrh-nonresidue`.

```huntspec
id: qrh_nonresidue
question: Given OpenAI's zero-free half-plane Re s > 7/8 for all Dirichlet L-functions, what explicit polylogarithmic bounds follow for the least character nonresidue, the least Miller-Rabin witness and the least primitive root?
frontier: OpenAI (Sept 30 2026) Corollary 1.2 gives n(p) <= C (log p)^32 with C unstated; Guo (8 Oct 2026) gives n(p) << (log p)^8 and g*(p) << (log p)^24 with absolute constants not computed; Bach under GRH gives 2 (log n)^2 for Miller witnesses
proposed_attack: Smoothed explicit formula with weight (n/x)^c log(x/n), zero sums bounded by the Hadamard identity at sigma0 = 2*theta + c, every constant enclosed in Arb, small moduli by exact subgroup generation
dead_routes:
  - Bounding the zero sum by x^(7/8) times an unweighted zero count without a decaying Mellin weight (the count diverges)
  - Vinogradov smooth-number amplification from the explicit formula alone (it needs full character sums, which the half-plane controls only beyond exp((log q)^(1-eps)))
required_oracles:
  - Arb ball arithmetic (python-flint) for every analytic constant, cross-checked against mpmath
  - exact enumeration of subgroup generation in (Z/qZ)^* for all small moduli
  - exhaustive least nonresidue, least primitive root and least strong witness tables computed by modular exponentiation
  - published record values (OEIS b-files, Jaeschke and Sorenson-Webster strong pseudoprimes) re-verified by direct computation
kill_conditions:
  - any computed least nonresidue, least witness or least primitive root exceeds the stated bound
  - a constant's Arb enclosure disagrees with the independent mpmath evaluation
  - the weakened-abscissa control (theta = 15/16) fails to change the measured exponent toward 16
  - a step of the written proof uses a zero location not supplied by OpenAI's Sept 30 2026 Theorem 1.1 plus the functional equation
agents_may:
  - search
  - derive
  - code
  - attack
  - run bounded local computations
agents_may_not:
  - declare novelty from an empty search
  - promote their own claim
  - alter shared mathematical implementations outside this hunt
  - launch heavy local work or paid compute
```

## Input theorem, used and not re-checked

OpenAI, "The Quasi-Riemann Hypothesis", Sept 30 2026, Thm 1.1 (subtitled
"A Zero-Free Half-Plane Re s > 7/8"): every Dirichlet L-function, including
zeta, has no zeros with Re s > 7/8 (the pole of zeta at s = 1 excepted). Its
Corollary 1.2 is the A = 32 nonresidue bound this hunt improves. The
Oct 5 2026 paper (human-assisted) proves the weaker 11/12 half-plane as its
Theorem 1.1 and cites the 7/8 paper as [36]. The lab's
kernel-checked statements are `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`
and `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (section 7 of the
new docs page on unmerged PR #271). No human has reviewed the 195-page argument, so every
result here is stated as "proved, given OpenAI, Sept 30 2026, Thm 1.1".

## Scope

Three targets, in order: (1) least n with chi(n) not in {0,1}, exponent
1/(1-7/8) = 8, explicit constant valid for every modulus q >= 3; (2) least
Miller-Rabin witness; (3) least primitive root, with the 2^omega(p-1) loss
handled by a sieve. Controls: exhaustive tables to 10^7 where the budget
allows, literature record values, and a weakened abscissa that must move the
exponent as predicted.

## Resource boundary

Four cores and 15 GB shared with three other agents. One heavy process at a
time, pytest with `-n0`, under 3 GB, about 60 CPU-minutes in total. No paid
compute, no push, no pull request. Writes only `hunts/qrh_nonresidue/`, its
case-log entry, `docs/37-methods.md` if a reusable method results, and the
regenerated `CONTEXT.md`.
