# robin_tfree: status at pause (2026-10-04)

**Unreviewed candidate, ordinary derivation plus enclosure-carrying computation.**
Not yet written up, reviewed, or added to the case log. Do not merge until it is.

## Claim (candidate)

For every prime x >= x0 = 29 996 208 012 611 (Morrill-Platt's verified range),
E(x) = log(e^-gamma prod_{p<=x} p/(p-1) / log theta(x)) <= 2.481e-8 (route A,
Buthe 2018 (1.6) only) or 2.342e-8 (route B, Buthe Table 1). Consequences:

- Robin's inequality holds for every 25-free n > 5040 (published record: 21-free,
  Axler, Ramanujan J. 2023). It also holds whenever nu_2(n) <= 24, nu_3 <= 14, nu_5 <= 9,
  nu_7 <= 7, ..., or q^(nu_q(n)+1) < 4.03e7 for any prime q.
- sigma(n) < (1 + 2.49e-8) e^gamma n log log n for every n > 5040 (Axler: 3.15e-7).

## Why it works

The partial-summation boundary term R(x)/(x log x) and the log theta(x) denominator
cancel exactly to first order (identity in `bound.py` docstring, checked on real
primes to 1e-25 in `test_bound.py`). Bounding them separately, as prior papers do,
costs 2.3e-8 and loses t = 25 (pinned by a test).

## Done

`bound.py` (Arb computation, writes `results.json`), `test_bound.py` (30 passing
tests: identity on real primes, closed-form integrals checked against quadrature,
bound dominates the true E(x) at x up to 3e6, planted weakened bound caught, inputs
checked, robustness: t = 25 survives adding 0.5 to every Table 1 entry).

## Left

1. RESULTS.md: full proof (reduction lemma, identity, second-order lemma |g| <= d^2/L),
   quoted inputs, novelty scope, and "The doors" (x0 is the active constraint;
   t = 26 needs exact theta on [x0, ~1e15]; link to Nicolas's primorial criterion).
2. MISSION.md with HuntSpec, RUNS.md, hunts/README.md case-log entry, docs/37 methods
   entry, `scripts/make_context.py`.
3. Independent adversarial review (fresh agent) of the derivation and the inputs.
4. Novelty search was cut off: checked Axler 2023, Morrill-Platt v1/v4, Assani et al.
   2025, Mishra-Sarkar 2026. Not checked: zbMATH/MathSciNet citations of Axler 2023.
