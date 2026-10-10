# Seventh-power multistrip audit

**Claim:** If all nontrivial zeros of zeta have real part <=7/8, then every integer n>=1 admits a prime strictly between n^7 and (n+1)^7.

**Primary verdict: conditional on the named input QRH(7/8).** The written implication, with the cited standard published inputs, passes this independent audit. All 764 interval margins exceed .13045 at 384-bit precision in an independently implemented density integrator. The uniform tail error is <.012961. No remaining mathematical gap was found. This is a written proof with enclosed arithmetic, not a kernel-checked theorem or a novelty determination.

## Pinned scope

Date: 2026-10-08. Auditor: independent_audit, a separate delegated context from the author, using mathbox proof-audit. Same model family remains a possible source of correlated error. Producer code was read-only throughout.

- Lab base: f4ef0715bbe2f4890b3dcea034757ef0c823053a.
- Inherited PR276: 1aff81ebbdb5b749c638a6450016e167f9b3f61e.
- routes/prime-gap-multistrip/layers.py SHA256: `457c1144f45640888656599e744a8e73877d59999ca14ab655c4231f7af0dbe5`.
- Producer RESULTS.md SHA256: `dea8cc623e534b8294b2271f10b063c17d7534453773a5e255e5bd8b9e357918`.
- Producer verification.txt SHA256: `31b28b250e36ba26bbc218f1baf6a7543e4731aa0063c984104acd0f951a3dab`.
- Inherited base_bound.py SHA256: `a5e2e54079979bbd71197ddddb4e45443bc027fe23a4692f7d44ea8e46410969`.

## Dependency graph

Exact explicit formula and spline transform -> prime-power weighted identity -> positive-ordinate zero bound, with conjugate factor 2 -> pointwise multistrip majorization -> positive Stieltjes density integrals -> finite cover and monotone infinite tail -> subtract proper prime powers -> strict prime existence. Nine small witnesses cover n<=9.

The inherited formula, weight, zero-counting and prime-power steps are reviewed in ../prime-gap/AUDIT.md. The formerly outstanding Montgomery-Vaughan source leaf is closed in ../prime-gap/SOURCE-CHECK.md. No part of this audit validates the claimed proof of QRH itself.

## Independent derivation of the new step

Let 3/4=s0<s1<...<s5=7/8, with intervening values .8,.85,.86,.87. Define f(s)=x^(s-1), x>1. For a zero with beta in (s[j],s[j+1]], the nonzero indicators in

    f(s0) + sum_j (f(s[j+1])-f(s[j])) * 1[beta>s[j]]

telescope exactly to f(s[j+1]), which is >=f(beta). For beta<=s0 the value is f(s0). At beta=s[j], the strict indicator correctly yields f(s[j]), not the next endpoint. This includes beta=7/8 without any strictness assumption on QRH. Every coefficient is nonnegative. In particular, replacing exceptional zero counts by upper bounds is legitimate: the argument never subtracts one independently estimated count from another.

With y=log x and t<=7/8,

    Delta_j(y) = y * integral_{s[j]}^{s[j+1]} exp(-(1-t)*y) dt,
    Delta_j'(y) = integral exp(-(1-t)*y) * (1-(1-t)*y) dt <=0

for y>=8. Throughout the finite cover y=7L>=15.75, so evaluating Delta at the left endpoint is safe. Each actual zero sum weighted by G(gamma/a) increases with a; evaluating a at the right endpoint and only then applying its upper majorant is safe. Monotonicity of the later closed-form majorant itself is not required.

The exceptional zero count at every split is zero below the verified height. Its Stieltjes boundary term there vanishes. Hence its weighted sum is bounded by the integral of the published density majorant against -G', starting at max(H,4.5a). The repaired Arb endpoint is retained as a ball. The independent checker verifies that H versus 4.5a, and B versus sqrt(48)a, are separated at every cell, so no undecided branch is used.

The rare integrals are independently evaluated in check.py from primitive antiderivatives. It does not import producer layers.py or density.moment. It does reuse the inherited base_bound.py for the already audited full zero count, spline constants, interval data and ordinary tail. This limits computational independence and is stated explicitly.

## Tail reconstruction

For L>=50, Bernoulli gives a<=1+n/7<=n. Replace a by n in the positive zero sums. Then B=4.5n>H, L<log B<L+2. For a density row write r=8(1-s)/3 and q=5-2s. All r<=2/3, q<4, and r+q/log B<.8. The second log term has exponent 2/log B<.8. Since t/B>=1, the power moment increases in its exponent. The checks establish M(.8)<3 and 4.5^(2/3)<3.

Thus R_s <=9A*n^r*(L+2)^4 +3C*(L+2)^2. Dropping the negative summand in Delta gives 2Delta*R_s at most

    18A*exp(-(7(1-t)-r)L)*(L+2)^4
    +6C*exp(-7(1-t)L)*(L+2)^2.

Every decay exponent dominates the corresponding logarithmic derivative, 4/(L+2) or 2/(L+2), at L=50 and therefore for all larger L. The inherited baseline tail at theta=3/4 bounds the baseline error only; it does not introduce QRH(3/4). Its prerequisites and decreasing monomials also pass. Summing all tail majorants at 50 yields <.012961. This proves uniformity on the infinite interval, rather than extrapolating sampled values.

## Source authentication and obligation matrix

Checked primary [KLN arXiv:2101.12263v1, section 5 Table 1](https://arxiv.org/html/2101.12263), using Lemma 4.14 and equation (4.71): the .75,.8,.85,.86,.87 rows all have k=1. Every A and C in the code rounds the corresponding printed constant upward. Their common threshold 3.0610046e10 is below H. Strict beta>s and positive ordinates match the required counts. The source's tabulated constant calculations are accepted as published inputs, not independently rerun. The introductory theorem's delta restriction mismatch is avoided by the checked Lemma 4.14.

| Obligation | Status | Basis |
|---|---|---|
| Pointwise telescope and equality boundaries | passed | Algebra above; exact rational atom tests |
| Positive coefficients and interval monotonicity | passed | Integral derivative; y>=8 |
| Stieltjes boundary and endpoint enclosure | passed | Prior audit plus branch checks in every cell |
| All 764 cells and start/end coverage | passed | Independent 384-bit implementation, [36/16,800/16] |
| Infinite tail and domains | passed | Analytic derivatives and certain arithmetic comparisons |
| Small cases and strict endpoints | passed | Nine proposed witnesses independently trial-divided |
| Density, zero-count and height sources | passed | Exact source checks here and prior audit |
| Explicit-formula primary source | passed | Prior SOURCE-CHECK.md closes original caveat |
| QRH(7/8) | conditional | Assumed; its proof is outside this audit |
| Worldwide novelty and Lean | out of scope | Neither claimed |

## Falsification and replay

check.py tests exact synthetic zero atoms at every split and inside each bin. It chooses x=2^1000 so all tested weights are rational powers with integral exponent, requiring no numerical tolerance. Removing the first layer or the last layer gives a strict underbound for a suitable atom; those mutants are rejected. The unchanged independent numerical bound fails for k6 at L29 with margin below -56, while k7 passes. This is a counterexample to positivity of that bound, not a counterexample involving primes.

The nine proposed k7 primes were checked independently by exhaustive trial division through their integer square roots, and their n values checked to be exactly 1 through 9 with strict interval membership.

From the zeta-research directory:

```
.venv/bin/python -B ../audits/prime-gap-multistrip/check.py
```

Full output is check-output.txt. The serial run took under one second and used no paid compute. An initial assertion comparing two overlapping Arb enclosures of the same rational 2/3 was indeterminate; the checker was corrected to compare the exact rational exponents. This was an audit-check implementation issue, not a producer defect.

No producer code change was needed. Documentation should now link the closed explicit-formula source audit instead of saying that source check is ongoing. The seventh-power conditional conclusion is stronger than the previous eighth-power candidate, under the same QRH hypothesis and the explicitly cited additional density rows.
