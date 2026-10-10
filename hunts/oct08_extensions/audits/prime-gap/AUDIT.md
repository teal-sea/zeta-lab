# Independent audit of the eighth-power claim

Claim: assuming every nontrivial zero of zeta has real part <= 7/8, every integer n >= 1 admits a prime p with n^8 < p < (n+1)^8.

**Primary verdict: conditional on named inputs.** The repaired analytic reduction and its finite enclosure cover pass this independent audit. Inputs are QRH(7/8), the classical explicit formula, and the published zero-count, zero-density and verified-height results identified below. QRH is an assumption, not established by this audit. The exact book text of the inherited explicit-formula input remains unverified here. No kernel checking or worldwide novelty determination is claimed.

Audit performed 2026-10-08 in a separate delegated context from the producer, using mathbox proof-audit and literature-check. Same model family may retain correlated errors. This is mathematical/code review plus independent checks, not independent formal proof.

## Pinned objects

- Repository base: f4ef0715bbe2f4890b3dcea034757ef0c823053a.
- Inherited PR276 proof: commit 1aff81ebbdb5b749c638a6450016e167f9b3f61e, hunts/qrh_prime_powers/RESULTS.md sections 1 through 6.4, and bound.py.
- Repaired density.py SHA256: ea2f62d92df2d8011131f973ef2570556f9c8d178e1fd14df4fccc5820335b55.
- base_bound.py SHA256: a5e2e54079979bbd71197ddddb4e45443bc027fe23a4692f7d44ea8e46410969. Verified byte-identical to pinned PR276 bound.py.
- Producer RESULTS.md SHA256: ae8887706fda55a3e00881963d4d8b80f943fee3920609279155683ed426c35f.

## Dependency graph and reconstruction

Classical explicit formula -> smoothed prime-power sum -> absolute zero-sum bound -> split at verified height and beta=17/20 -> KLN Stieltjes majorant -> finite interval cover plus monotone tail -> subtract proper prime powers -> prime existence. Small n=1,...,9 use explicit integer witnesses instead.

Let phi be the normalized quadratic spline supported on [0,1], w(t)=phi((t-x)/h), and W its Mellin transform. Direct integrations by parts give |W(beta+i gamma)| <= h*x^(beta-1)*g(|gamma|/a), where a=1+x/h and g(u)=min(1,9/(2u),216/u^3). The spline has integral 1, supremum 9/4, derivative L1 norm 9/2, and third distributional derivative total variation 216. These constants agree with the inherited code. Boundary values and first derivatives vanish; the support is contained in the closed interval, with w zero at its endpoints. The inherited phrase 'compact support in (x,x+h)' is technically imprecise but its integrations by parts remain valid.

The smoothed formula has main term h and trivial-zero subtraction integral w(t)/(t(t^2-1)) dt. Its sign, and the factor 2 from conjugate zeros, agree with the implementation. For positive ordinates above H, assign every zero the bound x^(-3/20), then add x^(-1/8) for the subset beta>17/20. This overcounts the exceptional subset but is a valid upper bound. Zeros at beta=17/20 stay in the first part; no limit in sigma is required.

Let F(t) count exceptional zeros up to t. Verified RH gives F(H)=0. With G(t)=g(t/a), integration by parts gives sum G(gamma)=integral_H^infinity F(t)(-G'(t)) dt. The boundary at infinity vanishes since F(t)=O(t^.4 log(t)^3.3) and G(t)=O(t^-3). G' vanishes below 9a/2, yielding start max(H,9a/2). An upper density bound must not be subtracted at H; the implementation does not do so. Strict/non-strict ordinate conventions differ only at countably many integration points and do not change this integral.

For B=max(H,9a/2), log(t)/log(B) <= (t/B)^(1/log(B)). Each density monomial therefore reduces to a power moment M(v). Directly integrating -G' gives, with c=sqrt(48)*a,

- B>=c: M(v)=648*a^3*B^-3/(3-v).
- B<c: M(v)=(9a/(2B))*(1-(c/B)^(v-1))/(1-v) + 648*a^3*B^-v*c^(v-3)/(3-v).

These are the implemented formulas. Relevant exponents are below 1. The full zero sum is monotone in a before bounding, so replacing a by its upper endpoint is valid even if the later majorant formula itself were nonmonotone.

Proper powers p^j contribute at most log(x+h)/j each. Their count is <=h/(j*x^(1-1/j))+1. Summing yields the stated P; dividing the weighted formula by 9/4 and subtracting P proves strict interval prime existence whenever its margin is positive.

For L>=40 the inherited tail function at theta=17/20 bounds only the full-count term and other errors; it does not assume QRH(17/20). The extra rare term uses a<=n and hence B=4.5n. Both moment exponents are <1/2, M(1/2)<2, log B<L+2, and 4.5^.4<2. Thus its error is <=72 exp(-.6L)(L+2)^4+16 exp(-L)(L+2)^2. Both decrease by logarithmic differentiation. This verifies the uniform tail, not a grid extrapolation.

## Obligation matrix

| Obligation | Status | Evidence |
|---|---|---|
| Quantifiers and strict endpoints | passed | Weight zero at endpoints; nine small witnesses separately checked |
| Conjugate factor and sigma equality | passed | Reconstruction above; density counts beta>17/20 |
| Stieltjes boundaries and density threshold | passed | F(H)=0; H exceeds original KLN threshold |
| Moment and logarithmic majorant | passed | Direct algebra plus independent quadrature checks |
| Complete finite cover | passed | 604 adjacent intervals [36/16,640/16], log10 above start |
| All decimal margins quoted here | passed | Certain Arb comparisons, 384 bits |
| Infinite tail | passed | Analytic monotonicity, all prerequisites independently checked |
| Small primality cases | passed | Exhaustive integer trial division for fixed witnesses |
| QRH(7/8) | conditional | Exact assumption; no audit of claimed OpenAI proof |
| Classical explicit formula source | conditional | Reduction reviewed; original book text not fetched |
| Published density constant calculation | external theorem | Exact source statement checked; author calculation not rerun |
| Lean/formal verification and novelty | out of scope | Neither asserted |

## Exact-source checks

KLN, arXiv:2101.12263v1, 2021-01-28, [Lemma 4.14, equation (4.71), section 5 Table 1](https://arxiv.org/html/2101.12263): at sigma=.85 and k=1, A=8.975 and B=3.588, applicable for T>=3.0610046e10. Enlarging to 9 and 4 gives the needed density bound. Important citation repair: introductory Theorem 1.1 says delta>=1 whereas Table 1 uses .303; Lemma 4.14 explicitly permits delta>0 and is the appropriate source. This audit accepts the paper's tabulated constants; it does not reproduce their optimization.

Bellotti-Wong, [arXiv:2412.15470v2, Theorem 1.1](https://arxiv.org/html/2412.15470v2), 2025-07-07: authenticated the second remainder bound and T>=e range. Code's coefficientwise larger constants are valid because log T and log log T are nonnegative there.

Platt-Trudgian, [arXiv:2004.09765, Theorem 1](https://arxiv.org/pdf/2004.09765), page 2: checked the stated height 3,000,175,332,800. The source computation itself was not rerun.

Montgomery-Vaughan, Multiplicative Number Theory I, Theorem 12.5: inherited exact-source leaf, not reauthenticated. The smoothed limiting argument was checked from the formula as quoted in PR276; dominated convergence and absolute convergence of the smoothed zero sum are adequate. A precise primary-source check of this leaf is the cheapest remaining source task.

## Defect found and repair

Original density.py SHA641d8e86b12da1a8b6b916fc2226334a1b21f920582623ba2b7dabb1c2a9f92c rounded B=max(H,4.5*a) upward via .upper(). This could omit a positive integration sliver. At L=30, the computed t1 already had radius about 7.6e-65. A large positive margin alone does not license that step.

Producer removed .upper(), retaining the ball enclosure for the true integration endpoint. Subsequent ball evaluation encloses the exact expression. Reviewed the repaired source and replayed checks afterward. This is a resolved rigor defect, not a counterexample to the mathematical claim.

## Reproduction and safe conclusion

From zeta-research:

```
.venv/bin/python -B ../audits/prime-gap/check.py
.venv/bin/python -B ../routes/prime-gap/density.py
```

check.py independently reconstructs four moment integrals using numerical quadrature (corroboration only), then checks all 604 interval margins >.95468 at 384 bits, fixed witnesses, and uniform tail error <.045583. Output is check-output.txt. The cover replay still imports the producer's bound implementation, so numerical independence is limited; the independent analytic reconstruction is what audits that implementation.

Strongest safe statement: the repaired written reduction establishes the desired conditional all-n result given the named standard source inputs and the stated half-plane assumption, with enclosure-carrying numerical inequalities and exact small witnesses. Exact primary authentication of the explicit-formula leaf remains outstanding. No evidence found of a remaining gap in the new density argument.
