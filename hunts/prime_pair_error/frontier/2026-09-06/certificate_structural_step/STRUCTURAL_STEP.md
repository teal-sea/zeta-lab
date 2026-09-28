# A targeted structural extension of the factorial-certificate pilot

Date: 2026-09-06.
Status: elementary deduction plus two computed seed instances, checked by exact integer arithmetic and rational logarithm enclosures. No independent proof review, LP optimality proof, literature novelty, improved prime-counting record, or improvement to the total CHHL error is asserted. This directory is a new conversation output; it has not been pushed to GitHub.

## 1. Existing inputs and the intended change

The repository pilot at `hunts/prime_pair_error/frontier/2026-09-06/factorial_certificate_pilot/PILOT.md` (blob `56a2b2d0e246ca04c480146c1d9eef22ac6360aa`) has seeds

    g(t) = sum_{j|L} a_j floor(t/j),
    sum a_j/j = 0,
    g >= 0 on one full period,
    g >= 1 on [1,M),  2 <= M <= L.

The completed review of that argument is separate from the new deductions here. Existing PR #196 compared three objectives on fixed seed spaces. This pass changes the allowed denominator space once, for a mathematical reason: an omitted prime index forces overcount in the lifted weight.

The arithmetic/factorial framework is classical; Bober discusses Chebyshev's construction and related floor sums. The omitted-prime observation below is an elementary deduction for this particular pilot, without a priority claim.

## 2. Omitted-prime lemma

Define the pointwise finite sum

    W(t) = sum_{k>=0} g(t/M^k).

Terms vanish when t/M^k < 1. The pilot proves W(t)>=1 for t>=1. Define

    kappa = integral_1^infinity g(t)/t^2 dt,
    C = kappa/(1-1/M).

Because g is nonnegative, Tonelli and rescaling yield

    C = integral_1^infinity W(t)/t^2 dt,
    C-1 = integral_1^infinity (W(t)-1)/t^2 dt.       (1)

The actual coefficient indices in W are j*M^k with j|L. At an integer n, the jump of floor(t/d) is one exactly when d|n. If p is a prime with p not dividing L*M, the only such coefficient index dividing p is 1. Therefore

    W(p)-W(p-1) = a_1.

At t=1, W(1)=g(1)=a_1>=1. As W(p-1)>=1,

    W(p)>=2.

All breakpoints are integers, so W(t)>=2 throughout [p,p+1). The intervals for distinct primes are disjoint. Equation (1) proves

    C-1 >= sum_{p prime, p not dividing L*M} 1/[p(p+1)].       (2)

Any finite sub-sum gives a rigorously computable lower bound. In particular, for L=2310 and M=15, using only primes 13 through 101 gives

    C-1 >= 4636340182006290715180151332142930117383 /
            234725263273365339787263823415551421974560
         = 0.019752199304625868... .

This is not an optimality certificate for the observed C=1.069854... . It proves that no change of objective or coefficients INSIDE THIS FIXED (L,M) SPACE can remove the entire leading excess. More generally, keeping the same finite set of prime divisors in all coefficient indices leaves a fixed positive gap via any excluded prime. New prime indices must enter a family whose C tends to 1. This is a restriction on the stated certificate class, not on all possible prime proofs.

## 3. One controlled extension

Keep M=15. Enlarge L=2310 to 13*2310=30030. This permits 13 and its products with divisors of 2310 among the floor denominators. It includes the old feasible seed by setting new coefficients to zero, so an exact minimum could not worsen; no exact optimum is asserted here.

A floating LP proposes each coefficient vector; exact rational reconstruction is then checked against every full-period constraint. An independent checker redoes the floor sums with Python integers rather than the LP matrix. Balance is checked with Fraction arithmetic.

| L | M | C (approx.) | coefficient mass A=sum abs(a_j) | W(12) | W(13) |
|---|---|---|---|---|---|
|2310|15|1.06985445257346424|15|1|2|
|30030|15|1.05580511754015490|39|1|1|

The new seed's coefficients are in `checked_results.json`. Denominator 3 suffices for all coefficients. Balance is zero; all 30,030 residues satisfy the appropriate nonnegative/cover constraints. The old seed is rechecked on 2,310 residues. This verifies valid seeds for the already-proved rescaling argument, not only validity through a sampled N.

The constant comparison is supported by rational intervals, not just a floating LP objective. For integer n, write n=2^e*r with 1<=r<2 and use

    log(r) = 2 sum_{k>=0} u^(2k+1)/(2k+1),
    u = (r-1)/(r+1).

After K terms the positive omitted tail is at most

    2*u^(2K+1)/[(2K+1)*(1-u^2)].

Use the same formula at r=2 for log(2), then combine intervals respecting each signed coefficient. With K=32 the intervals are disjoint and show C_new<C_old by exact rational arithmetic.

## 4. Account for the cost, not just the new constant

Both true factorial certificates B_N and the pilot's full sufficient envelope U_N were evaluated at 60 digits. Those evaluations are high-precision diagnostics, not interval enclosures. Feasibility and the constant comparison are independently exact as described above.

| N | old B_N | new B_N | old U_N | new U_N |
|---|---|---|---|---|
|10000|10681.264020|10533.543704|11067.229101|11516.971972|
|1000000|1069825.692303|1055759.569096|1070578.443304|1057687.644952|
|100000000|106985409.756940|105580426.553620|106986630.766850|105583595.088806|
|1000000000000|1069854452477.9289|1055805117379.8049|1069854455063.3176|1055805124013.9732|

The new seed lowers B_N in these four comparisons. At N=10000 it nevertheless raises U_N because the proven coefficient-mass allowance increases. This preserves the distinction found by PR #196; it is not hidden by selecting one metric.

Asymptotically the main coefficient improves, but it is still above 1 by a fixed amount. This one extension is not an RH-scale result, an analytic family, or a modern prime-counting improvement.

## 5. Next mathematical task: an extension rule with a uniform tradeoff

The proposed next step is to derive a rule for a new seed from an old one, rather than ask a solver for a separate table at every period. Write

    g_new(t) = g_old(t) + h_p(t),
    h_p(t) = sum_{j|pL} b_j floor(t/j),
    sum b_j/j = 0.

To remain in the pilot class, prove the final g_new>=0 everywhere and g_new>=1 on [1,M). The correction h_p itself may be negative; it is not a separately required majorant. Track its effect on C and A, including any retuning of the old coefficients. Merely adding the next prime to the support or finding another smaller C does not supply such a rule.

For clarity, one SUFFICIENT (not necessary) long-run tradeoff would be a family of valid seeds satisfying, with constants independent of the family index r,

    C_r - 1 <= c*2^(-r),
    A_r <= a*2^r.

The pilot then gives, uniformly,

    psi(N)-N <= c*N*2^(-r) + O(a*2^r*(log N)^2).

Choosing 2^r comparable to sqrt(N)/log N would yield O(sqrt(N)*log N), an RH-sufficient one-sided bound. Neither rate has been proved here. This states the actual strength required of a construction, not a new reduction claimed as a solution.

The measured first extension shrinks C-1 by about 20% while multiplying A by 2.6. It does not meet the example half-gap/double-mass tradeoff. It establishes only that the structural enlargement removes one forced overcount and lowers the constant, at a quantified cost.

## 6. Reproduction and boundaries

    OPENBLAS_NUM_THREADS=1 python probe.py
    OPENBLAS_NUM_THREADS=1 python check_and_compare.py

Dependencies: numpy, scipy, mpmath. The LP stage took about 8.1 seconds in this run. The independent checker verified 32,340 full-period residues with exact Python integers and enclosed the logarithmic constant comparison with rational arithmetic. Complete coefficient vectors and results are saved.

No original repository files were changed, no agents were launched, no GitHub PR was created, and nothing was merged. No larger sweep, optimization-optimality proof, independent referee review, or literature novelty claim is included.

Sources:
- Zeta Lab pilot, exact source and blob above.
- Bober, Factorial Ratios, Hypergeometric Series, and a Family of Step Functions, Chebyshev discussion and floor-sum framework: https://arxiv.org/html/0709.1977
- CHHL, The error term in counting prime pairs, Section 3 for prime-counting oscillation implications: https://arxiv.org/html/2308.14888v1
