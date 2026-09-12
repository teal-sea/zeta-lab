# Factorial upper-certificate pilot

Date: 2026-09-06. Executed in this chat. Not committed to Zeta Lab.

**Status:** numerical coefficient search followed by independent exact-rational feasibility checks and the elementary general argument below. This is not an independently refereed analytic result, a novelty claim, a better known prime-counting bound, or an improvement to total CHHL E(N). The smallest example recovers Chebyshev's classical construction.

## 1. A finite check that supplies certificates at every cutoff

Choose integers L >= M >= 2 and rational coefficients a_j, with each denominator index j dividing L. Define

    g(t) = sum_{j|L} a_j floor(t/j).

Require

    sum_j a_j/j = 0,
    g(r) >= 0  for r=0,...,L-1,
    g(r) >= 1  for r=1,...,M-1.

These are checked with rational/integer arithmetic, not a floating tolerance.
The balance identity gives g(t+L)=g(t). All breakpoints are integers, so checking one full integer period establishes nonnegativity for EVERY real t>=0, and g(t)>=1 on [1,M).

For a positive integer N put K=floor(log_M N), calculated using integer powers, and

    W_N(t) = sum_{k=0}^K g(t/M^k).

If 1<=t<=N, choose k=floor(log_M t). Then t/M^k lies in [1,M), so that term is at least one and the remaining terms are nonnegative. Thus W_N(t)>=1 for every such t. This is a general proof, not extrapolation from the test cutoffs.

The coefficients of W_N are the seed coefficients repeated at the index scales j*M^k; their number is at most O(log N) for a fixed seed, before combining repetitions.

## 2. Exact prime-weight upper certificate

Let Lambda be the von Mangoldt function, including proper prime powers, and psi(N)=sum_{d<=N} Lambda(d). The standard identity sum_{d|n} Lambda(d)=log n yields

    B_N = sum_{k=0}^K sum_j a_j log(floor(N/(j*M^k))!)
        = sum_{d<=N} Lambda(d) W_N(N/d)
        >= psi(N).

The rightmost inequality uses Lambda(d)>=0. There is no RH assumption.
Negative coefficients are allowed because the FINAL weights W_N are nonnegative and at least one. Coefficients are proposed without prime data.

## 3. What the certificate costs asymptotically

Write A=sum_j |a_j| and

    kappa = -sum_j a_j log(j)/j,
    C = kappa/(1-1/M).

For y>=0 (with 0 log 0=0), integral comparison with log t gives

    |log(floor(y)!) - (y log y-y)| <= 1+log^+(y).

For y>=1 this follows from

    m log m-m+1 <= log(m!) <= m log m-m+1+log m,
    0 <= (y log y-y)-(m log m-m) <= log y,
    m=floor y;

for 0<=y<1 the inequality follows directly.

The balanced coefficient sum cancels the x log x and x terms. Consequently

    |sum_j a_j log(floor(x/j)!) - kappa*x| <= A(1+log^+ x).

Adding the scales gives the fully quantified bound

    B_N <= kappa*N * (1-M^(-K-1))/(1-1/M)
           + A[(K+1)(1+log N) - log(M)*K(K+1)/2].

Also kappa=integral_1^infinity g(t)/t^2 dt: integrate the floors to a finite R, use their harmonic-number expression, and cancel the divergent coefficient by sum a_j/j=0. Since g>=1 on [1,M) and nonnegative everywhere, kappa>=1-1/M>0. Therefore

    psi(N) <= B_N <= C*N + A(K+1)(1+log N),
    B_N = C*N + O_{a,M}(log^2 N).

No floating decimal is needed to validate the factorial inequality. The decimals in the output only approximate the exact logarithmic constant C.

## 4. The actual small search

The LP searches all denominator indices dividing L, with M=2,...,30, at L=30,210,2310. It minimizes C in floating point, then reconstructs rational coefficients and independently checks balance and all period constraints using Python integers/Fractions. A failed reconstruction is an error, not silently accepted.

87 numerical candidates passed exact feasibility checking. The best values FOUND in each grid were:

| L | M | nonzero coefficients a_j | C (approximate) |
|---|---|---|---:|
|30|6|a_1=1; a_2=a_3=a_5=-1; a_30=1|1.105550427521|
|210|6|a_1=1; a_2=a_3=a_5=a_7=-1; a_10=a_14=a_30=1; a_42=a_210=-1|1.073965360073|
|2310|15|a_1=1; a_2=a_3=a_5=-1; a_6=1; a_7=-1; a_10=1; a_11=-1; a_30=-1; a_33=a_105=1; a_210=a_330=-1; a_385=1; a_1155=-1|1.069854452573|

No exact LP dual or global optimality proof is supplied. The valid certificates, not their optimality, are what the exact checker establishes.

Supplemental checks: each selected seed was lifted and checked at EVERY integer t through N for N=30,100,1000,10000 (12 full finite-cutoff tests). For N=100, each of the 25 prime exponents on both sides of the factorial identity was independently checked (75 exact identities across the three candidates). No sampled prime table supplies the coefficient search.

## 5. Already known versus possible next research

The L=30 seed is precisely Chebyshev's classical step function. Bober explicitly discusses it and the associated factorial ratio. This is a positive control, not a discovery.

The L=210 and L=2310 candidates improve the starting template's constant. They do NOT improve modern prime-counting bounds: the prime number theorem already gives psi(N)/N -> 1. No claim is made that these particular coefficient vectors are new. The larger seeds are not restricted to 0/1-valued step functions, so Bober's optimality discussion for that restricted class does not decide the broader rational LP.

A fixed seed leaves C>1. In fact, by periodicity g>=1 again on [L+1,L+2), which lies beyond [1,M); hence

    C-1 >= [1/(L+1)-1/(L+2)]/(1-1/M) > 0.

This is an elementary limitation of this fixed-seed construction, not of factorial certificates in general.

To pursue RH through a varying family, both the leading excess and the coefficient/error budget would need control. The explicit sufficient upper bound is

    B_N-N <= (C-1)N + A(K+1)(1+log N).

Thus getting a sequence of constants closer to 1 is not enough. One must select seeds as N grows and prove that the WHOLE right-hand side is O_epsilon(N^(1/2+epsilon)), for every epsilon>0. This is a substantive missing argument, not supplied by the 87 LP runs. No new RH bound is claimed.

A focused next task is to understand how (C-1), coefficient mass A, and the complexity of proving full-period positivity vary together. Keep the primal upper certificate and its exact constraints separate from a numerical optimum. Do not scale a search merely to advertise another fixed constant.

## 6. How and where to work

This prototype was small: the complete saved run took about 3.1 seconds in the present environment. No GPU, external agent runner, Lean build, or desktop service was needed.

Recommended division of labor (a proposal, not a claim that jobs were launched):
- Here: propose coefficient families and derive their uniform cost bounds.
- One fresh Claude Code or Codex session in zeta-lab: independently check this seed-to-certificate argument and reproduce the exact certificates; then preserve the code/results and add counterexamples/regression checks.
- Larger parallel searches or formalization only when there is a specific mathematical family or stable lemma to justify them. No new Fulcrum/Ostoyae graph is needed for this 87-case pilot.

## 7. Primary references

- NIST DLMF, 27.5.5: von Mangoldt divisor identity and Möbius inversion.
  https://dlmf.nist.gov/27.5
- Jonathan W. Bober, Factorial Ratios, Hypergeometric Series, and a Family of Step Functions, introduction (Chebyshev construction) and Section 3 (factorial/floor-sum relation).
  https://arxiv.org/html/0709.1977
- Andrew Fiori, Habiba Kadiri, Joshua Swidinsky, Sharper bounds for the Chebyshev function psi(x): a modern explicit-error benchmark; the pilot does not compete with these bounds.
  https://arxiv.org/abs/2204.02588

## 8. Reproduce

    python -m pip install -r requirements.txt
    OPENBLAS_NUM_THREADS=1 python pilot.py --output results.json

`results.json` records every coefficient vector, exact feasibility checks, selected examples, and execution time. These checks do not establish novelty or the missing asymptotic family bound. This folder and its ZIP are new outputs attached to this chat, not an existing or missing repository input.
