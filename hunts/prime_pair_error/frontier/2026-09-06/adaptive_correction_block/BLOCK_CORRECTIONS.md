# Adaptive carry shapes and small-prime masks: one accepted correction block

Continuation of the 2026-09-06 factorial-certificate investigation.

**Status:** a written all-cutoff construction, exact finite feasibility and logarithm checks, and a separate-code self-check by the originating ChatGPT session. No independent-agent or human review of this new work has occurred. No optimality, novelty, asymptotic refinement rate, modern prime-counting improvement, or improvement to total CHHL E(N) is claimed. No GitHub change or external-agent job was performed in this pass.

## 1. Result and exact starting point

The input is the unchanged `repair_cost_rule.zip` (SHA-256 `ea5fb1ab56e3515358e7ff54ed309fe9eb1e7e87b98e3991c80b7ccc91579582`). It includes the preceding two direct corrections at 20 and 21, not the rejected second attempt at 20. Its original independent-code checker was rerun successfully before the present search. That checker is a self-check from the earlier producing session, not an independent mathematical review.

The input itself is a continuation of the joint candidate reviewed in Zeta Lab PR #200 at `85a42e7c0c7dad8163dcab8d239bac5bb6fe1b38`. That review does not cover either the input's two direct corrections or the present block.

Use M=15, R=100000, and a common rational denominator 108. Denote by D the joint candidate's finite balanced seed, by g_* its fixed repair seed, and by F_old the finite direct update saved in the repair-cost input. Put

    V(t) = sum_{k>=0} g_*(t/15^k),
    W_base(t) = sum_{k>=0} D(t/15^k)
        + H0 sum_{m>=0} (m+1) g_*(t/(R*15^m)),
    W_old(t) = W_base(t) + F_old(t) + 6 V(t/R),
    H0 = 701/36.

The input establishes W_old(t)>=1 for t>=1. All sums are locally finite. D and g_* are fixed balanced floor sums, with masses 56345/108 and 15. The saved first-level mass ||D+F_old||_1 is 91127/108.

This pass finds a block h of 23 rationally weighted corrections. After adding 82 nonnegative repairs P and an explicit additional shield H V(t/R),

    W_new = W_old - h + P + H V(t/R),
    H = 2633/108,

is again a global majorant. Its leading constant is lower:

    C_old = 1.04590351044777009789513972597752956057210283983286...,
    C_new = 1.03411910424755277273462747901643856176993858443824... .

The decrease is 0.01178440620021732516..., approximately 25.7% of C_old-1. This is a percentage of one construction's leading excess, not a percentage of progress toward RH.

The complete sufficient factorial envelope is also improved for **every integer N>=10^6**, with all coefficient and shield costs included. At N=10^4 the actual factorial expression improves but its conservative envelope worsens; that comparison is retained. Taking the smaller of the two valid envelopes avoids any deterioration below the proved threshold.

## 2. The deliberate change in arithmetic ingredients

The old correction shape was

    b_q(t) = floor(t/q) - floor(t/(q+1)) - floor(t/[q(q+1)]),

always combined with the mask over divisors of 210. Here both the carry shape and that mask can vary.

For positive integers a,b,c satisfying

    1/a = 1/b + 1/c,

let

    b_(a,b,c)(t) = floor(t/a) - floor(t/b) - floor(t/c).

It takes only the values 0 and 1, since t/a=t/b+t/c. It vanishes for t<a and equals 1 at t=a when b,c>a. It is balanced. The complete two-denominator parametrization with a<b<=c is

    b=a+v, c=a+a^2/v, where v divides a^2 and 1<=v<=a.

Indeed (b-a)(c-a)=a^2 is equivalent to the reciprocal equation. These are classical binomial/factorial carry functions, not a new family claimed to have been discovered here; Bober discusses the corresponding factorial-ratio family [2].

For P in {1,2,6,30,210}, form

    h_(P;a,b,c)(t) = sum_{d|P} mu(d) b_(a,b,c)(t/d).

P=1 means no mask. These are finite balanced floor sums with integer denominator indices and bounded values. They need not be nonnegative. Their exact integral is

    kappa(h_(P;a,b,c))
      = (phi(P)/P) [log(b)/b + log(c)/c - log(a)/a].        (1)

This follows by dilation and the finite product sum_{d|P} mu(d)/d=phi(P)/P. Nothing requires a, b or c to be prime. Allowing these alternatives changes the admissible arithmetic functions, not just the score used on the old fixed menu.

## 3. A bound on every such mask, independent of its carry indices

This finite-table lemma makes the enlarged dictionary manageable without assuming bounds on untested high periods.

Let

    A_P(n) = #{1<=m<=n : gcd(m,P)=1}, A_P(0)=0.

By the elementary inclusion-exclusion identity,

    A_P(n) = sum_{d|P} mu(d) floor(n/d),
    A_P(n+P)=A_P(n)+phi(P).

The P=1 case is A_1(n)=n. For any real t>=0, set

    u=floor(t/b), v=floor(t/c), e=floor(t/a)-u-v in {0,1}.

Nested floors give exactly

    h_(P;a,b,c)(t) = A_P(u+v+e)-A_P(u)-A_P(v).             (2)

Write u=i+kP and v=j+lP, 0<=i,j<P. The linear period contributions cancel. Therefore all possible values are bounded by the finite set

    { A_P(i+j+e)-A_P(i)-A_P(j) : 0<=i,j<P, e=0,1 }.      (3)

Exhaustively evaluating (3) with integers yields:

| P | phi(P) | lower bound | upper bound H_P | cases checked |
|---:|---:|---:|---:|---:|
|1|1|0|1|2|
|2|1|-1|1|8|
|6|2|-1|1|72|
|30|8|-2|2|1800|
|210|48|-3|3|88200|

These bounds apply to **every** integer triple satisfying the reciprocal equation, not merely the selected examples or a finite range of a. Some individual triples may have a smaller true range. No assertion that every combination in (3) is attainable by every triple is needed for the bound.

Both implementations recompute the table. The separate checker additionally enumerates a full period of each of the 23 selected masked carries, totaling 1,088,718 cells. Those full-period checks are a cross-check; the finite-table reduction is the general argument.

For nonnegative amplitudes y_i,

    h = sum_i y_i h_i <= H := sum_i y_i H_(P_i)           (4)

globally. We do not assume that the individual maxima can occur simultaneously: their sum is an admissible, possibly conservative shield.

## 4. Search, proposal and selection record

This was exploratory, not preregistered. No prime counts were used to propose coefficients.

1. Starting from the exact integer prefix of W_old, scout P in {1,2,6,30,210}, 2<=a<=80, and every reciprocal split from Section 2. Scout unit-amplitude corrections only at a with W_old(a)>1. This produced 1065 rows, all retained in `scouting_scores.json`. This restriction is a heuristic for the scout, not a theorem excluding other useful corrections.
2. For each, evaluate the previous raw-deficit sufficient gain G and an upper allowance on its coefficient cost. Keep the 16 largest G values and the 16 best positive G/(3*number_of_mask_divisors + 3*raw_deficit_mass + 15H_P) values. Add the original mask-210 starts 18,19,20,21,24,25,32 as explicit options, including ones with unfavorable individual scores. Remove duplicates: 39 correction variables.
3. Optimize one **block** with amplitudes between 0 and 1. Auxiliary nonnegative deficits satisfy

       sum_i y_i h_i(n) - d_n <= W_old(n)-1, 1<=n<R.

   The objective maximizes

       sum_i y_i[kappa(h_i)-H_(P_i) C_*/R] - sum_n d_n k_n,

   where C_*=integral V(t)dt/t^2 and k_n is the carry-repair integral below. Constraints that cannot have a positive deficit under any allowed amplitude are omitted exactly by the bound sum_i max(h_i(n),0)<=W_old(n)-1. There are 8803 remaining constraints.
4. Also compute an alternative objective penalizing the sufficient coefficient/tail allowances at N=10^8. That alternative is preserved in `alternative_envelope_candidate.json`; its actual completed C is about 1.0342645, versus 1.0341191 for the gain-oriented block. Its completed envelope is also worse than the retained block at the tested N>=10^6. The candidate retained here is the gain-oriented block, selected after these evaluations, not an exact optimum claim.
5. Round the proposed amplitudes to multiples of 1/108. This need not preserve the floating LP's auxiliary feasibility. Recompute **all** deficits from the rounded amplitudes, construct repairs, and check the resulting coefficients exactly. Only the frozen rational point is asserted feasible. The LP's status is not used as a mathematical proof.

`discover.py` reproduces the scout and both LP proposals. `build.py` reconstructs the retained rational block, performs exact checks and evaluates its budget, without needing to solve an LP. `check.py` uses separate arithmetic implementations and imports neither producer nor baseline code.

## 5. The 23 frozen corrections

Each row is a masked carry from Section 2 with the indicated nonnegative amplitude. The whole block is applied directly to W_old, not to a seed followed by another radix-15 lifting.

| P | a | b | c | amplitude |
|---:|---:|---:|---:|---:|
|1|42|44|924|11/54|
|1|51|52|2652|2/3|
|210|42|45|630|43/54|
|6|80|90|720|19/36|
|1|44|45|1980|11/54|
|30|80|90|720|17/36|
|1|54|55|2970|1|
|6|68|70|2380|1|
|6|74|76|2812|1|
|6|51|52|2652|1/3|
|2|53|54|2862|1|
|2|50|51|2550|19/36|
|6|41|42|1722|1|
|6|50|51|2550|17/36|
|2|47|48|2256|1|
|30|72|75|1800|1|
|30|48|49|2352|1|
|30|49|50|2450|1|
|210|18|19|342|25/54|
|210|19|20|380|7/108|
|210|24|25|600|17/36|
|210|25|26|650|83/108|
|210|32|33|1056|29/108|

The sum in (4) is H=2633/108. The correction h has combined coefficient mass 3623/18.

## 6. Repairs and all-cutoff validity

For n=1,...,R-1 define raw deficits before repairs,

    d_n=max(0,1-W_old(n)+h(n)).

There are 498 nonzero raw deficits, with sum 48119/108. Use the previous carry repair b_n(t)=floor(t/n)-floor(t/(n+1))-floor(t/[n(n+1)]), and process n in increasing order:

    lambda_n=max(0,1-W_old(n)+h(n)-sum_{m<n} lambda_m b_m(n)).

All earlier repair terms are nonnegative, so 0<=lambda_n<=d_n. Every new repair starts at n, equals lambda_n there, is zero earlier, and cannot damage any cell. Only 82 nonzero repairs are needed, with sum 5243/108. Their full rational dictionary is in `results.json`.

Let P_rep=sum lambda_n b_n and

    W_new = W_old - h + P_rep + H V(t/R).                 (5)

Below R the tail term vanishes and the greedy argument establishes W_new>=1. The final exact reconstruction has minimum 1 on all 99999 integer cells. All breakpoints are integers, so this covers every real t in [1,R).

For t>=R, the global hypotheses give

    W_new(t) >= 1-H+0+H=1.

This is the final-weight tail invariant; it does not require positivity of a newly defined seed. The old W_old and V satisfy their all-cutoff hypotheses by the input's stated proofs. Every finite added floor sum is balanced and bounded. Absolute integrability against t^-2 follows from the old O(log^2 t) growth and the O(log t) shield, so the integral bookkeeping is legitimate.

For the repair cost,

    k_n = integral b_n(t)dt/t^2
        = log(n+1)/n-log(n)/(n+1)>0,
    integral P_rep(t)dt/t^2 = sum lambda_n k_n
                            <= Phi := sum d_n k_n.

Thus, before constructing repairs, a sufficient gain is

    G=kappa(h)-Phi-H*C_*/R,
    C_old-C_new >= G.                                     (6)

Exact rational logarithm bounds give, approximately:

| term | value |
|---|---:|
| gross kappa(h) | 0.0169965154087011496 |
| maximum repair bill Phi | 0.0053185613712742624 |
| tail shield H*C_*/R | 0.0002608265531135122 |
| guaranteed saving G | 0.0114171274843133750 |
| actual repair bill | 0.0049512826553703123 |
| actual saving | 0.0117844062002173252 |

The guarantee is an a priori bound relative to the repair procedure, not a closed-form distribution theorem: it still requires evaluating the finite prefix. We do not claim that every pair of good individual corrections is good together. They can compete for the same slack. The block objective accounts for that competition explicitly.

## 7. Complete factorial upper bound and every additional cost

Let F_step=-h+P_rep and F_new=F_old+F_step. Exact reconstruction gives

    ||F_step||_1=29723/108,
    ||D+F_old||_1=91127/108,
    ||D+F_new||_1=28306/27,
    T_new=6+H=3281/108.

The old H0 double-lift shield remains **unchanged**. T_new is the separate single-lift shield. They must not be combined by replacing H0 with H0+T_new in the double-lift expression.

For f(t)=sum c_j floor(t/j), put L_f(x)=sum c_j log(floor(x/j)!). The standard von Mangoldt divisor identity [1] gives

    B_new(N) = sum_{d<=N} Lambda(d) W_new(N/d) >= psi(N).

All coefficients are rational and may be signed. The elementary factorial error inequality in the input holds without a sign restriction:

    |L_f(x)-kappa(f)x| <= ||f||_1 (1+log^+ x)

for a finite balanced floor sum. Define l_N=1+log N,

    S1(N)=sum_{15^k<=N} [1+log(N/15^k)],
    S1_R(N)=sum_{R*15^k<=N} [1+log(N/(R*15^k))],
    S2(N)=sum_{R*15^m<=N} (m+1)[1+log(N/(R*15^m))].

Empty sums are zero. Merge finite corrections only at level zero, leaving higher D levels unchanged. The complete sufficient ceiling is

    U_new(N) = C_new*N
      + (28306/27) l_N
      + (56345/108)[S1(N)-l_N]
      + (3505/12) S2(N)
      + (16405/36) S1_R(N),                              (7)

and psi(N)<=B_new(N)<=U_new(N). Geometric tails are discarded only with the favorable signs kappa(D)>0 and kappa(g_*)>0, which both implementations check. The main term kappa(D+F_new) at level zero is retained exactly; no sign of kappa(F_step) is needed.

Compared with the input's U_old,

    U_old(N)-U_new(N)
       = gamma*N -(22097/108) l_N -(13165/36) S1_R(N),     (8)
    gamma=C_old-C_new>1/90.

For N>=10^6, put ell=log(N/R), a0=log15 and

    Q(N)=(22097/108)(1+log N)
          +(13165/36)(1+ell/a0)(1+ell).

The cost in (8) is at most Q(N). Differentiation gives

    Q(N)-NQ'(N)=(22097/108)log N
          +(13165/36)[ell+(ell^2-ell-1)/a0]>0

for ell>=2. Consequently Q(N)/N decreases on this entire range. At N0=10^6, the exact logarithm bounds 2<log10<7/3 and log15>2 give

    Q(N0)<(22097/108)*15+(13165/36)*(65/9)
          =925045/162 < N0/90,
    N0/90-925045/162=874955/162>0.

Thus U_new(N)<U_old(N) for **every integer N>=10^6**. This is an eventual comparison of two explicit fixed certificates, not an RH-scale estimate. Below that threshold the minimum of the two valid ceilings is safe.

Finite interval comparisons retain the unfavorable small-cutoff result:

| N | B_old-B_new | U_old-U_new |
|---:|---:|---:|
|10000|130.68828097|-1971.21048614|
|1000000|11873.39064130|7545.38828311|
|10000000|117999.48753388|111232.42765127|
|100000000|1178670.20025413|1168762.60299811|
|1000000000000|11784407209.41806427|11784377637.08621758|

`checks.json` stores outward-rounded decimal endpoints AND exact binary-rational endpoints. Decimal formatting is not used as an interval proof.

## 8. What happened to early excess

Selected exact integer-cell weights are:

| t | W_old(t) | W_new(t) |
|---:|---:|---:|
|18|79/54|1|
|19|245/108|119/54|
|20|2|2|
|21|1|1|
|24|53/36|1|
|25|191/108|1|
|32|137/108|1|
|42|2|1|
|48|2|1|
|50|2|1|
|51|2|1|
|54|2|1|
|68|2|1|
|74|3|1|
|80|2|1|

The block does not flatten the whole prefix. In particular t=20 remains at 2. No conclusion about the absence of other useful corrections follows from any zero amplitude in this finite LP.

## 9. What this establishes, and what it does not

It supplies explicit corrections passing the repair-cost criterion, a changed dictionary that permits multiple carry shapes and masks, a reusable global boundedness lemma independent of carry indices, and a complete bound beating the previous certificate for all sufficiently large cutoffs.

It does not prove that the search continues to find gains, that gains exhaust C_old-1, that coefficient growth permits a square-root error, or that C tends to 1. The final C remains above 1 by a fixed amount. No new bound on total CHHL E(N) is obtained. The floor/certificate branch has not switched to Nyman-Beurling or any other RH criterion.

Nor is this a fourth re-scoring of the original fixed period-2310 pilot. The admissible functions have changed: generalized reciprocal splits, variable masks, arbitrary new repair sites, and direct final-weight corrections are all present. Nevertheless it is still a finite search and a fixed candidate. Its value for the longer goal requires a uniform improvement-versus-complexity theorem not supplied here.

## 10. Reproduce, validate and preserve

Dependencies are numpy, scipy and mpmath. Versions used are recorded in `RUN_METADATA.json`. Run:

    OPENBLAS_NUM_THREADS=1 python build.py --output /tmp/block-rerun.json
    OPENBLAS_NUM_THREADS=1 python check.py --results /tmp/block-rerun.json --output /tmp/block-check.json
    OPENBLAS_NUM_THREADS=1 python discover.py --output-dir /tmp/new-block-search

The last directory must not already exist. `build.py` uses helper functions from the unmodified input ZIP via zipimport; it does not execute that package's main program. `check.py` imports no producer or baseline helper code. It uses integer divisor-event tables, event-scheduled repairs, independent mask-table enumeration, mpmath interval logarithms and interval log-gamma, and exact factorial prime-exponent identities.

The executed checker passed:

- 99999 final prefix cells;
- 90082 cases for the universal mask bounds;
- 1088718 full-period cells across the selected corrections;
- the independently rebuilt 82 repairs and their raw-deficit bounds;
- 1532 exact prime-exponent factorial identities;
- interval signs for all five B/U comparisons;
- the exact witnesses for the all-N>=10^6 ceiling comparison;
- the pinned unchanged input archive hash.

`SHA256SUMS.json` and `verify_files.py` cover the delivered files. This package is a conversation artifact, not a repository commit. No older package has been overwritten.

## References

[1] NIST DLMF 27.5.2--6, Möbius inversion and the von Mangoldt divisor identity: https://dlmf.nist.gov/27.5

[2] Jonathan Bober, *Factorial Ratios, Hypergeometric Series, and a Family of Step Functions*, Theorem 1.1's first family, the Chebyshev discussion, and Section 3: https://arxiv.org/html/0709.1977

[3] The unchanged local `repair_cost_rule.zip`, especially REPAIR_COST.md Sections 3 and 6, and its sources identifying the reviewed joint input. The input ZIP is included, not referenced by an inaccessible machine path.

The arithmetic identities and factorial framework are established mathematics. The bounds and finite constructions recorded here are supplied with their arguments and checks, without a literature-priority claim.
